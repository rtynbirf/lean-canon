# -*- coding: utf-8 -*-
"""П46 (Волна ×4, issue #3): якоря верификации как формальные инварианты.

Lean-тулчейн (lake + Mathlib v4.28.0, ~3 ГБ) в этой среде недоступен —
предложение П46 исполняется честным фоллбеком: якоря VERIFICATION_ANCHORS.txt
фиксируются как машиночитаемые инварианты VERIFICATION_ANCHORS.json, а
этот скрипт — их проверяющий (инвариант «проверяй строкой»).

Режимы:
  python3 scripts/verify_anchors.py            # сверка JSON-реестра с деревом (rc 0/1)
  python3 scripts/verify_anchors.py --selftest # самоиспытание проверяющего (rc 0/1)
  python3 scripts/verify_anchors.py --txt      # осмотр исходного .txt: [В]/[О] по строкам

Инварианты реестра (проверяются всегда):
  I1. каждый якорь = существующий файл; sha256 файла == пломбе якоря;
  I2. статус "proven" возможен ТОЛЬКО при lean_build.available == true
      (в фоллбеке все якоря — "axiom": не доказаны компилятором);
  I3. число axioms == числу якорей со статусом "axiom" == числу
      недоказанных якорей (приёмка issue, фоллбек-смысл);
  I4. каждый *.lean модуль PolymathAtlas/ покрыт якорем (пустых дыр нет);
  I5. top-level `axiom`-декларации в *.lean == списку lean_axioms
      (объявленные в коде аксиомы не прячутся).
"""
import argparse
import hashlib
import json
import os
import re
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
JSON_PATH = os.path.join(ROOT, "VERIFICATION_ANCHORS.json")
TXT_PATH = os.path.join(ROOT, "VERIFICATION_ANCHORS.txt")
LEAN_DIR = os.path.join(ROOT, "PolymathAtlas")

AXIOM_RE = re.compile(r"^axiom\s+([A-Za-z_][A-Za-z0-9_']*)", re.M)


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def lean_axioms(lean_dir=LEAN_DIR):
    """Топ-уровневые `axiom`-декларации по всем модулям (I5)."""
    out = []
    for name in sorted(os.listdir(lean_dir)):
        if not name.endswith(".lean"):
            continue
        text = open(os.path.join(lean_dir, name), encoding="utf-8").read()
        for m in AXIOM_RE.finditer(text):
            out.append({"module": f"PolymathAtlas/{name}", "name": m.group(1)})
    return out


def build_registry():
    """Собрать реестр из живого дерева (используется --selftest и генерацией)."""
    anchors = []
    for name in sorted(os.listdir(LEAN_DIR)):
        if name.endswith(".lean"):
            rel = f"PolymathAtlas/{name}"
            anchors.append({
                "id": "anchor-" + name[:-5].lower(),
                "path": rel,
                "kind": "module",
                "sha256": sha256_file(os.path.join(ROOT, rel)),
                "status": "axiom",  # не доказан компилятором (Lean недоступен)
            })
    for rel in ("lakefile.lean", "lean-toolchain"):
        anchors.append({
            "id": "anchor-" + os.path.basename(rel),
            "path": rel,
            "kind": "toolchain",
            "sha256": sha256_file(os.path.join(ROOT, rel)),
            "status": "axiom",
        })
    return {
        "registry_version": 1,
        "generated": "by scripts/verify_anchors.py (Волна ×4 · П46)",
        "source_txt": "VERIFICATION_ANCHORS.txt (сгенерирован 2026-11-04)",
        "lean_build": {
            "available": False,
            "note": "lake + Mathlib v4.28.0 (~3 ГБ) в среде Волны ×4 недоступны; "
                    "все якоря честно объявлены axiom — леммы/теоремы Lean не заявляются. "
                    "Появление тулчейна: lake build rc=0 → статусы «proven» по фактам сборки.",
        },
        "axioms": [a["id"] for a in anchors if a["status"] == "axiom"],
        "lean_axioms": lean_axioms(),
        "anchors": anchors,
    }


def verify(json_path=JSON_PATH, root=ROOT):
    """Сверка реестра с деревом → отчёт {ok, invariants, failures}."""
    report = {"ok": True, "checked": 0, "failures": [], "invariants": {}}

    def fail(code, detail):
        report["ok"] = False
        report["failures"].append({"invariant": code, "detail": detail})

    try:
        reg = json.load(open(json_path, encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as e:
        fail("STRUCTURE", f"реестр не читается: {e}")
        return report

    anchors = reg.get("anchors")
    if not isinstance(anchors, list) or not anchors:
        fail("I1", "реестр без якорей")
        return report

    seen = set()
    for a in anchors:
        aid, path = a.get("id"), a.get("path")
        report["checked"] += 1
        if not aid or not path or aid in seen:
            fail("I1", f"якорь без id/path или дубликат: {a!r}")
            continue
        seen.add(aid)
        p = os.path.join(root, path)
        if not os.path.exists(p):
            fail("I1", f"{aid}: файл отсутствует {path}")
            continue
        got = sha256_file(p)
        if got != a.get("sha256"):
            fail("I1", f"{aid}: MUTATED {path}: пломба {a.get('sha256','')[:12]}… != живой {got[:12]}…")

    # I2/I3: статусы и аксиомный счёт
    unproven = [a["id"] for a in anchors if a.get("status") != "proven"]
    axioms = reg.get("axioms")
    if not reg.get("lean_build", {}).get("available"):
        bad = [a.get("id") for a in anchors if a.get("status") == "proven"]
        if bad:
            fail("I2", f"proven без тулчейна: {bad}")
        if sorted(axioms or []) != sorted(unproven):
            fail("I3", "axioms != списку недоказанных якорей")
    report["invariants"] = {
        "anchors": len(anchors),
        "unproven": len(unproven),
        "axioms": len(axioms or []),
    }

    # I4: покрытие всех lean-модулей (корень передан, не глобальный)
    lean_root = os.path.join(root, "PolymathAtlas")
    lean_files = set()
    if os.path.isdir(lean_root):
        lean_files = {f"PolymathAtlas/{n}" for n in os.listdir(lean_root)
                      if n.endswith(".lean")}
    covered = {a.get("path") for a in anchors}
    for miss in sorted(lean_files - covered):
        fail("I4", f"модуль без якоря: {miss}")

    # I5: кодовые аксиомы не спрятаны (сверка в том же корне)
    live_lean_axioms = lean_axioms(lean_root) if os.path.isdir(lean_root) else []
    if sorted(map(json.dumps, reg.get("lean_axioms", []))) != \
       sorted(map(json.dumps, live_lean_axioms)):
        fail("I5", "lean_axioms реестра != топ-уровневым axiom в *.lean")

    return report


def check_txt(txt_path=TXT_PATH, root=ROOT):
    """Осмотр исходного .txt (-generated 2026-11-04): [В]/[О] по строкам."""
    rows = []
    for line in open(txt_path, encoding="utf-8"):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        h, p = line.split(None, 1)
        p = p.strip()
        if not os.path.exists(os.path.join(root, p)):
            rows.append((p, "[Н]", "MISSING"))
        elif sha256_file(os.path.join(root, p)) == h:
            rows.append((p, "[В]", "пломба жива"))
        else:
            rows.append((p, "[О]", "MUTATED: файл менялся после 2026-11-04 (пломба устарела)"))
    return rows


def selftest():
    """Самоиспытание проверяющего: подмена ловится, инварианты кусаются."""
    ok = True

    def need(cond, msg):
        nonlocal ok
        if not cond:
            ok = False
            print(f"SELFTEST FAIL: {msg}")

    with tempfile.TemporaryDirectory() as td:
        lean = os.path.join(td, "PolymathAtlas")
        os.makedirs(lean)
        open(os.path.join(lean, "Core.lean"), "w").write("theorem t : True := .intro\n")
        open(os.path.join(lean, "Gaps.lean"), "w").write("axiom unproven_gap : False\n")
        # собираем реестр руками (build_registry привязан к ROOT репо)
        anchors = []
        for name in ("Core.lean", "Gaps.lean"):
            rel = f"PolymathAtlas/{name}"
            anchors.append({"id": f"anchor-{name[:-5].lower()}", "path": rel,
                            "kind": "module",
                            "sha256": sha256_file(os.path.join(td, rel)),
                            "status": "axiom"})
        fixture = {"registry_version": 1, "lean_build": {"available": False},
                   "axioms": [a["id"] for a in anchors],
                   "lean_axioms": lean_axioms(lean),
                   "anchors": anchors}
        jp = os.path.join(td, "anchors.json")
        json.dump(fixture, open(jp, "w", encoding="utf-8"))
        r = verify(jp, td)
        need(r["ok"], f"чистая фикстура должна проходить: {r['failures']}")

        # подмена середины ловится
        open(os.path.join(lean, "Core.lean"), "a").write("-- silent mutation\n")
        r2 = verify(jp, td)
        need(not r2["ok"], "подмена модуля должна ловиться (I1)")

        # сокрытие кодовой аксиомы ловится
        fixture["lean_axioms"] = []
        json.dump(fixture, open(jp, "w", encoding="utf-8"))
        r3 = verify(jp, td)
        need(not r3["ok"], "скрытая axiom должна ловиться (I5)")
    print("SELFTEST:", "OK" if ok else "FAILED")
    return ok


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description="Проверяющий якорей (П46, фоллбек Lean)")
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--txt", action="store_true", help="осмотр VERIFICATION_ANCHORS.txt")
    ap.add_argument("--rebuild", action="store_true",
                    help="пересобрать VERIFICATION_ANCHORS.json из живого дерева (stdout)")
    args = ap.parse_args()

    if args.rebuild:
        print(json.dumps(build_registry(), ensure_ascii=False, indent=2))
        sys.exit(0)
    if args.selftest:
        sys.exit(0 if selftest() else 1)
    if args.txt:
        for p, v, note in check_txt():
            print(f"{v}  {p}  — {note}")
        sys.exit(0)
    r = verify()
    print(json.dumps(r, ensure_ascii=False, indent=2))
    sys.exit(0 if r["ok"] else 1)
