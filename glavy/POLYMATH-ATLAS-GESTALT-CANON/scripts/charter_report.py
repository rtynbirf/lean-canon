#!/usr/bin/env python3
"""CANON REPORT — Устав §4, гейт G-report.

Проверяет текстовые запреты Устава (§3) по всем исходникам канона и
генерирует отчёт дома: docs/auto/CANON_REPORT.md + docs/auto/stats.json.

Гейты (несоблюдение -> ненулевой код выхода):
  G1  нет `sorry` / `admit` / `native_decide` в исходниках (вне комментариев);
  G2  нет объявлений `axiom` (разрешённая тройка приходит из ядра, не из дома);
  G3  в доме есть хотя бы один .lean-модуль и нет пустых файлов.
"""
from __future__ import annotations

import datetime
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
SRC = ROOT / "RequestProject"
OUT = ROOT / "docs" / "auto"

MODIFIERS = r"(?:(?:private|protected|partial|unsafe|noncomputable|scoped|public|macro_inline|local)\s+)*"
FORBIDDEN = re.compile(r"\b(sorry|admit|native_decide)\b")


def strip_comments(text: str) -> str:
    # Lean: блок открывается `/-` и закрывается `-/`; докстринги `/-! ... -/` и
    # `/-- ... -/` — тоже блоки. Вложенность в каноне не встречается, ленивый
    # конец `-/` корректен.
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    text = re.sub(r"--[^\n]*", "", text)
    return text


def main() -> None:
    files = sorted(SRC.rglob("*.lean"))
    gates: list[tuple[str, bool, str]] = []
    g1_offenders: list[str] = []
    g2_offenders: list[str] = []
    g3_offenders: list[str] = []

    total = {k: 0 for k in ("theorem", "lemma", "def", "abbrev", "structure",
                            "inductive", "class", "instance", "axiom", "opaque")}
    towers: dict[str, dict[str, int]] = {}
    namespaces: dict[str, int] = {}
    largest: list[tuple[int, str]] = []
    total_lines = 0

    for p in files:
        rel = p.relative_to(SRC)
        text = p.read_text(encoding="utf-8", errors="replace")
        code = strip_comments(text)
        lines = len(text.splitlines())
        total_lines += lines
        largest.append((lines, str(rel)))

        tower = rel.parts[0] if len(rel.parts) > 1 else "(корень)"
        t = towers.setdefault(tower, {"files": 0, "lines": 0})
        t["files"] += 1
        t["lines"] += lines

        counts = {k: len(re.findall(rf"^\s*{MODIFIERS}{k}\b", code, flags=re.M))
                  for k in total}
        for k, v in counts.items():
            total[k] += v

        for m in FORBIDDEN.finditer(code):
            ln = code.count("\n", 0, m.start()) + 1
            g1_offenders.append(f"RequestProject/{rel}:{ln}: {m.group(0)}")

        for m in re.finditer(rf"^\s*{MODIFIERS}axiom\b", code, flags=re.M):
            ln = code.count("\n", 0, m.start()) + 1
            g2_offenders.append(f"RequestProject/{rel}:{ln}")

        if lines == 0:
            g3_offenders.append(f"RequestProject/{rel}: пустой файл")

        for m in re.finditer(r"^\s*namespace\s+([A-Za-z_][\w'.]*)", code, flags=re.M):
            root_ns = m.group(1).split(".")[0]
            namespaces[root_ns] = namespaces.get(root_ns, 0) + 1

    if not files:
        g3_offenders.append("в доме нет ни одного .lean-модуля")

    gates.append(("G1: запрет sorry/admit/native_decide", not g1_offenders,
                  "; ".join(g1_offenders[:20]) or "0 нарушений"))
    gates.append(("G2: запрет объявлений axiom", not g2_offenders,
                  "; ".join(g2_offenders[:20]) or "0 нарушений"))
    gates.append(("G3: модули на месте и непусты", not g3_offenders,
                  "; ".join(g3_offenders[:20]) or f"{len(files)} модулей"))

    commit = subprocess.run(["git", "rev-parse", "--short", "HEAD"],
                            capture_output=True, text=True).stdout.strip() or "?"
    now = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    ok = all(g[1] for g in gates)
    verdict = "ЧИСТО" if ok else "ГРЯЗНО"

    OUT.mkdir(parents=True, exist_ok=True)
    stats = {
        "generated_at": now,
        "commit": commit,
        "verdict": verdict,
        "lean_files": len(files),
        "total_lines": total_lines,
        "declarations": total,
        "towers": towers,
        "namespace_roots": dict(sorted(namespaces.items(),
                                       key=lambda kv: -kv[1])[:20]),
        "largest_files": [{"file": f, "lines": n}
                          for n, f in sorted(largest, reverse=True)[:20]],
    }
    (OUT / "stats.json").write_text(json.dumps(stats, ensure_ascii=False, indent=2),
                                    encoding="utf-8")

    md = [
        "# CANON REPORT — состояние дома",
        "",
        f"* Сгенерировано: {now} · коммит `{commit}`",
        f"* Вердикт автомата: **{verdict}**",
        "",
        "## Гейты Устава",
        "",
        "| Гейт | Статус | Детали |",
        "|---|---|---|",
    ]
    for name, passed, detail in gates:
        md.append(f"| {name} | {'✅ ЗЕЛЁН' if passed else '❌ КРАСН'} | {detail} |")
    md += [
        "",
        "## Декларации",
        "",
        "| Вид | Количество |",
        "|---|---|",
    ]
    for k, v in total.items():
        md.append(f"| `{k}` | {v} |")
    md += [
        "",
        f"Всего: **{len(files)}** модулей, **{total_lines}** строк Lean.",
        "",
        "## Башни (слои канона)",
        "",
        "| Слой | Файлы | Строки |",
        "|---|---|---|",
    ]
    for name in sorted(towers):
        t = towers[name]
        md.append(f"| {name} | {t['files']} | {t['lines']} |")
    md += [
        "",
        "## Корни пространств имён",
        "",
        "| Пространство | Объявлений `namespace` |",
        "|---|---|",
    ]
    for ns, c in list(namespaces.items())[:20]:
        md.append(f"| `{ns}` | {c} |")
    md.append("")
    (OUT / "CANON_REPORT.md").write_text("\n".join(md), encoding="utf-8")

    print(f"CANON-REPORT: {verdict} | files={len(files)} lines={total_lines} "
          f"theorems={total['theorem']} defs={total['def']} axioms={total['axiom']}")
    if not ok:
        for name, passed, detail in gates:
            if not passed:
                print(f"GATE FAILED — {name}: {detail}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
