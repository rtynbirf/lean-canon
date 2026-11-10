#!/usr/bin/env python3
"""СТОРОЖ-СВЕЖЕСТЬ (Устав §10).

Раз в неделю сравнивает пин дома (lean-toolchain + lakefile.toml) с мировым
краем (последний релиз leanprover/lean4). Если мир ушёл вперёд и похожего
issue ещё нет — открывает issue. Ничего в доме не меняет: апгрейд по Уставу —
отдельная операция перекрёстной проверки.
"""
from __future__ import annotations

import json
import pathlib
import re
import subprocess
import sys
import urllib.request

ROOT = pathlib.Path(__file__).resolve().parents[1]


def latest_release(repo: str) -> str:
    req = urllib.request.Request(
        f"https://api.github.com/repos/{repo}/releases/latest",
        headers={"User-Agent": "canon-watchdog"},
    )
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.load(r)["tag_name"]


def main() -> None:
    toolchain = (ROOT / "lean-toolchain").read_text().strip().split(":")[-1]
    lake = (ROOT / "lakefile.toml").read_text(encoding="utf-8")
    m = re.search(r'rev\s*=\s*"([^"]+)"', lake)
    mathlib_pin = m.group(1) if m else "?"
    world = latest_release("leanprover/lean4")

    print(f"дом: lean={toolchain} mathlib={mathlib_pin}")
    print(f"мир: lean={world}")

    if world == toolchain:
        print("ДОМ СВЕЖ: пин дома совпадает с мировым краем")
        return

    title = f"Сторож свежести: вышел Lean {world}, дом стоит на {toolchain}"
    seen = subprocess.run(
        ["gh", "issue", "list", "--state", "open", "--search", title,
         "--json", "number"],
        capture_output=True, text=True,
    )
    if seen.returncode == 0 and json.loads(seen.stdout or "[]"):
        print("issue уже открыт — не спамим")
        return

    body = (
        f"Дом запинен на `{toolchain}` / Mathlib `{mathlib_pin}`.\n\n"
        f"Вышел Lean `{world}` — следом обычно выходит и тег Mathlib `{world}`.\n\n"
        "По Уставу §10: **апгрейд — отдельная операция перекрёстной проверки "
        "всех модулей канона**, а не бытовая «уборка». Пока перекрёстная "
        "проверка не зелёная, дом стоит на своём пине. Issue закрывать только "
        "после зелёного свипа на новой версии."
    )
    subprocess.run(
        ["gh", "issue", "create", "--title", title, "--body", body,
         "--label", "enhancement"],
        check=True,
    )
    print("открыт issue о свежести")


if __name__ == "__main__":
    main()
