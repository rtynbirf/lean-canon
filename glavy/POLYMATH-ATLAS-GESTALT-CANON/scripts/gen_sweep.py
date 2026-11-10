#!/usr/bin/env python3
"""Генератор полного аксиомного свипа (Устав §4, гейт G-sweep).

Собирает список ВСЕХ модулей канона из `git ls-files` (никаких ручных списков —
новый файл в доме автоматически попадает под свип), подставляет его в
`scripts/axiom_sweep_body.lean` и печатает готовый Lean-файл в stdout:

    python3 scripts/gen_sweep.py > scripts/AxiomSweepGenerated.lean
    lake env lean scripts/AxiomSweepGenerated.lean
"""
from __future__ import annotations

import pathlib
import subprocess
import sys


def main() -> None:
    out = subprocess.check_output(["git", "ls-files", "RequestProject"], text=True)
    mods: list[str] = []
    for line in out.splitlines():
        f = line.strip()
        if f.endswith(".lean"):
            mods.append(f[: -len(".lean")].replace("/", "."))
    mods.sort()
    if not mods:
        sys.exit("CANON-GEN: ни одного модуля не найдено — дом пуст?")
    body_path = pathlib.Path("scripts/axiom_sweep_body.lean")
    body = body_path.read_text(encoding="utf-8")
    lean_list = "[" + ", ".join("`" + m for m in mods) + "]"
    text = body.replace("__MODULE_LIST__", lean_list)
    imports = "".join(f"import {m}\n" for m in mods)
    sys.stdout.write(imports + "\n" + text)


if __name__ == "__main__":
    main()
