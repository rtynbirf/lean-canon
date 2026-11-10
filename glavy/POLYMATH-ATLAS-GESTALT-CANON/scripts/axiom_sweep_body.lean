import Lean

/-! # CANON AXIOM SWEEP — автомат-страж Устава (§3, §4: гейт G-sweep)

Этот файл ГЕНЕРИРУЕТСЯ командой
    python3 scripts/gen_sweep.py > scripts/AxiomSweepGenerated.lean
и никогда не коммитится. Правка тела — только в `scripts/axiom_sweep_body.lean`.

Свип проходит по каждой константе каждого модуля канона (по данным
`ModuleData.constNames`, а не по grep-тексту) и требует, чтобы транзитивный
аксиомный след каждой константы лежал в разрешённом множестве Устава
`{ propext, Classical.choice, Quot.sound }`.

Автоматически ловится:
  * `sorry` / `admit`          → зависимость `sorryAx`;
  * `native_decide`            → зависимость `Lean.ofReduceBool`;
  * любое объявление `axiom`   → сама аксиома в следе;
  * любая иная внешняя аксиома, протёкшая через зависимости.
-/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let ourModules : List Name := __MODULE_LIST__
  let mut offenders : Array String := #[]
  let mut constCount := 0
  let mut thmCount := 0
  let mut defCount := 0
  let mut axiomCount := 0
  for mod in ourModules do
    let some idx := env.getModuleIdx? mod
      | throwError "CANON-SWEEP: module {mod} is not in the environment — import list is stale"
    let md := env.header.moduleData[idx]!
    for c in md.constNames do
      let some ci := env.find? c
        | continue
      constCount := constCount + 1
      match ci with
      | .thmInfo _ => thmCount := thmCount + 1
      | .defnInfo _ => defCount := defCount + 1
      | .axiomInfo _ => axiomCount := axiomCount + 1
      | _ => pure ()
      -- теоремы/определения/опак-декларации/аксиомы — полный след;
      -- конструкторы/рекурсоры/индуктивы наследуют след через пользователей.
      match ci with
      | .ctorInfo _ | .recInfo _ | .inductInfo _ | .quotInfo _ => pure ()
      | _ =>
        let axs ← Lean.collectAxioms c
        for a in axs do
          unless allowed.contains a do
            offenders := offenders.push s!"{c} ← forbidden axiom `{a}`"
    IO.println s!"canon-sweep: {mod} done (consts so far: {constCount}, offenders: {offenders.size})"
  if h : offenders.size > 0 then
    let shown := offenders.take 100
    throwError "CANON-SWEEP FAILED: {offenders.size} offender(s):\n{shown}\n..."
  logInfo m!"CANON-SWEEP OK: modules={ourModules.length} constants={constCount} theorems={thmCount} defs={defCount} axiomDecls={axiomCount} offenders=0 allowed=[propext, Classical.choice, Quot.sound]"
