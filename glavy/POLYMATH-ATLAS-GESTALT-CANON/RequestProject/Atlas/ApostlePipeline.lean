import Mathlib

/-!
# The Twelve Apostles as a Fault-Tolerant Processing Pipeline

This file formalizes the 13-phase "apostle pipeline": a metaphorical model of a
CPU / operating system processing a traumatic *input* through a *stack*, from the
initial `malloc` (Peter) to the terminal `Kernel Panic` (Judas) and the
out-of-stack `root` reset (Paul).

The model is a small deterministic finite-state machine:

* `Phase`      — the 13 phases, named after the apostles.
* `Params`     — one traumatic input and the resources spent processing it.
* `St`         — runtime state (current stack depth, crash flag).
* `step`       — the effect of a single phase on the state.
* `runToJudas` — running phases 1–12 (Peter … Judas, the crash check).
* `runFull`    — running all 13 phases (… Paul, the reset).

We prove:

* `runToJudas_stack` / `runToJudas_crashed` — closed forms for the state at Judas.
* `judas_crashes_iff` — the crash happens **iff** the net load overflows the stack.
* `gc_prevents_crash` / `cleanup_prevents_overflow` — enough cleanup avoids the crash.
* `more_gc_never_hurts` — garbage collection is monotone: more of it never
  increases the surviving load.
* `paul_recovers` — Paul's root access **always** returns a clean, crash-free
  state, regardless of what happened inside the stack ("вне Стека").
* `flinch_kernel_panic` — Peter's precondition: flinching during `malloc`
  panics the kernel before the process even begins.
* ordering facts (`flow_index`, `flow_nodup`, `Phase.index_injective`) witnessing
  that the 13 phases run in a fixed linear order.
-/

namespace ApostlePipeline

/-- The 13 phases of the pipeline, named after the apostles. -/
inductive Phase
  | peter | andrew | jamesZebedee | john | philip | bartholomew
  | thomas | matthew | jamesAlphaeus | thaddaeus | simonZelotes
  | judas | paul
deriving DecidableEq, Repr

/-- Parameters describing one traumatic "input" and the resources the system
    spends processing it. -/
structure Params where
  input    : Nat   -- Andrew: raw environmental hit (Δ)
  surge    : Nat   -- James (Zebedee): adrenaline spike added to the stack
  foreign  : Nat   -- Bartholomew: foreign guilt/shame cut away at validation
  selfPity : Nat   -- Matthew: self-pity removed during stack accounting
  patch    : Nat   -- James (Alphaeus): background sub-routine patching
  offload  : Nat   -- Thaddaeus: data offloaded to another node (P2P)
  gc       : Nat   -- Simon the Zealot: garbage collection sweep
  capacity : Nat   -- stack capacity before overflow

/-- Runtime state: current stack depth and whether the kernel crashed. -/
structure St where
  stack   : Nat
  crashed : Bool
deriving Repr, DecidableEq

/-- One phase's effect on the state, given the parameters. -/
def step (p : Params) : Phase → St → St
  | .peter,         _ => { stack := 0, crashed := false }          -- malloc: fresh stack
  | .andrew,        s => { s with stack := s.stack + p.input }     -- input Δ
  | .jamesZebedee,  s => { s with stack := s.stack + p.surge }     -- surge
  | .john,          s => s                                          -- logging: observe only
  | .philip,        s => s                                          -- parsing: observe only
  | .bartholomew,   s => { s with stack := s.stack - p.foreign }   -- validation
  | .thomas,        s => s                                          -- execution: embodiment
  | .matthew,       s => { s with stack := s.stack - p.selfPity }  -- accounting
  | .jamesAlphaeus, s => { s with stack := s.stack - p.patch }     -- sub-routine
  | .thaddaeus,     s => { s with stack := s.stack - p.offload }   -- P2P offload
  | .simonZelotes,  s => { s with stack := s.stack - p.gc }        -- garbage collection
  | .judas,         s => { s with crashed := decide (p.capacity < s.stack) } -- crash check
  | .paul,          _ => { stack := 0, crashed := false }          -- root reset

/-- Phases 1–12: from Peter's `malloc` through Judas's overflow check. -/
def orderToJudas : List Phase :=
  [.peter, .andrew, .jamesZebedee, .john, .philip, .bartholomew,
   .thomas, .matthew, .jamesAlphaeus, .thaddaeus, .simonZelotes, .judas]

/-- The full 13-phase flow, ending with Paul's root reset. -/
def flow : List Phase := orderToJudas ++ [.paul]

/-- Run phases 1–12 starting from state `s0`. -/
def runToJudas (p : Params) (s0 : St) : St :=
  orderToJudas.foldl (fun s ph => step p ph s) s0

/-- Run the full 13-phase pipeline starting from state `s0`. -/
def runFull (p : Params) (s0 : St) : St :=
  flow.foldl (fun s ph => step p ph s) s0

/-- The net stack depth that reaches Judas after every reduction phase. -/
def reduced (p : Params) : Nat :=
  p.input + p.surge - p.foreign - p.selfPity - p.patch - p.offload - p.gc

/-- `reduced` as a single truncated subtraction of the total freed resources. -/
theorem reduced_eq (p : Params) :
    reduced p =
      (p.input + p.surge) -
        (p.foreign + p.selfPity + p.patch + p.offload + p.gc) := by
  simp only [reduced]; omega

/-- Closed form for the stack depth reaching Judas. -/
theorem runToJudas_stack (p : Params) (s0 : St) :
    (runToJudas p s0).stack = reduced p := by
  simp [runToJudas, orderToJudas, step, reduced]

/-- Closed form for Judas's crash flag. -/
theorem runToJudas_crashed (p : Params) (s0 : St) :
    (runToJudas p s0).crashed = decide (p.capacity < reduced p) := by
  simp [runToJudas, orderToJudas, step, reduced]

/-- **The crash law.** The Judas Kernel Panic fires exactly when the surviving
    load overflows the stack capacity — "Стек переполнен". -/
theorem judas_crashes_iff (p : Params) (s0 : St) :
    (runToJudas p s0).crashed = true ↔ p.capacity < reduced p := by
  rw [runToJudas_crashed]; simp

/-- If the surviving load fits in the stack, Judas does not crash. -/
theorem gc_prevents_crash (p : Params) (s0 : St)
    (h : reduced p ≤ p.capacity) :
    (runToJudas p s0).crashed = false := by
  rw [runToJudas_crashed]; simp; omega

/-- **Cleanup theorem.** If the phases that free the stack (validation,
    accounting, sub-routine, P2P, garbage collection) together with the stack
    capacity absorb the whole incoming load, no crash occurs. -/
theorem cleanup_prevents_overflow (p : Params) (s0 : St)
    (h : p.input + p.surge ≤
          p.foreign + p.selfPity + p.patch + p.offload + p.gc + p.capacity) :
    (runToJudas p s0).crashed = false := by
  apply gc_prevents_crash
  rw [reduced_eq]; omega

/-- **Garbage collection is monotone.** Increasing Simon the Zealot's sweep
    never increases the load that survives to Judas. -/
theorem more_gc_never_hurts (p : Params) (g' : Nat) (h : p.gc ≤ g') :
    reduced { p with gc := g' } ≤ reduced p := by
  simp only [reduced_eq]; omega

/-- **Paul is outside the stack ("вне Стека").** However the run went — even a
    Judas overflow — Paul's root access resets the process to a clean,
    crash-free state with an empty stack. -/
theorem paul_recovers (p : Params) (s0 : St) :
    runFull p s0 = { stack := 0, crashed := false } := by
  simp [runFull, flow, orderToJudas, step]

/-- Peter's `malloc`: booting the process. Flinching (`flinch = true`) aborts. -/
def boot (flinch : Bool) : Option St :=
  if flinch then none else some { stack := 0, crashed := false }

/-- **Peter's precondition.** If you flinch and turn away during allocation,
    the kernel panics before the process starts. -/
theorem flinch_kernel_panic : boot true = none := rfl

/-- A steady boot yields a fresh, empty, crash-free stack. -/
theorem boot_ok : boot false = some { stack := 0, crashed := false } := rfl

/-- The linear position (1–13) of each phase in the pipeline. -/
def Phase.index : Phase → Nat
  | .peter => 1        | .andrew => 2         | .jamesZebedee => 3
  | .john => 4         | .philip => 5         | .bartholomew => 6
  | .thomas => 7       | .matthew => 8        | .jamesAlphaeus => 9
  | .thaddaeus => 10   | .simonZelotes => 11  | .judas => 12
  | .paul => 13

/-- The flow visits the phases in order 1, 2, …, 13. -/
theorem flow_index : flow.map Phase.index = List.range' 1 13 := by
  decide

/-- No phase is visited twice. -/
theorem flow_nodup : flow.Nodup := by decide

/-- All 13 phases occur in the flow. -/
theorem flow_length : flow.length = 13 := by decide

/-- The linear ordering assigns distinct positions to distinct phases. -/
theorem Phase.index_injective : Function.Injective Phase.index := by
  intro a b h
  cases a <;> cases b <;> simp_all [Phase.index]

/-! ### Concrete runs -/

/-- A start state: a freshly allocated, empty, crash-free stack. -/
def start : St := { stack := 0, crashed := false }

/-- An overwhelming hit with **no** cleanup overflows the stack: Kernel Panic. -/
example :
    (runToJudas
      { input := 100, surge := 50, foreign := 0, selfPity := 0, patch := 0,
        offload := 0, gc := 0, capacity := 64 } start).crashed = true := by
  decide

/-- The very same hit survives once the cleanup phases do their work. -/
example :
    (runToJudas
      { input := 100, surge := 50, foreign := 10, selfPity := 20, patch := 5,
        offload := 15, gc := 40, capacity := 64 } start).crashed = false := by
  decide

end ApostlePipeline
