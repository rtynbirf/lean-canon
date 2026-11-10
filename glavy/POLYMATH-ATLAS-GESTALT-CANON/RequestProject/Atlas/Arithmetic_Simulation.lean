import Mathlib
import RequestProject.Atlas.Arithmetic_Foundations
import RequestProject.Atlas.IdealAI_Countermodels

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # Observationally faithful simulation -/

namespace Arithmetic_Simulation

/-- Equal observations remain equal under every observation-based test. -/
theorem every_observer_test_agrees {System Observation Result : Type*}
    (observe : System → Observation) {real simulated : System}
    (fidelity : observe real = observe simulated) (test : Observation → Result) :
    test (observe real) = test (observe simulated) := by
  exact congrArg test fidelity

/-- Observational fidelity supplies the missing premise of the positive
simulation-indistinguishability theorem. -/
theorem simulation_indistinguishability
    (scenario : IdealAI.SimulationScenario)
    (fidelity : IdealAI.ObservationallyIndistinguishable scenario)
    (detailed : scenario.sufficientlyDetailed)
    (inside : scenario.observerInside) :
    ¬ scenario.canDistinguishSimulation := by
  exact IdealAI.Reclaimed.simulation_indistinguishability
    scenario fidelity detailed inside

end Arithmetic_Simulation
