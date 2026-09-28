import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section

open Set

open scoped NNReal

namespace LipschitzOnWith

variable {X F : Type*} [PseudoMetricSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem exists_lipschitz_extension {f : X → F} {s : Set X} {K : ℝ≥0}
    (hf : LipschitzOnWith K f s) :
    ∃ (g : X → F) (L : ℝ≥0), LipschitzWith L g ∧ EqOn f g s := by
  let e : F ≃L[ℝ] (Fin (Module.finrank ℝ F) → ℝ) := (Module.finBasis ℝ F).equivFunL
  obtain ⟨g, hg, hfg⟩ :=
    (e.toContinuousLinearMap.lipschitzWith.comp_lipschitzOnWith hf).extend_pi
  refine ⟨e.symm ∘ g, _, e.symm.toContinuousLinearMap.lipschitzWith.comp hg, ?_⟩
  intro x hx
  exact (e.symm_apply_apply (f x)).symm.trans (congrArg e.symm (hfg hx))

end LipschitzOnWith

end
