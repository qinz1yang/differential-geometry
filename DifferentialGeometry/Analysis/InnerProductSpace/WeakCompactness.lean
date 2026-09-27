import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped InnerProductSpace RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [TopologicalSpace.SeparableSpace E]

theorem exists_weakly_convergent_subsequence_of_norm_bounded
    {C : ℝ} (u : ℕ → E) (hu : ∀ m, ‖u m‖ ≤ C) :
    ∃ φ : ℕ → ℕ, ∃ v : E, StrictMono φ ∧
      ∀ z, Tendsto (fun m => inner ℝ (u (φ m)) z) atTop
        (𝓝 (inner ℝ v z)) := by
  let w : ℕ → WeakDual ℝ E := fun m =>
    StrongDual.toWeakDual (innerSL ℝ (u m))
  let c₀ : StrongDual ℝ E := innerSL ℝ (0 : E)
  have hwmem : ∀ m, w m ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall c₀ C := by
    intro m
    rw [Set.mem_preimage, Metric.mem_closedBall]
    change dist
      ((InnerProductSpace.toDualMap ℝ E) (u m))
      ((InnerProductSpace.toDualMap ℝ E) 0) ≤ C
    rw [(InnerProductSpace.toDualMap ℝ E).isometry.dist_eq, dist_zero_right]
    exact hu m
  rcases WeakDual.isSeqCompact_closedBall ℝ E c₀ C hwmem with
    ⟨wLim, _, φ, hφ, hw⟩
  let v : E :=
    (InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual wLim)
  refine ⟨φ, v, hφ, ?_⟩
  intro z
  have heval := (WeakDual.eval_continuous z).continuousAt.tendsto.comp hw
  simpa only [Function.comp_apply, Function.comp_def, w,
    StrongDual.toWeakDual_apply, WeakDual.toStrongDual_apply,
    innerSL_apply_apply, v, InnerProductSpace.toDual_symm_apply] using heval

end DifferentialGeometry.Analysis.InnerProductSpace

end
