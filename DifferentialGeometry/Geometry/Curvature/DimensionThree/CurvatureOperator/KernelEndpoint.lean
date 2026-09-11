import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.NullReactionRank
import Mathlib.Topology.Instances.Matrix

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open scoped Matrix _root_.Topology

private theorem matrix_eval_continuous (v : Fin 3 → ℝ) :
    Continuous (fun A : Matrix (Fin 3) (Fin 3) ℝ => A *ᵥ v) :=
  continuous_id.matrix_mulVec continuous_const

private theorem curvature_reaction_continuous : Continuous hamiltonIveyMatrixReaction := by
  unfold hamiltonIveyMatrixReaction
  have hid : Continuous (fun A : Matrix (Fin 3) (Fin 3) ℝ => A) := continuous_id
  have hc := ((hid.matrix_mul hid).add hid.matrix_adjugate).const_smul (2 : ℕ)
  exact hc.congr fun _ => rfl

theorem curvatureKernel_endpoint_of_rank_stable
    (A : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (b : ℝ)
    (hA : ContinuousWithinAt A (Set.Iio b) b)
    (hself : (A b).IsHermitian)
    (K : Submodule ℝ (Fin 3 → ℝ))
    (hfixed : ∀ᶠ t in 𝓝[<] b, LinearMap.ker (A t).mulVecLin = K)
    (hdim : Module.finrank ℝ K = Module.finrank ℝ (LinearMap.ker (A b).mulVecLin))
    (hnull : ∀ᶠ t in 𝓝[<] b, LinearMap.ker (A t).mulVecLin ≤
      LinearMap.ker (hamiltonIveyMatrixReaction (A t)).mulVecLin) :
    K = LinearMap.ker (A b).mulVecLin ∧
      LinearMap.ker (A b).mulVecLin ≤
        LinearMap.ker (hamiltonIveyMatrixReaction (A b)).mulVecLin ∧
      ((A b).rank = 0 ∨ (A b).rank = 1 ∨ (A b).rank = 3) := by
  have hle : K ≤ LinearMap.ker (A b).mulVecLin := by
    intro v hv
    have hlim : Tendsto (fun t => A t *ᵥ v) (𝓝[<] b) (𝓝 (A b *ᵥ v)) :=
      ((matrix_eval_continuous v).tendsto (A b)).comp hA
    have hzero : ∀ᶠ t in 𝓝[<] b, A t *ᵥ v = 0 := by
      filter_upwards [hfixed] with t ht
      change v ∈ LinearMap.ker (A t).mulVecLin
      rw [ht]
      exact hv
    change A b *ᵥ v = 0
    exact tendsto_nhds_unique hlim
      (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hzero))
  have hkernel : K = LinearMap.ker (A b).mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq hle hdim
  have hQ : ContinuousWithinAt (fun t => hamiltonIveyMatrixReaction (A t))
      (Set.Iio b) b :=
    curvature_reaction_continuous.continuousAt.comp_continuousWithinAt hA
  have hleQ : K ≤ LinearMap.ker (hamiltonIveyMatrixReaction (A b)).mulVecLin := by
    intro v hv
    have hlim : Tendsto (fun t => hamiltonIveyMatrixReaction (A t) *ᵥ v)
        (𝓝[<] b) (𝓝 (hamiltonIveyMatrixReaction (A b) *ᵥ v)) :=
      ((matrix_eval_continuous v).tendsto (hamiltonIveyMatrixReaction (A b))).comp hQ
    have hzero : ∀ᶠ t in 𝓝[<] b, hamiltonIveyMatrixReaction (A t) *ᵥ v = 0 := by
      filter_upwards [hfixed, hnull] with t hker hreaction
      apply hreaction
      rw [hker]
      exact hv
    change hamiltonIveyMatrixReaction (A b) *ᵥ v = 0
    exact tendsto_nhds_unique hlim
      (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hzero))
  have hnullb : LinearMap.ker (A b).mulVecLin ≤
      LinearMap.ker (hamiltonIveyMatrixReaction (A b)).mulVecLin := by
    simpa only [hkernel] using hleQ
  exact ⟨hkernel, hnullb,
    curvatureOperator_rank_trichotomy_of_null_reaction (A b) hself hnullb⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
