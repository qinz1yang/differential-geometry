import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryWholeFibreConnected

/-!
# G17 kernel (e): a compiled consumer on the model circle bundle (S-BAUG-D2)

`modelCircleBundle_adjusted_level_BAUGD`: `connected_adjusted_level_of_isotopy_BAUGD` and
`exists_embedding_adjusted_level_BAUGD` on `ℝ² × S¹` with `η = g = fst` (`U = univ`, `ℓ = 1`,
`a = 0`, `c = 0`, the right inverse `inl`, the gauge `ν = ‖·‖`): the adjusted level `{0} × S¹` is
connected, and it is the image of a smooth embedding of `S¹` whenever the original one is
(the two hypotheses of the kernels — right inverse, compact trace, closeness — are satisfiable).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Topology Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- **The model circle bundle through the FC34 kernels**: with `η = g = fst : ℝ² × S¹ → ℝ²` the
whole adjusted level over `0` is connected and a smooth circle. -/
theorem modelCircleBundle_adjusted_level_BAUGD :
    IsConnected {y : ℝ² × Circle | y ∈ (univ : Set (ℝ² × Circle)) ∧
      (Prod.fst : ℝ² × Circle → ℝ²) y = 0} ∧
    (∀ e₀ : Circle → ℝ² × Circle, IsSmoothEmbedding (𝓡 1) ((𝓡 2).prod (𝓡 1)) ∞ e₀ →
      range e₀ = {y | y ∈ (univ : Set (ℝ² × Circle)) ∧ (Prod.fst : ℝ² × Circle → ℝ²) y = 0} →
      ∃ ψ : Circle → ℝ² × Circle, IsSmoothEmbedding (𝓡 1) ((𝓡 2).prod (𝓡 1)) ∞ ψ ∧
        range ψ = {y | y ∈ (univ : Set (ℝ² × Circle)) ∧
          (Prod.fst : ℝ² × Circle → ℝ²) y = 0}) := by
  have hdim : Module.finrank ℝ ℝ² < Module.finrank ℝ (ℝ² × EuclideanSpace ℝ (Fin 1)) := by
    simp [Module.finrank_prod]
  have hsm : ContMDiffOn ((𝓡 2).prod (𝓡 1)) 𝓘(ℝ, ℝ²) ∞
      (Prod.fst : ℝ² × Circle → ℝ²) univ := contMDiff_fst.contMDiffOn
  have hQ : IsCompact {y : ℝ² × Circle | y ∈ (univ : Set (ℝ² × Circle)) ∧
      ‖(Prod.fst : ℝ² × Circle → ℝ²) y‖ ≤ 401 / 100 * 1} := by
    have : {y : ℝ² × Circle | y ∈ (univ : Set (ℝ² × Circle)) ∧
        ‖(Prod.fst : ℝ² × Circle → ℝ²) y‖ ≤ 401 / 100 * 1} =
        closedBall (0 : ℝ²) (401 / 100 * 1) ×ˢ (univ : Set Circle) := by
      ext p
      simp
    rw [this]
    exact (isCompact_closedBall _ _).prod isCompact_univ
  have hright : ∀ y ∈ (univ : Set (ℝ² × Circle)), ∃ R : ℝ² →L[ℝ] (ℝ² × EuclideanSpace ℝ (Fin 1)),
      (show (ℝ² × EuclideanSpace ℝ (Fin 1)) →L[ℝ] ℝ² from
        mfderiv ((𝓡 2).prod (𝓡 1)) 𝓘(ℝ, ℝ²) (Prod.fst : ℝ² × Circle → ℝ²) y).comp R =
          ContinuousLinearMap.id ℝ ℝ² ∧
      ∀ w, ‖R w‖ ≤ 1 * ‖w‖ := by
    intro y _
    refine ⟨ContinuousLinearMap.inl ℝ ℝ² (EuclideanSpace ℝ (Fin 1)), ?_, fun w => ?_⟩
    · have h : mfderiv ((𝓡 2).prod (𝓡 1)) 𝓘(ℝ, ℝ²) (Prod.fst : ℝ² × Circle → ℝ²) y =
          ContinuousLinearMap.fst ℝ ℝ² (EuclideanSpace ℝ (Fin 1)) := mfderiv_fst
      ext w
      simp [h]
    · simp
  have hconn : IsConnected {y : ℝ² × Circle | y ∈ (univ : Set (ℝ² × Circle)) ∧
      (Prod.fst : ℝ² × Circle → ℝ²) y = 0} := by
    have : {y : ℝ² × Circle | y ∈ (univ : Set (ℝ² × Circle)) ∧
        (Prod.fst : ℝ² × Circle → ℝ²) y = 0} = ({0} : Set ℝ²) ×ˢ (univ : Set Circle) := by
      ext p
      simp
    rw [this]
    exact isConnected_singleton.prod isConnected_univ
  refine ⟨connected_adjusted_level_of_isotopy_BAUGD (I := (𝓡 2).prod (𝓡 1)) hdim isOpen_univ hsm
    hsm (a := (0 : ℝ²)) (ℓ := 1) le_rfl (by simp) (fun y _ => by simp) (fun _ v => ‖v‖)
    (le_refl 0) (by simp) (fun y hy => hright y hy) (fun y _ v => by simp) hQ hconn,
    fun e₀ he₀ he₀r => ?_⟩
  exact exists_embedding_adjusted_level_BAUGD (I := (𝓡 2).prod (𝓡 1)) hdim isOpen_univ hsm hsm
    (a := (0 : ℝ²)) (ℓ := 1) le_rfl (by simp) (fun y _ => by simp) (fun _ v => ‖v‖)
    (le_refl 0) (by simp) (fun y hy => hright y hy) (fun y _ v => by simp) hQ (𝓡 1) e₀ he₀ he₀r

end DifferentialGeometry.Geometry.Collapse
