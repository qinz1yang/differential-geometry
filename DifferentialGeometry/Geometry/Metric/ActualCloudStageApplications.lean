import DifferentialGeometry.Geometry.Metric.ActualCloudStagePreservation
import DifferentialGeometry.Geometry.Metric.ActualCloudContributorApplications

/-! Consumer of CFS29's stage kernel on explicit data in `ℝ³`: blocks `span{e₀}` (`R = 1`), `span{e₁}` (`R = 1/100`,
small) and `span{e₂}` (`R = 1`), original image `e₀` at scale `ρ = 1`, an input perturbed by `10⁻⁴ e₂` (within
`3Σ/10`, `Σ = 1/640`), the stage projection `z ↦ z₀ e₀` (its small block vanishes on the core ball), and the half
blend `ψ = 1/2`. The blended adjustment moves the input but keeps the small marker exactly zero. -/

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis

namespace GC.MetricGeometry

/-- CFS29 consumer: the blended output differs from the input, and its small (`e₁`) block is zero. -/
theorem actualCloud_stage_preservation_consumer :
    let e : Fin 3 → EuclideanSpace ℝ (Fin 3) := fun j => EuclideanSpace.single j 1
    let V : Fin 3 → Submodule ℝ (EuclideanSpace ℝ (Fin 3)) := fun j => ℝ ∙ e j
    let Pst : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) := fun z => z 0 • e 0
    let y : EuclideanSpace ℝ (Fin 3) := e 0 + (1 / 10000 : ℝ) • e 2
    (V 1).starProjection (adjustmentMap ⊤ Pst (fun _ => 1 / 2) y) = 0 ∧
      adjustmentMap ⊤ Pst (fun _ => 1 / 2) y ≠ y := by
  intro e V Pst y
  let coord : Fin 3 → EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ := fun j => innerSL ℝ (e j)
  have hcoord : ∀ j z, coord j z = z j := by
    intro j z
    simp only [coord, e, innerSL_apply_apply, EuclideanSpace.inner_single_left, map_one, one_mul]
  have he00 : e 0 0 = 1 := by simp [e]
  have he01 : e 0 1 = 0 := by simp [e]
  have he02 : e 0 2 = 0 := by simp [e]
  have he20 : e 2 0 = 0 := by simp [e]
  have he21 : e 2 1 = 0 := by simp [e]
  have he22 : e 2 2 = 1 := by simp [e]
  have hproj_zero : ∀ (j : Fin 3) (z : EuclideanSpace ℝ (Fin 3)), z j = 0 →
      (V j).starProjection z = 0 := by
    intro j z hz
    apply ((V j).starProjection_apply_eq_zero_iff).mpr
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, ← innerSL_apply_apply (𝕜 := ℝ)]
    change coord j z = 0
    rw [hcoord, hz]
  have htop : ∀ z : EuclideanSpace ℝ (Fin 3), (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))).starProjection z = z :=
    fun z => Submodule.starProjection_eq_self_iff.mpr Submodule.mem_top
  let R : Fin 3 → ℝ := ![1, 1 / 100, 1]
  have hR0 : R 0 = 1 := rfl
  have hR1 : R 1 = 1 / 100 := rfl
  have hR2 : R 2 = 1 := rfl
  have hsmall : ∀ i : Fin 3, R i < 1 / 16 → i = 1 := by
    intro i hi
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, hR0] at hi; norm_num at hi
    · rfl
    · simp only [Fin.reduceFinMk, hR2] at hi; norm_num at hi
  have hyerr : ‖y - e 0‖ ≤ (3 * (1 / 640 : ℝ) / 10) * 1 := by
    simp only [y, add_sub_cancel_left, norm_smul, e, PiLp.norm_single, norm_one, mul_one,
      Real.norm_eq_abs]
    norm_num
  have hres := actualCloud_stage_small_marker_preservation (M := Unit) ⊤ Pst
    (fun _ => Submodule.mem_top) (fun _ => (1 / 2 : ℝ)) (fun _ => e 0) (fun _ => y) (fun _ => 1) V
    (fun j z => coord j z) R
    (by intro j; fin_cases j <;> simp [R])
    (by
      intro j q hpos
      rw [htop] at hpos
      fin_cases j
      · simp only [Fin.zero_eta, Fin.isValue, hR0]; norm_num
      · simp only [Fin.mk_one, Fin.isValue, hcoord, he01] at hpos
        exact absurd hpos (lt_irrefl 0)
      · simp only [Fin.reduceFinMk, Fin.isValue, hcoord, he02] at hpos
        exact absurd hpos (lt_irrefl 0))
    (fun _ _ => ⟨0, by rw [htop, hcoord, he00, hR0]⟩)
    {e 0} (fun _ => ()) (by intro x hx; rw [htop]; exact hx.symm)
    (σ := 1 / 640) (e := 3 * (1 / 640) / 10) (by norm_num) le_rfl
    (fun q _ => by rw [htop]; exact rfl)
    (fun q _ => hyerr)
    (by
      intro x _ z _ q _ i hi
      have hi1 := hsmall i (by simpa using hi)
      subst hi1
      apply hproj_zero
      simp only [Pst, PiLp.smul_apply, smul_eq_mul, he01, mul_zero])
    (fun _ => Or.inl le_top)
    (by
      intro q i hi
      have hi1 := hsmall i (by simpa using hi)
      subst hi1
      apply hproj_zero
      simp only [y, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, he01, he21, mul_zero, add_zero])
    () 1 (by rw [hR1]; norm_num)
  refine ⟨hres, ?_⟩
  intro heq
  have h2 := congrArg (fun z : EuclideanSpace ℝ (Fin 3) => z 2) heq
  simp only [adjustmentMap_apply, htop, Pst, y, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
    smul_eq_mul, he00, he02, he20, he22] at h2
  norm_num at h2

end GC.MetricGeometry
