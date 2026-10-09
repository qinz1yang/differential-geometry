import DifferentialGeometry.Topology.Manifold.ClosedBall.ChartMap
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

set_option autoImplicit false
noncomputable section

open DifferentialGeometry Set
open scoped Manifold ContDiff

local notation "D" =>
  (TopologicalSpace.Opens.mk (Metric.ball (0 : ℂ) 1) Metric.isOpen_ball :
    TopologicalSpace.Opens ℂ)
local notation "C" => DifferentialGeometry.Topology.ClosedCell 2

private local instance : ChartedSpace (EuclideanHalfSpace 2) C :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

private local instance : IsManifold (𝓡∂ 2) ∞ C :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

namespace DifferentialGeometry.Geometry.Metric

private theorem mem_closedCell_two_interior_iff (x : C) :
    x ∈ (𝓡∂ 2).interior C ↔ ‖x.val‖ < 1 := by
  rw [← ModelWithCorners.compl_boundary (I := 𝓡∂ 2) (M := C),
    DifferentialGeometry.Topology.Manifold.closedCell_boundary_eq_sphere 1]
  change ‖x.val‖ ≠ 1 ↔ ‖x.val‖ < 1
  exact ⟨fun hx => lt_of_le_of_ne x.property hx, ne_of_lt⟩

/-- A compact ball for the original metric lies in the interior of a scaled
closed disk carrying the literal pullback of that same metric. -/
theorem exists_closedCell_pullback_containing_riemannianClosedBallOf
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℂ) D) (p : D) {r : ℝ}
    (hcompact : IsCompact (riemannianClosedBallOf g p r)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      ∃ (j : C → D)
        (hj : ContMDiff (𝓡∂ 2) 𝓘(ℝ, ℂ) ∞ j)
        (himm : ∀ x : C,
          Function.Injective (mfderiv (𝓡∂ 2) 𝓘(ℝ, ℂ) j x))
        (gAux : SmoothRiemannianMetric (𝓡∂ 2) C),
        (∀ x : C, (j x : ℂ) =
          ρ • Complex.orthonormalBasisOneI.repr.symm x.val) ∧
        Function.Injective j ∧
        Set.range j = {z : D | ‖(z : ℂ)‖ ≤ ρ} ∧
        j '' ((𝓡∂ 2).interior C) = {z : D | ‖(z : ℂ)‖ < ρ} ∧
        riemannianClosedBallOf g p r ⊆ j '' ((𝓡∂ 2).interior C) ∧
        gAux = g.pullback j hj himm := by
  classical
  let K : Set ℂ := (Subtype.val : D → ℂ) '' riemannianClosedBallOf g p r
  have hK : IsCompact K := hcompact.image continuous_subtype_val
  have hKsub : K ⊆ Metric.ball (0 : ℂ) 1 := by
    rintro z ⟨x, _, rfl⟩
    exact x.property
  obtain ⟨ρ, hρ, hinside⟩ :=
    exists_pos_lt_subset_ball (show (0 : ℝ) < 1 by norm_num) hK.isClosed hKsub
  let L : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ :=
    Complex.orthonormalBasisOneI.repr.symm
  let A : ℂ ≃L[ℝ] ℂ := ContinuousLinearEquiv.smulLeft (Units.mk0 ρ hρ.1.ne')
  let e : EuclideanSpace ℝ (Fin 2) ≃ᴬ[ℝ] ℂ :=
    (L.toContinuousLinearEquiv.trans A).toContinuousAffineEquiv
  have he_apply (x : EuclideanSpace ℝ (Fin 2)) : e x = ρ • L x := rfl
  have he_norm (x : EuclideanSpace ℝ (Fin 2)) : ‖e x‖ = ρ * ‖x‖ := by
    rw [he_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hρ.1, L.norm_map]
  have he_inv_norm (z : ℂ) : ρ * ‖e.symm z‖ = ‖z‖ := by
    rw [← he_norm, e.apply_symm_apply]
  have he_mem (x : C) : e x.val ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, he_norm]
    exact ((mul_le_mul_of_nonneg_left x.property hρ.1.le).trans_eq (mul_one ρ)).trans_lt
      hρ.2
  let j : C → D := fun x => ⟨e x.val, he_mem x⟩
  have he_chart (x : C) :
      e x.val ∈ interior (extChartAt 𝓘(ℝ, ℂ) (0 : ℂ)).target := by
    rw [extChartAt_model_space_eq_id]
    simp only [PartialEquiv.refl_target, interior_univ, mem_univ]
  have hsmooth : ContMDiff (𝓡∂ 2) 𝓘(ℝ, ℂ) ∞ (fun x : C => e x.val) := by
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
      PartialEquiv.refl_coe, id_eq] using
      DifferentialGeometry.Topology.Manifold.contMDiff_extChartAt_symm_comp_affine_closedCell
        (m := 1) (k := (⊤ : ℕ∞)) (0 : ℂ) e he_chart
  have hj : ContMDiff (𝓡∂ 2) 𝓘(ℝ, ℂ) ∞ j :=
    (ContMDiff.subtypeVal_comp_iff D j).mp hsmooth
  have himm (x : C) : Function.Injective (mfderiv (𝓡∂ 2) 𝓘(ℝ, ℂ) j x) := by
    rw [← DifferentialGeometry.mfderiv_subtypeVal_comp
      (I := 𝓡∂ 2) (J := 𝓘(ℝ, ℂ)) j x]
    change Function.Injective (mfderiv (𝓡∂ 2) 𝓘(ℝ, ℂ) (fun y : C => e y.val) x)
    have hmap :
        (fun y : C => (extChartAt 𝓘(ℝ, ℂ) (0 : ℂ)).symm (e y.val)) =
          (fun y : C => e y.val) := by
      funext y
      simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
        PartialEquiv.refl_coe, id_eq]
    have hchart :=
      DifferentialGeometry.Topology.Manifold.injective_mfderiv_extChartAt_symm_comp_affine_closedCell
        (m := 1) (0 : ℂ) e (x := x) (he_chart x)
    exact (congrArg (fun f : C → ℂ =>
      Function.Injective (mfderiv (𝓡∂ 2) 𝓘(ℝ, ℂ) f x)) hmap).mp hchart
  have hinj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    apply e.injective
    exact congrArg (fun z : D => (z : ℂ)) hxy
  have hrange : Set.range j = {z : D | ‖(z : ℂ)‖ ≤ ρ} := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      change ‖e x.val‖ ≤ ρ
      rw [he_norm]
      exact (mul_le_mul_of_nonneg_left x.property hρ.1.le).trans_eq (mul_one ρ)
    · intro hz
      change ‖(z : ℂ)‖ ≤ ρ at hz
      have hy : ‖e.symm (z : ℂ)‖ ≤ 1 := by
        exact le_of_mul_le_mul_left (a := ρ)
          (by simpa only [he_inv_norm, mul_one] using hz) hρ.1
      refine ⟨⟨e.symm (z : ℂ), hy⟩, ?_⟩
      apply Subtype.ext
      exact e.apply_symm_apply (z : ℂ)
  have hinterior :
      j '' ((𝓡∂ 2).interior C) = {z : D | ‖(z : ℂ)‖ < ρ} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ‖e x.val‖ < ρ
      rw [he_norm]
      simpa only [mul_one] using
        mul_lt_mul_of_pos_left ((mem_closedCell_two_interior_iff x).mp hx) hρ.1
    · intro hz
      change ‖(z : ℂ)‖ < ρ at hz
      have hy : ‖e.symm (z : ℂ)‖ < 1 := by
        exact lt_of_mul_lt_mul_left (a := ρ)
          (by simpa only [he_inv_norm, mul_one] using hz) hρ.1.le
      let x : C := ⟨e.symm (z : ℂ), hy.le⟩
      refine ⟨x, (mem_closedCell_two_interior_iff x).mpr hy, ?_⟩
      apply Subtype.ext
      exact e.apply_symm_apply (z : ℂ)
  have hball : riemannianClosedBallOf g p r ⊆ j '' ((𝓡∂ 2).interior C) := by
    rw [hinterior]
    intro z hz
    change ‖(z : ℂ)‖ < ρ
    have hzK : (z : ℂ) ∈ K := ⟨z, hz, rfl⟩
    simpa only [Metric.mem_ball, dist_zero_right] using hinside hzK
  refine ⟨ρ, hρ.1, hρ.2, j, hj, himm, g.pullback j hj himm,
    ?_, hinj, hrange, hinterior, hball, rfl⟩
  intro x
  exact he_apply x.val

end DifferentialGeometry.Geometry.Metric
