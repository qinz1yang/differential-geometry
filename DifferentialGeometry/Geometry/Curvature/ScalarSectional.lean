import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.ContractedBianchi
import DifferentialGeometry.Geometry.Curvature.Coordinates.RiemannTensorBridge
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature
import DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric

set_option autoImplicit false

noncomputable section
open Bundle DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Riemannian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] in
theorem metricScalarAt_eq_sum_metricRm04StandardAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    metricScalarAt g x = ∑ i, ∑ j, metricRm04StandardAt g x (B j) (B i) (B i) (B j) := by
  rw [metricScalar_eq_scal, scalarCurv_eq_orthonormal_trace g x B hB]
  apply Finset.sum_congr rfl
  intro i _
  rw [ricciTensor_eq_orthonormal_trace g x (B i) (B i) B hB]
  apply Finset.sum_congr rfl
  intro j _
  exact (g.symm x _ _).trans (rm04_eq_inner_riem g x (B j) (B i) (B i) (B j)).symm

theorem metricScalarAt_of_constant_sectional
    (g : SmoothRiemannianMetric I M) (x : M) (c : ℝ)
    (h : ∀ u v : TangentSpace I x, metricRm04StandardAt g x u v v u =
      c * (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2)) :
    metricScalarAt g x = (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) * c := by
  classical
  let B : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x
  have hB : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  rw [metricScalarAt_eq_sum_metricRm04StandardAt g x B hB]
  simp only [h, hB]
  simp [mul_sub, Finset.sum_sub_distrib]
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem metricScalarAt_pos_of_sectionalCurvature_pos
    (g : SmoothRiemannianMetric I M) (x : M) (hdim : 2 ≤ Module.finrank ℝ E)
    (hpos : ∀ u v : TangentSpace I x,
      g.inner x u u * g.inner x v v - g.inner x u v ^ 2 ≠ 0 →
      0 < sectionalCurvature g x u v) : 0 < metricScalarAt g x := by
  let : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let B : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x
  have hB : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hoff (i j : Fin (Module.finrank ℝ E)) (hij : i ≠ j) :
      0 < metricRm04StandardAt g x (B j) (B i) (B i) (B j) := by
    have hs := hpos (B j) (B i) (by simp [hB, hij.symm])
    rw [sectionalCurvature_eq_metricRm04StandardAt_of_unit_orthogonal g x (B j) (B i)
      (by simpa using hB j j) (by simpa using hB i i)
      (by simpa only [if_neg hij.symm] using hB j i)] at hs
    exact hs
  have hdiag (i : Fin (Module.finrank ℝ E)) : metricRm04StandardAt g x (B i) (B i) (B i) (B i) = 0 := by
    have ha := (mem_algebraicCurvatureTensorSubmodule_iff_symmetries.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule g x)).1 (B i) (B i) (B i) (B i)
    change metricRm04StandardAt g x (B i) (B i) (B i) (B i) =
      -metricRm04StandardAt g x (B i) (B i) (B i) (B i) at ha
    linarith
  have hnonneg (i j : Fin (Module.finrank ℝ E)) :
      0 ≤ metricRm04StandardAt g x (B j) (B i) (B i) (B j) := by
    by_cases hij : i = j
    · subst j
      rw [hdiag]
    · exact (hoff i j hij).le
  rw [metricScalarAt_eq_sum_metricRm04StandardAt g x B hB]
  apply Finset.sum_pos'
  · intro i _
    exact Finset.sum_nonneg (fun j _ => hnonneg i j)
  · let i : Fin (Module.finrank ℝ E) := ⟨0, by omega⟩
    let j : Fin (Module.finrank ℝ E) := ⟨1, by omega⟩
    refine ⟨i, Finset.mem_univ _, ?_⟩
    apply Finset.sum_pos'
    · exact fun k _ => hnonneg i k
    · exact ⟨j, Finset.mem_univ _, hoff i j (by simp [i, j])⟩

end DifferentialGeometry.Geometry.Riemannian
