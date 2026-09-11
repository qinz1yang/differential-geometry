import DifferentialGeometry.Geometry.Curvature.TraceNormalizedOperator
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature

set_option autoImplicit false
noncomputable section
open Bundle Manifold DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff InnerProductSpace BigOperators
namespace DifferentialGeometry.Geometry.Curvature
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private theorem exists_pair_of_bivector_coordinates (c : Fin 3 → ℝ) :
    ∃ u v : Fin 3 → ℝ, ∀ i : Fin 3,
      u (bivectorIndex3 i).1 * v (bivectorIndex3 i).2 -
        u (bivectorIndex3 i).2 * v (bivectorIndex3 i).1 = c i := by
  by_cases ha : c 0 = 0
  · by_cases hb : c 1 = 0
    · refine ⟨![0, 1, 0], ![0, 0, c 2], ?_⟩
      intro i
      fin_cases i <;> simp [bivectorIndex3, ha, hb]
    · refine ⟨![1, c 2 / c 1, 0], ![0, 0, c 1], ?_⟩
      intro i
      fin_cases i <;> simp [bivectorIndex3, ha, hb]
  · refine ⟨![1, 0, -(c 2 / c 0)], ![0, c 0, c 1], ?_⟩
    intro i
    fin_cases i <;> simp [bivectorIndex3, ha]

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [I.Boundaryless] [BoundarylessManifold I M] in
private theorem exists_pair_for_curvature_quadratic
    (g : SmoothRiemannianMetric I M) (x : M)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace I x)) (hB : OrthonormalBasisAt g x B)
    (c : Fin 3 → ℝ) :
    ∃ u v : TangentSpace I x,
      (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 = ∑ i : Fin 3, c i ^ 2) ∧
      metricRm04StandardAt g x u v v u = ∑ i : Fin 3, ∑ j : Fin 3,
        c i * c j * curvatureOperatorMatrixAt x B (metricAlgebraicCurvatureTensorAt g x) i j := by
  obtain ⟨a, b, hab⟩ := exists_pair_of_bivector_coordinates c
  let u := B.equivFun.symm a
  let v := B.equivFun.symm b
  have hu : ∀ i, B.repr u i = a i := fun i => congrArg (fun f => f i) (B.equivFun.apply_symm_apply a)
  have hv : ∀ i, B.repr v i = b i := fun i => congrArg (fun f => f i) (B.equivFun.apply_symm_apply b)
  have hcoeff : ∀ i : Fin 3,
      (∑ k : Fin 1, (1 : ℝ) *
        (B.repr ((fun _ : Fin 1 => u) k) (bivectorIndex3 i).1 *
          B.repr ((fun _ : Fin 1 => v) k) (bivectorIndex3 i).2 -
          B.repr ((fun _ : Fin 1 => u) k) (bivectorIndex3 i).2 *
          B.repr ((fun _ : Fin 1 => v) k) (bivectorIndex3 i).1)) = c i := by
    intro i
    simpa only [Fin.sum_univ_one, one_mul, hu, hv] using hab i
  have hgram := algebraicCurvatureIdentityQuadraticEval_eq_bivectorNormSq g x
    (fun _ : Fin 1 => (1 : ℝ)) (fun _ => u) (fun _ => v) B hB
  have hquad := algebraicCurvatureOperatorQuadraticEval_eq_bivectorQuad x B
    (metricAlgebraicCurvatureTensorAt g x) (fun _ : Fin 1 => (1 : ℝ)) (fun _ => u) (fun _ => v)
  simp_rw [hcoeff] at hgram hquad
  refine ⟨u, v, ?_, ?_⟩
  · simpa only [algebraicCurvatureIdentityQuadraticEval, Fin.sum_univ_one, one_mul,
      g.symm x v u, pow_two] using hgram
  · simpa only [algebraicCurvatureOperatorQuadraticEval, Fin.sum_univ_one, one_mul,
      metricAlgebraicCurvatureTensorAt_coe, metricRm04StandardAt] using hquad

omit [BoundarylessManifold I M] in
theorem traceNormalizedCurvatureOperatorAt_inner_self_nonneg_of_sectionalCurvature_nonneg
    (g : SmoothRiemannianMetric I M) (x : M)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace I x)) (hB : OrthonormalBasisAt g x B)
    (hsec : ∀ u v : TangentSpace I x,
      g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 ≠ 0 →
      0 ≤ sectionalCurvature g x u v) (c : E3) :
    0 ≤ ⟪traceNormalizedCurvatureOperatorAt g x B c, c⟫_ℝ := by
  by_cases hc : c = 0
  · simp [hc]
  obtain ⟨u, v, hgram, hquad⟩ := exists_pair_for_curvature_quadratic g x B hB c.ofLp
  have hsum : 0 < ∑ i : Fin 3, c.ofLp i ^ 2 := by
    rw [← EuclideanSpace.real_norm_sq_eq c]
    exact sq_pos_of_pos (norm_pos_iff.mpr hc)
  have harea : 0 < g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 := by
    rw [hgram]
    exact hsum
  have hr := hsec u v (ne_of_gt harea)
  rw [sectionalCurvature_eq_metricRm04StandardAt_div] at hr
  have hR : 0 ≤ metricRm04StandardAt g x u v v u := by
    have hm := mul_nonneg hr harea.le
    rwa [div_mul_cancel₀ _ (ne_of_gt harea)] at hm
  rw [traceNormalizedCurvatureOperatorAt_inner_self]
  have heq : (∑ i : Fin 3, ∑ j : Fin 3, c i * c j *
      metricRm04StandardAt g x (B (bivectorIndex3 i).1) (B (bivectorIndex3 i).2)
        (B (bivectorIndex3 j).2) (B (bivectorIndex3 j).1)) = metricRm04StandardAt g x u v v u :=
    hquad.symm
  rw [heq]
  positivity

omit [BoundarylessManifold I M] in
theorem iInf_rayleigh_traceNormalizedCurvatureOperatorAt_nonneg_of_sectionalCurvature_nonneg
    (g : SmoothRiemannianMetric I M) (x : M)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace I x)) (hB : OrthonormalBasisAt g x B)
    (hsec : ∀ u v : TangentSpace I x,
      g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 ≠ 0 →
      0 ≤ sectionalCurvature g x u v) :
    0 ≤ ⨅ c : {c : E3 // c ≠ 0}, (traceNormalizedCurvatureOperatorAt g x B).rayleighQuotient c := by
  apply Real.iInf_nonneg
  intro c
  change 0 ≤ ⟪traceNormalizedCurvatureOperatorAt g x B c.val, c.val⟫_ℝ / ‖c.val‖ ^ 2
  exact div_nonneg
    (traceNormalizedCurvatureOperatorAt_inner_self_nonneg_of_sectionalCurvature_nonneg g x B hB hsec c)
    (sq_nonneg _)

omit [BoundarylessManifold I M] in
theorem leastCurvatureOperatorEigenvalueAt_nonneg_of_sectionalCurvature_nonneg
    (g : SmoothRiemannianMetric I M) (x : M)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace I x)) (hB : OrthonormalBasisAt g x B)
    (hsec : ∀ u v : TangentSpace I x,
      g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 ≠ 0 →
      0 ≤ sectionalCurvature g x u v) :
    0 ≤ leastCurvatureOperatorEigenvalueAt g x (metricAlgebraicCurvatureTensorAt g x) := by
  have h := iInf_rayleigh_traceNormalizedCurvatureOperatorAt_nonneg_of_sectionalCurvature_nonneg g x B hB hsec
  rw [iInf_rayleigh_traceNormalizedCurvatureOperatorAt g x B hB] at h
  linarith

end DifferentialGeometry.Geometry.Curvature
