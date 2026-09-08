import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Smoothness
import DifferentialGeometry.Tensor.Alternating.Trace
import Mathlib.LinearAlgebra.Trace

set_option autoImplicit false
noncomputable section
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.Geometry.Curvature
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

noncomputable local instance scalarTwoFormFiniteDimensional (x : M) :
    FiniteDimensional Real (TangentSpace I x [⋀^Fin 2]→L[Real] Real) :=
  (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2)
    (Module.finBasis Real (TangentSpace I x))).finiteDimensional_of_finite

omit [T2Space M] in
private theorem curvatureOperatorEndomorphismAt_pair_apply_orthonormal
    {n : ℕ} (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) (i j : Fin n) :
    curvatureOperatorEndomorphismAt (I := I) g x A
      (ContinuousAlternatingMap.elementaryCovector basis.cDualBasis ![i,j])
      ![basis i,basis j] =
      (A : Tensor0SSpace 4 I x) ![basis i,basis j,basis j,basis i] := by
  rw [curvatureOperatorEndomorphismAt_elementaryCovector_apply g x basis horth A]
  have hlast := (mem_algebraicCurvatureTensorSubmodule_iff_symmetries.mp A.property).2.1
    (basis i) (basis j) (basis i) (basis j)
  have hvec (v w z u : TangentSpace I x) :
      tensor04StdAt (A : Tensor0SSpace 4 I x) v w z u =
        (A : Tensor0SSpace 4 I x) ![v,w,z,u] := by
    unfold tensor04StdAt
    congr 1
    funext q
    fin_cases q <;> rfl
  simp only [hvec] at hlast
  linarith

private theorem metricScalarAt_eq_sum_rm04_orthonormal
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0) :
    metricScalarAt (I := I) g x =
      ∑ i : Idx, ∑ a : Idx,
        metricRm04 (I := I) (M := M) g x
          (vec4 (basis a) (basis i) (basis i) (basis a)) := by
  rw [metricScalarAt_def, Operator.metricTracePair0SAt_eq_sum_basis
    (I := I) g basis (identityInvMetric (Idx := Idx))
    (metricInverseInBasis_identity_of_orthonormal g basis horth)]
  simp only [identityInvMetric, diagonalInvMetric, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro i _
  exact ricci_diag_eq_sum_rm04_diag_of_orthonormal (I := I) g basis
    (metricRicci (I := I) g) (metricRm13 (I := I) g) (metricRm04 (I := I) g)
    (metricCurvData (I := I) g).ricciRealizes
    (rm04LowersRm13At_of_realizes (I := I) g (metricCov (I := I) g)
      (metricRm13 (I := I) g) (metricRm04 (I := I) g)
      (metricCurvData (I := I) g).rm13Realizes (metricCurvData (I := I) g).rm04Realizes x)
    horth i i

theorem trace_curvatureOperatorEndomorphismAt_eq_half_metricScalarAt
    (g : SmoothRiemannianMetric I M) (x : M) :
    LinearMap.trace Real (TangentSpace I x [⋀^Fin 2]→L[Real] Real)
      (curvatureOperatorEndomorphismAt (I := I) g x
        ⟨metricRm04 (I := I) g x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩).toLinearMap =
      metricScalarAt (I := I) g x / 2 := by
  obtain ⟨basis, horth⟩ : ∃ basis : Module.Basis
      (Fin (Module.finrank Real (TangentSpace I x))) Real (TangentSpace I x),
      ∀ i j, g.inner x (basis i) (basis j) = if i = j then 1 else 0 := by
    let D := (tangentMetricData (I := I) g x).metric
    let _ : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
    let _ : NormedAddCommGroup (TangentSpace I x) :=
      @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _ D.toCore
    let _ : InnerProductSpace Real (TangentSpace I x) :=
      @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
    let basis := stdOrthonormalBasis Real (TangentSpace I x)
    refine ⟨basis.toBasis, ?_⟩
    intro i j
    change D.inner (basis i) (basis j) = if i = j then 1 else 0
    rw [← D.toCore_inner]
    exact basis.inner_eq_ite i j
  rw [ContinuousAlternatingMap.trace_eq_half_sum_pair basis]
  simp_rw [ContinuousLinearMap.coe_coe,
    curvatureOperatorEndomorphismAt_pair_apply_orthonormal g x basis horth]
  rw [metricScalarAt_eq_sum_rm04_orthonormal g x basis horth]
  rw [Finset.sum_comm]
  simp only [div_eq_mul_inv, one_mul]
  rw [mul_comm]
  congr 1

theorem metricScalarAt_pos_of_curvatureOperator_ne_zero
    (g : SmoothRiemannianMetric I M) (x : M)
    (hpositive : ∀ a : TangentSpace I x [⋀^Fin 2]→L[Real] Real,
      0 ≤ (twoFormMetricData (I := I) g x).inner
        (curvatureOperatorEndomorphismAt (I := I) g x
          ⟨metricRm04 (I := I) g x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ a) a)
    (hne : curvatureOperatorEndomorphismAt (I := I) g x
      ⟨metricRm04 (I := I) g x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ ≠ 0) :
    0 < metricScalarAt (I := I) g x := by
  have htrace := (twoFormMetricData (I := I) g x).trace_pos_of_isSymmetric_of_nonneg_of_ne_zero
    (curvatureOperatorEndomorphismAt (I := I) g x
      ⟨metricRm04 (I := I) g x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩).toLinearMap
    (curvatureOperatorEndomorphismAt_isSymmetric (I := I) g x _) hpositive
    (fun hz => hne (ContinuousLinearMap.ext fun a => LinearMap.congr_fun hz a))
  rw [trace_curvatureOperatorEndomorphismAt_eq_half_metricScalarAt] at htrace
  linarith

theorem metricScalarAt_pos_of_curvatureOperator_rank_pos
    (g : SmoothRiemannianMetric I M) (x : M)
    (hpositive : ∀ a : TangentSpace I x [⋀^Fin 2]→L[Real] Real,
      0 ≤ (twoFormMetricData (I := I) g x).inner
        (curvatureOperatorEndomorphismAt (I := I) g x
          ⟨metricRm04 (I := I) g x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ a) a)
    (hrank : 0 < Module.finrank Real
      (curvatureOperatorImageAt (I := I) g x
        ⟨metricRm04 (I := I) g x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩)) :
    0 < metricScalarAt (I := I) g x := by
  apply metricScalarAt_pos_of_curvatureOperator_ne_zero g x hpositive
  intro hzero
  change 0 < Module.finrank Real
    (curvatureOperatorEndomorphismAt (I := I) g x
      ⟨metricRm04 (I := I) g x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩).toLinearMap.range at hrank
  rw [hzero] at hrank
  change 0 < Module.finrank Real (LinearMap.range
    (0 : (TangentSpace I x [⋀^Fin 2]→L[Real] Real) →ₗ[Real]
      (TangentSpace I x [⋀^Fin 2]→L[Real] Real))) at hrank
  rw [LinearMap.range_zero, finrank_bot] at hrank
  exact (lt_irrefl 0) hrank

end DifferentialGeometry.Geometry.Curvature
