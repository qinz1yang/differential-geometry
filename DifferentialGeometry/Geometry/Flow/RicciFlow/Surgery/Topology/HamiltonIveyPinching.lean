import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PinchingDatum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]

private theorem csInf_two_mul_matrix_rayleigh_eq
    (g : SmoothRiemannianMetric ThreeModel X) (x : X)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace ThreeModel x))
    (hB : OrthonormalBasisAt g x B) :
    sInf {r : ℝ | ∃ v : Fin 3 → ℝ, (∑ i, (v i)^2) = 1 ∧
      r = 2 * ∑ i, ∑ j, v i * tensor04CurvatureOperatorMatrixAt B (metricRm04At g x) i j * v j} =
        2 * leastCurvatureOperatorEigenvalueAt g x (metricAlgebraicCurvatureTensorAt g x) := by
  let A := metricAlgebraicCurvatureTensorAt g x
  have hquad (v : Fin 3 → ℝ) :
      (∑ i, ∑ j, v i * tensor04CurvatureOperatorMatrixAt B (metricRm04At g x) i j * v j) =
      algebraicCurvatureOperatorQuadraticEval A v
        (fun i => B (bivectorIndex3 i).1) (fun i => B (bivectorIndex3 i).2) := by
    rw [algebraicCurvatureOperatorQuadraticEval_eq_matrixQuad]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change v i * curvatureOperatorMatrixAt x B A i j * v j =
      v i * v j * curvatureOperatorMatrixAt x B A i j
    ring
  have hleast : IsLeast
      {r : ℝ | ∃ v : Fin 3 → ℝ, (∑ i, (v i)^2) = 1 ∧
        r = 2 * ∑ i, ∑ j, v i * tensor04CurvatureOperatorMatrixAt B (metricRm04At g x) i j * v j}
      (2 * leastCurvatureOperatorEigenvalueAt g x A) := by
    constructor
    · obtain ⟨v, hv, heq⟩ := exists_leastCurvatureOperatorEigenvalueAt_rayleigh_minimizer g x B hB A
      refine ⟨v, ?_, ?_⟩
      · simpa only [algebraicCurvatureIdentityQuadraticEval_bivectorBasis g x B hB] using hv
      · rw [hquad, heq]
    · rintro r ⟨v, hv, rfl⟩
      have hb := leastCurvatureOperatorEigenvalueAt_mul_identity_le g x B hB A v
        (fun i => B (bivectorIndex3 i).1) (fun i => B (bivectorIndex3 i).2)
      rw [algebraicCurvatureIdentityQuadraticEval_bivectorBasis g x B hB, hv, mul_one] at hb
      rw [hquad]
      exact mul_le_mul_of_nonneg_left hb (by norm_num)
  exact hleast.csInf_eq

theorem inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion
    (g : SmoothRiemannianMetric ThreeModel X) (a : ℝ) (x : X) :
    InFixedHamiltonIveyRegion g a x ↔
      (metricScalarAt g x, 2 * leastCurvatureOperatorEigenvalueAt g x
        (metricAlgebraicCurvatureTensorAt g x)) ∈ fixedHamiltonIveyRegion a := by
  constructor
  · intro h
    obtain ⟨B, hB⟩ := exists_orthonormalBasisAt g x (by
      change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
      simp)
    have hB' : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0 := by
      simpa only [OrthonormalBasisAt, delta3] using hB
    have hh := h B hB'
    change 0 ≤ _ ∨ fixedHamiltonIveyBarrier a (-_) ≤ metricScalarAt g x at hh
    rw [csInf_two_mul_matrix_rayleigh_eq g x B hB] at hh
    exact hh
  · intro h B hB
    have hB' : OrthonormalBasisAt g x B := by
      simpa only [OrthonormalBasisAt, delta3] using hB
    change 0 ≤ _ ∨ fixedHamiltonIveyBarrier a (-_) ≤ metricScalarAt g x
    rw [csInf_two_mul_matrix_rayleigh_eq g x B hB']
    exact h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Surgery.Topology

universe u

theorem exists_admissiblePinchingFunction_phiAlmostNonnegative_of_fixedHamiltonIveyRegion
    {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi ∧
      ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace ThreeSpace X]
        [IsManifold ThreeModel ∞ X] [T2Space X],
        ∀ (D : RealTimeInterval) (S : SolutionOn (I := ThreeModel) (M := X) D)
          (W : Set ℝ) (a : ℝ → ℝ),
          (∀ t ∈ W, a₀ ≤ a t) →
          (∀ t ∈ W, ∀ x : X, InFixedHamiltonIveyRegion (S.base.metric t) (a t) x) →
          PhiAlmostNonnegative S W Phi := by
  obtain ⟨Phi, hPhi, hbound⟩ :=
    exists_admissiblePinchingFunction_neg_le_of_fixedHamiltonIveyRegion ha₀
  refine ⟨Phi, hPhi, ?_⟩
  intro X _ _ _ _ D S W a ha hregion
  apply (phiAlmostNonnegative_iff_neg_le_leastCurvatureOperatorEigenvalueAt
    S W Phi (by simp [ThreeSpace])).mpr
  intro t ht x
  have hr := (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion
    (S.base.metric t) (a t) x).mp (hregion t ht x)
  have hb := hbound (a t) (ha t ht) _ _ hr
  have hp := hPhi.pos (S.scalar t x)
  change -(2 * leastCurvatureOperatorEigenvalueAt (S.base.metric t) x
    ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (S.base.metric t) x⟩) ≤ Phi (S.scalar t x) at hb
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Analysis.Convex

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]

private theorem curvatureOperatorMatrixAt_mem_initial_of_fixed_region
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    {t A : ℝ} (hA : 0 < A) (x : X)
    (hfixed : InFixedHamiltonIveyRegion (S.base.metric t) A x)
    (hscalar : -3 / A ≤ S.scalar t x)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace ThreeModel x))
    (hB : OrthonormalBasisAt (S.base.metric t) x B) :
    curvatureOperatorMatrixAt x B (metricAlgebraicCurvatureTensorAt (S.base.metric t) x) ∈
      hamiltonIveyConvexMatrixRegion (2 * A)⁻¹ 0 := by
  let C := metricAlgebraicCurvatureTensorAt (S.base.metric t) x
  let M := curvatureOperatorMatrixAt x B C
  let K := (2 * A)⁻¹
  have hK : 0 < K := by dsimp [K]; positivity
  have hM : M.IsHermitian := curvatureOperatorMatrixAt_isHermitian x B C
  have hmin : minimumRayleighQuotient3 M =
      leastCurvatureOperatorEigenvalueAt (S.base.metric t) x C := by
    rw [minimumRayleighQuotient3_eq_min_eigenvalue hM,
      leastCurvatureOperatorEigenvalueAt_eq_sectionalMin (S.base.metric t) x B hB C]
    rfl
  have htrace : M.trace = S.scalar t x / 2 := by
    rw [curvatureOperatorMatrixAt_trace_eq_sum_orderedSectionalCurvaturesAt]
    have h := scalar_eq_two_mul_sum_orderedSectionalCurvaturesAt S B hB
    change S.scalar t x = 2 * ∑ i, orderedSectionalCurvaturesAt x B C i at h
    linarith
  apply (mem_hamiltonIveyConvexMatrixRegion_initial_iff hK).mpr
  refine ⟨hM, ?_, ?_⟩
  · change -3 * K ≤ M.trace
    rw [htrace]
    have heq : -3 * K = (-3 / A) / 2 := by dsimp [K]; ring
    rw [heq]
    linarith
  · intro hle
    have hν : minimumRayleighQuotient3 M < 0 := lt_of_le_of_lt hle (neg_neg_of_pos hK)
    have hfix := (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion
      (S.base.metric t) A x).mp hfixed
    rw [← hmin] at hfix
    have hb : fixedHamiltonIveyBarrier A (-(2 * minimumRayleighQuotient3 M)) ≤ S.scalar t x := by
      rcases hfix with hnonneg | hb
      · linarith
      · exact hb
    have heq := two_mul_hamiltonIveyBarrier_eq_fixedHamiltonIveyBarrier
      (K := K) (t := 0) hK le_rfl (by linarith : 0 < -(2 * minimumRayleighQuotient3 M))
    have hparam : (2 * K)⁻¹ + 0 = A := by dsimp [K]; field_simp; ring
    rw [hparam] at heq
    have hhalf : -(2 * minimumRayleighQuotient3 M) / 2 = -minimumRayleighQuotient3 M := by ring
    rw [hhalf] at heq
    rw [htrace]
    simp only [hamiltonIveyBarrier, mul_zero, add_zero, Real.log_one] at heq
    linarith

theorem fixedHamiltonIveyRegion_and_scalar_lower_on_slab
    [CompactSpace X] {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (hS : IsSolutionOn S) {u T A : ℝ} (hT : 0 ≤ T) (hA : 0 < A)
    (hslab : Icc u (u + T) ⊆ D.carrier) (hreg : Ioo u (u + T) ⊆ D.regular)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion (S.base.metric u) A x)
    (hscalar : ∀ x, -3 / A ≤ S.scalar u x) :
    ∀ t ∈ Icc u (u + T), ∀ x,
      InFixedHamiltonIveyRegion (S.base.metric t) (A + t - u) x ∧
        -3 / (A + t - u) ≤ S.scalar t x := by
  let K := (2 * A)⁻¹
  have hK : 0 < K := by dsimp [K]; positivity
  have hprop := curvatureOperatorRegionPropagationOn_of_initial_region S hS hT hK hslab hreg
    (by simp [ThreeSpace]) (fun x B hB =>
      curvatureOperatorMatrixAt_mem_initial_of_fixed_region S hA x (hfixed x) (hscalar x) B hB)
  obtain ⟨hlo, hbar⟩ := hamilton_ivey_pinching_of_curvatureOperatorRegionPropagationOn S hprop
  intro t ht x
  have hτ : 0 ≤ t - u := sub_nonneg.mpr ht.1
  have hden : 0 < 1 + 4 * K * (t - u) := by positivity
  have hAτ : 0 < A + (t - u) := add_pos_of_pos_of_nonneg hA hτ
  have hA2τ : 0 < A + 2 * (t - u) := by positivity
  constructor
  · apply (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion
      (S.base.metric t) (A + t - u) x).mpr
    let ν := leastCurvatureOperatorEigenvalueAt (S.base.metric t) x
      (metricAlgebraicCurvatureTensorAt (S.base.metric t) x)
    change 0 ≤ 2 * ν ∨ fixedHamiltonIveyBarrier (A + t - u) (-(2 * ν)) ≤ S.scalar t x
    by_cases hν : 0 ≤ ν
    · exact Or.inl (mul_nonneg (by norm_num) hν)
    right
    have hνneg : ν < 0 := lt_of_not_ge hν
    have hb := hbar t ht x hνneg
    have heq := two_mul_hamiltonIveyBarrier_eq_fixedHamiltonIveyBarrier hK hτ
      (by linarith : 0 < -(2 * ν))
    have hparam : (2 * K)⁻¹ + (t - u) = A + t - u := by dsimp [K]; field_simp; ring
    rw [hparam, show -(2 * ν) / 2 = -ν by ring] at heq
    rw [← heq]
    change 2 * (-ν) * (Real.log (-ν / K) + Real.log (1 + 2 * K * (t - u)) - 3) ≤
      S.scalar t x at hb
    dsimp only [hamiltonIveyBarrier]
    nlinarith [hb]
  · have hb := hlo t ht x
    have heq : -6 * K / (1 + 4 * K * (t - u)) = -3 / (A + 2 * (t - u)) := by
      dsimp [K]
      field_simp
      ring
    rw [heq] at hb
    have hcompare : -3 / (A + (t - u)) ≤ -3 / (A + 2 * (t - u)) := by
      apply (div_le_div_iff₀ hAτ hA2τ).mpr
      nlinarith
    simpa only [← add_sub_assoc] using hcompare.trans hb

namespace OrientedThreeStage

variable {P : OrientedThreeStage.{u}} {a s : ℝ}

theorem IncomingSlab.fixedHamiltonIveyRegion_and_scalar_lower (G : P.IncomingSlab a s)
    {A : ℝ} (hA : 0 < A)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion (G.flow.base.metric a) A x)
    (hscalar : ∀ x, -3 / A ≤ G.flow.scalar a x) :
    ∀ t ∈ Ico a s, ∀ x,
      InFixedHamiltonIveyRegion (G.flow.base.metric t) (A + t - a) x ∧
        -3 / (A + t - a) ≤ G.flow.scalar t x := by
  intro t ht x
  exact fixedHamiltonIveyRegion_and_scalar_lower_on_slab G.flow G.equation
    (T := t - a) (sub_nonneg.mpr ht.1) hA
    (fun u hu => ⟨hu.1, by have := hu.2; linarith [ht.2]⟩)
    (fun u hu => ⟨hu.1, by have := hu.2; linarith [ht.2]⟩)
    hfixed hscalar t ⟨ht.1, by linarith⟩ x

end OrientedThreeStage

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
