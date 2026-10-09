import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.LeastEigenvalue
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.ReactionPreservation
import DifferentialGeometry.Geometry.Comparison.RadialHessianLowerBound

/-!
# Shifted sectional, curvature-operator and Ricci-upper bounds in dimension three

At a point of a Riemannian 3-manifold, for every real `K` the following are equivalent:
* `sec ≥ -K` (`SectionalBoundedBelowAt g x (-K)`);
* the curvature operator is bounded below by `-K` (`curvatureOperatorLowerBoundAt g x Rm K`);
* `Ric ≤ (R / 2 + K) g`, i.e. `(R / 2) g - Ric + K g ≥ 0`.

There is no factor `2`: a decomposable 2-form evaluates the curvature operator to
`Rm(v, w, w, v)` and the identity to the Gram area (`curvatureOperatorLowerBoundAt` at `n = 1`).
The proof uses a Ricci eigenframe, in which the curvature-operator matrix is
`diag(R/2 - r₃, R/2 - r₂, R/2 - r₁)`. The case `K = 0` is
`algebraicCurvatureOperatorNonnegative_iff_ricci_upper_bound3`.

We also record `Ric(v, v) ≤ 3 |Rm| g(v, v)`.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

private theorem metric_traceData
    (g : SmoothRiemannianMetric I M) (x : M)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (hB : OrthonormalBasisAt g x B) :
    RiemannFromRicci3DTraceDataAt g
      (-metricRicciAt g x) (-metricScalarAt g x)
      (metricRm04At g x) B := by
  have hLower :=
    rm04LowersRm13At_of_realizes
      g (leviCivitaConnectionOfMetric g)
      (metricRm13 g) (metricRm04 g)
      (metricCurvatureSections g).rm13Realizes
      (metricCurvatureSections g).rm04Realizes x
  have hcurv :
      AlgebraicCurvatureSymmetries3
        (standardRmCompAt B (metricRm04 g x)) :=
    algebraicCurvatureSymmetries3_standardRmCompAt_of_leviCivita_realizes
      (g := g) (Rm04 := metricRm04 g)
      (hRm04 := (metricCurvatureSections g).rm04Realizes) B
  have hinv : MetricInverseInBasis g x B delta3 :=
    orthonormal_invBasis3 g B hB
  have hRicFirst :
      RicciRealizesRm04FirstTraceAt
        (metricRicci g x) (metricRm04 g x) delta3 B :=
    ricciFirstTraceAt_of_rm13 g B delta3 hinv
      (metricRicci g x) (metricRm13 g x) (metricRm04 g x)
      ((metricCurvatureSections g).ricciRealizes x) hLower
  have hScalar :
      ScalarRealizesRicciTraceAt
        (metricScalarAt g x) (metricRicci g x) delta3 B := by
    unfold ScalarRealizesRicciTraceAt
    rw [metricRicci_apply]
    exact metricTracePair0SAt_eq_sum_basis
      g B delta3 hinv (metricRicciAt g x)
  simpa only [metricRicci_apply, metricRm04_apply] using
    traceDataOfFirst hB hcurv hRicFirst hScalar

/-- In an orthonormal Ricci eigenframe `Ric = diag(r₁, r₂, r₃)` the curvature-operator matrix
(bivector basis `e₀∧e₁, e₀∧e₂, e₁∧e₂`) is `diag(R/2 - r₃, R/2 - r₂, R/2 - r₁)`. -/
theorem curvatureOperatorMatrixAt_eq_diagonal_of_ricciDiag
    (g : SmoothRiemannianMetric I M) (x : M)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (hB : OrthonormalBasisAt g x B)
    (r1 r2 r3 : ℝ)
    (hdiag : ∀ i j : Fin 3,
      metricRicciAt g x (vec2 (I := I) (B i) (B j)) = ricciDiag3 r1 r2 r3 i j) :
    curvatureOperatorMatrixAt x B (metricAlgebraicCurvatureTensorAt g x) =
      Matrix.diagonal
        ![metricScalarAt g x / 2 - r3,
          metricScalarAt g x / 2 - r2,
          metricScalarAt g x / 2 - r1] := by
  have hR : metricScalarAt g x = r1 + r2 + r3 := by
    have hinv : MetricInverseInBasis g x B delta3 := orthonormal_invBasis3 g B hB
    change metricTracePair0SAt g (metricRicciAt g x) = _
    rw [metricTracePair0SAt_eq_sum_basis g B delta3 hinv (metricRicciAt g x)]
    simp [Fin.sum_univ_three, delta3, hdiag, ricciDiag3]
  have htrace := metric_traceData g x B hB
  have hneg (i j : Fin 3) :
      ricciCompAt B (-metricRicciAt g x) i j =
        -ricciDiag3 r1 r2 r3 i j := by
    rw [ricciCompAt_apply]
    change -metricRicciAt g x (vec2 (I := I) (B i) (B j)) = _
    rw [hdiag]
  ext i j
  change metricRm04At g x
    (vec4 (I := I)
      (B (bivectorIndex3 i).1) (B (bivectorIndex3 i).2)
      (B (bivectorIndex3 j).2) (B (bivectorIndex3 j).1)) = _
  rw [← rm04CompAt_apply,
    rm04Comp_displayedRiemannFromRicci3D_at htrace]
  simp only [hneg]
  fin_cases i <;> fin_cases j <;>
    norm_num [bivectorIndex3, Matrix.diagonal, ricciDiag3, delta3, hR,
      Matrix.cons_val_two,
      show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
      show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide,
      show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] <;>
    ring

private theorem exists_ricciEigenframe
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank ℝ (TangentSpace I x) = 3) :
    ∃ (B : Module.Basis (Fin 3) ℝ (TangentSpace I x)) (r1 r2 r3 : ℝ),
      OrthonormalBasisAt g x B ∧
        ∀ i j : Fin 3,
          metricRicciAt g x (vec2 (I := I) (B i) (B j)) = ricciDiag3 r1 r2 r3 i j := by
  have hsymm : RicciSymAt (I := I) (metricRicciAt g x) :=
    fun v w => metricRicciAt_symm g x v w
  obtain ⟨B, r1, r2, r3, hB, hdiag⟩ := ricciEigen3 g (metricRicciAt g x) hdim hsymm
  exact ⟨B, r1, r2, r3, hB, fun i j => by simpa only [ricciCompAt_apply] using hdiag.2 i j⟩

omit [T2Space M] in
private theorem quad_expansion
    (g : SmoothRiemannianMetric I M) (x : M)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace I x))
    (hB : OrthonormalBasisAt g x B)
    (r1 r2 r3 : ℝ)
    (hdiag : ∀ i j : Fin 3,
      metricRicciAt g x (vec2 (I := I) (B i) (B j)) = ricciDiag3 r1 r2 r3 i j)
    (v : TangentSpace I x) :
    metricRicciAt g x (vec2 (I := I) v v) =
        B.repr v 0 ^ 2 * r1 + B.repr v 1 ^ 2 * r2 + B.repr v 2 ^ 2 * r3 ∧
      g.inner x v v = B.repr v 0 ^ 2 + B.repr v 1 ^ 2 + B.repr v 2 ^ 2 := by
  constructor
  · rw [ricci_quad_sum_repr (I := I) (M := M) (metricRicciAt g x) B v]
    simp only [hdiag, Fin.sum_univ_three]
    simp [ricciDiag3]
    ring
  · have hon : ∀ i j : Fin 3, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 :=
      fun i j => hB i j
    have hv : v = ∑ i : Fin 3, B.repr v i • B i := (B.sum_repr v).symm
    have h := DifferentialGeometry.Geometry.Riemannian.inner_sum_orthonormal g x B hon
      (fun i => B.repr v i)
    rw [← hv, Fin.sum_univ_three] at h
    exact h

/-- A curvature-operator lower bound `-K` gives `sec ≥ -K` (decomposable 2-forms, `n = 1`). -/
theorem sectionalBoundedBelowAt_of_curvatureOperatorLowerBoundAt
    {g : SmoothRiemannianMetric I M} {x : M} {K : ℝ}
    (hK : curvatureOperatorLowerBoundAt g x (metricAlgebraicCurvatureTensorAt g x) K) :
    SectionalBoundedBelowAt g x (-K) := by
  intro v w
  have hh := hK 1 (fun _ => 1) (fun _ => v) (fun _ => w)
  simp only [algebraicCurvatureOperatorQuadraticEval, algebraicCurvatureIdentityQuadraticEval,
    Fin.sum_univ_one, one_mul] at hh
  change 0 ≤ metricRm04StandardAt g x v w w v +
    K * (g.inner x v v * g.inner x w w - g.inner x v w * g.inner x w v) at hh
  rw [g.symm x w v] at hh
  nlinarith [hh]

/-- `sec ≥ -K` gives `Ric ≤ (R / 2 + K) g` in dimension three. -/
theorem metricRicciAt_le_of_sectionalBoundedBelowAt
    {g : SmoothRiemannianMetric I M} {x : M}
    (hdim : Module.finrank ℝ (TangentSpace I x) = 3) {K : ℝ}
    (hsec : SectionalBoundedBelowAt g x (-K)) (v : TangentSpace I x) :
    metricRicciAt g x (vec2 (I := I) v v) ≤ (metricScalarAt g x / 2 + K) * g.inner x v v := by
  obtain ⟨B, r1, r2, r3, hB, hdiag⟩ := exists_ricciEigenframe g x hdim
  have hmat := curvatureOperatorMatrixAt_eq_diagonal_of_ricciDiag g x B hB r1 r2 r3 hdiag
  have hplane (i : Fin 3) :
      -K ≤ curvatureOperatorMatrixAt x B (metricAlgebraicCurvatureTensorAt g x) i i := by
    have hs := hsec (B (bivectorIndex3 i).1) (B (bivectorIndex3 i).2)
    have hne : (bivectorIndex3 i).1 ≠ (bivectorIndex3 i).2 := by
      fin_cases i <;> decide
    have h1 : g.inner x (B (bivectorIndex3 i).1) (B (bivectorIndex3 i).1) = 1 := by
      simpa [delta3] using hB (bivectorIndex3 i).1 (bivectorIndex3 i).1
    have h2 : g.inner x (B (bivectorIndex3 i).2) (B (bivectorIndex3 i).2) = 1 := by
      simpa [delta3] using hB (bivectorIndex3 i).2 (bivectorIndex3 i).2
    have h12 : g.inner x (B (bivectorIndex3 i).1) (B (bivectorIndex3 i).2) = 0 := by
      simpa [delta3, hne] using hB (bivectorIndex3 i).1 (bivectorIndex3 i).2
    rw [h1, h2, h12] at hs
    simp only [curvatureOperatorMatrixAt, metricAlgebraicCurvatureTensorAt_coe,
      tensor04StandardAt_apply]
    simp only [metricRm04StandardAt_apply] at hs
    linarith
  have h0 := hplane 0
  have h1 := hplane 1
  have h2 := hplane 2
  rw [hmat] at h0 h1 h2
  simp [Matrix.diagonal] at h0 h1 h2
  obtain ⟨hRic, hg⟩ := quad_expansion g x B hB r1 r2 r3 hdiag v
  rw [hRic, hg]
  nlinarith [mul_nonneg (sq_nonneg (B.repr v 0)) (by linarith : (0 : ℝ) ≤
      metricScalarAt g x / 2 + K - r1),
    mul_nonneg (sq_nonneg (B.repr v 1)) (by linarith : (0 : ℝ) ≤
      metricScalarAt g x / 2 + K - r2),
    mul_nonneg (sq_nonneg (B.repr v 2)) (by linarith : (0 : ℝ) ≤
      metricScalarAt g x / 2 + K - r3)]

/-- `Ric ≤ (R / 2 + K) g` gives a curvature-operator lower bound `-K` in dimension three. -/
theorem curvatureOperatorLowerBoundAt_of_metricRicciAt_le
    {g : SmoothRiemannianMetric I M} {x : M}
    (hdim : Module.finrank ℝ (TangentSpace I x) = 3) {K : ℝ}
    (hRic : ∀ v : TangentSpace I x,
      metricRicciAt g x (vec2 (I := I) v v) ≤ (metricScalarAt g x / 2 + K) * g.inner x v v) :
    curvatureOperatorLowerBoundAt g x (metricAlgebraicCurvatureTensorAt g x) K := by
  obtain ⟨B, r1, r2, r3, hB, hdiag⟩ := exists_ricciEigenframe g x hdim
  have hmat := curvatureOperatorMatrixAt_eq_diagonal_of_ricciDiag g x B hB r1 r2 r3 hdiag
  have hr (i : Fin 3) : ricciDiag3 r1 r2 r3 i i ≤ metricScalarAt g x / 2 + K := by
    have h := hRic (B i)
    rw [hdiag i i] at h
    have hii : g.inner x (B i) (B i) = 1 := by simpa [delta3] using hB i i
    rw [hii, mul_one] at h
    exact h
  have hr1 : r1 ≤ metricScalarAt g x / 2 + K := by simpa [ricciDiag3] using hr 0
  have hr2 : r2 ≤ metricScalarAt g x / 2 + K := by simpa [ricciDiag3] using hr 1
  have hr3 : r3 ≤ metricScalarAt g x / 2 + K := by simpa [ricciDiag3] using hr 2
  intro n c v w
  let a : Fin 3 → ℝ := fun i =>
    ∑ k : Fin n, c k *
      (B.repr (v k) (bivectorIndex3 i).1 * B.repr (w k) (bivectorIndex3 i).2 -
        B.repr (v k) (bivectorIndex3 i).2 * B.repr (w k) (bivectorIndex3 i).1)
  have hid :
      algebraicCurvatureIdentityQuadraticEval g c v w = ∑ i : Fin 3, a i ^ 2 :=
    algebraicCurvatureIdentityQuadraticEval_eq_bivectorNormSq g x c v w B hB
  have hquad :
      algebraicCurvatureOperatorQuadraticEval (metricAlgebraicCurvatureTensorAt g x) c v w =
        ∑ i : Fin 3, ∑ j : Fin 3, a i * a j *
          curvatureOperatorMatrixAt x B (metricAlgebraicCurvatureTensorAt g x) i j :=
    algebraicCurvatureOperatorQuadraticEval_eq_bivectorQuad
      x B (metricAlgebraicCurvatureTensorAt g x) c v w
  rw [hid, hquad, hmat]
  norm_num [Fin.sum_univ_three, Matrix.diagonal, Matrix.cons_val_two, Fin.reduceEq]
  nlinarith [mul_nonneg (sq_nonneg (a 0)) (by linarith : (0 : ℝ) ≤
      metricScalarAt g x / 2 - r3 + K),
    mul_nonneg (sq_nonneg (a 1)) (by linarith : (0 : ℝ) ≤
      metricScalarAt g x / 2 - r2 + K),
    mul_nonneg (sq_nonneg (a 2)) (by linarith : (0 : ℝ) ≤
      metricScalarAt g x / 2 - r1 + K)]

/-- In dimension three, `sec ≥ -K` iff `Ric ≤ (R / 2 + K) g`, for every real `K`. -/
theorem sectionalBoundedBelowAt_iff_metricRicciAt_le
    {g : SmoothRiemannianMetric I M} {x : M}
    (hdim : Module.finrank ℝ (TangentSpace I x) = 3) {K : ℝ} :
    SectionalBoundedBelowAt g x (-K) ↔
      ∀ v : TangentSpace I x,
        metricRicciAt g x (vec2 (I := I) v v) ≤ (metricScalarAt g x / 2 + K) * g.inner x v v :=
  ⟨fun hsec v => metricRicciAt_le_of_sectionalBoundedBelowAt hdim hsec v,
    fun hRic => sectionalBoundedBelowAt_of_curvatureOperatorLowerBoundAt
      (curvatureOperatorLowerBoundAt_of_metricRicciAt_le hdim hRic)⟩

/-- In dimension three, `sec ≥ -K` iff the curvature operator is bounded below by `-K`. -/
theorem sectionalBoundedBelowAt_iff_curvatureOperatorLowerBoundAt
    {g : SmoothRiemannianMetric I M} {x : M}
    (hdim : Module.finrank ℝ (TangentSpace I x) = 3) {K : ℝ} :
    SectionalBoundedBelowAt g x (-K) ↔
      curvatureOperatorLowerBoundAt g x (metricAlgebraicCurvatureTensorAt g x) K :=
  ⟨fun hsec => curvatureOperatorLowerBoundAt_of_metricRicciAt_le hdim
      (fun v => metricRicciAt_le_of_sectionalBoundedBelowAt hdim hsec v),
    sectionalBoundedBelowAt_of_curvatureOperatorLowerBoundAt⟩

/-- `Ric(v, v) ≤ 3 |Rm| g(v, v)` in dimension three. -/
theorem metricRicciAt_le_three_mul_of_rm_bound
    {g : SmoothRiemannianMetric I M} {x : M}
    (hdim : Module.finrank ℝ (TangentSpace I x) = 3) {B : ℝ}
    (hRm : Real.sqrt (normSq0S g x 4 (metricRm04 g x)) ≤ B) (v : TangentSpace I x) :
    metricRicciAt g x (vec2 (I := I) v v) ≤ 3 * B * g.inner x v v := by
  obtain ⟨F, r1, r2, r3, hF, hdiag⟩ := exists_ricciEigenframe g x hdim
  have hON : ∀ i j : Fin 3, g.inner x (F i) (F j) = if i = j then (1 : ℝ) else 0 :=
    fun i j => hF i j
  have hRmAt : Real.sqrt (normSq0S g x 4 (metricRm04At g x)) ≤ B := by
    simpa only [metricRm04_apply] using hRm
  have hr (i : Fin 3) : ricciDiag3 r1 r2 r3 i i ≤ 3 * B := by
    have h := metricRicciComp_le g F hON i i
    rw [hdiag i i] at h
    simp only [Fintype.card_fin, Nat.cast_ofNat] at h
    have hle := le_abs_self (ricciDiag3 r1 r2 r3 i i)
    linarith
  have hr1 := hr 0
  have hr2 := hr 1
  have hr3 := hr 2
  simp [ricciDiag3] at hr1 hr2 hr3
  obtain ⟨hRic, hg⟩ := quad_expansion g x F hF r1 r2 r3 hdiag v
  rw [hRic, hg]
  nlinarith [mul_nonneg (sq_nonneg (F.repr v 0)) (by linarith : (0 : ℝ) ≤ 3 * B - r1),
    mul_nonneg (sq_nonneg (F.repr v 1)) (by linarith : (0 : ℝ) ≤ 3 * B - r2),
    mul_nonneg (sq_nonneg (F.repr v 2)) (by linarith : (0 : ℝ) ≤ 3 * B - r3)]

end DifferentialGeometry.Geometry.Curvature.DimensionThree
