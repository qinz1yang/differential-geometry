import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.PullbackField
import DifferentialGeometry.Geometry.Metric.TensorInner.CoerciveBilinInverse
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Tensor0SBundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

section PositiveOrder

variable [CompleteSpace E] [I.Boundaryless]
variable [T2Space M] [SigmaCompactSpace M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem metricError_eq_zero
    (G g : SmoothRiemannianMetric I M) (x : M) :
    metricTensorErrorNorm (I := I)
        (Tensor0SBundle.metricTensorField (I := I) G) g x =
      metricDerivNorm (I := I) 0 G g g x := by
  rfl

theorem t02Norm_metricDiff
    (G g : SmoothRiemannianMetric I M) (a : Nat) (ha : 1 ≤ a) (x : M) :
    tensor02CovDerivNormWith (I := I) a
        (Tensor0SBundle.metricTensorField (I := I) G) g g x =
      metricDerivNorm (I := I) a G g g x := by
  classical
  obtain ⟨basis, hON⟩ :=
    DifferentialGeometry.Geometry.Curvature.exists_gOrthonormalBasis
      (I := I) g x
  have hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) g x basis
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h :=
      DifferentialGeometry.Geometry.Curvature.metricInverseInBasis_of_orthonormal
        (I := I) g basis hON
    simpa [Tensor0SBundle.identityInvMetric,
      Tensor0SBundle.diagonalInvMetric] using h
  rw [t02Norm_eq_iterCov (I := I)
      (Tensor0SBundle.metricTensorField (I := I) G) g a basis hinv,
    metricDerivNorm_eq_iterCov (I := I) G g g a basis hinv]
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
  rw [iterCov_sub, show 1 + b = b + 1 by omega,
    iterCov_metric_zero g b, sub_zero]

end PositiveOrder

section Carrier

variable [CompleteSpace E] [I.Boundaryless]
variable [T2Space M] [SigmaCompactSpace M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N]
variable [IsManifold I ∞ N]

noncomputable def PreApproxIsoDataOn.of_metric
    {K : Set M} {eps : Real} {p : Nat} {F : M → N}
    (G g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (heps : 0 < eps) (heps1 : eps < 1)
    (hsmooth : ContMDiffOn I I (∞ : WithTop ℕ∞) F K)
    (happly : ∀ x ∈ K, ∀ v : Fin 2 → TangentSpace I x,
      Tensor0SBundle.metricTensorField (I := I) G x v =
        h.inner (F x)
          (mfderiv I I F x (v 0)) (mfderiv I I F x (v 1)))
    (hderiv : ∀ a : Nat, a ≤ p → ∀ x ∈ K,
      metricDerivNorm (I := I) a G g g x ≤ eps) :
    PreApproxIsoDataOn (I := I) K eps p F g h where
  eps_pos := heps
  eps_lt_one := heps1
  smoothOn := hsmooth
  pullback := Tensor0SBundle.metricTensorField (I := I) G
  pullback_apply := happly
  c0_small := by
    intro x hx
    rw [metricError_eq_zero (I := I) G g x]
    exact hderiv 0 (Nat.zero_le p) x hx
  cov_deriv_small := by
    intro a ha hap x hx
    rw [t02Norm_metricDiff (I := I) G g a ha x]
    exact hderiv a hap x hx

end Carrier

theorem sqrt_norm_le_comp
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g0 g : SmoothMetric_gen I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv0 : MetricInverseInBasis_gen (I := I) g0 x basis
      (identityInvMetric (Idx := Idx)))
    {C B : Real} (hC : 1 ≤ C)
    (hequiv : ∀ v : TangentSpace I x,
      C⁻¹ * g0.inner x v v ≤ g.inner x v v ∧
        g.inner x v v ≤ C * g0.inner x v v)
    (T : Tensor0SSpace s I x) (hBnn : 0 ≤ B)
    (hB : ∀ slots : Fin s → Idx,
      |component0S (I := I) basis T slots| ≤ B) :
    Real.sqrt (normSq0S (I := I) g x s T) ≤
      Real.sqrt (C ^ s) *
        (Real.sqrt (Fintype.card (Fin s → Idx) : Real) * B) := by
  have hflat := normSq0S_le_card_of_component_bound
    (I := I) g0 x s basis hinv0 T B hBnn hB
  have hroot : Real.sqrt (normSq0S (I := I) g0 x s T) ≤
      Real.sqrt (Fintype.card (Fin s → Idx) : Real) * B := by
    calc
      Real.sqrt (normSq0S (I := I) g0 x s T) ≤
          Real.sqrt ((Fintype.card (Fin s → Idx) : Real) * B ^ 2) :=
        Real.sqrt_le_sqrt hflat
      _ = Real.sqrt (Fintype.card (Fin s → Idx) : Real) *
          Real.sqrt (B ^ 2) :=
        Real.sqrt_mul (by positivity) _
      _ = Real.sqrt (Fintype.card (Fin s → Idx) : Real) * B := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hBnn]
  exact (sqrt_normSq0S_le_of_metric_equiv (I := I)
    g0 g x s hC hequiv T).trans
      (mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg _))

theorem sqrt_norm_le_basis_comp_of_coercive
    {Idx : Type*} [Fintype Idx]
    (g : SmoothMetric_gen I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    {c B : Real} (hc : 0 < c)
    (hlow : ∀ v : TangentSpace I x,
      c * ‖v‖ * ‖v‖ ≤ g.inner x v v)
    (T : Tensor0SSpace s I x) (hBnn : 0 ≤ B)
    (hB : ∀ slots : Fin s → Idx,
      |component0S (I := I) basis T slots| ≤ B) :
    let coordSum :=
      ∑ i : Idx, ‖(basis.coord i).toContinuousLinearMap‖
    let epsBasis := c⁻¹ * coordSum ^ 2 + 1
    Real.sqrt (normSq0S (I := I) g x s T) ≤
      Real.sqrt
          (((1 + epsBasis) * (Fintype.card Idx : Real)) ^ s) *
        (Real.sqrt (Fintype.card (Fin s → Idx) : Real) * B) := by
  classical
  dsimp only
  let coordSum : Real :=
    ∑ i : Idx, ‖(basis.coord i).toContinuousLinearMap‖
  let epsBasis : Real := c⁻¹ * coordSum ^ 2 + 1
  let gInv := basisInvMetric (I := I) g x basis
  have hcoordSum_nonneg : 0 ≤ coordSum :=
    Finset.sum_nonneg fun i _ => norm_nonneg
      (basis.coord i).toContinuousLinearMap
  have hcoord_le (i : Idx) :
      ‖(basis.coord i).toContinuousLinearMap‖ ≤ coordSum := by
    exact Finset.single_le_sum
      (fun j _ => norm_nonneg (basis.coord j).toContinuousLinearMap)
      (Finset.mem_univ i)
  have hco : IsCoercive (g.inner x) := ⟨c, hc, hlow⟩
  have hsharp_eq (i : Idx) :
      (tangentFlatEquiv_gen (I := I) g x).symm (basis.coord i) =
        IsCoercive.sharp hco (basis.coord i).toContinuousLinearMap := by
    apply (tangentFlatEquiv_gen (I := I) g x).injective
    rw [(tangentFlatEquiv_gen (I := I) g x).apply_symm_apply]
    ext v
    change basis.coord i v =
      g.inner x
        (IsCoercive.sharp hco (basis.coord i).toContinuousLinearMap) v
    exact congrArg (fun eta : TangentSpace I x →L[Real] Real => eta v)
      (IsCoercive.apply_sharp hco
        (basis.coord i).toContinuousLinearMap).symm
  have hgInv_bound (i j : Idx) :
      |gInv i j| ≤ c⁻¹ * coordSum ^ 2 := by
    have hsharp := IsCoercive.sharp_norm_le hco hc hlow
      (basis.coord i).toContinuousLinearMap
    have heval := (basis.coord j).toContinuousLinearMap.le_opNorm
      (IsCoercive.sharp hco (basis.coord i).toContinuousLinearMap)
    calc
      |gInv i j| =
          ‖(basis.coord j).toContinuousLinearMap
            (IsCoercive.sharp hco
              (basis.coord i).toContinuousLinearMap)‖ := by
        rw [Real.norm_eq_abs]
        simp only [gInv, basisInvMetric, hsharp_eq i]
        rfl
      _ ≤ ‖(basis.coord j).toContinuousLinearMap‖ *
          ‖hco.sharp (basis.coord i).toContinuousLinearMap‖ := heval
      _ ≤ coordSum *
          (c⁻¹ * ‖(basis.coord i).toContinuousLinearMap‖) :=
        mul_le_mul (hcoord_le j) hsharp
          (norm_nonneg _) hcoordSum_nonneg
      _ ≤ coordSum * (c⁻¹ * coordSum) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hcoord_le i) (inv_nonneg.mpr hc.le))
          hcoordSum_nonneg
      _ = c⁻¹ * coordSum ^ 2 := by ring
  have heps_nonneg : 0 ≤ epsBasis := by
    dsimp only [epsBasis]
    positivity
  have hnear : ∀ i j : Idx,
      |gInv i j - (if i = j then (1 : Real) else 0)| ≤ epsBasis := by
    intro i j
    calc
      |gInv i j - (if i = j then (1 : Real) else 0)| ≤
          |gInv i j| + |(if i = j then (1 : Real) else 0)| :=
        by simpa using
          (abs_sub_le (gInv i j) 0
            (if i = j then (1 : Real) else 0))
      _ ≤ c⁻¹ * coordSum ^ 2 + 1 := by
        apply add_le_add (hgInv_bound i j)
        split_ifs <;> simp
      _ = epsBasis := rfl
  have hginv : MetricInverseInBasis_gen (I := I) g x basis gInv :=
    basisInvMetric_real (I := I) g x basis
  have hnorm := normSq0S_le_pow_sum_comp_sq
    (I := I) g x s basis gInv epsBasis heps_nonneg hginv hnear T
  have hsum :
      (∑ slots : Fin s → Idx,
          tensor0SComponent (I := I) T (fun i => basis i) slots ^ 2) ≤
        (Fintype.card (Fin s → Idx) : Real) * B ^ 2 := by
    calc
      (∑ slots : Fin s → Idx,
          tensor0SComponent (I := I) T (fun i => basis i) slots ^ 2) ≤
          ∑ _slots : Fin s → Idx, B ^ 2 := by
        apply Finset.sum_le_sum
        intro slots _
        have habs :
            |tensor0SComponent (I := I) T (fun i => basis i) slots| ≤
              |B| := by
          simpa only [component0S_apply, abs_of_nonneg hBnn] using hB slots
        simpa only [sq_abs] using sq_le_sq.mpr habs
      _ = (Fintype.card (Fin s → Idx) : Real) * B ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hfactor_nonneg :
      0 ≤ ((1 + epsBasis) * (Fintype.card Idx : Real)) ^ s := by
    positivity
  have hnorm' :
      normSq0S (I := I) g x s T ≤
        ((1 + epsBasis) * (Fintype.card Idx : Real)) ^ s *
          ((Fintype.card (Fin s → Idx) : Real) * B ^ 2) :=
    hnorm.trans (mul_le_mul_of_nonneg_left hsum hfactor_nonneg)
  calc
    Real.sqrt (normSq0S (I := I) g x s T) ≤
        Real.sqrt
          (((1 + epsBasis) * (Fintype.card Idx : Real)) ^ s *
            ((Fintype.card (Fin s → Idx) : Real) * B ^ 2)) :=
      Real.sqrt_le_sqrt hnorm'
    _ = Real.sqrt
          (((1 + epsBasis) * (Fintype.card Idx : Real)) ^ s) *
        Real.sqrt ((Fintype.card (Fin s → Idx) : Real) * B ^ 2) :=
      Real.sqrt_mul hfactor_nonneg _
    _ = Real.sqrt
          (((1 + epsBasis) * (Fintype.card Idx : Real)) ^ s) *
        (Real.sqrt (Fintype.card (Fin s → Idx) : Real) * B) := by
      rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hBnn]

end HCGCompactness
end DifferentialGeometry
