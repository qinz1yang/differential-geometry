import DifferentialGeometry.Geometry.Metric.TensorInner.Fiber.CoerciveBilinearInverse
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Comparison

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace Tensor0SBundle

open scoped Manifold ContDiff BigOperators

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

theorem exists_orthonormal_basis_norm_le_of_coercive
    (g : SmoothMetricGen I M) (x : M)
    {c : ℝ} (hc : 0 < c)
    (hlow : ∀ v : TangentSpace I x, c * ‖v‖ ^ 2 ≤ g.inner x v v) :
    ∃ basis : Module.Basis
        (Fin (Module.finrank ℝ (TangentSpace I x))) ℝ (TangentSpace I x),
      (∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : ℝ) else 0) ∧
        ∀ i, ‖(basis i : TangentSpace I x)‖ ≤ (Real.sqrt c)⁻¹ := by
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := I) g x
  refine ⟨basis, hON, fun i => ?_⟩
  have h1 : c * ‖(basis i : TangentSpace I x)‖ ^ 2 ≤ 1 := by
    have h := hlow (basis i)
    rw [hON i i, if_pos rfl] at h
    exact h
  have hs : Real.sqrt c > 0 := Real.sqrt_pos.mpr hc
  have hsq : Real.sqrt c * Real.sqrt c = c :=
    Real.mul_self_sqrt (le_of_lt hc)
  rw [inv_eq_one_div, le_div_iff₀ hs]
  nlinarith [h1, hsq, norm_nonneg (basis i : TangentSpace I x),
    sq_nonneg (‖(basis i : TangentSpace I x)‖ * Real.sqrt c - 1)]

theorem sqrt_normSq0S_le_of_metric_equiv_of_component_bound
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g₀ g : SmoothMetricGen I M) (x : M) (s : ℕ)
    (basis : Module.Basis Idx ℝ (TangentSpace I x))
    (hinv₀ : MetricInverseInBasisGen (I := I) g₀ x basis
      (identityInvMetric (Idx := Idx)))
    {C B : ℝ} (hC : 1 ≤ C)
    (hequiv : ∀ v : TangentSpace I x,
      C⁻¹ * g₀.inner x v v ≤ g.inner x v v ∧
        g.inner x v v ≤ C * g₀.inner x v v)
    (T : Tensor0SSpace s I x) (hBnn : 0 ≤ B)
    (hB : ∀ slots : Fin s → Idx,
      |component0S (I := I) basis T slots| ≤ B) :
    Real.sqrt (normSq0S (I := I) g x s T) ≤
      Real.sqrt (C ^ s) *
        (Real.sqrt (Fintype.card (Fin s → Idx) : ℝ) * B) := by
  have hflat := normSq0S_le_card_of_component_bound
    (I := I) g₀ x s basis hinv₀ T B hBnn hB
  have hroot : Real.sqrt (normSq0S (I := I) g₀ x s T) ≤
      Real.sqrt (Fintype.card (Fin s → Idx) : ℝ) * B := by
    calc
      Real.sqrt (normSq0S (I := I) g₀ x s T) ≤
          Real.sqrt ((Fintype.card (Fin s → Idx) : ℝ) * B ^ 2) :=
        Real.sqrt_le_sqrt hflat
      _ = Real.sqrt (Fintype.card (Fin s → Idx) : ℝ) *
          Real.sqrt (B ^ 2) :=
        Real.sqrt_mul (by positivity) _
      _ = Real.sqrt (Fintype.card (Fin s → Idx) : ℝ) * B := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hBnn]
  exact (sqrt_normSq0S_le_of_metric_equiv (I := I)
    g₀ g x s hC hequiv T).trans
      (mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg _))

theorem sqrt_normSq0S_le_of_component_bound_of_coercive
    {Idx : Type*} [Fintype Idx]
    (g : SmoothMetricGen I M) (x : M) (s : ℕ)
    (basis : Module.Basis Idx ℝ (TangentSpace I x))
    {c B : ℝ} (hc : 0 < c)
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
          (((1 + epsBasis) * (Fintype.card Idx : ℝ)) ^ s) *
        (Real.sqrt (Fintype.card (Fin s → Idx) : ℝ) * B) := by
  classical
  dsimp only
  let coordSum : ℝ :=
    ∑ i : Idx, ‖(basis.coord i).toContinuousLinearMap‖
  let epsBasis : ℝ := c⁻¹ * coordSum ^ 2 + 1
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
      (tangentFlatEquivGen (I := I) g x).symm (basis.coord i) =
        IsCoercive.sharp hco (basis.coord i).toContinuousLinearMap := by
    apply (tangentFlatEquivGen (I := I) g x).injective
    rw [(tangentFlatEquivGen (I := I) g x).apply_symm_apply]
    ext v
    change basis.coord i v =
      g.inner x
        (IsCoercive.sharp hco (basis.coord i).toContinuousLinearMap) v
    exact congrArg (fun eta : TangentSpace I x →L[ℝ] ℝ => eta v)
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
      |gInv i j - (if i = j then (1 : ℝ) else 0)| ≤ epsBasis := by
    intro i j
    calc
      |gInv i j - (if i = j then (1 : ℝ) else 0)| ≤
          |gInv i j| + |(if i = j then (1 : ℝ) else 0)| :=
        by simpa using
          (abs_sub_le (gInv i j) 0
            (if i = j then (1 : ℝ) else 0))
      _ ≤ c⁻¹ * coordSum ^ 2 + 1 := by
        apply add_le_add (hgInv_bound i j)
        split_ifs <;> simp
      _ = epsBasis := rfl
  have hginv : MetricInverseInBasisGen (I := I) g x basis gInv :=
    basisInvMetric_real (I := I) g x basis
  have hnorm := normSq0S_le_pow_sum_comp_sq
    (I := I) g x s basis gInv epsBasis heps_nonneg hginv hnear T
  have hsum :
      (∑ slots : Fin s → Idx,
          tensor0SComponent (I := I) T (fun i => basis i) slots ^ 2) ≤
        (Fintype.card (Fin s → Idx) : ℝ) * B ^ 2 := by
    calc
      (∑ slots : Fin s → Idx,
          tensor0SComponent (I := I) T (fun i => basis i) slots ^ 2) ≤
          ∑ _slots : Fin s → Idx, B ^ 2 := by
        apply Finset.sum_le_sum
        intro slots _
        have habs :
            |tensor0SComponent (I := I) T (fun i => basis i) slots| ≤
              |B| := by
          simpa only [tensor0SComponent_apply, component0S_apply,
            abs_of_nonneg hBnn] using hB slots
        simpa only [sq_abs] using sq_le_sq.mpr habs
      _ = (Fintype.card (Fin s → Idx) : ℝ) * B ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hfactor_nonneg :
      0 ≤ ((1 + epsBasis) * (Fintype.card Idx : ℝ)) ^ s := by
    positivity
  have hnorm' :
      normSq0S (I := I) g x s T ≤
        ((1 + epsBasis) * (Fintype.card Idx : ℝ)) ^ s *
          ((Fintype.card (Fin s → Idx) : ℝ) * B ^ 2) :=
    hnorm.trans (mul_le_mul_of_nonneg_left hsum hfactor_nonneg)
  calc
    Real.sqrt (normSq0S (I := I) g x s T) ≤
        Real.sqrt
          (((1 + epsBasis) * (Fintype.card Idx : ℝ)) ^ s *
            ((Fintype.card (Fin s → Idx) : ℝ) * B ^ 2)) :=
      Real.sqrt_le_sqrt hnorm'
    _ = Real.sqrt
          (((1 + epsBasis) * (Fintype.card Idx : ℝ)) ^ s) *
        Real.sqrt ((Fintype.card (Fin s → Idx) : ℝ) * B ^ 2) :=
      Real.sqrt_mul hfactor_nonneg _
    _ = Real.sqrt
          (((1 + epsBasis) * (Fintype.card Idx : ℝ)) ^ s) *
        (Real.sqrt (Fintype.card (Fin s → Idx) : ℝ) * B) := by
      rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hBnn]

end Tensor0SBundle
end DifferentialGeometry
