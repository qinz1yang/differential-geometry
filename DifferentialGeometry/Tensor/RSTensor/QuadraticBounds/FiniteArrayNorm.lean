import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetricDeriv
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace Tensor0SBundle

open scoped BigOperators

variable {Idx : Type*} [Fintype Idx]

def compNormSqMulti {r : ℕ} (A : (Fin r → Idx) → Real) : Real :=
  ∑ m : Fin r → Idx, (A m) ^ 2

theorem compNormSqMulti_nonneg {r : ℕ} (A : (Fin r → Idx) → Real) :
    0 ≤ compNormSqMulti A := by
  unfold compNormSqMulti
  exact Finset.sum_nonneg fun m _ => sq_nonneg _

theorem sq_le_compNormSqMulti {r : ℕ}
    (A : (Fin r → Idx) → Real) (m : Fin r → Idx) :
    (A m) ^ 2 ≤ compNormSqMulti A := by
  classical
  unfold compNormSqMulti
  exact Finset.single_le_sum (f := fun m' : Fin r → Idx => (A m') ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ m)

theorem abs_le_sqrt_compNormSqMulti {r : ℕ}
    (A : (Fin r → Idx) → Real) (m : Fin r → Idx) :
    |A m| ≤ Real.sqrt (compNormSqMulti A) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (sq_le_compNormSqMulti A m)

theorem abs_bilinear_sum_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : ι -> κ -> Real) (X : ι -> Real) (Y : κ -> Real)
    (C : Real) (hC : 0 <= C)
    (hF : forall i j, |F i j| <= C) :
    |∑ i, ∑ j, F i j * X i * Y j| <=
      C / 2 *
        ((Fintype.card κ : Real) * (∑ i, (X i) ^ 2) +
          (Fintype.card ι : Real) * (∑ j, (Y j) ^ 2)) := by
  classical
  calc
    |∑ i, ∑ j, F i j * X i * Y j| <=
        ∑ i, |∑ j, F i j * X i * Y j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ i, ∑ j, |F i j * X i * Y j| := by
      exact Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ i, ∑ j, C / 2 * ((X i) ^ 2 + (Y j) ^ 2) := by
      refine Finset.sum_le_sum fun i _ => ?_
      refine Finset.sum_le_sum fun j _ => ?_
      rw [abs_mul, abs_mul]
      have hxy : 2 * |X i| * |Y j| <= (X i) ^ 2 + (Y j) ^ 2 := by
        simpa only [sq_abs] using two_mul_le_add_sq |X i| |Y j|
      have hnonneg : 0 <= |X i| * |Y j| :=
        mul_nonneg (abs_nonneg _) (abs_nonneg _)
      have hcoeff : |F i j| * (|X i| * |Y j|) <=
          C * (|X i| * |Y j|) :=
        mul_le_mul_of_nonneg_right (hF i j) hnonneg
      calc
        |F i j| * |X i| * |Y j| =
            |F i j| * (|X i| * |Y j|) := by ring
        _ <= C * (|X i| * |Y j|) := hcoeff
        _ <= C / 2 * ((X i) ^ 2 + (Y j) ^ 2) := by
          nlinarith
    _ = C / 2 *
        ((Fintype.card κ : Real) * (∑ i, (X i) ^ 2) +
          (Fintype.card ι : Real) * (∑ j, (Y j) ^ 2)) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      have hX :
          (∑ i, C / 2 * (X i) ^ 2) =
            C / 2 * (∑ i, (X i) ^ 2) := by
        rw [Finset.mul_sum]
      have hY :
          (∑ j, C / 2 * (Y j) ^ 2) =
            C / 2 * (∑ j, (Y j) ^ 2) := by
        rw [Finset.mul_sum]
      have hXcard :
          (∑ i, (Fintype.card κ : Real) *
              (C / 2 * (X i) ^ 2)) =
            (Fintype.card κ : Real) *
              (∑ i, C / 2 * (X i) ^ 2) := by
        rw [Finset.mul_sum]
      rw [hXcard, hX, hY]
      ring

theorem abs_quadratic_sum_le
    {ι : Type*} [Fintype ι]
    (F : ι -> ι -> Real) (X : ι -> Real)
    (C : Real) (hC : 0 <= C)
    (hF : forall i j, |F i j| <= C) :
    |∑ i, ∑ j, F i j * X i * X j| <=
      C * (Fintype.card ι : Real) * (∑ i, (X i) ^ 2) := by
  have h := abs_bilinear_sum_le F X X C hC hF
  convert h using 1
  ring

theorem abs_sum_le_card_mul_of_bound
    {ι : Type*} [Fintype ι]
    (f : ι -> Real) (C : Real)
    (h : forall i, |f i| <= C) :
    |∑ i, f i| <= (Fintype.card ι : Real) * C := by
  classical
  calc
    |∑ i, f i| <= ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ _i : ι, C := Finset.sum_le_sum fun i _ => h i
    _ = (Fintype.card ι : Real) * C := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem abs_double_sum_le_card_mul_card_mul_of_bound
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι -> κ -> Real) (C : Real)
    (h : forall i j, |f i j| <= C) :
    |∑ i, ∑ j, f i j| <=
      (Fintype.card ι : Real) * (Fintype.card κ : Real) * C := by
  have houter := abs_sum_le_card_mul_of_bound
    (fun i => ∑ j, f i j) ((Fintype.card κ : Real) * C)
    (fun i => abs_sum_le_card_mul_of_bound (f i) C (h i))
  simpa only [mul_assoc] using houter

theorem sum_delta_erase_slot_eq [DecidableEq Idx] {s : ℕ}
    (I0 : Fin s → Idx) (b : Fin s) (G : (Fin s → Idx) → Real) :
    (∑ J0 : Fin s → Idx,
        (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
            identityInvMetric (Idx := Idx) (I0 a) (J0 a)) * G J0) =
      ∑ e : Idx, G (Function.update I0 b e) := by
  classical
  have hinj : Function.Injective (fun e : Idx => Function.update I0 b e) := by
    intro e e' he
    have := congrFun he b
    simpa [Function.update_self] using this
  have himg :
      (∑ e : Idx, G (Function.update I0 b e)) =
        ∑ J0 ∈ (Finset.univ : Finset Idx).image
            (fun e : Idx => Function.update I0 b e),
          (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
              identityInvMetric (Idx := Idx) (I0 a) (J0 a)) * G J0 := by
    rw [Finset.sum_image (fun a _ b _ h => hinj h)]
    refine Finset.sum_congr rfl fun e _ => ?_
    have hprod :
        (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
            identityInvMetric (Idx := Idx) (I0 a) (Function.update I0 b e a)) = 1 := by
      refine Finset.prod_eq_one fun a ha => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase ha)]
      rw [identityInvMetric_apply_self]
    rw [hprod, one_mul]
  rw [himg]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro J0 _ hJ0
  have hne : J0 ≠ Function.update I0 b (J0 b) := by
    intro h
    exact hJ0 (Finset.mem_image.mpr ⟨J0 b, Finset.mem_univ _, h.symm⟩)
  have hsome : ∃ a : Fin s, a ≠ b ∧ I0 a ≠ J0 a := by
    by_contra hnone
    apply hne
    funext a
    by_cases hab : a = b
    · subst hab; rw [Function.update_self]
    · rw [Function.update_of_ne hab]
      by_contra hcon
      exact hnone ⟨a, hab, fun h => hcon h.symm⟩
  obtain ⟨a, hab, hdis⟩ := hsome
  refine mul_eq_zero_of_left ?_ _
  refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hab, Finset.mem_univ a⟩) ?_
  rw [identityInvMetric, diagonalInvMetric_eq_zero_of_ne hdis]

private def ricStarArrayUpdateEquiv {s : ℕ}
    (b : Fin s) : ((Fin s → Idx) × Idx) ≃ ((Fin s → Idx) × Idx) where
  toFun Ie := (Function.update Ie.1 b Ie.2, Ie.1 b)
  invFun Ie := (Function.update Ie.1 b Ie.2, Ie.1 b)
  left_inv := by
    intro Ie
    rcases Ie with ⟨I0, e⟩
    ext q <;> simp
  right_inv := by
    intro Ie
    rcases Ie with ⟨I0, e⟩
    ext q <;> simp

theorem ricStarArray_pairing_self_adjoint {s : ℕ}
    (ric : Idx → Idx → Real) (cA cB : (Fin s → Idx) → Real)
    (hric : ∀ i j, ric i j = ric j i) :
    (∑ I0 : Fin s → Idx, ricStarArray ric cA I0 * cB I0) =
      ∑ I0 : Fin s → Idx, cA I0 * ricStarArray ric cB I0 := by
  classical
  unfold ricStarArray
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  change
    (∑ I0 : Fin s → Idx, ∑ e : Idx,
      ric (I0 b) e * cA (Function.update I0 b e) * cB I0) =
    ∑ I0 : Fin s → Idx, ∑ e : Idx,
      cA I0 * (ric (I0 b) e * cB (Function.update I0 b e))
  let F : ((Fin s → Idx) × Idx) → Real := fun Ie =>
    ric (Ie.1 b) Ie.2 * cA (Function.update Ie.1 b Ie.2) * cB Ie.1
  let G : ((Fin s → Idx) × Idx) → Real := fun Ie =>
    cA Ie.1 * (ric (Ie.1 b) Ie.2 * cB (Function.update Ie.1 b Ie.2))
  have hleft :
      (∑ I0 : Fin s → Idx, ∑ e : Idx,
          ric (I0 b) e * cA (Function.update I0 b e) * cB I0) =
        ∑ Ie, F Ie := by
    rw [Fintype.sum_prod_type]
  have hright :
      (∑ I0 : Fin s → Idx, ∑ e : Idx,
          cA I0 * (ric (I0 b) e * cB (Function.update I0 b e))) =
        ∑ Ie, G Ie := by
    rw [Fintype.sum_prod_type]
  rw [hleft, hright]
  refine Fintype.sum_equiv (ricStarArrayUpdateEquiv (Idx := Idx) b) F G ?_
  intro Ie
  rcases Ie with ⟨I0, e⟩
  have hupdate :
      Function.update (Function.update I0 b e) b (I0 b) = I0 := by
    funext q
    by_cases hqb : q = b
    · subst q
      simp
    · simp [Function.update, hqb]
  change
    ric (I0 b) e * cA (Function.update I0 b e) * cB I0 =
      cA (Function.update I0 b e) *
        (ric ((Function.update I0 b e) b) (I0 b) *
          cB (Function.update (Function.update I0 b e) b (I0 b)))
  rw [Function.update_self, hric, hupdate]
  ring

theorem ricReactionContract_eq_two_mul_coordContract_ricStarArray_raise {s : ℕ}
    (gInv ric : Idx → Idx → Real)
    (cA cB : (Fin s → Idx) → Real) :
    ricReactionContract gInv ric cA cB =
      2 * coordContract gInv cA
        (ricStarArray (fun i e => ∑ q : Idx, gInv e q * ric i q) cB) := by
  classical
  unfold ricReactionContract coordContract ricStarArray
  congr 1
  have hslot (I0 : Fin s → Idx) (b : Fin s) :
      (∑ J0 : Fin s → Idx,
          (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
              gInv (I0 a) (J0 a)) *
            (∑ p : Idx, ∑ q : Idx,
              gInv (I0 b) p * gInv (J0 b) q * ric p q) *
            cA I0 * cB J0) =
        ∑ J0 : Fin s → Idx,
          (∏ a : Fin s, gInv (I0 a) (J0 a)) * cA I0 *
            (∑ e : Idx,
              (∑ q : Idx, gInv e q * ric (J0 b) q) *
                cB (Function.update J0 b e)) := by
    let F : ((Fin s → Idx) × Idx) → Real := fun Je =>
      (∏ a : Fin s, gInv (I0 a) (Je.1 a)) * cA I0 *
        ((∑ q : Idx, gInv Je.2 q * ric (Je.1 b) q) *
          cB (Function.update Je.1 b Je.2))
    let G : ((Fin s → Idx) × Idx) → Real := fun Jp =>
      (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
          gInv (I0 a) (Jp.1 a)) *
        (∑ q : Idx,
          gInv (I0 b) Jp.2 * gInv (Jp.1 b) q * ric Jp.2 q) *
        cA I0 * cB Jp.1
    have hF :
        (∑ J0 : Fin s → Idx,
            (∏ a : Fin s, gInv (I0 a) (J0 a)) * cA I0 *
              (∑ e : Idx,
                (∑ q : Idx, gInv e q * ric (J0 b) q) *
                  cB (Function.update J0 b e))) =
          ∑ Je, F Je := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun J0 _ => ?_
      rw [Finset.mul_sum]
    have hG :
        (∑ J0 : Fin s → Idx,
            (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
                gInv (I0 a) (J0 a)) *
              (∑ p : Idx, ∑ q : Idx,
                gInv (I0 b) p * gInv (J0 b) q * ric p q) *
              cA I0 * cB J0) =
          ∑ Jp, G Jp := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun J0 _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    rw [hG, hF]
    exact (Fintype.sum_equiv (ricStarArrayUpdateEquiv (Idx := Idx) b) F G (fun Je => by
      rcases Je with ⟨J0, e⟩
      change
        (∏ a : Fin s, gInv (I0 a) (J0 a)) * cA I0 *
            ((∑ q : Idx, gInv e q * ric (J0 b) q) *
              cB (Function.update J0 b e)) =
          (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
              gInv (I0 a) (Function.update J0 b e a)) *
            (∑ q : Idx,
              gInv (I0 b) (J0 b) *
                gInv (Function.update J0 b e b) q * ric (J0 b) q) *
            cA I0 * cB (Function.update J0 b e)
      rw [show (∏ a : Fin s, gInv (I0 a) (J0 a)) =
          (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
              gInv (I0 a) (J0 a)) * gInv (I0 b) (J0 b) by
        rw [Finset.prod_erase_mul (Finset.univ : Finset (Fin s)) _
          (Finset.mem_univ b)]]
      rw [show
          (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
              gInv (I0 a) (Function.update J0 b e a)) =
            ∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
              gInv (I0 a) (J0 a) by
        refine Finset.prod_congr rfl fun a ha => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase ha)]]
      rw [Function.update_self]
      rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ => ?_
      ring)).symm
  calc
    (∑ I0 : Fin s → Idx, ∑ J0 : Fin s → Idx,
        (∑ b : Fin s,
            (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
                gInv (I0 a) (J0 a)) *
              (∑ p : Idx, ∑ q : Idx,
                gInv (I0 b) p * gInv (J0 b) q * ric p q)) *
          cA I0 * cB J0) =
      ∑ I0 : Fin s → Idx, ∑ b : Fin s, ∑ J0 : Fin s → Idx,
        (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
            gInv (I0 a) (J0 a)) *
          (∑ p : Idx, ∑ q : Idx,
            gInv (I0 b) p * gInv (J0 b) q * ric p q) *
          cA I0 * cB J0 := by
        refine Finset.sum_congr rfl fun I0 _ => ?_
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
    _ = ∑ I0 : Fin s → Idx, ∑ b : Fin s, ∑ J0 : Fin s → Idx,
        (∏ a : Fin s, gInv (I0 a) (J0 a)) * cA I0 *
          (∑ e : Idx,
            (∑ q : Idx, gInv e q * ric (J0 b) q) *
              cB (Function.update J0 b e)) := by
        refine Finset.sum_congr rfl fun I0 _ => ?_
        refine Finset.sum_congr rfl fun b _ => hslot I0 b
    _ = ∑ I0 : Fin s → Idx, ∑ J0 : Fin s → Idx,
        (∏ a : Fin s, gInv (I0 a) (J0 a)) * cA I0 *
          (∑ b : Fin s, ∑ e : Idx,
            (∑ q : Idx, gInv e q * ric (J0 b) q) *
              cB (Function.update J0 b e)) := by
        refine Finset.sum_congr rfl fun I0 _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun J0 _ => ?_
        rw [Finset.mul_sum]

theorem ricReactionContract_symm {s : ℕ}
    (gInv ric : Idx → Idx → Real)
    (cA cB : (Fin s → Idx) → Real)
    (hgInv : ∀ i j, gInv i j = gInv j i)
    (hric : ∀ i j, ric i j = ric j i) :
    ricReactionContract gInv ric cA cB =
      ricReactionContract gInv ric cB cA := by
  classical
  unfold ricReactionContract
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun I0 _ => ?_
  refine Finset.sum_congr rfl fun J0 _ => ?_
  have hcoeff :
      (∑ b : Fin s,
          (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
              gInv (J0 a) (I0 a)) *
            (∑ p : Idx, ∑ q : Idx,
              gInv (J0 b) p * gInv (I0 b) q * ric p q)) =
        ∑ b : Fin s,
          (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
              gInv (I0 a) (J0 a)) *
            (∑ p : Idx, ∑ q : Idx,
              gInv (I0 b) p * gInv (J0 b) q * ric p q) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    have hprod :
        (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
            gInv (J0 a) (I0 a)) =
          ∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
            gInv (I0 a) (J0 a) := by
      refine Finset.prod_congr rfl fun a _ => hgInv (J0 a) (I0 a)
    have hsum :
        (∑ p : Idx, ∑ q : Idx,
            gInv (J0 b) p * gInv (I0 b) q * ric p q) =
          ∑ p : Idx, ∑ q : Idx,
            gInv (I0 b) p * gInv (J0 b) q * ric p q := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => ?_
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hric]
      ring
    rw [hprod, hsum]
  rw [hcoeff]
  ring

theorem ricReactionContract_delta_eq_compContract [DecidableEq Idx] {s : ℕ}
    (ric : Idx → Idx → Real) (cA cB : (Fin s → Idx) → Real) :
    ricReactionContract (identityInvMetric (Idx := Idx)) ric cA cB =
      2 * ∑ I0 : Fin s → Idx, cA I0 * ricStarArray ric cB I0 := by
  classical
  unfold ricReactionContract ricStarArray
  congr 1
  refine Finset.sum_congr rfl fun I0 _ => ?_
  have hric : ∀ (J0 : Fin s → Idx) (b : Fin s),
      (∑ p : Idx, ∑ q : Idx,
          identityInvMetric (Idx := Idx) (I0 b) p *
            identityInvMetric (Idx := Idx) (J0 b) q * ric p q) =
        ric (I0 b) (J0 b) := by
    intro J0 b
    rw [Finset.sum_eq_single (I0 b)]
    · rw [Finset.sum_eq_single (J0 b)]
      · rw [identityInvMetric_apply_self, identityInvMetric_apply_self]; ring
      · intro q _ hq
        rw [show identityInvMetric (Idx := Idx) (J0 b) q = 0 from
          diagonalInvMetric_eq_zero_of_ne (fun h => hq h.symm)]
        ring
      · intro h; exact absurd (Finset.mem_univ (J0 b)) h
    · intro p _ hp
      refine Finset.sum_eq_zero fun q _ => ?_
      rw [show identityInvMetric (Idx := Idx) (I0 b) p = 0 from
        diagonalInvMetric_eq_zero_of_ne (fun h => hp h.symm)]
      ring
    · intro h; exact absurd (Finset.mem_univ (I0 b)) h
  have hstep1 :
      (∑ J0 : Fin s → Idx,
          (∑ b : Fin s,
              (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
                  identityInvMetric (Idx := Idx) (I0 a) (J0 a)) *
                (∑ p : Idx, ∑ q : Idx,
                  identityInvMetric (Idx := Idx) (I0 b) p *
                    identityInvMetric (Idx := Idx) (J0 b) q * ric p q)) *
            cA I0 * cB J0) =
        ∑ b : Fin s, ∑ J0 : Fin s → Idx,
          (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
              identityInvMetric (Idx := Idx) (I0 a) (J0 a)) *
            (ric (I0 b) (J0 b) * cB J0) * cA I0 := by
    have hdist :
        (∑ J0 : Fin s → Idx,
            (∑ b : Fin s,
                (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
                    identityInvMetric (Idx := Idx) (I0 a) (J0 a)) *
                  (∑ p : Idx, ∑ q : Idx,
                    identityInvMetric (Idx := Idx) (I0 b) p *
                      identityInvMetric (Idx := Idx) (J0 b) q * ric p q)) *
              cA I0 * cB J0) =
          ∑ J0 : Fin s → Idx, ∑ b : Fin s,
            (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
                identityInvMetric (Idx := Idx) (I0 a) (J0 a)) *
              (ric (I0 b) (J0 b) * cB J0) * cA I0 := by
      refine Finset.sum_congr rfl fun J0 _ => ?_
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hric J0 b]
      ring
    rw [hdist, Finset.sum_comm]
  rw [hstep1]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hstep2 :
      (∑ J0 : Fin s → Idx,
          (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
              identityInvMetric (Idx := Idx) (I0 a) (J0 a)) *
            (ric (I0 b) (J0 b) * cB J0) * cA I0) =
        cA I0 *
          ∑ J0 : Fin s → Idx,
            (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
                identityInvMetric (Idx := Idx) (I0 a) (J0 a)) *
              (ric (I0 b) (J0 b) * cB J0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun J0 _ => ?_
    ring
  rw [hstep2, sum_delta_erase_slot_eq (Idx := Idx) I0 b
    (fun J0 : Fin s → Idx => ric (I0 b) (J0 b) * cB J0)]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Function.update_self]

theorem hasDerivWithinAt_inner0S_ricciFlow_orthonormal
    [DecidableEq Idx]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    {s : Nat} {x : M} {u : Set Real} {t : Real}
    (g : Real -> SmoothMetric I M)
    (Q : Tensor0SSpace 2 I x)
    (A B : Real -> Tensor0SSpace s I x)
    (Adot Bdot : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      (g t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (hg : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g r).inner x X Y)
        ((-2 : Real) * Q (fun a : Fin 2 => if a = 0 then X else Y)) t)
    (hA : ∀ v : Fin s -> TangentSpace I x,
      HasDerivWithinAt (fun r : Real => A r v) (Adot v) u t)
    (hB : ∀ v : Fin s -> TangentSpace I x,
      HasDerivWithinAt (fun r : Real => B r v) (Bdot v) u t) :
    HasDerivWithinAt
      (fun r : Real => inner0S (I := I) (g r) x s (A r) (B r))
      (2 * ∑ slots : Fin s -> Idx,
          tensor0SComponent (I := I) (A t) basis slots *
            ricStarArray
              (fun i j => Q (fun a : Fin 2 =>
                if a = 0 then basis i else basis j))
              (fun slots' => tensor0SComponent (I := I) (B t) basis slots')
              slots +
        inner0S (I := I) (g t) x s Adot (B t) +
        inner0S (I := I) (g t) x s (A t) Bdot)
      u t := by
  classical
  let gInv : Real -> Idx -> Idx -> Real := fun r =>
    basisInvMetric (I := I) (g r) x basis
  let ric : Idx -> Idx -> Real := fun i j =>
    Q (fun a : Fin 2 => if a = 0 then basis i else basis j)
  let gInvDt : Idx -> Idx -> Real := fun i j =>
    -(∑ p, ∑ q, gInv t i p * ((-2 : Real) * ric p q) * gInv t q j)
  let Adt : (Fin s -> Idx) -> Real := fun slots =>
    tensor0SComponent (I := I) Adot basis slots
  let Bdt : (Fin s -> Idx) -> Real := fun slots =>
    tensor0SComponent (I := I) Bdot basis slots
  have hinvAll (r : Real) :
      MetricInverseInBasisGen (I := I) (g r) x basis (gInv r) := by
    simpa only [gInv] using basisInvMetric_real (I := I) (g r) x basis
  have hgInv (i j : Idx) :
      HasDerivWithinAt (fun r : Real => gInv r i j) (gInvDt i j) u t := by
    have hfull : HasDerivAt (fun r : Real => gInv r i j) (gInvDt i j) t := by
      simpa only [gInv, gInvDt, ric] using
        (basisInv_time (I := I) g (fun p q => (-2 : Real) * ric p q) basis
          (fun p q => by simpa only [ric] using hg (basis p) (basis q)) i j)
    exact hfull.hasDerivWithinAt
  have hflow (i j : Idx) :
      gInvDt i j = 2 * (∑ p, ∑ q, gInv t i p * gInv t j q * ric p q) := by
    have hterm :
        (∑ p, ∑ q, gInv t i p * ((-2 : Real) * ric p q) * gInv t q j) =
          ∑ p, ∑ q, (-2 : Real) *
            (gInv t i p * gInv t j q * ric p q) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [gInv]
      rw [basisInvMetric_symm (I := I) (g t) x basis q j]
      ring
    have hfactor :
        (∑ p, ∑ q, (-2 : Real) *
          (gInv t i p * gInv t j q * ric p q)) =
          (-2 : Real) * (∑ p, ∑ q, gInv t i p * gInv t j q * ric p q) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
    simp only [gInvDt]
    rw [hterm, hfactor]
    ring
  have hmain := hasDerivWithinAt_inner0S_ricciFlow
    (I := I) g gInv gInvDt ric A B Adt Bdt Adot Bdot basis hinvAll hgInv
    (fun slots => hA (fun a => basis (slots a)))
    (fun slots => hB (fun a => basis (slots a)))
    (fun _ => rfl) (fun _ => rfl) hflow
  have hinvId : MetricInverseInBasisGen (I := I) (g t) x basis
      (identityInvMetric (Idx := Idx)) :=
    metricInverseInBasis_identity_of_orthonormal (I := I) (g t) basis horth
  have hgInvId : gInv t = identityInvMetric (Idx := Idx) :=
    invBasis_unique (I := I) (g t) x basis _ _ (hinvAll t) hinvId
  rw [hgInvId, ricReactionContract_delta_eq_compContract] at hmain
  simpa only [ric, Adt, Bdt] using hmain

theorem abs_ricStarArray_le {s : ℕ}
    (ric : Idx → Idx → Real) (cB : (Fin s → Idx) → Real)
    (Rbnd : Real) (hRbnd_nonneg : (0 : Real) ≤ Rbnd)
    (hRbnd : ∀ p q : Idx, |ric p q| ≤ Rbnd)
    (I0 : Fin s → Idx) :
    |ricStarArray ric cB I0| ≤
      (s : Real) * (Fintype.card Idx : Real) * Rbnd *
        Real.sqrt (compNormSqMulti cB) := by
  classical
  unfold ricStarArray
  have hstep :
      |∑ b : Fin s, ∑ e : Idx, ric (I0 b) e * cB (Function.update I0 b e)| ≤
        ∑ b : Fin s, ∑ e : Idx, Rbnd * Real.sqrt (compNormSqMulti cB) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun b _ => ?_
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun e _ => ?_
    rw [abs_mul]
    exact mul_le_mul (hRbnd (I0 b) e)
      (abs_le_sqrt_compNormSqMulti cB (Function.update I0 b e))
      (abs_nonneg _) hRbnd_nonneg
  refine le_trans hstep ?_
  rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
  rw [show ((Fintype.card Idx : Real) *
        (Rbnd * Real.sqrt (compNormSqMulti cB))) =
      (Fintype.card Idx : Real) * Rbnd *
        Real.sqrt (compNormSqMulti cB) from by ring]
  rw [show ((s : Real) *
        ((Fintype.card Idx : Real) * Rbnd *
          Real.sqrt (compNormSqMulti cB))) =
      (s : Real) * (Fintype.card Idx : Real) * Rbnd *
        Real.sqrt (compNormSqMulti cB) from by ring]

end Tensor0SBundle
end DifferentialGeometry
