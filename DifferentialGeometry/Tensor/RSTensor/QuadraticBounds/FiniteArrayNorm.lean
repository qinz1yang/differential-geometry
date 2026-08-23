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
