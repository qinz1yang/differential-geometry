import Mathlib.Topology.Path
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open Set

namespace Path

variable {X : Type*} [PseudoEMetricSpace X] {x y z : X}

theorem eVariationOn_extend (γ : Path x y) :
    eVariationOn γ.extend (Icc (0 : ℝ) 1) = eVariationOn γ univ := by
  have heq : γ.extend ∘ (fun t : unitInterval => (t : ℝ)) = γ := by
    funext t
    exact γ.extend_extends' t
  have ht := eVariationOn.comp_eq_of_monotoneOn γ.extend
    (fun t : unitInterval => (t : ℝ))
    (show MonotoneOn (fun t : unitInterval => (t : ℝ)) univ from fun _ _ _ _ h => h)
  rw [heq, image_univ, Subtype.range_val] at ht
  exact ht.symm

theorem eVariationOn_symm (γ : Path x y) :
    eVariationOn γ.symm univ = eVariationOn γ univ := by
  have hle {a b : X} (η : Path a b) : eVariationOn η.symm univ ≤ eVariationOn η univ := by
    apply eVariationOn.comp_le_of_antitoneOn η unitInterval.symm
    · intro s hs t ht hst
      change 1 - (t : ℝ) ≤ 1 - (s : ℝ)
      exact sub_le_sub_left (show (s : ℝ) ≤ (t : ℝ) from hst) 1
    · exact fun _ _ => mem_univ _
  exact le_antisymm (hle γ) (by simpa only [symm_symm] using hle γ.symm)

theorem eVariationOn_trans (γ : Path x y) (η : Path y z) :
    eVariationOn (γ.trans η) univ = eVariationOn γ univ + eVariationOn η univ := by
  rw [← eVariationOn_extend, ← eVariationOn_extend γ, ← eVariationOn_extend η]
  have hleft : eVariationOn (γ.trans η).extend (Icc (0 : ℝ) (1 / 2)) =
      eVariationOn γ.extend (Icc (0 : ℝ) 1) := by
    have hc : EqOn (γ.trans η).extend (γ.extend ∘ (fun t : ℝ => 2 * t)) (Icc (0 : ℝ) (1 / 2)) :=
      fun t ht => extend_trans_of_le_half γ η ht.2
    rw [eVariationOn.congr hc,
      eVariationOn.comp_eq_of_monotoneOn γ.extend _
        (show MonotoneOn (fun t : ℝ => 2 * t) (Icc 0 (1 / 2)) from
          fun _ _ _ _ h => mul_le_mul_of_nonneg_left h (by norm_num))]
    congr 1
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      constructor <;> linarith [hs.1, hs.2]
    · intro ht
      refine ⟨t / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, by ring⟩
  have hright : eVariationOn (γ.trans η).extend (Icc (1 / 2 : ℝ) 1) =
      eVariationOn η.extend (Icc (0 : ℝ) 1) := by
    have hc : EqOn (γ.trans η).extend (η.extend ∘ (fun t : ℝ => 2 * t - 1)) (Icc (1 / 2 : ℝ) 1) :=
      fun t ht => extend_trans_of_half_le γ η ht.1
    rw [eVariationOn.congr hc,
      eVariationOn.comp_eq_of_monotoneOn η.extend _
        (show MonotoneOn (fun t : ℝ => 2 * t - 1) (Icc (1 / 2) 1) from
          fun _ _ _ _ h => sub_le_sub_right (mul_le_mul_of_nonneg_left h (by norm_num)) 1)]
    congr 1
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      constructor <;> linarith [hs.1, hs.2]
    · intro ht
      refine ⟨(t + 1) / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, by ring⟩
  have ht := eVariationOn.Icc_add_Icc (γ.trans η).extend (s := univ)
    (a := (0 : ℝ)) (b := 1 / 2) (c := 1) (by norm_num) (by norm_num) (mem_univ _)
  simp only [univ_inter] at ht
  rw [hleft, hright] at ht
  exact ht.symm

end Path
