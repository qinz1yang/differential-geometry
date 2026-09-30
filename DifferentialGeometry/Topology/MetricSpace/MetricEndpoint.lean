import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set

namespace Metric

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

def IsEndpoint (p : X) : Prop :=
  ∀ x y : X, dist x p + dist p y = dist x y → x = p ∨ y = p

theorem isEndpoint_isometryEquiv_iff (e : X ≃ᵢ Y) (p : X) :
    IsEndpoint (e p) ↔ IsEndpoint p := by
  constructor
  · intro h x y hxy
    have h' := h (e x) (e y) (by simpa only [e.dist_eq] using hxy)
    exact h'.imp (fun h => e.injective h) (fun h => e.injective h)
  · intro h a b hab
    obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    exact (h x y (by simpa only [e.dist_eq] using hab)).imp (congrArg e) (congrArg e)

theorem not_isEndpoint_real (p : ℝ) : ¬ IsEndpoint p := by
  intro hp
  have hdist : dist (p - 1) p + dist p (p + 1) = dist (p - 1) (p + 1) := by
    simp only [Real.dist_eq]
    rw [show p - 1 - p = -1 by ring, show p - (p + 1) = -1 by ring,
      show p - 1 - (p + 1) = -2 by ring]
    norm_num
  rcases hp (p - 1) (p + 1) hdist with h | h <;> linarith

theorem isEndpoint_Ici_iff (p : Ici (0 : ℝ)) : IsEndpoint p ↔ (p : ℝ) = 0 := by
  constructor
  · intro hp
    have hp0 : 0 ≤ (p : ℝ) := p.property
    let x : Ici (0 : ℝ) := ⟨0, by simp⟩
    let y : Ici (0 : ℝ) := ⟨2 * p, by change 0 ≤ 2 * (p : ℝ); linarith⟩
    have he : dist x p + dist p y = dist x y := by
      change |0 - (p : ℝ)| + |(p : ℝ) - 2 * p| = |0 - 2 * (p : ℝ)|
      rw [abs_of_nonpos (by linarith [hp0]), abs_of_nonpos (by linarith [hp0]),
        abs_of_nonpos (by linarith [hp0])]
      ring
    rcases hp x y he with h | h
    · exact (congrArg (fun t : Ici (0 : ℝ) => (t : ℝ)) h).symm
    · have hh := congrArg (fun t : Ici (0 : ℝ) => (t : ℝ)) h
      change 2 * (p : ℝ) = p at hh
      linarith
  · intro hp x y hxy
    change |(x : ℝ) - p| + |(p : ℝ) - y| = |(x : ℝ) - y| at hxy
    rw [hp, sub_zero, zero_sub, abs_neg, abs_of_nonneg x.property,
      abs_of_nonneg y.property] at hxy
    rcases le_total (x : ℝ) y with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hxy
      exact Or.inl (Subtype.ext (by linarith))
    · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hxy
      exact Or.inr (Subtype.ext (by linarith))

theorem isEndpoint_Icc_iff {L : ℝ} (hL : 0 ≤ L) (p : Icc (0 : ℝ) L) :
    IsEndpoint p ↔ (p : ℝ) = 0 ∨ (p : ℝ) = L := by
  constructor
  · intro hp
    let x : Icc (0 : ℝ) L := ⟨0, le_rfl, hL⟩
    let y : Icc (0 : ℝ) L := ⟨L, hL, le_rfl⟩
    have he : dist x p + dist p y = dist x y := by
      change |0 - (p : ℝ)| + |(p : ℝ) - L| = |0 - L|
      rw [abs_of_nonpos (by linarith [p.property.1]),
        abs_of_nonpos (by linarith [p.property.2]), abs_of_nonpos (by linarith)]
      ring
    rcases hp x y he with h | h
    · exact Or.inl (congrArg (fun t : Icc (0 : ℝ) L => (t : ℝ)) h).symm
    · exact Or.inr (congrArg (fun t : Icc (0 : ℝ) L => (t : ℝ)) h).symm
  · rintro (hp | hp) x y hxy
    · change |(x : ℝ) - p| + |(p : ℝ) - y| = |(x : ℝ) - y| at hxy
      rw [hp, sub_zero, zero_sub, abs_neg, abs_of_nonneg x.property.1,
        abs_of_nonneg y.property.1] at hxy
      rcases le_total (x : ℝ) y with h | h
      · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hxy
        exact Or.inl (Subtype.ext (by linarith))
      · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hxy
        exact Or.inr (Subtype.ext (by linarith))
    · change |(x : ℝ) - p| + |(p : ℝ) - y| = |(x : ℝ) - y| at hxy
      rw [hp, abs_of_nonpos (sub_nonpos.mpr x.property.2),
        abs_of_nonneg (sub_nonneg.mpr y.property.2)] at hxy
      rcases le_total (x : ℝ) y with h | h
      · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hxy
        exact Or.inr (Subtype.ext (by linarith))
      · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hxy
        exact Or.inl (Subtype.ext (by linarith))

end Metric
