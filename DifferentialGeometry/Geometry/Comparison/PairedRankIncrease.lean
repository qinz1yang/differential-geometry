import DifferentialGeometry.Geometry.Comparison.BalancedCrossAngles
import DifferentialGeometry.Geometry.Comparison.BalancedMidpoint
import DifferentialGeometry.Geometry.Comparison.PairedPacketExtension

set_option autoImplicit false

open Set Real Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X ι : Type*} [MetricSpace X]

theorem PairedComparisonPacket.exists_extension_of_near_coordinates
    {δ β : ℝ} {V Ω : Set X} {a b : ι → X}
    (hpacket : PairedComparisonPacket δ V a b)
    (hcurves : ∀ x y : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + η))
    (hcomp : fourPointComparison 1 Ω) (hV : V ⊆ Ω)
    (hanchors : range a ∪ range b ⊆ Ω) {a₀ A : ℝ} (ha₀ : 0 < a₀)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hδ : 0 ≤ δ) (hδβ : δ ≤ β / 100)
    (hbounds : ∀ z ∈ V, ∀ c ∈ range a ∪ range b, dist z c ∈ Icc a₀ A)
    {x y : X} (hL : 0 < dist x y) (hL1 : dist x y ≤ 1) (hLa : dist x y ≤ a₀ / 2)
    (hLK : dist x y ≤ (β / (100 * Real.pi)) ^ 2 / (4 * cosh (A + 1) / sinh a₀))
    (hball : closedBall x (dist x y) ⊆ V)
    (hcoord : ∀ i, |dist x (a i) - dist y (a i)| ≤ (β / (100 * Real.pi)) ^ 2 * dist x y) :
    ∃ z ∈ V, dist x z = dist y z ∧ dist x y / 2 ≤ dist x z ∧
      dist x z < 3 * dist x y / 4 ∧
      PairedComparisonPacket β {z} (fun i : Option ι => i.elim x a) (fun i : Option ι => i.elim y b) ∧
      range (fun i : Option ι => i.elim x a) ∪ range (fun i : Option ι => i.elim y b) ⊆ Ω := by
  have hx : x ∈ V := hball (mem_closedBall_self hL.le)
  have hy : y ∈ V := hball (by rw [mem_closedBall, dist_comm y x])
  obtain ⟨_, z, hbal, hslo, hsup, hsup', hang⟩ :=
    exists_balanced_midpoint_with_comparison_angle hcurves x y hL hL1
      (show 0 < β / 100 by positivity) (show β / 100 ≤ 1 by linarith)
  have hsupper : dist x z < 3 * dist x y / 4 := hsup.trans_le hsup'
  have hsL : dist z x ≤ dist x y := by rw [dist_comm]; linarith
  have hz : z ∈ V := hball (by rw [mem_closedBall]; exact hsL)
  have hs : 0 < dist z x := by rw [dist_comm]; linarith
  have hbalance : dist z x = dist z y := by simpa only [dist_comm z x, dist_comm z y] using hbal
  let K := 4 * cosh (A + 1) / sinh a₀
  have hK : 0 < K := div_pos (by positivity) (sinh_pos_iff.mpr ha₀)
  have hKs : K * dist z x ≤ (β / (100 * Real.pi)) ^ 2 := by
    have h := (le_div_iff₀ hK).mp hLK
    have h' := mul_le_mul_of_nonneg_left hsL hK.le
    nlinarith
  have herr := rank_increase_angle_error_lt hβ hδβ hKs
  have hcross : ∀ i, ∀ u ∈ ({a i, b i} : Set X), ∀ v ∈ ({x, y} : Set X),
      Real.pi / 2 - β < comparisonAngleNegCurvature 1 (dist z u) (dist z v) (dist u v) := by
    intro i u hu v hv
    have ha : a i ∈ range a ∪ range b := Or.inl ⟨i, rfl⟩
    have hb : b i ∈ range a ∪ range b := Or.inr ⟨i, rfl⟩
    have h := balanced_cross_angles_near_pi_div_two hcomp (hV hx) (hV hy) (hV hz)
      (hanchors ha) (hanchors hb) ha₀
      (hbounds x hx _ ha) (hbounds y hy _ ha) (hbounds z hz _ ha)
      (hbounds x hx _ hb) (hbounds y hy _ hb) (hbounds z hz _ hb)
      hs (hsL.trans hL1) (hsL.trans hLa) hbalance (sq_nonneg _) hδ
      (show 0 ≤ β / 100 by positivity) (hcoord i)
      (hpacket.opposite x hx i) (hpacket.opposite y hy i) (hpacket.opposite z hz i) hang u hu v hv
    have hlo := (abs_le.mp h).1
    change 2 * δ + 3 * (β / 100) / 2 + 4 * (Real.pi * sqrt ((4 * cosh (A + 1) / sinh a₀) * dist z x)) +
      (Real.pi * sqrt ((β / (100 * Real.pi)) ^ 2 + (4 * cosh (A + 1) / sinh a₀) * dist z x)) / 2 < β / 10 at herr
    linarith
  have hβpacket := (hpacket.weaken (show δ ≤ β by linarith)).mono
    (show {z} ⊆ V from singleton_subset_iff.mpr hz)
  refine ⟨z, hz, hbal, hslo, hsupper, hβpacket.extend (by linarith) hcross, ?_⟩
  rintro c (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · cases i with
    | none => exact hV hx
    | some i => exact hanchors (Or.inl ⟨i, rfl⟩)
  · cases i with
    | none => exact hV hy
    | some i => exact hanchors (Or.inr ⟨i, rfl⟩)

end DifferentialGeometry.Geometry.Comparison.Toponogov
