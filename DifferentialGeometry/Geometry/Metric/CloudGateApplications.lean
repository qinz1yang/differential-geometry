import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Fixed-data threshold gates on the actual compact image and its relative closed support. -/

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry

variable {M H : Type*} [TopologicalSpace M] [CompactSpace M] [NormedAddCommGroup H]

theorem exists_fixedData_gate_support_tolerance
    (O : Set H) (hO : IsOpen O) (F : M → O) (hF : Continuous F)
    (ρ : M → ℝ) (hρ : Continuous ρ) (A : Set M) (hA : IsOpen A)
    (G ψ : O → ℝ) (hG : Continuous G)
    (hgate : tsupport ψ ⊆ {z | (1 / 2 : ℝ) ≤ G z})
    (houtside : ∀ p ∉ A, G (F p) = 0) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ f : M → H,
      (∀ p, ‖f p - (F p : H)‖ ≤ κ * ρ p) →
      ∀ p, ∃ hp : f p ∈ O, (⟨f p, hp⟩ : O) ∈ tsupport ψ → p ∈ A := by
  let Fambient : M → H := fun p => (F p : H)
  have hFc : Continuous Fambient := continuous_subtype_val.comp hF
  have hcompact : IsCompact (range Fambient) := isCompact_range hFc
  have hinO : range Fambient ⊆ O := by
    rintro z ⟨p, rfl⟩
    exact (F p).property
  obtain ⟨δ₀, hδ₀, hnearO⟩ := hcompact.exists_cthickening_subset_open hO hinO
  let V : Set H := Subtype.val '' {z : O | G z < 1 / 2}
  have hV : IsOpen V := hO.isOpenMap_subtype_val _ (isOpen_lt hG continuous_const)
  have hbadCompact : IsCompact (Fambient '' Aᶜ) :=
    (hA.isClosed_compl.isCompact).image hFc
  have hbadV : Fambient '' Aᶜ ⊆ V := by
    rintro z ⟨p, hp, rfl⟩
    refine ⟨F p, ?_, rfl⟩
    change G (F p) < 1 / 2
    rw [houtside p hp]
    norm_num
  obtain ⟨δ₁, hδ₁, hnearV⟩ := hbadCompact.exists_cthickening_subset_open hV hbadV
  obtain ⟨R, hR⟩ := (isCompact_range hρ).bddAbove
  let Rmax : ℝ := max 1 R
  have hRmax : 0 < Rmax := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hρbound (p : M) : ρ p ≤ Rmax :=
    (hR (mem_range_self p)).trans (le_max_right _ _)
  let κ : ℝ := min δ₀ δ₁ / (2 * Rmax)
  have hκ : 0 < κ := div_pos (lt_min hδ₀ hδ₁) (by positivity)
  refine ⟨κ, hκ, ?_⟩
  intro f hclose p
  have hd : dist (f p) (Fambient p) ≤ min δ₀ δ₁ := by
    rw [dist_eq_norm]
    have hb := mul_le_mul_of_nonneg_left (hρbound p) hκ.le
    have heq : κ * Rmax = min δ₀ δ₁ / 2 := by
      dsimp only [κ]
      field_simp
    rw [heq] at hb
    exact (hclose p).trans (hb.trans (by linarith [lt_min hδ₀ hδ₁]))
  have hp : f p ∈ O := hnearO (mem_cthickening_of_dist_le
    (f p) (Fambient p) δ₀ (range Fambient) (mem_range_self p)
    (hd.trans (min_le_left _ _)))
  refine ⟨hp, ?_⟩
  intro hsupport
  by_contra hnot
  have hv : f p ∈ V := hnearV (mem_cthickening_of_dist_le
    (f p) (Fambient p) δ₁ (Fambient '' Aᶜ) ⟨p, hnot, rfl⟩
    (hd.trans (min_le_right _ _)))
  obtain ⟨z, hz, heq⟩ := hv
  have hz' : z = (⟨f p, hp⟩ : O) := Subtype.ext heq
  have hg : G (⟨f p, hp⟩ : O) < 1 / 2 := by simpa only [hz', Set.mem_ofPred_eq] using hz
  exact (not_lt_of_ge (hgate hsupport)) hg

theorem exists_bounded_fixedData_gate_support_tolerance
    (O : Set H) (hO : IsOpen O) (F : M → O) (hF : Continuous F)
    (ρ : M → ℝ) (hρ : Continuous ρ) (hρnonneg : ∀ p, 0 ≤ ρ p)
    (A : Set M) (hA : IsOpen A) (G ψ : O → ℝ) (hG : Continuous G)
    (hgate : tsupport ψ ⊆ {z | (1 / 2 : ℝ) ≤ G z})
    (houtside : ∀ p ∉ A, G (F p) = 0) {c : ℝ} (hc : 0 < c) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ c ∧ ∀ f : M → H,
      (∀ p, ‖f p - (F p : H)‖ ≤ κ * ρ p) →
      ∀ p, ∃ hp : f p ∈ O, (⟨f p, hp⟩ : O) ∈ tsupport ψ → p ∈ A := by
  obtain ⟨κ₀, hκ₀, hproduce⟩ := exists_fixedData_gate_support_tolerance
    O hO F hF ρ hρ A hA G ψ hG hgate houtside
  refine ⟨min κ₀ c, lt_min hκ₀ hc, min_le_right _ _, ?_⟩
  intro f hclose
  exact hproduce f (fun p => (hclose p).trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (hρnonneg p)))

theorem fixedData_zero_gate_consumer :
    ∃ κ : ℝ, 0 < κ ∧ ∀ f : Unit → ℝ,
      (∀ p, ‖f p‖ ≤ κ) → ∀ p, f p ∈ Metric.ball 0 2 := by
  have hh := exists_fixedData_gate_support_tolerance
    (M := Unit) (H := ℝ) (ball 0 2) isOpen_ball
    (fun p => ⟨0, by norm_num [mem_ball]⟩)
    continuous_const (fun p => 1) continuous_const ∅ isOpen_empty
    (fun z => 0) (fun z => 0) continuous_const (by simp) (by intro p hp; rfl)
  obtain ⟨κ, hκ, hproduce⟩ := hh
  refine ⟨κ, hκ, ?_⟩
  intro f hf p
  have hp := hproduce f (by intro q; simpa only [sub_zero, mul_one] using hf q) p
  exact hp.choose

end GC.MetricGeometry
