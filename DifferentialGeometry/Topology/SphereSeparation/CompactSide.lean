import Mathlib.Topology.MetricSpace.Bounded
import DifferentialGeometry.Topology.FundamentalGroup.Sphere
import DifferentialGeometry.Topology.SphereSeparation.Defs

set_option autoImplicit false

namespace DifferentialGeometry.Topology.SphereSeparation

open Set

theorem not_isPreconnected_compl_sphereTwoProdReal_zeroSlice :
    ¬ IsPreconnected (Set.range (fun x : SphereTwo => (x, (0 : ℝ))))ᶜ := by
  intro hconn
  let p₀ : SphereTwo :=
    ⟨sphereTwoNorthVector, by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_sphereTwoNorthVector]⟩
  have hleft : ((p₀, (1 : ℝ)) : SphereTwo × ℝ) ∈
      (Set.range (fun x : SphereTwo => (x, (0 : ℝ))))ᶜ := by
    rintro ⟨x, hx⟩
    exact absurd (congrArg Prod.snd hx) (by norm_num)
  have hright : ((p₀, (-1 : ℝ)) : SphereTwo × ℝ) ∈
      (Set.range (fun x : SphereTwo => (x, (0 : ℝ))))ᶜ := by
    rintro ⟨x, hx⟩
    exact absurd (congrArg Prod.snd hx) (by norm_num)
  have hsub : (Set.range (fun x : SphereTwo => (x, (0 : ℝ))))ᶜ ⊆
      (fun p : SphereTwo × ℝ => p.2) ⁻¹' (Iio (0 : ℝ) ∪ Ioi (0 : ℝ)) := by
    intro p hp
    have hne : p.2 ≠ 0 := by
      intro hzero
      exact hp ⟨p.1, Prod.ext rfl hzero.symm⟩
    simpa only [mem_preimage, mem_union, mem_Iio, mem_Ioi] using lt_or_gt_of_ne hne
  have hdisj : Disjoint ((fun p : SphereTwo × ℝ => p.2) ⁻¹' Iio (0 : ℝ))
      ((fun p : SphereTwo × ℝ => p.2) ⁻¹' Ioi (0 : ℝ)) := by
    rw [Set.disjoint_left]
    intro p ha hb
    simp only [mem_preimage, mem_Iio] at ha
    simp only [mem_preimage, mem_Ioi] at hb
    linarith
  rcases hconn.subset_or_subset
    (isOpen_Iio.preimage continuous_snd) (isOpen_Ioi.preimage continuous_snd)
    hdisj hsub with h | h
  · exact absurd (h hleft) (by simp only [mem_preimage, mem_Iio]; norm_num)
  · exact absurd (h hright) (by simp only [mem_preimage, mem_Ioi]; norm_num)

namespace SphereSides

variable {X : Type*} [TopologicalSpace X] {S : Set X}

theorem endSide_eq_compl_closure_compactSide (d : SphereSides S) :
    d.endSide = (closure d.compactSide)ᶜ := by
  rw [d.closure_compactSide]
  ext x
  simp only [mem_compl_iff, mem_union, not_or]
  constructor
  · intro hx
    exact ⟨fun hc => Set.disjoint_left.mp d.disjoint hc hx,
      fun hS => d.endSide_subset_compl hx hS⟩
  · rintro ⟨hc, hS⟩
    have hx : x ∈ d.compactSide ∪ d.endSide := by
      rw [d.union_eq_compl]
      exact hS
    exact hx.resolve_left hc

theorem not_nonempty_sphereTwoProdReal_zeroSlice :
    ¬ Nonempty
      (SphereSides (Set.range (fun x : SphereTwo => (x, (0 : ℝ))))) := by
  rintro ⟨d⟩
  let g : SphereTwo × ℝ → ℝ := fun p => p.2
  have hg : Continuous g := continuous_snd
  have hend : d.endSide = (closure d.compactSide)ᶜ :=
    d.endSide_eq_compl_closure_compactSide
  let p₀ : SphereTwo :=
    ⟨sphereTwoNorthVector, by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_sphereTwoNorthVector]⟩
  have hbdd : Bornology.IsBounded (g '' closure d.compactSide) :=
    (d.isCompact_closure_compactSide.image hg).isBounded
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hbdd
  have hfar : ∀ t : ℝ, r < |t| → (p₀, t) ∈ d.endSide := by
    intro t ht
    rw [hend]
    intro hcon
    have h1 : t ∈ g '' closure d.compactSide := ⟨(p₀, t), hcon, rfl⟩
    have h2 : t ∈ Metric.closedBall (0 : ℝ) r := hr h1
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h2
    linarith
  have hpos : (p₀, r + 1) ∈ d.endSide :=
    hfar (r + 1) (by have h := le_abs_self (r + 1); linarith)
  have hneg : (p₀, -(r + 1)) ∈ d.endSide :=
    hfar (-(r + 1)) (by rw [abs_neg]; have h := le_abs_self (r + 1); linarith)
  have hsub : d.endSide ⊆ g ⁻¹' (Iio (0 : ℝ) ∪ Ioi (0 : ℝ)) := by
    intro p hp
    have hne : g p ≠ 0 := by
      intro hzero
      exact (d.endSide_subset_compl hp) ⟨p.1, Prod.ext rfl hzero.symm⟩
    simpa only [mem_preimage, mem_union, mem_Iio, mem_Ioi] using lt_or_gt_of_ne hne
  have hdisj : Disjoint (g ⁻¹' Iio (0 : ℝ)) (g ⁻¹' Ioi (0 : ℝ)) := by
    rw [Set.disjoint_left]
    intro p ha hb
    simp only [mem_preimage, mem_Iio] at ha
    simp only [mem_preimage, mem_Ioi] at hb
    linarith
  rcases (d.isConnected_endSide.isPreconnected).subset_or_subset
    (isOpen_Iio.preimage hg) (isOpen_Ioi.preimage hg) hdisj hsub with h | h
  · have h1 : r + 1 < 0 := h hpos
    have h2 : -(r + 1) < 0 := h hneg
    linarith
  · have h1 : 0 < r + 1 := h hpos
    have h2 : 0 < -(r + 1) := h hneg
    linarith

end SphereSides

end DifferentialGeometry.Topology.SphereSeparation
