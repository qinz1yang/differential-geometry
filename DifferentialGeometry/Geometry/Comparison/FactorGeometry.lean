import DifferentialGeometry.Geometry.Metric.L2Product
import DifferentialGeometry.Geometry.Comparison.FourPoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.HausdorffDimension

set_option autoImplicit false

open Set MeasureTheory

namespace IsometryEquiv

variable {X E Y : Type*} [MetricSpace X] [MetricSpace E] [MetricSpace Y]

theorem l2_product_fst_eq_of_dist_add_eq (e : X ≃ᵢ WithLp 2 (E × Y))
    {u : E} {a b z : X} (ha : (e a).fst = u) (hb : (e b).fst = u)
    (hz : dist a z + dist z b = dist a b) : (e z).fst = u := by
  have hrep (w : X) (hw : (e w).fst = u) :
      e w = WithLp.toLp 2 (u, (e w).snd) := by
    apply (WithLp.equiv 2 _).injective
    exact Prod.ext hw rfl
  have hd : dist (e a) (e z) + dist (e z) (e b) = dist (e a) (e b) := by
    simpa only [e.dist_eq] using hz
  rw [hrep a ha, hrep b hb, (WithLp.isometry_prodMk_left u).dist_eq (e a).snd (e b).snd] at hd
  exact WithLp.fst_eq_of_dist_add_eq u (e a).snd (e b).snd (e z) hd

theorem exists_segment_l2_product_factor (e : X ≃ᵢ WithLp 2 (E × Y)) (u : E)
    (hsegments : ∀ a b : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t)
    (a b : Y) : ∃ f : Icc (0 : ℝ) 1 → Y,
      Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t := by
  let g : Y → X := fun y => e.symm (WithLp.toLp 2 (u, y))
  have hg : Isometry g := e.symm.isometry.comp (WithLp.isometry_prodMk_left u)
  obtain ⟨f, hf, hzero, hone, hd⟩ := hsegments (g a) (g b)
  have hfst (t : Icc (0 : ℝ) 1) : (e (f t)).fst = u := by
    apply e.l2_product_fst_eq_of_dist_add_eq (a := g a) (b := g b) (by simp [g]) (by simp [g])
    have h₁ := hd ⟨0, by norm_num⟩ t
    have h₂ := hd t ⟨1, by norm_num⟩
    rw [hzero] at h₁
    rw [hone] at h₂
    simp only [Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg,
      abs_of_nonneg t.property.1] at h₁
    simp only [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr t.property.2),
      neg_sub] at h₂
    linarith
  have hrep (t : Icc (0 : ℝ) 1) : e (f t) = WithLp.toLp 2 (u, (e (f t)).snd) := by
    apply (WithLp.equiv 2 _).injective
    exact Prod.ext (hfst t) rfl
  refine ⟨fun t => (e (f t)).snd,
    (WithLp.continuous_snd 2 E Y).comp (e.continuous.comp hf), ?_, ?_, ?_⟩
  · change (e (f ⟨0, by norm_num⟩)).snd = a
    rw [hzero]
    simp [g]
  · change (e (f ⟨1, by norm_num⟩)).snd = b
    rw [hone]
    simp [g]
  · intro s t
    have h := e.dist_eq (f s) (f t)
    rw [hrep s, hrep t, (WithLp.isometry_prodMk_left u).dist_eq (e (f s)).snd (e (f t)).snd,
      hd, hg.dist_eq] at h
    exact h

theorem dimH_l2_product_factor_le (e : X ≃ᵢ WithLp 2 (E × Y)) (u : E) :
    dimH (univ : Set Y) ≤ dimH (univ : Set X) := by
  have hi := e.symm.isometry.comp (WithLp.isometry_prodMk_left (Y := Y) u)
  rw [← hi.dimH_image]
  exact dimH_mono (subset_univ _)

theorem euclidean_rank_le_dimH {k : ℕ}
    (e : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Y)) (y : Y) :
    (k : ENNReal) ≤ dimH (univ : Set X) := by
  have hi := e.symm.isometry.comp
    (WithLp.isometry_prodMk_right (E := EuclideanSpace ℝ (Fin k)) y)
  have hdim := hi.dimH_image (univ : Set (EuclideanSpace ℝ (Fin k)))
  rw [Real.dimH_univ_eq_finrank, finrank_euclideanSpace_fin] at hdim
  rw [← hdim]
  exact dimH_mono (subset_univ _)

end IsometryEquiv

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem fourPointComparison.of_isometry {κ : ℝ} (h : fourPointComparison κ (univ : Set X))
    {f : Y → X} (hf : Isometry f) : fourPointComparison κ (univ : Set Y) := by
  intro p hp a ha b hb c hc hap hbp hcp
  have hh := h (f p) (mem_univ _) (f a) (mem_univ _) (f b) (mem_univ _) (f c) (mem_univ _)
    (fun he => hap (hf.injective he)) (fun he => hbp (hf.injective he))
    (fun he => hcp (hf.injective he))
  simpa only [hf.dist_eq] using hh

theorem fourPointComparison_l2_product_factor {E : Type*} [MetricSpace E] {κ : ℝ}
    (h : fourPointComparison κ (univ : Set X))
    (e : X ≃ᵢ WithLp 2 (E × Y)) (u : E) : fourPointComparison κ (univ : Set Y) :=
  h.of_isometry (e.symm.isometry.comp (WithLp.isometry_prodMk_left u))

end DifferentialGeometry.Geometry.Comparison.Toponogov
