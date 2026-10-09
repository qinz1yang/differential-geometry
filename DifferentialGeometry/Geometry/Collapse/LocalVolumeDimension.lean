import DifferentialGeometry.Geometry.Comparison.RadialEuclideanPacking
import DifferentialGeometry.Topology.MetricSpace.FiniteNets
import DifferentialGeometry.Topology.MetricSpace.PolynomialCovering
import DifferentialGeometry.Topology.MetricSpace.CeilCoveringBound
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

noncomputable section

open Set Metric Real
open scoped ENNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X]

private theorem annulus_dimH_le_of_chart
    (hcurves : ∀ x y : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + η))
    (hcomp : fourPointComparison 1 (univ : Set X))
    {q : X} {ρ L : ℝ} (hρ : 0 < ρ) (hL : 1 ≤ L) {m : ℕ} (hm : 0 < m)
    (f : ball q ρ → EuclideanSpace ℝ (Fin m))
    (hlower : ∀ x y, L⁻¹ * dist x y ≤ dist (f x) (f y))
    (hupper : ∀ x y, dist (f x) (f y) ≤ L * dist x y)
    {a D : ℝ} (ha : 0 < a) (haD : a ≤ D) :
    dimH {x : X | dist q x ∈ Icc a D} ≤ m := by
  let t := min (1 / 2) (ρ / (2 * D))
  have hD : 0 < D := ha.trans_le haD
  have ht : t ∈ Ioo 0 1 :=
    ⟨lt_min (by norm_num) (by positivity), (min_le_left _ _).trans_lt (by norm_num)⟩
  have htD : t * D < ρ := by
    have h := mul_le_mul_of_nonneg_right (min_le_right (1 / 2) (ρ / (2 * D))) hD.le
    have he : ρ / (2 * D) * D = ρ / 2 := by field_simp
    rw [he] at h
    exact h.trans_lt (half_lt_self hρ)
  let g : ball q ρ → EuclideanSpace ℝ (Fin m) :=
    fun x => f x - f ⟨q, mem_ball_self hρ⟩
  have hg0 : g ⟨q, mem_ball_self hρ⟩ = 0 := sub_self _
  have hgl : ∀ x y, L⁻¹ * dist x y ≤ dist (g x) (g y) := by
    intro x y
    simpa only [g, dist_sub_right] using hlower x y
  have hgu : ∀ x y, dist (g x) (g y) ≤ L * dist x y := by
    intro x y
    simpa only [g, dist_sub_right] using hupper x y
  let B := 8 * L ^ 2 * ρ * sqrt m / (t * D / sinh D)
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hB : 0 < B := by
    dsimp [B]
    have hs : 0 < sqrt (m : ℝ) := sqrt_pos.mpr (by exact_mod_cast hm)
    have hh : 0 < sinh D := sinh_pos_iff.mpr hD
    positivity
  have hd : dimH {x : X | dist q x ∈ Icc a D} ≤ ENNReal.ofReal (m : ℝ) := by
    apply dimH_le_of_polynomial_nets (Nat.cast_nonneg m) (by positivity : 0 < (2 + B) ^ m)
    intro ε hε hεone
    have hpack := finitePackingNumber_le_of_radial_centered_dist_bounds
      hcurves hcomp (mem_univ q) ha haD ht htD hε (subset_univ _) (subset_univ _)
      (fun x hx => hx) hm hρ hLp hg0 hgl hgu
    have he : 8 * L ^ 2 * ρ * sqrt m / ((t * D / sinh D) * ε) = B / ε := by
      dsimp [B]
      rw [div_div]
    rw [he] at hpack
    obtain ⟨S, hcard, hS, hnet⟩ := exists_finset_net_card_le_of_packing hε
      (⌊(1 + B / ε) ^ m⌋₊) (fun A hA hsep => by
        exact_mod_cast (card_le_finitePackingNumber A hA hsep).trans hpack)
    refine ⟨S, fun x hx => hS hx, ?_, fun x hx => ?_⟩
    · have hfloor := Nat.floor_le (by positivity : 0 ≤ (1 + B / ε) ^ m)
      have hceil : (1 + B / ε) ^ m ≤
          (((1 + Nat.ceil (B / ε)) ^ m : ℕ) : ℝ) := by
        push_cast
        exact pow_le_pow_left₀ (by positivity) (by linarith [Nat.le_ceil (B / ε)]) m
      exact (show (S.card : ℝ) ≤ (⌊(1 + B / ε) ^ m⌋₊ : ℝ) by
        exact_mod_cast hcard).trans
          (hfloor.trans (hceil.trans (ceil_covering_bound_le_polynomial hB.le hε hεone m)))
    · obtain ⟨y, hy, hxy⟩ := hnet x hx
      exact ⟨y, hy, hxy.le⟩
  simpa using hd

/-- LC10: a single open bilipschitz chart determines global dimension, without completeness. -/
theorem dimH_eq_of_open_bilipschitz_ball
    (hcurves : ∀ x y : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + η))
    (hcomp : fourPointComparison 1 (univ : Set X))
    (q : X) {ρ L : ℝ} (hρ : 0 < ρ) (hL : 1 ≤ L) {m : ℕ} (hm : 0 < m)
    (f : ball q ρ → EuclideanSpace ℝ (Fin m))
    (hlower : ∀ x y, L⁻¹ * dist x y ≤ dist (f x) (f y))
    (hupper : ∀ x y, dist (f x) (f y) ≤ L * dist x y) (hopen : IsOpen (range f)) :
    dimH (univ : Set X) = m := by
  let A : ℕ → Set X := fun n => {x | dist q x ∈ Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)}
  have hA : ∀ n, dimH (A n) ≤ m := by
    intro n
    apply annulus_dimH_le_of_chart hcurves hcomp hρ hL hm f hlower hupper (by positivity)
    have hden : 1 ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    exact (div_le_one (by positivity)).2 hden |>.trans hden
  have hcover : (univ : Set X) = {q} ∪ ⋃ n, A n := by
    symm
    apply eq_univ_iff_forall.mpr
    intro x
    by_cases hx : x = q
    · exact Or.inl hx
    · have hd : 0 < dist q x := dist_pos.mpr (Ne.symm hx)
      obtain ⟨n, hn⟩ := exists_nat_gt (max (dist q x) ((dist q x)⁻¹))
      have hlo : (dist q x)⁻¹ < (n : ℝ) + 1 := by linarith [le_max_right (dist q x) ((dist q x)⁻¹)]
      have hh : 1 < ((n : ℝ) + 1) * dist q x := (inv_lt_iff_one_lt_mul₀ hd).mp hlo
      exact Or.inr (mem_iUnion.mpr ⟨n, (div_le_iff₀ (by positivity)).mpr (by linarith),
        by linarith [le_max_left (dist q x) ((dist q x)⁻¹)]⟩)
  have hupperdim : dimH (univ : Set X) ≤ m := by
    rw [hcover, dimH_union, dimH_singleton, dimH_iUnion]
    exact max_le (by positivity) (iSup_le hA)
  have hf : LipschitzWith ⟨L, (zero_le_one.trans hL)⟩ f :=
    LipschitzWith.of_dist_le_mul hupper
  have hfrange : dimH (range f) = m := by
    have hd := Real.dimH_of_nonempty_interior (s := range f)
      (by rw [hopen.interior_eq]; exact ⟨f ⟨q, mem_ball_self hρ⟩, mem_range_self _⟩)
    rw [finrank_euclideanSpace_fin] at hd
    exact hd
  have hchart : dimH (range f) ≤ dimH (ball q ρ) := by
    have h := hf.dimH_image_le (univ : Set (ball q ρ))
    have hi := (isometry_subtype_coe (s := ball q ρ)).dimH_image (univ : Set (ball q ρ))
    simpa only [image_univ, Subtype.range_coe] using h.trans_eq hi.symm
  exact le_antisymm hupperdim (hfrange ▸ hchart.trans (dimH_mono (subset_univ _)))

end DifferentialGeometry.Geometry.Collapse
