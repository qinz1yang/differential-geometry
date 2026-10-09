import DifferentialGeometry.Geometry.Metric.Approximation.ProductAnchorParameters
import DifferentialGeometry.Geometry.Metric.Approximation.RealProductRescaling

/-!
# Long product anchors at an arbitrary scale (metric part of LFR19)

The unit-scale anchor calculation `exists_uniform_product_anchor_parameters` (LC78, metric part)
is transported to scale `L > 0`: the source and the factor are rescaled by `L⁻¹`
(`KleinerLottApprox.recenterRescaleRealProduct`), the real coordinate becomes `u / L`, and the
comparison cosines in curvature `-ν²` of the rescaled sides are the comparison cosines in
curvature `-(ν / L)²` of the original sides. The anchors are produced here: they are lifts of
`(± s L, y₀)` through the supplied approximation.
-/

set_option autoImplicit false

open Set Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

universe u v

/-- Comparison cosines are invariant under a common rescaling of the sides and the inverse
rescaling of the curvature parameter. -/
theorem hyperbolicComparisonCosine_mul_sides (k c a b d : ℝ) :
    hyperbolicComparisonCosine k (c * a) (c * b) (c * d) =
      hyperbolicComparisonCosine (k * c) a b d := by
  simp only [hyperbolicComparisonCosine, ← mul_assoc]

private theorem scaled_parameter_bounds {L β : ℝ} (hL : 0 < L) (hβ : 0 < β)
    (hsmall : 4 * (L + L⁻¹) * β < 1) :
    3 * L⁻¹ * β ≤ 4 * (L + L⁻¹) * β ∧
      (4 * (L + L⁻¹) * β)⁻¹ / L⁻¹ + 2 * β ≤ β⁻¹ ∧
      β ≤ 4 * (L + L⁻¹) * β * L⁻¹ := by
  have hLi : 0 < L⁻¹ := inv_pos.mpr hL
  have hLL : L * L⁻¹ = 1 := mul_inv_cancel₀ hL.ne'
  have htwo : 2 ≤ L + L⁻¹ := by
    have h : L + L⁻¹ - 2 = (L - 1) ^ 2 / L := by field_simp; ring
    have h' : 0 ≤ (L - 1) ^ 2 / L := div_nonneg (sq_nonneg _) hL.le
    linarith
  refine ⟨by nlinarith [mul_pos hL hβ, mul_pos hLi hβ], ?_, ?_⟩
  · rw [div_inv_eq_mul, inv_mul_eq_div]
    have hβ8 : 8 * β < 1 := by nlinarith
    have hκ : 4 * L * β ≤ 4 * (L + L⁻¹) * β := by nlinarith [mul_pos hLi hβ]
    have hfirst : L / (4 * (L + L⁻¹) * β) ≤ (4 * β)⁻¹ := by
      calc L / (4 * (L + L⁻¹) * β) ≤ L / (4 * L * β) :=
            div_le_div_of_nonneg_left hL.le (by positivity) hκ
        _ = (4 * β)⁻¹ := by field_simp
    have hsecond : 2 * β ≤ (3 / 4) * β⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hβ]
      nlinarith
    have hsplit : (4 * β)⁻¹ + (3 / 4) * β⁻¹ = β⁻¹ := by
      field_simp
      ring
    linarith
  · have h1 : 4 * (L + L⁻¹) * β * L⁻¹ = 4 * β * (L * L⁻¹) + 4 * β * (L⁻¹ * L⁻¹) := by ring
    rw [h1, hLL]
    nlinarith [mul_nonneg hβ.le (mul_pos hLi hLi).le]

/-- **Long product anchors at scale `L`** (metric part of LFR19). For `R ≥ 1` and `ε > 0` there
are `s` and `β₀` such that every normalized `(1, β)`-splitting with `β < β₀` has lifts
`a₊, a₋` of `(± s L, y₀)` satisfying the value estimate on `B(q, R L)` with error `ε L` and the
comparison-cosine estimates, in curvature `-k²` for a `k ≥ β` with `512 (s + R + 1) L < k⁻¹`,
for every tested pair at distance at least `L`. -/
theorem exists_scaled_product_anchor_parameters {L R ε : ℝ} (hL : 0 < L) (hR : 1 ≤ R)
    (hε : 0 < ε) :
    ∃ s > 2 * R + 10, ∃ β₀ > 0, ∀ β : ℝ, 0 < β → β < β₀ →
      ∃ k : ℝ, β ≤ k ∧ 512 * ((s + R + 1) * L) < k⁻¹ ∧
      ∀ (X : Type u) (Y : Type v) [MetricSpace X] [MetricSpace Y] (q : X) (y₀ : Y)
        (F : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ), y₀)) β),
        ∃ aPlus aMinus : X, |dist q aPlus - s * L| < 3 * L ∧ |dist q aMinus - s * L| < 3 * L ∧
        (∀ x ∈ ball q (R * L),
          |(dist q aPlus - dist x aPlus) - (F.toFun x).fst| < ε * L) ∧
        (∀ x ∈ ball q (R * L),
          hyperbolicComparisonCosine k (dist x aPlus) (dist x aMinus) (dist aPlus aMinus)
            < -1 + ε) ∧
        (∀ x ∈ ball q (R * L), ∀ z ∈ ball q (R * L), L ≤ dist x z →
          hyperbolicComparisonCosine k (dist x aPlus) (dist x z) (dist z aPlus)
            < ((F.toFun z).fst - (F.toFun x).fst) / dist x z + ε ∧
          hyperbolicComparisonCosine k (dist x aMinus) (dist x z) (dist z aMinus)
            < -((F.toFun z).fst - (F.toFun x).fst) / dist x z + ε) := by
  obtain ⟨s, hs, ν₀, hν₀, hpar⟩ :=
    exists_uniform_product_anchor_parameters hR hε
  have hLi : 0 < L⁻¹ := inv_pos.mpr hL
  have hκ : 0 < 4 * (L + L⁻¹) := by positivity
  refine ⟨s, hs, min ν₀ 1 / (4 * (L + L⁻¹)), div_pos (lt_min hν₀ one_pos) hκ, ?_⟩
  intro β hβ hβsmall
  set δ : ℝ := 4 * (L + L⁻¹) * β with hδdef
  have hδlt : δ < min ν₀ 1 := by
    rw [hδdef, mul_comm]
    exact (lt_div_iff₀ hκ).mp hβsmall
  have hδν : δ < ν₀ := hδlt.trans_le (min_le_left _ _)
  have hδone : δ < 1 := hδlt.trans_le (min_le_right _ _)
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  obtain ⟨hbudget, hdomain, hβk⟩ := scaled_parameter_bounds hL hβ hδone
  obtain ⟨hbuffer, hmetric⟩ := hpar δ hδpos hδν
  refine ⟨δ * L⁻¹, hβk, ?_, ?_⟩
  · rw [mul_inv, inv_inv]
    have hh := mul_lt_mul_of_pos_right hbuffer hL
    linarith
  intro X Y mX mY q y₀ F
  have hs0 : 0 < s := by linarith
  have hdom : dist q q + δ⁻¹ / L⁻¹ + 2 * β ≤ β⁻¹ := by
    rw [dist_self, zero_add]
    exact hdomain
  let G₀ := F.recenterRescaleRealProduct q hLi hbudget hδone hdom
  have hsnd : WithLp.toLp 2 ((0 : ℝ), (F.toFun q).snd) = WithLp.toLp 2 ((0 : ℝ), y₀) := by
    rw [F.basepoint]
    rfl
  set u : X → ℝ := fun x => (F.toFun x).fst with hu
  have hFq : u q = 0 := by
    change (F.toFun q).fst = 0
    rw [F.basepoint]
    rfl
  let mX' : MetricSpace X := mX.rescale L⁻¹ hLi
  let mY' : MetricSpace Y := mY.rescale L⁻¹ hLi
  let G : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ), y₀)) δ :=
    G₀.mapTargetIsometryAt (IsometryEquiv.refl _) _ hsnd
  have hGfst (x : X) : (G.toFun x).fst = L⁻¹ * (u x - u q) := rfl
  have hdX (a b : X) : dist a b = L⁻¹ * @dist X mX.toDist a b := rfl
  have hcoverPlus : dist (WithLp.toLp 2 (s, y₀)) (WithLp.toLp 2 ((0 : ℝ), y₀)) < δ⁻¹ - δ := by
    rw [WithLp.prod_dist_eq_sqrt_sq_add_sq]
    change Real.sqrt (dist s 0 ^ 2 + dist y₀ y₀ ^ 2) < δ⁻¹ - δ
    rw [dist_self, Real.dist_eq, sub_zero, abs_of_pos hs0, zero_pow two_ne_zero, add_zero,
      Real.sqrt_sq hs0.le]
    linarith
  have hcoverMinus :
      dist (WithLp.toLp 2 (-s, y₀)) (WithLp.toLp 2 ((0 : ℝ), y₀)) < δ⁻¹ - δ := by
    rw [WithLp.prod_dist_eq_sqrt_sq_add_sq]
    change Real.sqrt (dist (-s) 0 ^ 2 + dist y₀ y₀ ^ 2) < δ⁻¹ - δ
    rw [dist_self, Real.dist_eq, sub_zero, abs_neg, abs_of_pos hs0, zero_pow two_ne_zero,
      add_zero, Real.sqrt_sq hs0.le]
    linarith
  obtain ⟨aPlus, haPlus, himagePlus⟩ := G.coverage_witness _ hcoverPlus
  obtain ⟨aMinus, haMinus, himageMinus⟩ := G.coverage_witness _ hcoverMinus
  rw [dist_comm] at himagePlus himageMinus
  have hrPlus := G.supplied_anchor_radius_error aPlus haPlus himagePlus
  have hrMinus := G.supplied_anchor_radius_error aMinus haMinus himageMinus
  rw [abs_of_pos hs0] at hrPlus
  rw [abs_neg, abs_of_pos hs0] at hrMinus
  obtain ⟨-, -, hvalue, hopposite, htested⟩ :=
    hmetric X Y q y₀ G aPlus aMinus haPlus haMinus himagePlus himageMinus
  have hball (x : X) (hx : @dist X mX.toDist x q < R * L) : x ∈ ball q R := by
    change L⁻¹ * @dist X mX.toDist x q < R
    rw [inv_mul_lt_iff₀ hL]
    linarith
  have hrad (a : X) (h : |dist q a - s| < 3 * δ) : |@dist X mX.toDist q a - s * L| < 3 * L := by
    rw [hdX] at h
    have he : @dist X mX.toDist q a - s * L = L * (L⁻¹ * @dist X mX.toDist q a - s) := by
      rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul, mul_comm L s]
    rw [he, abs_mul, abs_of_pos hL]
    have h3 := mul_lt_mul_of_pos_left h hL
    nlinarith
  refine ⟨aPlus, aMinus, hrad aPlus hrPlus, hrad aMinus hrMinus, ?_, ?_, ?_⟩
  · intro x hx
    have h := hvalue x (hball x hx)
    rw [hdX, hdX, hGfst, hFq, sub_zero, ← mul_sub, ← mul_sub, abs_mul, abs_of_pos hLi,
      inv_mul_lt_iff₀ hL] at h
    linarith
  · intro x hx
    have h := hopposite x (hball x hx)
    rwa [hdX, hdX, hdX, hyperbolicComparisonCosine_mul_sides] at h
  · intro x hx z hz hxz
    have hxz' : 1 ≤ dist x z := by
      rw [hdX, le_inv_mul_iff₀ hL]
      linarith
    obtain ⟨hp, hm⟩ := htested x (hball x hx) z (hball z hz) hxz'
    have hratio : ((G.toFun z).fst - (G.toFun x).fst) / dist x z =
        (u z - u x) / @dist X mX.toDist x z := by
      rw [hGfst, hGfst, hdX, hFq, sub_zero, sub_zero, ← mul_sub, mul_div_mul_left _ _ hLi.ne']
    rw [hratio, hdX, hdX, hdX, hyperbolicComparisonCosine_mul_sides] at hp
    rw [neg_div, hratio, ← neg_div, hdX, hdX, hdX, hyperbolicComparisonCosine_mul_sides] at hm
    exact ⟨hp, hm⟩

end GC.MetricGeometry
