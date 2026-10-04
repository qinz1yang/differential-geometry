import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldHypLayout
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldEuclidInjective

/-!
# Injectivity of the hyperbolic compact fold before the core replacement

Lane CF-H3i, tier 3 (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §5, curvature `-1`; the flat model is
`CompactFoldEuclidInjective`). The piecewise map `hypPreFold σ L` is injective on the whole
triangle minus `v₃ = 0` (`injOn_hypPreFold_of` for a layout `L` satisfying the parameter
inequalities of `hypLayout_params` and the lens separation of `norm_gt_of_lensRegion`;
`injOn_hypPreFold` for `hypLayout σ`). The triangle minus `0` splits into four regions, with
`κ = compactProfileSlope`:
* `hypRegionOne = {canon 0 < -e}`: the map is `cornerOne` (the apex germ there is its restriction)
  and `‖E - 3/2‖ = hypInnerRadial (hd 0) < 3/2 - κe`;
* `hypRegionTwo = {canon 1 < -e}`: `cornerTwo`, `‖E + 3/2‖ < 3/2 - κe` (the two regions are
  disjoint since `canon 0 + canon 1 ≥ 0` on the triangle);
* `hypRegionLens = {canon 0, canon 1 ≥ -e, lensCoord < β}`: `bridgeTwo`, `‖E ∓ 3/2‖ ≥ 3/2 - κe`
  and `‖E‖ < 3/2` (the outer germ is excluded by the lens separation);
* `hypRegionThree` (the rest): `cornerThree` (the outer germ is its restriction), `‖E‖ > 13/5` and
  `‖E ∓ 3/2‖ ≥ 3/2 - κe` (inside the outer blend `‖E‖ ≥ 3`, beyond it the angle lies between the
  two bridge angles about `0`).
So the images of the regions are pairwise disjoint. On a corner region the modulus fixes the
pseudo-hyperbolic distance to the vertex (the radial profiles are strictly monotone,
`strictMonoOn_hypInnerRadial`, `strictAntiOn_hypOuterRadial`), and the angle, which lies in
`[0, π]`, is strictly monotone along the hyperbolic circle of that distance inside the closed
sector: the circle is `hypArc v u ϖ φ = mobInv v (u ϖ e^{iφ})` with `hcirc v (hypArc φ) t =
hypArc (φ + t)` (`hcirc_hypArc`), and every validity condition of the angle derivative of
`CompactFoldHypCorners` holds on the open sector arc whether or not it stays in the triangle
(`hypArcOne_valid`, `hypArcTwo_valid`, `hypArcThree_valid`), so two points with the same
distance and the same angle coincide (`hypArc_eq_of_angle`, `eq_of_cornerOne`, …). On the lens
the moduli fix `hd 0` and `hd 1`; in the coordinate `W = rotTwo z` these fix `Re W` (from the
two-circle identity `norm_mob_ofReal_sq`) and `|W|`, and `Im W ≥ 0` fixes the point.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace HypFold

theorem hyp_canonForm_lt_canonForm {τ x y : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (hxy : x < y)
    (hy1 : y < 1) : canonForm τ x < canonForm τ y := by
  have hx : 0 < 1 - x * τ := by nlinarith
  have hy : 0 < 1 - y * τ := by nlinarith
  rw [canonForm, canonForm, div_lt_div_iff₀ hx hy]
  have : 0 < (y - x) * (1 - τ ^ 2) := mul_pos (by linarith) (by nlinarith)
  nlinarith

theorem strictMonoOn_canonForm {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    StrictMonoOn (canonForm τ) (Ico 0 1) :=
  fun _ _ _ hy hxy => hyp_canonForm_lt_canonForm hτ0 hτ1 hxy hy.2

theorem hyp_canonForm_zero (τ : ℝ) : canonForm τ 0 = -τ := by
  simp [canonForm]

theorem hyp_canonForm_neg {τ ϖ : ℝ} (hτ1 : τ < 1) (hϖ0 : 0 ≤ ϖ) (hϖ : ϖ < τ) :
    canonForm τ ϖ < 0 := by
  have hD : 0 < 1 - ϖ * τ := by nlinarith
  rw [canonForm]
  exact div_neg_of_neg_of_pos (by linarith) hD

theorem strictMonoOn_hypInnerRadial {p : ℕ} (hp : 1 ≤ p) {a b τ : ℝ} (hab : a < b)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) : StrictMonoOn (hypInnerRadial p a b τ) (Ico 0 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ico 0 1) (fun x hx => ?_) (fun x hx => ?_)
  · have hD : 1 - x * τ ≠ 0 := by nlinarith [hx.1, hx.2]
    exact (contDiffAt_hypInnerRadial p a b hD).continuousAt.continuousWithinAt
  · rw [interior_Ico] at hx
    obtain ⟨S', hS', hd⟩ := exists_hasDerivAt_hypInnerRadial hp hab hτ0 hτ1 hx.1 hx.2
    rw [hd.deriv]
    exact hS'

theorem strictAntiOn_hypOuterRadial {p : ℕ} (hp : 1 ≤ p) {a b τ : ℝ} (hab : a < b)
    (hb : b ≤ 1 / 5) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    StrictAntiOn (hypOuterRadial p a b τ) (Ico 0 1) := by
  refine strictAntiOn_of_deriv_neg (convex_Ico 0 1) (fun x hx => ?_) (fun x hx => ?_)
  · have hD : 1 - x * τ ≠ 0 := by nlinarith [hx.1, hx.2]
    exact (contDiffAt_hypOuterRadial p a b hD).continuousAt.continuousWithinAt
  · rw [interior_Ico] at hx
    obtain ⟨S', hS', hd⟩ := exists_hasDerivAt_hypOuterRadial hp hab hb hτ0 hτ1 hx.1 hx.2
    rw [hd.deriv]
    exact hS'

theorem hypInnerRadial_zero {p : ℕ} (hp : 1 ≤ p) {a b τ : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    hypInnerRadial p a b τ 0 = 0 := by
  rw [hypInnerRadial, coneStep_eq_zero hab ha, zero_pow (by omega)]
  ring

theorem hypInnerRadial_nonneg {p : ℕ} (hp : 1 ≤ p) {a b τ ϖ : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hϖ0 : 0 ≤ ϖ) (hϖ1 : ϖ < 1) :
    0 ≤ hypInnerRadial p a b τ ϖ := by
  have := (strictMonoOn_hypInnerRadial hp hab hτ0 hτ1).monotoneOn ⟨le_rfl, by norm_num⟩
    ⟨hϖ0, hϖ1⟩ hϖ0
  rwa [hypInnerRadial_zero hp ha hab] at this

theorem hypInnerRadial_of_ge {p : ℕ} {a b τ ϖ : ℝ} (hab : a < b) (hϖ : b ≤ ϖ) :
    hypInnerRadial p a b τ ϖ = 3 / 2 + compactProfileSlope * canonForm τ ϖ := by
  rw [hypInnerRadial, coneStep_eq_one hab hϖ]
  ring

theorem hypOuterRadial_of_ge {p : ℕ} {a b τ ϖ : ℝ} (hab : a < b) (hϖ : b ≤ ϖ) :
    hypOuterRadial p a b τ ϖ = 3 - compactProfileSlope * canonForm τ ϖ := by
  rw [hypOuterRadial, coneStep_eq_one hab hϖ]
  ring

theorem hypInnerRadial_lt_of_canonForm {p : ℕ} (hp : 1 ≤ p) {a b τ e ϖ : ℝ} (hab : a < b)
    (hb1 : b < 1) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hc : canonForm τ b < -e) (hϖ0 : 0 ≤ ϖ)
    (hϖ1 : ϖ < 1) (hϖ : canonForm τ ϖ < -e) :
    hypInnerRadial p a b τ ϖ < 3 / 2 - compactProfileSlope * e := by
  have hκ : (0 : ℝ) < compactProfileSlope := by unfold compactProfileSlope; norm_num
  rcases lt_or_ge ϖ b with h | h
  · have hb0 : 0 ≤ b := by linarith
    have := strictMonoOn_hypInnerRadial hp hab hτ0 hτ1 ⟨hϖ0, hϖ1⟩ ⟨hb0, hb1⟩ h
    rw [hypInnerRadial_of_ge hab le_rfl] at this
    nlinarith
  · rw [hypInnerRadial_of_ge hab h]
    nlinarith

theorem hypOuterRadial_gt {p : ℕ} {a b τ ϖ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (hϖ0 : 0 ≤ ϖ)
    (hϖ1 : ϖ < 1) : 13 / 5 < hypOuterRadial p a b τ ϖ := by
  have hc := abs_lt.1 (abs_canonForm_lt_one hτ0 hτ1 hϖ0 hϖ1)
  have hϖp : ϖ ^ p ≤ 1 := pow_le_one₀ hϖ0 hϖ1.le
  have h0 := coneStep_nonneg a b ϖ
  have h1 := coneStep_le_one a b ϖ
  have hA : 13 / 5 < 7 / 2 - ϖ ^ p / 2 := by linarith
  have hB : 13 / 5 < 3 - compactProfileSlope * canonForm τ ϖ := by
    unfold compactProfileSlope
    linarith [hc.2]
  unfold hypOuterRadial
  nlinarith [mul_nonneg h0
      (by linarith : (0 : ℝ) ≤ 3 - compactProfileSlope * canonForm τ ϖ - 13 / 5),
    mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - coneStep a b ϖ)
      (by linarith : (0 : ℝ) ≤ 7 / 2 - ϖ ^ p / 2 - 13 / 5)]

theorem three_le_hypOuterRadial {p : ℕ} {a b τ ϖ : ℝ} (hτ1 : τ < 1) (hϖ0 : 0 ≤ ϖ)
    (hϖ1 : ϖ < 1) (hϖ : ϖ < τ) : 3 ≤ hypOuterRadial p a b τ ϖ := by
  have hc := hyp_canonForm_neg hτ1 hϖ0 hϖ
  have hϖp : ϖ ^ p ≤ 1 := pow_le_one₀ hϖ0 hϖ1.le
  have h0 := coneStep_nonneg a b ϖ
  have h1 := coneStep_le_one a b ϖ
  have hB : 3 ≤ 3 - compactProfileSlope * canonForm τ ϖ := by
    unfold compactProfileSlope
    linarith
  unfold hypOuterRadial
  nlinarith [mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 3 - compactProfileSlope * canonForm τ ϖ - 3),
    mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - coneStep a b ϖ)
      (by linarith : (0 : ℝ) ≤ 7 / 2 - ϖ ^ p / 2 - 3)]

theorem hyp_convex_angle {s x y : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) (hx : 0 ≤ x ∧ x ≤ Real.pi)
    (hy : 0 ≤ y ∧ y ≤ Real.pi) : 0 ≤ (1 - s) * x + s * y ∧ (1 - s) * x + s * y ≤ Real.pi := by
  constructor <;> nlinarith

theorem hyp_convex_angle' {s x y : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) (hx : 0 ≤ x ∧ x ≤ Real.pi)
    (hy : 0 ≤ y ∧ y ≤ Real.pi) : 0 ≤ s * x + (1 - s) * y ∧ s * x + (1 - s) * y ≤ Real.pi := by
  constructor <;> nlinarith

theorem hyp_three_le_norm_sub_add (u : ℂ) : 3 ≤ ‖u - 3 / 2‖ + ‖u + 3 / 2‖ := by
  have h := norm_sub_le (u + 3 / 2) (u - 3 / 2)
  rw [show u + 3 / 2 - (u - 3 / 2) = ((3 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3)] at h
  linarith

def hypArc (v u : ℂ) (ϖ φ : ℝ) : ℂ := mobInv v (u * ((ϖ : ℂ) * exp ((φ : ℂ) * I)))

section Arc

variable {v u : ℂ} {ϖ : ℝ} (hv : ‖v‖ < 1) (hu : ‖u‖ = 1) (hϖ0 : 0 ≤ ϖ) (hϖ1 : ϖ < 1)
include hv hu hϖ0 hϖ1

omit hv in
theorem norm_hypArc_arg (φ : ℝ) : ‖u * ((ϖ : ℂ) * exp ((φ : ℂ) * I))‖ < 1 := by
  rw [norm_mul, hu, one_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hϖ0]
  exact hϖ1

theorem mob_hypArc (φ : ℝ) : mob v (hypArc v u ϖ φ) = u * ((ϖ : ℂ) * exp ((φ : ℂ) * I)) :=
  mob_mobInv (by have := normSq_lt_one_of_norm_lt hv; linarith)
    (one_add_conj_mul_ne_zero hv (norm_hypArc_arg hu hϖ0 hϖ1 φ))

theorem norm_hypArc_lt_one (φ : ℝ) : ‖hypArc v u ϖ φ‖ < 1 := by
  have h := norm_mob_lt_one (a := -v) (by rwa [norm_neg]) (norm_hypArc_arg hu hϖ0 hϖ1 φ)
  unfold hypArc mobInv
  rw [mob] at h
  simpa [sub_neg_eq_add] using h

theorem hcirc_hypArc (φ t : ℝ) : hcirc v (hypArc v u ϖ φ) t = hypArc v u ϖ (φ + t) := by
  rw [hcirc, mob_hypArc hv hu hϖ0 hϖ1, hypArc]
  congr 1
  rw [mul_assoc, mul_assoc, ← Complex.exp_add]
  push_cast
  ring_nf

theorem continuous_hypArc : Continuous (hypArc v u ϖ) := by
  have hd : ∀ φ : ℝ, 1 + conj v * (u * ((ϖ : ℂ) * exp ((φ : ℂ) * I))) ≠ 0 :=
    fun φ => one_add_conj_mul_ne_zero hv (norm_hypArc_arg hu hϖ0 hϖ1 φ)
  unfold hypArc mobInv
  exact Continuous.div (by fun_prop) (by fun_prop) hd

theorem hypArc_lt {Θ : ℂ → ℝ} {ψ ψ' : ℝ} (hψ : ψ < ψ')
    (hc : ContinuousAt Θ (hypArc v u ϖ ψ)) (hc' : ContinuousAt Θ (hypArc v u ϖ ψ'))
    (hin : ∀ φ ∈ Ioo ψ ψ', ContinuousAt Θ (hypArc v u ϖ φ) ∧
      ∃ D, 0 < D ∧ HasDerivAt (fun t => Θ (hcirc v (hypArc v u ϖ φ) t)) D 0) :
    Θ (hypArc v u ϖ ψ) < Θ (hypArc v u ϖ ψ') := by
  have hγ := continuous_hypArc hv hu hϖ0 hϖ1
  have hmono : StrictMonoOn (fun φ => Θ (hypArc v u ϖ φ)) (Icc ψ ψ') := by
    refine strictMonoOn_of_deriv_pos (convex_Icc ψ ψ') (fun φ hφ => ?_) (fun φ hφ => ?_)
    · have hcφ : ContinuousAt Θ (hypArc v u ϖ φ) := by
        rcases eq_or_lt_of_le hφ.1 with e | e
        · rw [← e]
          exact hc
        rcases eq_or_lt_of_le hφ.2 with e' | e'
        · rw [e']
          exact hc'
        exact (hin φ ⟨e, e'⟩).1
      exact (hcφ.comp hγ.continuousAt).continuousWithinAt
    · rw [interior_Icc] at hφ
      obtain ⟨D, hD, hder⟩ := (hin φ hφ).2
      simp only [hcirc_hypArc hv hu hϖ0 hϖ1] at hder
      rw [(hasDerivAt_of_shift' hder).deriv]
      exact hD
  exact hmono ⟨le_rfl, hψ.le⟩ ⟨hψ.le, le_rfl⟩ hψ

theorem hypArc_eq_of_angle {Θ : ℂ → ℝ} {θ ψ ψ' : ℝ} (h0 : 0 ≤ ψ) (h1 : ψ ≤ θ) (h0' : 0 ≤ ψ')
    (h1' : ψ' ≤ θ) (hc : ContinuousAt Θ (hypArc v u ϖ ψ))
    (hc' : ContinuousAt Θ (hypArc v u ϖ ψ'))
    (hin : ∀ φ, 0 < φ → φ < θ → ContinuousAt Θ (hypArc v u ϖ φ) ∧
      ∃ D, 0 < D ∧ HasDerivAt (fun t => Θ (hcirc v (hypArc v u ϖ φ) t)) D 0)
    (hΘ : Θ (hypArc v u ϖ ψ) = Θ (hypArc v u ϖ ψ')) :
    hypArc v u ϖ ψ = hypArc v u ϖ ψ' := by
  rcases lt_trichotomy ψ ψ' with hlt | heq | hgt
  · have := hypArc_lt hv hu hϖ0 hϖ1 hlt hc hc' fun φ hφ =>
      hin φ (by linarith [hφ.1]) (by linarith [hφ.2])
    linarith
  · rw [heq]
  · have := hypArc_lt hv hu hϖ0 hϖ1 hgt hc' hc fun φ hφ =>
      hin φ (by linarith [hφ.1]) (by linarith [hφ.2])
    linarith

theorem hypArc_eq_of_angle_anti {Θ : ℂ → ℝ} {θ ψ ψ' : ℝ} (h0 : 0 ≤ ψ) (h1 : ψ ≤ θ)
    (h0' : 0 ≤ ψ') (h1' : ψ' ≤ θ) (hc : ContinuousAt Θ (hypArc v u ϖ ψ))
    (hc' : ContinuousAt Θ (hypArc v u ϖ ψ'))
    (hin : ∀ φ, 0 < φ → φ < θ → ContinuousAt Θ (hypArc v u ϖ φ) ∧
      ∃ D, D < 0 ∧ HasDerivAt (fun t => Θ (hcirc v (hypArc v u ϖ φ) t)) D 0)
    (hΘ : Θ (hypArc v u ϖ ψ) = Θ (hypArc v u ϖ ψ')) :
    hypArc v u ϖ ψ = hypArc v u ϖ ψ' := by
  refine hypArc_eq_of_angle (Θ := fun z => -Θ z) hv hu hϖ0 hϖ1 h0 h1 h0' h1' hc.neg hc'.neg
    (fun φ hφ0 hφ1 => ?_) (by simp only [hΘ])
  obtain ⟨hcφ, D, hD, hder⟩ := hin φ hφ0 hφ1
  exact ⟨hcφ.neg, -D, by linarith, hder.neg⟩

end Arc

theorem eq_hypArc {v u z R : ℂ} (hv : ‖v‖ < 1) (hz : ‖z‖ < 1) (hR : mob v z = u * R)
    (hpos : 0 < ‖R‖ + R.re) : z = hypArc v u ‖R‖ (discAngle R) := by
  have hR0 : R ≠ 0 := by
    rintro rfl
    simp at hpos
  rw [hypArc, ← halfArg_polar_self hR0 hpos, ← hR,
    mobInv_mob (by have := normSq_lt_one_of_norm_lt hv; linarith)
      (one_sub_conj_mul_ne_zero hv hz)]

variable (σ : CompactShape)

def hypRegionOne (L : HypLayout) : Set ℂ :=
  {z | z ∈ σ.triangle ∧ z ≠ 0 ∧ canon σ 0 z < -L.e}

def hypRegionTwo (L : HypLayout) : Set ℂ :=
  {z | z ∈ σ.triangle ∧ z ≠ 0 ∧ canon σ 1 z < -L.e}

def hypRegionLens (L : HypLayout) : Set ℂ :=
  {z | z ∈ σ.triangle ∧ z ≠ 0 ∧ -L.e ≤ canon σ 0 z ∧ -L.e ≤ canon σ 1 z ∧ lensCoord σ z < L.β}

def hypRegionThree (L : HypLayout) : Set ℂ :=
  {z | z ∈ σ.triangle ∧ z ≠ 0 ∧ -L.e ≤ canon σ 0 z ∧ -L.e ≤ canon σ 1 z ∧ L.β ≤ lensCoord σ z}

variable {σ}

theorem mem_hypRegions {L : HypLayout} {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) :
    z ∈ hypRegionOne σ L ∨ z ∈ hypRegionTwo σ L ∨ z ∈ hypRegionLens σ L ∨
      z ∈ hypRegionThree σ L := by
  by_cases c1 : canon σ 0 z < -L.e
  · exact Or.inl ⟨hz, h0, c1⟩
  by_cases c2 : canon σ 1 z < -L.e
  · exact Or.inr (Or.inl ⟨hz, h0, c2⟩)
  rw [not_lt] at c1 c2
  by_cases l : lensCoord σ z < L.β
  · exact Or.inr (Or.inr (Or.inl ⟨hz, h0, c1, c2, l⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hz, h0, c1, c2, not_lt.1 l⟩))

theorem hyp_im_bridgeOne_nonneg {z : ℂ} (hz : 0 ≤ σ.wallSide 1 z) :
    0 ≤ (bridgeOne σ z).im :=
  im_twoCircle_nonneg hz

theorem hyp_im_bridgeZero_nonneg {z : ℂ} (hz : 0 ≤ σ.wallSide 0 z) :
    0 ≤ (bridgeZero σ z).im :=
  im_twoCircle_nonneg hz

theorem hyp_im_bridgeTwo_nonneg {z : ℂ} (hz : 0 ≤ (σ.rotTwo z).im) :
    0 ≤ (bridgeTwo σ z).im :=
  im_twoCircle_nonneg hz

section Hyp

variable (h : σ.curv = .hyperbolic)
include h

theorem rotOne_hypArc {ϖ φ : ℝ} (hϖ0 : 0 ≤ ϖ) (hϖ1 : ϖ < 1) :
    σ.rotOne (hypArc σ.vertexOne (-exp ((σ.θ₃ : ℂ) * I)) ϖ φ) =
      (ϖ : ℂ) * exp ((φ : ℂ) * I) := by
  rw [rotOne_eq_mul_mob h, mob_hypArc (norm_vertexOne_lt_one h) (norm_neg_exp σ.θ₃) hϖ0 hϖ1]
  linear_combination ((ϖ : ℂ) * exp ((φ : ℂ) * I)) * exp_mul_exp_neg σ.θ₃

theorem rotTwo_hypArc {ϖ φ : ℝ} (hϖ0 : 0 ≤ ϖ) (hϖ1 : ϖ < 1) :
    σ.rotTwo (hypArc σ.vertexTwo (-exp (-((σ.θ₂ : ℂ) * I))) ϖ φ) =
      (ϖ : ℂ) * exp ((φ : ℂ) * I) := by
  rw [rotTwo_eq_mul_mob h, mob_hypArc (norm_vertexTwo_lt_one h) (norm_neg_exp_neg σ.θ₂) hϖ0 hϖ1]
  linear_combination ((ϖ : ℂ) * exp ((φ : ℂ) * I)) * exp_mul_exp_neg σ.θ₂

omit h in
theorem hypArc_zero_one {r φ : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    hypArc 0 1 r φ = (r : ℂ) * exp ((φ : ℂ) * I) := by
  have := mob_hypArc (v := 0) (u := 1) (φ := φ) (by simp) norm_one hr0 hr1
  rwa [mob_zero_left, one_mul] at this

omit h in
theorem hyp_im_polar_rot (r θ φ : ℝ) :
    (exp (-((θ : ℂ) * I)) * ((r : ℂ) * exp ((φ : ℂ) * I))).im = r * Real.sin (φ - θ) := by
  rw [show exp (-((θ : ℂ) * I)) * ((r : ℂ) * exp ((φ : ℂ) * I)) =
      (r : ℂ) * exp (((φ - θ : ℝ) : ℂ) * I) by
    rw [mul_left_comm, ← Complex.exp_add]; push_cast; ring_nf,
    im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

omit h in
theorem hyp_im_polar (r φ : ℝ) : ((r : ℂ) * exp ((φ : ℂ) * I)).im = r * Real.sin φ := by
  rw [im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

omit h in
theorem hyp_polar_im_pos {r φ θ : ℝ} (hr : 0 < r) (hφ0 : 0 < φ) (hφ1 : φ < θ)
    (hθ : θ ≤ Real.pi / 2) :
    0 < ((r : ℂ) * exp ((φ : ℂ) * I)).im ∧
      (exp (-((θ : ℂ) * I)) * ((r : ℂ) * exp ((φ : ℂ) * I))).im < 0 := by
  have hpi := Real.pi_pos
  rw [hyp_im_polar, hyp_im_polar_rot]
  exact ⟨mul_pos hr (Real.sin_pos_of_pos_of_lt_pi hφ0 (by linarith)),
    mul_neg_of_pos_of_neg hr (Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith))⟩

theorem hypArcOne_valid {a b β β' : ℝ} (hβ : β < β') {ϖ φ : ℝ} (hϖ0 : 0 < ϖ) (hϖ1 : ϖ < 1)
    (hφ0 : 0 < φ) (hφ1 : φ < σ.θ₁) :
    ContinuousAt (angleCornerOne σ a b β β')
        (hypArc σ.vertexOne (-exp ((σ.θ₃ : ℂ) * I)) ϖ φ) ∧
      ∃ D, 0 < D ∧ HasDerivAt (fun t => angleCornerOne σ a b β β'
        (hcirc σ.vertexOne (hypArc σ.vertexOne (-exp ((σ.θ₃ : ℂ) * I)) ϖ φ) t)) D 0 := by
  set y := hypArc σ.vertexOne (-exp ((σ.θ₃ : ℂ) * I)) ϖ φ with hy
  have hy1 : ‖y‖ < 1 :=
    norm_hypArc_lt_one (norm_vertexOne_lt_one h) (norm_neg_exp σ.θ₃) hϖ0.le hϖ1 φ
  have hr := rotOne_hypArc h (φ := φ) hϖ0.le hϖ1
  rw [← hy] at hr
  obtain ⟨hs1, hs2⟩ := hyp_polar_im_pos hϖ0 hφ0 hφ1 (θ₁_le σ)
  rw [← hr] at hs1 hs2
  have t13 := sideOneThree_pos h
  have t13' := sideOneThree_lt_one h
  have t12 := sideOneTwo_pos h
  have t12' := sideOneTwo_lt_one h
  have hw1 : 0 < σ.wallSide 1 y := by
    have e := rotOne_im_mul_normSq h hy1
    have hN := normSq_pos.2 (one_sub_conj_mul_ne_zero (norm_vertexOne_lt_one h) hy1)
    have : 0 < (1 - sideOneThree σ ^ 2) * σ.wallSide 1 y := by rw [← e]; positivity
    exact pos_of_mul_pos_right this (by nlinarith)
  have hs3 : 0 < (σ.rotTwo y).im := by
    have e := rotOne_rot_im_mul_normSq h hy1
    have hN := normSq_pos.2 (one_sub_sideOneTwo_mul_rotTwo_ne_zero h hy1)
    have : 0 < (1 - sideOneTwo σ ^ 2) * (σ.rotTwo y).im := by nlinarith
    exact pos_of_mul_pos_right this (by nlinarith)
  have hne : (exp (-((σ.θ₃ : ℂ) * I)) * y).im ≠ 0 := by
    have := wallSide_one_eq_neg_im (σ := σ) y
    intro h'
    linarith
  have d13 : y ∈ domOneThree σ := mem_pairDom t13 t13' (by rw [norm_exp_neg_mul]; exact hy1)
    (Or.inl hne) (Or.inl hne)
  have d12 : y ∈ domOneTwo σ := ⟨hy1, mem_pairDom t12 t12' (norm_rotTwo_lt_one h hy1)
    (Or.inl hs3.ne') (Or.inl hs3.ne')⟩
  have hψ := norm_add_re_pos (Or.inl hs1.ne')
  have hψ' := norm_add_re_pos (Or.inl hs2.ne)
  have hpos1 := hpos_one_at_one h hy1
  have hpos2 := hpos_two_at_one h d12
  have hord := angleOneAtOne_le_angleTwoAtOne h d13 d12 hpos1 hpos2 hw1.le hs3.le
  exact ⟨(contDiffAt_angleCornerOne h a b β β' d13 d12 hψ hpos1 hpos2).continuousAt,
    exists_hasDerivAt_angleCornerOne h hβ d13 d12 hψ hψ' hpos1 hpos2 hord
      (Or.inl (re_rot_nonneg (θ₁_pos σ) (θ₁_le σ) hs1.le hs2.le))⟩

theorem hypArcTwo_valid {a b β β' : ℝ} (hβ : β < β') {ϖ φ : ℝ} (hϖ0 : 0 < ϖ) (hϖ1 : ϖ < 1)
    (hφ0 : 0 < φ) (hφ1 : φ < σ.θ₂) :
    ContinuousAt (angleCornerTwo σ a b β β')
        (hypArc σ.vertexTwo (-exp (-((σ.θ₂ : ℂ) * I))) ϖ φ) ∧
      ∃ D, 0 < D ∧ HasDerivAt (fun t => angleCornerTwo σ a b β β'
        (hcirc σ.vertexTwo (hypArc σ.vertexTwo (-exp (-((σ.θ₂ : ℂ) * I))) ϖ φ) t)) D 0 := by
  set y := hypArc σ.vertexTwo (-exp (-((σ.θ₂ : ℂ) * I))) ϖ φ with hy
  have hy1 : ‖y‖ < 1 :=
    norm_hypArc_lt_one (norm_vertexTwo_lt_one h) (norm_neg_exp_neg σ.θ₂) hϖ0.le hϖ1 φ
  have hr := rotTwo_hypArc h (φ := φ) hϖ0.le hϖ1
  rw [← hy] at hr
  obtain ⟨hs1, hs2⟩ := hyp_polar_im_pos hϖ0 hφ0 hφ1 (θ₂_le σ)
  rw [← hr] at hs1 hs2
  have t23 := sideTwoThree_pos h
  have t23' := sideTwoThree_lt_one h
  have t12 := sideOneTwo_pos h
  have t12' := sideOneTwo_lt_one h
  have hw0 : 0 < σ.wallSide 0 y := by
    have e := rotTwo_rot_im_mul_normSq h y
    have hN := normSq_pos.2 (one_sub_vertexTwo_mul_ne_zero h hy1)
    have : 0 < (1 - sideTwoThree σ ^ 2) * σ.wallSide 0 y := by nlinarith
    exact pos_of_mul_pos_right this (by nlinarith)
  have hw0' : 0 < y.im := hw0
  have d12 : y ∈ domOneTwo σ := ⟨hy1, mem_pairDom t12 t12' (norm_rotTwo_lt_one h hy1)
    (Or.inl hs1.ne') (Or.inl hs1.ne')⟩
  have d03 : y ∈ domZeroThree σ := mem_pairDom t23 t23' hy1 (Or.inl hw0'.ne') (Or.inl hw0'.ne')
  have hψ' := norm_add_re_pos (Or.inl hs2.ne)
  have hpos2 := hpos_two_at_two h d12
  have hpos0 := hpos_zero_at_two h hy1
  have hord := angleTwoAtTwo_le_angleZeroAtTwo h d12 d03 hpos2 hpos0 hs1.le hw0.le
  exact ⟨(contDiffAt_angleCornerTwo h a b β β' d12 d03 hpos2 hpos0).continuousAt,
    exists_hasDerivAt_angleCornerTwo h hβ d12 d03 hψ' hpos2 hpos0 hord
      (Or.inl (re_nonneg_of_sector (θ₂_pos σ) (θ₂_le σ) hs1.le hs2.le))⟩

theorem hypArcThree_valid {a b w δ : ℝ} (hw : 0 < w) (hδ : 0 < δ) {r φ : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) (hφ0 : 0 < φ) (hφ1 : φ < σ.θ₃) :
    ContinuousAt (angleCornerThree σ a b w δ) (hypArc 0 1 r φ) ∧
      ∃ D, D < 0 ∧ HasDerivAt (fun t => angleCornerThree σ a b w δ
        (hcirc 0 (hypArc 0 1 r φ) t)) D 0 := by
  rw [hypArc_zero_one hr0.le hr1]
  set y := (r : ℂ) * exp ((φ : ℂ) * I) with hy
  have hy1 : ‖y‖ < 1 := by
    rw [hy, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr0]
    exact hr1
  obtain ⟨hs1, hs2⟩ := hyp_polar_im_pos hr0 hφ0 hφ1 (θ₃_le σ)
  rw [← hy] at hs1 hs2
  have hw1 : 0 < σ.wallSide 1 y := by
    rw [wallSide_one_eq_neg_im]
    linarith
  have hw0 : 0 < σ.wallSide 0 y := hs1
  have d13 : y ∈ domOneThree σ := mem_pairDom (sideOneThree_pos h) (sideOneThree_lt_one h)
    (by rw [norm_exp_neg_mul]; exact hy1) (Or.inl hs2.ne) (Or.inl hs2.ne)
  have d03 : y ∈ domZeroThree σ := mem_pairDom (sideTwoThree_pos h) (sideTwoThree_lt_one h) hy1
    (Or.inl hs1.ne') (Or.inl hs1.ne')
  have hψ := norm_add_re_pos (Or.inl hs1.ne')
  have hpos1 := hpos_one_at_three h hy1
  have hpos0 := hpos_zero_at_three h hy1
  have hord := angleOneAtThree_le_angleZeroAtThree h d13 d03 hpos1 hpos0 hw1.le hw0.le
  exact ⟨(contDiffAt_angleCornerThree h a b w δ d13 d03 hψ hpos1 hpos0).continuousAt,
    exists_hasDerivAt_angleCornerThree h hw hδ d13 d03 hψ hpos1 hpos0 hord
      (Or.inl ⟨hw0.le, hw1.le⟩)⟩

theorem contAt_angleCornerOne_of_mem (a b β β' : ℝ) {z : ℂ} (hz : z ∈ σ.triangle)
    (h0 : z ≠ 0) (h1 : z ≠ σ.vertexOne) (h2 : z ≠ σ.vertexTwo) :
    ContinuousAt (angleCornerOne σ a b β β') z := by
  have d12 := mem_domOneTwo h hz h1 h2
  exact (contDiffAt_angleCornerOne h a b β β' (mem_domOneThree h hz h0 h1) d12
    (valid_one h hz h1).1 (hpos_one_at_one h (norm_lt_one_of_mem h hz))
    (hpos_two_at_one h d12)).continuousAt

theorem contAt_angleCornerTwo_of_mem (a b β β' : ℝ) {z : ℂ} (hz : z ∈ σ.triangle)
    (h0 : z ≠ 0) (h1 : z ≠ σ.vertexOne) (h2 : z ≠ σ.vertexTwo) :
    ContinuousAt (angleCornerTwo σ a b β β') z := by
  have d12 := mem_domOneTwo h hz h1 h2
  exact (contDiffAt_angleCornerTwo h a b β β' d12 (mem_domZeroThree h hz h0 h2)
    (hpos_two_at_two h d12) (hpos_zero_at_two h (norm_lt_one_of_mem h hz))).continuousAt

theorem contAt_angleCornerThree_of_mem (a b w δ : ℝ) {z : ℂ} (hz : z ∈ σ.triangle)
    (h0 : z ≠ 0) (h1 : z ≠ σ.vertexOne) (h2 : z ≠ σ.vertexTwo) :
    ContinuousAt (angleCornerThree σ a b w δ) z := by
  have hz1 := norm_lt_one_of_mem h hz
  exact (contDiffAt_angleCornerThree h a b w δ (mem_domOneThree h hz h0 h1)
    (mem_domZeroThree h hz h0 h2) (valid_three hz h0) (hpos_one_at_three h hz1)
    (hpos_zero_at_three h hz1)).continuousAt

theorem angleCornerOne_mem_of_mem (a b β β' : ℝ) {z : ℂ} (hz : z ∈ σ.triangle)
    (h1 : z ≠ σ.vertexOne) (h2 : z ≠ σ.vertexTwo) :
    0 ≤ angleCornerOne σ a b β β' z ∧ angleCornerOne σ a b β β' z ≤ Real.pi := by
  have d12 := mem_domOneTwo h hz h1 h2
  have a1 := halfArg_mem_Ico' (hpos_one_at_one h (norm_lt_one_of_mem h hz))
    (hyp_im_bridgeOne_nonneg (hz.2 1))
  have a2 := negHalfArg_mem_Ioc' (hpos_two_at_one h d12)
    (hyp_im_bridgeTwo_nonneg (sector_two h hz).1)
  have hs := sector_one h hz
  have hψ := discAngle_mem_sector (θ₁_pos σ) (θ₁_le σ)
    (rotOne_ne_zero h (norm_lt_one_of_mem h hz) h1) hs.1 hs.2
  have hp : (0 : ℝ) ≤ σ.p₁ := Nat.cast_nonneg _
  have hpψ : (σ.p₁ : ℝ) * psiOne σ z ≤ Real.pi := by
    rw [← θ₁_mul σ, mul_comm σ.θ₁]
    exact mul_le_mul_of_nonneg_left hψ.2 hp
  exact hyp_convex_angle (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _)
    ⟨mul_nonneg hp hψ.1, hpψ⟩ (hyp_convex_angle' (coneStep_nonneg _ _ _)
      (coneStep_le_one _ _ _) ⟨a1.1, a1.2.le⟩ ⟨a2.1.le, a2.2⟩)

theorem angleCornerTwo_mem_of_mem (a b β β' : ℝ) {z : ℂ} (hz : z ∈ σ.triangle)
    (h1 : z ≠ σ.vertexOne) (h2 : z ≠ σ.vertexTwo) :
    0 ≤ angleCornerTwo σ a b β β' z ∧ angleCornerTwo σ a b β β' z ≤ Real.pi := by
  have d12 := mem_domOneTwo h hz h1 h2
  have a2 := halfArg_mem_Ico' (hpos_two_at_two h d12) (hyp_im_bridgeTwo_nonneg (sector_two h hz).1)
  have a0 := negHalfArg_mem_Ioc' (hpos_zero_at_two h (norm_lt_one_of_mem h hz))
    (hyp_im_bridgeZero_nonneg (hz.2 0))
  have hs := sector_two h hz
  have hψ := discAngle_mem_sector (θ₂_pos σ) (θ₂_le σ)
    (fun e => h2 (rotTwo_injOn h (norm_lt_one_of_mem h hz) (norm_vertexTwo_lt_one h)
      (by rw [e, rotTwo_vertexTwo h]))) hs.1 hs.2
  have hp : (0 : ℝ) ≤ σ.p₂ := Nat.cast_nonneg _
  have hpψ : (σ.p₂ : ℝ) * psiTwo σ z ≤ Real.pi := by
    rw [← θ₂_mul σ, mul_comm σ.θ₂]
    exact mul_le_mul_of_nonneg_left hψ.2 hp
  exact hyp_convex_angle (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _)
    ⟨mul_nonneg hp hψ.1, hpψ⟩ (hyp_convex_angle (coneStep_nonneg _ _ _)
      (coneStep_le_one _ _ _) ⟨a2.1, a2.2.le⟩ ⟨a0.1.le, a0.2⟩)

theorem angleCornerThree_mem_of_mem (a b w δ : ℝ) {z : ℂ} (hz : z ∈ σ.triangle)
    (h0 : z ≠ 0) :
    0 ≤ angleCornerThree σ a b w δ z ∧ angleCornerThree σ a b w δ z ≤ Real.pi := by
  have hz1 := norm_lt_one_of_mem h hz
  have a1 := halfArg_mem_Ico' (hpos_one_at_three h hz1) (hyp_im_bridgeOne_nonneg (hz.2 1))
  have a0 := negHalfArg_mem_Ioc' (hpos_zero_at_three h hz1) (hyp_im_bridgeZero_nonneg (hz.2 0))
  have hψ := discAngle_mem hz h0
  have hp : (0 : ℝ) ≤ σ.p₃ := Nat.cast_nonneg _
  have hpψ : (σ.p₃ : ℝ) * discAngle z ≤ Real.pi := by
    rw [← θ₃_mul σ, mul_comm σ.θ₃]
    exact mul_le_mul_of_nonneg_left hψ.2 hp
  exact hyp_convex_angle (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _)
    ⟨by linarith, by nlinarith [mul_nonneg hp hψ.1]⟩ (hyp_convex_angle (coneStep_nonneg _ _ _)
      (coneStep_le_one _ _ _) ⟨a0.1.le, a0.2⟩ ⟨a1.1, a1.2.le⟩)

omit h in
theorem hd_zero_vertexOne' : hd σ 0 σ.vertexOne = 0 := by
  change ‖mob σ.vertexOne σ.vertexOne‖ = 0
  rw [mob_self, norm_zero]

omit h in
theorem hd_one_vertexTwo' : hd σ 1 σ.vertexTwo = 0 := by
  change ‖mob σ.vertexTwo σ.vertexTwo‖ = 0
  rw [mob_self, norm_zero]

theorem eq_vertexOne_of_hd {z : ℂ} (hz : ‖z‖ < 1) (h0 : hd σ 0 z = 0) : z = σ.vertexOne := by
  by_contra hne
  exact rotOne_ne_zero h hz hne (norm_eq_zero.1 (by rw [norm_rotOne_eq_hd h]; exact h0))

theorem rotTwo_ne_zero_of_ne {z : ℂ} (hz : ‖z‖ < 1) (h2 : z ≠ σ.vertexTwo) : σ.rotTwo z ≠ 0 :=
  fun e => h2 (rotTwo_injOn h hz (norm_vertexTwo_lt_one h) (by rw [e, rotTwo_vertexTwo h]))

theorem eq_vertexTwo_of_hd {z : ℂ} (hz : ‖z‖ < 1) (h0 : hd σ 1 z = 0) : z = σ.vertexTwo := by
  by_contra hne
  exact rotTwo_ne_zero_of_ne h hz hne (norm_eq_zero.1 (by rw [norm_rotTwo_eq_hd h]; exact h0))

theorem lensCoord_nonneg_of_mem {z : ℂ} (hz : z ∈ σ.triangle) : 0 ≤ lensCoord σ z :=
  div_nonneg (by linarith [(sector_two h hz).1])
    (by linarith [normSq_rotTwo_lt_one h (norm_lt_one_of_mem h hz)])

theorem eq_of_cornerOne {a b β β' : ℝ} (hβ : β < β') {z w : ℂ} (hz : z ∈ σ.triangle)
    (hz0 : z ≠ 0) (hz1 : z ≠ σ.vertexOne) (hz2 : z ≠ σ.vertexTwo) (hw : w ∈ σ.triangle)
    (hw0 : w ≠ 0) (hw1 : w ≠ σ.vertexOne) (hw2 : w ≠ σ.vertexTwo)
    (hϖ : hd σ 0 w = hd σ 0 z)
    (hΘ : angleCornerOne σ a b β β' z = angleCornerOne σ a b β β' w) : z = w := by
  have hv := norm_vertexOne_lt_one h
  have hu := norm_neg_exp σ.θ₃
  have hzn := norm_lt_one_of_mem h hz
  have hwn := norm_lt_one_of_mem h hw
  have hR : ∀ x : ℂ, mob σ.vertexOne x = -exp ((σ.θ₃ : ℂ) * I) * σ.rotOne x := fun x => by
    rw [rotOne_eq_mul_mob h]
    linear_combination (-(mob σ.vertexOne x)) * exp_mul_exp_neg σ.θ₃
  have pz := eq_hypArc hv hzn (hR z) (valid_one h hz hz1).1
  have pw := eq_hypArc hv hwn (hR w) (valid_one h hw hw1).1
  rw [norm_rotOne_eq_hd h] at pz pw
  rw [hϖ] at pw
  have hϖ0 : 0 < hd σ 0 z := by
    rw [← norm_rotOne_eq_hd h]
    exact norm_pos_iff.2 (rotOne_ne_zero h hzn hz1)
  have hϖ1 := hd_lt_one h 0 hzn
  have sz := sector_one h hz
  have sw := sector_one h hw
  have ψz := discAngle_mem_sector (θ₁_pos σ) (θ₁_le σ) (rotOne_ne_zero h hzn hz1) sz.1 sz.2
  have ψw := discAngle_mem_sector (θ₁_pos σ) (θ₁_le σ) (rotOne_ne_zero h hwn hw1) sw.1 sw.2
  have hc := contAt_angleCornerOne_of_mem h a b β β' hz hz0 hz1 hz2
  have hc' := contAt_angleCornerOne_of_mem h a b β β' hw hw0 hw1 hw2
  have key := hypArc_eq_of_angle (Θ := angleCornerOne σ a b β β') hv hu hϖ0.le hϖ1 ψz.1 ψz.2
    ψw.1 ψw.2 (by rw [← pz]; exact hc) (by rw [← pw]; exact hc')
    (fun φ h0 h1 => hypArcOne_valid h hβ hϖ0 hϖ1 h0 h1) (by rw [← pz, ← pw]; exact hΘ)
  rw [← pz, ← pw] at key
  exact key

theorem eq_of_cornerTwo {a b β β' : ℝ} (hβ : β < β') {z w : ℂ} (hz : z ∈ σ.triangle)
    (hz0 : z ≠ 0) (hz1 : z ≠ σ.vertexOne) (hz2 : z ≠ σ.vertexTwo) (hw : w ∈ σ.triangle)
    (hw0 : w ≠ 0) (hw1 : w ≠ σ.vertexOne) (hw2 : w ≠ σ.vertexTwo)
    (hϖ : hd σ 1 w = hd σ 1 z)
    (hΘ : angleCornerTwo σ a b β β' z = angleCornerTwo σ a b β β' w) : z = w := by
  have hv := norm_vertexTwo_lt_one h
  have hu := norm_neg_exp_neg σ.θ₂
  have hzn := norm_lt_one_of_mem h hz
  have hwn := norm_lt_one_of_mem h hw
  have hR : ∀ x : ℂ, mob σ.vertexTwo x = -exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo x := fun x => by
    rw [rotTwo_eq_mul_mob h]
    linear_combination (-(mob σ.vertexTwo x)) * exp_mul_exp_neg σ.θ₂
  have pz := eq_hypArc hv hzn (hR z) (valid_two h hz hz2).1
  have pw := eq_hypArc hv hwn (hR w) (valid_two h hw hw2).1
  rw [norm_rotTwo_eq_hd h] at pz pw
  rw [hϖ] at pw
  have hϖ0 : 0 < hd σ 1 z := by
    rw [← norm_rotTwo_eq_hd h]
    exact norm_pos_iff.2 (rotTwo_ne_zero_of_ne h hzn hz2)
  have hϖ1 := hd_lt_one h 1 hzn
  have sz := sector_two h hz
  have sw := sector_two h hw
  have ψz := discAngle_mem_sector (θ₂_pos σ) (θ₂_le σ) (rotTwo_ne_zero_of_ne h hzn hz2) sz.1 sz.2
  have ψw := discAngle_mem_sector (θ₂_pos σ) (θ₂_le σ) (rotTwo_ne_zero_of_ne h hwn hw2) sw.1 sw.2
  have hc := contAt_angleCornerTwo_of_mem h a b β β' hz hz0 hz1 hz2
  have hc' := contAt_angleCornerTwo_of_mem h a b β β' hw hw0 hw1 hw2
  have key := hypArc_eq_of_angle (Θ := angleCornerTwo σ a b β β') hv hu hϖ0.le hϖ1 ψz.1 ψz.2
    ψw.1 ψw.2 (by rw [← pz]; exact hc) (by rw [← pw]; exact hc')
    (fun φ h0 h1 => hypArcTwo_valid h hβ hϖ0 hϖ1 h0 h1) (by rw [← pz, ← pw]; exact hΘ)
  rw [← pz, ← pw] at key
  exact key

theorem eq_of_cornerThree {a b w δ : ℝ} (hw : 0 < w) (hδ : 0 < δ) {z z' : ℂ}
    (hz : z ∈ σ.triangle) (hz0 : z ≠ 0) (hz1 : z ≠ σ.vertexOne) (hz2 : z ≠ σ.vertexTwo)
    (hz' : z' ∈ σ.triangle) (hz0' : z' ≠ 0) (hz1' : z' ≠ σ.vertexOne)
    (hz2' : z' ≠ σ.vertexTwo) (hr : ‖z'‖ = ‖z‖)
    (hΘ : angleCornerThree σ a b w δ z = angleCornerThree σ a b w δ z') : z = z' := by
  have hv : ‖(0 : ℂ)‖ < 1 := by simp
  have hzn := norm_lt_one_of_mem h hz
  have hR : ∀ x : ℂ, mob 0 x = 1 * x := fun x => by rw [mob_zero_left, one_mul]
  have pz := eq_hypArc hv hzn (hR z) (valid_three hz hz0)
  have pw := eq_hypArc hv (norm_lt_one_of_mem h hz') (hR z') (valid_three hz' hz0')
  rw [hr] at pw
  have ψz := discAngle_mem hz hz0
  have ψw := discAngle_mem hz' hz0'
  have hc := contAt_angleCornerThree_of_mem h a b w δ hz hz0 hz1 hz2
  have hc' := contAt_angleCornerThree_of_mem h a b w δ hz' hz0' hz1' hz2'
  have key := hypArc_eq_of_angle_anti (Θ := angleCornerThree σ a b w δ) hv norm_one
    (norm_nonneg z) hzn ψz.1 ψz.2 ψw.1 ψw.2 (by rw [← pz]; exact hc) (by rw [← pw]; exact hc')
    (fun φ h0 h1 => hypArcThree_valid h hw hδ (norm_pos_iff.2 hz0) hzn h0 h1)
    (by rw [← pz, ← pw]; exact hΘ)
  rw [← pz, ← pw] at key
  exact key

section Layout

variable {L : HypLayout}
  (hp : 0 < L.g ∧ L.g < L.a ∧ L.a < L.b ∧ L.b < 1 ∧ 0 < L.e ∧
    canonForm (tauOne σ) L.b < -L.e ∧ canonForm (tauTwo σ) L.b < -L.e ∧ 0 < L.β ∧
    L.β < L.β' ∧ L.β' < L.a * Real.sin σ.θ₁ ∧ L.β' < L.a * Real.sin σ.θ₂ ∧ 0 < L.g₃ ∧
    L.g₃ < L.a₃ ∧ L.a₃ < L.b₃ ∧ L.b₃ < tauThree σ ∧ L.b₃ ≤ 1 / 5)
include hp

theorem hyp_e_lt : L.e < tauOne σ ∧ L.e < tauTwo σ := by
  obtain ⟨hg0, hga, hab, hb1, -, hc1, hc2, -⟩ := id hp
  have e1 := hyp_canonForm_lt_canonForm (tauOne_pos h) (tauOne_lt_one (σ := σ)) (x := 0)
    (by linarith) hb1
  have e2 := hyp_canonForm_lt_canonForm (tauTwo_pos h) (tauTwo_lt_one (σ := σ)) (x := 0)
    (by linarith) hb1
  rw [hyp_canonForm_zero] at e1 e2
  constructor <;> linarith

theorem canon_zero_lt_of_hd {z : ℂ} (hlt : hd σ 0 z < L.g) : canon σ 0 z < -L.e := by
  obtain ⟨hg0, hga, hab, hb1, -, hc1, -⟩ := id hp
  rw [canon_zero_eq]
  have := hyp_canonForm_lt_canonForm (tauOne_pos h) (tauOne_lt_one (σ := σ))
    (by linarith : hd σ 0 z < L.b) hb1
  linarith

theorem canon_one_lt_of_hd {z : ℂ} (hlt : hd σ 1 z < L.g) : canon σ 1 z < -L.e := by
  obtain ⟨hg0, hga, hab, hb1, -, -, hc2, -⟩ := id hp
  rw [canon_one_eq]
  have := hyp_canonForm_lt_canonForm (tauTwo_pos h) (tauTwo_lt_one (σ := σ))
    (by linarith : hd σ 1 z < L.b) hb1
  linarith

omit h in
theorem canon_two_neg_of_norm {z : ℂ} (hlt : ‖z‖ < L.g₃) : canon σ 2 z < 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hga₃, hab₃, hb₃, -⟩ := id hp
  rw [canon_two_eq]
  exact hyp_canonForm_neg (tauThree_lt_one (σ := σ)) (norm_nonneg z) (by linarith)

theorem ne_vertexOne_of_canon {z : ℂ} (hc : -L.e ≤ canon σ 0 z) : z ≠ σ.vertexOne := by
  rintro rfl
  rw [canon_zero_vertexOne] at hc
  linarith [(hyp_e_lt h hp).1]

theorem ne_vertexTwo_of_canon {z : ℂ} (hc : -L.e ≤ canon σ 1 z) : z ≠ σ.vertexTwo := by
  rintro rfl
  rw [canon_one_vertexTwo] at hc
  linarith [(hyp_e_lt h hp).2]

theorem ne_vertexTwo_of_regionOne {z : ℂ} (hz : z ∈ hypRegionOne σ L) : z ≠ σ.vertexTwo := by
  have he := hp.2.2.2.2.1
  have s := canon_zero_add_one_nonneg h hz.1
  exact ne_vertexTwo_of_canon h hp (by linarith [hz.2.2])

theorem ne_vertexOne_of_regionTwo {z : ℂ} (hz : z ∈ hypRegionTwo σ L) : z ≠ σ.vertexOne := by
  have he := hp.2.2.2.2.1
  have s := canon_zero_add_one_nonneg h hz.1
  exact ne_vertexOne_of_canon h hp (by linarith [hz.2.2])

theorem hypPreFold_regionOne {z : ℂ} (hz : z ∈ hypRegionOne σ L) :
    hypPreFold σ L z = cornerOne σ L.a L.b L.β L.β' z := by
  obtain ⟨hg0, hga, hab, -, he0, -⟩ := id hp
  obtain ⟨hT, -, hc⟩ := hz
  have s01 := canon_zero_add_one_nonneg h hT
  have s02 := canon_zero_add_two_nonneg h hT
  have c2 : ¬ hd σ 1 z < L.g := fun hlt => by linarith [canon_one_lt_of_hd h hp hlt]
  have c3 : ¬ ‖z‖ < L.g₃ := fun hlt => by linarith [canon_two_neg_of_norm hp hlt]
  by_cases c1 : hd σ 0 z < L.g
  · simp only [hypPreFold, c1, ↓reduceIte]
    symm
    refine cornerOne_eq_apexOne h hab (by linarith) (by linarith) ?_
    by_cases hv : z = σ.vertexOne
    · exact Or.inl hv
    · exact Or.inr (valid_one h hT hv).1
  · simp only [hypPreFold, c1, c2, c3, hc, ↓reduceIte]

theorem hypPreFold_regionTwo {z : ℂ} (hz : z ∈ hypRegionTwo σ L) :
    hypPreFold σ L z = cornerTwo σ L.a L.b L.β L.β' z := by
  obtain ⟨hg0, hga, hab, -, he0, -⟩ := id hp
  obtain ⟨hT, -, hc⟩ := hz
  have s01 := canon_zero_add_one_nonneg h hT
  have s12 := canon_one_add_two_nonneg h hT
  have c1 : ¬ hd σ 0 z < L.g := fun hlt => by linarith [canon_zero_lt_of_hd h hp hlt]
  have c3 : ¬ ‖z‖ < L.g₃ := fun hlt => by linarith [canon_two_neg_of_norm hp hlt]
  have c4 : ¬ canon σ 0 z < -L.e := fun hlt => by linarith
  by_cases c2 : hd σ 1 z < L.g
  · simp only [hypPreFold, c1, c2, ↓reduceIte]
    symm
    refine cornerTwo_eq_apexTwo h hab (by linarith) (by linarith) ?_
    by_cases hv : z = σ.vertexTwo
    · exact Or.inl hv
    · exact Or.inr (valid_two h hT hv).1
  · simp only [hypPreFold, c1, c2, c3, c4, hc, ↓reduceIte]

theorem norm_hypPreFold_regionOne {z : ℂ} (hz : z ∈ hypRegionOne σ L) :
    ‖hypPreFold σ L z - 3 / 2‖ = hypInnerRadial σ.p₁ L.a L.b (tauOne σ) (hd σ 0 z) := by
  obtain ⟨hg0, hga, hab, -⟩ := id hp
  rw [hypPreFold_regionOne h hp hz, cornerOne, show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by
    push_cast; ring]
  exact norm_real_add_polar _ _ _ (hypInnerRadial_nonneg (one_le_p₁ (σ := σ)) (by linarith) hab
    (tauOne_pos h) (tauOne_lt_one (σ := σ)) (hd_nonneg 0 z)
    (hd_lt_one h 0 (norm_lt_one_of_mem h hz.1)))

theorem norm_hypPreFold_regionTwo {z : ℂ} (hz : z ∈ hypRegionTwo σ L) :
    ‖hypPreFold σ L z + 3 / 2‖ = hypInnerRadial σ.p₂ L.a L.b (tauTwo σ) (hd σ 1 z) := by
  obtain ⟨hg0, hga, hab, -⟩ := id hp
  rw [hypPreFold_regionTwo h hp hz, cornerTwo,
    show ∀ u : ℂ, u + 3 / 2 = u - ((-(3 / 2) : ℝ) : ℂ) by intro u; push_cast; ring]
  exact norm_real_add_polar _ _ _ (hypInnerRadial_nonneg (one_le_p₂ (σ := σ)) (by linarith) hab
    (tauTwo_pos h) (tauTwo_lt_one (σ := σ)) (hd_nonneg 1 z)
    (hd_lt_one h 1 (norm_lt_one_of_mem h hz.1)))

theorem image_hypRegionOne {z : ℂ} (hz : z ∈ hypRegionOne σ L) :
    ‖hypPreFold σ L z - 3 / 2‖ < 3 / 2 - compactProfileSlope * L.e := by
  obtain ⟨-, -, hab, hb1, -, hc1, -⟩ := id hp
  rw [norm_hypPreFold_regionOne h hp hz]
  exact hypInnerRadial_lt_of_canonForm (one_le_p₁ (σ := σ)) hab hb1 (tauOne_pos h)
    (tauOne_lt_one (σ := σ))
    hc1 (hd_nonneg 0 z) (hd_lt_one h 0 (norm_lt_one_of_mem h hz.1)) hz.2.2

theorem image_hypRegionTwo {z : ℂ} (hz : z ∈ hypRegionTwo σ L) :
    ‖hypPreFold σ L z + 3 / 2‖ < 3 / 2 - compactProfileSlope * L.e := by
  obtain ⟨-, -, hab, hb1, -, -, hc2, -⟩ := id hp
  rw [norm_hypPreFold_regionTwo h hp hz]
  exact hypInnerRadial_lt_of_canonForm (one_le_p₂ (σ := σ)) hab hb1 (tauTwo_pos h)
    (tauTwo_lt_one (σ := σ))
    hc2 (hd_nonneg 1 z) (hd_lt_one h 1 (norm_lt_one_of_mem h hz.1)) hz.2.2

theorem hypPreFold_regionLens
    (hlens : ∀ z ∈ σ.triangle, -L.e ≤ canon σ 0 z → -L.e ≤ canon σ 1 z →
      lensCoord σ z ≤ L.β' → L.b₃ < ‖z‖)
    {z : ℂ} (hz : z ∈ hypRegionLens σ L) : hypPreFold σ L z = bridgeTwo σ z := by
  obtain ⟨-, -, -, -, -, -, -, -, hββ, -, -, -, hga₃, hab₃, -⟩ := id hp
  obtain ⟨hT, -, c0, c1, hl⟩ := hz
  have n1 : ¬ hd σ 0 z < L.g := fun hlt => by linarith [canon_zero_lt_of_hd h hp hlt]
  have n2 : ¬ hd σ 1 z < L.g := fun hlt => by linarith [canon_one_lt_of_hd h hp hlt]
  have n3 : ¬ ‖z‖ < L.g₃ := not_lt.2 (by linarith [hlens z hT c0 c1 (by linarith)])
  have n4 : ¬ canon σ 0 z < -L.e := not_lt.2 c0
  have n5 : ¬ canon σ 1 z < -L.e := not_lt.2 c1
  have n6 : |lensCoord σ z| < L.β := by rwa [abs_of_nonneg (lensCoord_nonneg_of_mem h hT)]
  simp only [hypPreFold, n1, n2, n3, n4, n5, n6, ↓reduceIte]

theorem image_hypRegionLens
    (hlens : ∀ z ∈ σ.triangle, -L.e ≤ canon σ 0 z → -L.e ≤ canon σ 1 z →
      lensCoord σ z ≤ L.β' → L.b₃ < ‖z‖)
    {z : ℂ} (hz : z ∈ hypRegionLens σ L) :
    3 / 2 - compactProfileSlope * L.e ≤ ‖hypPreFold σ L z - 3 / 2‖ ∧
      3 / 2 - compactProfileSlope * L.e ≤ ‖hypPreFold σ L z + 3 / 2‖ ∧
        ‖hypPreFold σ L z‖ < 3 / 2 := by
  have e := hypPreFold_regionLens h hp hlens hz
  obtain ⟨hT, -, c0, c1, -⟩ := hz
  have d12 := mem_domOneTwo h hT (ne_vertexOne_of_canon h hp c0) (ne_vertexTwo_of_canon h hp c1)
  obtain ⟨e1, e2⟩ := norm_bridgeTwo h d12
  rw [e, e1, e2]
  unfold modOne modTwo compactProfileSlope
  exact ⟨by linarith, by linarith, norm_bridgeTwo_lt h d12⟩

theorem hypPreFold_regionThree {z : ℂ} (hz : z ∈ hypRegionThree σ L) :
    hypPreFold σ L z = cornerThree σ L.a₃ L.b₃ 1 L.e z := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hga₃, hab₃, -⟩ := id hp
  obtain ⟨hT, h0, c0, c1, hl⟩ := hz
  have n1 : ¬ hd σ 0 z < L.g := fun hlt => by linarith [canon_zero_lt_of_hd h hp hlt]
  have n2 : ¬ hd σ 1 z < L.g := fun hlt => by linarith [canon_one_lt_of_hd h hp hlt]
  have n4 : ¬ canon σ 0 z < -L.e := not_lt.2 c0
  have n5 : ¬ canon σ 1 z < -L.e := not_lt.2 c1
  have n6 : ¬ |lensCoord σ z| < L.β := by
    rw [abs_of_nonneg (lensCoord_nonneg_of_mem h hT)]
    exact not_lt.2 hl
  by_cases n3 : ‖z‖ < L.g₃
  · simp only [hypPreFold, n1, n2, n3, ↓reduceIte]
    exact (cornerThree_eq_outerGerm hab₃ (by linarith) (valid_three hT h0)).symm
  · simp only [hypPreFold, n1, n2, n3, n4, n5, n6, ↓reduceIte]

theorem norm_hypPreFold_regionThree {z : ℂ} (hz : z ∈ hypRegionThree σ L) :
    ‖hypPreFold σ L z‖ = hypOuterRadial σ.p₃ L.a₃ L.b₃ (tauThree σ) ‖z‖ := by
  have hg := hypOuterRadial_gt (p := σ.p₃) (a := L.a₃) (b := L.b₃) (tauThree_pos h)
    (tauThree_lt_one (σ := σ)) (norm_nonneg z) (norm_lt_one_of_mem h hz.1)
  rw [hypPreFold_regionThree h hp hz, cornerThree, ofReal_zero, zero_add, norm_mul,
    Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by linarith)]

theorem image_hypRegionThree {z : ℂ} (hz : z ∈ hypRegionThree σ L) :
    13 / 5 < ‖hypPreFold σ L z‖ ∧
      3 / 2 - compactProfileSlope * L.e ≤ ‖hypPreFold σ L z - 3 / 2‖ ∧
        3 / 2 - compactProfileSlope * L.e ≤ ‖hypPreFold σ L z + 3 / 2‖ := by
  obtain ⟨-, -, -, -, he0, -, -, -, -, -, -, -, -, hab₃, hb₃, -⟩ := id hp
  have hn := norm_hypPreFold_regionThree h hp hz
  have hz' := hz
  obtain ⟨hT, h0, c0, c1, -⟩ := hz
  have hz1 := norm_lt_one_of_mem h hT
  have hg := hypOuterRadial_gt (p := σ.p₃) (a := L.a₃) (b := L.b₃) (tauThree_pos h)
    (tauThree_lt_one (σ := σ)) (norm_nonneg z) hz1
  refine ⟨hn ▸ hg, ?_⟩
  have hκ : 0 < compactProfileSlope * L.e := by unfold compactProfileSlope; positivity
  rcases lt_or_ge ‖z‖ L.b₃ with hlt | hge
  · have h3 : 3 ≤ ‖hypPreFold σ L z‖ := hn ▸ three_le_hypOuterRadial (tauThree_lt_one (σ := σ))
      (norm_nonneg z) hz1 (by linarith)
    have a := norm_sub_norm_le (hypPreFold σ L z) (3 / 2)
    have b := norm_sub_norm_le (hypPreFold σ L z) (-(3 / 2))
    rw [sub_neg_eq_add] at b
    have n32 : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by
      rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs]
      norm_num
    rw [norm_neg, n32] at b
    rw [n32] at a
    constructor <;> linarith
  · have h1 := ne_vertexOne_of_canon h hp c0
    have h2 := ne_vertexTwo_of_canon h hp c1
    have d13 := mem_domOneThree h hT h0 h1
    have d03 := mem_domZeroThree h hT h0 h2
    have hpos1 := hpos_one_at_three h hz1
    have hpos0 := hpos_zero_at_three h hz1
    have a1 : 0 ≤ angleOneAtThree σ z ∧ angleOneAtThree σ z < Real.pi :=
      halfArg_mem_Ico' hpos1 (hyp_im_bridgeOne_nonneg (hT.2 1))
    have a0 : 0 < angleZeroAtThree σ z ∧ angleZeroAtThree σ z ≤ Real.pi :=
      negHalfArg_mem_Ioc' hpos0 (hyp_im_bridgeZero_nonneg (hT.2 0))
    have hord := angleOneAtThree_le_angleZeroAtThree h d13 d03 hpos1 hpos0 (hT.2 1) (hT.2 0)
    have hM : 0 < modThree σ z := by linarith [(modThree_mem h hz1).1]
    set ν := nuThree σ 1 L.e z with hν
    have hν0 : 0 ≤ ν := coneStep_nonneg _ _ _
    have hν1 : ν ≤ 1 := coneStep_le_one _ _ _
    set Θ := (1 - ν) * angleZeroAtThree σ z + ν * angleOneAtThree σ z with hΘ
    have hΘ1 : angleOneAtThree σ z ≤ Θ := by nlinarith
    have hΘ0 : Θ ≤ angleZeroAtThree σ z := by nlinarith
    have hC : hypPreFold σ L z = (modThree σ z : ℂ) * exp ((Θ : ℂ) * I) := by
      rw [hypPreFold_regionThree h hp hz', cornerThree, angleCornerThree,
        hypOuterRadial_of_ge hab₃ hge, coneStep_eq_one hab₃ hge, ← modThree_eq_radial]
      simp only [ofReal_zero, zero_add, sub_self, zero_mul, one_mul, hΘ, hν]
    have hB1 := bridgeOne_polar h d13
    have hB0 := bridgeZero_polar h d03
    rw [ofReal_zero, zero_add] at hB1 hB0
    have q1 := normSq_polar_sub_real (modThree σ z) (3 / 2) Θ
    have q0 := normSq_polar_sub_real (modThree σ z) (-(3 / 2)) Θ
    have r1 := normSq_polar_sub_real (modThree σ z) (3 / 2) (angleOneAtThree σ z)
    have r0 := normSq_polar_sub_real (modThree σ z) (-(3 / 2)) (angleZeroAtThree σ z)
    have c32 : ((3 / 2 : ℝ) : ℂ) = 3 / 2 := by push_cast; ring
    have c32' : ((-(3 / 2) : ℝ) : ℂ) = -(3 / 2) := by push_cast; ring
    rw [← hB1, c32, (norm_bridgeOne h d13).2] at r1
    rw [← hB0, c32', sub_neg_eq_add, (norm_bridgeZero h d03).2] at r0
    rw [← hC, c32] at q1
    rw [← hC, c32', sub_neg_eq_add] at q0
    have cA := Real.cos_le_cos_of_nonneg_of_le_pi a1.1 (by linarith) hΘ1
    have cB := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) a0.2 hΘ0
    have m1 : 3 / 2 - compactProfileSlope * L.e ≤ modOne σ z := by
      unfold modOne compactProfileSlope
      linarith
    have m2 : 3 / 2 - compactProfileSlope * L.e ≤ modTwo σ z := by
      unfold modTwo compactProfileSlope
      linarith
    have hk : compactProfileSlope * L.e < 3 / 2 := by
      have := (hyp_e_lt h hp).1
      have := tauOne_lt_one (σ := σ)
      unfold compactProfileSlope
      linarith
    have p1 := mul_le_mul_of_nonneg_left cA hM.le
    have p0 := mul_le_mul_of_nonneg_left cB hM.le
    have s1 : modOne σ z ^ 2 ≤ ‖hypPreFold σ L z - 3 / 2‖ ^ 2 := by rw [q1, r1]; linarith
    have s0 : modTwo σ z ^ 2 ≤ ‖hypPreFold σ L z + 3 / 2‖ ^ 2 := by rw [q0, r0]; linarith
    exact ⟨m1.trans (le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) s1),
      m2.trans (le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) s0)⟩

theorem injOn_hypRegionOne : InjOn (hypPreFold σ L) (hypRegionOne σ L) := by
  intro z hz w hw hE
  obtain ⟨hg0, hga, hab, -, -, -, -, -, hββ, -⟩ := id hp
  have nz := norm_hypPreFold_regionOne h hp hz
  have nw := norm_hypPreFold_regionOne h hp hw
  rw [hE, nw] at nz
  have hzn := norm_lt_one_of_mem h hz.1
  have hwn := norm_lt_one_of_mem h hw.1
  have hϖ : hd σ 0 w = hd σ 0 z := (strictMonoOn_hypInnerRadial (one_le_p₁ (σ := σ)) hab
    (tauOne_pos h) (tauOne_lt_one (σ := σ))).injOn ⟨hd_nonneg 0 w, hd_lt_one h 0 hwn⟩
      ⟨hd_nonneg 0 z, hd_lt_one h 0 hzn⟩ nz
  rcases (hd_nonneg (σ := σ) 0 z).eq_or_lt with h0 | hpos
  · rw [eq_vertexOne_of_hd h hzn h0.symm, eq_vertexOne_of_hd h hwn (hϖ.trans h0.symm)]
  · have hz1 : z ≠ σ.vertexOne := fun e => by
      rw [e, hd_zero_vertexOne'] at hpos
      exact lt_irrefl _ hpos
    have hw1 : w ≠ σ.vertexOne := fun e => by
      rw [← hϖ, e, hd_zero_vertexOne'] at hpos
      exact lt_irrefl _ hpos
    have hz2 := ne_vertexTwo_of_regionOne h hp hz
    have hw2 := ne_vertexTwo_of_regionOne h hp hw
    rw [hypPreFold_regionOne h hp hz, hypPreFold_regionOne h hp hw, cornerOne, cornerOne,
      hϖ] at hE
    have hS : ((hypInnerRadial σ.p₁ L.a L.b (tauOne σ) (hd σ 0 z) : ℝ) : ℂ) ≠ 0 :=
      ofReal_ne_zero.2 (hypInnerRadial_pos (tauOne_pos h) (tauOne_lt_one (σ := σ)) hpos
        (hd_lt_one h 0 hzn)).ne'
    have hΘ := angle_eq_of_exp_eq_mem (mul_left_cancel₀ hS (add_left_cancel hE))
      (angleCornerOne_mem_of_mem h _ _ _ _ hz.1 hz1 hz2)
      (angleCornerOne_mem_of_mem h _ _ _ _ hw.1 hw1 hw2)
    exact eq_of_cornerOne h hββ hz.1 hz.2.1 hz1 hz2 hw.1 hw.2.1 hw1 hw2 hϖ hΘ

theorem injOn_hypRegionTwo : InjOn (hypPreFold σ L) (hypRegionTwo σ L) := by
  intro z hz w hw hE
  obtain ⟨hg0, hga, hab, -, -, -, -, -, hββ, -⟩ := id hp
  have nz := norm_hypPreFold_regionTwo h hp hz
  have nw := norm_hypPreFold_regionTwo h hp hw
  rw [hE, nw] at nz
  have hzn := norm_lt_one_of_mem h hz.1
  have hwn := norm_lt_one_of_mem h hw.1
  have hϖ : hd σ 1 w = hd σ 1 z := (strictMonoOn_hypInnerRadial (one_le_p₂ (σ := σ)) hab
    (tauTwo_pos h) (tauTwo_lt_one (σ := σ))).injOn ⟨hd_nonneg 1 w, hd_lt_one h 1 hwn⟩
      ⟨hd_nonneg 1 z, hd_lt_one h 1 hzn⟩ nz
  rcases (hd_nonneg (σ := σ) 1 z).eq_or_lt with h0 | hpos
  · rw [eq_vertexTwo_of_hd h hzn h0.symm, eq_vertexTwo_of_hd h hwn (hϖ.trans h0.symm)]
  · have hz2 : z ≠ σ.vertexTwo := fun e => by
      rw [e, hd_one_vertexTwo'] at hpos
      exact lt_irrefl _ hpos
    have hw2 : w ≠ σ.vertexTwo := fun e => by
      rw [← hϖ, e, hd_one_vertexTwo'] at hpos
      exact lt_irrefl _ hpos
    have hz1 := ne_vertexOne_of_regionTwo h hp hz
    have hw1 := ne_vertexOne_of_regionTwo h hp hw
    rw [hypPreFold_regionTwo h hp hz, hypPreFold_regionTwo h hp hw, cornerTwo, cornerTwo,
      hϖ] at hE
    have hS : ((hypInnerRadial σ.p₂ L.a L.b (tauTwo σ) (hd σ 1 z) : ℝ) : ℂ) ≠ 0 :=
      ofReal_ne_zero.2 (hypInnerRadial_pos (tauTwo_pos h) (tauTwo_lt_one (σ := σ)) hpos
        (hd_lt_one h 1 hzn)).ne'
    have hΘ := angle_eq_of_exp_eq_mem (mul_left_cancel₀ hS (add_left_cancel hE))
      (angleCornerTwo_mem_of_mem h _ _ _ _ hz.1 hz1 hz2)
      (angleCornerTwo_mem_of_mem h _ _ _ _ hw.1 hw1 hw2)
    exact eq_of_cornerTwo h hββ hz.1 hz.2.1 hz1 hz2 hw.1 hw.2.1 hw1 hw2 hϖ hΘ

theorem injOn_hypRegionThree : InjOn (hypPreFold σ L) (hypRegionThree σ L) := by
  intro z hz w hw hE
  obtain ⟨-, -, -, -, he0, -, -, -, -, -, -, -, -, hab₃, -, hb₃⟩ := id hp
  have nz := norm_hypPreFold_regionThree h hp hz
  have nw := norm_hypPreFold_regionThree h hp hw
  rw [hE, nw] at nz
  have hzn := norm_lt_one_of_mem h hz.1
  have hwn := norm_lt_one_of_mem h hw.1
  have hr : ‖w‖ = ‖z‖ := (strictAntiOn_hypOuterRadial (one_le_p₃ (σ := σ)) hab₃ hb₃
    (tauThree_pos h) (tauThree_lt_one (σ := σ))).injOn ⟨norm_nonneg w, hwn⟩
      ⟨norm_nonneg z, hzn⟩ nz
  have hz1 := ne_vertexOne_of_canon h hp hz.2.2.1
  have hz2 := ne_vertexTwo_of_canon h hp hz.2.2.2.1
  have hw1 := ne_vertexOne_of_canon h hp hw.2.2.1
  have hw2 := ne_vertexTwo_of_canon h hp hw.2.2.2.1
  rw [hypPreFold_regionThree h hp hz, hypPreFold_regionThree h hp hw, cornerThree, cornerThree,
    hr] at hE
  have hg := hypOuterRadial_gt (p := σ.p₃) (a := L.a₃) (b := L.b₃) (tauThree_pos h)
    (tauThree_lt_one (σ := σ)) (norm_nonneg z) hzn
  have hS : ((hypOuterRadial σ.p₃ L.a₃ L.b₃ (tauThree σ) ‖z‖ : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.2 (by linarith)
  have hΘ := angle_eq_of_exp_eq_mem (mul_left_cancel₀ hS (add_left_cancel hE))
    (angleCornerThree_mem_of_mem h _ _ _ _ hz.1 hz.2.1)
    (angleCornerThree_mem_of_mem h _ _ _ _ hw.1 hw.2.1)
  exact eq_of_cornerThree h one_pos he0 hz.1 hz.2.1 hz1 hz2 hw.1 hw.2.1 hw1 hw2 hr hΘ

theorem injOn_hypRegionLens
    (hlens : ∀ z ∈ σ.triangle, -L.e ≤ canon σ 0 z → -L.e ≤ canon σ 1 z →
      lensCoord σ z ≤ L.β' → L.b₃ < ‖z‖) :
    InjOn (hypPreFold σ L) (hypRegionLens σ L) := by
  intro z hz w hw hE
  rw [hypPreFold_regionLens h hp hlens hz, hypPreFold_regionLens h hp hlens hw] at hE
  obtain ⟨hT, -, c0, c1, -⟩ := hz
  obtain ⟨hT', -, c0', c1', -⟩ := hw
  have hzn := norm_lt_one_of_mem h hT
  have hwn := norm_lt_one_of_mem h hT'
  have d12 := mem_domOneTwo h hT (ne_vertexOne_of_canon h hp c0) (ne_vertexTwo_of_canon h hp c1)
  have d12' := mem_domOneTwo h hT' (ne_vertexOne_of_canon h hp c0')
    (ne_vertexTwo_of_canon h hp c1')
  have m1 : modOne σ z = modOne σ w := by
    rw [← (norm_bridgeTwo h d12).1, ← (norm_bridgeTwo h d12').1, hE]
  have m2 : modTwo σ z = modTwo σ w := by
    rw [← (norm_bridgeTwo h d12).2, ← (norm_bridgeTwo h d12').2, hE]
  have k1 : canon σ 0 z = canon σ 0 w := by
    unfold modOne compactProfileSlope at m1
    linarith
  have k2 : canon σ 1 z = canon σ 1 w := by
    unfold modTwo compactProfileSlope at m2
    linarith
  rw [canon_zero_eq, canon_zero_eq] at k1
  rw [canon_one_eq, canon_one_eq] at k2
  have e0 : hd σ 0 z = hd σ 0 w := (strictMonoOn_canonForm (tauOne_pos h)
    (tauOne_lt_one (σ := σ))).injOn ⟨hd_nonneg 0 z, hd_lt_one h 0 hzn⟩
      ⟨hd_nonneg 0 w, hd_lt_one h 0 hwn⟩ k1
  have e1 : hd σ 1 z = hd σ 1 w := (strictMonoOn_canonForm (tauTwo_pos h)
    (tauTwo_lt_one (σ := σ))).injOn ⟨hd_nonneg 1 z, hd_lt_one h 1 hzn⟩
      ⟨hd_nonneg 1 w, hd_lt_one h 1 hwn⟩ k2
  have n1 : ‖σ.rotTwo z‖ = ‖σ.rotTwo w‖ := by
    rw [norm_rotTwo_eq_hd h, norm_rotTwo_eq_hd h, e1]
  have n0 : ‖mob (sideOneTwo σ : ℂ) (σ.rotTwo w)‖ = ‖mob (sideOneTwo σ : ℂ) (σ.rotTwo z)‖ := by
    rw [← norm_disc_vertexOne_eq h hzn, ← norm_disc_vertexOne_eq h hwn,
      CompactShape.disc_eq_mob h, CompactShape.disc_eq_mob h]
    exact e0.symm
  have t0 := sideOneTwo_pos h
  have t1 := sideOneTwo_lt_one h
  have hWz := norm_rotTwo_lt_one h hzn
  have hWw := norm_rotTwo_lt_one h hwn
  have qz := norm_mob_ofReal_sq (one_sub_ofReal_mul_ne_zero t0 t1 hWz)
  have qw := norm_mob_ofReal_sq (one_sub_ofReal_mul_ne_zero t0 t1 hWw)
  rw [n0] at qw
  have hm := norm_mob_ofReal_lt_one t0 t1 hWz
  have hm0 := norm_nonneg (mob (sideOneTwo σ : ℂ) (σ.rotTwo z))
  have sz := normSq_eq_sq_norm_aux (σ.rotTwo z)
  have sw := normSq_eq_sq_norm_aux (σ.rotTwo w)
  rw [n1] at sz
  set m := ‖mob (sideOneTwo σ : ℂ) (σ.rotTwo z)‖ with hmdef
  set t := sideOneTwo σ with ht
  set X := (σ.rotTwo z).re with hX
  set Y := (σ.rotTwo z).im with hY
  set X' := (σ.rotTwo w).re with hX'
  set Y' := (σ.rotTwo w).im with hY'
  have hr : X ^ 2 + Y ^ 2 = X' ^ 2 + Y' ^ 2 := by linarith
  have key : 2 * t * (1 - m ^ 2) * (X - X') = 0 := by
    linear_combination qz - qw - (m ^ 2 * t ^ 2 - 1) * hr
  have hm2 : 0 < 1 - m ^ 2 := by nlinarith
  have hXX : X = X' := by
    have h2t : 2 * t * (1 - m ^ 2) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero t0.ne') hm2.ne'
    exact sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_left h2t)
  have hYY : Y = Y' := by
    have hsq : Y ^ 2 = Y' ^ 2 := by rw [hXX] at hr; linarith
    exact (pow_left_inj₀ (sector_two h hT).1 (sector_two h hT').1 two_ne_zero).1 hsq
  exact rotTwo_injOn h hzn hwn (Complex.ext hXX hYY)

theorem injOn_hypPreFold_of
    (hlens : ∀ z ∈ σ.triangle, -L.e ≤ canon σ 0 z → -L.e ≤ canon σ 1 z →
      lensCoord σ z ≤ L.β' → L.b₃ < ‖z‖) :
    InjOn (hypPreFold σ L) (σ.triangle \ {0}) := by
  intro z hz w hw hE
  have he0 := hp.2.2.2.2.1
  have hκ : 0 < compactProfileSlope * L.e := by unfold compactProfileSlope; positivity
  have t := hyp_three_le_norm_sub_add (hypPreFold σ L w)
  rcases mem_hypRegions (L := L) hz.1 hz.2 with a | a | a | a <;>
    rcases mem_hypRegions (L := L) hw.1 hw.2 with b | b | b | b
  · exact injOn_hypRegionOne h hp a b hE
  · have := image_hypRegionOne h hp a
    rw [hE] at this
    linarith [image_hypRegionTwo h hp b]
  · have := image_hypRegionOne h hp a
    rw [hE] at this
    linarith [(image_hypRegionLens h hp hlens b).1]
  · have := image_hypRegionOne h hp a
    rw [hE] at this
    linarith [(image_hypRegionThree h hp b).2.1]
  · have := image_hypRegionTwo h hp a
    rw [hE] at this
    linarith [image_hypRegionOne h hp b]
  · exact injOn_hypRegionTwo h hp a b hE
  · have := image_hypRegionTwo h hp a
    rw [hE] at this
    linarith [(image_hypRegionLens h hp hlens b).2.1]
  · have := image_hypRegionTwo h hp a
    rw [hE] at this
    linarith [(image_hypRegionThree h hp b).2.2]
  · have := (image_hypRegionLens h hp hlens a).1
    rw [hE] at this
    linarith [image_hypRegionOne h hp b]
  · have := (image_hypRegionLens h hp hlens a).2.1
    rw [hE] at this
    linarith [image_hypRegionTwo h hp b]
  · exact injOn_hypRegionLens h hp hlens a b hE
  · have := (image_hypRegionLens h hp hlens a).2.2
    rw [hE] at this
    linarith [(image_hypRegionThree h hp b).1]
  · have := (image_hypRegionThree h hp a).2.1
    rw [hE] at this
    linarith [image_hypRegionOne h hp b]
  · have := (image_hypRegionThree h hp a).2.2
    rw [hE] at this
    linarith [image_hypRegionTwo h hp b]
  · have := (image_hypRegionThree h hp a).1
    rw [hE] at this
    linarith [(image_hypRegionLens h hp hlens b).2.2]
  · exact injOn_hypRegionThree h hp a b hE

end Layout

theorem injOn_hypPreFold : InjOn (hypPreFold σ (hypLayout σ)) (σ.triangle \ {0}) :=
  injOn_hypPreFold_of h (hypLayout_params h) fun _ hz h0 h1 hl =>
    norm_gt_of_lensRegion h hz h0 h1 hl

end Hyp

end HypFold

end GC.Seifert
