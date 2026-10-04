import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldEuclidCover

/-!
# Injectivity of the flat compact fold before the core replacement

Lane CF, tier 3, curvature `0` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §5, with review 23 §6.1). The map `preFold` is
injective on the whole triangle minus `v₃ = 0` (`injOn_preFold`); the core is needed only for
smoothness. The triangle splits into four regions:
* `regionOne = {d₁ < r₁ - δ}`: `preFold = cornerOne`, `‖E - 3/2‖ = innerRadial d₁ < 3/2 - κδ`;
* `regionTwo = {d₂ < r₂ - δ}`: `preFold = cornerTwo`, `‖E + 3/2‖ < 3/2 - κδ`;
* `regionLens = {dⱼ ≥ rⱼ - δ, wallSide 2 < β}`: `preFold = bridgeTwo`, `‖E ∓ 3/2‖ ≥ 3/2 - κδ`,
  `‖E‖ < 3/2`;
* `regionThree = {dⱼ ≥ rⱼ - δ, wallSide 2 ≥ β}`: `preFold = cornerThree`, `‖E‖ > 13/5` and
  `‖E ∓ 3/2‖ ≥ 3/2 - κδ` (inside the outer bend `‖E‖ ≥ 3`; beyond it the angle lies between the
  bridge angles, and `|M e^{iΘ} ∓ 3/2|` is monotone in `Θ ∈ [0, π]`).
So the regions have pairwise disjoint images. On each region the modulus fixes the distance to
the vertex (`innerRadial`, `outerRadial` are strictly monotone) and the angle, which lies in
`[0, π]`, is strictly monotone along the whole open sector arc of that distance
(`strictMonoOn_arc`, `strictAntiOn_arc`): for the corner at `v₃` this is the global angle order of
review 23 §6.1 across the two angular intervals into which wall 2 may cut the arc, since every
validity condition of the angle derivative holds on the open sector arc (`valid_arc_three`). On the
lens the two distances `d₁, d₂` and `wallSide 2 ≥ 0` fix the point.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Set
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

theorem angle_eq_of_exp_eq_mem {a b : ℝ} (h : exp ((a : ℂ) * I) = exp ((b : ℂ) * I))
    (ha : 0 ≤ a ∧ a ≤ Real.pi) (hb : 0 ≤ b ∧ b ≤ Real.pi) : a = b := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  have hre : a = b + n * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simp at this
    linarith
  have hpi := Real.pi_pos
  have hn0 : n = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hlt
      nlinarith
    · have : (1 : ℝ) ≤ n := by exact_mod_cast hgt
      nlinarith
  rw [hn0] at hre
  simpa using hre

theorem hasDerivAt_of_shift' {g : ℝ → ℝ} {x D : ℝ} (h : HasDerivAt (fun t => g (x + t)) D 0) :
    HasDerivAt g D x := by
  have h' : HasDerivAt (fun t => g (x + t)) D (x - x) := by rwa [sub_self]
  have := h'.comp_sub_const x x
  simpa using this

theorem circ_arc (c w : ℂ) (φ t : ℝ) :
    circ c (c + w * exp ((φ : ℂ) * I)) t = c + w * exp (((φ + t : ℝ) : ℂ) * I) := by
  simp only [circ, add_sub_cancel_left]
  rw [mul_assoc, ← Complex.exp_add]
  push_cast
  ring_nf

theorem strictMonoOn_arc {c w : ℂ} {Θ : ℂ → ℝ} {a b : ℝ}
    (hcont : ∀ φ ∈ Icc a b, ContinuousAt Θ (c + w * exp ((φ : ℂ) * I)))
    (hder : ∀ φ ∈ Ioo a b, ∃ D, 0 < D ∧
      HasDerivAt (fun t => Θ (circ c (c + w * exp ((φ : ℂ) * I)) t)) D 0) :
    StrictMonoOn (fun φ : ℝ => Θ (c + w * exp ((φ : ℂ) * I))) (Icc a b) := by
  have hγ : Continuous fun φ : ℝ => c + w * exp ((φ : ℂ) * I) := by fun_prop
  refine strictMonoOn_of_deriv_pos (convex_Icc a b)
    (fun φ hφ => ((hcont φ hφ).comp (f := fun φ : ℝ => c + w * exp ((φ : ℂ) * I))
      hγ.continuousAt).continuousWithinAt) (fun φ hφ => ?_)
  rw [interior_Icc] at hφ
  obtain ⟨D, hD, h⟩ := hder φ hφ
  simp only [circ_arc] at h
  rw [(hasDerivAt_of_shift' h).deriv]
  exact hD

theorem strictAntiOn_arc {c w : ℂ} {Θ : ℂ → ℝ} {a b : ℝ}
    (hcont : ∀ φ ∈ Icc a b, ContinuousAt Θ (c + w * exp ((φ : ℂ) * I)))
    (hder : ∀ φ ∈ Ioo a b, ∃ D, D < 0 ∧
      HasDerivAt (fun t => Θ (circ c (c + w * exp ((φ : ℂ) * I)) t)) D 0) :
    StrictAntiOn (fun φ : ℝ => Θ (c + w * exp ((φ : ℂ) * I))) (Icc a b) := by
  have hγ : Continuous fun φ : ℝ => c + w * exp ((φ : ℂ) * I) := by fun_prop
  refine strictAntiOn_of_deriv_neg (convex_Icc a b)
    (fun φ hφ => ((hcont φ hφ).comp (f := fun φ : ℝ => c + w * exp ((φ : ℂ) * I))
      hγ.continuousAt).continuousWithinAt) (fun φ hφ => ?_)
  rw [interior_Icc] at hφ
  obtain ⟨D, hD, h⟩ := hder φ hφ
  simp only [circ_arc] at h
  rw [(hasDerivAt_of_shift' h).deriv]
  exact hD

theorem strictMonoOn_innerRadial {p : ℕ} (hp : 1 ≤ p) {a b r₀ : ℝ} (hab : a < b) (hb : b ≤ 1)
    (hr₀ : r₀ < 1) : StrictMonoOn (innerRadial p a b r₀) (Ici 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0)
    (EuclidShape.contDiff_innerRadial p a b r₀).continuous.continuousOn (fun x hx => ?_)
  rw [interior_Ici] at hx
  obtain ⟨S', hS', h⟩ := exists_hasDerivAt_innerRadial hp hab hb hr₀ hx
  rw [h.deriv]
  exact hS'

theorem strictAntiOn_outerRadial {p : ℕ} (hp : 1 ≤ p) {a b r₀ : ℝ} (hab : a < b)
    (hb : b ≤ 1 / 5) (hr₀ : r₀ < 1) : StrictAntiOn (outerRadial p a b r₀) (Ici 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ici 0)
    (EuclidShape.contDiff_outerRadial p a b r₀).continuous.continuousOn (fun x hx => ?_)
  rw [interior_Ici] at hx
  obtain ⟨S', hS', h⟩ := exists_hasDerivAt_outerRadial hp hab hb hr₀ hx
  rw [h.deriv]
  exact hS'

theorem innerRadial_zero {p : ℕ} (hp : 1 ≤ p) {a b r₀ : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    innerRadial p a b r₀ 0 = 0 := by
  rw [innerRadial, coneStep_eq_zero hab ha, zero_pow (by omega)]
  ring

theorem innerRadial_of_ge {p : ℕ} {a b r₀ d : ℝ} (hab : a < b) (hd : b ≤ d) :
    innerRadial p a b r₀ d = 3 / 2 + EuclidShape.profileSlope * (d - r₀) := by
  rw [innerRadial, coneStep_eq_one hab hd]
  ring

theorem outerRadial_of_ge {p : ℕ} {a b r₀ d : ℝ} (hab : a < b) (hd : b ≤ d) :
    outerRadial p a b r₀ d = 3 - EuclidShape.profileSlope * (d - r₀) := by
  rw [outerRadial, coneStep_eq_one hab hd]
  ring

theorem norm_real_add_polar (c S Θ : ℝ) (hS : 0 ≤ S) :
    ‖((c : ℝ) : ℂ) + (S : ℂ) * exp ((Θ : ℂ) * I) - (c : ℂ)‖ = S := by
  rw [add_sub_cancel_left, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hS]

theorem normSq_polar_sub_real (M c Θ : ℝ) :
    ‖(M : ℂ) * exp ((Θ : ℂ) * I) - (c : ℂ)‖ ^ 2 = M ^ 2 - 2 * c * M * Real.cos Θ + c ^ 2 := by
  rw [EuclidShape.normSq_eq_sq_norm]
  simp only [sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero, add_zero]
  have := Real.sin_sq_add_cos_sq Θ
  linear_combination M ^ 2 * this

theorem norm_add_re_pos_of_im_ne {w : ℂ} (h : w.im ≠ 0) : 0 < ‖w‖ + w.re := by
  have := Complex.abs_re_lt_norm.2 h
  linarith [neg_abs_le w.re]

theorem convex_mem_angle {τ x y : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) (hx : 0 ≤ x ∧ x ≤ Real.pi)
    (hy : 0 ≤ y ∧ y ≤ Real.pi) : 0 ≤ (1 - τ) * x + τ * y ∧ (1 - τ) * x + τ * y ≤ Real.pi := by
  constructor <;> nlinarith

namespace EuclidShape

variable (σ : EuclidShape)

theorem proj_one_nonneg {z : ℂ} (hz : z ∈ σ.triangle) :
    0 ≤ Real.sin σ.θ₃ - (σ.rotTwo z).re := by
  have h1 := hz 1
  have h2 := hz 2
  rw [σ.wallSide_one_eq_proj] at h1
  by_contra hneg
  have := mul_neg_of_pos_of_neg σ.sin_θ₁_pos (not_le.1 hneg)
  nlinarith [mul_nonneg σ.cos_θ₁_nonneg h2]

theorem proj_two_nonneg {z : ℂ} (hz : z ∈ σ.triangle) : 0 ≤ (σ.rotTwo z).re := by
  have h0 := hz 0
  have h2 := hz 2
  rw [σ.wallSide_zero_eq_proj] at h0
  by_contra hneg
  have := mul_neg_of_pos_of_neg σ.sin_θ₂_pos (not_le.1 hneg)
  nlinarith [mul_nonneg σ.cos_θ₂_nonneg h2]

theorem kappa_delta_pos : 0 < profileSlope * σ.cornerShrink := by
  unfold profileSlope
  linarith [σ.cornerShrink_pos]

theorem kappa_delta_lt : profileSlope * σ.cornerShrink < 3 / 2 := by
  have := σ.cornerShrink_lt_inradius
  have := σ.inradius_lt_half
  unfold profileSlope
  linarith

def regionOne : Set ℂ := {z | z ∈ σ.triangle ∧ ‖z - σ.vertexOne‖ < σ.radOne - σ.cornerShrink}

def regionTwo : Set ℂ := {z | z ∈ σ.triangle ∧ ‖z - σ.vertexTwo‖ < σ.radTwo - σ.cornerShrink}

def regionLens : Set ℂ :=
  {z | z ∈ σ.triangle ∧ σ.radOne - σ.cornerShrink ≤ ‖z - σ.vertexOne‖ ∧
    σ.radTwo - σ.cornerShrink ≤ ‖z - σ.vertexTwo‖ ∧ σ.wallSide 2 z < σ.lensWidth}

def regionThree : Set ℂ :=
  {z | z ∈ σ.triangle ∧ z ≠ 0 ∧ σ.radOne - σ.cornerShrink ≤ ‖z - σ.vertexOne‖ ∧
    σ.radTwo - σ.cornerShrink ≤ ‖z - σ.vertexTwo‖ ∧ σ.lensWidth ≤ σ.wallSide 2 z}

theorem mem_regions {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) :
    z ∈ σ.regionOne ∨ z ∈ σ.regionTwo ∨ z ∈ σ.regionLens ∨ z ∈ σ.regionThree := by
  by_cases c1 : ‖z - σ.vertexOne‖ < σ.radOne - σ.cornerShrink
  · exact Or.inl ⟨hz, c1⟩
  by_cases c2 : ‖z - σ.vertexTwo‖ < σ.radTwo - σ.cornerShrink
  · exact Or.inr (Or.inl ⟨hz, c2⟩)
  rw [not_lt] at c1 c2
  by_cases l : σ.wallSide 2 z < σ.lensWidth
  · exact Or.inr (Or.inr (Or.inl ⟨hz, c1, c2, l⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hz, h0, c1, c2, not_lt.1 l⟩))

theorem ne_zero_of_regionOne {z : ℂ} (hz : z ∈ σ.regionOne) : z ≠ 0 := by
  have hfar := (σ.far_of_cornerOne hz.2).2
  rintro rfl
  rw [norm_zero] at hfar
  linarith [σ.radThree_pos, σ.cornerShrink_pos]

theorem ne_zero_of_regionTwo {z : ℂ} (hz : z ∈ σ.regionTwo) : z ≠ 0 := by
  have hfar := (σ.far_of_cornerTwo hz.2).2
  rintro rfl
  rw [norm_zero] at hfar
  linarith [σ.radThree_pos, σ.cornerShrink_pos]

theorem preFold_regionOne {z : ℂ} (hz : z ∈ σ.regionOne) :
    σ.preFold z = σ.foldCornerOne z := by
  have h0 := σ.ne_zero_of_regionOne hz
  obtain ⟨hT, hr⟩ := hz
  have hp := σ.params
  have hfar := σ.far_of_cornerOne hr
  have h2 := σ.inradius_le_radTwo
  have h3 := σ.inradius_le_radThree
  have hc2 : ¬ ‖z - σ.vertexTwo‖ < σ.germRadius := by
    unfold germRadius cornerShrink at *
    linarith [hfar.1]
  have hc3 : ¬ ‖z‖ < σ.outerGermRadius := by
    unfold outerGermRadius cornerShrink at *
    linarith [hfar.2]
  rcases lt_or_ge ‖z - σ.vertexOne‖ σ.germRadius with h1 | h1
  · simp only [preFold, h1, ↓reduceIte, foldCornerOne]
    refine (σ.cornerOne_eq_apexOne hp.2.2.1 (by unfold blendStart; linarith [hp.1])
      (by linarith [hp.2.1]) ?_).symm
    by_cases hv : z = σ.vertexOne
    · exact Or.inl hv
    · exact Or.inr (σ.psiOne_pos_of_domOne (σ.triangle_subset_domOne hT h0 hv))
  · have h1' : ¬ ‖z - σ.vertexOne‖ < σ.germRadius := not_lt.2 h1
    simp only [preFold, h1', hc2, hc3, hr, ↓reduceIte]

theorem preFold_regionTwo {z : ℂ} (hz : z ∈ σ.regionTwo) :
    σ.preFold z = σ.foldCornerTwo z := by
  have h0 := σ.ne_zero_of_regionTwo hz
  obtain ⟨hT, hr⟩ := hz
  have hp := σ.params
  have hfar := σ.far_of_cornerTwo hr
  have h1' := σ.inradius_le_radOne
  have h3 := σ.inradius_le_radThree
  have hc1 : ¬ ‖z - σ.vertexOne‖ < σ.germRadius := by
    unfold germRadius cornerShrink at *
    linarith [hfar.1]
  have hc3 : ¬ ‖z‖ < σ.outerGermRadius := by
    unfold outerGermRadius cornerShrink at *
    linarith [hfar.2]
  have hc4 : ¬ ‖z - σ.vertexOne‖ < σ.radOne - σ.cornerShrink := by
    linarith [hfar.1, hp.2.2.2.2.2.2.2.2.2.2.2.1]
  rcases lt_or_ge ‖z - σ.vertexTwo‖ σ.germRadius with h2 | h2
  · simp only [preFold, hc1, h2, ↓reduceIte, foldCornerTwo]
    refine (σ.cornerTwo_eq_apexTwo hp.2.2.1 (by unfold blendStart; linarith [hp.1])
      (by linarith [hp.2.1]) ?_).symm
    by_cases hv : z = σ.vertexTwo
    · exact Or.inl hv
    · have hv1 : z ≠ σ.vertexOne := by
        rintro rfl
        rw [sub_self, norm_zero] at hfar
        linarith [hfar.1, σ.radOne_pos, σ.cornerShrink_pos]
      exact Or.inr (σ.psiTwo_pos_of_domTwo (σ.triangle_subset_domTwo hT hv1 hv))
  · have h2' : ¬ ‖z - σ.vertexTwo‖ < σ.germRadius := not_lt.2 h2
    simp only [preFold, hc1, h2', hc3, hc4, hr, ↓reduceIte]

theorem not_germ_of_far {z : ℂ} (c1 : σ.radOne - σ.cornerShrink ≤ ‖z - σ.vertexOne‖)
    (c2 : σ.radTwo - σ.cornerShrink ≤ ‖z - σ.vertexTwo‖) :
    ¬ ‖z - σ.vertexOne‖ < σ.germRadius ∧ ¬ ‖z - σ.vertexTwo‖ < σ.germRadius := by
  have hp := σ.params
  constructor <;> refine not_lt.2 ?_ <;> linarith [hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1]

theorem preFold_regionLens {z : ℂ} (hz : z ∈ σ.regionLens) :
    σ.preFold z = σ.bridgeTwo z := by
  obtain ⟨hT, c1, c2, l⟩ := hz
  obtain ⟨hc1, hc2⟩ := σ.not_germ_of_far c1 c2
  have hl : |σ.wallSide 2 z| < σ.lensWidth := by rwa [abs_of_nonneg (hT 2)]
  have hc3 : ¬ ‖z‖ < σ.outerGermRadius := not_lt.2 (σ.norm_ge_of_lens hl).le
  have hr1 : ¬ ‖z - σ.vertexOne‖ < σ.radOne - σ.cornerShrink := not_lt.2 c1
  have hr2 : ¬ ‖z - σ.vertexTwo‖ < σ.radTwo - σ.cornerShrink := not_lt.2 c2
  simp only [preFold, hc1, hc2, hc3, hr1, hr2, hl, ↓reduceIte]

theorem preFold_regionThree {z : ℂ} (hz : z ∈ σ.regionThree) :
    σ.preFold z = σ.foldCornerThree z := by
  obtain ⟨hT, h0, c1, c2, l⟩ := hz
  have hp := σ.params
  obtain ⟨hc1, hc2⟩ := σ.not_germ_of_far c1 c2
  have hr1 : ¬ ‖z - σ.vertexOne‖ < σ.radOne - σ.cornerShrink := not_lt.2 c1
  have hr2 : ¬ ‖z - σ.vertexTwo‖ < σ.radTwo - σ.cornerShrink := not_lt.2 c2
  have hl : ¬ |σ.wallSide 2 z| < σ.lensWidth := not_lt.2 (by rwa [abs_of_nonneg (hT 2)])
  by_cases h3 : ‖z‖ < σ.outerGermRadius
  · simp only [preFold, hc1, hc2, h3, ↓reduceIte, foldCornerThree]
    exact (σ.cornerThree_eq_outerGerm hp.2.2.2.2.2.2.2.2.1
      (by linarith [hp.2.2.2.2.2.2.2.1]) (σ.norm_pos_add_re hT h0)).symm
  · simp only [preFold, hc1, hc2, h3, hr1, hr2, hl, ↓reduceIte]


theorem blendStart_nonneg : 0 ≤ σ.blendStart := by
  unfold blendStart
  linarith [σ.inradius_pos]

theorem strictMono_innerOne :
    StrictMonoOn (innerRadial σ.p₁ σ.blendStart σ.blendEnd σ.radOne) (Ici 0) :=
  strictMonoOn_innerRadial σ.one_le_p₁ σ.params.2.2.1 σ.params.2.2.2.2.2.1 σ.radOne_lt_one

theorem strictMono_innerTwo :
    StrictMonoOn (innerRadial σ.p₂ σ.blendStart σ.blendEnd σ.radTwo) (Ici 0) :=
  strictMonoOn_innerRadial σ.one_le_p₂ σ.params.2.2.1 σ.params.2.2.2.2.2.1 σ.radTwo_lt_one

theorem strictAnti_outer :
    StrictAntiOn (outerRadial σ.p₃ σ.outerBlendStart σ.outerBlendEnd σ.radThree) (Ici 0) :=
  strictAntiOn_outerRadial σ.one_le_p₃ σ.params.2.2.2.2.2.2.2.2.1
    σ.params.2.2.2.2.2.2.2.2.2.1 σ.radThree_lt_one

theorem innerOne_nonneg {d : ℝ} (hd : 0 ≤ d) :
    0 ≤ innerRadial σ.p₁ σ.blendStart σ.blendEnd σ.radOne d := by
  have := σ.strictMono_innerOne.monotoneOn (Set.mem_Ici.2 le_rfl) hd hd
  rwa [innerRadial_zero σ.one_le_p₁ σ.blendStart_nonneg σ.params.2.2.1] at this

theorem innerTwo_nonneg {d : ℝ} (hd : 0 ≤ d) :
    0 ≤ innerRadial σ.p₂ σ.blendStart σ.blendEnd σ.radTwo d := by
  have := σ.strictMono_innerTwo.monotoneOn (Set.mem_Ici.2 le_rfl) hd hd
  rwa [innerRadial_zero σ.one_le_p₂ σ.blendStart_nonneg σ.params.2.2.1] at this

theorem innerOne_lt {d : ℝ} (hd0 : 0 ≤ d) (hd : d < σ.radOne - σ.cornerShrink) :
    innerRadial σ.p₁ σ.blendStart σ.blendEnd σ.radOne d <
      3 / 2 - profileSlope * σ.cornerShrink := by
  have hp := σ.params
  have h := σ.strictMono_innerOne hd0 (show (0 : ℝ) ≤ σ.radOne - σ.cornerShrink by
    linarith [hp.2.2.2.1, hp.2.1, hp.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.2.1]) hd
  rw [innerRadial_of_ge hp.2.2.1 hp.2.2.2.1.le] at h
  unfold profileSlope at h ⊢
  linarith

theorem innerTwo_lt {d : ℝ} (hd0 : 0 ≤ d) (hd : d < σ.radTwo - σ.cornerShrink) :
    innerRadial σ.p₂ σ.blendStart σ.blendEnd σ.radTwo d <
      3 / 2 - profileSlope * σ.cornerShrink := by
  have hp := σ.params
  have h := σ.strictMono_innerTwo hd0 (show (0 : ℝ) ≤ σ.radTwo - σ.cornerShrink by
    linarith [hp.2.2.2.2.1, hp.2.1, hp.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.2.1]) hd
  rw [innerRadial_of_ge hp.2.2.1 hp.2.2.2.2.1.le] at h
  unfold profileSlope at h ⊢
  linarith

theorem three_halves_cast : (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) := by
  push_cast
  ring

theorem norm_preFold_regionOne {z : ℂ} (hz : z ∈ σ.regionOne) :
    ‖σ.preFold z - 3 / 2‖ =
      innerRadial σ.p₁ σ.blendStart σ.blendEnd σ.radOne ‖z - σ.vertexOne‖ := by
  rw [σ.preFold_regionOne hz, foldCornerOne, cornerOne, three_halves_cast]
  exact norm_real_add_polar _ _ _ (σ.innerOne_nonneg (norm_nonneg _))

theorem norm_preFold_regionTwo {z : ℂ} (hz : z ∈ σ.regionTwo) :
    ‖σ.preFold z + 3 / 2‖ =
      innerRadial σ.p₂ σ.blendStart σ.blendEnd σ.radTwo ‖z - σ.vertexTwo‖ := by
  rw [σ.preFold_regionTwo hz, foldCornerTwo, cornerTwo,
    show ∀ u : ℂ, u + 3 / 2 = u - ((-(3 / 2) : ℝ) : ℂ) by intro u; push_cast; ring]
  exact norm_real_add_polar _ _ _ (σ.innerTwo_nonneg (norm_nonneg _))

theorem image_regionOne {z : ℂ} (hz : z ∈ σ.regionOne) :
    ‖σ.preFold z - 3 / 2‖ < 3 / 2 - profileSlope * σ.cornerShrink := by
  rw [σ.norm_preFold_regionOne hz]
  exact σ.innerOne_lt (norm_nonneg _) hz.2

theorem image_regionTwo {z : ℂ} (hz : z ∈ σ.regionTwo) :
    ‖σ.preFold z + 3 / 2‖ < 3 / 2 - profileSlope * σ.cornerShrink := by
  rw [σ.norm_preFold_regionTwo hz]
  exact σ.innerTwo_lt (norm_nonneg _) hz.2

theorem radOne_sub_pos : 0 < σ.radOne - σ.cornerShrink := by
  have hp := σ.params
  linarith [hp.2.2.2.1, hp.2.1, hp.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.2.1]

theorem radTwo_sub_pos : 0 < σ.radTwo - σ.cornerShrink := by
  have hp := σ.params
  linarith [hp.2.2.2.2.1, hp.2.1, hp.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.2.1]

theorem image_regionLens {z : ℂ} (hz : z ∈ σ.regionLens) :
    3 / 2 - profileSlope * σ.cornerShrink ≤ ‖σ.preFold z - 3 / 2‖ ∧
      3 / 2 - profileSlope * σ.cornerShrink ≤ ‖σ.preFold z + 3 / 2‖ ∧
        ‖σ.preFold z‖ < 3 / 2 := by
  have e := σ.preFold_regionLens hz
  obtain ⟨hT, c1, c2, -⟩ := hz
  have h1 := ne_of_norm_pos σ.radOne_sub_pos c1
  have h2 := ne_of_norm_pos σ.radTwo_sub_pos c2
  obtain ⟨e1, e2⟩ := σ.norm_bridgeTwo (σ.triangle_subset_domTwo hT h1 h2)
  rw [e, e1, e2, modOne_eq, modTwo_eq]
  unfold profileSlope
  exact ⟨by linarith, by linarith, σ.norm_bridgeTwo_lt hT h1 h2⟩

theorem outerRadial_ge_three {z : ℂ} (hz : z ∈ σ.triangle) (h : ‖z‖ < σ.outerBlendEnd) :
    3 ≤ outerRadial σ.p₃ σ.outerBlendStart σ.outerBlendEnd σ.radThree ‖z‖ := by
  have hp := σ.params
  have hd1 : ‖z‖ ≤ 1 := σ.norm_le_one_of_mem hz
  have hA : ‖z‖ ^ σ.p₃ ≤ 1 := pow_le_one₀ (norm_nonneg _) hd1
  have hB : 3 ≤ 3 - profileSlope * (‖z‖ - σ.radThree) := by
    unfold profileSlope
    linarith [hp.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  have hτ0 := coneStep_nonneg σ.outerBlendStart σ.outerBlendEnd ‖z‖
  have hτ1 := coneStep_le_one σ.outerBlendStart σ.outerBlendEnd ‖z‖
  unfold outerRadial
  nlinarith [mul_nonneg hτ0 (by linarith : (0 : ℝ) ≤ 3 - profileSlope * (‖z‖ - σ.radThree) - 3),
    mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - coneStep σ.outerBlendStart σ.outerBlendEnd ‖z‖)
      (by linarith : (0 : ℝ) ≤ 7 / 2 - ‖z‖ ^ σ.p₃ / 2 - 3)]

theorem outerRadial_gt {z : ℂ} (hz : z ∈ σ.triangle) :
    13 / 5 < outerRadial σ.p₃ σ.outerBlendStart σ.outerBlendEnd σ.radThree ‖z‖ := by
  rcases lt_or_ge ‖z‖ σ.outerBlendEnd with h | h
  · linarith [σ.outerRadial_ge_three hz h]
  · rw [outerRadial_of_ge σ.params.2.2.2.2.2.2.2.2.1 h, ← modThree_eq]
    exact (σ.modThree_mem hz).1

theorem norm_preFold_regionThree {z : ℂ} (hz : z ∈ σ.regionThree) :
    ‖σ.preFold z‖ = outerRadial σ.p₃ σ.outerBlendStart σ.outerBlendEnd σ.radThree ‖z‖ := by
  have hS := (σ.outerRadial_gt hz.1).le
  rw [σ.preFold_regionThree hz, foldCornerThree, cornerThree, ofReal_zero, zero_add, norm_mul,
    Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith)]

theorem im_bridgeOne_nonneg {z : ℂ} (hz : z ∈ σ.triangle) : 0 ≤ (σ.bridgeOne z).im := by
  rw [bridgeOne, twoCircle_im]
  have := Real.sqrt_nonneg (σ.cofBridgeOne z)
  have := hz 1
  positivity

theorem im_bridgeZero_nonneg {z : ℂ} (hz : z ∈ σ.triangle) : 0 ≤ (σ.bridgeZero z).im := by
  rw [bridgeZero, twoCircle_im]
  have := Real.sqrt_nonneg (σ.cofBridgeZero z)
  have := hz 0
  positivity

theorem im_bridgeTwo_nonneg {z : ℂ} (hz : z ∈ σ.triangle) : 0 ≤ (σ.bridgeTwo z).im := by
  rw [bridgeTwo, twoCircle_im]
  have := Real.sqrt_nonneg (σ.cofBridgeTwo z)
  have := hz 2
  positivity

theorem angles_three {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) (h1 : z ≠ σ.vertexOne)
    (h2 : z ≠ σ.vertexTwo) :
    0 ≤ σ.angleOneAtThree z ∧ σ.angleOneAtThree z ≤ σ.angleZeroAtThree z ∧
      σ.angleZeroAtThree z ≤ Real.pi := by
  have d1 := σ.triangle_subset_domOne hz h0 h1
  have d0 := σ.triangle_subset_domZero hz h0 h2
  have hM := σ.modThree_pos d1.2.2
  have r1 := σ.re_bridgeOne_pos hz
  have r0 := σ.re_bridgeZero_neg hz
  refine ⟨(halfArg_mem_Ico (by linarith) (σ.im_bridgeOne_nonneg hz)).1,
    (halfArg_lt_negHalfArg_of_re hM r1 r0 (σ.sq_of_bridgeOne_three d1)
      (σ.sq_of_bridgeZero_three d0)).le,
    (negHalfArg_mem_Ioc (by linarith) (σ.im_bridgeZero_nonneg hz)).2⟩

theorem preFold_regionThree_far {z : ℂ} (hz : z ∈ σ.regionThree)
    (h : σ.outerBlendEnd ≤ ‖z‖) :
    σ.preFold z = (σ.modThree z : ℂ) * exp ((((1 - σ.nuThree 1 σ.cornerShrink z) *
      σ.angleZeroAtThree z + σ.nuThree 1 σ.cornerShrink z * σ.angleOneAtThree z : ℝ) : ℂ) * I) := by
  have hab := σ.params.2.2.2.2.2.2.2.2.1
  rw [σ.preFold_regionThree hz, foldCornerThree, cornerThree, angleCornerThree,
    outerRadial_of_ge hab h, coneStep_eq_one hab h, ← modThree_eq]
  simp only [ofReal_zero, zero_add, sub_self, zero_mul, one_mul]

theorem image_regionThree {z : ℂ} (hz : z ∈ σ.regionThree) :
    13 / 5 < ‖σ.preFold z‖ ∧ 3 / 2 - profileSlope * σ.cornerShrink ≤ ‖σ.preFold z - 3 / 2‖ ∧
      3 / 2 - profileSlope * σ.cornerShrink ≤ ‖σ.preFold z + 3 / 2‖ := by
  have hn := σ.norm_preFold_regionThree hz
  have hg := σ.outerRadial_gt hz.1
  have hk := σ.kappa_delta_lt
  have hk0 := σ.kappa_delta_pos
  refine ⟨hn ▸ hg, ?_⟩
  have hz' := hz
  obtain ⟨hT, h0, c1, c2, -⟩ := hz
  have h1 := ne_of_norm_pos σ.radOne_sub_pos c1
  have h2 := ne_of_norm_pos σ.radTwo_sub_pos c2
  rcases lt_or_ge ‖z‖ σ.outerBlendEnd with h | h
  · have h3 := σ.outerRadial_ge_three hT h
    have a := norm_sub_norm_le (σ.preFold z) (3 / 2)
    have b := norm_sub_norm_le (σ.preFold z) (-(3 / 2))
    rw [sub_neg_eq_add] at b
    have n32 : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by
      rw [three_halves_cast, Complex.norm_real, Real.norm_eq_abs]
      norm_num
    rw [norm_neg, n32] at b
    rw [n32] at a
    constructor <;> linarith
  · have d1 := σ.triangle_subset_domOne hT h0 h1
    have d0 := σ.triangle_subset_domZero hT h0 h2
    obtain ⟨a0, a10, a1π⟩ := σ.angles_three hT h0 h1 h2
    have hM := σ.modThree_pos d1.2.2
    set ν := σ.nuThree 1 σ.cornerShrink z with hν
    have hν0 : 0 ≤ ν := coneStep_nonneg _ _ _
    have hν1 : ν ≤ 1 := coneStep_le_one _ _ _
    set Θ := (1 - ν) * σ.angleZeroAtThree z + ν * σ.angleOneAtThree z with hΘ
    have hΘ1 : σ.angleOneAtThree z ≤ Θ := by nlinarith
    have hΘ0 : Θ ≤ σ.angleZeroAtThree z := by nlinarith
    have hC := σ.preFold_regionThree_far hz' h
    rw [← hΘ] at hC
    have hpos1 : 0 < σ.modThree z + (σ.bridgeOne z).re := by linarith [σ.re_bridgeOne_pos hT]
    have hpos0 : 0 < σ.modThree z - (σ.bridgeZero z).re := by linarith [σ.re_bridgeZero_neg hT]
    have hB1 := σ.bridgeOne_eq_polar_three d1 hpos1
    have hB0 := σ.bridgeZero_eq_polar_three d0 hpos0
    rw [ofReal_zero, zero_add] at hB1 hB0
    have q1 := normSq_polar_sub_real (σ.modThree z) (3 / 2) Θ
    have q0 := normSq_polar_sub_real (σ.modThree z) (-(3 / 2)) Θ
    have r1 := normSq_polar_sub_real (σ.modThree z) (3 / 2) (σ.angleOneAtThree z)
    have r0 := normSq_polar_sub_real (σ.modThree z) (-(3 / 2)) (σ.angleZeroAtThree z)
    rw [← hB1, ← three_halves_cast, (σ.norm_bridgeOne d1).2] at r1
    rw [← hB0, show ((-(3 / 2) : ℝ) : ℂ) = -(3 / 2) by push_cast; ring, sub_neg_eq_add,
      (σ.norm_bridgeZero d0).2] at r0
    rw [← hC, ← three_halves_cast] at q1
    rw [← hC, show ((-(3 / 2) : ℝ) : ℂ) = -(3 / 2) by push_cast; ring, sub_neg_eq_add] at q0
    have cA := Real.cos_le_cos_of_nonneg_of_le_pi a0 (by linarith) hΘ1
    have cB := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) a1π hΘ0
    have m1 : 3 / 2 - profileSlope * σ.cornerShrink ≤ σ.modOne z := by
      rw [modOne_eq]
      unfold profileSlope at *
      linarith
    have m2 : 3 / 2 - profileSlope * σ.cornerShrink ≤ σ.modTwo z := by
      rw [modTwo_eq]
      unfold profileSlope at *
      linarith
    constructor
    · nlinarith [norm_nonneg (σ.preFold z - 3 / 2)]
    · nlinarith [norm_nonneg (σ.preFold z + 3 / 2)]


theorem rotTwo_inj {z w : ℂ} (h : σ.rotTwo z = σ.rotTwo w) : z = w := by
  have := σ.norm_sub_eq_rotTwo z w
  rw [h, sub_self, norm_zero, norm_eq_zero, sub_eq_zero] at this
  exact this

theorem injOn_regionLens : InjOn σ.preFold σ.regionLens := by
  intro z hz w hw h
  rw [σ.preFold_regionLens hz, σ.preFold_regionLens hw] at h
  obtain ⟨hT, c1, c2, -⟩ := hz
  obtain ⟨hT', c1', c2', -⟩ := hw
  obtain ⟨e1, e2⟩ := σ.norm_bridgeTwo (σ.triangle_subset_domTwo hT
    (ne_of_norm_pos σ.radOne_sub_pos c1) (ne_of_norm_pos σ.radTwo_sub_pos c2))
  obtain ⟨e1', e2'⟩ := σ.norm_bridgeTwo (σ.triangle_subset_domTwo hT'
    (ne_of_norm_pos σ.radOne_sub_pos c1') (ne_of_norm_pos σ.radTwo_sub_pos c2'))
  rw [h, e1'] at e1
  rw [h, e2'] at e2
  rw [modOne_eq, modOne_eq] at e1
  rw [modTwo_eq, modTwo_eq] at e2
  unfold profileSlope at e1 e2
  have d1 : ‖w - σ.vertexOne‖ = ‖z - σ.vertexOne‖ := by linarith
  have d2 : ‖w - σ.vertexTwo‖ = ‖z - σ.vertexTwo‖ := by linarith
  have q1 := σ.norm_sq_sub_vertexOne z
  have q2 := σ.norm_sq_sub_vertexTwo z
  have q1' := σ.norm_sq_sub_vertexOne w
  have q2' := σ.norm_sq_sub_vertexTwo w
  rw [d1] at q1'
  rw [d2] at q2'
  have hs := σ.sin_θ₃_pos
  have hX : (σ.rotTwo z).re = (σ.rotTwo w).re := by
    have : 2 * Real.sin σ.θ₃ * ((σ.rotTwo z).re - (σ.rotTwo w).re) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · linarith
  have hW : σ.wallSide 2 z = σ.wallSide 2 w := by
    have hsq : σ.wallSide 2 z ^ 2 = σ.wallSide 2 w ^ 2 := by rw [hX] at q2; linarith
    exact (pow_left_inj₀ (hT 2) (hT' 2) two_ne_zero).1 hsq
  exact σ.rotTwo_inj (Complex.ext hX hW)

theorem p₁_mul_le {ψ : ℝ} (h0 : 0 ≤ ψ) (h1 : ψ ≤ σ.θ₁) :
    0 ≤ (σ.p₁ : ℝ) * ψ ∧ (σ.p₁ : ℝ) * ψ ≤ Real.pi := by
  have hp : (0 : ℝ) ≤ σ.p₁ := Nat.cast_nonneg _
  refine ⟨mul_nonneg hp h0, ?_⟩
  rw [← σ.θ₁_mul, mul_comm σ.θ₁]
  exact mul_le_mul_of_nonneg_left h1 hp

theorem p₂_mul_le {ψ : ℝ} (h0 : 0 ≤ ψ) (h1 : ψ ≤ σ.θ₂) :
    0 ≤ (σ.p₂ : ℝ) * ψ ∧ (σ.p₂ : ℝ) * ψ ≤ Real.pi := by
  have hp : (0 : ℝ) ≤ σ.p₂ := Nat.cast_nonneg _
  refine ⟨mul_nonneg hp h0, ?_⟩
  rw [← σ.θ₂_mul, mul_comm σ.θ₂]
  exact mul_le_mul_of_nonneg_left h1 hp

theorem p₃_mul_le {ψ : ℝ} (h0 : 0 ≤ ψ) (h1 : ψ ≤ σ.θ₃) :
    0 ≤ (σ.p₃ : ℝ) * ψ ∧ (σ.p₃ : ℝ) * ψ ≤ Real.pi := by
  have hp : (0 : ℝ) ≤ σ.p₃ := Nat.cast_nonneg _
  refine ⟨mul_nonneg hp h0, ?_⟩
  rw [← σ.θ₃_mul, mul_comm σ.θ₃]
  exact mul_le_mul_of_nonneg_left h1 hp

theorem convex_angle' {s x y : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) (hx : 0 ≤ x ∧ x ≤ Real.pi)
    (hy : 0 ≤ y ∧ y ≤ Real.pi) : 0 ≤ s * x + (1 - s) * y ∧ s * x + (1 - s) * y ≤ Real.pi := by
  constructor <;> nlinarith

theorem validOne_of {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) (h1 : z ≠ σ.vertexOne)
    (h2 : z ≠ σ.vertexTwo) (hd : ‖z - σ.vertexOne‖ ≤ σ.radOne) :
    z ∈ σ.domOne ∧ z ∈ σ.domTwo ∧ 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re ∧
      0 < σ.modOne z + ((σ.bridgeOne z).re - 3 / 2) ∧
      0 < σ.modOne z - ((σ.bridgeTwo z).re - 3 / 2) ∧
      σ.angleOneAtOne z ≤ σ.angleTwoAtOne z := by
  have d1 := σ.triangle_subset_domOne hz h0 h1
  have d2 := σ.triangle_subset_domTwo hz h1 h2
  have r1 := σ.three_halves_lt_re_bridgeOne hz hd
  have r2 := (σ.re_bridgeTwo_mem hz).2
  have hM := σ.modOne_pos z
  exact ⟨d1, d2, σ.psiOne_pos_of_domOne d1, by linarith, by linarith,
    (halfArg_lt_negHalfArg_of_re hM (by linarith) (by linarith)
      (σ.sq_of_bridgeOne_one d1) (σ.sq_of_bridgeTwo_one d2)).le⟩

theorem validTwo_of {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) (h1 : z ≠ σ.vertexOne)
    (h2 : z ≠ σ.vertexTwo) (hd : ‖z - σ.vertexTwo‖ ≤ σ.radTwo) :
    z ∈ σ.domTwo ∧ z ∈ σ.domZero ∧ 0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re ∧
      0 < σ.modTwo z + ((σ.bridgeTwo z).re + 3 / 2) ∧
      0 < σ.modTwo z - ((σ.bridgeZero z).re + 3 / 2) ∧
      σ.angleTwoAtTwo z ≤ σ.angleZeroAtTwo z := by
  have d2 := σ.triangle_subset_domTwo hz h1 h2
  have d0 := σ.triangle_subset_domZero hz h0 h2
  have r2 := (σ.re_bridgeTwo_mem hz).1
  have r0 := σ.re_bridgeZero_lt hz hd
  have hM := σ.modTwo_pos z
  exact ⟨d2, d0, σ.psiTwo_pos_of_domTwo d2, by linarith, by linarith,
    (halfArg_lt_negHalfArg_of_re hM (by linarith) (by linarith)
      (σ.sq_of_bridgeTwo_two d2) (σ.sq_of_bridgeZero_two d0)).le⟩

theorem angleCornerOne_mem {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) (h1 : z ≠ σ.vertexOne)
    (h2 : z ≠ σ.vertexTwo) (hd : ‖z - σ.vertexOne‖ ≤ σ.radOne) :
    0 ≤ σ.angleCornerOne σ.blendStart σ.blendEnd σ.lensWidth σ.switchTop z ∧
      σ.angleCornerOne σ.blendStart σ.blendEnd σ.lensWidth σ.switchTop z ≤ Real.pi := by
  obtain ⟨-, -, -, hp1, hp2, -⟩ := σ.validOne_of hz h0 h1 h2 hd
  have a1 := halfArg_mem_Ico hp1 (σ.im_bridgeOne_nonneg hz)
  have a2 := negHalfArg_mem_Ioc hp2 (σ.im_bridgeTwo_nonneg hz)
  have hψ := σ.psiOne_mem hz h0 h1
  exact convex_mem_angle (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _)
    (σ.p₁_mul_le hψ.1 hψ.2) (convex_angle' (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _)
      ⟨a1.1, a1.2.le⟩ ⟨a2.1.le, a2.2⟩)

theorem angleCornerTwo_mem {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) (h1 : z ≠ σ.vertexOne)
    (h2 : z ≠ σ.vertexTwo) (hd : ‖z - σ.vertexTwo‖ ≤ σ.radTwo) :
    0 ≤ σ.angleCornerTwo σ.blendStart σ.blendEnd σ.lensWidth σ.switchTop z ∧
      σ.angleCornerTwo σ.blendStart σ.blendEnd σ.lensWidth σ.switchTop z ≤ Real.pi := by
  obtain ⟨-, -, -, hp2, hp0, -⟩ := σ.validTwo_of hz h0 h1 h2 hd
  have a2 := halfArg_mem_Ico hp2 (σ.im_bridgeTwo_nonneg hz)
  have a0 := negHalfArg_mem_Ioc hp0 (σ.im_bridgeZero_nonneg hz)
  have hψ := σ.psiTwo_mem hz h1 h2
  have a2' : 0 ≤ σ.angleTwoAtTwo z ∧ σ.angleTwoAtTwo z < Real.pi := a2
  have a0' : 0 < σ.angleZeroAtTwo z ∧ σ.angleZeroAtTwo z ≤ Real.pi := a0
  exact convex_mem_angle (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _)
    (σ.p₂_mul_le hψ.1 hψ.2) (convex_mem_angle (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _)
      ⟨a2'.1, a2'.2.le⟩ ⟨a0'.1.le, a0'.2⟩)

def arcOne (d φ : ℝ) : ℂ :=
  σ.vertexOne + -((d : ℂ) * exp ((σ.θ₃ : ℂ) * I)) * exp ((φ : ℂ) * I)

def arcTwo (d φ : ℝ) : ℂ :=
  σ.vertexTwo + -((d : ℂ) * exp (-((σ.θ₂ : ℂ) * I))) * exp ((φ : ℂ) * I)

theorem rotOne_arcOne (d φ : ℝ) : σ.rotOne (σ.arcOne d φ) = (d : ℂ) * exp ((φ : ℂ) * I) := by
  have e := exp_mul_I_mul_exp_neg σ.θ₃
  rw [rotOne, arcOne, add_sub_cancel_left]
  linear_combination (d : ℂ) * exp ((φ : ℂ) * I) * e

theorem rotTwo_arcTwo (d φ : ℝ) : σ.rotTwo (σ.arcTwo d φ) = (d : ℂ) * exp ((φ : ℂ) * I) := by
  have e := exp_mul_I_mul_exp_neg σ.θ₂
  rw [rotTwo, arcTwo, add_sub_cancel_left]
  linear_combination (d : ℂ) * exp ((φ : ℂ) * I) * e

theorem norm_arcOne {d φ : ℝ} (hd : 0 ≤ d) : ‖σ.arcOne d φ - σ.vertexOne‖ = d := by
  rw [← norm_rotOne, rotOne_arcOne, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd]

theorem norm_arcTwo {d φ : ℝ} (hd : 0 ≤ d) : ‖σ.arcTwo d φ - σ.vertexTwo‖ = d := by
  rw [← norm_rotTwo, rotTwo_arcTwo, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd]

theorem eq_arcOne {z : ℂ} (h : 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re) :
    z = σ.arcOne ‖z - σ.vertexOne‖ (σ.psiOne z) := by
  have hp := halfArg_polar_self (ne_zero_of_norm_add_re_pos h) h
  rw [norm_rotOne] at hp
  have e := exp_mul_I_mul_exp_neg σ.θ₃
  rw [arcOne, psiOne]
  have hr : σ.rotOne z = -(exp (-((σ.θ₃ : ℂ) * I)) * (z - σ.vertexOne)) := rfl
  rw [show -(((‖z - σ.vertexOne‖ : ℝ) : ℂ) * exp ((σ.θ₃ : ℂ) * I)) *
      exp ((discAngle (σ.rotOne z) : ℂ) * I) = -(exp ((σ.θ₃ : ℂ) * I) *
        (((‖z - σ.vertexOne‖ : ℝ) : ℂ) * exp ((discAngle (σ.rotOne z) : ℂ) * I))) by ring,
    ← hp, hr]
  linear_combination (-(z - σ.vertexOne)) * e

theorem eq_arcTwo {z : ℂ} (h : 0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re) :
    z = σ.arcTwo ‖z - σ.vertexTwo‖ (σ.psiTwo z) := by
  have hp := halfArg_polar_self (ne_zero_of_norm_add_re_pos h) h
  rw [norm_rotTwo] at hp
  have e := exp_mul_I_mul_exp_neg σ.θ₂
  rw [arcTwo, psiTwo]
  have hr : σ.rotTwo z = -(exp ((σ.θ₂ : ℂ) * I) * (z - σ.vertexTwo)) := rfl
  rw [show -(((‖z - σ.vertexTwo‖ : ℝ) : ℂ) * exp (-((σ.θ₂ : ℂ) * I))) *
      exp ((discAngle (σ.rotTwo z) : ℂ) * I) = -(exp (-((σ.θ₂ : ℂ) * I)) *
        (((‖z - σ.vertexTwo‖ : ℝ) : ℂ) * exp ((discAngle (σ.rotTwo z) : ℂ) * I))) by ring,
    ← hp, hr]
  linear_combination (-(z - σ.vertexTwo)) * e

theorem arcOne_mem {d φ : ℝ} (hd0 : 0 < d) (hd : d ≤ σ.radOne) (hφ0 : 0 ≤ φ)
    (hφ1 : φ ≤ σ.θ₁) :
    σ.arcOne d φ ∈ σ.triangle ∧ σ.arcOne d φ ≠ 0 ∧ σ.arcOne d φ ≠ σ.vertexOne ∧
      σ.arcOne d φ ≠ σ.vertexTwo := by
  have hn := σ.norm_arcOne (φ := φ) hd0.le
  have hr := σ.rotOne_arcOne d φ
  have hpi := Real.pi_pos
  have h12 := σ.radOne_add_radTwo
  have h13 := σ.radOne_add_radThree
  refine ⟨fun i => ?_, ?_, ?_, ?_⟩
  · fin_cases i
    · have hi := Complex.abs_im_le_norm (σ.arcOne d φ - σ.vertexOne)
      rw [hn, sub_im, vertexOne_im'] at hi
      have := σ.radOne_lt_altitude
      change 0 ≤ (σ.arcOne d φ).im
      linarith [(abs_le.1 hi).1]
    · change 0 ≤ σ.wallSide 1 (σ.arcOne d φ)
      rw [wallSide_one_eq_im_rotOne, hr, im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
      exact mul_nonneg hd0.le (Real.sin_nonneg_of_nonneg_of_le_pi hφ0
        (by linarith [σ.θ₁_le]))
    · change 0 ≤ σ.wallSide 2 (σ.arcOne d φ)
      rw [wallSide_two_eq_rotOne, hr, show exp (-((σ.θ₁ : ℂ) * I)) * ((d : ℂ) *
          exp ((φ : ℂ) * I)) = (d : ℂ) * exp (((φ - σ.θ₁ : ℝ) : ℂ) * I) by
        rw [mul_left_comm, ← Complex.exp_add]; push_cast; ring_nf,
        im_ofReal_mul, Complex.exp_ofReal_mul_I_im, show φ - σ.θ₁ = -(σ.θ₁ - φ) by ring,
        Real.sin_neg]
      have := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith : 0 ≤ σ.θ₁ - φ)
        (by linarith [σ.θ₁_le] : σ.θ₁ - φ ≤ Real.pi)
      nlinarith
  · intro h
    rw [h, zero_sub, norm_neg, norm_vertexOne] at hn
    linarith [σ.radThree_pos]
  · intro h
    rw [h, sub_self, norm_zero] at hn
    linarith
  · intro h
    rw [h, ← norm_neg, neg_sub, norm_vertexOne_sub_vertexTwo] at hn
    linarith [σ.radTwo_pos]

theorem arcTwo_mem {d φ : ℝ} (hd0 : 0 < d) (hd : d ≤ σ.radTwo) (hφ0 : 0 ≤ φ)
    (hφ1 : φ ≤ σ.θ₂) :
    σ.arcTwo d φ ∈ σ.triangle ∧ σ.arcTwo d φ ≠ 0 ∧ σ.arcTwo d φ ≠ σ.vertexOne ∧
      σ.arcTwo d φ ≠ σ.vertexTwo := by
  have hn := σ.norm_arcTwo (φ := φ) hd0.le
  have hr := σ.rotTwo_arcTwo d φ
  have hpi := Real.pi_pos
  have h12 := σ.radOne_add_radTwo
  have h23 := σ.radTwo_add_radThree
  refine ⟨fun i => ?_, ?_, ?_, ?_⟩
  · fin_cases i
    · change 0 ≤ σ.wallSide 0 (σ.arcTwo d φ)
      rw [wallSide_zero_eq_rotTwo, hr, show exp (-((σ.θ₂ : ℂ) * I)) * ((d : ℂ) *
          exp ((φ : ℂ) * I)) = (d : ℂ) * exp (((φ - σ.θ₂ : ℝ) : ℂ) * I) by
        rw [mul_left_comm, ← Complex.exp_add]; push_cast; ring_nf,
        im_ofReal_mul, Complex.exp_ofReal_mul_I_im, show φ - σ.θ₂ = -(σ.θ₂ - φ) by ring,
        Real.sin_neg]
      have := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith : 0 ≤ σ.θ₂ - φ)
        (by linarith [σ.θ₂_le] : σ.θ₂ - φ ≤ Real.pi)
      nlinarith
    · have hi := σ.abs_wallSide_one_sub_le (σ.arcTwo d φ) σ.vertexTwo
      rw [hn, σ.wallSide_one_vertexTwo'] at hi
      have := σ.radTwo_lt_altitude
      change 0 ≤ σ.wallSide 1 (σ.arcTwo d φ)
      linarith [(abs_le.1 hi).1]
    · change 0 ≤ (σ.rotTwo (σ.arcTwo d φ)).im
      rw [hr, im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
      exact mul_nonneg hd0.le (Real.sin_nonneg_of_nonneg_of_le_pi hφ0
        (by linarith [σ.θ₂_le]))
  · intro h
    rw [h, zero_sub, norm_neg, norm_vertexTwo] at hn
    linarith [σ.radThree_pos]
  · intro h
    rw [h, norm_vertexOne_sub_vertexTwo] at hn
    linarith [σ.radOne_pos]
  · intro h
    rw [h, sub_self, norm_zero] at hn
    linarith


theorem strictMono_arcOne {d : ℝ} (hd0 : 0 < d) (hd : d ≤ σ.radOne) :
    StrictMonoOn (fun φ => σ.angleCornerOne σ.blendStart σ.blendEnd σ.lensWidth σ.switchTop
      (σ.arcOne d φ)) (Icc 0 σ.θ₁) := by
  have hβ : σ.lensWidth < σ.switchTop := σ.params.2.2.2.2.2.2.2.2.2.2.1
  have hn : ∀ φ : ℝ, ‖σ.arcOne d φ - σ.vertexOne‖ ≤ σ.radOne := fun φ => by
    rw [σ.norm_arcOne hd0.le]
    exact hd
  refine strictMonoOn_arc (c := σ.vertexOne) (w := -((d : ℂ) * exp ((σ.θ₃ : ℂ) * I)))
    (fun φ hφ => ?_) (fun φ hφ => ?_)
  · obtain ⟨hT, h0, h1, h2⟩ := σ.arcOne_mem hd0 hd hφ.1 hφ.2
    obtain ⟨d1, d2, hψ, hp1, hp2, -⟩ := σ.validOne_of hT h0 h1 h2 (hn φ)
    exact (σ.contDiffAt_angleCornerOne _ _ _ _ d1 d2 hψ hp1 hp2).continuousAt
  · obtain ⟨hT, h0, h1, h2⟩ := σ.arcOne_mem hd0 hd hφ.1.le hφ.2.le
    obtain ⟨d1, d2, hψ, hp1, hp2, hord⟩ := σ.validOne_of hT h0 h1 h2 (hn φ)
    exact σ.exists_hasDerivAt_angleCornerOne_circ hβ d1 d2 hψ hp1 hp2 hord
      (Or.inl (show (σ.rotTwo (σ.arcOne d φ)).re - Real.sin σ.θ₃ ≤ 0 by
        linarith [σ.proj_one_nonneg hT]))

theorem strictMono_arcTwo {d : ℝ} (hd0 : 0 < d) (hd : d ≤ σ.radTwo) :
    StrictMonoOn (fun φ => σ.angleCornerTwo σ.blendStart σ.blendEnd σ.lensWidth σ.switchTop
      (σ.arcTwo d φ)) (Icc 0 σ.θ₂) := by
  have hβ : σ.lensWidth < σ.switchTop := σ.params.2.2.2.2.2.2.2.2.2.2.1
  have hn : ∀ φ : ℝ, ‖σ.arcTwo d φ - σ.vertexTwo‖ ≤ σ.radTwo := fun φ => by
    rw [σ.norm_arcTwo hd0.le]
    exact hd
  refine strictMonoOn_arc (c := σ.vertexTwo) (w := -((d : ℂ) * exp (-((σ.θ₂ : ℂ) * I))))
    (fun φ hφ => ?_) (fun φ hφ => ?_)
  · obtain ⟨hT, h0, h1, h2⟩ := σ.arcTwo_mem hd0 hd hφ.1 hφ.2
    obtain ⟨d2, d0, hψ, hp2, hp0, -⟩ := σ.validTwo_of hT h0 h1 h2 (hn φ)
    exact (σ.contDiffAt_angleCornerTwo _ _ _ _ d2 d0 hψ hp2 hp0).continuousAt
  · obtain ⟨hT, h0, h1, h2⟩ := σ.arcTwo_mem hd0 hd hφ.1.le hφ.2.le
    obtain ⟨d2, d0, hψ, hp2, hp0, hord⟩ := σ.validTwo_of hT h0 h1 h2 (hn φ)
    exact σ.exists_hasDerivAt_angleCornerTwo_circ hβ d2 d0 hψ hp2 hp0 hord
      (Or.inl (σ.proj_two_nonneg hT))

theorem ne_vertexTwo_of_regionOne {z : ℂ} (hz : z ∈ σ.regionOne) : z ≠ σ.vertexTwo := by
  intro hzv
  have := (σ.far_of_cornerOne hz.2).1
  rw [hzv, sub_self, norm_zero] at this
  linarith [σ.radTwo_pos, σ.cornerShrink_pos]

theorem ne_vertexOne_of_regionTwo {z : ℂ} (hz : z ∈ σ.regionTwo) : z ≠ σ.vertexOne := by
  intro hzv
  have := (σ.far_of_cornerTwo hz.2).1
  rw [hzv, sub_self, norm_zero] at this
  linarith [σ.radOne_pos, σ.cornerShrink_pos]

theorem injOn_regionOne : InjOn σ.preFold σ.regionOne := by
  intro z hz w hw h
  have nz := σ.norm_preFold_regionOne hz
  have nw := σ.norm_preFold_regionOne hw
  rw [h, nw] at nz
  have hd : ‖w - σ.vertexOne‖ = ‖z - σ.vertexOne‖ :=
    σ.strictMono_innerOne.injOn (norm_nonneg _) (norm_nonneg _) nz
  rcases (norm_nonneg (z - σ.vertexOne)).eq_or_lt with h0 | hpos
  · have hz1 : z = σ.vertexOne := by
      rw [← sub_eq_zero, ← norm_eq_zero]
      exact h0.symm
    have hw1 : w = σ.vertexOne := by
      rw [← sub_eq_zero, ← norm_eq_zero, hd]
      exact h0.symm
    rw [hz1, hw1]
  · have hz0 := σ.ne_zero_of_regionOne hz
    have hw0 := σ.ne_zero_of_regionOne hw
    have hz1 : z ≠ σ.vertexOne := ne_of_norm_pos hpos le_rfl
    have hw1 : w ≠ σ.vertexOne := ne_of_norm_pos hpos hd.ge
    have hz2 := σ.ne_vertexTwo_of_regionOne hz
    have hw2 := σ.ne_vertexTwo_of_regionOne hw
    have hdr : ‖z - σ.vertexOne‖ ≤ σ.radOne := by linarith [hz.2, σ.cornerShrink_pos]
    have hdr' : ‖w - σ.vertexOne‖ ≤ σ.radOne := by linarith [hw.2, σ.cornerShrink_pos]
    rw [σ.preFold_regionOne hz, σ.preFold_regionOne hw, foldCornerOne,
      cornerOne, cornerOne, hd] at h
    have hS : (innerRadial σ.p₁ σ.blendStart σ.blendEnd σ.radOne ‖z - σ.vertexOne‖ : ℂ) ≠ 0 :=
      ofReal_ne_zero.2 (innerRadial_pos σ.radOne_lt_one hpos).ne'
    have hΘ := angle_eq_of_exp_eq_mem (mul_left_cancel₀ hS (add_left_cancel h))
      (σ.angleCornerOne_mem hz.1 hz0 hz1 hz2 hdr) (σ.angleCornerOne_mem hw.1 hw0 hw1 hw2 hdr')
    have hψz := σ.psiOne_mem hz.1 hz0 hz1
    have hψw := σ.psiOne_mem hw.1 hw0 hw1
    have pz := σ.eq_arcOne (σ.validOne_of hz.1 hz0 hz1 hz2 hdr).2.2.1
    have pw := σ.eq_arcOne (σ.validOne_of hw.1 hw0 hw1 hw2 hdr').2.2.1
    rw [hd] at pw
    have he : σ.psiOne z = σ.psiOne w := (σ.strictMono_arcOne hpos hdr).injOn
      ⟨hψz.1, hψz.2⟩ ⟨hψw.1, hψw.2⟩ (by
        rw [← pz, ← pw]
        exact hΘ)
    calc z = σ.arcOne ‖z - σ.vertexOne‖ (σ.psiOne z) := pz
      _ = σ.arcOne ‖z - σ.vertexOne‖ (σ.psiOne w) := by rw [he]
      _ = w := pw.symm

theorem injOn_regionTwo : InjOn σ.preFold σ.regionTwo := by
  intro z hz w hw h
  have nz := σ.norm_preFold_regionTwo hz
  have nw := σ.norm_preFold_regionTwo hw
  rw [h, nw] at nz
  have hd : ‖w - σ.vertexTwo‖ = ‖z - σ.vertexTwo‖ :=
    σ.strictMono_innerTwo.injOn (norm_nonneg _) (norm_nonneg _) nz
  rcases (norm_nonneg (z - σ.vertexTwo)).eq_or_lt with h0 | hpos
  · have hz2 : z = σ.vertexTwo := by
      rw [← sub_eq_zero, ← norm_eq_zero]
      exact h0.symm
    have hw2 : w = σ.vertexTwo := by
      rw [← sub_eq_zero, ← norm_eq_zero, hd]
      exact h0.symm
    rw [hz2, hw2]
  · have hz0 := σ.ne_zero_of_regionTwo hz
    have hw0 := σ.ne_zero_of_regionTwo hw
    have hz2 : z ≠ σ.vertexTwo := ne_of_norm_pos hpos le_rfl
    have hw2 : w ≠ σ.vertexTwo := ne_of_norm_pos hpos hd.ge
    have hz1 := σ.ne_vertexOne_of_regionTwo hz
    have hw1 := σ.ne_vertexOne_of_regionTwo hw
    have hdr : ‖z - σ.vertexTwo‖ ≤ σ.radTwo := by linarith [hz.2, σ.cornerShrink_pos]
    have hdr' : ‖w - σ.vertexTwo‖ ≤ σ.radTwo := by linarith [hw.2, σ.cornerShrink_pos]
    rw [σ.preFold_regionTwo hz, σ.preFold_regionTwo hw, foldCornerTwo,
      cornerTwo, cornerTwo, hd] at h
    have hS : (innerRadial σ.p₂ σ.blendStart σ.blendEnd σ.radTwo ‖z - σ.vertexTwo‖ : ℂ) ≠ 0 :=
      ofReal_ne_zero.2 (innerRadial_pos σ.radTwo_lt_one hpos).ne'
    have hΘ := angle_eq_of_exp_eq_mem (mul_left_cancel₀ hS (add_left_cancel h))
      (σ.angleCornerTwo_mem hz.1 hz0 hz1 hz2 hdr) (σ.angleCornerTwo_mem hw.1 hw0 hw1 hw2 hdr')
    have hψz := σ.psiTwo_mem hz.1 hz1 hz2
    have hψw := σ.psiTwo_mem hw.1 hw1 hw2
    have pz := σ.eq_arcTwo (σ.validTwo_of hz.1 hz0 hz1 hz2 hdr).2.2.1
    have pw := σ.eq_arcTwo (σ.validTwo_of hw.1 hw0 hw1 hw2 hdr').2.2.1
    rw [hd] at pw
    have he : σ.psiTwo z = σ.psiTwo w := (σ.strictMono_arcTwo hpos hdr).injOn
      ⟨hψz.1, hψz.2⟩ ⟨hψw.1, hψw.2⟩ (by
        rw [← pz, ← pw]
        exact hΘ)
    calc z = σ.arcTwo ‖z - σ.vertexTwo‖ (σ.psiTwo z) := pz
      _ = σ.arcTwo ‖z - σ.vertexTwo‖ (σ.psiTwo w) := by rw [he]
      _ = w := pw.symm


def arcThree (r φ : ℝ) : ℂ := 0 + (r : ℂ) * exp ((φ : ℂ) * I)

theorem eq_arcThree {z : ℂ} (h : 0 < ‖z‖ + z.re) : z = arcThree ‖z‖ (discAngle z) := by
  rw [arcThree, zero_add]
  exact halfArg_polar_self (ne_zero_of_norm_add_re_pos h) h

theorem re_rotOne (z : ℂ) :
    (σ.rotOne z).re = Real.sin σ.θ₂ - (exp (-((σ.θ₃ : ℂ) * I)) * z).re := by
  have hv : exp (-((σ.θ₃ : ℂ) * I)) * σ.vertexOne = (Real.sin σ.θ₂ : ℂ) := by
    rw [vertexOne, mul_left_comm, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  rw [rotOne, mul_sub, hv, neg_sub, sub_re, ofReal_re]

theorem re_bridgeOne_pos_of {z : ℂ} (hz : z ∈ σ.domOne) (h : σ.modOne z ≤ σ.modThree z) :
    0 < (σ.bridgeOne z).re := by
  have hA := σ.modThree_pos hz.2.2
  have hB := σ.modOne_pos z
  rw [bridgeOne, twoCircle_re]
  have : 0 < σ.modThree z ^ 2 - σ.modOne z ^ 2 + (3 / 2 - 0) ^ 2 := by nlinarith
  have h2 : (0 : ℝ) < 2 * (3 / 2 - 0) := by norm_num
  have := div_pos this h2
  linarith

theorem re_bridgeZero_neg_of {z : ℂ} (hz : z ∈ σ.domZero) (h : σ.modTwo z ≤ σ.modThree z) :
    (σ.bridgeZero z).re < 0 := by
  have hA := σ.modThree_pos hz.2.2
  have hB := σ.modTwo_pos z
  rw [bridgeZero, twoCircle_re]
  have : 0 < σ.modThree z ^ 2 - σ.modTwo z ^ 2 + (-(3 / 2) - 0) ^ 2 := by nlinarith
  have h2 : 2 * (-(3 / 2) - 0 : ℝ) < 0 := by norm_num
  have := div_neg_of_pos_of_neg this h2
  linarith

theorem valid_arc_three {r φ : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hφ0 : 0 < φ) (hφ1 : φ < σ.θ₃) :
    arcThree r φ ∈ σ.domOne ∧ arcThree r φ ∈ σ.domZero ∧
      0 < ‖arcThree r φ‖ + (arcThree r φ).re ∧
      0 < σ.modThree (arcThree r φ) + (σ.bridgeOne (arcThree r φ)).re ∧
      0 < σ.modThree (arcThree r φ) - (σ.bridgeZero (arcThree r φ)).re ∧
      σ.angleOneAtThree (arcThree r φ) ≤ σ.angleZeroAtThree (arcThree r φ) ∧
      0 ≤ σ.wallSide 0 (arcThree r φ) ∧ 0 ≤ σ.wallSide 1 (arcThree r φ) := by
  set z := arcThree r φ with hzdef
  have hpi := Real.pi_pos
  have hθ := σ.θ₃_le
  have hn : ‖z‖ = r := by
    rw [hzdef, arcThree, zero_add, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  have him : z.im = r * Real.sin φ := by
    rw [hzdef, arcThree, zero_add, im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hw1 : σ.wallSide 1 z = r * Real.sin (σ.θ₃ - φ) := by
    rw [wallSide_one_eq_rotThree, hzdef, arcThree, zero_add,
      show exp (-((σ.θ₃ : ℂ) * I)) * ((r : ℂ) * exp ((φ : ℂ) * I)) =
        (r : ℂ) * exp (((φ - σ.θ₃ : ℝ) : ℂ) * I) by
      rw [mul_left_comm, ← Complex.exp_add]; push_cast; ring_nf,
      im_ofReal_mul, Complex.exp_ofReal_mul_I_im, show φ - σ.θ₃ = -(σ.θ₃ - φ) by ring,
      Real.sin_neg]
    ring
  have hs1 : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ0 (by linarith)
  have hs2 : 0 < Real.sin (σ.θ₃ - φ) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have himp : 0 < z.im := by rw [him]; positivity
  have hw1p : 0 < σ.wallSide 1 z := by rw [hw1]; positivity
  have hz2 : ‖z‖ < 2 := by linarith
  have d1 : z ∈ σ.domOne := by
    refine ⟨?_, ?_, hz2⟩
    · have hne : (exp (-((σ.θ₃ : ℂ) * I)) * z).im ≠ 0 := by
        rw [wallSide_one_eq_rotThree] at hw1p
        linarith
      have := norm_add_re_pos_of_im_ne hne
      have hnorm : ‖exp (-((σ.θ₃ : ℂ) * I)) * z‖ = ‖z‖ := by
        rw [norm_mul, show -((σ.θ₃ : ℂ) * I) = ((-σ.θ₃ : ℝ) : ℂ) * I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, one_mul]
      rwa [hnorm] at this
    · have hne : (σ.rotOne z).im ≠ 0 := by
        rw [← wallSide_one_eq_im_rotOne]
        exact hw1p.ne'
      have := norm_add_re_pos_of_im_ne hne
      rwa [norm_rotOne, re_rotOne] at this
  have d0 : z ∈ σ.domZero := by
    refine ⟨norm_add_re_pos_of_im_ne himp.ne', ?_, hz2⟩
    have hne : (σ.vertexTwo - z).im ≠ 0 := by
      rw [sub_im, vertexTwo_im']
      linarith
    have := norm_add_re_pos_of_im_ne hne
    rwa [← norm_neg, neg_sub, sub_re, vertexTwo_re'] at this
  have hM3 : 13 / 5 ≤ σ.modThree z := by
    rw [modThree_eq, hn]
    unfold profileSlope
    linarith [σ.radThree_pos]
  have hd1 : ‖z - σ.vertexOne‖ ≤ 2 := by
    have := norm_sub_le z σ.vertexOne
    rw [norm_vertexOne] at this
    linarith [Real.sin_le_one σ.θ₂]
  have hd2 : ‖z - σ.vertexTwo‖ ≤ 2 := by
    have := norm_sub_le z σ.vertexTwo
    rw [norm_vertexTwo] at this
    linarith [Real.sin_le_one σ.θ₁]
  have hM1 : σ.modOne z ≤ σ.modThree z := by
    rw [modOne_eq]
    unfold profileSlope at *
    linarith [σ.radOne_pos]
  have hM2 : σ.modTwo z ≤ σ.modThree z := by
    rw [modTwo_eq]
    unfold profileSlope at *
    linarith [σ.radTwo_pos]
  have r1 := σ.re_bridgeOne_pos_of d1 hM1
  have r0 := σ.re_bridgeZero_neg_of d0 hM2
  have hM := σ.modThree_pos d1.2.2
  exact ⟨d1, d0, norm_add_re_pos_of_im_ne himp.ne', by linarith, by linarith,
    (halfArg_lt_negHalfArg_of_re hM r1 r0 (σ.sq_of_bridgeOne_three d1)
      (σ.sq_of_bridgeZero_three d0)).le, himp.le, hw1p.le⟩

theorem contAt_angleThree_of_mem {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (h1 : z ≠ σ.vertexOne) (h2 : z ≠ σ.vertexTwo) :
    ContinuousAt (σ.angleCornerThree σ.outerBlendStart σ.outerBlendEnd 1 σ.cornerShrink) z := by
  have d1 := σ.triangle_subset_domOne hz h0 h1
  have d0 := σ.triangle_subset_domZero hz h0 h2
  have hM := σ.modThree_pos d1.2.2
  exact (σ.contDiffAt_angleCornerThree _ _ _ _ d1 d0 (σ.norm_pos_add_re hz h0)
    (by linarith [σ.re_bridgeOne_pos hz]) (by linarith [σ.re_bridgeZero_neg hz])).continuousAt

theorem angleCornerThree_mem {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (h1 : z ≠ σ.vertexOne) (h2 : z ≠ σ.vertexTwo) :
    0 ≤ σ.angleCornerThree σ.outerBlendStart σ.outerBlendEnd 1 σ.cornerShrink z ∧
      σ.angleCornerThree σ.outerBlendStart σ.outerBlendEnd 1 σ.cornerShrink z ≤ Real.pi := by
  obtain ⟨a0, a10, a1π⟩ := σ.angles_three hz h0 h1 h2
  have hψ := σ.discAngle_mem hz h0
  have hp := σ.p₃_mul_le hψ.1 hψ.2.1
  exact convex_mem_angle (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _)
    ⟨by linarith, by linarith⟩ (convex_mem_angle (coneStep_nonneg _ _ _)
      (coneStep_le_one _ _ _) ⟨by linarith, a1π⟩ ⟨a0, by linarith⟩)

theorem angleThree_lt {r ψ ψ' : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (h0 : 0 ≤ ψ) (hψ : ψ < ψ')
    (h1 : ψ' ≤ σ.θ₃)
    (hc : ContinuousAt (σ.angleCornerThree σ.outerBlendStart σ.outerBlendEnd 1 σ.cornerShrink)
      (arcThree r ψ))
    (hc' : ContinuousAt (σ.angleCornerThree σ.outerBlendStart σ.outerBlendEnd 1 σ.cornerShrink)
      (arcThree r ψ')) :
    σ.angleCornerThree σ.outerBlendStart σ.outerBlendEnd 1 σ.cornerShrink (arcThree r ψ') <
      σ.angleCornerThree σ.outerBlendStart σ.outerBlendEnd 1 σ.cornerShrink
        (arcThree r ψ) := by
  have hδ := σ.cornerShrink_pos
  have hanti : StrictAntiOn (fun φ => σ.angleCornerThree σ.outerBlendStart σ.outerBlendEnd 1
      σ.cornerShrink (arcThree r φ)) (Icc ψ ψ') := by
    refine strictAntiOn_arc (c := 0) (w := (r : ℂ)) (fun φ hφ => ?_) (fun φ hφ => ?_)
    · rcases eq_or_lt_of_le hφ.1 with e | e
      · rw [← e]
        exact hc
      rcases eq_or_lt_of_le hφ.2 with e' | e'
      · rw [e']
        exact hc'
      obtain ⟨d1, d0, hψ0, hp1, hp0, -, -, -⟩ :=
        σ.valid_arc_three (φ := φ) hr0 hr1 (by linarith) (by linarith)
      exact (σ.contDiffAt_angleCornerThree _ _ _ _ d1 d0 hψ0 hp1 hp0).continuousAt
    · obtain ⟨d1, d0, hψ0, hp1, hp0, hord, w0, w1⟩ :=
        σ.valid_arc_three (φ := φ) hr0 hr1 (by linarith [hφ.1]) (by linarith [hφ.2])
      exact σ.exists_hasDerivAt_angleCornerThree_circ one_pos hδ d1 d0 hψ0 hp1 hp0 hord
        (Or.inl ⟨w0, w1⟩)
  exact hanti ⟨le_rfl, hψ.le⟩ ⟨hψ.le, le_rfl⟩ hψ

theorem facts_regionThree {z : ℂ} (hz : z ∈ σ.regionThree) :
    z ∈ σ.triangle ∧ z ≠ 0 ∧ z ≠ σ.vertexOne ∧ z ≠ σ.vertexTwo :=
  ⟨hz.1, hz.2.1, ne_of_norm_pos σ.radOne_sub_pos hz.2.2.1,
    ne_of_norm_pos σ.radTwo_sub_pos hz.2.2.2.1⟩

theorem injOn_regionThree : InjOn σ.preFold σ.regionThree := by
  intro z hz w hw h
  have nz := σ.norm_preFold_regionThree hz
  have nw := σ.norm_preFold_regionThree hw
  rw [h, nw] at nz
  have hr : ‖w‖ = ‖z‖ := σ.strictAnti_outer.injOn (norm_nonneg _) (norm_nonneg _) nz
  obtain ⟨hT, h0, h1, h2⟩ := σ.facts_regionThree hz
  obtain ⟨hT', h0', h1', h2'⟩ := σ.facts_regionThree hw
  have hS : (outerRadial σ.p₃ σ.outerBlendStart σ.outerBlendEnd σ.radThree ‖z‖ : ℂ) ≠ 0 :=
    ofReal_ne_zero.2 (by linarith [σ.outerRadial_gt hT])
  rw [σ.preFold_regionThree hz, σ.preFold_regionThree hw, foldCornerThree, cornerThree,
    cornerThree, hr] at h
  have hΘ := angle_eq_of_exp_eq_mem (mul_left_cancel₀ hS (add_left_cancel h))
    (σ.angleCornerThree_mem hT h0 h1 h2) (σ.angleCornerThree_mem hT' h0' h1' h2')
  have pz := eq_arcThree (σ.norm_pos_add_re hT h0)
  have pw := eq_arcThree (σ.norm_pos_add_re hT' h0')
  rw [hr] at pw
  have ψz := σ.discAngle_mem hT h0
  have ψw := σ.discAngle_mem hT' h0'
  have hr0 : 0 < ‖z‖ := norm_pos_iff.2 h0
  have hr1 := σ.norm_le_one_of_mem hT
  have cz := σ.contAt_angleThree_of_mem hT h0 h1 h2
  have cw := σ.contAt_angleThree_of_mem hT' h0' h1' h2'
  rw [pz] at cz
  rw [pw] at cw
  rcases lt_trichotomy (discAngle z) (discAngle w) with hlt | heq | hgt
  · exfalso
    have := σ.angleThree_lt hr0 hr1 ψz.1 hlt ψw.2.1 cz cw
    rw [← pz, ← pw] at this
    linarith
  · calc z = arcThree ‖z‖ (discAngle z) := pz
      _ = arcThree ‖z‖ (discAngle w) := by rw [heq]
      _ = w := pw.symm
  · exfalso
    have := σ.angleThree_lt hr0 hr1 ψw.1 hgt ψz.2.1 cw cz
    rw [← pz, ← pw] at this
    linarith

theorem three_le_norm_sub_add (u : ℂ) : 3 ≤ ‖u - 3 / 2‖ + ‖u + 3 / 2‖ := by
  have h := norm_sub_le (u + 3 / 2) (u - 3 / 2)
  rw [show u + 3 / 2 - (u - 3 / 2) = ((3 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3)] at h
  linarith

theorem injOn_preFold : InjOn σ.preFold (σ.triangle \ {0}) := by
  intro z hz w hw h
  have hk := σ.kappa_delta_pos
  have hk' := σ.kappa_delta_lt
  have t := three_le_norm_sub_add (σ.preFold w)
  rcases σ.mem_regions hz.1 hz.2 with a | a | a | a <;>
    rcases σ.mem_regions hw.1 hw.2 with b | b | b | b
  · exact σ.injOn_regionOne a b h
  · have := σ.image_regionOne a
    rw [h] at this
    linarith [σ.image_regionTwo b]
  · have := σ.image_regionOne a
    rw [h] at this
    linarith [σ.image_regionLens b]
  · have := σ.image_regionOne a
    rw [h] at this
    linarith [σ.image_regionThree b]
  · have := σ.image_regionTwo a
    rw [h] at this
    linarith [σ.image_regionOne b]
  · exact σ.injOn_regionTwo a b h
  · have := σ.image_regionTwo a
    rw [h] at this
    linarith [σ.image_regionLens b]
  · have := σ.image_regionTwo a
    rw [h] at this
    linarith [σ.image_regionThree b]
  · have := σ.image_regionLens a
    rw [h] at this
    linarith [σ.image_regionOne b]
  · have := σ.image_regionLens a
    rw [h] at this
    linarith [σ.image_regionTwo b]
  · exact σ.injOn_regionLens a b h
  · have := σ.image_regionLens a
    rw [h] at this
    linarith [σ.image_regionThree b]
  · have := σ.image_regionThree a
    rw [h] at this
    linarith [σ.image_regionOne b]
  · have := σ.image_regionThree a
    rw [h] at this
    linarith [σ.image_regionTwo b]
  · have := σ.image_regionThree a
    rw [h] at this
    linarith [σ.image_regionLens b]
  · exact σ.injOn_regionThree a b h

end EuclidShape

end GC.Seifert
