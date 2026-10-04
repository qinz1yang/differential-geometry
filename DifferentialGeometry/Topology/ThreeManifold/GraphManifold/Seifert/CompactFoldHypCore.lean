import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldHypWalls
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldEuclidCore
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldHypLayout

/-!
# The hyperbolic compact fold with its core replaced

Lane CF-H3w, tier 3, curvature `-1` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §6, review 23 §6). Template:
`CompactFoldEuclidCore`.

**Image bounds.** Every branch of `hypPreFold` is `c + S e^{iΘ}` with `c ∈ {0, ±3/2}`, a radius
below the convex-combination bounds (`hypInnerRadial_lt`, `hypOuterRadial_lt`) and an angle that
is a convex combination of angles in `[0, π]`, in `(0, π)` at interior points
(`discAngle_mem_sector_open`, `im_pow_of_sector`); the apex models are `±3/2 + w^p/2` with
`w` in its sector, the outer germ is `cornerThree` with radial weight zero. Hence
`‖hypPreFold‖ < 7/2` and `Im ≥ 0` on `T \ {0}`, `Im > 0` on the open triangle
(`hypPreFold_image`, from `apexOne_image`, `apexTwo_image`, `cornerOne_image`, …).

**Star shape in a centred chart.** In the disc model the triangle is not Euclidean-star-shaped
about points near wall 2 (the geodesic bows inward), so the core is a hyperbolic disc
`{‖mob p z‖ < t}` and the argument runs in the chart `Z = mob p z`. Each side function has the
form `hpForm α u z = α(1 + |z|²) + Re(u z)` (`wallSide_eq_hpForm`); this form is preserved by
`mobInv p` up to the factor `|1 + p̄ Z|²`, with new constant term `hpForm α u p`
(`hpForm_mobInv`), and on a segment from `0` it is at least `A(1 - s)(1 - s|Z|²)`
(`hpForm_smul_ge`). So for `p` in the open triangle the geodesic segments
`s ↦ mobInv p (s · mob p z)` stay in `T`, in its interior for `s < 1`
(`mobInv_smul_mem_triangle`), and the part of `T \ {0}` outside the core is preconnected
(`isPreconnected_hypCoreOut`: geodesic segments to a hyperbolic circle about `p`).

**Core replacement.** `exists_hypFoldCore` is curvature-generic in its data: a map `E` smooth on
an open good set `G` with positive Jacobian off `v₁, v₂`, injective on `T \ {0}`, with the image
bounds above and the outer germ near `v₃ = 0`; a core `(p, t, m)` whose `m`-neighbourhood lies in
the open triangle and outside of whose `(t - m)`-disc `T \ {0}` lies in `G`. K16f's
`exists_core_replacement` applied to `E ∘ mobInv p` on the round annulus `t - m < |Z| < t + m`
gives `Q`; `hout` uses the preconnected set `E(T \ {0} outside the core)` joined at a point of
wall 0 near `v₃` (where `|E| = 7/2 - x^{p₃}/2` exceeds `max |E|` on the core circle) to a ray.
The fold `F = Q ∘ mob p` on the core, `E` elsewhere, is smooth with positive Jacobian off
`v₁, v₂` on an open `U ⊇ T \ {0}`, equal to `E` outside the core, injective on `T \ {0}` and maps
it into `basePlusSeven`. On a wall neighbourhood outside the core the reflection identity of
`hypPreFold` passes to `F` (`hypFold_refl_of_far`).

**Instantiation at CF-H3's layout** (`CompactFoldHypLayout`): with `E = hypPreFold σ (hypLayout σ)`
and the core `(hypCoreCenter σ, hypCoreRadius σ, hypCoreMargin σ)` the image bounds and the outer
germ on `T` near `v₃` (`hypPreFold_eq_outer`) are discharged, the wall neighbourhoods avoid the
core (`hypWallNbhd_far_core`, from `core_separation`), and `exists_hypFoldCore_layout` keeps as
hypotheses only the good set (open, in the disc, covering `T \ {0}` outside the inner core disc,
`E` smooth with positive Jacobian off `v₁, v₂` there) and the injectivity of `E` on `T \ {0}`;
it adds `F ∘ refl i = conj ∘ F` on `hypWallNbhd σ (hypLayout σ) i`.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Set Metric
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace HypFold

def hpForm (α : ℝ) (u z : ℂ) : ℝ := α * (1 + normSq z) + (u * z).re

theorem hpForm_mobInv (α : ℝ) (u : ℂ) {p Z : ℂ} (hD : 1 + conj p * Z ≠ 0) :
    hpForm α u (mobInv p Z) * normSq (1 + conj p * Z) =
      hpForm (hpForm α u p) (4 * α * conj p + u + conj u * conj p ^ 2) Z := by
  set D := 1 + conj p * Z with hDdef
  have hz : mobInv p Z * D = Z + p := by
    rw [mobInv, div_mul_cancel₀ _ hD]
  have e1 : normSq (mobInv p Z) * normSq D = normSq (Z + p) := by
    rw [← normSq_mul, hz]
  have e2 : (u * mobInv p Z).re * normSq D = (u * (Z + p) * conj D).re := by
    rw [← re_mul_ofReal, ← Complex.mul_conj, ← hz]
    ring_nf
  have e3 : hpForm α u (mobInv p Z) * normSq D =
      α * (normSq D + normSq (Z + p)) + (u * (Z + p) * conj D).re := by
    rw [hpForm, add_mul, ← e2, ← e1]
    ring
  rw [e3, hDdef, hpForm, hpForm]
  simp only [normSq_apply, mul_re, mul_im, add_re, add_im, conj_re, conj_im, one_re, one_im,
    pow_two, re_ofNat, im_ofNat, ofReal_re, ofReal_im]
  ring

theorem hpForm_smul_ge {A : ℝ} {u Z : ℂ} (h1 : 0 ≤ hpForm A u Z) {s : ℝ} (hs0 : 0 ≤ s) :
    A * (1 - s) * (1 - s * normSq Z) ≤ hpForm A u ((s : ℂ) * Z) := by
  have e : hpForm A u ((s : ℂ) * Z) = A * (1 + s ^ 2 * normSq Z) + s * (u * Z).re := by
    rw [hpForm, normSq_mul, normSq_ofReal, show u * ((s : ℂ) * Z) = (s : ℂ) * (u * Z) by ring,
      re_ofReal_mul]
    ring
  rw [e]
  unfold hpForm at h1
  nlinarith [mul_nonneg hs0 h1]

variable {σ : CompactShape}

section Star

variable (h : σ.curv = .hyperbolic)
include h

theorem wallSide_eq_hpForm (i : Fin 3) : ∃ α : ℝ, ∃ u : ℂ, ∀ z, σ.wallSide i z = hpForm α u z := by
  fin_cases i
  · refine ⟨0, -I, fun z => ?_⟩
    change z.im = _
    simp [hpForm]
  · refine ⟨0, (Real.sin σ.θ₃ : ℂ) + (Real.cos σ.θ₃ : ℂ) * I, fun z => ?_⟩
    change σ.wallSide 1 z = _
    rw [wallSide_one_apply, hpForm]
    simp only [mul_re, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im, mul_im]
    ring
  · refine ⟨sideTwoThree σ * Real.sin σ.θ₂, (-((1 + sideTwoThree σ ^ 2) * Real.sin σ.θ₂) : ℝ) +
      ((1 - sideTwoThree σ ^ 2) * Real.cos σ.θ₂ : ℝ) * I, fun z => ?_⟩
    change σ.wallSide 2 z = _
    rw [wallSide_two_apply h, hpForm]
    simp only [mul_re, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im, mul_im]
    ring

theorem wallSide_mobInv_smul (i : Fin 3) {p z : ℂ} (hp : ‖p‖ < 1) (hpi : 0 < σ.wallSide i p)
    (hz : ‖z‖ < 1) (hzi : 0 ≤ σ.wallSide i z) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ σ.wallSide i (mobInv p ((s : ℂ) * mob p z)) ∧
      (s < 1 → 0 < σ.wallSide i (mobInv p ((s : ℂ) * mob p z))) := by
  obtain ⟨α, u, hw⟩ := wallSide_eq_hpForm h i
  set Z := mob p z with hZ
  have hZ1 : ‖Z‖ < 1 := norm_mob_lt_one hp hz
  have hsZ : ‖(s : ℂ) * Z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
    nlinarith [norm_nonneg Z]
  have hD : 1 + conj p * Z ≠ 0 := one_add_conj_mul_ne_zero hp hZ1
  have hDs : 1 + conj p * ((s : ℂ) * Z) ≠ 0 := one_add_conj_mul_ne_zero hp hsZ
  have hzz : mobInv p Z = z := mobInv_mob (normSq_lt_one_of_norm_lt hp).ne
    (one_sub_conj_mul_ne_zero hp hz)
  have e0 := hpForm_mobInv α u hD
  rw [hzz, ← hw] at e0
  have hA : 0 < hpForm α u p := by rw [← hw]; exact hpi
  have hnn : 0 ≤ hpForm (hpForm α u p) (4 * α * conj p + u + conj u * conj p ^ 2) Z := by
    rw [← e0]
    exact mul_nonneg hzi (normSq_nonneg _)
  have es := hpForm_mobInv α u hDs
  rw [← hw] at es
  have hge := hpForm_smul_ge hnn hs0
  have hN : 0 < normSq (1 + conj p * ((s : ℂ) * Z)) := normSq_pos.2 hDs
  have hR : normSq Z < 1 := normSq_lt_one_of_norm_lt hZ1
  have hsR : s * normSq Z < 1 := by nlinarith [normSq_nonneg Z]
  constructor
  · have : 0 ≤ σ.wallSide i (mobInv p ((s : ℂ) * Z)) * normSq (1 + conj p * ((s : ℂ) * Z)) := by
      rw [es]
      refine le_trans ?_ hge
      have := mul_nonneg (mul_nonneg hA.le (sub_nonneg.2 hs1)) (sub_nonneg.2 hsR.le)
      exact this
    exact nonneg_of_mul_nonneg_left this hN
  · intro hs
    have : 0 < σ.wallSide i (mobInv p ((s : ℂ) * Z)) * normSq (1 + conj p * ((s : ℂ) * Z)) := by
      rw [es]
      refine lt_of_lt_of_le ?_ hge
      exact mul_pos (mul_pos hA (sub_pos.2 hs)) (sub_pos.2 hsR)
    exact pos_of_mul_pos_left this hN.le

theorem mobInv_smul_mem_triangle {p z : ℂ} (hp : ‖p‖ < 1) (hpi : ∀ i, 0 < σ.wallSide i p)
    (hz : z ∈ σ.triangle) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    mobInv p ((s : ℂ) * mob p z) ∈ σ.triangle ∧
      (s < 1 → ∀ i, 0 < σ.wallSide i (mobInv p ((s : ℂ) * mob p z))) := by
  have hz1 := norm_lt_one_of_mem h hz
  have hZ1 : ‖mob p z‖ < 1 := norm_mob_lt_one hp hz1
  have hsZ : ‖(s : ℂ) * mob p z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
    nlinarith [norm_nonneg (mob p z)]
  refine ⟨⟨?_, fun i => (wallSide_mobInv_smul h i hp (hpi i) hz1 (hz.2 i) hs0 hs1).1⟩,
    fun hs i => (wallSide_mobInv_smul h i hp (hpi i) hz1 (hz.2 i) hs0 hs1).2 hs⟩
  rw [CompactShape.plane_hyp h, mem_ball_zero_iff]
  exact norm_mobInv_lt_one hp hsZ

omit h in
theorem ne_zero_of_wallSide_pos {z : ℂ} (hz : ∀ i, 0 < σ.wallSide i z) : z ≠ 0 := by
  rintro rfl
  have := hz 0
  change 0 < (0 : ℂ).im at this
  rw [zero_im] at this
  exact lt_irrefl 0 this

omit h in
theorem continuousAt_mobInv {p Z : ℂ} (hp : ‖p‖ < 1) (hZ : ‖Z‖ < 1) :
    ContinuousAt (mobInv p) Z := by
  have e : mobInv p = mob (-p) := funext (mobInv_eq_mob_neg p)
  rw [e]
  apply (contDiffAt_mob _).continuousAt
  rw [map_neg, neg_mul, sub_neg_eq_add]
  exact one_add_conj_mul_ne_zero hp hZ

omit h in
theorem mob_mobInv_of_norm {p Z : ℂ} (hp : ‖p‖ < 1) (hZ : ‖Z‖ < 1) : mob p (mobInv p Z) = Z :=
  mob_mobInv (normSq_lt_one_of_norm_lt hp).ne (one_add_conj_mul_ne_zero hp hZ)

omit h in
theorem mobInv_mob_of_norm {p z : ℂ} (hp : ‖p‖ < 1) (hz : ‖z‖ < 1) : mobInv p (mob p z) = z :=
  mobInv_mob (normSq_lt_one_of_norm_lt hp).ne (one_sub_conj_mul_ne_zero hp hz)

end Star

variable (σ) in
def hypCoreOut (p : ℂ) (t : ℝ) : Set ℂ := {z | z ∈ σ.triangle ∧ z ≠ 0 ∧ t < ‖mob p z‖}

section CoreOut

variable (h : σ.curv = .hyperbolic)
include h

theorem isPreconnected_hypCoreOut {p : ℂ} {t m : ℝ} (hp : ‖p‖ < 1) (hm : 0 < m) (ht : 0 < t)
    (htm : t + m < 1)
    (hcore : ∀ z, ‖z‖ < 1 → ‖mob p z‖ < t + m → z ∈ σ.triangle ∧ ∀ i, 0 < σ.wallSide i z) :
    IsPreconnected (hypCoreOut σ p t) := by
  have hpi : ∀ i, 0 < σ.wallSide i p :=
    (hcore p hp (by rw [mob_self, norm_zero]; linarith)).2
  set ρ₂ := t + m / 2 with hρ₂
  have hρ₂t : t < ρ₂ := by linarith
  have hρ₂m : ρ₂ < t + m := by linarith
  have hρ₂0 : 0 < ρ₂ := by linarith
  have hin : ∀ Z : ℂ, ‖Z‖ < t + m → t < ‖Z‖ → mobInv p Z ∈ hypCoreOut σ p t := by
    intro Z h1 h2
    have hZ1 : ‖Z‖ < 1 := by linarith
    have hm' := mob_mobInv_of_norm hp hZ1
    obtain ⟨hT, hpos⟩ := hcore _ (norm_mobInv_lt_one hp hZ1) (by rw [hm']; exact h1)
    exact ⟨hT, ne_zero_of_wallSide_pos hpos, by rw [hm']; exact h2⟩
  have hCsub : mobInv p '' sphere 0 ρ₂ ⊆ hypCoreOut σ p t := by
    rintro _ ⟨Z, hZ, rfl⟩
    rw [mem_sphere_zero_iff_norm] at hZ
    exact hin Z (by rw [hZ]; exact hρ₂m) (by rw [hZ]; exact hρ₂t)
  have hCc : IsPreconnected (mobInv p '' sphere 0 ρ₂) :=
    (isPreconnected_sphere (by rw [Complex.rank_real_complex]; norm_num) 0 ρ₂).image _
      fun Z hZ => (continuousAt_mobInv hp (by
        rw [mem_sphere_zero_iff_norm] at hZ; linarith)).continuousWithinAt
  have hx₀ : mobInv p (ρ₂ : ℂ) ∈ mobInv p '' sphere 0 ρ₂ :=
    ⟨ρ₂, by rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hρ₂0], rfl⟩
  refine isPreconnected_of_forall (mobInv p (ρ₂ : ℂ)) fun z hz => ?_
  obtain ⟨hzT, hz0, hzr⟩ := hz
  have hz1 := norm_lt_one_of_mem h hzT
  set Z := mob p z with hZ
  set d := ‖Z‖ with hd
  have hd0 : 0 < d := by linarith
  have hd1 : d < 1 := norm_mob_lt_one hp hz1
  set g : ℝ → ℂ := fun s => mobInv p ((s : ℂ) * Z) with hg
  have hk : ρ₂ / d * d = ρ₂ := div_mul_cancel₀ _ hd0.ne'
  have hnorm : ∀ s : ℝ, 0 ≤ s → ‖(s : ℂ) * Z‖ = s * d := fun s hs => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
  have hsr : ∀ s ∈ uIcc 1 (ρ₂ / d), 0 ≤ s ∧ t < s * d ∧ s * d < 1 ∧
      (1 < s → s * d ≤ ρ₂) := by
    intro s hs
    rcases mem_uIcc.1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have h3 := mul_le_mul_of_nonneg_right h2 hd0.le
      rw [hk] at h3
      refine ⟨by linarith, by nlinarith, by linarith, fun _ => h3⟩
    · have h0 : 0 ≤ ρ₂ / d := div_nonneg hρ₂0.le hd0.le
      have h3 := mul_le_mul_of_nonneg_right h1 hd0.le
      rw [hk] at h3
      refine ⟨by linarith, by linarith, by nlinarith, fun h => absurd h (not_lt.2 h2)⟩
  have hsegsub : g '' uIcc 1 (ρ₂ / d) ⊆ hypCoreOut σ p t := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨hs0, hlo, hlt1, hhi⟩ := hsr s hs
    have hn := hnorm s hs0
    rcases le_or_gt s 1 with hs1 | hs1
    · obtain ⟨hT, hpos⟩ := mobInv_smul_mem_triangle h hp hpi hzT hs0 hs1
      have hmg : mob p (g s) = (s : ℂ) * Z := mob_mobInv_of_norm hp (by rw [hn]; exact hlt1)
      refine ⟨hT, ?_, by rw [hmg, hn]; exact hlo⟩
      rcases hs1.lt_or_eq with hs1 | hs1
      · exact ne_zero_of_wallSide_pos (hpos hs1)
      · change mobInv p ((s : ℂ) * Z) ≠ 0
        rw [hs1, ofReal_one, one_mul, hZ, mobInv_mob_of_norm hp hz1]
        exact hz0
    · exact hin _ (by rw [hn]; linarith [hhi hs1]) (by rw [hn]; exact hlo)
  have hsegc : IsPreconnected (g '' uIcc 1 (ρ₂ / d)) := by
    refine isPreconnected_uIcc.image _ fun s hs => ?_
    obtain ⟨hs0, -, hlt1, -⟩ := hsr s hs
    exact (continuousAt_mobInv hp (by rw [hnorm s hs0]; exact hlt1)).comp_continuousWithinAt
      ((continuous_ofReal.mul continuous_const).continuousWithinAt)
  have hzseg : z ∈ g '' uIcc 1 (ρ₂ / d) := ⟨1, left_mem_uIcc, by
    change mobInv p (((1 : ℝ) : ℂ) * Z) = z
    rw [ofReal_one, one_mul, hZ, mobInv_mob_of_norm hp hz1]⟩
  have hcseg : g (ρ₂ / d) ∈ g '' uIcc 1 (ρ₂ / d) := ⟨ρ₂ / d, right_mem_uIcc, rfl⟩
  have hcC : g (ρ₂ / d) ∈ mobInv p '' sphere 0 ρ₂ := ⟨_, by
    rw [mem_sphere_zero_iff_norm, hnorm _ (div_nonneg hρ₂0.le hd0.le), hk], rfl⟩
  exact ⟨_ ∪ mobInv p '' sphere 0 ρ₂, union_subset hsegsub hCsub, Or.inr hx₀, Or.inl hzseg,
    hsegc.union _ hcseg hcC hCc⟩

end CoreOut

theorem norm_real_add_polar_le (c S Θ : ℝ) (hS : 0 ≤ S) :
    ‖((c : ℝ) : ℂ) + (S : ℂ) * exp ((Θ : ℂ) * I)‖ ≤ |c| + S := by
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hS, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem combo_Icc {τ x y : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) (hx : 0 ≤ x ∧ x ≤ Real.pi)
    (hy : 0 ≤ y ∧ y ≤ Real.pi) :
    0 ≤ (1 - τ) * x + τ * y ∧ (1 - τ) * x + τ * y ≤ Real.pi := by
  have a := mul_nonneg (sub_nonneg.2 h1) hx.1
  have b := mul_nonneg h0 hy.1
  have c := mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hx.2)
  have d := mul_nonneg h0 (sub_nonneg.2 hy.2)
  constructor <;> nlinarith

theorem combo_Icc' {τ x y : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) (hx : 0 ≤ x ∧ x ≤ Real.pi)
    (hy : 0 ≤ y ∧ y ≤ Real.pi) :
    0 ≤ τ * x + (1 - τ) * y ∧ τ * x + (1 - τ) * y ≤ Real.pi := by
  have e := combo_Icc (τ := 1 - τ) (by linarith) (by linarith) hx hy
  rwa [sub_sub_cancel] at e

theorem angle_open_combo' {τ x y : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) (hx : 0 < x ∧ x < Real.pi)
    (hy : 0 < y ∧ y < Real.pi) :
    0 < τ * x + (1 - τ) * y ∧ τ * x + (1 - τ) * y < Real.pi := by
  have e := angle_open_combo (τ := 1 - τ) (by linarith) (by linarith) hx hy
  rwa [sub_sub_cancel] at e

theorem halfArg_pos_of {S R J : ℝ} (hSR : 0 < S + R) (hJ : 0 < J) : 0 < halfArg S R J := by
  unfold halfArg
  have := Real.arctan_pos.2 (div_pos hJ hSR)
  linarith

theorem negHalfArg_lt_pi_of {S R J : ℝ} (hSR : 0 < S - R) (hJ : 0 < J) :
    negHalfArg S R J < Real.pi := by
  unfold negHalfArg
  have := Real.arctan_pos.2 (div_pos hJ hSR)
  linarith

theorem discAngle_mem_sector_open {θ : ℝ} (hθ : 0 < θ) (hθ' : θ ≤ Real.pi / 2) {w : ℂ}
    (h1 : 0 < w.im) (h2 : (exp (-((θ : ℂ) * I)) * w).im < 0) :
    0 < discAngle w ∧ discAngle w < θ := by
  have hw : w ≠ 0 := by
    rintro rfl
    rw [zero_im] at h1
    exact lt_irrefl 0 h1
  obtain ⟨a, b⟩ := discAngle_mem_sector hθ hθ' hw h1.le h2.le
  have hp := halfArg_polar_self hw
    (norm_add_re_pos_of_re hw (re_nonneg_of_sector hθ hθ' h1.le h2.le))
  refine ⟨lt_of_le_of_ne a fun e => ?_, lt_of_le_of_ne b fun e => ?_⟩
  · change (0 : ℝ) = discAngle w at e
    rw [← e, ofReal_zero, zero_mul, Complex.exp_zero, mul_one] at hp
    rw [hp, ofReal_im] at h1
    exact lt_irrefl 0 h1
  · rw [e] at hp
    rw [hp, mul_comm, mul_assoc, exp_mul_exp_neg, mul_one, ofReal_im] at h2
    exact lt_irrefl 0 h2

theorem im_pow_of_sector {θ : ℝ} {p : ℕ} (hθ : 0 < θ) (hθ' : θ ≤ Real.pi / 2)
    (hp : θ * p = Real.pi) {w : ℂ} (h1 : 0 ≤ w.im) (h2 : (exp (-((θ : ℂ) * I)) * w).im ≤ 0) :
    0 ≤ (w ^ p).im ∧ (0 < w.im → (exp (-((θ : ℂ) * I)) * w).im < 0 → 0 < (w ^ p).im) := by
  have hp0 : (0 : ℝ) < p := by
    by_contra hc
    have : (p : ℝ) = 0 := le_antisymm (not_lt.1 hc) (Nat.cast_nonneg p)
    rw [this, mul_zero] at hp
    exact Real.pi_pos.ne hp
  by_cases hw : w = 0
  · subst hw
    have : p ≠ 0 := by
      rintro rfl
      simp at hp0
    refine ⟨by rw [zero_pow this, zero_im], fun h => ?_⟩
    rw [zero_im] at h
    exact absurd h (lt_irrefl 0)
  have hpos := norm_add_re_pos_of_re hw (re_nonneg_of_sector hθ hθ' h1 h2)
  have hψ := discAngle_mem_sector hθ hθ' hw h1 h2
  have e : (w ^ p).im = ‖w‖ ^ p * Real.sin (p * discAngle w) := by
    rw [polar_pow' hpos, im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hle : (p : ℝ) * discAngle w ≤ Real.pi := by
    rw [← hp, mul_comm θ]
    exact mul_le_mul_of_nonneg_left hψ.2 hp0.le
  have hn : 0 < ‖w‖ ^ p := pow_pos (norm_pos_iff.2 hw) p
  refine ⟨?_, fun h3 h4 => ?_⟩
  · rw [e]
    exact mul_nonneg hn.le (Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg hp0.le hψ.1) hle)
  · obtain ⟨a, b⟩ := discAngle_mem_sector_open hθ hθ' h3 h4
    have hlt : (p : ℝ) * discAngle w < Real.pi := by
      rw [← hp, mul_comm θ]
      exact mul_lt_mul_of_pos_left b hp0
    rw [e]
    exact mul_pos hn (Real.sin_pos_of_pos_of_lt_pi (mul_pos hp0 a) hlt)

theorem hypInnerRadial_lt {p : ℕ} {a b τ ϖ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (hϖ0 : 0 ≤ ϖ)
    (hϖ1 : ϖ < 1) : hypInnerRadial p a b τ ϖ < 19 / 10 := by
  have hc0 := coneStep_nonneg a b ϖ
  have hc1 := coneStep_le_one a b ϖ
  have hc := abs_lt.1 (abs_canonForm_lt_one hτ0 hτ1 hϖ0 hϖ1)
  have hA : ϖ ^ p / 2 < 19 / 10 := by
    have := pow_le_one₀ hϖ0 hϖ1.le (n := p)
    linarith
  have hB : 3 / 2 + compactProfileSlope * canonForm τ ϖ < 19 / 10 := by
    unfold compactProfileSlope
    linarith [hc.2]
  unfold hypInnerRadial
  nlinarith [mul_nonneg (sub_nonneg.2 hc1) (sub_pos.2 hA).le, mul_nonneg hc0 (sub_pos.2 hB).le]

theorem hypOuterRadial_lt {p : ℕ} {a b τ ϖ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (hϖ0 : 0 < ϖ)
    (hϖ1 : ϖ < 1) : hypOuterRadial p a b τ ϖ < 7 / 2 := by
  have hc0 := coneStep_nonneg a b ϖ
  have hc1 := coneStep_le_one a b ϖ
  have hc := abs_lt.1 (abs_canonForm_lt_one hτ0 hτ1 hϖ0.le hϖ1)
  have hA : 7 / 2 - ϖ ^ p / 2 < 7 / 2 := by
    have := pow_pos hϖ0 p
    linarith
  have hB : 3 - compactProfileSlope * canonForm τ ϖ < 7 / 2 := by
    unfold compactProfileSlope
    linarith [hc.1]
  unfold hypOuterRadial
  nlinarith [mul_nonneg (sub_nonneg.2 hc1) (sub_pos.2 hA).le, mul_nonneg hc0 (sub_pos.2 hB).le]

section Image

variable (h : σ.curv = .hyperbolic)
include h

theorem im_rotOne_pos {z : ℂ} (hz : ‖z‖ < 1) (hw : 0 < σ.wallSide 1 z) : 0 < (σ.rotOne z).im := by
  have e := rotOne_im_mul_normSq h hz
  have ht := sideOneThree_lt_one h
  have ht0 := sideOneThree_pos h
  have hN := normSq_pos.2 (one_sub_conj_vertexOne_mul_ne_zero h hz)
  have : 0 < (σ.rotOne z).im * normSq (1 - conj σ.vertexOne * z) := by
    rw [e]
    exact mul_pos (by nlinarith) hw
  exact pos_of_mul_pos_left this hN.le

theorem im_rotTwo_pos {z : ℂ} (hw : 0 < σ.wallSide 2 z) : 0 < (σ.rotTwo z).im := by
  rw [wallSide_two_eq_rotTwo h] at hw
  exact pos_of_mul_pos_left hw (normSq_nonneg _)

theorem im_rot_rotTwo_neg {z : ℂ} (hz : ‖z‖ < 1) (hw : 0 < σ.wallSide 0 z) :
    (exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z).im < 0 := by
  have e := rotTwo_rot_im_mul_normSq h z
  have ht := sideTwoThree_lt_one h
  have ht0 := sideTwoThree_pos h
  have hN := normSq_pos.2 (one_sub_vertexTwo_mul_ne_zero h hz)
  have : (exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z).im * normSq (1 - σ.vertexTwo * z) < 0 := by
    rw [e]
    have := mul_pos (by nlinarith : (0 : ℝ) < 1 - sideTwoThree σ ^ 2) hw
    linarith
  by_contra hc
  push Not at hc
  linarith [mul_nonneg hc hN.le]

theorem im_rot_rotOne_neg {z : ℂ} (hz : ‖z‖ < 1) (hw : 0 < σ.wallSide 2 z) :
    (exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).im < 0 := by
  have e := rotOne_rot_im_mul_normSq h hz
  have ht := sideOneTwo_lt_one h
  have ht0 := sideOneTwo_pos h
  have hne : 1 - (sideOneTwo σ : ℂ) * σ.rotTwo z ≠ 0 := by
    have := one_sub_conj_mul_ne_zero (a := (sideOneTwo σ : ℂ))
      (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]; exact ht)
      (norm_rotTwo_lt_one h hz)
    rwa [Complex.conj_ofReal] at this
  have hN := normSq_pos.2 hne
  have hI := im_rotTwo_pos h hw
  have : (exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).im *
      normSq (1 - (sideOneTwo σ : ℂ) * σ.rotTwo z) < 0 := by
    rw [e]
    have := mul_pos (by nlinarith : (0 : ℝ) < 1 - sideOneTwo σ ^ 2) hI
    linarith
  by_contra hc
  push Not at hc
  linarith [mul_nonneg hc hN.le]

omit h in
theorem im_rot_three_neg {z : ℂ} (hw : 0 < σ.wallSide 1 z) :
    (exp (-((σ.θ₃ : ℂ) * I)) * z).im < 0 := by
  have := wallSide_one_eq_neg_im (σ := σ) z
  linarith

theorem apexOne_image {z : ℂ} (hz : z ∈ σ.triangle) :
    ‖(3 / 2 + σ.rotOne z ^ σ.p₁ / 2 : ℂ)‖ < 7 / 2 ∧ 0 ≤ (3 / 2 + σ.rotOne z ^ σ.p₁ / 2 : ℂ).im ∧
      ((∀ i, 0 < σ.wallSide i z) → 0 < (3 / 2 + σ.rotOne z ^ σ.p₁ / 2 : ℂ).im) := by
  have hz1 := norm_lt_one_of_mem h hz
  have hs := sector_one h hz
  have him := im_pow_of_sector (p := σ.p₁) (θ₁_pos σ) (θ₁_le σ) (θ₁_mul σ) hs.1 hs.2
  have e : (3 / 2 + σ.rotOne z ^ σ.p₁ / 2 : ℂ).im = (σ.rotOne z ^ σ.p₁).im / 2 := by
    simp
  have hn : ‖σ.rotOne z ^ σ.p₁‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_rotOne_lt_one h hz1).le
  refine ⟨?_, by rw [e]; linarith [him.1], fun hpos => ?_⟩
  · refine lt_of_le_of_lt (norm_add_le _ _) ?_
    have ha : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by
      rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by norm_num)]
    have hb : ‖σ.rotOne z ^ σ.p₁ / 2‖ ≤ 1 / 2 := by
      rw [norm_div, show ‖(2 : ℂ)‖ = 2 by
        rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos two_pos]]
      linarith
    linarith
  · rw [e]
    have := him.2 (im_rotOne_pos h hz1 (hpos 1)) (im_rot_rotOne_neg h hz1 (hpos 2))
    linarith

theorem apexTwo_image {z : ℂ} (hz : z ∈ σ.triangle) :
    ‖(-(3 / 2) + σ.rotTwo z ^ σ.p₂ / 2 : ℂ)‖ < 7 / 2 ∧
      0 ≤ (-(3 / 2) + σ.rotTwo z ^ σ.p₂ / 2 : ℂ).im ∧
      ((∀ i, 0 < σ.wallSide i z) → 0 < (-(3 / 2) + σ.rotTwo z ^ σ.p₂ / 2 : ℂ).im) := by
  have hz1 := norm_lt_one_of_mem h hz
  have hs := sector_two h hz
  have him := im_pow_of_sector (p := σ.p₂) (θ₂_pos σ) (θ₂_le σ) (θ₂_mul σ) hs.1 hs.2
  have e : (-(3 / 2) + σ.rotTwo z ^ σ.p₂ / 2 : ℂ).im = (σ.rotTwo z ^ σ.p₂).im / 2 := by
    simp
  have hn : ‖σ.rotTwo z ^ σ.p₂‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_rotTwo_lt_one h hz1).le
  refine ⟨?_, by rw [e]; linarith [him.1], fun hpos => ?_⟩
  · refine lt_of_le_of_lt (norm_add_le _ _) ?_
    have ha : ‖(-(3 / 2) : ℂ)‖ = 3 / 2 := by
      rw [norm_neg, show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by norm_num)]
    have hb : ‖σ.rotTwo z ^ σ.p₂ / 2‖ ≤ 1 / 2 := by
      rw [norm_div, show ‖(2 : ℂ)‖ = 2 by
        rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos two_pos]]
      linarith
    linarith
  · rw [e]
    have := him.2 (im_rotTwo_pos h (hpos 2)) (im_rot_rotTwo_neg h hz1 (hpos 0))
    linarith

theorem hd_zero_pos {z : ℂ} (hz : ‖z‖ < 1) (h1 : z ≠ σ.vertexOne) : 0 < hd σ 0 z := by
  rw [← norm_rotOne_eq_hd h]
  exact norm_pos_iff.2 (rotOne_ne_zero h hz h1)

theorem hd_one_pos {z : ℂ} (hz : z ∈ σ.triangle) (h2 : z ≠ σ.vertexTwo) : 0 < hd σ 1 z := by
  have hv := (valid_two h hz h2).1
  rw [← norm_rotTwo_eq_hd h]
  refine norm_pos_iff.2 fun h0 => ?_
  rw [h0, norm_zero, zero_re, add_zero] at hv
  exact lt_irrefl 0 hv

theorem cornerOne_image (a b β β' : ℝ) {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (h1 : z ≠ σ.vertexOne) (h2 : z ≠ σ.vertexTwo) :
    ‖cornerOne σ a b β β' z‖ < 7 / 2 ∧ 0 ≤ (cornerOne σ a b β β' z).im ∧
      ((∀ i, 0 < σ.wallSide i z) → 0 < (cornerOne σ a b β β' z).im) := by
  have hz1 := norm_lt_one_of_mem h hz
  have hd12 := mem_domOneTwo h hz h1 h2
  have hd13 := mem_domOneThree h hz h0 h1
  have hϖ := hd_zero_pos h hz1 h1
  have hS0 := hypInnerRadial_pos (p := σ.p₁) (a := a) (b := b) (tauOne_pos h) tauOne_lt_one hϖ
    (hd_lt_one h 0 hz1)
  have hS1 := hypInnerRadial_lt (p := σ.p₁) (a := a) (b := b) (tauOne_pos h) tauOne_lt_one hϖ.le
    (hd_lt_one h 0 hz1)
  have hs := sector_one h hz
  have hψ := discAngle_mem_sector (θ₁_pos σ) (θ₁_le σ) (rotOne_ne_zero h hz1 h1) hs.1 hs.2
  have hp : (0 : ℝ) < σ.p₁ := by exact_mod_cast (one_le_p₁ (σ := σ))
  have hpθ : (σ.p₁ : ℝ) * σ.θ₁ = Real.pi := by rw [mul_comm]; exact θ₁_mul σ
  have hA0 : 0 ≤ (σ.p₁ : ℝ) * psiOne σ z ∧ (σ.p₁ : ℝ) * psiOne σ z ≤ Real.pi :=
    ⟨mul_nonneg hp.le hψ.1, by rw [← hpθ]; exact mul_le_mul_of_nonneg_left hψ.2 hp.le⟩
  have hA1 := halfArg_mem_Ico' (hpos_one_at_one h hz1)
    (im_twoCircle_nonneg (hz.2 1) : 0 ≤ (bridgeOne σ z).im)
  have hA2 := negHalfArg_mem_Ioc' (hpos_two_at_one h hd12)
    (im_twoCircle_nonneg (sector_two h hz).1 : 0 ≤ (bridgeTwo σ z).im)
  have hin := combo_Icc' (coneStep_nonneg β β' (lensCoord σ z)) (coneStep_le_one β β' _)
    ⟨hA1.1, hA1.2.le⟩ ⟨hA2.1.le, hA2.2⟩
  have hΘ : 0 ≤ angleCornerOne σ a b β β' z ∧ angleCornerOne σ a b β β' z ≤ Real.pi :=
    combo_Icc (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _) hA0 hin
  refine ⟨?_, ?_, fun hpos => ?_⟩
  · refine lt_of_le_of_lt (norm_real_add_polar_le _ _ _ hS0.le) ?_
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    linarith
  · rw [cornerOne, im_real_add_polar]
    exact mul_nonneg hS0.le (Real.sin_nonneg_of_nonneg_of_le_pi hΘ.1 hΘ.2)
  · obtain ⟨a1, a2⟩ := discAngle_mem_sector_open (θ₁_pos σ) (θ₁_le σ)
      (im_rotOne_pos h hz1 (hpos 1)) (im_rot_rotOne_neg h hz1 (hpos 2))
    have hB0 : 0 < (σ.p₁ : ℝ) * psiOne σ z ∧ (σ.p₁ : ℝ) * psiOne σ z < Real.pi :=
      ⟨mul_pos hp a1, by rw [← hpθ]; exact mul_lt_mul_of_pos_left a2 hp⟩
    have hB1 : 0 < angleOneAtOne σ z :=
      halfArg_pos_of (hpos_one_at_one h hz1) (im_bridgeOne_pos h hd13 (hpos 1))
    have hB2 : angleTwoAtOne σ z < Real.pi :=
      negHalfArg_lt_pi_of (hpos_two_at_one h hd12)
        (im_bridgeTwo_pos h hd12 (im_rotTwo_pos h (hpos 2)))
    have hin' := angle_open_combo' (coneStep_nonneg β β' (lensCoord σ z))
      (coneStep_le_one β β' _) ⟨hB1, hA1.2⟩ ⟨hA2.1, hB2⟩
    have hΘ' : 0 < angleCornerOne σ a b β β' z ∧ angleCornerOne σ a b β β' z < Real.pi :=
      angle_open_combo (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _) hB0 hin'
    rw [cornerOne, im_real_add_polar]
    exact mul_pos hS0 (Real.sin_pos_of_pos_of_lt_pi hΘ'.1 hΘ'.2)

theorem cornerTwo_image (a b β β' : ℝ) {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (h1 : z ≠ σ.vertexOne) (h2 : z ≠ σ.vertexTwo) :
    ‖cornerTwo σ a b β β' z‖ < 7 / 2 ∧ 0 ≤ (cornerTwo σ a b β β' z).im ∧
      ((∀ i, 0 < σ.wallSide i z) → 0 < (cornerTwo σ a b β β' z).im) := by
  have hz1 := norm_lt_one_of_mem h hz
  have hd12 := mem_domOneTwo h hz h1 h2
  have hd03 := mem_domZeroThree h hz h0 h2
  have hϖ := hd_one_pos h hz h2
  have hS0 := hypInnerRadial_pos (p := σ.p₂) (a := a) (b := b) (tauTwo_pos h) tauTwo_lt_one hϖ
    (hd_lt_one h 1 hz1)
  have hS1 := hypInnerRadial_lt (p := σ.p₂) (a := a) (b := b) (tauTwo_pos h) tauTwo_lt_one hϖ.le
    (hd_lt_one h 1 hz1)
  have hs := sector_two h hz
  have hne : σ.rotTwo z ≠ 0 := by
    intro h0'
    have hv := (valid_two h hz h2).1
    rw [h0', norm_zero, zero_re, add_zero] at hv
    exact lt_irrefl 0 hv
  have hψ := discAngle_mem_sector (θ₂_pos σ) (θ₂_le σ) hne hs.1 hs.2
  have hp : (0 : ℝ) < σ.p₂ := by exact_mod_cast (one_le_p₂ (σ := σ))
  have hpθ : (σ.p₂ : ℝ) * σ.θ₂ = Real.pi := by rw [mul_comm]; exact θ₂_mul σ
  have hA0 : 0 ≤ (σ.p₂ : ℝ) * psiTwo σ z ∧ (σ.p₂ : ℝ) * psiTwo σ z ≤ Real.pi :=
    ⟨mul_nonneg hp.le hψ.1, by rw [← hpθ]; exact mul_le_mul_of_nonneg_left hψ.2 hp.le⟩
  have hA2 := halfArg_mem_Ico' (hpos_two_at_two h hd12)
    (im_twoCircle_nonneg hs.1 : 0 ≤ (bridgeTwo σ z).im)
  have hA0' := negHalfArg_mem_Ioc' (hpos_zero_at_two h hz1)
    (im_twoCircle_nonneg (hz.2 0) : 0 ≤ (bridgeZero σ z).im)
  have hin := combo_Icc (coneStep_nonneg β β' (lensCoord σ z)) (coneStep_le_one β β' _)
    ⟨hA2.1, hA2.2.le⟩ ⟨hA0'.1.le, hA0'.2⟩
  have hΘ : 0 ≤ angleCornerTwo σ a b β β' z ∧ angleCornerTwo σ a b β β' z ≤ Real.pi :=
    combo_Icc (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _) hA0 hin
  refine ⟨?_, ?_, fun hpos => ?_⟩
  · refine lt_of_le_of_lt (norm_real_add_polar_le _ _ _ hS0.le) ?_
    rw [abs_of_neg (by norm_num : (-(3 / 2) : ℝ) < 0)]
    linarith
  · rw [cornerTwo, im_real_add_polar]
    exact mul_nonneg hS0.le (Real.sin_nonneg_of_nonneg_of_le_pi hΘ.1 hΘ.2)
  · obtain ⟨a1, a2⟩ := discAngle_mem_sector_open (θ₂_pos σ) (θ₂_le σ)
      (im_rotTwo_pos h (hpos 2)) (im_rot_rotTwo_neg h hz1 (hpos 0))
    have hB0 : 0 < (σ.p₂ : ℝ) * psiTwo σ z ∧ (σ.p₂ : ℝ) * psiTwo σ z < Real.pi :=
      ⟨mul_pos hp a1, by rw [← hpθ]; exact mul_lt_mul_of_pos_left a2 hp⟩
    have hB2 : 0 < angleTwoAtTwo σ z :=
      halfArg_pos_of (hpos_two_at_two h hd12)
        (im_bridgeTwo_pos h hd12 (im_rotTwo_pos h (hpos 2)))
    have hB3 : angleZeroAtTwo σ z < Real.pi :=
      negHalfArg_lt_pi_of (hpos_zero_at_two h hz1) (im_bridgeZero_pos h hd03 (hpos 0))
    have hin' := angle_open_combo (coneStep_nonneg β β' (lensCoord σ z))
      (coneStep_le_one β β' _) ⟨hB2, hA2.2⟩ ⟨hA0'.1, hB3⟩
    have hΘ' : 0 < angleCornerTwo σ a b β β' z ∧ angleCornerTwo σ a b β β' z < Real.pi :=
      angle_open_combo (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _) hB0 hin'
    rw [cornerTwo, im_real_add_polar]
    exact mul_pos hS0 (Real.sin_pos_of_pos_of_lt_pi hΘ'.1 hΘ'.2)

theorem cornerThree_image (a b w δ : ℝ) {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (h1 : z ≠ σ.vertexOne) (h2 : z ≠ σ.vertexTwo) :
    ‖cornerThree σ a b w δ z‖ < 7 / 2 ∧ 0 ≤ (cornerThree σ a b w δ z).im ∧
      ((∀ i, 0 < σ.wallSide i z) → 0 < (cornerThree σ a b w δ z).im) := by
  have hz1 := norm_lt_one_of_mem h hz
  have hd13 := mem_domOneThree h hz h0 h1
  have hd03 := mem_domZeroThree h hz h0 h2
  have hϖ : 0 < ‖z‖ := norm_pos_iff.2 h0
  have hS0 := hypOuterRadial_pos (p := σ.p₃) (a := a) (b := b) (tauThree_pos h) tauThree_lt_one
    hϖ.le hz1
  have hS1 := hypOuterRadial_lt (p := σ.p₃) (a := a) (b := b) (tauThree_pos h) tauThree_lt_one
    hϖ hz1
  have hψ := discAngle_mem hz h0
  have hp : (0 : ℝ) < σ.p₃ := by exact_mod_cast (one_le_p₃ (σ := σ))
  have hpθ : (σ.p₃ : ℝ) * σ.θ₃ = Real.pi := by rw [mul_comm]; exact θ₃_mul σ
  have hle : (σ.p₃ : ℝ) * discAngle z ≤ Real.pi := by
    rw [← hpθ]
    exact mul_le_mul_of_nonneg_left hψ.2 hp.le
  have hA0 : 0 ≤ Real.pi - σ.p₃ * discAngle z ∧ Real.pi - σ.p₃ * discAngle z ≤ Real.pi :=
    ⟨by linarith, by linarith [mul_nonneg hp.le hψ.1]⟩
  have hZ := negHalfArg_mem_Ioc' (hpos_zero_at_three h hz1)
    (im_twoCircle_nonneg (hz.2 0) : 0 ≤ (bridgeZero σ z).im)
  have hO := halfArg_mem_Ico' (hpos_one_at_three h hz1)
    (im_twoCircle_nonneg (hz.2 1) : 0 ≤ (bridgeOne σ z).im)
  have hin := combo_Icc (coneStep_nonneg (-w) w (blendThree σ w δ z)) (coneStep_le_one _ _ _)
    ⟨hZ.1.le, hZ.2⟩ ⟨hO.1, hO.2.le⟩
  have hΘ : 0 ≤ angleCornerThree σ a b w δ z ∧ angleCornerThree σ a b w δ z ≤ Real.pi :=
    combo_Icc (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _) hA0 hin
  refine ⟨?_, ?_, fun hpos => ?_⟩
  · refine lt_of_le_of_lt (norm_real_add_polar_le _ _ _ hS0.le) ?_
    rw [abs_zero, zero_add]
    exact hS1
  · rw [cornerThree, im_real_add_polar]
    exact mul_nonneg hS0.le (Real.sin_nonneg_of_nonneg_of_le_pi hΘ.1 hΘ.2)
  · obtain ⟨a1, a2⟩ := discAngle_mem_sector_open (θ₃_pos σ) (θ₃_le σ) (hpos 0)
      (im_rot_three_neg (hpos 1))
    have hB0 : 0 < Real.pi - σ.p₃ * discAngle z ∧ Real.pi - σ.p₃ * discAngle z < Real.pi := by
      have : (σ.p₃ : ℝ) * discAngle z < Real.pi := by
        rw [← hpθ]
        exact mul_lt_mul_of_pos_left a2 hp
      exact ⟨by linarith, by linarith [mul_pos hp a1]⟩
    have hB3 : angleZeroAtThree σ z < Real.pi :=
      negHalfArg_lt_pi_of (hpos_zero_at_three h hz1) (im_bridgeZero_pos h hd03 (hpos 0))
    have hB1 : 0 < angleOneAtThree σ z :=
      halfArg_pos_of (hpos_one_at_three h hz1) (im_bridgeOne_pos h hd13 (hpos 1))
    have hin' := angle_open_combo (coneStep_nonneg (-w) w (blendThree σ w δ z))
      (coneStep_le_one _ _ _) ⟨hZ.1, hB3⟩ ⟨hB1, hO.2⟩
    have hΘ' : 0 < angleCornerThree σ a b w δ z ∧ angleCornerThree σ a b w δ z < Real.pi :=
      angle_open_combo (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _) hB0 hin'
    rw [cornerThree, im_real_add_polar]
    exact mul_pos hS0 (Real.sin_pos_of_pos_of_lt_pi hΘ'.1 hΘ'.2)

theorem hypPreFold_image {L : HypLayout} (hg : 0 < L.g) {z : ℂ} (hz : z ∈ σ.triangle)
    (h0 : z ≠ 0) :
    ‖hypPreFold σ L z‖ < 7 / 2 ∧ 0 ≤ (hypPreFold σ L z).im ∧
      ((∀ i, 0 < σ.wallSide i z) → 0 < (hypPreFold σ L z).im) := by
  have hz1 := norm_lt_one_of_mem h hz
  have hv1 : ¬ hd σ 0 z < L.g → z ≠ σ.vertexOne := fun hc e => hc (by
    rw [e]
    change ‖mob σ.vertexOne σ.vertexOne‖ < L.g
    rw [mob_self, norm_zero]
    exact hg)
  have hv2 : ¬ hd σ 1 z < L.g → z ≠ σ.vertexTwo := fun hc e => hc (by
    rw [e]
    change ‖mob σ.vertexTwo σ.vertexTwo‖ < L.g
    rw [mob_self, norm_zero]
    exact hg)
  unfold hypPreFold
  split_ifs with c1 c2 c3 c4 c5 c6
  · exact apexOne_image h hz
  · exact apexTwo_image h hz
  · rw [← cornerThree_eq_outerGerm (a := 1) (b := 2) (w := 1) (δ := 1) one_lt_two hz1.le
      (valid_three hz h0)]
    exact cornerThree_image h 1 2 1 1 hz h0 (hv1 c1) (hv2 c2)
  · exact cornerOne_image h _ _ _ _ hz h0 (hv1 c1) (hv2 c2)
  · exact cornerTwo_image h _ _ _ _ hz h0 (hv1 c1) (hv2 c2)
  · have hd12 := mem_domOneTwo h hz (hv1 c1) (hv2 c2)
    exact ⟨by linarith [norm_bridgeTwo_lt h hd12],
      (im_twoCircle_nonneg (sector_two h hz).1 : 0 ≤ (bridgeTwo σ z).im),
      fun hpos => im_bridgeTwo_pos h hd12 (im_rotTwo_pos h (hpos 2))⟩
  · exact cornerThree_image h _ _ _ _ hz h0 (hv1 c1) (hv2 c2)

end Image

theorem hypDet_fderiv_comp {f g : ℂ → ℂ} {x : ℂ} (hf : DifferentiableAt ℝ f (g x))
    (hg : DifferentiableAt ℝ g x) :
    (fderiv ℝ (f ∘ g) x).det = (fderiv ℝ f (g x)).det * (fderiv ℝ g x).det := by
  rw [fderiv_comp x hf hg]
  change LinearMap.det ((fderiv ℝ f (g x) : ℂ →ₗ[ℝ] ℂ) ∘ₗ (fderiv ℝ g x : ℂ →ₗ[ℝ] ℂ)) = _
  rw [LinearMap.det_comp]

theorem contDiffAt_mobInv {p Z : ℂ} (hp : ‖p‖ < 1) (hZ : ‖Z‖ < 1) :
    ContDiffAt ℝ ∞ (mobInv p) Z := by
  have e : mobInv p = mob (-p) := funext (mobInv_eq_mob_neg p)
  rw [e]
  apply contDiffAt_mob
  rw [map_neg, neg_mul, sub_neg_eq_add]
  exact one_add_conj_mul_ne_zero hp hZ

theorem det_fderiv_mobInv_pos {p Z : ℂ} (hp : ‖p‖ < 1) (hZ : ‖Z‖ < 1) :
    0 < (fderiv ℝ (mobInv p) Z).det := by
  have e : mobInv p = mob (-p) := funext (mobInv_eq_mob_neg p)
  rw [e]
  apply det_fderiv_mob_pos
  · rw [normSq_neg]
    exact (normSq_lt_one_of_norm_lt hp).ne
  · rw [map_neg, neg_mul, sub_neg_eq_add]
    exact one_add_conj_mul_ne_zero hp hZ

section Core

variable (h : σ.curv = .hyperbolic)
include h

theorem exists_hypFoldCore {E : ℂ → ℂ} {G : Set ℂ} {p : ℂ} {t m : ℝ} (hp : ‖p‖ < 1)
    (hm : 0 < m) (hmt : m < t) (htm : t + m < 1)
    (hcore : ∀ z, ‖z‖ < 1 → ‖mob p z‖ < t + m → z ∈ σ.triangle ∧ ∀ i, 0 < σ.wallSide i z)
    (hGo : IsOpen G) (hGd : ∀ z ∈ G, ‖z‖ < 1)
    (hGT : ∀ z ∈ σ.triangle, z ≠ 0 → t - m < ‖mob p z‖ → z ∈ G)
    (hEs : ∀ z ∈ G, ContDiffAt ℝ ∞ E z)
    (hEd : ∀ z ∈ G, z ≠ σ.vertexOne → z ≠ σ.vertexTwo → 0 < (fderiv ℝ E z).det)
    (hinj : InjOn E (σ.triangle \ {0}))
    (himg : ∀ z ∈ σ.triangle, z ≠ 0 → ‖E z‖ < 7 / 2 ∧ 0 ≤ (E z).im ∧
      ((∀ i, 0 < σ.wallSide i z) → 0 < (E z).im))
    {ρ : ℝ} (hρ : 0 < ρ)
    (hout : ∀ z ∈ σ.triangle, 0 < ‖z‖ → ‖z‖ < ρ → E z = compactOuterGerm σ.p₃ z) :
    ∃ F : ℂ → ℂ, ∃ U : Set ℂ, IsOpen U ∧ (0 : ℂ) ∉ U ∧ (∀ z ∈ U, ‖z‖ < 1) ∧
      σ.triangle \ {0} ⊆ U ∧ (∀ z ∈ G, z ≠ 0 → t < ‖mob p z‖ → z ∈ U) ∧
      ContDiffOn ℝ ∞ F U ∧
      (∀ z ∈ U, z ≠ σ.vertexOne → z ≠ σ.vertexTwo → 0 < (fderiv ℝ F z).det) ∧
      (∀ z, t ≤ ‖mob p z‖ → F z = E z) ∧
      InjOn F (σ.triangle \ {0}) ∧ MapsTo F (σ.triangle \ {0}) basePlusSeven := by
  have ht0 : 0 < t := by linarith
  set E' : ℂ → ℂ := fun Z => E (mobInv p Z) with hE'
  have hann : ∀ Z : ℂ, t - m < ‖Z‖ → ‖Z‖ < t + m → ‖Z‖ < 1 ∧ mobInv p Z ∈ σ.triangle ∧
      (∀ i, 0 < σ.wallSide i (mobInv p Z)) ∧ mobInv p Z ≠ 0 ∧ mobInv p Z ≠ σ.vertexOne ∧
      mobInv p Z ≠ σ.vertexTwo ∧ mobInv p Z ∈ G ∧ mob p (mobInv p Z) = Z := by
    intro Z h1 h2
    have hZ1 : ‖Z‖ < 1 := by linarith
    have hm' := mob_mobInv_of_norm hp hZ1
    obtain ⟨hT, hpos⟩ := hcore _ (norm_mobInv_lt_one hp hZ1) (by rw [hm']; exact h2)
    obtain ⟨h0, a1, a2⟩ := σ.ne_of_mem_openTriangle ⟨hT.1, hpos⟩
    exact ⟨hZ1, hT, hpos, h0, a1, a2, hGT _ hT h0 (by rw [hm']; exact h1), hm'⟩
  have hdE : ∀ Z : ℂ, ‖Z‖ < 1 → mobInv p Z ∈ G →
      (fderiv ℝ E' Z).det = (fderiv ℝ E (mobInv p Z)).det * (fderiv ℝ (mobInv p) Z).det :=
    fun Z hZ hG => hypDet_fderiv_comp ((hEs _ hG).differentiableAt (by simp))
      ((contDiffAt_mobInv hp hZ).differentiableAt (by simp))
  have hE'c : ContDiffOn ℝ ∞ E' {Z | t - m < ‖Z - 0‖ ∧ ‖Z - 0‖ < t + m} := by
    intro Z hZ
    have hZ' : t - m < ‖Z‖ ∧ ‖Z‖ < t + m := by simpa using hZ
    obtain ⟨hZ1, -, -, -, -, -, hG, -⟩ := hann Z hZ'.1 hZ'.2
    exact ((hEs _ hG).comp Z (contDiffAt_mobInv hp hZ1)).contDiffWithinAt
  have hE'det : ∀ Z, t - m < ‖Z - 0‖ → ‖Z - 0‖ < t + m → (fderiv ℝ E' Z).det ≠ 0 := by
    intro Z h1 h2
    rw [sub_zero] at h1 h2
    obtain ⟨hZ1, -, -, -, a1, a2, hG, -⟩ := hann Z h1 h2
    rw [hdE Z hZ1 hG]
    exact (mul_pos (hEd _ hG a1 a2) (det_fderiv_mobInv_pos hp hZ1)).ne'
  have hE'inj : InjOn E' {Z | t - m < ‖Z - 0‖ ∧ ‖Z - 0‖ < t + m} := by
    intro Z hZ W hW hEq
    have hZ' : t - m < ‖Z‖ ∧ ‖Z‖ < t + m := by simpa using hZ
    have hW' : t - m < ‖W‖ ∧ ‖W‖ < t + m := by simpa using hW
    obtain ⟨-, hT, -, h0, -, -, -, hm1⟩ := hann Z hZ'.1 hZ'.2
    obtain ⟨-, hT', -, h0', -, -, -, hm2⟩ := hann W hW'.1 hW'.2
    have e := hinj ⟨hT, h0⟩ ⟨hT', h0'⟩ hEq
    rw [← hm1, ← hm2, e]
  have hsph : ∀ q ∈ sphere (0 : ℂ) t, ‖q‖ = t ∧ mobInv p q ∈ σ.triangle ∧ mobInv p q ≠ 0 ∧
      ContinuousAt E' q ∧ E' q ∈ openHalfSeven := by
    intro q hq
    have hq' : ‖q‖ = t := by rwa [mem_sphere_zero_iff_norm] at hq
    obtain ⟨hq1, hT, hpos, h0, -, -, hG, -⟩ := hann q (by linarith) (by linarith)
    obtain ⟨hn, -, hi⟩ := himg _ hT h0
    exact ⟨hq', hT, h0, (hEs _ hG).continuousAt.comp (contDiffAt_mobInv hp hq1).continuousAt,
      hn, hi hpos⟩
  obtain ⟨qmax, hqmax, hmax⟩ := (isCompact_sphere (0 : ℂ) t).exists_isMaxOn
    (NormedSpace.sphere_nonempty.2 ht0.le)
    (fun q hq => (hsph q hq).2.2.2.1.norm.continuousWithinAt)
  set M := ‖E' qmax‖ with hM
  have hM7 : M < 7 / 2 := (hsph qmax hqmax).2.2.2.2.1
  have hM0 : 0 ≤ M := norm_nonneg _
  set x := min (ρ / 2) (min (sideTwoThree σ) (7 / 2 - M)) with hx
  have hx0 : 0 < x := lt_min (by linarith) (lt_min (sideTwoThree_pos h) (by linarith))
  have hxρ : x < ρ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hxv : x ≤ sideTwoThree σ := (min_le_right _ _).trans (min_le_left _ _)
  have hxM : x ≤ 7 / 2 - M := (min_le_right _ _).trans (min_le_right _ _)
  have hx1 : x < 1 := lt_of_le_of_lt hxv (sideTwoThree_lt_one h)
  set zt : ℂ := (x : ℂ) with hzt
  have hztT : zt ∈ σ.triangle := σ.real_mem_triangle hx0.le hxv
  have hztn : ‖zt‖ = x := by rw [hzt, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
  have hzt0 : zt ≠ 0 := by
    intro e
    rw [e, norm_zero] at hztn
    linarith
  have hztc : t < ‖mob p zt‖ := by
    by_contra hc
    push Not at hc
    have := (hcore zt (by rw [hztn]; exact hx1) (by linarith)).2 0
    change 0 < zt.im at this
    rw [hzt, ofReal_im] at this
    exact lt_irrefl 0 this
  have hpow : x ^ σ.p₃ ≤ x := pow_le_of_le_one hx0.le hx1.le (by have := σ.two_le_p₃; omega)
  have hEzt : E zt = compactOuterGerm σ.p₃ zt :=
    hout zt hztT (by rw [hztn]; exact hx0) (by rw [hztn]; exact hxρ)
  have hnE : M < ‖E zt‖ := by
    rw [hEzt, norm_compactOuterGerm hzt0 (by rw [hztn]; linarith), hztn]
    linarith
  set u₀ := E zt with hu₀
  have hu0 : u₀ ≠ 0 := by
    intro e
    rw [e, norm_zero] at hnE
    linarith
  have hGout : ∀ z ∈ hypCoreOut σ p t, z ∈ G := fun z hz =>
    hGT z hz.1 hz.2.1 (by linarith [hz.2.2])
  have hEcont : ContinuousOn E (hypCoreOut σ p t) := fun z hz =>
    (hEs z (hGout z hz)).continuousAt.continuousWithinAt
  set S := E '' hypCoreOut σ p t ∪ (fun s : ℝ => (s : ℂ) * u₀) '' Ici 1 with hSdef
  have hztout : zt ∈ hypCoreOut σ p t := ⟨hztT, hzt0, hztc⟩
  have hSc : IsPreconnected S :=
    ((isPreconnected_hypCoreOut h hp hm ht0 htm hcore).image E hEcont).union u₀
      ⟨zt, hztout, rfl⟩ ⟨1, mem_Ici.2 le_rfl, by simp⟩ (isPreconnected_ray u₀)
  have hSb : ¬ Bornology.IsBounded S := fun hb =>
    not_isBounded_ray hu0 (hb.subset subset_union_right)
  have hSd : Disjoint S (E' '' sphere 0 t) := by
    rw [disjoint_left]
    rintro v (⟨y, hy, hyv⟩ | hv) ⟨q, hq, hqv⟩
    · obtain ⟨hq', hqT, hq0, -⟩ := hsph q hq
      have e := hinj ⟨hy.1, hy.2.1⟩ ⟨hqT, hq0⟩ (hyv.trans hqv.symm)
      have h2 := hy.2.2
      rw [e, mob_mobInv_of_norm hp (by rw [hq']; linarith), hq'] at h2
      exact lt_irrefl _ h2
    · have h1 := norm_ray_ge hv
      have h2 : ‖E' q‖ ≤ M := hmax hq
      rw [hqv] at h2
      linarith
  set Z₀ : ℂ := ((t + m / 2 : ℝ) : ℂ) with hZ₀
  have hZ₀n : ‖Z₀‖ = t + m / 2 := by
    rw [hZ₀, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hout' : ∃ z₀, t < ‖z₀ - 0‖ ∧ ‖z₀ - 0‖ < t + m ∧ ∃ S : Set ℂ, IsPreconnected S ∧
      E' z₀ ∈ S ∧ Disjoint S (E' '' sphere 0 t) ∧ ¬ Bornology.IsBounded S := by
    obtain ⟨-, hT, -, h0, -, -, -, hm'⟩ := hann Z₀ (by rw [hZ₀n]; linarith)
      (by rw [hZ₀n]; linarith)
    refine ⟨Z₀, by rw [sub_zero, hZ₀n]; linarith, by rw [sub_zero, hZ₀n]; linarith, S, hSc,
      Or.inl ⟨mobInv p Z₀, ⟨hT, h0, by rw [hm', hZ₀n]; linarith⟩, rfl⟩, hSd, hSb⟩
  obtain ⟨Q, hQs, hQi, hQd, ⟨V, hVo, hsV, hQV⟩, hQc⟩ :=
    exists_core_replacement hm hmt hE'c hE'det hE'inj hout'
  have hQE : Q =ᶠ[𝓝 qmax] E' := Filter.eventually_of_mem (hVo.mem_nhds (hsV hqmax)) hQV
  have hQpos : ∀ u, 0 < (fderiv ℝ Q u).det := by
    have hq := (hsph qmax hqmax).1
    obtain ⟨hq1, -, -, -, a1, a2, hG, -⟩ := hann qmax (by linarith) (by linarith)
    refine det_pos_of_ne_zero hQs hQd (u₀ := qmax) ?_
    rw [hQE.fderiv_eq, hdE qmax hq1 hG]
    exact mul_pos (hEd _ hG a1 a2) (det_fderiv_mobInv_pos hp hq1)
  have hQball : Q '' ball (0 : ℂ) t ⊆ openHalfSeven := by
    rintro _ ⟨w, hw, rfl⟩
    by_contra hcon
    obtain ⟨S₀, hS₀, huS, hS₀d, hS₀b⟩ := outside_halfSeven hcon
    have hΓ : Disjoint S₀ (E' '' sphere 0 t) := by
      refine disjoint_left.2 fun v hv ⟨q, hq, hqv⟩ => disjoint_left.1 hS₀d hv ?_
      rw [← hqv]
      exact (hsph q hq).2.2.2.2
    exact disjoint_left.1 (hQc S₀ hS₀ hS₀b hΓ) huS ⟨w, hw, rfl⟩
  have hφc : ∀ z : ℂ, ‖z‖ < 1 → ContDiffAt ℝ ∞ (mob p) z := fun z hz =>
    contDiffAt_mob (one_sub_conj_mul_ne_zero hp hz)
  classical
  set F : ℂ → ℂ := fun z => if ‖z‖ < 1 ∧ ‖mob p z‖ < t then Q (mob p z) else E z with hFdef
  have hF1 : ∀ z, ¬ (‖z‖ < 1 ∧ ‖mob p z‖ < t) → F z = E z := fun z hz => ite_eq_right hz
  have hFE : ∀ z, t ≤ ‖mob p z‖ → F z = E z := fun z hz =>
    hF1 z fun h' => absurd h'.2 (not_lt.2 hz)
  have hFQ : ∀ z, ‖z‖ < 1 → (mob p z ∈ V ∨ ‖mob p z‖ < t) → F z = Q (mob p z) := by
    intro z hz1 hc
    by_cases hb : ‖mob p z‖ < t
    · exact ite_eq_left ⟨hz1, hb⟩
    · rw [hF1 z fun h' => hb h'.2]
      rcases hc with hV | hb'
      · rw [hQV hV]
        change E z = E (mobInv p (mob p z))
        rw [mobInv_mob_of_norm hp hz1]
      · exact absurd hb' hb
  have hφcont : ContinuousOn (mob p) (ball (0 : ℂ) 1) := fun z hz =>
    (hφc z (by simpa using hz)).continuousAt.continuousWithinAt
  set W := ball (0 : ℂ) 1 ∩ mob p ⁻¹' (V ∪ ball 0 t) with hW
  have hWo : IsOpen W := hφcont.isOpen_inter_preimage isOpen_ball (hVo.union isOpen_ball)
  have hWmem : ∀ z ∈ W, ‖z‖ < 1 ∧ (mob p z ∈ V ∨ ‖mob p z‖ < t) := by
    intro z hz
    refine ⟨by simpa using hz.1, ?_⟩
    rcases hz.2 with h' | h'
    · exact Or.inl h'
    · exact Or.inr (by simpa using h')
  have hFW : ∀ z ∈ W, F z = Q (mob p z) := fun z hz => hFQ z (hWmem z hz).1 (hWmem z hz).2
  set G' := G ∩ mob p ⁻¹' {w | t < ‖w‖} with hG'
  have hG'o : IsOpen G' := ContinuousOn.isOpen_inter_preimage
    (fun z hz => (hφc z (hGd z hz)).continuousAt.continuousWithinAt) hGo
    (isOpen_lt continuous_const continuous_norm)
  have hFG : ∀ z ∈ G', F z = E z := fun z hz => hFE z (le_of_lt hz.2)
  have hevW : ∀ z ∈ W, F =ᶠ[𝓝 z] (Q ∘ mob p) := fun z hz =>
    Filter.eventually_of_mem (hWo.mem_nhds hz) hFW
  have hevG : ∀ z ∈ G', F =ᶠ[𝓝 z] E := fun z hz =>
    Filter.eventually_of_mem (hG'o.mem_nhds hz) hFG
  set U := (W ∪ G') ∩ {z | z ≠ 0} with hU
  have hUo : IsOpen U := (hWo.union hG'o).inter isOpen_ne
  refine ⟨F, U, hUo, fun h' => h'.2 rfl, ?_, ?_, ?_, ?_, ?_, hFE, ?_, ?_⟩
  · rintro z ⟨hz | hz, -⟩
    · exact (hWmem z hz).1
    · exact hGd z hz.1
  · rintro z ⟨hzT, hz0⟩
    have hz1 := norm_lt_one_of_mem h hzT
    refine ⟨?_, hz0⟩
    rcases lt_trichotomy ‖mob p z‖ t with hc | hc | hc
    · exact Or.inl ⟨by simpa using hz1, Or.inr (by simpa using hc)⟩
    · exact Or.inl ⟨by simpa using hz1, Or.inl (hsV (by simpa using hc))⟩
    · exact Or.inr ⟨hGT z hzT hz0 (by linarith), hc⟩
  · intro z hz h0 hc
    exact ⟨Or.inr ⟨hz, hc⟩, h0⟩
  · intro z hz
    rcases hz.1 with hw | hg
    · exact ((hQs.contDiffAt.comp z (hφc z (hWmem z hw).1)).congr_of_eventuallyEq
        (hevW z hw)).contDiffWithinAt
    · exact ((hEs z hg.1).congr_of_eventuallyEq (hevG z hg)).contDiffWithinAt
  · intro z hz h1 h2
    rcases hz.1 with hw | hg
    · rw [(hevW z hw).fderiv_eq, hypDet_fderiv_comp (hQs.contDiffAt.differentiableAt (by simp))
        ((hφc z (hWmem z hw).1).differentiableAt (by simp))]
      exact mul_pos (hQpos _) (det_fderiv_mob_pos (normSq_lt_one_of_norm_lt hp).ne
        (one_sub_conj_mul_ne_zero hp (hWmem z hw).1))
    · rw [(hevG z hg).fderiv_eq]
      exact hEd z hg.1 h1 h2
  · have key : ∀ a b : ℂ, a ∈ σ.triangle \ {0} → b ∈ σ.triangle \ {0} → ‖mob p a‖ < t →
        t ≤ ‖mob p b‖ → F a = F b → False := by
      intro a b ha hb hna hnb hab
      have ha1 := norm_lt_one_of_mem h ha.1
      have hb1 := norm_lt_one_of_mem h hb.1
      have hFa : F a = Q (mob p a) := hFQ a ha1 (Or.inr hna)
      rcases hnb.lt_or_eq with hlt | heq
      · have hbS : E b ∈ S := Or.inl ⟨b, ⟨hb.1, hb.2, hlt⟩, rfl⟩
        rw [← hFE b hnb, ← hab, hFa] at hbS
        exact disjoint_left.1 (hQc S hSc hSb hSd) hbS
          ⟨mob p a, by rw [mem_ball_zero_iff]; exact hna, rfl⟩
      · have hbV : mob p b ∈ V := hsV (by rw [mem_sphere_zero_iff_norm]; exact heq.symm)
        rw [hFa, hFQ b hb1 (Or.inl hbV)] at hab
        have := hQi hab
        rw [this] at hna
        linarith
    intro z hz z' hz' heq
    have hz1 := norm_lt_one_of_mem h hz.1
    have hz1' := norm_lt_one_of_mem h hz'.1
    by_cases h1 : ‖mob p z‖ < t <;> by_cases h2 : ‖mob p z'‖ < t
    · rw [hFQ z hz1 (Or.inr h1), hFQ z' hz1' (Or.inr h2)] at heq
      have := hQi heq
      rw [← mobInv_mob_of_norm hp hz1, this, mobInv_mob_of_norm hp hz1']
    · exact (key z z' hz hz' h1 (not_lt.1 h2) heq).elim
    · exact (key z' z hz' hz h2 (not_lt.1 h1) heq.symm).elim
    · rw [hFE z (not_lt.1 h1), hFE z' (not_lt.1 h2)] at heq
      exact hinj hz hz' heq
  · rintro z ⟨hzT, hz0⟩
    have hz1 := norm_lt_one_of_mem h hzT
    by_cases hc : ‖mob p z‖ < t
    · rw [hFQ z hz1 (Or.inr hc)]
      have := hQball ⟨mob p z, by rw [mem_ball_zero_iff]; exact hc, rfl⟩
      exact ⟨this.1, this.2.le⟩
    · rw [hFE z (not_lt.1 hc)]
      obtain ⟨hn, hi, -⟩ := himg z hzT hz0
      exact ⟨hn, hi⟩

theorem hypFold_refl_of_far {L : HypLayout} (hab : L.a < L.b) (hb1 : L.b < 1)
    (hc1 : canonForm (tauOne σ) L.b < -L.e) (hc2 : canonForm (tauTwo σ) L.b < -L.e)
    (hβ0 : 0 < L.β) (hβ : L.β < L.β') {F : ℂ → ℂ} {p : ℂ} {t : ℝ}
    (hFE : ∀ z, t ≤ ‖mob p z‖ → F z = hypPreFold σ L z) (i : Fin 3)
    (hV : ∀ z ∈ hypWallNbhd σ L i, t ≤ ‖mob p z‖) {z : ℂ} (hz : z ∈ hypWallNbhd σ L i) :
    F (σ.refl i z) = conj (F z) := by
  rw [hFE _ (hV _ (refl_mapsTo_hypWallNbhd h L i hz)), hFE z (hV z hz)]
  exact hypPreFold_refl h hab hb1 hc1 hc2 hβ0 hβ i hz

theorem hypPreFold_eq_outer {L : HypLayout} (hgb : L.g < L.b) (hb1 : L.b < 1) (he : 0 < L.e)
    (hc1 : canonForm (tauOne σ) L.b < -L.e) (hc2 : canonForm (tauTwo σ) L.b < -L.e)
    (hg₃ : L.g₃ < tauThree σ) {z : ℂ} (hz : z ∈ σ.triangle) (hzg : ‖z‖ < L.g₃) :
    hypPreFold σ L z = compactOuterGerm σ.p₃ z := by
  have hτ := tau_mem h 2
  have hz1 : ‖z‖ < tauThree σ := hzg.trans hg₃
  have hn : canon σ 2 z < 0 := by
    change canonForm (tauThree σ) ‖z‖ < 0
    unfold canonForm
    exact div_neg_of_neg_of_pos (by linarith)
      (by nlinarith [norm_nonneg z, tauThree_lt_one (σ := σ)])
  have h0 : ¬ hd σ 0 z < L.g := not_lt.2 (lt_hd_of_canon_nonneg h 0
    (by linarith [canon_zero_add_two_nonneg h hz]) hgb hb1 he hc1).le
  have h1 : ¬ hd σ 1 z < L.g := not_lt.2 (lt_hd_of_canon_nonneg h 1
    (by linarith [canon_one_add_two_nonneg h hz]) hgb hb1 he hc2).le
  unfold hypPreFold
  rw [ite_eq_right h0, ite_eq_right h1, ite_eq_left hzg]

theorem hypWallNbhd_far_core (i : Fin 3) {z : ℂ} (hz : z ∈ hypWallNbhd σ (hypLayout σ) i) :
    hypCoreRadius σ ≤ ‖mob (hypCoreCenter σ) z‖ := by
  have hz1 := (hypWallNbhd_subset (hypLayout σ) (hypLayout_params h).2.2.2.2.2.2.2.2.2.2.2.1 i
    hz).1
  by_contra hc
  push Not at hc
  obtain ⟨a0, a1, l1, l2, -⟩ := core_separation h hz1 hc
  fin_cases i
  · rcases hypWallNbhd_zero_subset (hypLayout σ) hz with q | q
    · linarith
    · linarith
  · rcases hypWallNbhd_one_subset (hypLayout σ) hz with q | q
    · linarith
    · linarith
  · have q := hypWallNbhd_two_subset (hypLayout σ) hz
    have := le_abs_self (lensCoord σ z)
    change |lensCoord σ z| < (hypLayout σ).β / 2 at q
    linarith

theorem exists_hypFoldCore_layout {G : Set ℂ} (hGo : IsOpen G) (hGd : ∀ z ∈ G, ‖z‖ < 1)
    (hGT : ∀ z ∈ σ.triangle, z ≠ 0 →
      hypCoreRadius σ - hypCoreMargin σ < ‖mob (hypCoreCenter σ) z‖ → z ∈ G)
    (hEs : ∀ z ∈ G, ContDiffAt ℝ ∞ (hypPreFold σ (hypLayout σ)) z)
    (hEd : ∀ z ∈ G, z ≠ σ.vertexOne → z ≠ σ.vertexTwo →
      0 < (fderiv ℝ (hypPreFold σ (hypLayout σ)) z).det)
    (hinj : InjOn (hypPreFold σ (hypLayout σ)) (σ.triangle \ {0})) :
    ∃ F : ℂ → ℂ, ∃ U : Set ℂ, IsOpen U ∧ (0 : ℂ) ∉ U ∧ (∀ z ∈ U, ‖z‖ < 1) ∧
      σ.triangle \ {0} ⊆ U ∧
      (∀ z ∈ G, z ≠ 0 → hypCoreRadius σ < ‖mob (hypCoreCenter σ) z‖ → z ∈ U) ∧
      ContDiffOn ℝ ∞ F U ∧
      (∀ z ∈ U, z ≠ σ.vertexOne → z ≠ σ.vertexTwo → 0 < (fderiv ℝ F z).det) ∧
      (∀ z, hypCoreRadius σ ≤ ‖mob (hypCoreCenter σ) z‖ → F z = hypPreFold σ (hypLayout σ) z) ∧
      (∀ i, ∀ z ∈ hypWallNbhd σ (hypLayout σ) i, F (σ.refl i z) = conj (F z)) ∧
      InjOn F (σ.triangle \ {0}) ∧ MapsTo F (σ.triangle \ {0}) basePlusSeven := by
  obtain ⟨hg0, hga, hab, hb1, he, hc1, hc2, hβ0, hβ, -, -, hg₃0, hg₃a, ha₃, hb₃, -⟩ :=
    hypLayout_params h (σ := σ)
  obtain ⟨hm, hmt, htm⟩ := hypCore_params h (σ := σ)
  obtain ⟨F, U, hUo, h0U, hUd, hTU, hGU, hF, hdet, hFE, hinjF, hmaps⟩ :=
    exists_hypFoldCore h (norm_hypCoreCenter_lt_one h) hm hmt htm
      (fun z hz hc => mem_openTriangle_of_core h hz hc) hGo hGd hGT hEs hEd hinj
      (fun z hz h0 => hypPreFold_image h hg0 hz h0) hg₃0
      (fun z hz _ hzg => hypPreFold_eq_outer h (hga.trans hab) hb1 he hc1 hc2
        ((hg₃a.trans ha₃).trans hb₃) hz hzg)
  exact ⟨F, U, hUo, h0U, hUd, hTU, hGU, hF, hdet, hFE,
    fun i z hz => hypFold_refl_of_far h hab hb1 hc1 hc2 hβ0 hβ hFE i
      (fun w hw => hypWallNbhd_far_core h i hw) hz, hinjF, hmaps⟩

end Core

end HypFold

end GC.Seifert
