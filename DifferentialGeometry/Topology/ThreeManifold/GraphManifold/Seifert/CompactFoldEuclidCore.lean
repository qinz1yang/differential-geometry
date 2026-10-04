import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldEuclidWalls
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSpec
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsCoreJordan
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsFoldCore

/-!
# The flat compact fold with its incircle core replaced

Lane CF, tier 3, curvature `0` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §6, with review 23 §6: the Euclidean centre and
radius of the core and `hout` joined to the outer cone). The map `E = preFold` is smooth with
positive Jacobian outside the inner core disc `‖z - I‖ < coreRadius - coreMargin` and injective
on the triangle minus `v₃ = 0`. The annulus `‖z - I‖ ∈ (r - δ, r + δ)` (`r = coreRadius`,
`δ = coreMargin`) lies inside the incircle, hence in the open triangle (`mem_of_near`).

For `hout` take a point of the annulus on the outer side and the set `S = E(coreOut) ∪ ray`,
where `coreOut = {z ∈ T \ {0}, ‖z - I‖ > r}` is preconnected (radial segments to the circle of
radius `r + δ/2`, `isPreconnected_coreOut`) and the ray starts at the image of a point close to
`v₃`, where `E` is the outer germ of modulus `7/2 - ‖z‖^{p₃}/2`, larger than the maximum of `‖E‖`
on the core circle. K16f's `exists_core_replacement` then gives a plane diffeomorphism `Q` equal
to `E` near the circle; its Jacobian is positive everywhere by connectedness
(`det_pos_of_ne_zero`). The fold `F` is `Q` on the open core disc and `E` elsewhere
(`exists_foldCore`): it is smooth with positive Jacobian off `v₁, v₂` on an open set containing
`T \ {0}`, injective there, and maps it into `basePlusSeven`, the core disc going into the open
upper half disc because every point outside that half disc lies on a ray missing it
(`outside_halfSeven`).
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Set Metric
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

def openHalfSeven : Set ℂ := {u | ‖u‖ < 7 / 2 ∧ 0 < u.im}

theorem outside_halfSeven {u : ℂ} (hu : u ∉ openHalfSeven) :
    ∃ S : Set ℂ, IsPreconnected S ∧ u ∈ S ∧ Disjoint S openHalfSeven ∧
      ¬ Bornology.IsBounded S := by
  by_cases him : u.im ≤ 0
  · have hdown : IsPreconnected ((fun t : ℝ => u - (t : ℂ) * I) '' Ici 0) :=
      isPreconnected_Ici.image _ (by fun_prop)
    have hdownb : ¬ Bornology.IsBounded ((fun t : ℝ => u - (t : ℂ) * I) '' Ici 0) := by
      rw [isBounded_iff_forall_norm_le]
      rintro ⟨C, hC⟩
      set t : ℝ := |C| + ‖u‖ + 1
      have ht := hC (u - (t : ℂ) * I) ⟨t, mem_Ici.2 (by positivity), rfl⟩
      have h1 := norm_sub_norm_le ((t : ℂ) * I) u
      rw [norm_sub_rev] at h1
      rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity), mul_one] at h1
      linarith [le_abs_self C]
    refine ⟨_, hdown, ⟨0, mem_Ici.2 le_rfl, by simp⟩, disjoint_left.2 ?_, hdownb⟩
    rintro v ⟨t, ht, rfl⟩ hv
    have := hv.2
    simp only [sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_one, zero_mul,
      add_zero] at this
    linarith [mem_Ici.1 ht]
  · push Not at him
    have h3 : 7 / 2 ≤ ‖u‖ := by
      by_contra h
      exact hu ⟨not_le.1 h, him⟩
    have hu0 : u ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h3
      linarith
    refine ⟨_, isPreconnected_ray u, ⟨1, mem_Ici.2 le_rfl, by simp⟩, disjoint_left.2 ?_,
      not_isBounded_ray hu0⟩
    intro v hv hvp
    have := norm_ray_ge hv
    linarith [hvp.1]

theorem det_pos_of_ne_zero {Q : ℂ → ℂ} (hQ : ContDiff ℝ ∞ Q)
    (hne : ∀ u, (fderiv ℝ Q u).det ≠ 0) {u₀ : ℂ} (h0 : 0 < (fderiv ℝ Q u₀).det) (u : ℂ) :
    0 < (fderiv ℝ Q u).det := by
  have hc : Continuous fun v => (fderiv ℝ Q v).det :=
    ContinuousLinearMap.continuous_det.comp (hQ.continuous_fderiv (by simp))
  by_contra hle
  have hlt : (fderiv ℝ Q u).det < 0 := lt_of_le_of_ne (not_lt.1 hle) (hne u)
  obtain ⟨w, -, hw⟩ := isPreconnected_univ.intermediate_value (mem_univ u) (mem_univ u₀)
    hc.continuousOn ⟨hlt.le, h0.le⟩
  exact hne w hw

theorem norm_compactOuterGerm {p : ℕ} {z : ℂ} (hz : z ≠ 0) (hm : ‖z‖ ^ p ≤ 7) :
    ‖compactOuterGerm p z‖ = 7 / 2 - ‖z‖ ^ p / 2 := by
  have hn : ‖conj z / ((‖z‖ : ℝ) : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      div_self (norm_ne_zero_iff.2 hz)]
  rw [compactOuterGerm, norm_neg, norm_mul, norm_pow, hn, one_pow, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by linarith)]

namespace EuclidShape

variable (σ : EuclidShape)

theorem abs_wallSide_sub_le (i : Fin 3) (z w : ℂ) :
    |σ.wallSide i z - σ.wallSide i w| ≤ ‖z - w‖ := by
  fin_cases i
  · change |z.im - w.im| ≤ _
    rw [← sub_im]
    exact Complex.abs_im_le_norm _
  · exact σ.abs_wallSide_one_sub_le z w
  · exact σ.abs_wallSide_two_sub_le z w

theorem wallSide_incenter (i : Fin 3) : σ.wallSide i σ.incenter = σ.inradius := by
  fin_cases i
  · exact σ.wallSide_zero_incenter
  · exact σ.wallSide_one_incenter
  · exact σ.wallSide_two_incenter

theorem wallSide_pos_of_near {z : ℂ} (h : ‖z - σ.incenter‖ < σ.inradius) (i : Fin 3) :
    0 < σ.wallSide i z := by
  have h1 := σ.abs_wallSide_sub_le i z σ.incenter
  rw [σ.wallSide_incenter] at h1
  linarith [(abs_le.1 h1).1]

theorem mem_of_near {z : ℂ} (h : ‖z - σ.incenter‖ < σ.inradius) :
    z ∈ σ.triangle ∧ (∀ i, 0 < σ.wallSide i z) ∧ z ≠ 0 ∧ z ≠ σ.vertexOne ∧
      z ≠ σ.vertexTwo :=
  ⟨fun i => (σ.wallSide_pos_of_near h i).le, σ.wallSide_pos_of_near h,
    σ.ne_of_interior (σ.wallSide_pos_of_near h)⟩

theorem wallSide_lineMap (i : Fin 3) (a b : ℂ) (s : ℝ) :
    σ.wallSide i (a + (s : ℂ) * (b - a)) = (1 - s) * σ.wallSide i a + s * σ.wallSide i b := by
  fin_cases i
  · change (a + (s : ℂ) * (b - a)).im = (1 - s) * a.im + s * b.im
    simp only [add_im, mul_im, ofReal_re, ofReal_im, sub_re, sub_im, zero_mul, add_zero]
    ring
  · change σ.wallSide 1 _ = (1 - s) * σ.wallSide 1 a + s * σ.wallSide 1 b
    simp only [wallSide_one_apply, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, sub_re,
      sub_im, zero_mul, sub_zero, add_zero]
    ring
  · change σ.wallSide 2 _ = (1 - s) * σ.wallSide 2 a + s * σ.wallSide 2 b
    simp only [wallSide_two_apply, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, sub_re,
      sub_im, zero_mul, sub_zero, add_zero]
    ring

theorem lineMap_mem {a b : ℂ} (ha : a ∈ σ.triangle) (hb : b ∈ σ.triangle) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) : a + (s : ℂ) * (b - a) ∈ σ.triangle := fun i => by
  rw [σ.wallSide_lineMap]
  have := ha i
  have := hb i
  have : 0 ≤ 1 - s := by linarith
  positivity

theorem incenter_mem : σ.incenter ∈ σ.triangle := fun i => by
  rw [σ.wallSide_incenter]
  exact σ.inradius_pos.le

theorem inradius_le_norm_incenter : σ.inradius ≤ ‖σ.incenter‖ := by
  rw [← σ.wallSide_zero_incenter, wallSide_zero_apply]
  exact le_trans (le_abs_self _) (Complex.abs_im_le_norm _)

theorem core_consts : 0 < σ.coreMargin ∧ σ.coreMargin < σ.coreRadius ∧
    σ.coreRadius + σ.coreMargin < σ.inradius := by
  have := σ.inradius_pos
  unfold coreRadius coreMargin
  refine ⟨?_, ?_, ?_⟩ <;> linarith

def coreOut : Set ℂ := {z | z ∈ σ.triangle ∧ z ≠ 0 ∧ σ.coreRadius < ‖z - σ.incenter‖}

theorem norm_lineMap_sub (c z : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    ‖c + (s : ℂ) * (z - c) - c‖ = s * ‖z - c‖ := by
  rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]

theorem isPreconnected_coreOut : IsPreconnected σ.coreOut := by
  obtain ⟨hδ, hδr, hrρ⟩ := σ.core_consts
  set c := σ.incenter with hc
  set ρ₂ := σ.coreRadius + σ.coreMargin / 2 with hρ₂
  have hρ₂r : σ.coreRadius < ρ₂ := by linarith
  have hρ₂ρ : ρ₂ < σ.inradius := by linarith
  have hnear : ∀ w : ℂ, ‖w - c‖ ≤ ρ₂ → σ.coreRadius < ‖w - c‖ → w ∈ σ.coreOut := by
    intro w hw hr
    obtain ⟨hT, -, h0, -⟩ := σ.mem_of_near (lt_of_le_of_lt hw hρ₂ρ)
    exact ⟨hT, h0, hr⟩
  have hCsub : sphere c ρ₂ ⊆ σ.coreOut := fun w hw => by
    have : ‖w - c‖ = ρ₂ := by rwa [mem_sphere_iff_norm] at hw
    exact hnear w this.le (by rw [this]; exact hρ₂r)
  have hCc : IsPreconnected (sphere c ρ₂) :=
    isPreconnected_sphere (by rw [Complex.rank_real_complex]; norm_num) c ρ₂
  have hρ₂0 : 0 < ρ₂ := by linarith
  have hx₀ : c + (ρ₂ : ℂ) ∈ sphere c ρ₂ := by
    rw [mem_sphere_iff_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hρ₂0]
  refine isPreconnected_of_forall (c + (ρ₂ : ℂ)) fun z hz => ?_
  obtain ⟨hzT, hz0, hzr⟩ := hz
  set d := ‖z - c‖ with hd
  have hd0 : 0 < d := by linarith
  set g : ℝ → ℂ := fun s => c + (s : ℂ) * (z - c) with hg
  have hk : ρ₂ / d * d = ρ₂ := div_mul_cancel₀ _ hd0.ne'
  have hsr : ∀ s ∈ uIcc 1 (ρ₂ / d), 0 ≤ s ∧ σ.coreRadius < s * d ∧
      (1 < s → s * d ≤ ρ₂) := by
    intro s hs
    rcases mem_uIcc.1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨by linarith, by nlinarith, fun _ => ?_⟩
      nlinarith
    · have h0 : 0 ≤ ρ₂ / d := div_nonneg hρ₂0.le hd0.le
      refine ⟨by linarith, ?_, fun h => absurd h (not_lt.2 h2)⟩
      have := mul_le_mul_of_nonneg_right h1 hd0.le
      rw [hk] at this
      linarith
  have hsegsub : g '' uIcc 1 (ρ₂ / d) ⊆ σ.coreOut := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨hs0, hlo, hhi⟩ := hsr s hs
    have hn := norm_lineMap_sub c z hs0
    rcases le_or_gt s 1 with hs1 | hs1
    · refine ⟨σ.lineMap_mem σ.incenter_mem hzT hs0 hs1, ?_, by rw [hn]; exact hlo⟩
      rcases hs1.lt_or_eq with hs1 | hs1
      · intro h0
        have hw := σ.wallSide_lineMap 0 c z s
        change (c + (s : ℂ) * (z - c)) = 0 at h0
        rw [h0, σ.wallSide_zero_zero, σ.wallSide_incenter] at hw
        have := hzT 0
        have := σ.inradius_pos
        nlinarith
      · change c + (s : ℂ) * (z - c) ≠ 0
        rw [hs1, ofReal_one, one_mul, add_sub_cancel]
        exact hz0
    · exact hnear _ (by rw [hn]; exact hhi hs1) (by rw [hn]; exact hlo)
  have hsegc : IsPreconnected (g '' uIcc 1 (ρ₂ / d)) :=
    isPreconnected_uIcc.image _ (by fun_prop)
  have hzseg : z ∈ g '' uIcc 1 (ρ₂ / d) := ⟨1, left_mem_uIcc, by simp [hg]⟩
  have hcseg : g (ρ₂ / d) ∈ g '' uIcc 1 (ρ₂ / d) := ⟨ρ₂ / d, right_mem_uIcc, rfl⟩
  have hcC : g (ρ₂ / d) ∈ sphere c ρ₂ := by
    rw [mem_sphere_iff_norm, hg]
    dsimp only
    rw [norm_lineMap_sub c z (div_nonneg hρ₂0.le hd0.le), ← hd, hk]
  exact ⟨_ ∪ sphere c ρ₂, union_subset hsegsub hCsub, Or.inr hx₀, Or.inl hzseg,
    hsegc.union _ hcseg hcC hCc⟩

theorem exists_foldCore : ∃ F : ℂ → ℂ, ∃ U : Set ℂ, IsOpen U ∧ (0 : ℂ) ∉ U ∧
    σ.triangle \ {0} ⊆ U ∧
    (∀ z, z ≠ 0 → z ∈ σ.goodSet → σ.coreRadius < ‖z - σ.incenter‖ → z ∈ U) ∧
    ContDiffOn ℝ ∞ F U ∧
    (∀ z ∈ U, z ≠ σ.vertexOne → z ≠ σ.vertexTwo → 0 < (fderiv ℝ F z).det) ∧
    (∀ z, σ.coreRadius ≤ ‖z - σ.incenter‖ → F z = σ.preFold z) ∧
    InjOn F (σ.triangle \ {0}) ∧ MapsTo F (σ.triangle \ {0}) basePlusSeven := by
  obtain ⟨hδ, hδr, hrρ⟩ := σ.core_consts
  have hρ := σ.inradius_pos
  have hcn := σ.inradius_le_norm_incenter
  set c := σ.incenter with hc
  set r := σ.coreRadius with hr
  set δ := σ.coreMargin with hδdef
  set E := σ.preFold with hE
  have hr0 : 0 < r := by linarith
  have hann : ∀ z : ℂ, r - δ < ‖z - c‖ → ‖z - c‖ < r + δ → z ∈ σ.triangle ∧
      (∀ i, 0 < σ.wallSide i z) ∧ z ≠ 0 ∧ z ≠ σ.vertexOne ∧ z ≠ σ.vertexTwo ∧
      z ∈ σ.goodSet := by
    intro z h1 h2
    obtain ⟨hT, hpos, h0, a1, a2⟩ := σ.mem_of_near (by linarith : ‖z - c‖ < σ.inradius)
    exact ⟨hT, hpos, h0, a1, a2, σ.mem_goodSet hT h0 h1.le⟩
  have hE' : ContDiffOn ℝ ∞ E {z | r - δ < ‖z - c‖ ∧ ‖z - c‖ < r + δ} := fun z hz => by
    obtain ⟨-, -, -, a1, a2, hg⟩ := hann z hz.1 hz.2
    exact (σ.good_preFold hg a1 a2).1.contDiffWithinAt
  have hdet : ∀ z, r - δ < ‖z - c‖ → ‖z - c‖ < r + δ → (fderiv ℝ E z).det ≠ 0 := by
    intro z h1 h2
    obtain ⟨-, -, -, a1, a2, hg⟩ := hann z h1 h2
    exact (σ.good_preFold hg a1 a2).2.ne'
  have hinjT := σ.injOn_preFold
  have hinj : InjOn E {z | r - δ < ‖z - c‖ ∧ ‖z - c‖ < r + δ} := by
    intro z hz w hw h
    obtain ⟨hT, -, h0, -⟩ := hann z hz.1 hz.2
    obtain ⟨hT', -, h0', -⟩ := hann w hw.1 hw.2
    exact hinjT ⟨hT, h0⟩ ⟨hT', h0'⟩ h
  have hsph : ∀ q ∈ sphere c r, ‖q - c‖ = r ∧ q ∈ σ.triangle ∧ q ≠ 0 ∧ ContinuousAt E q ∧
      E q ∈ openHalfSeven := by
    intro q hq
    have hq' : ‖q - c‖ = r := by rwa [mem_sphere_iff_norm] at hq
    obtain ⟨hT, hpos, h0, a1, a2, hg⟩ := hann q (by linarith) (by linarith)
    exact ⟨hq', hT, h0, (σ.good_preFold hg a1 a2).1.continuousAt,
      σ.norm_preFold_lt hT h0, σ.im_preFold_pos hT hpos⟩
  have hgoodOut : ∀ z ∈ σ.coreOut, z ∈ σ.goodSet := fun z hz =>
    σ.mem_goodSet hz.1 hz.2.1 (by linarith [hz.2.2])
  have hEcont : ContinuousOn E σ.coreOut := fun z hz =>
    (σ.contDiffAt_preFold (hgoodOut z hz)).continuousAt.continuousWithinAt
  obtain ⟨qmax, hqmax, hmax⟩ := (isCompact_sphere c r).exists_isMaxOn
    (NormedSpace.sphere_nonempty.2 hr0.le)
    (fun q hq => (hsph q hq).2.2.2.1.norm.continuousWithinAt)
  set M := ‖E qmax‖ with hM
  have hM7 : M < 7 / 2 := (hsph qmax hqmax).2.2.2.2.1
  set s := min (σ.inradius / 64) (7 / 2 - M) with hs
  have hs0 : 0 < s := lt_min (by linarith) (by linarith)
  have hsρ : s ≤ σ.inradius / 64 := min_le_left _ _
  have hsM : s ≤ 7 / 2 - M := min_le_right _ _
  have hcn0 : 0 < ‖c‖ := by linarith
  set k := s / ‖c‖ with hk
  have hk0 : 0 ≤ k := div_nonneg hs0.le hcn0.le
  have hk1 : k ≤ 1 := (div_le_one hcn0).2 (by linarith)
  have hkc : k * ‖c‖ = s := by rw [hk, div_mul_cancel₀ _ hcn0.ne']
  set zt : ℂ := 0 + (k : ℂ) * (c - 0) with hzt
  have hztT : zt ∈ σ.triangle := σ.lineMap_mem σ.zero_mem_triangle σ.incenter_mem hk0 hk1
  have hztn : ‖zt‖ = s := by
    rw [hzt, zero_add, sub_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hk0, hkc]
  have hzt0 : zt ≠ 0 := by
    intro h
    rw [h, norm_zero] at hztn
    linarith
  have hztc : r < ‖zt - c‖ := by
    have e : zt - c = ((k - 1 : ℝ) : ℂ) * c := by
      rw [hzt]
      push_cast
      ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    have hrv : r = σ.inradius - σ.inradius / 32 := rfl
    nlinarith
  have hρ1 := σ.inradius_lt_half
  have hs1 : s ≤ 1 := by linarith
  have hpow : s ^ σ.p₃ ≤ s := pow_le_of_le_one hs0.le hs1 (by have := σ.two_le_p₃; omega)
  have hEzt : E zt = compactOuterGerm σ.p₃ zt :=
    σ.preFold_eq_outer ⟨by rw [hztn]; exact hs0, by rw [hztn]; unfold outerGermRadius; linarith⟩
  have hnE : M < ‖E zt‖ := by
    rw [hEzt, norm_compactOuterGerm hzt0 (by rw [hztn]; linarith), hztn]
    linarith
  set u₀ := E zt with hu₀
  have hu0 : u₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnE
    linarith [norm_nonneg (E qmax)]
  set S := E '' σ.coreOut ∪ (fun t : ℝ => (t : ℂ) * u₀) '' Ici 1 with hSdef
  have hztout : zt ∈ σ.coreOut := ⟨hztT, hzt0, hztc⟩
  have hSc : IsPreconnected S :=
    (σ.isPreconnected_coreOut.image E hEcont).union u₀ ⟨zt, hztout, rfl⟩
      ⟨1, mem_Ici.2 le_rfl, by simp⟩ (isPreconnected_ray u₀)
  have hSb : ¬ Bornology.IsBounded S := fun hb =>
    not_isBounded_ray hu0 (hb.subset subset_union_right)
  have hSd : Disjoint S (E '' sphere c r) := by
    rw [disjoint_left]
    rintro v (⟨x, hx, hxv⟩ | hv) ⟨q, hq, hqv⟩
    · obtain ⟨hq', hqT, hq0, -⟩ := hsph q hq
      have := hinjT ⟨hx.1, hx.2.1⟩ ⟨hqT, hq0⟩ (hxv.trans hqv.symm)
      have h2 := hx.2.2
      rw [this, hq'] at h2
      exact lt_irrefl _ h2
    · have h1 := norm_ray_ge hv
      have h2 : ‖E q‖ ≤ M := hmax hq
      rw [hqv] at h2
      linarith
  set z₀ : ℂ := c + ((r + δ / 2 : ℝ) : ℂ) with hz₀
  have hz₀n : ‖z₀ - c‖ = r + δ / 2 := by
    rw [hz₀, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hout : ∃ z₀, r < ‖z₀ - c‖ ∧ ‖z₀ - c‖ < r + δ ∧ ∃ S : Set ℂ, IsPreconnected S ∧
      E z₀ ∈ S ∧ Disjoint S (E '' sphere c r) ∧ ¬ Bornology.IsBounded S := by
    obtain ⟨hT, -, h0, -⟩ := hann z₀ (by rw [hz₀n]; linarith) (by rw [hz₀n]; linarith)
    exact ⟨z₀, by rw [hz₀n]; linarith, by rw [hz₀n]; linarith, S, hSc,
      Or.inl ⟨z₀, ⟨hT, h0, by rw [hz₀n]; linarith⟩, rfl⟩, hSd, hSb⟩
  obtain ⟨Q, hQs, hQi, hQd, ⟨V, hVo, hsV, hQV⟩, hQc⟩ :=
    exists_core_replacement hδ hδr hE' hdet hinj hout
  have hQE : Q =ᶠ[𝓝 qmax] E := Filter.eventually_of_mem (hVo.mem_nhds (hsV hqmax)) hQV
  have hQpos : ∀ u, 0 < (fderiv ℝ Q u).det := by
    have hq := (hsph qmax hqmax).1
    obtain ⟨-, -, -, a1, a2, hg⟩ := hann qmax (by linarith) (by linarith)
    refine det_pos_of_ne_zero hQs hQd (u₀ := qmax) ?_
    rw [hQE.fderiv_eq]
    exact (σ.good_preFold hg a1 a2).2
  have hQball : Q '' ball c r ⊆ openHalfSeven := by
    rintro _ ⟨w, hw, rfl⟩
    by_contra hcon
    obtain ⟨S₀, hS₀, huS, hS₀d, hS₀b⟩ := outside_halfSeven hcon
    have hΓ : Disjoint S₀ (E '' sphere c r) := by
      refine disjoint_left.2 fun v hv ⟨q, hq, hqv⟩ => disjoint_left.1 hS₀d hv ?_
      rw [← hqv]
      exact (hsph q hq).2.2.2.2
    exact disjoint_left.1 (hQc S₀ hS₀ hS₀b hΓ) huS ⟨w, hw, rfl⟩
  classical
  set F : ℂ → ℂ := fun z => if ‖z - c‖ < r then Q z else E z with hFdef
  have hF1 : ∀ z, r ≤ ‖z - c‖ → F z = E z := fun z hz => by
    simp only [hFdef, not_lt.2 hz, ↓reduceIte]
  have hFQ : ∀ z, (z ∈ V ∨ ‖z - c‖ < r) → F z = Q z := by
    intro z h
    by_cases hb : ‖z - c‖ < r
    · simp only [hFdef, hb, ↓reduceIte]
    · rw [hF1 z (not_lt.1 hb)]
      rcases h with hV | hb'
      · exact (hQV hV).symm
      · exact absurd hb' hb
  set W := V ∪ ball c r with hW
  have hWo : IsOpen W := hVo.union isOpen_ball
  have hFW : ∀ z ∈ W, F z = Q z := fun z hz => hFQ z (by
    rcases hz with h | h
    · exact Or.inl h
    · exact Or.inr (by rwa [mem_ball, dist_eq_norm] at h))
  set G := {z : ℂ | r < ‖z - c‖} ∩ σ.goodSet with hG
  have hGo : IsOpen G :=
    (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter σ.isOpen_goodSet
  have hFG : ∀ z ∈ G, F z = E z := fun z hz => hF1 z hz.1.le
  have hevW : ∀ z ∈ W, F =ᶠ[𝓝 z] Q := fun z hz =>
    Filter.eventually_of_mem (hWo.mem_nhds hz) hFW
  have hevG : ∀ z ∈ G, F =ᶠ[𝓝 z] E := fun z hz =>
    Filter.eventually_of_mem (hGo.mem_nhds hz) hFG
  set U := (W ∪ G) ∩ {z | z ≠ 0} with hU
  have hUo : IsOpen U := (hWo.union hGo).inter isOpen_ne
  refine ⟨F, U, hUo, fun h => h.2 rfl, ?_, ?_, ?_, ?_, fun z hz => hF1 z hz, ?_, ?_⟩
  · rintro z ⟨hzT, hz0⟩
    refine ⟨?_, hz0⟩
    rcases lt_trichotomy ‖z - c‖ r with h | h | h
    · exact Or.inl (Or.inr (by rwa [mem_ball, dist_eq_norm]))
    · exact Or.inl (Or.inl (hsV (by rwa [mem_sphere_iff_norm])))
    · exact Or.inr ⟨h, σ.mem_goodSet hzT hz0 (by linarith)⟩
  · intro z h0 hg h
    exact ⟨Or.inr ⟨h, hg⟩, h0⟩
  · intro z hz
    rcases hz.1 with h | h
    · exact (hQs.contDiffAt.congr_of_eventuallyEq (hevW z h)).contDiffWithinAt
    · exact ((σ.contDiffAt_preFold h.2).congr_of_eventuallyEq (hevG z h)).contDiffWithinAt
  · intro z hz h1 h2
    rcases hz.1 with h | h
    · rw [(hevW z h).fderiv_eq]
      exact hQpos z
    · rw [(hevG z h).fderiv_eq]
      exact (σ.good_preFold h.2 h1 h2).2
  · have key : ∀ a b : ℂ, a ∈ σ.triangle \ {0} → b ∈ σ.triangle \ {0} → ‖a - c‖ < r →
        r ≤ ‖b - c‖ → F a = F b → False := by
      intro a b ha hb hna hnb hab
      have hFa : F a = Q a := hFQ a (Or.inr hna)
      rcases hnb.lt_or_eq with hlt | heq
      · have hbS : E b ∈ S := Or.inl ⟨b, ⟨hb.1, hb.2, hlt⟩, rfl⟩
        rw [← hF1 b hnb, ← hab, hFa] at hbS
        exact disjoint_left.1 (hQc S hSc hSb hSd) hbS
          ⟨a, by rwa [mem_ball, dist_eq_norm], rfl⟩
      · have hbV : b ∈ V := hsV (by rw [mem_sphere_iff_norm]; exact heq.symm)
        rw [hFa, hFQ b (Or.inl hbV)] at hab
        have := hQi hab
        rw [this] at hna
        linarith
    intro z hz z' hz' heq
    by_cases h1 : ‖z - c‖ < r <;> by_cases h2 : ‖z' - c‖ < r
    · rw [hFQ z (Or.inr h1), hFQ z' (Or.inr h2)] at heq
      exact hQi heq
    · exact (key z z' hz hz' h1 (not_lt.1 h2) heq).elim
    · exact (key z' z hz' hz h2 (not_lt.1 h1) heq.symm).elim
    · rw [hF1 z (not_lt.1 h1), hF1 z' (not_lt.1 h2)] at heq
      exact hinjT hz hz' heq
  · rintro z ⟨hzT, hz0⟩
    by_cases h : ‖z - c‖ < r
    · rw [hFQ z (Or.inr h)]
      have := hQball ⟨z, by rwa [mem_ball, dist_eq_norm], rfl⟩
      exact ⟨this.1, this.2.le⟩
    · rw [hF1 z (not_lt.1 h)]
      exact ⟨σ.norm_preFold_lt hzT hz0, σ.im_preFold_nonneg hzT hz0⟩

end EuclidShape

end GC.Seifert
