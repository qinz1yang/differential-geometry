import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldTwoConeRegion

/-!
# The corner at the second cone vertex, by the swap

Lane A4b3 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §5, two-cone
shapes). On the cone disc `R₂ = {η₂ < h}` at `v₂` the fold is
`regionTwoC hθ q z = -conj (coneRegion' q (W - z̄))`, the mirror `u ↦ -ū` of the cone region at
the first vertex of the swapped shape `σ' = σ.swap hθ` (angles `(θ₂, θ₁)`). Every property of
`coneRegion` on `T' ∩ R₁'` transports (`swapPt_mem_triangle`, `swap_etaOne`, `swap_sinhN`,
`swap_refl_*`, `det_fderiv_mirror`): local forms (`regionTwoC_local`), the image
`‖E - 3/2‖ = coneRadial' η₂ < G(h)` (`regionTwoC_image`), injectivity, the agreements on `∂R₂` with
`bridgeTwoC` (lens side, via `swap_bridgeTwoC`) and with `bridgeZeroC` (wall side, via
`swap_bridgeOne`), the wall identities for the reflections in walls 0 and 2, the wall values, and
the apex: near `v₂` the map is `3/2 + conj(ω₂)^q/2`, whose mirror is `coneApexTwo q`.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Set
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace ConeShape

variable (σ : ConeShape)

def regionTwoC (hθ : 0 < σ.θ₂) (q : ℕ) (z : ℂ) : ℂ :=
  -conj ((σ.swap hθ).coneRegion q (σ.swapPt z))

def apexTwoBefore (q : ℕ) (z : ℂ) : ℂ := 3 / 2 + conj (σ.discTwo z) ^ q / 2

theorem neg_conj_apexTwoBefore (q : ℕ) (z : ℂ) :
    -conj (σ.apexTwoBefore q z) = σ.coneApexTwo q z := by
  simp only [apexTwoBefore, coneApexTwo, discTwo, map_add, map_div₀, map_pow, Complex.conj_conj,
    map_ofNat]
  ring

theorem mirror_eventuallyEq {F G : ℂ → ℂ} {z₀ : ℂ} (h : F =ᶠ[𝓝 (σ.swapPt z₀)] G) :
    (fun z => -conj (F (σ.swapPt z))) =ᶠ[𝓝 z₀] (fun z => -conj (G (σ.swapPt z))) := by
  have := (σ.continuous_swapPt.tendsto z₀).eventually h
  filter_upwards [this] with w hw
  rw [hw]

theorem swapPt_ne_iff {z w : ℂ} : σ.swapPt z ≠ σ.swapPt w ↔ z ≠ w := by
  constructor
  · intro h h'; exact h (by rw [h'])
  · intro h h'; apply h; rw [← σ.swapPt_swapPt z, h', σ.swapPt_swapPt]

theorem norm_neg_conj_sub (u : ℂ) : ‖-conj u - 3 / 2‖ = ‖u + 3 / 2‖ := by
  rw [show -conj u - 3 / 2 = -conj (u + 3 / 2) by simp [map_ofNat]; ring, norm_neg,
    Complex.norm_conj]

section VertexTwo

variable (hθ : 0 < σ.θ₂) (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)
  (h₂ : Real.cos σ.θ₂ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₂)

theorem swapPt_ne_vertexOne_iff {z : ℂ} :
    σ.swapPt z ≠ (σ.swap hθ).vertexOne ↔ z ≠ σ.vertexTwo := by
  rw [σ.swap_vertexOne hθ, σ.swapPt_ne_iff]

theorem swapPt_ne_vertexTwo_iff {z : ℂ} :
    σ.swapPt z ≠ (σ.swap hθ).vertexTwo ↔ z ≠ σ.vertexOne := by
  rw [σ.swap_vertexTwo hθ, σ.swapPt_ne_iff]

theorem swap_apexBefore (q : ℕ) (z : ℂ) :
    -conj ((σ.swap hθ).apexBefore q (σ.swapPt z)) = σ.apexTwoBefore q z := by
  simp only [apexBefore, apexTwoBefore, σ.swap_discOne hθ, map_sub, map_neg, map_div₀, map_pow,
    Complex.conj_conj, map_ofNat]
  ring

include h₁ h₂ in
theorem regionTwoC_eventually_apex {q : ℕ} :
    σ.regionTwoC hθ q =ᶠ[𝓝 σ.vertexTwo] σ.apexTwoBefore q := by
  have h := (σ.swap hθ).coneRegion_eventually_apex h₂ h₁ (p := q)
  rw [σ.swap_vertexOne hθ] at h
  have := σ.mirror_eventuallyEq h
  filter_upwards [this] with w hw
  have hw' : -conj ((σ.swap hθ).coneRegion q (σ.swapPt w)) =
      -conj ((σ.swap hθ).apexBefore q (σ.swapPt w)) := hw
  rw [regionTwoC, hw', σ.swap_apexBefore hθ]

include h₁ h₂ in
theorem regionTwoC_vertexTwo {q : ℕ} (hq : q ≠ 0) : σ.regionTwoC hθ q σ.vertexTwo = 3 / 2 := by
  rw [regionTwoC, ← σ.swap_vertexOne hθ, (σ.swap hθ).coneRegion_vertexOne h₂ h₁ hq]
  simp [map_ofNat]

include hθ in
theorem contDiffAt_apexTwoBefore (q : ℕ) {z : ℂ} (hz : 0 < z.im) :
    ContDiffAt ℝ ∞ (σ.apexTwoBefore q) z := by
  have hd : ContDiffAt ℝ ∞ σ.discTwo z :=
    (contDiffAt_coneDisc (σ.vertexTwo_im_pos hθ) hz).restrict_scalars ℝ
  have hc : ContDiffAt ℝ ∞ (fun u => conj (σ.discTwo u)) z :=
    (conjCLE : ℂ →L[ℝ] ℂ).contDiff.contDiffAt.comp z hd
  exact contDiffAt_const.add ((hc.pow q).div_const 2)

include h₁ h₂ in
theorem regionTwoC_local {q : ℕ} (hq : 1 ≤ q) {z : ℂ} (hz : z ∈ σ.triangle)
    (h2 : σ.etaTwoC z ≤ σ.foldH) :
    ∃ g : ℂ → ℂ, ∃ D : Set ℂ, IsOpen D ∧ z ∈ D ∧ ContDiffOn ℝ ∞ g D ∧
      σ.regionTwoC hθ q =ᶠ[𝓝 z] g ∧ (z ≠ σ.vertexTwo → (fderiv ℝ g z).det ≠ 0) := by
  have hzT := (σ.swapPt_mem_triangle hθ).2 hz
  have h1' : (σ.swap hθ).etaOne (σ.swapPt z) ≤ (σ.swap hθ).foldH := by
    rw [σ.swap_etaOne hθ, σ.swap_foldH hθ]; exact h2
  obtain ⟨g, D, hD, hzD, hg, hEg, hdet⟩ :=
    (σ.swap hθ).coneRegion_local σ.θ₁_pos h₂ h₁ hq hzT h1'
  refine ⟨fun w => -conj (g (σ.swapPt w)), σ.swapPt ⁻¹' D,
    hD.preimage σ.continuous_swapPt, hzD, fun w hw => ?_, σ.mirror_eventuallyEq hEg, fun hzv => ?_⟩
  · exact (σ.contDiffAt_mirror (hg.contDiffAt (hD.mem_nhds (show σ.swapPt w ∈ D from hw)))
      ).contDiffWithinAt
  · rw [σ.det_fderiv_mirror ((hg.contDiffAt (hD.mem_nhds hzD)).differentiableAt (by simp))]
    exact hdet ((σ.swapPt_ne_vertexOne_iff hθ).2 hzv)

include h₁ h₂ in
theorem regionTwoC_image {q : ℕ} (hq : 1 ≤ q) (hqθ : σ.θ₂ * q = Real.pi) {z : ℂ}
    (hz : z ∈ σ.triangle) (h2 : σ.etaTwoC z < σ.foldH) :
    ‖σ.regionTwoC hθ q z - 3 / 2‖ = coneRadial q (σ.swap hθ).foldA₁ (σ.swap hθ).foldB₁
        σ.vertexTwo.im σ.constK (σ.etaTwoC z) ∧
      ‖σ.regionTwoC hθ q z - 3 / 2‖ < coneProfile σ.constK σ.foldH ∧
        0 ≤ (σ.regionTwoC hθ q z).im := by
  have hzT := (σ.swapPt_mem_triangle hθ).2 hz
  have h1' : (σ.swap hθ).etaOne (σ.swapPt z) < (σ.swap hθ).foldH := by
    rw [σ.swap_etaOne hθ, σ.swap_foldH hθ]; exact h2
  obtain ⟨e1, e2, e3⟩ := (σ.swap hθ).coneRegion_image σ.θ₁_pos h₂ h₁ hq hqθ hzT h1'
  rw [σ.swap_etaOne hθ, σ.swap_constK hθ, σ.swap_vertexOne_im] at e1
  rw [σ.swap_constK hθ, σ.swap_foldH hθ] at e2
  refine ⟨?_, ?_, ?_⟩
  · rw [regionTwoC, norm_neg_conj_sub, e1]
  · rw [regionTwoC, norm_neg_conj_sub]; exact e2
  · rw [regionTwoC, neg_im, conj_im, neg_neg]; exact e3

include h₁ h₂ in
theorem regionTwoC_injective {q : ℕ} (hq : 1 ≤ q) (hqθ : σ.θ₂ * q = Real.pi) {z z' : ℂ}
    (hz : z ∈ σ.triangle) (hz' : z' ∈ σ.triangle) (h2 : σ.etaTwoC z < σ.foldH)
    (h2' : σ.etaTwoC z' < σ.foldH) (heq : σ.regionTwoC hθ q z = σ.regionTwoC hθ q z') :
    z = z' := by
  have h1 : (σ.swap hθ).etaOne (σ.swapPt z) < (σ.swap hθ).foldH := by
    rw [σ.swap_etaOne hθ, σ.swap_foldH hθ]; exact h2
  have h1' : (σ.swap hθ).etaOne (σ.swapPt z') < (σ.swap hθ).foldH := by
    rw [σ.swap_etaOne hθ, σ.swap_foldH hθ]; exact h2'
  have heq' : (σ.swap hθ).coneRegion q (σ.swapPt z) = (σ.swap hθ).coneRegion q (σ.swapPt z') := by
    rw [regionTwoC, regionTwoC, neg_inj] at heq
    exact (starRingEnd ℂ).injective heq
  have := (σ.swap hθ).coneRegion_injective σ.θ₁_pos h₂ h₁ hq hqθ
    ((σ.swapPt_mem_triangle hθ).2 hz) ((σ.swapPt_mem_triangle hθ).2 hz') h1 h1' heq'
  rw [← σ.swapPt_swapPt z, this, σ.swapPt_swapPt]

include hθ h₁ h₂ in
theorem ne_vertices_of_etaTwoC_eq {z : ℂ} (hz : 0 < z.im) (he : σ.etaTwoC z = σ.foldH) :
    z ≠ σ.vertexOne ∧ z ≠ σ.vertexTwo := by
  constructor
  · rintro rfl
    have := σ.foldH_lt_etaTwoC_of_etaOne_le hθ hz
      (by rw [σ.etaOne_vertexOne]; exact (σ.vertexOne_im_lt_foldH h₁ h₂).le)
    linarith
  · rintro rfl
    have h0 : σ.etaTwoC σ.vertexTwo = σ.vertexTwo.im := by
      simp [etaTwoC, coneHeight, coneDisc_self]
    have := σ.vertexTwo_im_lt_foldH hθ h₁ h₂
    linarith

include h₁ h₂ in
theorem regionTwoC_eventually_bridgeTwoC {q : ℕ} {z : ℂ} (hz : z ∈ σ.triangle)
    (he : σ.etaTwoC z = σ.foldH) (hs : σ.sinhN z < 1 / 10) :
    σ.regionTwoC hθ q =ᶠ[𝓝 z] σ.bridgeTwoC := by
  have hzT := (σ.swapPt_mem_triangle hθ).2 hz
  have he' : (σ.swap hθ).etaOne (σ.swapPt z) = (σ.swap hθ).foldH := by
    rw [σ.swap_etaOne hθ, σ.swap_foldH hθ]; exact he
  have hs' : (σ.swap hθ).sinhN (σ.swapPt z) < 1 / 10 := by rw [σ.swap_sinhN hθ]; exact hs
  have h := (σ.swap hθ).coneRegion_eventually_bridgeTwoC σ.θ₁_pos h₂ h₁ (p := q) hzT he' hs'
  have hm := σ.mirror_eventuallyEq h
  obtain ⟨hv1, hv2⟩ := σ.ne_vertices_of_etaTwoC_eq hθ h₁ h₂ hz.1 he
  have hd := σ.mem_domTwoC_of_mem_triangle hθ hz hv1 hv2
  have hd' := σ.swap_mem_domTwoC_of_mem_triangle hθ hz hv1 hv2
  have hdo : ∀ᶠ w in 𝓝 z, σ.swapPt w ∈ (σ.swap hθ).domTwoC :=
    σ.continuous_swapPt.continuousAt.preimage_mem_nhds
      (((σ.swap hθ).isOpen_domTwoC σ.θ₁_pos).mem_nhds hd')
  filter_upwards [hm, (σ.isOpen_domTwoC hθ).mem_nhds hd, hdo] with w hw hwd hwd'
  have hw' : -conj ((σ.swap hθ).coneRegion q (σ.swapPt w)) =
      -conj ((σ.swap hθ).bridgeTwoC (σ.swapPt w)) := hw
  rw [regionTwoC, hw', σ.swap_bridgeTwoC hθ hwd hwd', map_neg, Complex.conj_conj, neg_neg]

include h₁ h₂ in
theorem regionTwoC_eventually_bridgeZeroC {q : ℕ} {z : ℂ} (hz : z ∈ σ.triangle)
    (he : σ.etaTwoC z = σ.foldH) (hs : 7 / 50 < σ.sinhN z) :
    σ.regionTwoC hθ q =ᶠ[𝓝 z] σ.bridgeZeroC := by
  have hzT := (σ.swapPt_mem_triangle hθ).2 hz
  have he' : (σ.swap hθ).etaOne (σ.swapPt z) = (σ.swap hθ).foldH := by
    rw [σ.swap_etaOne hθ, σ.swap_foldH hθ]; exact he
  have hs' : 7 / 50 < (σ.swap hθ).sinhN (σ.swapPt z) := by rw [σ.swap_sinhN hθ]; exact hs
  have h := (σ.swap hθ).coneRegion_eventually_bridgeOne h₂ h₁ (p := q) hzT he' hs'
  have hm := σ.mirror_eventuallyEq h
  filter_upwards [hm] with w hw
  have hw' : -conj ((σ.swap hθ).coneRegion q (σ.swapPt w)) =
      -conj ((σ.swap hθ).bridgeOne (σ.swapPt w)) := hw
  rw [regionTwoC, hw', σ.swap_bridgeOne hθ, map_neg, Complex.conj_conj, neg_neg]

include h₁ h₂ in
theorem regionTwoC_refl_zero {q : ℕ} (z : ℂ)
    (h : σ.etaTwoC z < (σ.swap hθ).foldA₁ ∨
      |discAngle (σ.discTwo z)| < (σ.swap hθ).foldPhiA) :
    σ.regionTwoC hθ q (σ.refl 0 z) = conj (σ.regionTwoC hθ q z) := by
  have h' : (σ.swap hθ).etaOne (σ.swapPt z) < (σ.swap hθ).foldA₁ ∨
      |discAngle ((σ.swap hθ).discOne (σ.swapPt z))| < (σ.swap hθ).foldPhiA := by
    rw [σ.swap_etaOne hθ, σ.swap_discAngle hθ, abs_neg]; exact h
  have := (σ.swap hθ).coneRegion_refl_one h₂ h₁ (p := q) (σ.swapPt z) h'
  rw [σ.swap_refl_one hθ] at this
  rw [regionTwoC, regionTwoC, this, map_neg]

include h₁ h₂ in
theorem regionTwoC_refl_two {q : ℕ} (hqθ : σ.θ₂ * q = Real.pi) {z : ℂ} (hz : 0 < z.im)
    (h : σ.etaTwoC z < (σ.swap hθ).foldA₁ ∨ (σ.swapPt z ∈ (σ.swap hθ).domOne ∧
      (σ.swap hθ).foldPhiB ≤ discAngle ((σ.swap hθ).discOne (σ.swapPt z)) ∧
      (σ.swap hθ).foldPhiB ≤ 2 * σ.θ₂ - discAngle ((σ.swap hθ).discOne (σ.swapPt z)))) :
    σ.regionTwoC hθ q (σ.refl 2 z) = conj (σ.regionTwoC hθ q z) := by
  have h' : (σ.swap hθ).etaOne (σ.swapPt z) < (σ.swap hθ).foldA₁ ∨
      (σ.swapPt z ∈ (σ.swap hθ).domOne ∧
        (σ.swap hθ).foldPhiB ≤ discAngle ((σ.swap hθ).discOne (σ.swapPt z)) ∧
        (σ.swap hθ).foldPhiB ≤ 2 * (σ.swap hθ).θ₁ -
          discAngle ((σ.swap hθ).discOne (σ.swapPt z))) := by
    rw [σ.swap_etaOne hθ]; exact h
  have := (σ.swap hθ).coneRegion_refl_two h₂ h₁ (p := q) hqθ (by simpa using hz) h'
  rw [σ.swap_refl_two hθ hz] at this
  rw [regionTwoC, regionTwoC, this, map_neg]

include h₁ h₂ in
theorem regionTwoC_wall_zero {q : ℕ} (hq : 1 ≤ q) {z : ℂ} (hz : z ∈ σ.triangle)
    (hx : z.re = 0) (h2 : σ.etaTwoC z < σ.foldH) : 3 / 2 ≤ (σ.regionTwoC hθ q z).re := by
  have hzT := (σ.swapPt_mem_triangle hθ).2 hz
  have h1' : (σ.swap hθ).etaOne (σ.swapPt z) < (σ.swap hθ).foldH := by
    rw [σ.swap_etaOne hθ, σ.swap_foldH hθ]; exact h2
  have hx' : (σ.swapPt z).re = (σ.swap hθ).width := by
    rw [swapPt_re, hx, sub_zero, σ.swap_width hθ]
  have := (σ.swap hθ).coneRegion_wall_one h₂ h₁ hq hzT hx' h1'
  rw [regionTwoC, neg_re, conj_re]
  linarith

include h₁ h₂ in
theorem regionTwoC_wall_two {q : ℕ} (hq : 1 ≤ q) (hqθ : σ.θ₂ * q = Real.pi) {z : ℂ}
    (hz : z ∈ σ.triangle) (hw : σ.wallSide 2 z = 0) (h2 : σ.etaTwoC z < σ.foldH) :
    -(3 / 2) ≤ (σ.regionTwoC hθ q z).re ∧ (σ.regionTwoC hθ q z).re ≤ 3 / 2 := by
  have hzT := (σ.swapPt_mem_triangle hθ).2 hz
  have h1' : (σ.swap hθ).etaOne (σ.swapPt z) < (σ.swap hθ).foldH := by
    rw [σ.swap_etaOne hθ, σ.swap_foldH hθ]; exact h2
  have hw' : (σ.swap hθ).wallSide 2 (σ.swapPt z) = 0 := by rw [σ.swap_wallSide_two hθ]; exact hw
  have := (σ.swap hθ).coneRegion_wall_two h₂ h₁ hq hqθ hzT hw' h1'
  rw [regionTwoC, neg_re, conj_re]
  constructor <;> linarith [this.1, this.2]

end VertexTwo

end ConeShape

end GC.Seifert
