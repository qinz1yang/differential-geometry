import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsCornerGeometry
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsFoldTopology
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsCornerInf
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsCornerZero

/-!
# Local form, smoothness and Jacobian of the K16f fold outside the core disc

Packet K16f, tier 2. Near every point `z` of the upper half-plane outside the closed disc
`(x - 1/4)² + (y - 37/100)² ≤ (12/125)²` the fold `foldMap` coincides with one of the explicit
maps `cornerZero`, `cornerHalf`, `bridgeTwo`, `cornerInf` (`foldMap_local`): on the horocycle
`heightOne = 3/5` all branches agree by `horocycle_zero_cases` (either all equal `bridgeZero`,
or all equal `bridgeTwo`), the boundary of the lens meets the region only inside the core disc
or inside a horoball (`lens_arc_inside`, `lens_boundary_heightHalf`), and the cusp `1/2` follows
by the mirror symmetry `foldMap_foldMirror`. Hence `foldMap` is smooth there with nonzero
Jacobian determinant (`contDiffAt_foldMap`, `det_fderiv_foldMap_ne_zero`).
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff Topology

namespace GC.Seifert

theorem normSq_sub_half_lt_iff {w : ℂ} (hw : 0 < w.im) :
    Complex.normSq (w - 1 / 2) < 1 / 4 ↔ holeX w.re w.im < -(1 / 4) := by
  have hs : 0 < w.re ^ 2 + w.im ^ 2 := by positivity
  rw [Complex.normSq_apply, holeX, div_lt_iff₀ (by positivity)]
  simp only [Complex.sub_re, Complex.sub_im]
  norm_num
  constructor <;> intro h <;> nlinarith

theorem normSq_lt_iff_holeX_half {w : ℂ} (hw : 0 < w.im) :
    Complex.normSq w < 1 / 4 ↔ holeX (1 / 2 - w.re) w.im < -(1 / 4) := by
  have hs : 0 < (1 / 2 - w.re) ^ 2 + w.im ^ 2 := by positivity
  rw [Complex.normSq_apply, holeX, div_lt_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith

theorem continuousAt_heightOne {z : ℂ} (hz : 0 < z.im) :
    ContinuousAt (fun w : ℂ => heightOne w.re w.im) z := by
  unfold heightOne
  have hre : Continuous fun w : ℂ => w.re := Complex.continuous_re
  have him : Continuous fun w : ℂ => w.im := Complex.continuous_im
  have h : 4 * (z.re ^ 2 + z.im ^ 2) ≠ 0 := by positivity
  fun_prop (disch := exact h)

theorem continuousAt_heightHalf {z : ℂ} (hz : 0 < z.im) :
    ContinuousAt (fun w : ℂ => heightOne (1 / 2 - w.re) w.im) z := by
  unfold heightOne
  have hre : Continuous fun w : ℂ => w.re := Complex.continuous_re
  have him : Continuous fun w : ℂ => w.im := Complex.continuous_im
  have h : 4 * ((1 / 2 - z.re) ^ 2 + z.im ^ 2) ≠ 0 := by positivity
  fun_prop (disch := exact h)

theorem continuousAt_holeX {z : ℂ} (hz : 0 < z.im) :
    ContinuousAt (fun w : ℂ => holeX w.re w.im) z := by
  unfold holeX
  have hre : Continuous fun w : ℂ => w.re := Complex.continuous_re
  have him : Continuous fun w : ℂ => w.im := Complex.continuous_im
  have h : 4 * (z.re ^ 2 + z.im ^ 2) ≠ 0 := by positivity
  fun_prop (disch := exact h)

theorem continuous_wallTwo : Continuous fun w : ℂ => wallTwo w.re w.im := by
  unfold wallTwo
  fun_prop

theorem foldLens_foldMirror (z : ℂ) : foldLens (foldMirror z) ↔ foldLens z := by
  have h1 : Complex.normSq (foldMirror z) = Complex.normSq (z - 1 / 2) := by
    rw [Complex.normSq_apply, Complex.normSq_apply, foldMirror_re, foldMirror_im]
    simp only [Complex.sub_re, Complex.sub_im]
    norm_num
    ring
  have h2 : Complex.normSq (foldMirror z - 1 / 2) = Complex.normSq z := by
    rw [Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, foldMirror_re, foldMirror_im]
    norm_num
  unfold foldLens
  rw [foldMirror_re, foldMirror_im, wallTwo_mirror, h1, h2]
  tauto

theorem heightOne_foldMirror (z : ℂ) :
    heightOne (foldMirror z).re (foldMirror z).im = heightOne (1 / 2 - z.re) z.im := by
  rw [foldMirror_re, foldMirror_im]

theorem heightHalf_foldMirror (z : ℂ) :
    heightOne (1 / 2 - (foldMirror z).re) (foldMirror z).im = heightOne z.re z.im := by
  rw [foldMirror_re, foldMirror_im, sub_sub_cancel]

theorem foldMap_foldMirror {z : ℂ} (hz : 0 < z.im) :
    foldMap (foldMirror z) = -(starRingEnd ℂ) (foldMap z) := by
  by_cases h0 : 3 / 5 < heightOne z.re z.im
  · have hh := heightHalf_lt_of_heightOne (x := z.re) hz (by linarith)
    rw [foldMap_of_heightOne h0, foldMap_of_heightHalf (by rw [heightOne_foldMirror]; linarith)
      (by rw [heightHalf_foldMirror]; exact h0), cornerHalf, foldMirror_foldMirror]
  · by_cases hh : 3 / 5 < heightOne (1 / 2 - z.re) z.im
    · rw [foldMap_of_heightHalf h0 hh,
        foldMap_of_heightOne (by rw [heightOne_foldMirror]; exact hh), cornerHalf]
      simp
    · by_cases hl : foldLens z
      · rw [foldMap_of_lens h0 hh hl, foldMap_of_lens (by rw [heightOne_foldMirror]; exact hh)
          (by rw [heightHalf_foldMirror]; exact h0) ((foldLens_foldMirror z).2 hl)]
        exact bridgeTwo_mirror z
      · rw [foldMap_of_not_lens h0 hh hl, foldMap_of_not_lens
          (by rw [heightOne_foldMirror]; exact hh) (by rw [heightHalf_foldMirror]; exact h0)
          (fun h => hl ((foldLens_foldMirror z).1 h))]
        exact cornerInf_foldMirror z

theorem continuous_foldMirror : Continuous foldMirror := by
  unfold foldMirror
  fun_prop

theorem eventuallyEq_of_foldMirror {Φ Ψ : ℂ → ℂ} {z : ℂ} (hz : 0 < z.im)
    (h : foldMap =ᶠ[𝓝 (foldMirror z)] Φ)
    (hΨ : ∀ w, Ψ w = -(starRingEnd ℂ) (Φ (foldMirror w))) : foldMap =ᶠ[𝓝 z] Ψ := by
  have ht : Filter.Tendsto foldMirror (𝓝 z) (𝓝 (foldMirror z)) :=
    continuous_foldMirror.continuousAt
  have h1 := ht.eventually h
  have h2 : ∀ᶠ w in 𝓝 z, 0 < w.im := Complex.continuous_im.continuousAt.eventually (lt_mem_nhds hz)
  filter_upwards [h1, h2] with w hw hwi
  rw [hΨ, ← hw, foldMap_foldMirror hwi]
  simp

theorem foldMap_local_of_heightOne {z : ℂ} (hz : 0 < z.im)
    (hout : (12 / 125) ^ 2 < (z.re - 1 / 4) ^ 2 + (z.im - 37 / 100) ^ 2)
    (h : 3 / 5 ≤ heightOne z.re z.im) :
    (599 / 1000 < heightOne z.re z.im ∧ foldMap =ᶠ[𝓝 z] cornerZero) ∨
      foldMap =ᶠ[𝓝 z] bridgeTwo ∨ foldMap =ᶠ[𝓝 z] cornerInf := by
  have him : ∀ᶠ w in 𝓝 z, 0 < w.im :=
    Complex.continuous_im.continuousAt.eventually (lt_mem_nhds hz)
  have hh0 : heightOne (1 / 2 - z.re) z.im < 599 / 1000 :=
    heightHalf_lt_of_heightOne hz (by linarith)
  have hhn : ∀ᶠ w in 𝓝 z, heightOne (1 / 2 - w.re) w.im < 3 / 5 :=
    (continuousAt_heightHalf hz).eventually (gt_mem_nhds (by linarith))
  have h0n : ∀ᶠ w in 𝓝 z, 599 / 1000 < heightOne w.re w.im :=
    (continuousAt_heightOne hz).eventually (lt_mem_nhds (by linarith))
  rcases lt_or_eq_of_le h with hlt | heq
  · left
    refine ⟨by linarith, ?_⟩
    filter_upwards [(continuousAt_heightOne hz).eventually (lt_mem_nhds hlt)] with w hw
    exact foldMap_of_heightOne hw
  rcases horocycle_zero_cases hz heq.symm hout with ⟨hX, hx, hy, hw⟩ | ⟨hX, hw, hX'⟩
  · right; right
    have hXn : ∀ᶠ w in 𝓝 z, -(31 / 100) < holeX w.re w.im :=
      (continuousAt_holeX hz).eventually (lt_mem_nhds (by linarith))
    have hxn : ∀ᶠ w in 𝓝 z, w.re < 23 / 100 :=
      Complex.continuous_re.continuousAt.eventually (gt_mem_nhds (by linarith))
    have hyn : ∀ᶠ w in 𝓝 z, w.im < 12 / 25 :=
      Complex.continuous_im.continuousAt.eventually (gt_mem_nhds (by linarith))
    have hln : ∀ᶠ w in 𝓝 z, ¬ foldLens w := by
      rcases hw with hw | hw
      · filter_upwards [continuous_wallTwo.continuousAt.eventually (lt_mem_nhds
          (show (1 / 25 : ℝ) < wallTwo z.re z.im by linarith))] with w hw' hl
        exact absurd hl.1 (not_lt.2 hw'.le)
      · filter_upwards [(continuousAt_holeX hz).eventually (lt_mem_nhds hw), him] with w hw' hwi hl
        exact absurd ((normSq_sub_half_lt_iff hwi).1 hl.2.2) (not_lt.2 hw'.le)
    filter_upwards [him, hhn, h0n, hXn, hxn, hyn, hln] with w hwi hwh hw0 hwX hwx hwy hwl
    by_cases h0w : 3 / 5 < heightOne w.re w.im
    · rw [foldMap_of_heightOne h0w, cornerZero_eq_bridgeZero hwi hw0 hwX.le,
        cornerInf_eq_bridgeZero hwi hwx.le hwy.le]
    · exact foldMap_of_not_lens h0w (not_lt.2 hwh.le) hwl
  · right; left
    have hXn : ∀ᶠ w in 𝓝 z, holeX w.re w.im < -(35 / 100) :=
      (continuousAt_holeX hz).eventually (gt_mem_nhds (by linarith))
    have hwn : ∀ᶠ w in 𝓝 z, wallTwo w.re w.im < 1 / 25 :=
      continuous_wallTwo.continuousAt.eventually (gt_mem_nhds (by linarith))
    have hns : Complex.normSq z < 1 / 4 := by
      have hs : 0 < z.re ^ 2 + z.im ^ 2 := by positivity
      have e1 : z.re ^ 2 + z.im ^ 2 = 5 / 12 * z.im := by
        have := heq
        unfold heightOne at this
        field_simp at this
        linarith
      rw [Complex.normSq_apply]
      nlinarith
    have hnn : ∀ᶠ w in 𝓝 z, Complex.normSq w < 1 / 4 :=
      Complex.continuous_normSq.continuousAt.eventually (gt_mem_nhds hns)
    filter_upwards [him, hhn, hXn, hwn, hnn] with w hwi hwh hwX hww hwn
    by_cases h0w : 3 / 5 < heightOne w.re w.im
    · rw [foldMap_of_heightOne h0w, cornerZero_eq_bridgeTwo hwi hwX.le]
    · exact foldMap_of_lens h0w (not_lt.2 hwh.le) ⟨hww, hwn,
        (normSq_sub_half_lt_iff hwi).2 (by linarith)⟩

theorem foldMap_local {z : ℂ} (hz : 0 < z.im)
    (hout : (12 / 125) ^ 2 < (z.re - 1 / 4) ^ 2 + (z.im - 37 / 100) ^ 2) :
    (599 / 1000 < heightOne z.re z.im ∧ foldMap =ᶠ[𝓝 z] cornerZero) ∨
      (599 / 1000 < heightOne (1 / 2 - z.re) z.im ∧ foldMap =ᶠ[𝓝 z] cornerHalf) ∨
        foldMap =ᶠ[𝓝 z] bridgeTwo ∨ foldMap =ᶠ[𝓝 z] cornerInf := by
  by_cases h0 : 3 / 5 ≤ heightOne z.re z.im
  · rcases foldMap_local_of_heightOne hz hout h0 with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  by_cases hh : 3 / 5 ≤ heightOne (1 / 2 - z.re) z.im
  · have hMz : 0 < (foldMirror z).im := by rw [foldMirror_im]; exact hz
    have hMout : (12 / 125) ^ 2 < ((foldMirror z).re - 1 / 4) ^ 2 +
        ((foldMirror z).im - 37 / 100) ^ 2 := by
      rw [foldMirror_re, foldMirror_im]
      nlinarith
    rcases foldMap_local_of_heightOne hMz hMout (by rw [heightOne_foldMirror]; exact hh) with
      ⟨h1, h2⟩ | h | h
    · refine Or.inr (Or.inl ⟨by rw [← heightOne_foldMirror]; exact h1, ?_⟩)
      exact eventuallyEq_of_foldMirror hz h2 fun w => rfl
    · refine Or.inr (Or.inr (Or.inl ?_))
      refine eventuallyEq_of_foldMirror hz h fun w => ?_
      rw [foldMirror, bridgeTwo_mirror]
      simp
    · refine Or.inr (Or.inr (Or.inr ?_))
      refine eventuallyEq_of_foldMirror hz h fun w => ?_
      rw [cornerInf_foldMirror]
      simp
  push Not at h0 hh
  have h0n : ∀ᶠ w in 𝓝 z, ¬ 3 / 5 < heightOne w.re w.im :=
    ((continuousAt_heightOne hz).eventually (gt_mem_nhds h0)).mono fun w hw => not_lt.2 hw.le
  have hhn : ∀ᶠ w in 𝓝 z, ¬ 3 / 5 < heightOne (1 / 2 - w.re) w.im :=
    ((continuousAt_heightHalf hz).eventually (gt_mem_nhds hh)).mono fun w hw => not_lt.2 hw.le
  have hns : Complex.normSq z = z.re ^ 2 + z.im ^ 2 := by rw [Complex.normSq_apply]; ring
  have hns' : Complex.normSq (z - 1 / 2) = (z.re - 1 / 2) ^ 2 + z.im ^ 2 := by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    norm_num
    ring
  by_cases hin : wallTwo z.re z.im < 1 / 25 ∧ Complex.normSq z < 1 / 4 ∧
      Complex.normSq (z - 1 / 2) < 1 / 4
  · refine Or.inr (Or.inr (Or.inl ?_))
    have hl : ∀ᶠ w in 𝓝 z, foldLens w :=
      (continuous_wallTwo.continuousAt.eventually (gt_mem_nhds hin.1)).and
        ((Complex.continuous_normSq.continuousAt.eventually (gt_mem_nhds hin.2.1)).and
          ((Complex.continuous_normSq.comp
            (continuous_id.sub continuous_const)).continuousAt.eventually
              (gt_mem_nhds hin.2.2)))
    filter_upwards [h0n, hhn, hl] with w hw0 hwh hwl
    exact foldMap_of_lens hw0 hwh hwl
  · refine Or.inr (Or.inr (Or.inr ?_))
    have hout' : 1 / 25 < wallTwo z.re z.im ∨ 1 / 4 < Complex.normSq z ∨
        1 / 4 < Complex.normSq (z - 1 / 2) := by
      by_contra hc
      push Not at hc
      obtain ⟨hw, hn1, hn2⟩ := hc
      rcases lt_or_eq_of_le hn1 with hn1 | hn1
      · rcases lt_or_eq_of_le hn2 with hn2 | hn2
        · rcases lt_or_eq_of_le hw with hw | hw
          · exact hin ⟨hw, hn1, hn2⟩
          · have := lens_arc_inside hz hw (by rw [← hns]; exact hn1) (by rw [← hns']; exact hn2)
              h0.le hh.le
            linarith
        · have hq : (1 / 2 - z.re) ^ 2 + z.im ^ 2 = 1 / 4 := by rw [← hn2, hns']; ring
          have := lens_boundary_heightHalf hz hq (by rw [wallTwo_mirror]; exact hw)
          rw [sub_sub_cancel] at this
          linarith
      · have := lens_boundary_heightHalf hz (by rw [← hn1, hns]) hw
        linarith
    have hl : ∀ᶠ w in 𝓝 z, ¬ foldLens w := by
      rcases hout' with h1 | h1 | h1
      · filter_upwards [continuous_wallTwo.continuousAt.eventually (lt_mem_nhds h1)] with w hw hl
        exact absurd hl.1 (not_lt.2 hw.le)
      · filter_upwards [Complex.continuous_normSq.continuousAt.eventually (lt_mem_nhds h1)]
          with w hw hl
        exact absurd hl.2.1 (not_lt.2 hw.le)
      · filter_upwards [(Complex.continuous_normSq.comp
          (continuous_id.sub continuous_const)).continuousAt.eventually (lt_mem_nhds h1)]
          with w hw hl
        exact absurd hl.2.2 (not_lt.2 hw.le)
    filter_upwards [h0n, hhn, hl] with w hw0 hwh hwl
    exact foldMap_of_not_lens hw0 hwh hwl

theorem contDiffAt_foldMap {z : ℂ} (hz : 0 < z.im)
    (hout : (12 / 125) ^ 2 < (z.re - 1 / 4) ^ 2 + (z.im - 37 / 100) ^ 2) :
    ContDiffAt ℝ ∞ foldMap z := by
  rcases foldMap_local hz hout with ⟨h1, h⟩ | ⟨h1, h⟩ | h | h
  · exact (contDiffAt_cornerZero hz h1).congr_of_eventuallyEq h
  · exact (contDiffAt_cornerHalf hz h1).congr_of_eventuallyEq h
  · exact (contDiffAt_bridgeTwo hz).congr_of_eventuallyEq h
  · exact (contDiffAt_cornerInf hz).congr_of_eventuallyEq h

theorem det_fderiv_foldMap_ne_zero {z : ℂ} (hz : 0 < z.im)
    (hout : (12 / 125) ^ 2 < (z.re - 1 / 4) ^ 2 + (z.im - 37 / 100) ^ 2) :
    (fderiv ℝ foldMap z).det ≠ 0 := by
  rcases foldMap_local hz hout with ⟨h1, h⟩ | ⟨h1, h⟩ | h | h
  · rw [h.fderiv_eq]; exact det_fderiv_cornerZero_ne_zero hz h1
  · rw [h.fderiv_eq]; exact det_fderiv_cornerHalf_ne_zero hz h1
  · rw [h.fderiv_eq]; exact det_fderiv_bridgeTwo_ne_zero hz
  · rw [h.fderiv_eq]; exact det_fderiv_cornerInf_ne_zero hz

end GC.Seifert
