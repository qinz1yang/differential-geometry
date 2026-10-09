import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldTwoConeSwap
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldOneConeFoldData

/-!
# The cone region at `v₁` of a two-cone shape

Lane A4b3 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §5–§6, two-cone
shapes). On the cone disc `R₁ = {η₁ < h}` the fold is `coneRegion p`: the apex model
`apexBefore p` on the apex zone `η₁ < foldA₁`, the corner `cornerConeC` elsewhere. For a shape with
a second cone (`θ₂ > 0`, admissible) this file proves, on `T ∩ R₁`:
* `R₁` is disjoint from `R₂ = {η₂ < h}` and lies in `‖ω₁‖ < t`, hence in the domain of the
  two-cone bridge (`foldH_lt_etaTwoC_of_etaOne_le`, `norm_discOne_lt_tCone`);
* the local forms (`coneRegion_local`: smooth with nonzero Jacobian off `v₁`), the image
  (`coneRegion_image`: `‖E + 3/2‖ = coneRadial η₁ < G(h)`, `Im E ≥ 0`), injectivity
  (`coneRegion_injective`), the agreements on `∂R₁` with the wall-2 bridge on the lens side and
  with the wall-1 bridge on the wall side (`coneRegion_eventually_bridgeTwoC`,
  `coneRegion_eventually_bridgeOne`), the wall identities (`coneRegion_refl_one`,
  `coneRegion_refl_two`) and the wall values (`coneRegion_wall_one`, `coneRegion_wall_two`).
Applied to the swapped shape these give the same statements at `v₂`.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Set
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace ConeShape

variable (σ : ConeShape)

def coneRegion (p : ℕ) (z : ℂ) : ℂ :=
  if σ.etaOne z < σ.foldA₁ then σ.apexBefore p z
  else σ.cornerConeC p σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB z

section Region

variable (hθ : 0 < σ.θ₂) (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)
  (h₂ : Real.cos σ.θ₂ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₂)

include hθ h₁ h₂ in
theorem vertexTwo_im_lt_foldH : σ.vertexTwo.im < σ.foldH := by
  have hw := (ConeLayout.window_before_wallTwo σ hθ h₁ h₂).1
  have hv := σ.vertexTwo_im_pos hθ
  have hH := σ.foldH_pos
  have hK := σ.constK_pos
  have hsq : σ.vertexTwo.im ^ 2 < σ.foldH ^ 2 := by
    rw [σ.vertexTwo_im_sq, σ.foldH_sq]
    nlinarith
  nlinarith

include hθ in
theorem foldH_lt_etaTwoC_of_etaOne_le {z : ℂ} (hz : 0 < z.im) (h : σ.etaOne z ≤ σ.foldH) :
    σ.foldH < σ.etaTwoC z := by
  have hK := σ.constK_le_coneHeight_mul hθ hz
  have h0 := σ.etaOne_pos hz
  have hH := σ.foldH_pos
  have hs := σ.sqrt_constK_pos
  have hKs : σ.constK = Real.sqrt σ.constK ^ 2 := (Real.sq_sqrt σ.constK_pos.le).symm
  change σ.constK ≤ σ.etaOne z * σ.etaTwoC z at hK
  unfold foldH at h ⊢
  by_contra hle
  push Not at hle
  have : σ.etaOne z * σ.etaTwoC z ≤ 20 / 21 * Real.sqrt σ.constK *
      (20 / 21 * Real.sqrt σ.constK) :=
    mul_le_mul h hle (σ.etaTwoC_pos hθ hz).le (by positivity)
  nlinarith

include hθ in
theorem foldH_lt_etaOne_of_etaTwoC_le {z : ℂ} (hz : 0 < z.im) (h : σ.etaTwoC z ≤ σ.foldH) :
    σ.foldH < σ.etaOne z := by
  by_contra hle
  push Not at hle
  have := σ.foldH_lt_etaTwoC_of_etaOne_le hθ hz hle
  linarith

include hθ h₁ h₂ in
theorem norm_discOne_lt_tCone {z : ℂ} (hz : 0 < z.im) (h : σ.etaOne z ≤ σ.foldH) :
    ‖σ.discOne z‖ < σ.tCone := by
  have hv1 := σ.vertexOne_im_pos
  have hv2 := σ.vertexTwo_im_pos hθ
  have ht1 := σ.tCone_lt_one hθ
  have hr1 := σ.norm_discOne_lt_one hz
  have hK := σ.constK_eq_cones hθ
  change σ.constK = σ.vertexOne.im * σ.vertexTwo.im * (1 + σ.tCone) / (1 - σ.tCone) at hK
  have hvH := σ.vertexTwo_im_lt_foldH hθ h₁ h₂
  have hHs := σ.foldH_lt_sqrt
  have hH := σ.foldH_pos
  have hsK : Real.sqrt σ.constK ^ 2 = σ.constK := Real.sq_sqrt σ.constK_pos.le
  have hη : σ.etaOne z = σ.vertexOne.im * (1 + ‖σ.discOne z‖) / (1 - ‖σ.discOne z‖) := rfl
  by_contra hle
  push Not at hle
  have h1 : σ.vertexOne.im * (1 + σ.tCone) / (1 - σ.tCone) ≤ σ.etaOne z := by
    rw [hη, div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have h2 : σ.foldH * σ.vertexTwo.im < σ.constK := by
    have : σ.foldH * σ.vertexTwo.im < σ.foldH * σ.foldH := mul_lt_mul_of_pos_left hvH hH
    nlinarith
  have h3 : σ.constK = σ.vertexTwo.im * (σ.vertexOne.im * (1 + σ.tCone) / (1 - σ.tCone)) := by
    rw [hK]; ring
  rw [h3] at h2
  nlinarith

include hθ in
theorem mem_domTwoC_of_norm_lt {z : ℂ} (hz : 0 < z.im)
    (hd : 0 < ‖σ.discOne z‖ + (σ.rotOne z).re) (hr : ‖σ.discOne z‖ < σ.tCone) :
    z ∈ σ.domTwoC := by
  refine ⟨hz, hd, ?_⟩
  have hX : (σ.rotOne z).re < σ.tCone := by
    have := Complex.re_le_norm (σ.rotOne z)
    rw [σ.norm_rotOne] at this
    linarith
  have h1 := σ.one_sub_t_rot_pos hθ hz
  have : 0 < (σ.tCone - (σ.rotOne z).re) / (1 - σ.tCone * (σ.rotOne z).re) :=
    div_pos (by linarith) h1
  linarith [norm_nonneg (σ.discTwo z)]

include hθ h₁ h₂ in
theorem mem_doms_of_etaOne_le {z : ℂ} (hz : z ∈ σ.triangle) (hzv : z ≠ σ.vertexOne)
    (h1 : σ.etaOne z ≤ σ.foldH) : z ∈ σ.domOne ∧ z ∈ σ.domTwoC :=
  ⟨σ.mem_domOne_of_mem_triangle hz hzv, σ.mem_domTwoC_of_norm_lt hθ hz.1
    (σ.mem_domTwo_of_mem_triangle hz hzv).2 (σ.norm_discOne_lt_tCone hθ h₁ h₂ hz.1 h1)⟩

include h₁ h₂ in
theorem coneRegion_eq_of_mem_triangle {p : ℕ} (hp : 1 ≤ p) {z : ℂ} (hz : z ∈ σ.triangle) :
    σ.coneRegion p z = σ.cornerConeC p σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB z := by
  by_cases ha : σ.etaOne z < σ.foldA₁
  · simp only [coneRegion, ha, ↓reduceIte]
    have hpos : z = σ.vertexOne ∨ z ∈ σ.domOne := by
      by_cases hzv : z = σ.vertexOne
      · exact Or.inl hzv
      · exact Or.inr (σ.mem_domOne_of_mem_triangle hz hzv)
    exact (σ.cornerConeC_eq_apex hp (σ.foldA₁_lt_foldB₁ h₁ h₂) hz.1 hpos ha.le).symm
  · simp only [coneRegion, ha, ↓reduceIte]

include h₁ h₂ in
theorem coneRegion_eventually_apex {p : ℕ} :
    σ.coneRegion p =ᶠ[𝓝 σ.vertexOne] σ.apexBefore p := by
  have hv := σ.vertexOne_im_pos
  have h1 : σ.etaOne σ.vertexOne < σ.foldA₁ := by
    rw [σ.etaOne_vertexOne]; exact σ.vertexOne_im_lt_foldA₁ h₁ h₂
  filter_upwards [(σ.continuousAt_etaOne hv).eventually_lt continuousAt_const h1] with w hw1
  simp only [coneRegion, hw1, ↓reduceIte]

include h₁ h₂ in
theorem coneRegion_vertexOne {p : ℕ} (hp : p ≠ 0) : σ.coneRegion p σ.vertexOne = -(3 / 2) := by
  rw [(σ.coneRegion_eventually_apex h₁ h₂ (p := p)).self_of_nhds, apexBefore,
    show σ.discOne σ.vertexOne = 0 from coneDisc_self _, map_zero, zero_pow hp]
  norm_num

include hθ h₁ h₂ in
theorem coneRegion_local {p : ℕ} (hp : 1 ≤ p) {z : ℂ} (hz : z ∈ σ.triangle)
    (h1 : σ.etaOne z ≤ σ.foldH) :
    ∃ g : ℂ → ℂ, ∃ D : Set ℂ, IsOpen D ∧ z ∈ D ∧ ContDiffOn ℝ ∞ g D ∧
      σ.coneRegion p =ᶠ[𝓝 z] g ∧ (z ≠ σ.vertexOne → (fderiv ℝ g z).det ≠ 0) := by
  have hAB := σ.foldA₁_lt_foldB₁ h₁ h₂
  by_cases ha : σ.etaOne z < σ.foldA₁
  · refine ⟨σ.apexBefore p, {w | 0 < w.im}, isOpen_upper, hz.1,
      fun w hw => (σ.contDiffAt_apexBefore p hw).contDiffWithinAt, ?_,
      fun hzv => σ.det_fderiv_apexBefore_ne_zero (by omega) hz.1 hzv⟩
    filter_upwards [(σ.continuousAt_etaOne hz.1).eventually_lt continuousAt_const ha] with w hw1
    simp only [coneRegion, hw1, ↓reduceIte]
  push Not at ha
  have hzv := σ.ne_vertexOne_of_foldA₁_le h₁ h₂ ha
  obtain ⟨hz1, hz2⟩ := σ.mem_doms_of_etaOne_le hθ h₁ h₂ hz hzv h1
  have hφ := σ.foldPhiA_lt_foldPhiB h₁ h₂
  refine ⟨σ.cornerConeC p σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB, σ.domOne ∩ σ.domTwoC,
    σ.isOpen_domOne.inter (σ.isOpen_domTwoC hθ), ⟨hz1, hz2⟩,
    fun w hw => (σ.contDiffAt_cornerConeC hθ p _ _ _ _ hw.1 hw.2).contDiffWithinAt, ?_,
    fun _ => ?_⟩
  · filter_upwards [σ.isOpen_domOne.mem_nhds hz1] with w hwd
    by_cases hwa : σ.etaOne w < σ.foldA₁
    · simp only [coneRegion, hwa, ↓reduceIte]
      exact (σ.cornerConeC_eq_apex hp hAB hwd.1 (Or.inr hwd) hwa.le).symm
    · simp only [coneRegion, hwa, ↓reduceIte]
  · exact σ.det_fderiv_cornerConeC_ne_zero hθ hp hAB hφ hz1 hz2
      (σ.angleTwoConeC_le_angleOneCone hθ hz1 hz2 (σ.wallOne_nonneg_of_mem_triangle hz)
        (σ.wallTwo_nonneg_of_mem_triangle hz))

theorem angleTwoConeC_mem (hθ : 0 < σ.θ₂) {z : ℂ} (hz : z ∈ σ.domTwoC)
    (hw : 0 ≤ σ.wallTwo z) : 0 ≤ σ.angleTwoConeC z ∧ σ.angleTwoConeC z < Real.pi := by
  have hp := σ.bridgeTwoC_cone_pos hθ hz
  rw [sub_neg_eq_add] at hp
  exact halfArg_mem_Ico (σ.bridgeTwoC_im_nonneg hθ hz hw) hp

theorem angleConeC_mem (hθ : 0 < σ.θ₂) {p : ℕ} (hp : σ.θ₁ * p = Real.pi) (a b φa φb : ℝ)
    {z : ℂ} (hz1 : z ∈ σ.domOne) (hz2 : z ∈ σ.domTwoC) (hw1 : 0 ≤ σ.wallOne z)
    (hw2 : 0 ≤ σ.wallTwo z)
    (hφ : 0 ≤ discAngle (σ.discOne z) ∧ discAngle (σ.discOne z) ≤ σ.θ₁) :
    0 ≤ σ.angleConeC p a b φa φb z ∧ σ.angleConeC p a b φa φb z ≤ Real.pi := by
  have h1 := σ.angleOneCone_mem hz1 hw1
  have h2 := σ.angleTwoConeC_mem hθ hz2 hw2
  have hl0 := coneStep_nonneg φa φb (discAngle (σ.discOne z))
  have hl1 := coneStep_le_one φa φb (discAngle (σ.discOne z))
  have ht0 := coneStep_nonneg a b (σ.etaOne z)
  have ht1 := coneStep_le_one a b (σ.etaOne z)
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have ha0 : 0 ≤ Real.pi - p * discAngle (σ.discOne z) := by
    have : (p : ℝ) * discAngle (σ.discOne z) ≤ p * σ.θ₁ := mul_le_mul_of_nonneg_left hφ.2 hp0
    linarith [mul_comm σ.θ₁ (p : ℝ)]
  have ha1 : Real.pi - p * discAngle (σ.discOne z) ≤ Real.pi := by
    have := mul_nonneg hp0 hφ.1
    linarith
  have hB : 0 ≤ σ.angleConeBlendC φa φb z ∧ σ.angleConeBlendC φa φb z ≤ Real.pi := by
    unfold angleConeBlendC coneLambda
    constructor <;> nlinarith
  unfold angleConeC
  constructor <;> nlinarith

include hθ h₁ h₂ in
theorem coneRegion_image {p : ℕ} (hp : 1 ≤ p) (hpθ : σ.θ₁ * p = Real.pi) {z : ℂ}
    (hz : z ∈ σ.triangle) (h1 : σ.etaOne z < σ.foldH) :
    ‖σ.coneRegion p z + 3 / 2‖ =
        coneRadial p σ.foldA₁ σ.foldB₁ σ.vertexOne.im σ.constK (σ.etaOne z) ∧
      ‖σ.coneRegion p z + 3 / 2‖ < coneProfile σ.constK σ.foldH ∧
        0 ≤ (σ.coneRegion p z).im := by
  have hge : σ.vertexOne.im ≤ σ.etaOne z := coneHeight_ge σ.vertexOne_im_pos hz.1
  obtain ⟨hS0, hS1⟩ := σ.coneRadial_lt_foldH hp hge h1
  have hE := σ.coneRegion_eq_of_mem_triangle h₁ h₂ hp hz
  have hnorm : ‖σ.coneRegion p z + 3 / 2‖ =
      coneRadial p σ.foldA₁ σ.foldB₁ σ.vertexOne.im σ.constK (σ.etaOne z) := by
    rw [hE, cornerConeC, neg_add_cancel_comm, norm_ofReal_mul_exp _ _ hS0]
  refine ⟨hnorm, hnorm ▸ hS1, ?_⟩
  rw [hE, cornerConeC, add_im]
  by_cases hzv : z = σ.vertexOne
  · subst hzv
    rw [σ.etaOne_vertexOne, σ.coneRadial_vertex h₁ h₂ hp]
    simp
  · obtain ⟨hz1, hz2⟩ := σ.mem_doms_of_etaOne_le hθ h₁ h₂ hz hzv h1.le
    have hA := σ.angleConeC_mem hθ hpθ σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB hz1 hz2
      (σ.wallOne_nonneg_of_mem_triangle hz) (σ.wallTwo_nonneg_of_mem_triangle hz)
      (σ.discAngle_mem_of_mem_triangle hz hzv)
    rw [show (-(3 / 2 : ℂ)).im = 0 by norm_num, zero_add]
    exact im_ofReal_mul_exp_nonneg hS0 hA.1 hA.2

include hθ in
theorem disc_factsC {w : ℂ} (hw : 0 < w.im) {r ψ : ℝ} (hr : 0 < r)
    (hd : σ.discOne w = (r : ℂ) * exp ((ψ : ℂ) * I)) (hψ0 : 0 ≤ ψ) (hψ1 : ψ ≤ σ.θ₁)
    (hrt : r < σ.tCone) :
    w ∈ σ.domOne ∧ w ∈ σ.domTwoC ∧ 0 ≤ σ.wallOne w ∧ 0 ≤ σ.wallTwo w := by
  obtain ⟨h1, h2, h3, h4⟩ := σ.disc_facts hw hr hd hψ0 hψ1
  have hn : ‖σ.discOne w‖ = r := by rw [hd, norm_ofReal_mul_exp _ _ hr.le]
  exact ⟨h1, σ.mem_domTwoC_of_norm_lt hθ hw h2.2 (by rw [hn]; exact hrt), h3, h4⟩

include hθ h₁ h₂ in
theorem cornerConeC_injective {p : ℕ} (hp : 1 ≤ p) (hpθ : σ.θ₁ * p = Real.pi) {z z' : ℂ}
    (hz : z ∈ σ.triangle) (hz' : z' ∈ σ.triangle) (h1 : σ.etaOne z < σ.foldH)
    (h1' : σ.etaOne z' < σ.foldH)
    (heq : σ.cornerConeC p σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB z =
      σ.cornerConeC p σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB z') : z = z' := by
  have hv := σ.vertexOne_im_pos
  have hK := σ.constK_pos
  have hAB := σ.foldA₁_lt_foldB₁ h₁ h₂
  have hφ := σ.foldPhiA_lt_foldPhiB h₁ h₂
  have hge : σ.vertexOne.im ≤ σ.etaOne z := coneHeight_ge hv hz.1
  have hge' : σ.vertexOne.im ≤ σ.etaOne z' := coneHeight_ge hv hz'.1
  set S := coneRadial p σ.foldA₁ σ.foldB₁ σ.vertexOne.im σ.constK with hSdef
  have hS0 : 0 ≤ S (σ.etaOne z) := (σ.coneRadial_lt_foldH hp hge h1).1
  have hS0' : 0 ≤ S (σ.etaOne z') := (σ.coneRadial_lt_foldH hp hge' h1').1
  have hmod : S (σ.etaOne z) = S (σ.etaOne z') := by
    have e1 : ‖σ.cornerConeC p σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB z + 3 / 2‖ =
        S (σ.etaOne z) := by
      rw [cornerConeC, neg_add_cancel_comm, norm_ofReal_mul_exp _ _ hS0]
    have e2 : ‖σ.cornerConeC p σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB z' + 3 / 2‖ =
        S (σ.etaOne z') := by
      rw [cornerConeC, neg_add_cancel_comm, norm_ofReal_mul_exp _ _ hS0']
    rw [← e1, ← e2, heq]
  have hmono := strictMonoOn_coneRadial hp hAB hv hK
  have hη : σ.etaOne z = σ.etaOne z' := hmono.injOn hge hge' hmod
  by_cases hzv : z = σ.vertexOne
  · subst hzv
    by_contra hne
    have := coneHeight_gt hv hz'.1 (Ne.symm hne)
    change σ.vertexOne.im < σ.etaOne z' at this
    rw [← hη, σ.etaOne_vertexOne] at this
    linarith
  have hzv' : z' ≠ σ.vertexOne := by
    intro h'
    apply hzv
    have := coneHeight_gt hv hz.1 hzv
    change σ.vertexOne.im < σ.etaOne z at this
    rw [hη, h', σ.etaOne_vertexOne] at this
    linarith
  obtain ⟨hz1, hz2⟩ := σ.mem_doms_of_etaOne_le hθ h₁ h₂ hz hzv h1.le
  obtain ⟨hz1', hz2'⟩ := σ.mem_doms_of_etaOne_le hθ h₁ h₂ hz' hzv' h1'.le
  have hSpos : 0 < S (σ.etaOne z) := by
    have hlt : σ.vertexOne.im < σ.etaOne z := coneHeight_gt hv hz.1 hzv
    have := hmono (Set.mem_Ici.2 le_rfl) hge hlt
    rw [σ.coneRadial_vertex h₁ h₂ hp] at this
    exact this
  have hA := σ.angleConeC_mem hθ hpθ σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB hz1 hz2
    (σ.wallOne_nonneg_of_mem_triangle hz) (σ.wallTwo_nonneg_of_mem_triangle hz)
    (σ.discAngle_mem_of_mem_triangle hz hzv)
  have hA' := σ.angleConeC_mem hθ hpθ σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB hz1' hz2'
    (σ.wallOne_nonneg_of_mem_triangle hz') (σ.wallTwo_nonneg_of_mem_triangle hz')
    (σ.discAngle_mem_of_mem_triangle hz' hzv')
  have hexp : exp ((σ.angleConeC p σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB z : ℂ) * I) =
      exp ((σ.angleConeC p σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB z' : ℂ) * I) := by
    have h3 := heq
    rw [cornerConeC, cornerConeC, ← hSdef, hη] at h3
    have hG0 : ((S (σ.etaOne z') : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (by rw [← hη]; exact hSpos.ne')
    exact mul_left_cancel₀ hG0 (add_left_cancel h3)
  have hAA := eq_of_exp_eq_of_mem hexp hA hA'
  set w₁ := σ.discOne z with hω
  set φ := discAngle w₁ with hφdef
  set φ' := discAngle (σ.discOne z') with hφ'def
  set r := ‖w₁‖ with hr
  have hr0 : 0 < r := norm_pos_iff.2 (σ.discOne_ne_zero hz1)
  have hr1 : r < 1 := norm_coneDisc_lt_one hv hz.1
  have hrt : r < σ.tCone := σ.norm_discOne_lt_tCone hθ h₁ h₂ hz.1 h1.le
  have hnorm : ‖σ.discOne z'‖ = r := by
    rw [hr, σ.norm_discOne_eq hz.1, σ.norm_discOne_eq hz'.1, hη]
  have hpol := σ.discOne_polar hz1
  have hpol' := σ.discOne_polar hz1'
  rw [hnorm] at hpol'
  set t := φ' - φ with ht
  have hz't : z' = circleCurve σ.vertexOne w₁ t := by
    apply coneDisc_injOn hv hz'.1 (circleCurve_im_pos hv hr1 t)
    change σ.discOne z' = _
    rw [coneDisc_circleCurve hv hr1 t, hpol', ← hφ'def]
    conv_rhs => rw [hω, hpol, ← hω, ← hr, ← hφdef]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    rw [ht]
    push_cast
    ring
  have hφm := σ.discAngle_mem_of_mem_triangle hz hzv
  have hφm' := σ.discAngle_mem_of_mem_triangle hz' hzv'
  have hder : ∀ s ∈ Icc (min 0 t) (max 0 t), ∃ D < 0,
      HasDerivAt (fun u => σ.angleConeC p σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB
        (circleCurve σ.vertexOne w₁ u)) D s := by
    intro s hs
    have hm := mem_Icc_minmax hs
    set w := circleCurve σ.vertexOne w₁ s with hwdef
    have hwim : 0 < w.im := circleCurve_im_pos hv hr1 s
    have hwd : σ.discOne w = (r : ℂ) * exp (((φ + s : ℝ) : ℂ) * I) := by
      change coneDisc σ.vertexOne w = _
      rw [hwdef, coneDisc_circleCurve hv hr1 s]
      conv_lhs => rw [hω, hpol, ← hω, ← hr, ← hφdef]
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    obtain ⟨hw1, hw2, hwo, hwt⟩ := σ.disc_factsC hθ hwim hr0 hwd
      (by linarith [le_min hφm.1 hφm'.1]) (by linarith [max_le hφm.2 hφm'.2]) hrt
    obtain ⟨D, hD, hDd⟩ := σ.exists_hasDerivAt_angleConeC hθ hp σ.foldA₁ σ.foldB₁ hφ hw1 hw2
      (σ.angleTwoConeC_le_angleOneCone hθ hw1 hw2 hwo hwt)
    refine ⟨D, hD, hasDerivAt_of_shift ?_⟩
    refine hDd.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)
    rw [hwdef, coneDisc_circleCurve hv hr1 s]
    simp only [circleCurve_add]
  have hc0 : circleCurve σ.vertexOne w₁ 0 = z := circleCurve_zero hv hz.1
  have ht0 : t = 0 := by
    refine eq_zero_of_strictAntiOn hder ?_
    rw [← hz't, hc0]
    exact hAA
  rw [hz't, ht0, hc0]

include hθ h₁ h₂ in
theorem coneRegion_injective {p : ℕ} (hp : 1 ≤ p) (hpθ : σ.θ₁ * p = Real.pi) {z z' : ℂ}
    (hz : z ∈ σ.triangle) (hz' : z' ∈ σ.triangle) (h1 : σ.etaOne z < σ.foldH)
    (h1' : σ.etaOne z' < σ.foldH) (heq : σ.coneRegion p z = σ.coneRegion p z') : z = z' := by
  rw [σ.coneRegion_eq_of_mem_triangle h₁ h₂ hp hz,
    σ.coneRegion_eq_of_mem_triangle h₁ h₂ hp hz'] at heq
  exact σ.cornerConeC_injective hθ h₁ h₂ hp hpθ hz hz' h1 h1' heq

include hθ h₁ h₂ in
theorem coneRegion_eventually_bridgeTwoC {p : ℕ} {z : ℂ} (hz : z ∈ σ.triangle)
    (he : σ.etaOne z = σ.foldH) (hs : σ.sinhN z < 1 / 10) :
    σ.coneRegion p =ᶠ[𝓝 z] σ.bridgeTwoC := by
  have hAB := σ.foldA₁_lt_foldB₁ h₁ h₂
  have hBH := σ.foldB₁_lt_foldH h₁ h₂
  have hzv := σ.ne_vertexOne_of_foldA₁_le h₁ h₂ (by rw [he]; linarith)
  obtain ⟨hz1, hz2⟩ := σ.mem_doms_of_etaOne_le hθ h₁ h₂ hz hzv he.le
  have hφ := σ.foldPhiA_lt_foldPhiB h₁ h₂
  have hφb := σ.foldPhiB_lt_of_sinhN_lt h₁ h₂ hz1 he (σ.discAngle_mem_of_mem_triangle hz hzv) hs
  have hb : σ.foldB₁ < σ.etaOne z := by rw [he]; exact hBH
  filter_upwards [(σ.isOpen_domTwoC hθ).mem_nhds hz2,
    continuousAt_const.eventually_lt (σ.continuousAt_etaOne hz.1) hb,
    continuousAt_const.eventually_lt (σ.continuousAt_discAngle hz1) hφb] with w hw2 hwb hwφ
  have hwa : ¬ σ.etaOne w < σ.foldA₁ := not_lt.2 (by linarith)
  simp only [coneRegion, hwa, ↓reduceIte]
  exact σ.cornerConeC_eq_bridgeTwoC hθ p hAB hφ hw2 hwb.le hwφ.le

include h₁ h₂ in
theorem coneRegion_eventually_bridgeOne {p : ℕ} {z : ℂ} (hz : z ∈ σ.triangle)
    (he : σ.etaOne z = σ.foldH) (hs : 7 / 50 < σ.sinhN z) :
    σ.coneRegion p =ᶠ[𝓝 z] σ.bridgeOne := by
  have hAB := σ.foldA₁_lt_foldB₁ h₁ h₂
  have hBH := σ.foldB₁_lt_foldH h₁ h₂
  have hzv := σ.ne_vertexOne_of_foldA₁_le h₁ h₂ (by rw [he]; linarith)
  have hz1 := σ.mem_domOne_of_mem_triangle hz hzv
  have hφ := σ.foldPhiA_lt_foldPhiB h₁ h₂
  have hφa := σ.lt_foldPhiA_of_sinhN_gt h₁ h₂ hz1 he (σ.discAngle_mem_of_mem_triangle hz hzv) hs
  have hb : σ.foldB₁ < σ.etaOne z := by rw [he]; exact hBH
  filter_upwards [σ.isOpen_domOne.mem_nhds hz1,
    continuousAt_const.eventually_lt (σ.continuousAt_etaOne hz.1) hb,
    (σ.continuousAt_discAngle hz1).eventually_lt continuousAt_const hφa] with w hw1 hwb hwφ
  have hwa : ¬ σ.etaOne w < σ.foldA₁ := not_lt.2 (by linarith)
  simp only [coneRegion, hwa, ↓reduceIte]
  exact σ.cornerConeC_eq_bridgeOne p hAB hφ hw1 hwb.le hwφ.le

include h₁ h₂ in
theorem coneRegion_refl_one {p : ℕ} (z : ℂ)
    (h : σ.etaOne z < σ.foldA₁ ∨ |discAngle (σ.discOne z)| < σ.foldPhiA) :
    σ.coneRegion p (σ.refl 1 z) = conj (σ.coneRegion p z) := by
  have hφ := σ.foldPhiA_lt_foldPhiB h₁ h₂
  have e1 := σ.etaOne_refl_one z
  by_cases ha : σ.etaOne z < σ.foldA₁
  · have ha' : σ.etaOne (σ.refl 1 z) < σ.foldA₁ := by rw [e1]; exact ha
    simp only [coneRegion, ha, ha', ↓reduceIte]
    exact σ.apexBefore_refl_one p z
  · have ha' : ¬ σ.etaOne (σ.refl 1 z) < σ.foldA₁ := by rw [e1]; exact ha
    simp only [coneRegion, ha, ha', ↓reduceIte]
    exact σ.cornerConeC_refl_one p hφ z (h.resolve_left ha).le

include h₁ h₂ in
theorem coneRegion_refl_two {p : ℕ} (hpθ : σ.θ₁ * p = Real.pi) {z : ℂ} (hz : 0 < z.im)
    (h : σ.etaOne z < σ.foldA₁ ∨ (z ∈ σ.domOne ∧ σ.foldPhiB ≤ discAngle (σ.discOne z) ∧
      σ.foldPhiB ≤ 2 * σ.θ₁ - discAngle (σ.discOne z))) :
    σ.coneRegion p (σ.refl 2 z) = conj (σ.coneRegion p z) := by
  have hφ := σ.foldPhiA_lt_foldPhiB h₁ h₂
  have e1 := σ.etaOne_refl_two hz
  by_cases ha : σ.etaOne z < σ.foldA₁
  · have ha' : σ.etaOne (σ.refl 2 z) < σ.foldA₁ := by rw [e1]; exact ha
    simp only [coneRegion, ha, ha', ↓reduceIte]
    exact σ.apexBefore_refl_two hpθ hz
  · have ha' : ¬ σ.etaOne (σ.refl 2 z) < σ.foldA₁ := by rw [e1]; exact ha
    simp only [coneRegion, ha, ha', ↓reduceIte]
    obtain ⟨hd, hb1, hb2⟩ := h.resolve_left ha
    exact σ.cornerConeC_refl_two hpθ hφ (σ.foldPhiB_pos h₁ h₂) hd hb1 hb2

include h₁ h₂ in
theorem coneRegion_wall_one {p : ℕ} (hp : 1 ≤ p) {z : ℂ} (hz : z ∈ σ.triangle)
    (hx : z.re = σ.width) (h1 : σ.etaOne z < σ.foldH) : (σ.coneRegion p z).re ≤ -(3 / 2) := by
  have hφ := σ.foldPhiA_lt_foldPhiB h₁ h₂
  have hv := σ.vertexOne_im_pos
  have hy := σ.vertexOne_im_le_of_wallOne hz hx
  have hdisc := σ.discOne_of_wallOne hx hz.1
  set r := (z.im - σ.vertexOne.im) / (z.im + σ.vertexOne.im) with hr
  have hr0 : 0 ≤ r := div_nonneg (by linarith) (by linarith)
  have hwall : σ.wallOne z = 0 := by rw [wallOne, hdisc, ofReal_im]
  have hangle : discAngle (σ.discOne z) = 0 := by
    rw [hdisc]; simp [discAngle, halfArg_zero]
  by_cases ha : σ.etaOne z < σ.foldA₁
  · simp only [coneRegion, ha, ↓reduceIte]
    rw [apexBefore, hdisc, conj_ofReal]
    have := pow_nonneg hr0 p
    have hre : ((r : ℂ) ^ p).re = r ^ p := by rw [← ofReal_pow, ofReal_re]
    norm_num
    linarith
  · simp only [coneRegion, ha, ↓reduceIte]
    have hS : 0 ≤ coneRadial p σ.foldA₁ σ.foldB₁ σ.vertexOne.im σ.constK (σ.etaOne z) :=
      (σ.coneRadial_lt_foldH hp (coneHeight_ge hv hz.1) h1).1
    have hΘ : σ.angleConeC p σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB z = Real.pi := by
      rw [angleConeC, angleConeBlendC, coneLambda, hangle,
        coneStep_eq_zero hφ (σ.foldPhiA_pos h₁ h₂).le, angleOneCone,
        σ.bridgeOne_im_of_wallOne hwall, negHalfArg_zero]
      ring
    rw [cornerConeC, hΘ, Complex.exp_pi_mul_I]
    simp only [mul_neg, mul_one, add_re, neg_re, ofReal_re]
    norm_num
    linarith

theorem bridgeTwoC_im_of_wallTwo {z : ℂ} (hw : σ.wallTwo z = 0) : (σ.bridgeTwoC z).im = 0 := by
  rw [bridgeTwoC, innerBridge, hw]
  exact twoCircle_im_eq_zero _ _ _ _ _

include h₁ h₂ in
theorem coneRegion_wall_two {p : ℕ} (hp : 1 ≤ p) (hpθ : σ.θ₁ * p = Real.pi) {z : ℂ}
    (hz : z ∈ σ.triangle) (hw : σ.wallSide 2 z = 0) (h1 : σ.etaOne z < σ.foldH) :
    -(3 / 2) ≤ (σ.coneRegion p z).re ∧ (σ.coneRegion p z).re ≤ 3 / 2 := by
  have hφ := σ.foldPhiA_lt_foldPhiB h₁ h₂
  have hv := σ.vertexOne_im_pos
  have hGh := σ.coneProfile_foldH_lt
  by_cases hzv : z = σ.vertexOne
  · subst hzv
    rw [σ.coneRegion_vertexOne h₁ h₂ (by omega)]
    norm_num
  have hz1 := σ.mem_domOne_of_mem_triangle hz hzv
  have hw2 := σ.wallTwo_eq_zero_of hz.1 hw
  have hφθ := σ.discAngle_of_wallTwo hz hw hzv
  by_cases ha : σ.etaOne z < σ.foldA₁
  · simp only [coneRegion, ha, ↓reduceIte]
    have hpol := σ.discOne_polar hz1
    rw [hφθ] at hpol
    set r := ‖σ.discOne z‖ with hr
    have hr0 : 0 ≤ r := norm_nonneg _
    have hr1 : r < 1 := norm_coneDisc_lt_one hv hz.1
    have hc : conj (σ.discOne z) ^ p = -((r ^ p : ℝ) : ℂ) := by
      rw [hpol, map_mul, conj_ofReal, ← Complex.exp_conj, mul_pow, ← Complex.exp_nat_mul]
      have e : (p : ℂ) * conj ((σ.θ₁ : ℂ) * I) = -(Real.pi : ℂ) * I := by
        rw [show conj ((σ.θ₁ : ℂ) * I) = -((σ.θ₁ : ℂ) * I) by simp, ← hpθ]
        push_cast; ring
      rw [e, show -(Real.pi : ℂ) * I = -((Real.pi : ℂ) * I) by ring, Complex.exp_neg,
        Complex.exp_pi_mul_I]
      push_cast; ring
    rw [apexBefore, hc]
    have hpow : r ^ p ≤ 1 := pow_le_one₀ hr0 hr1.le
    have hpow0 : 0 ≤ r ^ p := pow_nonneg hr0 p
    simp only [neg_div, sub_neg_eq_add, add_re, neg_re, div_ofNat_re, ofReal_re]
    norm_num
    constructor <;> linarith
  · simp only [coneRegion, ha, ↓reduceIte]
    obtain ⟨hS0, hS1⟩ := σ.coneRadial_lt_foldH hp
      (show σ.vertexOne.im ≤ σ.etaOne z from coneHeight_ge hv hz.1) h1
    have hΘ : σ.angleConeC p σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB z = 0 := by
      rw [angleConeC, angleConeBlendC, coneLambda, hφθ,
        coneStep_eq_one hφ (σ.foldPhiB_lt h₁ h₂).le, angleTwoConeC,
        σ.bridgeTwoC_im_of_wallTwo hw2, halfArg_zero]
      have : Real.pi - (p : ℝ) * σ.θ₁ = 0 := by rw [mul_comm, hpθ]; ring
      rw [this]
      ring
    rw [cornerConeC, hΘ]
    simp only [ofReal_zero, zero_mul, Complex.exp_zero, mul_one, add_re, neg_re, ofReal_re]
    norm_num
    constructor <;> linarith

end Region

end ConeShape

end GC.Seifert
