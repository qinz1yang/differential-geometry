import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldOneConeImage

/-!
# Injectivity of the assembled cone fold on the triangle

Lane A4b2 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §5–§6). The map
`foldE p` is injective on the whole triangle `T` of a one-cone shape (`foldE_injOn`), not only
outside the Jordan core: by the image regions of `SF/ConeFoldOneConeImage.lean` the four branches
have pairwise disjoint images, and each branch is injective on its part of `T`:
* `cornerZero` on `R₂`: the modulus `G(η₀)` fixes the horocycle, along which the angle strictly
  decreases (`cornerZero_injective`);
* `cornerCone` on `R₁`: the modulus `coneRadial η₁` fixes the circle about `v₁` (or the vertex),
  along which the angle strictly decreases (`cornerCone_injective`);
* `bridgeTwo`: the two moduli fix `η₀, η₁`, hence the Fermi chart point on the side
  `Re ζ ≤ 0` (`bridgeTwo_injective`);
* `cornerInfW`: the modulus `outerProfile y` fixes the height, along which the angle strictly
  increases (`cornerInfW_injective`).
In every case the angles lie in `[0, π]`, so equal values of `e^{iA}` give equal angles.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Set
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

theorem eq_of_exp_eq_of_mem {a b : ℝ} (h : exp ((a : ℂ) * I) = exp ((b : ℂ) * I))
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

theorem strictAntiOn_Icc_of_hasDerivAt {g : ℝ → ℝ} {a b : ℝ}
    (h : ∀ s ∈ Icc a b, ∃ D < 0, HasDerivAt g D s) : StrictAntiOn g (Icc a b) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc a b) (fun s hs => ?_) (fun s hs => ?_)
  · obtain ⟨D, -, hD⟩ := h s hs
    exact hD.continuousAt.continuousWithinAt
  · obtain ⟨D, hDn, hD⟩ := h s (interior_subset hs)
    rw [hD.deriv]
    exact hDn

theorem strictMonoOn_Icc_of_hasDerivAt {g : ℝ → ℝ} {a b : ℝ}
    (h : ∀ s ∈ Icc a b, ∃ D, 0 < D ∧ HasDerivAt g D s) : StrictMonoOn g (Icc a b) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc a b) (fun s hs => ?_) (fun s hs => ?_)
  · obtain ⟨D, -, hD⟩ := h s hs
    exact hD.continuousAt.continuousWithinAt
  · obtain ⟨D, hDn, hD⟩ := h s (interior_subset hs)
    rw [hD.deriv]
    exact hDn

theorem eq_zero_of_strictAntiOn {g : ℝ → ℝ} {t : ℝ}
    (h : ∀ s ∈ Icc (min 0 t) (max 0 t), ∃ D < 0, HasDerivAt g D s) (he : g 0 = g t) : t = 0 := by
  have hm := strictAntiOn_Icc_of_hasDerivAt h
  have h0 : (0 : ℝ) ∈ Icc (min 0 t) (max 0 t) := ⟨min_le_left _ _, le_max_left _ _⟩
  have ht : t ∈ Icc (min 0 t) (max 0 t) := ⟨min_le_right _ _, le_max_right _ _⟩
  exact (hm.injOn h0 ht he).symm

theorem eq_zero_of_strictMonoOn {g : ℝ → ℝ} {t : ℝ}
    (h : ∀ s ∈ Icc (min 0 t) (max 0 t), ∃ D, 0 < D ∧ HasDerivAt g D s) (he : g 0 = g t) :
    t = 0 := by
  have hm := strictMonoOn_Icc_of_hasDerivAt h
  have h0 : (0 : ℝ) ∈ Icc (min 0 t) (max 0 t) := ⟨min_le_left _ _, le_max_left _ _⟩
  have ht : t ∈ Icc (min 0 t) (max 0 t) := ⟨min_le_right _ _, le_max_right _ _⟩
  exact (hm.injOn h0 ht he).symm

theorem hasDerivAt_of_shift {g : ℝ → ℝ} {D s : ℝ} (h : HasDerivAt (fun u => g (s + u)) D 0) :
    HasDerivAt g D s := by
  have h' :=
    (show HasDerivAt (fun u => g (s + u)) D (s - s) by rw [sub_self]; exact h).comp_sub_const s s
  refine h'.congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)
  simp

theorem mem_Icc_minmax {a b s : ℝ} (hs : s ∈ Icc (min 0 (b - a)) (max 0 (b - a))) :
    min a b ≤ a + s ∧ a + s ≤ max a b := by
  obtain ⟨h1, h2⟩ := hs
  constructor
  · rcases le_total a b with h | h
    · rw [min_eq_left h]
      rw [min_eq_left (by linarith : (0 : ℝ) ≤ b - a)] at h1
      linarith
    · rw [min_eq_right h]
      rw [min_eq_right (by linarith : b - a ≤ 0)] at h1
      linarith
  · rcases le_total a b with h | h
    · rw [max_eq_right h]
      rw [max_eq_right (by linarith : (0 : ℝ) ≤ b - a)] at h2
      linarith
    · rw [max_eq_left h]
      rw [max_eq_left (by linarith : b - a ≤ 0)] at h2
      linarith

/-! ### Horocycles at the cusp `0` -/

theorem horoCurve_add {z : ℂ} (hz : 0 < z.im) (s u : ℝ) :
    horoCurve (horoCurve z s) u = horoCurve z (s + u) := by
  have h1 := one_sub_four_mul_ne hz s
  have h2 := one_sub_four_mul_ne hz (s + u)
  have h3 := one_sub_four_mul_ne (horoCurve_im_pos hz s) u
  unfold horoCurve at h3 ⊢
  have e : (1 - 4 * (s : ℂ) * z) * (1 - 4 * (u : ℂ) * (z / (1 - 4 * (s : ℂ) * z))) =
      1 - 4 * ((s + u : ℝ) : ℂ) * z := by
    field_simp
    push_cast
    ring
  rw [div_div, e]

theorem horoX_eq (z : ℂ) : horoX z = -z.re / (4 * normSq z) := by
  by_cases hz : z = 0
  · simp [hz, horoX]
  have hn : normSq z ≠ 0 := normSq_eq_zero.not.2 hz
  simp only [horoX, div_re, normSq_mul]
  simp [normSq_apply]
  rw [normSq_apply] at hn
  field_simp

theorem neg_inv_four_im {z : ℂ} (hz : 0 < z.im) :
    (-1 / (4 * z)).im = 1 / (4 * cuspZeroHeight z) := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hn : normSq z ≠ 0 := normSq_eq_zero.not.2 hz0
  simp only [div_im, normSq_mul]
  simp [normSq_apply, cuspZeroHeight]
  rw [normSq_apply] at hn
  field_simp

theorem neg_inv_four_horoCurve {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    -1 / (4 * horoCurve z t) = -1 / (4 * z) + t := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have h1 := one_sub_four_mul_ne hz t
  unfold horoCurve
  field_simp
  ring

theorem eq_horoCurve {z z' : ℂ} (hz : 0 < z.im) (hz' : 0 < z'.im)
    (hη : cuspZeroHeight z = cuspZeroHeight z') :
    z' = horoCurve z (horoX z' - horoX z) := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hz0' : z' ≠ 0 := fun h => by rw [h] at hz'; simp at hz'
  have hw : horoCurve z (horoX z' - horoX z) ≠ 0 := fun h => by
    have := horoCurve_im_pos hz (horoX z' - horoX z)
    rw [h] at this; simp at this
  have key : -1 / (4 * z') = -1 / (4 * horoCurve z (horoX z' - horoX z)) := by
    rw [neg_inv_four_horoCurve hz]
    apply Complex.ext
    · simp only [add_re, ofReal_re]
      change horoX z' = horoX z + (horoX z' - horoX z)
      ring
    · rw [add_im, ofReal_im, add_zero, neg_inv_four_im hz', neg_inv_four_im hz, hη]
  have e1 : (4 : ℂ) * z' ≠ 0 := mul_ne_zero (by norm_num) hz0'
  have e2 : (4 : ℂ) * horoCurve z (horoX z' - horoX z) ≠ 0 := mul_ne_zero (by norm_num) hw
  rw [div_eq_div_iff e1 e2] at key
  have : (4 : ℂ) * (horoCurve z (horoX z' - horoX z) - z') = 0 := by linear_combination -key
  have := (mul_eq_zero.1 this).resolve_left (by norm_num)
  linear_combination -this

theorem cuspZeroHeight_horoCurve' {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    cuspZeroHeight (horoCurve z t) = cuspZeroHeight z := cuspZeroHeight_horoCurve hz t

/-! ### Circles about `v₁` -/

theorem circleCurve_add (v ω₀ : ℂ) (s u : ℝ) :
    circleCurve v (ω₀ * exp ((s : ℂ) * I)) u = circleCurve v ω₀ (s + u) := by
  unfold circleCurve
  rw [mul_assoc, ← Complex.exp_add]
  push_cast
  ring_nf

theorem coneDisc_injOn {v z z' : ℂ} (hv : 0 < v.im) (hz : 0 < z.im) (hz' : 0 < z'.im)
    (h : coneDisc v z = coneDisc v z') : z = z' := by
  have e := mul_one_sub_coneDisc hv hz
  have e' := mul_one_sub_coneDisc hv hz'
  rw [h] at e
  have h1 : 1 - coneDisc v z' ≠ 0 := one_sub_ne_of_norm_lt (norm_coneDisc_lt_one hv hz')
  exact mul_right_cancel₀ h1 (e.trans e'.symm)

theorem strictMonoOn_coneRadial {p : ℕ} (hp : 1 ≤ p) {a b y₁ K : ℝ} (hab : a < b) (hy₁ : 0 < y₁)
    (hK : 0 < K) : StrictMonoOn (coneRadial p a b y₁ K) (Ici y₁) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici y₁) (fun η hη => ?_) (fun η hη => ?_)
  · have hη0 : 0 < η := lt_of_lt_of_le hy₁ hη
    have hd : η + y₁ ≠ 0 := by linarith
    have hτ := (contDiff_coneStep a b).continuous.continuousAt (x := η)
    have hG := (contDiff_coneProfile hK).continuous.continuousAt (x := η)
    have hq : ContinuousAt (fun s : ℝ => (s - y₁) / (s + y₁)) η :=
      (continuousAt_id.sub continuousAt_const).div (continuousAt_id.add continuousAt_const) hd
    exact ((((continuousAt_const.sub hτ).mul (hq.pow p)).div_const 2).add
      (hτ.mul hG)).continuousWithinAt
  · rw [interior_Ici] at hη
    obtain ⟨S', hS', hd⟩ := exists_hasDerivAt_coneRadial hp hab hy₁ hK hη
    rw [hd.deriv]
    exact hS'

namespace ConeShape

variable (σ : ConeShape)

theorem coneRadial_vertex (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)
    (h₂ : Real.cos σ.θ₂ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₂) {p : ℕ} (hp : 1 ≤ p) :
    coneRadial p σ.foldA₁ σ.foldB₁ σ.vertexOne.im σ.constK σ.vertexOne.im = 0 := by
  unfold coneRadial
  rw [coneStep_eq_zero (σ.foldA₁_lt_foldB₁ h₁ h₂) (σ.vertexOne_im_lt_foldA₁ h₁ h₂).le]
  simp [zero_pow (by omega : p ≠ 0)]

theorem disc_facts {w : ℂ} (hw : 0 < w.im) {r ψ : ℝ} (hr : 0 < r)
    (hd : σ.discOne w = (r : ℂ) * exp ((ψ : ℂ) * I)) (hψ0 : 0 ≤ ψ) (hψ1 : ψ ≤ σ.θ₁) :
    w ∈ σ.domOne ∧ w ∈ σ.domTwo ∧ 0 ≤ σ.wallOne w ∧ 0 ≤ σ.wallTwo w := by
  have hθ := σ.θ₁_le
  have hθ0 := σ.θ₁_pos
  have hn : ‖σ.discOne w‖ = r := by rw [hd, norm_ofReal_mul_exp _ _ hr.le]
  have hre : (σ.discOne w).re = r * Real.cos ψ := by
    rw [hd, re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have him : (σ.discOne w).im = r * Real.sin ψ := by
    rw [hd, im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hrot : exp (-(σ.θ₁ * I)) * σ.discOne w = (r : ℂ) * exp (((ψ - σ.θ₁ : ℝ) : ℂ) * I) := by
    rw [hd, mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hc1 : 0 ≤ Real.cos ψ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  have hc2 : 0 ≤ Real.cos (ψ - σ.θ₁) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  refine ⟨⟨hw, ?_⟩, ⟨hw, ?_⟩, ?_, ?_⟩
  · rw [hn, hre]
    nlinarith
  · rw [hn, hrot, re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    nlinarith
  · rw [wallOne, him]
    exact mul_nonneg hr.le (Real.sin_nonneg_of_nonneg_of_le_pi hψ0 (by linarith))
  · rw [wallTwo, hrot, im_ofReal_mul, Complex.exp_ofReal_mul_I_im,
      show ψ - σ.θ₁ = -(σ.θ₁ - ψ) by ring, Real.sin_neg]
    have := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith : 0 ≤ σ.θ₁ - ψ) (by linarith)
    nlinarith

theorem cornerCone_injective (hθ : σ.θ₂ = 0) (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)
    {p : ℕ} (hp : 1 ≤ p) (hpθ : σ.θ₁ * p = Real.pi) {z z' : ℂ} (hz : z ∈ σ.triangle)
    (hz' : z' ∈ σ.triangle) (h1 : σ.etaOne z < σ.foldH) (h1' : σ.etaOne z' < σ.foldH)
    (heq : σ.cornerCone p σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB z =
      σ.cornerCone p σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB z') : z = z' := by
  have h₂ := σ.adm_two_of_cusp hθ
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
    have e1 : ‖σ.cornerCone p σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB z + 3 / 2‖ =
        S (σ.etaOne z) := by
      rw [cornerCone, neg_add_cancel_comm, norm_ofReal_mul_exp _ _ hS0]
    have e2 : ‖σ.cornerCone p σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB z' + 3 / 2‖ =
        S (σ.etaOne z') := by
      rw [cornerCone, neg_add_cancel_comm, norm_ofReal_mul_exp _ _ hS0']
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
  have hz1 := σ.mem_domOne_of_mem_triangle hz hzv
  have hz2 := σ.mem_domTwo_of_mem_triangle hz hzv
  have hz1' := σ.mem_domOne_of_mem_triangle hz' hzv'
  have hz2' := σ.mem_domTwo_of_mem_triangle hz' hzv'
  have hSpos : 0 < S (σ.etaOne z) := by
    have hlt : σ.vertexOne.im < σ.etaOne z := coneHeight_gt hv hz.1 hzv
    have := hmono (Set.mem_Ici.2 le_rfl) hge hlt
    rw [σ.coneRadial_vertex h₁ h₂ hp] at this
    exact this
  have hA := σ.angleCone_mem hθ hpθ σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB hz1 hz2
    (σ.wallOne_nonneg_of_mem_triangle hz) (σ.wallTwo_nonneg_of_mem_triangle hz)
    (σ.discAngle_mem_of_mem_triangle hz hzv)
  have hA' := σ.angleCone_mem hθ hpθ σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB hz1' hz2'
    (σ.wallOne_nonneg_of_mem_triangle hz') (σ.wallTwo_nonneg_of_mem_triangle hz')
    (σ.discAngle_mem_of_mem_triangle hz' hzv')
  have hexp : exp ((σ.angleCone p σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB z : ℂ) * I) =
      exp ((σ.angleCone p σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB z' : ℂ) * I) := by
    have h3 := heq
    rw [cornerCone, cornerCone, ← hSdef, hη] at h3
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
      HasDerivAt (fun u => σ.angleCone p σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB
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
    obtain ⟨hw1, hw2, hwo, hwt⟩ := σ.disc_facts hwim hr0 hwd
      (by linarith [le_min hφm.1 hφm'.1]) (by linarith [max_le hφm.2 hφm'.2])
    obtain ⟨D, hD, hDd⟩ := σ.exists_hasDerivAt_angleCone hθ hp σ.foldA₁ σ.foldB₁ hφ hw1 hw2
      (σ.angleTwoCone_le_angleOneCone hθ hw1 hw2 hwo hwt)
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

/-! ### The wall-2 bridge -/

theorem fermiChart_injOn {z z' : ℂ} (hz : 0 < z.im) (hz' : 0 < z'.im)
    (h : σ.fermiChart z = σ.fermiChart z') : z = z' := by
  have h1 := σ.rightFoot_sub_ne hz
  have h2 := σ.rightFoot_sub_ne hz'
  have hk : (σ.chartScale : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 σ.chartScale_pos.ne'
  unfold fermiChart at h
  rw [div_eq_div_iff h1 h2] at h
  have hd : (σ.rightFoot : ℂ) - σ.leftFoot ≠ 0 := by
    rw [rightFoot, leftFoot]
    push_cast
    norm_num
  have : (σ.chartScale : ℂ) * ((σ.rightFoot : ℂ) - σ.leftFoot) * (z - z') = 0 := by
    linear_combination h
  rcases mul_eq_zero.1 this with h3 | h3
  · rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd h4 hk
    · exact absurd h4 hd
  · exact sub_eq_zero.1 h3

theorem bridgeTwo_injective (hθ : σ.θ₂ = 0) {z z' : ℂ} (hz : z ∈ σ.triangle)
    (hz' : z' ∈ σ.triangle) (hzv : z ≠ σ.vertexOne) (hzv' : z' ≠ σ.vertexOne)
    (heq : σ.bridgeTwo z = σ.bridgeTwo z') : z = z' := by
  have hK := σ.constK_pos
  have hz2 := σ.mem_domTwo_of_mem_triangle hz hzv
  have hz2' := σ.mem_domTwo_of_mem_triangle hz' hzv'
  have hη₀ : cuspZeroHeight z = cuspZeroHeight z' := by
    have e1 := σ.norm_bridgeTwo_sub hθ hz2
    have e2 := σ.norm_bridgeTwo_sub hθ hz2'
    rw [heq, e2] at e1
    exact (strictMonoOn_coneProfile hK).injOn (cuspZeroHeight_pos hz.1).le
      (cuspZeroHeight_pos hz'.1).le e1.symm
  have hη₁ : σ.etaOne z = σ.etaOne z' := by
    have e1 := σ.norm_bridgeTwo_add hθ hz2
    have e2 := σ.norm_bridgeTwo_add hθ hz2'
    rw [heq, e2] at e1
    exact (strictMonoOn_coneProfile hK).injOn (σ.etaOne_pos hz.1).le (σ.etaOne_pos hz'.1).le
      e1.symm
  have key : ∀ w : ℂ, 0 < w.im → (σ.fermiChart w).im *
      (σ.etaOne w ^ 2 + σ.vertexOne.im ^ 2 - σ.tOne * σ.etaOne w * cuspZeroHeight w) =
        Real.sqrt σ.constK * σ.etaOne w := by
    intro w hw
    have I0 := σ.sqrt_constK_mul_normSq_fermiChart hθ hw
    have I1 := σ.sqrt_constK_mul_coneHeight_one hw
    change Real.sqrt σ.constK * σ.etaOne w * (1 + σ.tOne * normSq (σ.fermiChart w)) =
      (σ.fermiChart w).im * (σ.etaOne w ^ 2 + σ.vertexOne.im ^ 2) at I1
    linear_combination -I1 + σ.etaOne w * σ.tOne * I0
  have k1 := key z hz.1
  have k2 := key z' hz'.1
  rw [← hη₀, ← hη₁] at k2
  set c := σ.etaOne z ^ 2 + σ.vertexOne.im ^ 2 - σ.tOne * σ.etaOne z * cuspZeroHeight z
  have hpos : 0 < Real.sqrt σ.constK * σ.etaOne z := mul_pos σ.sqrt_constK_pos (σ.etaOne_pos hz.1)
  have hc : c ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at k1
    linarith
  have hY : (σ.fermiChart z).im = (σ.fermiChart z').im :=
    mul_right_cancel₀ hc (k1.trans k2.symm)
  have hN : normSq (σ.fermiChart z) = normSq (σ.fermiChart z') := by
    have I0 := σ.sqrt_constK_mul_normSq_fermiChart hθ hz.1
    have I0' := σ.sqrt_constK_mul_normSq_fermiChart hθ hz'.1
    rw [← hη₀, ← hY] at I0'
    exact mul_left_cancel₀ σ.sqrt_constK_pos.ne' (I0.trans I0'.symm)
  have hX : (σ.fermiChart z).re ≤ 0 := by
    rw [σ.fermiChart_re]
    have := σ.normSq_sub_rightFoot_pos hz.1
    have := hz.2 2
    have := σ.chartScale_pos
    have : 0 ≤ σ.chartScale * σ.wallSide 2 z / normSq (z - σ.rightFoot) := by positivity
    linarith
  have hX' : (σ.fermiChart z').re ≤ 0 := by
    rw [σ.fermiChart_re]
    have := σ.normSq_sub_rightFoot_pos hz'.1
    have := hz'.2 2
    have := σ.chartScale_pos
    have : 0 ≤ σ.chartScale * σ.wallSide 2 z' / normSq (z' - σ.rightFoot) := by positivity
    linarith
  have hX2 : (σ.fermiChart z).re ^ 2 = (σ.fermiChart z').re ^ 2 := by
    rw [normSq_apply, normSq_apply, hY] at hN
    nlinarith
  have hXe : (σ.fermiChart z).re = (σ.fermiChart z').re := by
    have hm : ((σ.fermiChart z).re - (σ.fermiChart z').re) *
        ((σ.fermiChart z).re + (σ.fermiChart z').re) = 0 := by linear_combination hX2
    rcases mul_eq_zero.1 hm with h | h
    · linarith
    · linarith
  exact σ.fermiChart_injOn hz.1 hz'.1 (Complex.ext hXe hY)

/-! ### The corner at `∞` -/

theorem mem_domOne_of_re_ne {w : ℂ} (hw : 0 < w.im) (hx : w.re ≠ σ.width) : w ∈ σ.domOne := by
  refine ⟨hw, ?_⟩
  have hN := normSq_sub_conj_pos σ.vertexOne_im_pos hw
  have h := σ.im_coneDisc_vertexOne_mul w
  have hi : (σ.discOne w).im ≠ 0 := by
    intro h0
    change (coneDisc σ.vertexOne w).im = 0 at h0
    rw [h0, zero_mul] at h
    simp only [wallSide] at h
    have hv := σ.vertexOne_im_pos
    rcases mul_eq_zero.1 h.symm with h' | h'
    · linarith
    · exact hx (by linarith)
  have h2 : (σ.discOne w).re ^ 2 < ‖σ.discOne w‖ ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]
    have := sq_pos_of_ne_zero hi
    nlinarith
  have h3 : |(σ.discOne w).re| < ‖σ.discOne w‖ := abs_lt_of_sq_lt_sq h2 (norm_nonneg _)
  linarith [neg_abs_le (σ.discOne w).re]

theorem mem_domOne_of_im_gt {w : ℂ} (hw : σ.vertexOne.im < w.im) : w ∈ σ.domOne := by
  have hw0 : 0 < w.im := lt_trans σ.vertexOne_im_pos hw
  by_cases hx : w.re = σ.width
  · refine ⟨hw0, ?_⟩
    have hN := normSq_sub_conj_pos σ.vertexOne_im_pos hw0
    have h := coneDisc_re_mul σ.vertexOne w
    rw [hx, vertexOne_re, sub_self] at h
    have : 0 < (coneDisc σ.vertexOne w).re * normSq (w - conj σ.vertexOne) := by
      rw [h]; nlinarith [σ.vertexOne_im_pos]
    have hre := pos_of_mul_pos_left this hN.le
    change 0 < ‖coneDisc σ.vertexOne w‖ + (coneDisc σ.vertexOne w).re
    linarith [norm_nonneg (coneDisc σ.vertexOne w)]
  · exact σ.mem_domOne_of_re_ne hw0 hx

theorem re_lt_width_of_im_le {z : ℂ} (hz : z ∈ σ.triangle) (hzv : z ≠ σ.vertexOne)
    (hy : z.im ≤ σ.vertexOne.im) : z.re < σ.width := by
  rcases (σ.re_le_width_of_mem_triangle hz).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hzv
    have hw2 := hz.2 2
    simp only [wallSide] at hw2
    rw [h] at hw2
    have hW : σ.width - σ.centre = Real.cos σ.θ₁ / 4 := by unfold width centre; ring
    rw [hW] at hw2
    have hs := Real.sin_sq_add_cos_sq σ.θ₁
    have hv := σ.vertexOne_im
    have hsq : σ.vertexOne.im ^ 2 ≤ z.im ^ 2 := by rw [hv]; nlinarith
    have : σ.vertexOne.im ≤ z.im :=
      (pow_le_pow_iff_left₀ σ.vertexOne_im_pos.le hz.1.le two_ne_zero).1 hsq
    exact Complex.ext (by rw [h, vertexOne_re]) (le_antisymm hy this)

theorem cornerInfW_injective (hθ : σ.θ₂ = 0) {z z' : ℂ} (hz : z ∈ σ.triangle)
    (hz' : z' ∈ σ.triangle) (hzv : z ≠ σ.vertexOne) (hzv' : z' ≠ σ.vertexOne)
    (heq : σ.cornerInfW σ.blendWeight σ.foldY₁ σ.foldY₂ z =
      σ.cornerInfW σ.blendWeight σ.foldY₁ σ.foldY₂ z') : z = z' := by
  have hK := σ.constK_pos
  have hz1 := σ.mem_domOne_of_mem_triangle hz hzv
  have hz1' := σ.mem_domOne_of_mem_triangle hz' hzv'
  have hRpos : ∀ w : ℂ, 0 < w.im → 0 < outerProfile σ.constK σ.foldY₁ σ.foldY₂ w.im := fun w hw =>
    lt_trans (by norm_num) (two_lt_outerProfile hK σ.sqrt_constK_le_half
      (lt_trans σ.foldY₁_pos σ.foldY₁_lt_foldY₂) σ.foldY₂_lt_sqrt hw)
  have hy : z.im = z'.im := by
    have e1 : ‖σ.cornerInfW σ.blendWeight σ.foldY₁ σ.foldY₂ z‖ =
        outerProfile σ.constK σ.foldY₁ σ.foldY₂ z.im := by
      rw [cornerInfW, norm_ofReal_mul_exp _ _ (hRpos z hz.1).le]
    have e2 : ‖σ.cornerInfW σ.blendWeight σ.foldY₁ σ.foldY₂ z'‖ =
        outerProfile σ.constK σ.foldY₁ σ.foldY₂ z'.im := by
      rw [cornerInfW, norm_ofReal_mul_exp _ _ (hRpos z' hz'.1).le]
    rw [heq, e2] at e1
    exact (outerProfile_mono hK σ.sqrt_constK_le_half σ.foldY₁_pos.le σ.foldY₁_lt_foldY₂
      σ.foldY₂_lt_sqrt).injOn hz.1 hz'.1 e1.symm
  have hA := σ.angleInfW_mem (ν := σ.blendWeight) hz1 (σ.re_nonneg_of_triangle hz)
    (σ.wallOne_nonneg_of_mem_triangle hz) (σ.blendWeight_nonneg z) (σ.blendWeight_le_one z)
  have hA' := σ.angleInfW_mem (ν := σ.blendWeight) hz1' (σ.re_nonneg_of_triangle hz')
    (σ.wallOne_nonneg_of_mem_triangle hz') (σ.blendWeight_nonneg z') (σ.blendWeight_le_one z')
  have hexp : exp ((σ.angleInfW σ.blendWeight z : ℂ) * I) =
      exp ((σ.angleInfW σ.blendWeight z' : ℂ) * I) := by
    have h3 := heq
    rw [cornerInfW, cornerInfW, hy] at h3
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.2 (hRpos z' hz'.1).ne') h3
  have hAA := eq_of_exp_eq_of_mem hexp ⟨le_trans hA.1 hA.2.1, le_trans hA.2.2.1 hA.2.2.2⟩
    ⟨le_trans hA'.1 hA'.2.1, le_trans hA'.2.2.1 hA'.2.2.2⟩
  set t := z'.re - z.re with ht
  have hz't : z' = z + (t : ℂ) := by
    apply Complex.ext
    · simp [ht]
    · simp [hy]
  have hder : ∀ s ∈ Icc (min 0 t) (max 0 t), ∃ D, 0 < D ∧
      HasDerivAt (fun u : ℝ => σ.angleInfW σ.blendWeight (z + (u : ℂ))) D s := by
    intro s hs
    have hm := mem_Icc_minmax hs
    set w := z + (s : ℂ) with hwdef
    have hwim : w.im = z.im := by simp [hwdef]
    have hwre : w.re = z.re + s := by simp [hwdef]
    have hx0 : 0 ≤ w.re := by
      rw [hwre]; linarith [le_min (σ.re_nonneg_of_triangle hz) (σ.re_nonneg_of_triangle hz')]
    have hxW : w.re ≤ σ.width := by
      rw [hwre]; linarith [max_le (σ.re_le_width_of_mem_triangle hz)
        (σ.re_le_width_of_mem_triangle hz')]
    have hw1 : w ∈ σ.domOne := by
      rcases lt_or_ge σ.vertexOne.im z.im with hgt | hle
      · exact σ.mem_domOne_of_im_gt (by rw [hwim]; exact hgt)
      · have h1 := σ.re_lt_width_of_im_le hz hzv hle
        have h2 := σ.re_lt_width_of_im_le hz' hzv' (by rw [← hy]; exact hle)
        refine σ.mem_domOne_of_re_ne (by rw [hwim]; exact hz.1) (ne_of_lt ?_)
        rw [hwre]
        linarith [max_lt h1 h2]
    have hwv := σ.vertexOne_ne_of_domOne hw1
    obtain ⟨d, hd, hdd⟩ := σ.exists_hasDerivAt_blendWeight hw1.1 hwv (fun h => absurd hθ h) hx0 hxW
    obtain ⟨D, hD, hDd⟩ := σ.exists_hasDerivAt_angleInfW hw1 hdd hd (σ.blendWeight_nonneg w)
      (σ.blendWeight_le_one w)
    refine ⟨D, hD, hasDerivAt_of_shift ?_⟩
    refine hDd.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)
    simp only [hwdef]
    push_cast
    ring_nf
  have ht0 : t = 0 := by
    refine eq_zero_of_strictMonoOn hder ?_
    simp only [ofReal_zero, add_zero, ← hz't]
    exact hAA
  rw [hz't, ht0, ofReal_zero, add_zero]


theorem wallSide_two_eq_horoX (hθ : σ.θ₂ = 0) (z : ℂ) :
    σ.wallSide 2 z = normSq z * (1 + 2 * horoX z) := by
  by_cases hz : z = 0
  · simp [hz, wallSide, σ.cusp_centre hθ]
    norm_num
  have hn : normSq z ≠ 0 := normSq_eq_zero.not.2 hz
  rw [horoX_eq, wallSide, σ.cusp_centre hθ]
  field_simp
  rw [normSq_apply]
  ring

theorem horoX_mem_of_mem_triangle (hθ : σ.θ₂ = 0) {z : ℂ} (hz : z ∈ σ.triangle) :
    -1 / 2 ≤ horoX z ∧ horoX z ≤ 0 := by
  have hz0 : z ≠ 0 := fun h => by have := hz.1; rw [h] at this; simp at this
  have hn : 0 < normSq z := normSq_pos.2 hz0
  have hw := hz.2 2
  rw [σ.wallSide_two_eq_horoX hθ] at hw
  have hx := σ.re_nonneg_of_triangle hz
  constructor
  · have := nonneg_of_mul_nonneg_right hw hn
    linarith
  · rw [horoX_eq]
    have : 0 ≤ z.re / (4 * normSq z) := by positivity
    rw [neg_div]
    linarith

theorem mem_triangle_of_horo (hθ : σ.θ₂ = 0) {w : ℂ} (hw : 0 < w.im) (hX0 : -1 / 2 ≤ horoX w)
    (hX1 : horoX w ≤ 0) (hη : cuspZeroHeight w < 2 * σ.width) : w ∈ σ.triangle := by
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  have hn : 0 < normSq w := normSq_pos.2 hw0
  have hx : 0 ≤ w.re := by
    rw [horoX_eq] at hX1
    have : -w.re / (4 * normSq w) * (4 * normSq w) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hX1 (by positivity)
    rw [div_mul_cancel₀ _ (by positivity)] at this
    linarith
  refine ⟨hw, fun i => ?_⟩
  fin_cases i
  · exact hx
  · change 0 ≤ σ.width - w.re
    have h1 : w.re ^ 2 + w.im ^ 2 = cuspZeroHeight w * w.im := by
      rw [cuspZeroHeight, div_mul_cancel₀ _ hw.ne', normSq_apply]; ring
    have h2 : (2 * w.re) ^ 2 ≤ cuspZeroHeight w ^ 2 := by
      nlinarith [sq_nonneg (2 * w.im - cuspZeroHeight w)]
    have h3 := (pow_le_pow_iff_left₀ (by positivity) (cuspZeroHeight_pos hw).le two_ne_zero).1 h2
    linarith
  · change 0 ≤ σ.wallSide 2 w
    rw [σ.wallSide_two_eq_horoX hθ]
    exact mul_nonneg hn.le (by linarith)

theorem two_width_gt_foldH (hθ : σ.θ₂ = 0) : σ.foldH < 2 * σ.width := by
  have := σ.foldH_lt_half
  have hc := σ.cos_θ₁_nonneg
  unfold width
  rw [hθ, Real.cos_zero]
  linarith

theorem cornerZero_injective (hθ : σ.θ₂ = 0) (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)
    {z z' : ℂ} (hz : z ∈ σ.triangle) (hz' : z' ∈ σ.triangle) (h0 : cuspZeroHeight z < σ.foldH)
    (h0' : cuspZeroHeight z' < σ.foldH)
    (heq : σ.cornerZero σ.foldA₀ σ.foldB₀ z = σ.cornerZero σ.foldA₀ σ.foldB₀ z') : z = z' := by
  have hK := σ.constK_pos
  have hG : coneProfile σ.constK (cuspZeroHeight z) = coneProfile σ.constK (cuspZeroHeight z') := by
    have h1 : ‖σ.cornerZero σ.foldA₀ σ.foldB₀ z - 3 / 2‖ =
        coneProfile σ.constK (cuspZeroHeight z) := by
      rw [cornerZero, add_sub_cancel_left, norm_ofReal_mul_exp _ _ (σ.holeModulus_pos z).le]
    have h2 : ‖σ.cornerZero σ.foldA₀ σ.foldB₀ z' - 3 / 2‖ =
        coneProfile σ.constK (cuspZeroHeight z') := by
      rw [cornerZero, add_sub_cancel_left, norm_ofReal_mul_exp _ _ (σ.holeModulus_pos z').le]
    rw [← h1, ← h2, heq]
  have hη : cuspZeroHeight z = cuspZeroHeight z' :=
    (strictMonoOn_coneProfile hK).injOn (cuspZeroHeight_pos hz.1).le
      (cuspZeroHeight_pos hz'.1).le hG
  have hzv := σ.ne_vertexOne_of_cuspZeroHeight_le hθ h₁ h0.le
  have hzv' := σ.ne_vertexOne_of_cuspZeroHeight_le hθ h₁ h0'.le
  have hA := σ.angleHole_mem hθ σ.foldA₀ σ.foldB₀ (σ.mem_domTwo_of_mem_triangle hz hzv)
    (σ.re_nonneg_of_triangle hz) (σ.wallTwo_nonneg_of_mem_triangle hz)
  have hA' := σ.angleHole_mem hθ σ.foldA₀ σ.foldB₀ (σ.mem_domTwo_of_mem_triangle hz' hzv')
    (σ.re_nonneg_of_triangle hz') (σ.wallTwo_nonneg_of_mem_triangle hz')
  have hexp : exp ((σ.angleHole σ.foldA₀ σ.foldB₀ z : ℂ) * I) =
      exp ((σ.angleHole σ.foldA₀ σ.foldB₀ z' : ℂ) * I) := by
    have h3 := heq
    rw [cornerZero, cornerZero, hη] at h3
    have hG0 : ((coneProfile σ.constK (cuspZeroHeight z') : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (σ.holeModulus_pos z').ne'
    exact mul_left_cancel₀ hG0 (add_left_cancel h3)
  have hAA := eq_of_exp_eq_of_mem hexp hA hA'
  set t := horoX z' - horoX z with ht
  have hz't : z' = horoCurve z t := eq_horoCurve hz.1 hz'.1 hη
  have hX := σ.horoX_mem_of_mem_triangle hθ hz
  have hX' := σ.horoX_mem_of_mem_triangle hθ hz'
  have hder : ∀ s ∈ Icc (min 0 t) (max 0 t), ∃ D < 0,
      HasDerivAt (fun u => σ.angleHole σ.foldA₀ σ.foldB₀ (horoCurve z u)) D s := by
    intro s hs
    have hm := mem_Icc_minmax hs
    set w := horoCurve z s with hwdef
    have hwim : 0 < w.im := horoCurve_im_pos hz.1 s
    have hwX : horoX w = horoX z + s := horoX_horoCurve hz.1 s
    have hwη : cuspZeroHeight w = cuspZeroHeight z := cuspZeroHeight_horoCurve hz.1 s
    have hwT : w ∈ σ.triangle := σ.mem_triangle_of_horo hθ hwim
      (by rw [hwX]; linarith [min_le_iff.1 (le_refl (min (horoX z) (horoX z'))),
        le_min hX.1 hX'.1])
      (by rw [hwX]; linarith [max_le hX.2 hX'.2])
      (by rw [hwη]; linarith [σ.two_width_gt_foldH hθ])
    have hwv := σ.ne_vertexOne_of_cuspZeroHeight_le hθ h₁ (by rw [hwη]; exact h0.le)
    have hw2 := σ.mem_domTwo_of_mem_triangle hwT hwv
    obtain ⟨D, hD, hDd⟩ := σ.exists_hasDerivAt_angleHole hθ σ.foldA₀_lt_foldB₀ hw2
      (σ.angleZeroHole_le_angleTwoHole hθ hw2 (σ.re_nonneg_of_triangle hwT)
        (σ.wallTwo_nonneg_of_mem_triangle hwT))
    refine ⟨D, hD, hasDerivAt_of_shift ?_⟩
    refine hDd.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)
    simp only [hwdef, horoCurve_add hz.1]
  have ht0 : t = 0 := by
    refine eq_zero_of_strictAntiOn hder ?_
    simp only [horoCurve_zero, ← hz't]
    exact hAA
  rw [hz't, ht0, horoCurve_zero]

/-! ### Injectivity of `foldE` on the triangle -/

section Inj

variable (hθ : σ.θ₂ = 0) (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)

include hθ h₁ in
theorem foldE_cases {p : ℕ} (hp : 1 ≤ p) (hpθ : σ.θ₁ * p = Real.pi) {z : ℂ}
    (hz : z ∈ σ.triangle) :
    (cuspZeroHeight z < σ.foldH ∧ ‖σ.foldE p z - 3 / 2‖ < coneProfile σ.constK σ.foldH) ∨
    (σ.foldH ≤ cuspZeroHeight z ∧ σ.etaOne z < σ.foldH ∧
      ‖σ.foldE p z + 3 / 2‖ < coneProfile σ.constK σ.foldH) ∨
    (σ.foldH ≤ cuspZeroHeight z ∧ σ.foldH ≤ σ.etaOne z ∧ |σ.sinhN z| < 1 / 10 ∧
      coneProfile σ.constK σ.foldH ≤ ‖σ.foldE p z - 3 / 2‖ ∧
      coneProfile σ.constK σ.foldH ≤ ‖σ.foldE p z + 3 / 2‖ ∧ ‖σ.foldE p z‖ < 2) ∨
    (σ.foldH ≤ cuspZeroHeight z ∧ σ.foldH ≤ σ.etaOne z ∧ 1 / 10 ≤ |σ.sinhN z| ∧
      coneProfile σ.constK σ.foldH ≤ ‖σ.foldE p z - 3 / 2‖ ∧
      coneProfile σ.constK σ.foldH ≤ ‖σ.foldE p z + 3 / 2‖ ∧ 2 < ‖σ.foldE p z‖) := by
  rcases lt_or_ge (cuspZeroHeight z) σ.foldH with h0 | h0
  · obtain ⟨e, hlt, -⟩ := σ.foldE_image_zero hθ h₁ (p := p) hz h0
    exact Or.inl ⟨h0, e ▸ hlt⟩
  rcases lt_or_ge (σ.etaOne z) σ.foldH with h1 | h1
  · obtain ⟨-, hlt, -⟩ := σ.foldE_image_cone hθ h₁ hp hpθ hz h1
    exact Or.inr (Or.inl ⟨h0, h1, hlt⟩)
  rcases lt_or_ge |σ.sinhN z| (1 / 10) with hL | hL
  · obtain ⟨e1, e2, g1, g2, hn, -⟩ := σ.foldE_image_lens hθ h₁ (p := p) hz h0 h1 hL
    exact Or.inr (Or.inr (Or.inl ⟨h0, h1, hL, e1 ▸ g1, e2 ▸ g2, hn⟩))
  · obtain ⟨e, g1, g2, -⟩ := σ.foldE_image_inf hθ h₁ (p := p) hz h0 h1 hL
    have h2 : 2 < ‖σ.foldE p z‖ := by
      rw [e]
      exact two_lt_outerProfile σ.constK_pos σ.sqrt_constK_le_half
        (lt_trans σ.foldY₁_pos σ.foldY₁_lt_foldY₂) σ.foldY₂_lt_sqrt hz.1
    exact Or.inr (Or.inr (Or.inr ⟨h0, h1, hL, g1, g2, h2⟩))

theorem not_both_small {u : ℂ} (h1 : ‖u - 3 / 2‖ < coneProfile σ.constK σ.foldH)
    (h2 : ‖u + 3 / 2‖ < coneProfile σ.constK σ.foldH) : False := by
  have hG := σ.coneProfile_foldH_lt
  have := norm_sub_le (u + 3 / 2) (u - 3 / 2)
  rw [show u + 3 / 2 - (u - 3 / 2) = (3 : ℂ) by ring] at this
  norm_num at this
  linarith

include hθ h₁ in
theorem foldE_injOn {p : ℕ} (hp : 1 ≤ p) (hpθ : σ.θ₁ * p = Real.pi) :
    Set.InjOn (σ.foldE p) σ.triangle := by
  have h₂ := σ.adm_two_of_cusp hθ
  have hAH : σ.foldA₁ < σ.foldH :=
    lt_trans (σ.foldA₁_lt_foldB₁ h₁ h₂) (σ.foldB₁_lt_foldH h₁ h₂)
  intro z hz z' hz' heq
  rcases σ.foldE_cases hθ h₁ hp hpθ hz with hZ | hC | hL | hI <;>
  rcases σ.foldE_cases hθ h₁ hp hpθ hz' with hZ' | hC' | hL' | hI'
  · rw [σ.foldE_of_zero hZ.1, σ.foldE_of_zero hZ'.1] at heq
    exact σ.cornerZero_injective hθ h₁ hz hz' hZ.1 hZ'.1 heq
  · rw [← heq] at hC'; exact (σ.not_both_small hZ.2 hC'.2.2).elim
  · rw [← heq] at hL'; linarith [hZ.2, hL'.2.2.2.1]
  · rw [← heq] at hI'; linarith [hZ.2, hI'.2.2.2.1]
  · rw [heq] at hC; exact (σ.not_both_small hZ'.2 hC.2.2).elim
  · rw [σ.foldE_of_cone hθ h₁ hp hz hC.2.1, σ.foldE_of_cone hθ h₁ hp hz' hC'.2.1] at heq
    exact σ.cornerCone_injective hθ h₁ hp hpθ hz hz' hC.2.1 hC'.2.1 heq
  · rw [← heq] at hL'; linarith [hC.2.2, hL'.2.2.2.2.1]
  · rw [← heq] at hI'; linarith [hC.2.2, hI'.2.2.2.2.1]
  · rw [heq] at hL; linarith [hZ'.2, hL.2.2.2.1]
  · rw [heq] at hL; linarith [hC'.2.2, hL.2.2.2.2.1]
  · rw [σ.foldE_of_lens hθ h₁ hL.1 hL.2.1 hL.2.2.1,
      σ.foldE_of_lens hθ h₁ hL'.1 hL'.2.1 hL'.2.2.1] at heq
    exact σ.bridgeTwo_injective hθ hz hz' (σ.ne_vertexOne_of_foldA₁_le h₁ h₂ (by linarith [hL.2.1]))
      (σ.ne_vertexOne_of_foldA₁_le h₁ h₂ (by linarith [hL'.2.1])) heq
  · rw [← heq] at hI'; linarith [hL.2.2.2.2.2, hI'.2.2.2.2.2]
  · rw [heq] at hI; linarith [hZ'.2, hI.2.2.2.1]
  · rw [heq] at hI; linarith [hC'.2.2, hI.2.2.2.2.1]
  · rw [heq] at hI; linarith [hL'.2.2.2.2.2, hI.2.2.2.2.2]
  · rw [σ.foldE_of_inf hθ h₁ hI.1 hI.2.1 hI.2.2.1,
      σ.foldE_of_inf hθ h₁ hI'.1 hI'.2.1 hI'.2.2.1] at heq
    exact σ.cornerInfW_injective hθ hz hz'
      (σ.ne_vertexOne_of_foldA₁_le h₁ h₂ (by linarith [hI.2.1]))
      (σ.ne_vertexOne_of_foldA₁_le h₁ h₂ (by linarith [hI'.2.1])) heq

include hθ h₁ in
theorem foldE_mem_target {p : ℕ} (hp : 1 ≤ p) (hpθ : σ.θ₁ * p = Real.pi) {z : ℂ}
    (hz : z ∈ σ.triangle) :
    ‖σ.foldE p z‖ < 3 ∧ 0 ≤ (σ.foldE p z).im ∧ 1 / 2 < ‖σ.foldE p z - 3 / 2‖ := by
  have hK := σ.constK_pos
  have hG := σ.coneProfile_foldH_lt
  have hG' := σ.half_lt_coneProfile_foldH
  rcases lt_or_ge (cuspZeroHeight z) σ.foldH with h0 | h0
  · obtain ⟨e, hlt, him⟩ := σ.foldE_image_zero hθ h₁ (p := p) hz h0
    refine ⟨?_, him, ?_⟩
    · have := norm_le_norm_add_norm_sub' (σ.foldE p z) (3 / 2)
      have h3 : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
      linarith
    · rw [e]; exact half_lt_coneProfile hK (cuspZeroHeight_pos hz.1).ne'
  rcases lt_or_ge (σ.etaOne z) σ.foldH with h1 | h1
  · obtain ⟨-, hlt, him⟩ := σ.foldE_image_cone hθ h₁ hp hpθ hz h1
    refine ⟨?_, him, ?_⟩
    · have := norm_sub_le (σ.foldE p z + 3 / 2) (3 / 2)
      rw [add_sub_cancel_right] at this
      have h3 : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
      linarith
    · have := norm_sub_le (σ.foldE p z + 3 / 2) (σ.foldE p z - 3 / 2)
      rw [show σ.foldE p z + 3 / 2 - (σ.foldE p z - 3 / 2) = (3 : ℂ) by ring] at this
      norm_num at this
      linarith
  rcases lt_or_ge |σ.sinhN z| (1 / 10) with hL | hL
  · obtain ⟨e1, -, -, -, hn, him⟩ := σ.foldE_image_lens hθ h₁ (p := p) hz h0 h1 hL
    have h3 : 1 / 2 < ‖σ.foldE p z - 3 / 2‖ := by
      rw [e1]; exact half_lt_coneProfile hK (cuspZeroHeight_pos hz.1).ne'
    exact ⟨by linarith, him, h3⟩
  · obtain ⟨e, -, -, him⟩ := σ.foldE_image_inf hθ h₁ (p := p) hz h0 h1 hL
    have h2 : 2 < ‖σ.foldE p z‖ := by
      rw [e]
      exact two_lt_outerProfile hK σ.sqrt_constK_le_half
        (lt_trans σ.foldY₁_pos σ.foldY₁_lt_foldY₂) σ.foldY₂_lt_sqrt hz.1
    have h3' : ‖σ.foldE p z‖ < 3 := by
      rw [e]
      exact outerProfile_lt_three hK σ.sqrt_constK_le_half σ.foldY₁_pos.le σ.foldY₁_lt_foldY₂
        σ.foldY₂_lt_sqrt hz.1
    refine ⟨h3', him, ?_⟩
    have := norm_sub_norm_le (σ.foldE p z) (3 / 2)
    have h3 : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
    linarith

end Inj

end ConeShape

end GC.Seifert
