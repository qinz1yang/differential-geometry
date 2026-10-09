import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldTwoConeBridges

/-!
# The angle of the two-cone wall-2 bridge along circles about `v₁`

Lane A4b3 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §2 and §5, for the
two-cone shapes `(p₁, p₂, ⊤)`). Along the hyperbolic circle about `v₁` through `z`, oriented from
wall 1 to wall 2, the rotated disc coordinate is `ω' = X + iY = ω'₀ e^{it}` and the disc coordinate
`μ = |ω₂|` at the second cone satisfies `μ² = N/D` with `N = (X - t)² + Y²`, `D = (1 - tX)² + t²Y²`
(`moebius_rel`, `t = tCone`). Since `N' = D' = 2tY`, one gets
`d μ²/dψ = 2tY (D - N)/D² = -2t (1 - r²)(1 - t²) wallTwo/D²` (`Y = -wallTwo`), so the virtual height
`η₂ = y₂ (1 + μ)/(1 - μ)` has derivative `wallTwo · κ` with `κ < 0` off `v₂`
(`exists_hasDerivAt_etaTwoC_circle`). As for the cusp, the angle `angleTwoConeC` of the bridge
`bridgeTwoC` about `-3/2` therefore strictly decreases along these circles
(`exists_hasDerivAt_angleTwoConeC`), and it is smooth on `domTwoC` (`contDiffAt_angleTwoConeC`).
-/

set_option autoImplicit false

noncomputable section

open Complex Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace ConeShape

variable (σ : ConeShape)

def angleTwoConeC (z : ℂ) : ℝ :=
  halfArg (coneProfile σ.constK (σ.etaOne z)) ((σ.bridgeTwoC z).re + 3 / 2) (σ.bridgeTwoC z).im

theorem rotOne_circleCurve {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    σ.rotOne (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t) =
      exp (-(σ.θ₁ * I)) * (coneDisc σ.vertexOne z * exp ((t : ℂ) * I)) := by
  rw [rotOne, discOne, coneDisc_circleCurve σ.vertexOne_im_pos
    (norm_coneDisc_lt_one σ.vertexOne_im_pos hz)]

theorem vertexOne_ne_of_domTwoC {z : ℂ} (hz : z ∈ σ.domTwoC) : z ≠ σ.vertexOne := fun h =>
  σ.discOne_ne_zero_of_domTwoC hz (by rw [h, discOne, coneDisc_self])

theorem contDiffAt_etaOne_of_domTwoC {z : ℂ} (hz : z ∈ σ.domTwoC) :
    ContDiffAt ℝ ∞ σ.etaOne z :=
  contDiffAt_coneHeight σ.vertexOne_im_pos hz.1 (σ.vertexOne_ne_of_domTwoC hz)

theorem contDiffAt_etaTwoC (hθ : 0 < σ.θ₂) {z : ℂ} (hz : 0 < z.im) (hzv : z ≠ σ.vertexTwo) :
    ContDiffAt ℝ ∞ σ.etaTwoC z :=
  contDiffAt_coneHeight (σ.vertexTwo_im_pos hθ) hz hzv

theorem etaTwoC_pos (hθ : 0 < σ.θ₂) {z : ℂ} (hz : 0 < z.im) : 0 < σ.etaTwoC z :=
  coneHeight_pos (σ.vertexTwo_im_pos hθ) hz

theorem exists_hasDerivAt_etaTwoC_circle (hθ : 0 < σ.θ₂) {z : ℂ} (hz : z ∈ σ.domTwoC) :
    ∃ κ : ℝ, κ < 0 ∧ HasDerivAt
      (fun t : ℝ => σ.etaTwoC (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t))
      (σ.wallTwo z * κ) 0 := by
  have hv := σ.vertexOne_im_pos
  have hv2 := σ.vertexTwo_im_pos hθ
  have hω := norm_coneDisc_lt_one hv hz.1
  have ht1 := σ.tCone_lt_one hθ
  have ht0 := σ.tCone_pos
  set γ := circleCurve σ.vertexOne (coneDisc σ.vertexOne z) with hγ
  set c : ℂ := exp (-(σ.θ₁ * I)) with hc
  set ω₀ := coneDisc σ.vertexOne z with hω₀
  set Wf : ℝ → ℂ := fun t => c * (ω₀ * exp ((t : ℂ) * I)) with hWf
  have hrot : ∀ t, σ.rotOne (γ t) = Wf t := fun t => σ.rotOne_circleCurve hz.1 t
  have hγim : ∀ t, 0 < (γ t).im := fun t => circleCurve_im_pos hv hω t
  have hγ0 : γ 0 = z := circleCurve_zero hv hz.1
  set τ := σ.tCone with hτ
  set X : ℝ → ℝ := fun t => (Wf t).re with hX
  set Y : ℝ → ℝ := fun t => (Wf t).im with hY
  set N : ℝ → ℝ := fun t => (X t - τ) ^ 2 + Y t ^ 2 with hN
  set D : ℝ → ℝ := fun t => (1 - τ * X t) ^ 2 + τ ^ 2 * Y t ^ 2 with hD
  have hX0 : X 0 = (σ.rotOne z).re := by rw [hX]; simp only; rw [← hrot 0, hγ0]
  have hY0 : Y 0 = -σ.wallTwo z := by
    rw [hY]; simp only; rw [← hrot 0, hγ0, σ.rotOne_im]
  have hDpos : ∀ t, 0 < D t := by
    intro t
    have h := σ.one_sub_t_rot_pos hθ (hγim t)
    rw [hrot t] at h
    have : 0 < (1 - τ * X t) ^ 2 := by positivity
    simp only [hD]
    positivity
  have hmoeb : ∀ t, ‖σ.discTwo (γ t)‖ ^ 2 * D t = N t := by
    intro t
    have h := σ.moebius_rel hθ (hγim t)
    rw [hrot t] at h
    exact h
  have hμ : ∀ t, ‖σ.discTwo (γ t)‖ = Real.sqrt (N t / D t) := by
    intro t
    rw [← Real.sqrt_sq (norm_nonneg (σ.discTwo (γ t)))]
    congr 1
    rw [eq_div_iff (hDpos t).ne']
    exact hmoeb t
  have hzv2 := σ.ne_vertexTwo_of_domTwoC hθ hz
  have hμ0pos : 0 < ‖σ.discTwo z‖ := norm_pos_iff.2 (coneDisc_ne_zero hv2 hz.1 hzv2)
  have hμ1 : ‖σ.discTwo z‖ < 1 := σ.norm_discTwo_lt_one hθ hz.1
  have hm0 : Real.sqrt (N 0 / D 0) = ‖σ.discTwo z‖ := by rw [← hμ 0, hγ0]
  have hq0 : N 0 / D 0 ≠ 0 := by
    intro h
    rw [h, Real.sqrt_zero] at hm0
    linarith
  have hW : HasDerivAt Wf (Wf 0 * I) 0 := by
    have := (hasDerivAt_rot ω₀).const_mul c
    refine this.congr_deriv ?_
    simp [hWf]
    ring
  have hXd : HasDerivAt X (-(Y 0)) 0 := by
    have := reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hW
    refine this.congr_deriv ?_
    simp [hY]
  have hYd : HasDerivAt Y (X 0) 0 := by
    have := imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hW
    refine this.congr_deriv ?_
    simp [hX]
  have hNd : HasDerivAt N (2 * τ * Y 0) 0 := by
    have := ((hXd.sub_const τ).pow 2).add (hYd.pow 2)
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat]
    ring
  have hDd : HasDerivAt D (2 * τ * Y 0) 0 := by
    have := (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hXd.const_mul τ)).pow 2).add
      ((hYd.pow 2).const_mul (τ ^ 2))
    refine this.congr_deriv ?_
    simp only [Pi.sub_apply, Nat.cast_ofNat]
    ring
  have hq : HasDerivAt (fun t => N t / D t)
      (2 * τ * Y 0 * (D 0 - N 0) / D 0 ^ 2) 0 := by
    have := hNd.div hDd (hDpos 0).ne'
    refine this.congr_deriv ?_
    have := (hDpos 0).ne'
    field_simp
  have hm := hq.sqrt hq0
  rw [hm0] at hm
  set m₀ := ‖σ.discTwo z‖ with hm₀
  set y₂ := σ.vertexTwo.im with hy₂
  have hne : (1 : ℝ) - Real.sqrt (N 0 / D 0) ≠ 0 := by rw [hm0]; linarith
  have he := ((hm.const_add 1).const_mul y₂).div ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hm)
    hne
  have hfun : (fun t : ℝ => σ.etaTwoC (γ t)) =
      fun t => y₂ * (1 + Real.sqrt (N t / D t)) / (1 - Real.sqrt (N t / D t)) := by
    funext t
    simp only [etaTwoC, coneHeight]
    rw [← discTwo, hμ t]
  have hDN : D 0 - N 0 = (1 - ‖σ.discOne z‖ ^ 2) * (1 - τ ^ 2) := by
    have hr : ‖σ.discOne z‖ ^ 2 = X 0 ^ 2 + Y 0 ^ 2 := by
      rw [hX0, show Y 0 = (σ.rotOne z).im by rw [hY0, σ.rotOne_im], ← σ.norm_rotOne,
        Complex.sq_norm, normSq_apply]
      ring
    rw [hr]
    simp only [hD, hN]
    ring
  have hr1 : ‖σ.discOne z‖ < 1 := σ.norm_discOne_lt_one hz.1
  refine ⟨-(2 * y₂ / (1 - m₀) ^ 2 * (2 * τ * (D 0 - N 0) / D 0 ^ 2) / (2 * m₀)), ?_, ?_⟩
  · have h1 : 0 < D 0 - N 0 := by
      rw [hDN]
      have : 0 < 1 - ‖σ.discOne z‖ ^ 2 := by nlinarith [norm_nonneg (σ.discOne z)]
      have : 0 < 1 - τ ^ 2 := by nlinarith
      positivity
    have h2 : 0 < 1 - m₀ := by linarith
    have h3 := hDpos 0
    rw [neg_lt_zero]
    positivity
  · rw [hfun]
    refine he.congr_deriv ?_
    simp only [Pi.sub_apply]
    rw [hm0, hY0]
    have h2 : (1 : ℝ) - m₀ ≠ 0 := by linarith
    have h3 := (hDpos 0).ne'
    have h4 : m₀ ≠ 0 := hμ0pos.ne'
    field_simp
    ring

theorem bridgeTwoC_cone_pos (hθ : 0 < σ.θ₂) {z : ℂ} (hz : z ∈ σ.domTwoC) :
    0 < coneProfile σ.constK (σ.etaOne z) + ((σ.bridgeTwoC z).re - -(3 / 2)) := by
  have hK := σ.constK_pos
  have e1 := sq_add_sq_eq_of_norm (σ.norm_bridgeTwoC_add hθ hz)
  simp only [add_re, add_im, div_ofNat_re, div_ofNat_im] at e1
  norm_num at e1
  have h2 := σ.norm_bridgeTwoC_lt_two hθ hz
  have e2 : (σ.bridgeTwoC z).re ^ 2 + (σ.bridgeTwoC z).im ^ 2 < 4 := by
    have := sq_add_sq_eq_of_norm (u := σ.bridgeTwoC z) rfl
    nlinarith [norm_nonneg (σ.bridgeTwoC z)]
  have hG := half_lt_coneProfile hK (σ.etaOne_pos hz.1).ne'
  by_contra hc
  have hle : (σ.bridgeTwoC z).re + 3 / 2 ≤ -coneProfile σ.constK (σ.etaOne z) := by
    linarith [not_lt.1 hc]
  nlinarith

theorem contDiffAt_angleTwoConeC (hθ : 0 < σ.θ₂) {z : ℂ} (hz : z ∈ σ.domTwoC) :
    ContDiffAt ℝ ∞ σ.angleTwoConeC z := by
  have hb := σ.contDiffAt_bridgeTwoC hθ hz
  have hG : ContDiffAt ℝ ∞ (fun u => coneProfile σ.constK (σ.etaOne u)) z :=
    (contDiff_coneProfile σ.constK_pos).contDiffAt.comp z (σ.contDiffAt_etaOne_of_domTwoC hz)
  have hp := σ.bridgeTwoC_cone_pos hθ hz
  rw [sub_neg_eq_add] at hp
  exact contDiffAt_halfArg_comp hG ((reCLM.contDiff.contDiffAt.comp z hb).add contDiffAt_const)
    (imCLM.contDiff.contDiffAt.comp z hb) hp

theorem contDiffAt_cofTwoC' (hθ : 0 < σ.θ₂) {z : ℂ} (hz : z ∈ σ.domTwoC) :
    ContDiffAt ℝ ∞ σ.cofTwoC z := σ.contDiffAt_cofTwoC hθ hz

theorem exists_hasDerivAt_angleTwoConeC (hθ : 0 < σ.θ₂) {z : ℂ} (hz : z ∈ σ.domTwoC) :
    ∃ D : ℝ, D < 0 ∧ HasDerivAt
      (fun t : ℝ => σ.angleTwoConeC (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t)) D 0 := by
  have hK := σ.constK_pos
  have hv := σ.vertexOne_im_pos
  have hv2 := σ.vertexTwo_im_pos hθ
  have hω := norm_coneDisc_lt_one hv hz.1
  have h0 : circleCurve σ.vertexOne (coneDisc σ.vertexOne z) 0 = z := circleCurve_zero hv hz.1
  have hγ := σ.hasDerivAt_circle_velocity hz.1
  have hev : ∀ᶠ t : ℝ in 𝓝 0,
      circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t ∈ σ.domTwoC := by
    have := (continuous_circleCurve (v := σ.vertexOne) hω).continuousAt (x := 0)
      |>.preimage_mem_nhds ((σ.isOpen_domTwoC hθ).mem_nhds (by rw [h0]; exact hz))
    exact this
  have hwc : ∀ t : ℝ, σ.wallTwo (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t) =
      -(exp (-(σ.θ₁ * I)) * (coneDisc σ.vertexOne z * exp ((t : ℂ) * I))).im :=
    fun t => σ.wallTwo_circleCurve hz.1 t
  have hηc : ∀ t : ℝ, σ.etaOne (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t) =
      σ.etaOne z := fun t => σ.etaOne_circleCurve hz.1 t
  obtain ⟨κ₀, hκ₀neg, he'⟩ := σ.exists_hasDerivAt_etaTwoC_circle hθ hz
  set K := σ.constK
  set ω₀ := coneDisc σ.vertexOne z with hω₀
  set γ := circleCurve σ.vertexOne ω₀ with hγdef
  set η₁ := σ.etaOne z with hη₁
  set A₀ := coneProfile K η₁ with hA₀
  have hA₀pos : 0 < A₀ := by have := half_le_coneProfile hK η₁; linarith
  set e : ℝ → ℝ := fun t => σ.etaTwoC (γ t) with hedef
  have he0 : e 0 = σ.etaTwoC z := by simp [hedef, h0]
  set κ := 4 * K * e 0 / (e 0 ^ 2 + K) ^ 2 * κ₀ with hκ
  have hκneg : κ < 0 := by
    have : 0 < e 0 := by rw [he0]; exact σ.etaTwoC_pos hθ hz.1
    have : 0 < 4 * K * e 0 / (e 0 ^ 2 + K) ^ 2 := by positivity
    exact mul_neg_of_pos_of_neg this hκ₀neg
  have hB : HasDerivAt (fun t => coneProfile K (e t)) (σ.wallTwo (γ 0) * κ) 0 := by
    refine ((hasDerivAt_coneProfile hK (e 0)).comp 0 he').congr_deriv ?_
    rw [h0, hκ]
    ring
  set c := exp (-(σ.θ₁ * I)) with hc
  have hw : HasDerivAt (fun t => σ.wallTwo (γ t)) (-(c * ω₀).re) 0 := by
    have e2 : (fun t => σ.wallTwo (γ t)) =
        fun t : ℝ => -(c * (ω₀ * exp ((t : ℂ) * I))).im := funext hwc
    rw [e2]
    have := (imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_rot ω₀).const_mul c)).neg
    refine this.congr_deriv ?_
    simp
    ring
  have hzv2 := σ.ne_vertexTwo_of_domTwoC hθ hz
  have hPc : ContDiffAt ℝ ∞
      (fun u : ℂ => innerCofactor K (σ.etaTwoC u) η₁ (σ.cofTwoC u)) z := by
    have h1 := σ.contDiffAt_etaTwoC hθ hz.1 hzv2
    have h2 := σ.contDiffAt_cofTwoC hθ hz
    have hηz := σ.etaOne_pos hz.1
    have hcz := σ.etaTwoC_pos hθ hz.1
    unfold innerCofactor
    have hd : (σ.etaTwoC z ^ 2 + K) * (η₁ ^ 2 + K) ≠ 0 := by positivity
    have hG' := (contDiff_coneProfile hK).contDiffAt (x := σ.etaTwoC z)
    exact ((((hG'.comp z h1).add contDiffAt_const).add contDiffAt_const).mul
      (contDiffAt_const.sub (((hG'.comp z h1).sub contDiffAt_const).pow 2))).mul
      (h2.mul ((contDiffAt_const.mul ((contDiffAt_const.mul h1).add contDiffAt_const)).div
        (((h1.pow 2).add contDiffAt_const).mul contDiffAt_const) hd))
  have hPd : DifferentiableAt ℝ
      (fun t : ℝ => innerCofactor K (e t) η₁ (σ.cofTwoC (γ t))) 0 := by
    have := ((hPc.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ
      h0.symm).differentiableAt
    simpa [Function.comp_def, hedef] using this
  have hP0 : ∀ᶠ t : ℝ in 𝓝 0, 0 < innerCofactor K (e t) η₁ (σ.cofTwoC (γ t)) := by
    filter_upwards [hev] with t ht
    exact innerCofactor_pos hK (σ.etaTwoC_pos hθ ht.1) (σ.etaOne_pos hz.1) (σ.cofTwoC_pos hθ ht)
  have hH : ∀ᶠ t : ℝ in 𝓝 0, ((A₀ + coneProfile K (e t)) ^ 2 - (3 / 2 - -(3 / 2)) ^ 2) *
      ((3 / 2 - -(3 / 2)) ^ 2 - (A₀ - coneProfile K (e t)) ^ 2) =
      σ.wallTwo (γ t) ^ 2 * innerCofactor K (e t) η₁ (σ.cofTwoC (γ t)) := by
    filter_upwards [hev] with t ht
    have hd := σ.etaOne_mul_etaTwoC_sub hθ ht
    rw [hηc t] at hd
    have h := innerBridge_heron hK hd
    rw [hA₀]
    linear_combination h
  have hbr : ∀ t, σ.bridgeTwoC (γ t) = twoCircle (-(3 / 2)) (3 / 2) A₀ (coneProfile K (e t))
      (σ.wallTwo (γ t)) (innerCofactor K (e t) η₁ (σ.cofTwoC (γ t))) := by
    intro t
    rw [bridgeTwoC, innerBridge, twoCircle_swap, hηc t]
  have hpos : 0 < A₀ + ((twoCircle (-(3 / 2)) (3 / 2) A₀ (coneProfile K (e 0))
      (σ.wallTwo (γ 0)) (innerCofactor K (e 0) η₁ (σ.cofTwoC (γ 0)))).re - -(3 / 2)) := by
    rw [← hbr 0, h0]
    exact σ.bridgeTwoC_cone_pos hθ hz
  have h := hasDerivAt_halfArg_twoCircle' (a := -(3 / 2)) (b := 3 / 2) (by norm_num) hA₀pos hB
    hw hPd hP0 hH hpos
  have he2 : (fun t : ℝ => σ.angleTwoConeC (γ t)) = fun t : ℝ => halfArg A₀
      ((twoCircle (-(3 / 2)) (3 / 2) A₀ (coneProfile K (e t)) (σ.wallTwo (γ t))
        (innerCofactor K (e t) η₁ (σ.cofTwoC (γ t)))).re - -(3 / 2))
      (twoCircle (-(3 / 2)) (3 / 2) A₀ (coneProfile K (e t)) (σ.wallTwo (γ t))
        (innerCofactor K (e t) η₁ (σ.cofTwoC (γ t)))).im := by
    funext t
    rw [angleTwoConeC, hbr t, hηc t, sub_neg_eq_add]
  rw [he2]
  refine ⟨_, ?_, h⟩
  have hsq := Real.sqrt_pos.2 (hP0.self_of_nhds)
  split_ifs with hw0
  · rw [h0] at hw0
    have hnc : ‖c‖ = 1 := by
      rw [hc, Complex.norm_exp]
      simp
    have hre : 0 < (c * ω₀).re := by
      apply re_pos_of_im_eq_zero
      · rw [norm_mul, hnc, one_mul]
        exact hz.2.1
      · have := hwc 0
        rw [h0] at this
        simp only [ofReal_zero, zero_mul, Complex.exp_zero, mul_one] at this
        linarith
    have h3 : (0 : ℝ) < 2 * |3 / 2 - -(3 / 2)| * A₀ := by positivity
    have : 0 < (c * ω₀).re *
        Real.sqrt (innerCofactor K (e 0) η₁ (σ.cofTwoC (γ 0))) /
          (2 * |3 / 2 - -(3 / 2)| * A₀) := by
      positivity
    have e3 : -(c * ω₀).re * Real.sqrt (innerCofactor K (e 0) η₁ (σ.cofTwoC (γ 0))) /
        (2 * |3 / 2 - -(3 / 2)| * A₀) = -((c * ω₀).re *
        Real.sqrt (innerCofactor K (e 0) η₁ (σ.cofTwoC (γ 0))) /
          (2 * |3 / 2 - -(3 / 2)| * A₀)) := by
      ring
    rw [e3]
    linarith
  · have hB0 : 0 < coneProfile K (e 0) := by
      have := half_le_coneProfile hK (e 0)
      linarith
    have e3 : 2 * |(3 / 2 : ℝ) - -(3 / 2)| * coneProfile K (e 0) * κ /
        ((3 / 2 - -(3 / 2)) * Real.sqrt (innerCofactor K (e 0) η₁ (σ.cofTwoC (γ 0)))) =
        2 * coneProfile K (e 0) * κ /
          Real.sqrt (innerCofactor K (e 0) η₁ (σ.cofTwoC (γ 0))) := by
      rw [show |(3 / 2 : ℝ) - -(3 / 2)| = 3 by norm_num]
      field_simp
      ring
    rw [e3]
    have : 2 * coneProfile K (e 0) * κ < 0 := by
      have : 0 < 2 * coneProfile K (e 0) := by positivity
      exact mul_neg_of_pos_of_neg this hκneg
    exact div_neg_of_neg_of_pos this hsq

end ConeShape

end GC.Seifert
