import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldOneConeLayout
import DifferentialGeometry.Compat.Ch567.Tensor.LinearAlgebra.ComplexDeterminant

/-!
# The assembled cone fold `E` of the one-cone shapes

Lane A4b2 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §6 and the
errata after review 15). For a shape with a cusp at `0` (`θ₂ = 0`) and a cone of order `p` at
`v₁` the map `foldE p` (built before the final mirror `u ↦ -conj u`) is
* the cusp-`0` corner `cornerZero` on `R₂ = {η₀ < h}`,
* the apex model `apexBefore p = -3/2 - conj(ω₁)^p/2` on the apex zone `{η₁ < foldA₁}`,
* the cone corner `cornerCone` on the rest of `R₁ = {η₁ < h}`,
* the wall-2 bridge `bridgeTwo` on the lens `|sinh n| < 1/10` outside `R₁ ∪ R₂`,
* the corner at `∞`, `cornerInfW blendWeight`, elsewhere.
`foldE_local`: at every point of the triangle outside the open inner core of the layout,
`foldE p` agrees near the point with a map that is smooth on an open neighbourhood and has
nonzero Jacobian there (off `v₁`). The branch boundaries outside the core are handled by the
agreements J1 (`∂R₂`: `cornerZero = bridgeTwo` for `horoX < foldA₀`, `= bridgeZero` for
`horoX > foldB₀`, where also `cornerInfW = bridgeZero`), J2 (`∂R₁`: `cornerCone = bridgeTwo`
for `φ > foldPhiB`, `= bridgeOne` for `φ < foldPhiA`, where also `cornerInfW = bridgeOne`), the
apex zone (`cornerCone = apexBefore`), and the core certificates (switch windows and the lens
boundary lie in the inner core). The Jacobian of `bridgeTwo` on the lens is that of
`cornerZero`, which agrees with it there (`horoX < foldA₀`).
-/

set_option autoImplicit false

noncomputable section

open Complex Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

theorem det_neg_conj_clm :
    LinearMap.det ((-(conjCLE : ℂ →L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = -1 := by
  rw [LinearMap.det_complex]
  simp

theorem det_fderiv_neg_conj {g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℝ g z) :
    (fderiv ℝ (fun w => -conj (g w)) z).det = -(fderiv ℝ g z).det := by
  have h : HasFDerivAt (fun w => -conj (g w))
      ((-(conjCLE : ℂ →L[ℝ] ℂ)).comp (fderiv ℝ g z)) z :=
    (-(conjCLE : ℂ →L[ℝ] ℂ)).hasFDerivAt.comp z hg.hasFDerivAt
  rw [h.fderiv]
  change LinearMap.det (((-(conjCLE : ℂ →L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) ∘ₗ
    (fderiv ℝ g z : ℂ →ₗ[ℝ] ℂ)) = -LinearMap.det (fderiv ℝ g z : ℂ →ₗ[ℝ] ℂ)
  rw [LinearMap.det_comp, det_neg_conj_clm]
  ring

theorem continuous_det_clm : Continuous fun L : ℂ →L[ℝ] ℂ => L.det := by
  have e : (fun L : ℂ →L[ℝ] ℂ => L.det) =
      fun L => (L 1).re * (L I).im - (L I).re * (L 1).im := by
    funext L
    rw [ContinuousLinearMap.det, LinearMap.det_complex]
    rfl
  rw [e]
  have h1 : Continuous fun L : ℂ →L[ℝ] ℂ => L 1 := continuous_id.clm_apply continuous_const
  have h2 : Continuous fun L : ℂ →L[ℝ] ℂ => L I := continuous_id.clm_apply continuous_const
  fun_prop

theorem eventually_det_ne_zero {g : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (hg : ContDiffOn ℝ ∞ g D)
    {z : ℂ} (hz : z ∈ D) (hdet : (fderiv ℝ g z).det ≠ 0) :
    ∀ᶠ w in 𝓝 z, (fderiv ℝ g w).det ≠ 0 := by
  have hc : ContinuousOn (fun w => (fderiv ℝ g w).det) D :=
    continuous_det_clm.comp_continuousOn (hg.continuousOn_fderiv_of_isOpen hD (by simp))
  exact (hc.continuousAt (hD.mem_nhds hz)).eventually_ne hdet

namespace ConeShape

variable (σ : ConeShape)

def foldE (p : ℕ) (z : ℂ) : ℂ :=
  if cuspZeroHeight z < σ.foldH then σ.cornerZero σ.foldA₀ σ.foldB₀ z
  else if σ.etaOne z < σ.foldA₁ then σ.apexBefore p z
  else if σ.etaOne z < σ.foldH then σ.cornerCone p σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB z
  else if |σ.sinhN z| < 1 / 10 then σ.bridgeTwo z
  else σ.cornerInfW σ.blendWeight σ.foldY₁ σ.foldY₂ z

/-! ### Continuity and smoothness of the pieces -/

theorem continuousAt_etaOne {z : ℂ} (hz : 0 < z.im) : ContinuousAt σ.etaOne z := by
  have hv := σ.vertexOne_im_pos
  have hd : ContinuousAt (coneDisc σ.vertexOne) z := (contDiffAt_coneDisc hv hz).continuousAt
  have hn : ContinuousAt (fun u => ‖coneDisc σ.vertexOne u‖) z := hd.norm
  have h1 : 1 - ‖coneDisc σ.vertexOne z‖ ≠ 0 := (sub_pos.2 (norm_coneDisc_lt_one hv hz)).ne'
  change ContinuousAt (fun u => σ.vertexOne.im * (1 + ‖coneDisc σ.vertexOne u‖) /
    (1 - ‖coneDisc σ.vertexOne u‖)) z
  exact (continuousAt_const.mul (continuousAt_const.add hn)).div (continuousAt_const.sub hn) h1

theorem continuous_wallSide_two : Continuous (σ.wallSide 2) := by
  change Continuous fun z : ℂ => (z.re - σ.centre) ^ 2 + z.im ^ 2 - 1 / 16
  fun_prop

theorem continuousAt_sinhN {z : ℂ} (hz : 0 < z.im) : ContinuousAt σ.sinhN z :=
  (continuousAt_const.mul σ.continuous_wallSide_two.continuousAt).div
    continuous_im.continuousAt hz.ne'

theorem continuousAt_cuspZeroHeight {z : ℂ} (hz : 0 < z.im) : ContinuousAt cuspZeroHeight z :=
  (contDiffAt_cuspZeroHeight hz).continuousAt

theorem continuousAt_discAngle {z : ℂ} (hz : z ∈ σ.domOne) :
    ContinuousAt (fun u => discAngle (σ.discOne u)) z :=
  (σ.contDiffAt_discAngle hz).continuousAt

theorem etaTwo_eq_of_cusp (hθ : σ.θ₂ = 0) : σ.etaTwo = cuspZeroHeight :=
  funext fun z => by simp [etaTwo, hθ]

theorem continuousAt_blendFn (hθ : σ.θ₂ = 0) {z : ℂ} (hz : 0 < z.im) :
    ContinuousAt σ.blendFn z := by
  have h0 := continuousAt_cuspZeroHeight hz
  have h1 := σ.continuousAt_etaOne hz
  have hne : cuspZeroHeight z + σ.etaOne z ≠ 0 :=
    (add_pos (cuspZeroHeight_pos hz) (σ.etaOne_pos hz)).ne'
  have e : σ.blendFn = fun u => 2 * u.re / σ.width - 1 +
      42 * (cuspZeroHeight u - σ.etaOne u) / (cuspZeroHeight u + σ.etaOne u) := by
    funext u
    rw [blendFn, σ.etaTwo_eq_of_cusp hθ]
    rfl
  rw [e]
  exact (((continuousAt_const.mul continuous_re.continuousAt).div_const _).sub
    continuousAt_const).add ((continuousAt_const.mul (h0.sub h1)).div (h0.add h1) hne)

theorem contDiffAt_blendFn (hθ : σ.θ₂ = 0) {z : ℂ} (hz : 0 < z.im) (hzv : z ≠ σ.vertexOne) :
    ContDiffAt ℝ ∞ σ.blendFn z := by
  have h0 := contDiffAt_cuspZeroHeight hz
  have h1 : ContDiffAt ℝ ∞ σ.etaOne z := contDiffAt_coneHeight σ.vertexOne_im_pos hz hzv
  have hne : cuspZeroHeight z + σ.etaOne z ≠ 0 :=
    (add_pos (cuspZeroHeight_pos hz) (σ.etaOne_pos hz)).ne'
  have e : σ.blendFn = fun u => 2 * u.re / σ.width - 1 +
      42 * (cuspZeroHeight u - σ.etaOne u) / (cuspZeroHeight u + σ.etaOne u) := by
    funext u
    rw [blendFn, σ.etaTwo_eq_of_cusp hθ]
    rfl
  rw [e]
  exact ((((contDiffAt_const.mul reCLM.contDiff.contDiffAt).div_const _).sub
    contDiffAt_const)).add ((contDiffAt_const.mul (h0.sub h1)).div (h0.add h1) hne)

theorem contDiffAt_blendWeight (hθ : σ.θ₂ = 0) {z : ℂ} (hz : 0 < z.im)
    (hzv : z ≠ σ.vertexOne) : ContDiffAt ℝ ∞ σ.blendWeight z :=
  (contDiff_coneStep _ _).contDiffAt.comp z (σ.contDiffAt_blendFn hθ hz hzv)

theorem contDiffAt_cornerZero (hθ : σ.θ₂ = 0) (a b : ℝ) {z : ℂ} (hz : z ∈ σ.domTwo) :
    ContDiffAt ℝ ∞ (σ.cornerZero a b) z := by
  have h1 : ContDiffAt ℝ ∞ (fun u => ((coneProfile σ.constK (cuspZeroHeight u) : ℝ) : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z (σ.contDiffAt_holeModulus hz.1)
  have h2 : ContDiffAt ℝ ∞ (fun u : ℂ => exp ((σ.angleHole a b u : ℂ) * I)) z :=
    (Complex.contDiff_exp (𝕜 := ℝ)).contDiffAt.comp z
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp z (σ.contDiffAt_angleHole hθ a b hz)).mul
        contDiffAt_const)
  exact contDiffAt_const.add (h1.mul h2)

theorem contDiffAt_coneRadial (p : ℕ) (a b : ℝ) {η : ℝ} (hη : 0 < η) :
    ContDiffAt ℝ ∞ (coneRadial p a b σ.vertexOne.im σ.constK) η := by
  have hd : η + σ.vertexOne.im ≠ 0 := by linarith [σ.vertexOne_im_pos]
  have hτ := (contDiff_coneStep a b).contDiffAt (x := η)
  have hG := (contDiff_coneProfile σ.constK_pos).contDiffAt (x := η)
  have hq : ContDiffAt ℝ ∞ (fun s : ℝ => (s - σ.vertexOne.im) / (s + σ.vertexOne.im)) η :=
    (contDiffAt_id.sub contDiffAt_const).div (contDiffAt_id.add contDiffAt_const) hd
  change ContDiffAt ℝ ∞ (fun s => (1 - coneStep a b s) *
    ((s - σ.vertexOne.im) / (s + σ.vertexOne.im)) ^ p / 2 +
      coneStep a b s * coneProfile σ.constK s) η
  exact (((contDiffAt_const.sub hτ).mul (hq.pow p)).div_const 2).add (hτ.mul hG)

theorem contDiffAt_cornerCone (hθ : σ.θ₂ = 0) (p : ℕ) (a b φa φb : ℝ) {z : ℂ}
    (hz1 : z ∈ σ.domOne) (hz2 : z ∈ σ.domTwo) :
    ContDiffAt ℝ ∞ (σ.cornerCone p a b φa φb) z := by
  have hS : ContDiffAt ℝ ∞ (fun u => coneRadial p a b σ.vertexOne.im σ.constK (σ.etaOne u)) z :=
    (σ.contDiffAt_coneRadial p a b (σ.etaOne_pos hz1.1)).comp z (σ.contDiffAt_etaOne hz1)
  have h1 : ContDiffAt ℝ ∞
      (fun u => ((coneRadial p a b σ.vertexOne.im σ.constK (σ.etaOne u) : ℝ) : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z hS
  have h2 : ContDiffAt ℝ ∞ (fun u : ℂ => exp ((σ.angleCone p a b φa φb u : ℂ) * I)) z :=
    (Complex.contDiff_exp (𝕜 := ℝ)).contDiffAt.comp z
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp z
        (σ.contDiffAt_angleCone hθ p a b φa φb hz1 hz2)).mul contDiffAt_const)
  exact contDiffAt_const.add (h1.mul h2)

theorem contDiffAt_apexBefore (p : ℕ) {z : ℂ} (hz : 0 < z.im) :
    ContDiffAt ℝ ∞ (σ.apexBefore p) z := by
  have hd := σ.contDiffAt_discOne hz
  have hc : ContDiffAt ℝ ∞ (fun u => conj (σ.discOne u)) z :=
    (conjCLE : ℂ →L[ℝ] ℂ).contDiff.contDiffAt.comp z hd
  exact contDiffAt_const.sub ((hc.pow p).div_const 2)

theorem apexBefore_eq_neg_conj (p : ℕ) :
    σ.apexBefore p = fun z => -conj (σ.coneApexOne p z) :=
  funext fun z => σ.apexBefore_eq p z

theorem det_fderiv_apexBefore_ne_zero {p : ℕ} (hp : p ≠ 0) {z : ℂ} (hz : 0 < z.im)
    (hzv : z ≠ σ.vertexOne) : (fderiv ℝ (σ.apexBefore p) z).det ≠ 0 := by
  have hd : DifferentiableAt ℝ (σ.coneApexOne p) z :=
    ((σ.contDiffOn_coneApexOne p).contDiffAt
      ((isOpen_lt continuous_const continuous_im).mem_nhds hz)).differentiableAt (by simp)
  rw [σ.apexBefore_eq_neg_conj, det_fderiv_neg_conj hd]
  exact neg_ne_zero.2 (σ.det_fderiv_coneApexOne_pos hp hz hzv).ne'

/-! ### Membership facts -/

theorem isOpen_upper : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const continuous_im

theorem sinhN_nonneg_of_mem_triangle {z : ℂ} (hz : z ∈ σ.triangle) : 0 ≤ σ.sinhN z := by
  have := hz.2 2
  have := hz.1
  unfold sinhN
  positivity

theorem etaOne_vertexOne : σ.etaOne σ.vertexOne = σ.vertexOne.im := by
  simp [etaOne, coneHeight, coneDisc_self]

theorem ne_vertexOne_of_foldA₁_le (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)
    (h₂ : Real.cos σ.θ₂ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₂) {z : ℂ} (h : σ.foldA₁ ≤ σ.etaOne z) :
    z ≠ σ.vertexOne := by
  rintro rfl
  rw [σ.etaOne_vertexOne] at h
  linarith [σ.vertexOne_im_lt_foldA₁ h₁ h₂]

theorem ne_vertexOne_of_cuspZeroHeight_le (hθ : σ.θ₂ = 0)
    (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁) {z : ℂ} (h : cuspZeroHeight z ≤ σ.foldH) :
    z ≠ σ.vertexOne := by
  have h₂ : Real.cos σ.θ₂ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₂ :=
    Or.inr (by rw [hθ, Real.cos_zero]; norm_num)
  rintro rfl
  have := σ.foldH_lt_cuspZeroHeight_of_etaOne_le hθ σ.vertexOne_im_pos
    (by rw [σ.etaOne_vertexOne]; exact (σ.vertexOne_im_lt_foldH h₁ h₂).le)
  linarith

/-! ### Local forms of `foldE` at the points of the triangle -/

theorem adm_two_of_cusp (hθ : σ.θ₂ = 0) : Real.cos σ.θ₂ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₂ :=
  Or.inr (by rw [hθ, Real.cos_zero]; norm_num)

theorem re_nonneg_of_triangle {z : ℂ} (hz : z ∈ σ.triangle) : 0 ≤ z.re := hz.2 0

theorem re_le_width_of_mem_triangle {z : ℂ} (hz : z ∈ σ.triangle) : z.re ≤ σ.width := by
  have := hz.2 1
  simp only [wallSide] at this
  linarith

section Local

variable (hθ : σ.θ₂ = 0) (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)

include hθ h₁ in
theorem foldE_local_zero {p : ℕ} {z : ℂ} (hz : z ∈ σ.triangle)
    (h0 : cuspZeroHeight z < σ.foldH) :
    ∃ g : ℂ → ℂ, ∃ D : Set ℂ, IsOpen D ∧ z ∈ D ∧ ContDiffOn ℝ ∞ g D ∧
      σ.foldE p =ᶠ[𝓝 z] g ∧ (z ≠ σ.vertexOne → (fderiv ℝ g z).det ≠ 0) := by
  have hzv := σ.ne_vertexOne_of_cuspZeroHeight_le hθ h₁ h0.le
  have hz2 := σ.mem_domTwo_of_mem_triangle hz hzv
  refine ⟨σ.cornerZero σ.foldA₀ σ.foldB₀, σ.domTwo, σ.isOpen_domTwo, hz2,
    fun w hw => (σ.contDiffAt_cornerZero hθ _ _ hw).contDiffWithinAt, ?_, fun _ => ?_⟩
  · filter_upwards [(continuousAt_cuspZeroHeight hz.1).eventually_lt continuousAt_const h0]
      with w hw
    simp only [foldE, hw, ↓reduceIte]
  · exact σ.det_fderiv_cornerZero_ne_zero hθ σ.foldA₀_lt_foldB₀ hz2
      (σ.angleZeroHole_le_angleTwoHole hθ hz2 (σ.re_nonneg_of_triangle hz)
        (σ.wallTwo_nonneg_of_mem_triangle hz))

include hθ h₁ in
theorem foldE_local_apex {p : ℕ} (hp : p ≠ 0) {z : ℂ} (hz : 0 < z.im)
    (h1 : σ.etaOne z < σ.foldA₁) :
    ∃ g : ℂ → ℂ, ∃ D : Set ℂ, IsOpen D ∧ z ∈ D ∧ ContDiffOn ℝ ∞ g D ∧
      σ.foldE p =ᶠ[𝓝 z] g ∧ (z ≠ σ.vertexOne → (fderiv ℝ g z).det ≠ 0) := by
  have h₂ := σ.adm_two_of_cusp hθ
  have hAB := σ.foldA₁_lt_foldB₁ h₁ h₂
  have hBH := σ.foldB₁_lt_foldH h₁ h₂
  have h0 : σ.foldH < cuspZeroHeight z :=
    σ.foldH_lt_cuspZeroHeight_of_etaOne_le hθ hz (by linarith)
  refine ⟨σ.apexBefore p, {w | 0 < w.im}, isOpen_upper, hz,
    fun w hw => (σ.contDiffAt_apexBefore p hw).contDiffWithinAt, ?_,
    fun hzv => σ.det_fderiv_apexBefore_ne_zero hp hz hzv⟩
  filter_upwards [continuousAt_const.eventually_lt (continuousAt_cuspZeroHeight hz) h0,
    (σ.continuousAt_etaOne hz).eventually_lt continuousAt_const h1] with w hw0 hw1
  simp only [foldE, (not_lt.2 hw0.le), hw1, ↓reduceIte]

include hθ h₁ in
theorem foldE_local_cone {p : ℕ} (hp : 1 ≤ p) {z : ℂ} (hz : z ∈ σ.triangle)
    (ha : σ.foldA₁ ≤ σ.etaOne z) (h1 : σ.etaOne z < σ.foldH) :
    ∃ g : ℂ → ℂ, ∃ D : Set ℂ, IsOpen D ∧ z ∈ D ∧ ContDiffOn ℝ ∞ g D ∧
      σ.foldE p =ᶠ[𝓝 z] g ∧ (z ≠ σ.vertexOne → (fderiv ℝ g z).det ≠ 0) := by
  have h₂ := σ.adm_two_of_cusp hθ
  have hzv := σ.ne_vertexOne_of_foldA₁_le h₁ h₂ ha
  have hz1 := σ.mem_domOne_of_mem_triangle hz hzv
  have hz2 := σ.mem_domTwo_of_mem_triangle hz hzv
  have hAB := σ.foldA₁_lt_foldB₁ h₁ h₂
  have hφ := σ.foldPhiA_lt_foldPhiB h₁ h₂
  have h0 : σ.foldH < cuspZeroHeight z := σ.foldH_lt_cuspZeroHeight_of_etaOne_le hθ hz.1 h1.le
  refine ⟨σ.cornerCone p σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB, σ.domOne ∩ σ.domTwo,
    σ.isOpen_domOne.inter σ.isOpen_domTwo, ⟨hz1, hz2⟩,
    fun w hw => (σ.contDiffAt_cornerCone hθ p _ _ _ _ hw.1 hw.2).contDiffWithinAt, ?_, fun _ => ?_⟩
  · filter_upwards [continuousAt_const.eventually_lt (continuousAt_cuspZeroHeight hz.1) h0,
      (σ.continuousAt_etaOne hz.1).eventually_lt continuousAt_const h1,
      σ.isOpen_domOne.mem_nhds hz1] with w hw0 hw1 hwd
    by_cases hwa : σ.etaOne w < σ.foldA₁
    · simp only [foldE, (not_lt.2 hw0.le), hwa, ↓reduceIte]
      exact (σ.cornerCone_eq_apex hp hAB hwd.1 (Or.inr hwd) hwa.le).symm
    · simp only [foldE, (not_lt.2 hw0.le), hwa, hw1, ↓reduceIte]
  · exact σ.det_fderiv_cornerCone_ne_zero hθ hp hAB hφ hz1 hz2
      (σ.angleTwoCone_le_angleOneCone hθ hz1 hz2 (σ.wallOne_nonneg_of_mem_triangle hz)
        (σ.wallTwo_nonneg_of_mem_triangle hz))

include hθ h₁ in
theorem foldE_local_J1_lens {p : ℕ} {z : ℂ} (hz : z ∈ σ.triangle)
    (he : cuspZeroHeight z = σ.foldH) (hs : σ.sinhN z < 1 / 10) :
    ∃ g : ℂ → ℂ, ∃ D : Set ℂ, IsOpen D ∧ z ∈ D ∧ ContDiffOn ℝ ∞ g D ∧
      σ.foldE p =ᶠ[𝓝 z] g ∧ (z ≠ σ.vertexOne → (fderiv ℝ g z).det ≠ 0) := by
  have h₂ := σ.adm_two_of_cusp hθ
  have hzv := σ.ne_vertexOne_of_cuspZeroHeight_le hθ h₁ he.le
  have hz2 := σ.mem_domTwo_of_mem_triangle hz hzv
  have hX : horoX z < σ.foldA₀ := σ.horoX_lt_foldA₀ hθ hz.1 he.ge hs
  have h1 : σ.foldH < σ.etaOne z := σ.foldH_lt_etaOne_of_cuspZeroHeight_le hθ hz.1 he.le
  have hAH : σ.foldA₁ < σ.foldH :=
    lt_trans (σ.foldA₁_lt_foldB₁ h₁ h₂) (σ.foldB₁_lt_foldH h₁ h₂)
  have hs' : |σ.sinhN z| < 1 / 10 := by rwa [abs_of_nonneg (σ.sinhN_nonneg_of_mem_triangle hz)]
  have hcz : σ.cornerZero σ.foldA₀ σ.foldB₀ =ᶠ[𝓝 z] σ.bridgeTwo := by
    filter_upwards [σ.isOpen_domTwo.mem_nhds hz2,
      (contDiffAt_horoX hz.1).continuousAt.eventually_lt continuousAt_const hX] with w hw hwX
    exact σ.cornerZero_eq_bridgeTwo hθ σ.foldA₀_lt_foldB₀ hw hwX.le
  refine ⟨σ.bridgeTwo, σ.domTwo, σ.isOpen_domTwo, hz2,
    fun w hw => (σ.contDiffAt_bridgeTwo hw).contDiffWithinAt, ?_, fun _ => ?_⟩
  · filter_upwards [hcz, continuousAt_const.eventually_lt (σ.continuousAt_etaOne hz.1) h1,
      (continuous_abs.continuousAt.comp (σ.continuousAt_sinhN hz.1)).eventually_lt
        continuousAt_const hs'] with w hcw hw1 hwL
    by_cases hw0 : cuspZeroHeight w < σ.foldH
    · simp only [foldE, hw0, ↓reduceIte]
      exact hcw
    · simp only [Function.comp] at hwL
      simp only [foldE, hw0, (not_lt.2 (le_trans hAH.le hw1.le)),
        (not_lt.2 hw1.le), hwL, ↓reduceIte]
  · rw [← hcz.fderiv_eq]
    exact σ.det_fderiv_cornerZero_ne_zero hθ σ.foldA₀_lt_foldB₀ hz2
      (σ.angleZeroHole_le_angleTwoHole hθ hz2 (σ.re_nonneg_of_triangle hz)
        (σ.wallTwo_nonneg_of_mem_triangle hz))

include hθ h₁ in
theorem foldE_local_J1_wall {p : ℕ} {z : ℂ} (hz : z ∈ σ.triangle)
    (he : cuspZeroHeight z = σ.foldH) (hs : 7 / 50 < σ.sinhN z) :
    ∃ g : ℂ → ℂ, ∃ D : Set ℂ, IsOpen D ∧ z ∈ D ∧ ContDiffOn ℝ ∞ g D ∧
      σ.foldE p =ᶠ[𝓝 z] g ∧ (z ≠ σ.vertexOne → (fderiv ℝ g z).det ≠ 0) := by
  have h₂ := σ.adm_two_of_cusp hθ
  have hzv := σ.ne_vertexOne_of_cuspZeroHeight_le hθ h₁ he.le
  have hz2 := σ.mem_domTwo_of_mem_triangle hz hzv
  have hX : σ.foldB₀ < horoX z := σ.foldB₀_lt_horoX hθ hz.1 he.le hs
  have h1 : σ.foldH < σ.etaOne z := σ.foldH_lt_etaOne_of_cuspZeroHeight_le hθ hz.1 he.le
  have hAH : σ.foldA₁ < σ.foldH :=
    lt_trans (σ.foldA₁_lt_foldB₁ h₁ h₂) (σ.foldB₁_lt_foldH h₁ h₂)
  have hs' : 1 / 10 < |σ.sinhN z| := by
    rw [abs_of_nonneg (σ.sinhN_nonneg_of_mem_triangle hz)]; linarith
  have hbl : σ.blendFn z < -1 / 2 := by
    have := σ.blendFn_le_of_etaTwo_le hz.1 (σ.re_le_width_of_mem_triangle hz)
      (by rw [σ.etaTwo_eq_of_cusp hθ, he, foldH_eq])
    linarith
  have hy : z.im < σ.foldY₁ :=
    lt_of_le_of_lt (le_trans (im_le_cuspZeroHeight hz.1) he.le) σ.foldH_lt_foldY₁
  have hcz : σ.cornerZero σ.foldA₀ σ.foldB₀ =ᶠ[𝓝 z] σ.bridgeZero := by
    filter_upwards [isOpen_upper.mem_nhds hz.1,
      continuousAt_const.eventually_lt (contDiffAt_horoX hz.1).continuousAt hX] with w hw hwX
    exact σ.cornerZero_eq_bridgeZero σ.foldA₀_lt_foldB₀ hw hwX.le
  refine ⟨σ.bridgeZero, {w | 0 < w.im}, isOpen_upper, hz.1,
    fun w hw => (σ.contDiffAt_bridgeZero hw).contDiffWithinAt, ?_, fun _ => ?_⟩
  · filter_upwards [hcz, continuousAt_const.eventually_lt (σ.continuousAt_etaOne hz.1) h1,
      continuousAt_const.eventually_lt
        (continuous_abs.continuousAt.comp (σ.continuousAt_sinhN hz.1)) hs',
      (σ.continuousAt_blendFn hθ hz.1).eventually_lt continuousAt_const hbl,
      continuous_im.continuousAt.eventually_lt continuousAt_const hy,
      isOpen_upper.mem_nhds hz.1] with w hcw hw1 hwL hwb hwy hwu
    by_cases hw0 : cuspZeroHeight w < σ.foldH
    · simp only [foldE, hw0, ↓reduceIte]
      exact hcw
    · simp only [Function.comp] at hwL
      simp only [foldE, hw0, (not_lt.2 (le_trans hAH.le hw1.le)),
        (not_lt.2 hw1.le), (not_lt.2 hwL.le), ↓reduceIte]
      exact σ.cornerInfW_eq_bridgeZero σ.foldY₁_lt_foldY₂ hwu (σ.blendWeight_eq_zero hwb.le)
        hwy.le
  · rw [← hcz.fderiv_eq]
    exact σ.det_fderiv_cornerZero_ne_zero hθ σ.foldA₀_lt_foldB₀ hz2
      (σ.angleZeroHole_le_angleTwoHole hθ hz2 (σ.re_nonneg_of_triangle hz)
        (σ.wallTwo_nonneg_of_mem_triangle hz))

include hθ h₁ in
theorem foldE_local_J2_lens {p : ℕ} (hp : 1 ≤ p) {z : ℂ} (hz : z ∈ σ.triangle)
    (he : σ.etaOne z = σ.foldH) (hs : σ.sinhN z < 1 / 10) :
    ∃ g : ℂ → ℂ, ∃ D : Set ℂ, IsOpen D ∧ z ∈ D ∧ ContDiffOn ℝ ∞ g D ∧
      σ.foldE p =ᶠ[𝓝 z] g ∧ (z ≠ σ.vertexOne → (fderiv ℝ g z).det ≠ 0) := by
  have h₂ := σ.adm_two_of_cusp hθ
  have hAB := σ.foldA₁_lt_foldB₁ h₁ h₂
  have hBH := σ.foldB₁_lt_foldH h₁ h₂
  have hzv := σ.ne_vertexOne_of_foldA₁_le h₁ h₂ (by rw [he]; linarith)
  have hz1 := σ.mem_domOne_of_mem_triangle hz hzv
  have hz2 := σ.mem_domTwo_of_mem_triangle hz hzv
  have hφ := σ.foldPhiA_lt_foldPhiB h₁ h₂
  have hφb := σ.foldPhiB_lt_of_sinhN_lt h₁ h₂ hz1 he (σ.discAngle_mem_of_mem_triangle hz hzv) hs
  have h0 : σ.foldH < cuspZeroHeight z := σ.foldH_lt_cuspZeroHeight_of_etaOne_le hθ hz.1 he.le
  have hb : σ.foldB₁ < σ.etaOne z := by rw [he]; exact hBH
  have hs' : |σ.sinhN z| < 1 / 10 := by rwa [abs_of_nonneg (σ.sinhN_nonneg_of_mem_triangle hz)]
  have hcc : σ.cornerCone p σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB =ᶠ[𝓝 z] σ.bridgeTwo := by
    filter_upwards [σ.isOpen_domTwo.mem_nhds hz2,
      continuousAt_const.eventually_lt (σ.continuousAt_etaOne hz.1) hb,
      continuousAt_const.eventually_lt (σ.continuousAt_discAngle hz1) hφb] with w hw2 hwb hwφ
    exact σ.cornerCone_eq_bridgeTwo hθ p hAB hφ hw2 hwb.le hwφ.le
  refine ⟨σ.bridgeTwo, σ.domTwo, σ.isOpen_domTwo, hz2,
    fun w hw => (σ.contDiffAt_bridgeTwo hw).contDiffWithinAt, ?_, fun _ => ?_⟩
  · filter_upwards [hcc, continuousAt_const.eventually_lt (continuousAt_cuspZeroHeight hz.1) h0,
      continuousAt_const.eventually_lt (σ.continuousAt_etaOne hz.1) hb,
      (continuous_abs.continuousAt.comp (σ.continuousAt_sinhN hz.1)).eventually_lt
        continuousAt_const hs'] with w hcw hw0 hwb hwL
    have hwa : ¬ σ.etaOne w < σ.foldA₁ := not_lt.2 (by linarith)
    by_cases hw1 : σ.etaOne w < σ.foldH
    · simp only [foldE, (not_lt.2 hw0.le), hwa, hw1, ↓reduceIte]
      exact hcw
    · simp only [Function.comp] at hwL
      simp only [foldE, (not_lt.2 hw0.le), hwa, hw1, hwL, ↓reduceIte]
  · rw [← hcc.fderiv_eq]
    exact σ.det_fderiv_cornerCone_ne_zero hθ hp hAB hφ hz1 hz2
      (σ.angleTwoCone_le_angleOneCone hθ hz1 hz2 (σ.wallOne_nonneg_of_mem_triangle hz)
        (σ.wallTwo_nonneg_of_mem_triangle hz))

include hθ h₁ in
theorem foldE_local_J2_wall {p : ℕ} (hp : 1 ≤ p) {z : ℂ} (hz : z ∈ σ.triangle)
    (he : σ.etaOne z = σ.foldH) (hs : 7 / 50 < σ.sinhN z) :
    ∃ g : ℂ → ℂ, ∃ D : Set ℂ, IsOpen D ∧ z ∈ D ∧ ContDiffOn ℝ ∞ g D ∧
      σ.foldE p =ᶠ[𝓝 z] g ∧ (z ≠ σ.vertexOne → (fderiv ℝ g z).det ≠ 0) := by
  have h₂ := σ.adm_two_of_cusp hθ
  have hAB := σ.foldA₁_lt_foldB₁ h₁ h₂
  have hBH := σ.foldB₁_lt_foldH h₁ h₂
  have hzv := σ.ne_vertexOne_of_foldA₁_le h₁ h₂ (by rw [he]; linarith)
  have hz1 := σ.mem_domOne_of_mem_triangle hz hzv
  have hz2 := σ.mem_domTwo_of_mem_triangle hz hzv
  have hφ := σ.foldPhiA_lt_foldPhiB h₁ h₂
  have hφa := σ.lt_foldPhiA_of_sinhN_gt h₁ h₂ hz1 he (σ.discAngle_mem_of_mem_triangle hz hzv) hs
  have h0 : σ.foldH < cuspZeroHeight z := σ.foldH_lt_cuspZeroHeight_of_etaOne_le hθ hz.1 he.le
  have hb : σ.foldB₁ < σ.etaOne z := by rw [he]; exact hBH
  have hs' : 1 / 10 < |σ.sinhN z| := by
    rw [abs_of_nonneg (σ.sinhN_nonneg_of_mem_triangle hz)]; linarith
  have hbl : 1 / 2 < σ.blendFn z := by
    have := σ.one_le_blendFn_of_etaOne_le hz.1 (σ.re_nonneg_of_triangle hz)
      (by change σ.etaOne z ≤ _; rw [he, foldH_eq])
    linarith
  have hy : z.im < σ.foldY₁ :=
    lt_of_le_of_lt (le_trans (σ.im_le_etaOne hz1) he.le) σ.foldH_lt_foldY₁
  have hcc : σ.cornerCone p σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB =ᶠ[𝓝 z] σ.bridgeOne := by
    filter_upwards [σ.isOpen_domOne.mem_nhds hz1,
      continuousAt_const.eventually_lt (σ.continuousAt_etaOne hz.1) hb,
      (σ.continuousAt_discAngle hz1).eventually_lt continuousAt_const hφa] with w hw1 hwb hwφ
    exact σ.cornerCone_eq_bridgeOne p hAB hφ hw1 hwb.le hwφ.le
  refine ⟨σ.bridgeOne, σ.domOne, σ.isOpen_domOne, hz1,
    fun w hw => (σ.contDiffAt_bridgeOne hw).contDiffWithinAt, ?_, fun _ => ?_⟩
  · filter_upwards [hcc, continuousAt_const.eventually_lt (continuousAt_cuspZeroHeight hz.1) h0,
      continuousAt_const.eventually_lt (σ.continuousAt_etaOne hz.1) hb,
      continuousAt_const.eventually_lt
        (continuous_abs.continuousAt.comp (σ.continuousAt_sinhN hz.1)) hs',
      continuousAt_const.eventually_lt (σ.continuousAt_blendFn hθ hz.1) hbl,
      continuous_im.continuousAt.eventually_lt continuousAt_const hy,
      σ.isOpen_domOne.mem_nhds hz1] with w hcw hw0 hwb hwL hwbl hwy hwd
    have hwa : ¬ σ.etaOne w < σ.foldA₁ := not_lt.2 (by linarith)
    by_cases hw1 : σ.etaOne w < σ.foldH
    · simp only [foldE, (not_lt.2 hw0.le), hwa, hw1, ↓reduceIte]
      exact hcw
    · simp only [Function.comp] at hwL
      simp only [foldE, (not_lt.2 hw0.le), hwa, hw1,
        (not_lt.2 hwL.le), ↓reduceIte]
      exact σ.cornerInfW_eq_bridgeOne σ.foldY₁_lt_foldY₂ hwd (σ.blendWeight_eq_one hwbl.le)
        hwy.le
  · rw [← hcc.fderiv_eq]
    exact σ.det_fderiv_cornerCone_ne_zero hθ hp hAB hφ hz1 hz2
      (σ.angleTwoCone_le_angleOneCone hθ hz1 hz2 (σ.wallOne_nonneg_of_mem_triangle hz)
        (σ.wallTwo_nonneg_of_mem_triangle hz))

include hθ h₁ in
theorem foldE_local_lens {p : ℕ} {z : ℂ} (hz : z ∈ σ.triangle)
    (h0 : σ.foldH < cuspZeroHeight z) (h1 : σ.foldH < σ.etaOne z) (hL : |σ.sinhN z| < 1 / 10) :
    ∃ g : ℂ → ℂ, ∃ D : Set ℂ, IsOpen D ∧ z ∈ D ∧ ContDiffOn ℝ ∞ g D ∧
      σ.foldE p =ᶠ[𝓝 z] g ∧ (z ≠ σ.vertexOne → (fderiv ℝ g z).det ≠ 0) := by
  have h₂ := σ.adm_two_of_cusp hθ
  have hAH : σ.foldA₁ < σ.foldH :=
    lt_trans (σ.foldA₁_lt_foldB₁ h₁ h₂) (σ.foldB₁_lt_foldH h₁ h₂)
  have hzv := σ.ne_vertexOne_of_foldA₁_le h₁ h₂ (by linarith)
  have hz2 := σ.mem_domTwo_of_mem_triangle hz hzv
  have hX : horoX z < σ.foldA₀ :=
    σ.horoX_lt_foldA₀ hθ hz.1 h0.le (lt_of_le_of_lt (le_abs_self _) hL)
  have hcz : σ.cornerZero σ.foldA₀ σ.foldB₀ =ᶠ[𝓝 z] σ.bridgeTwo := by
    filter_upwards [σ.isOpen_domTwo.mem_nhds hz2,
      (contDiffAt_horoX hz.1).continuousAt.eventually_lt continuousAt_const hX] with w hw hwX
    exact σ.cornerZero_eq_bridgeTwo hθ σ.foldA₀_lt_foldB₀ hw hwX.le
  refine ⟨σ.bridgeTwo, σ.domTwo, σ.isOpen_domTwo, hz2,
    fun w hw => (σ.contDiffAt_bridgeTwo hw).contDiffWithinAt, ?_, fun _ => ?_⟩
  · filter_upwards [continuousAt_const.eventually_lt (continuousAt_cuspZeroHeight hz.1) h0,
      continuousAt_const.eventually_lt (σ.continuousAt_etaOne hz.1) h1,
      (continuous_abs.continuousAt.comp (σ.continuousAt_sinhN hz.1)).eventually_lt
        continuousAt_const hL] with w hw0 hw1 hwL
    simp only [Function.comp] at hwL
    simp only [foldE, (not_lt.2 hw0.le), (not_lt.2 (le_trans hAH.le hw1.le)),
      (not_lt.2 hw1.le), hwL, ↓reduceIte]
  · rw [← hcz.fderiv_eq]
    exact σ.det_fderiv_cornerZero_ne_zero hθ σ.foldA₀_lt_foldB₀ hz2
      (σ.angleZeroHole_le_angleTwoHole hθ hz2 (σ.re_nonneg_of_triangle hz)
        (σ.wallTwo_nonneg_of_mem_triangle hz))

include hθ h₁ in
theorem foldE_local_inf {p : ℕ} {z : ℂ} (hz : z ∈ σ.triangle)
    (h0 : σ.foldH < cuspZeroHeight z) (h1 : σ.foldH < σ.etaOne z) (hL : 1 / 10 < |σ.sinhN z|) :
    ∃ g : ℂ → ℂ, ∃ D : Set ℂ, IsOpen D ∧ z ∈ D ∧ ContDiffOn ℝ ∞ g D ∧
      σ.foldE p =ᶠ[𝓝 z] g ∧ (z ≠ σ.vertexOne → (fderiv ℝ g z).det ≠ 0) := by
  have h₂ := σ.adm_two_of_cusp hθ
  have hAH : σ.foldA₁ < σ.foldH :=
    lt_trans (σ.foldA₁_lt_foldB₁ h₁ h₂) (σ.foldB₁_lt_foldH h₁ h₂)
  have hzv := σ.ne_vertexOne_of_foldA₁_le h₁ h₂ (by linarith)
  have hz1 := σ.mem_domOne_of_mem_triangle hz hzv
  refine ⟨σ.cornerInfW σ.blendWeight σ.foldY₁ σ.foldY₂, σ.domOne, σ.isOpen_domOne, hz1,
    fun w hw => (σ.contDiffAt_cornerInfW _ _ hw (σ.contDiffAt_blendWeight hθ hw.1
      (σ.vertexOne_ne_of_domOne hw))).contDiffWithinAt, ?_, fun _ => ?_⟩
  · filter_upwards [continuousAt_const.eventually_lt (continuousAt_cuspZeroHeight hz.1) h0,
      continuousAt_const.eventually_lt (σ.continuousAt_etaOne hz.1) h1,
      continuousAt_const.eventually_lt
        (continuous_abs.continuousAt.comp (σ.continuousAt_sinhN hz.1)) hL] with w hw0 hw1 hwL
    simp only [Function.comp] at hwL
    simp only [foldE, (not_lt.2 hw0.le), (not_lt.2 (le_trans hAH.le hw1.le)),
      (not_lt.2 hw1.le), (not_lt.2 hwL.le), ↓reduceIte]
  · obtain ⟨d, hd, hdd⟩ := σ.exists_hasDerivAt_blendWeight hz.1 hzv (fun h => absurd hθ h)
      (σ.re_nonneg_of_triangle hz) (σ.re_le_width_of_mem_triangle hz)
    exact σ.det_fderiv_cornerInfW_ne_zero σ.foldY₁_pos.le σ.foldY₁_lt_foldY₂ σ.foldY₂_lt_sqrt
      σ.sqrt_constK_le_half hz1 (σ.contDiffAt_blendWeight hθ hz.1 hzv) hdd hd
      (σ.blendWeight_nonneg z) (σ.blendWeight_le_one z)

include hθ h₁ in
theorem foldE_local {p : ℕ} (hp : 1 ≤ p) {z : ℂ} (hz : z ∈ σ.triangle)
    (hcore : ConeLayout.coreInner ^ 2 ≤ normSq (σ.fermiChart z - ConeLayout.coreCentre)) :
    ∃ g : ℂ → ℂ, ∃ D : Set ℂ, IsOpen D ∧ z ∈ D ∧ ContDiffOn ℝ ∞ g D ∧
      σ.foldE p =ᶠ[𝓝 z] g ∧ (z ≠ σ.vertexOne → (fderiv ℝ g z).det ≠ 0) := by
  have h₂ := σ.adm_two_of_cusp hθ
  have hc : ¬ normSq (σ.fermiChart z - ConeLayout.coreCentre) < ConeLayout.coreInner ^ 2 :=
    not_lt.2 hcore
  have hsn := σ.sinhN_nonneg_of_mem_triangle hz
  rcases lt_trichotomy (cuspZeroHeight z) σ.foldH with h0 | h0 | h0
  · exact σ.foldE_local_zero hθ h₁ hz h0
  · rcases lt_or_ge (σ.sinhN z) (1 / 10) with hs | hs
    · exact σ.foldE_local_J1_lens hθ h₁ hz h0 hs
    rcases lt_or_ge (7 / 50) (σ.sinhN z) with hs' | hs'
    · exact σ.foldE_local_J1_wall hθ h₁ hz h0 hs'
    · exact absurd (σ.inner_core_of_windowTwo hθ hz h0 hs hs') hc
  · rcases lt_or_ge (σ.etaOne z) σ.foldA₁ with ha | ha
    · exact σ.foldE_local_apex hθ h₁ (by omega) hz.1 ha
    rcases lt_trichotomy (σ.etaOne z) σ.foldH with h1 | h1 | h1
    · exact σ.foldE_local_cone hθ h₁ hp hz ha h1
    · rcases lt_or_ge (σ.sinhN z) (1 / 10) with hs | hs
      · exact σ.foldE_local_J2_lens hθ h₁ hp hz h1 hs
      rcases lt_or_ge (7 / 50) (σ.sinhN z) with hs' | hs'
      · exact σ.foldE_local_J2_wall hθ h₁ hp hz h1 hs'
      · exact absurd (σ.inner_core_of_windowOne h₁ h₂ hz h1 hs hs') hc
    · rcases lt_trichotomy |σ.sinhN z| (1 / 10) with hL | hL | hL
      · exact σ.foldE_local_lens hθ h₁ hz h0 h1 hL
      · rw [abs_of_nonneg hsn] at hL
        exact absurd (σ.inner_core_of_lens hθ h₁ hz h0.le h1.le hL) hc
      · exact σ.foldE_local_inf hθ h₁ hz h0 h1 hL

end Local

end ConeShape

end GC.Seifert
