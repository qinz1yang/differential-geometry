import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldSpec
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.CliffordCoordinates
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClassicalInputs
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# The fibre phase of the cone-fold descent

For the one-cone shape `(p, ⊤, ⊤)` the total-space fold is `(z, s) ↦ coneLift (f z, e^{2πis}
Ψ(z)⁻¹)` with a circle-valued phase `Ψ = foldPhase q`. Near the apex `v = vertexOne` and near walls
1 and 2 it must be `unitOf (ω_v z) ^ q` (`ω_v = coneDisc v`), near wall 0 it must be constant `1`;
the two are glued by the weight `foldChi`, a smooth step in `foldSplit z = Re z (1 + 1/|z|²)`, which
vanishes on wall 0, is odd under `σ₀`, and is `≥ width` on `{Re z ≥ width}` and on wall 2 (where
`|z|² = Re z / 2`). On `foldFar = {foldSplit > 2 width/3}` the phase is `unitOf (ω_v) ^ q`, on
`foldNear = {foldSplit < width/3}` it is `1`, and it is smooth on the upper half-plane minus `v`
because `ω_v` lies in the slit plane wherever `foldSplit < width`. The wall identities `Ψ ∘ σ₁ =
Ψ⁻¹`, `Ψ ∘ σ₂ = exp(2 q θ₁) Ψ⁻¹`, `Ψ ∘ σ₀ = Ψ⁻¹` hold on the corresponding regions.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology
open scoped ContDiff ComplexConjugate Manifold
open GC.GraphManifold

namespace GC.Seifert

theorem circleExp_int_mul_arg {w : ℂ} (hw : w ≠ 0) (q : ℤ) :
    Circle.exp (q * arg w) = unitOf w ^ q := by
  apply Circle.ext
  rw [Circle.coe_zpow, Circle.coe_exp, coe_unitOf hw]
  have hn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hw
  have h1 : (‖w‖⁻¹ : ℝ) • w = exp (arg w * I) := by
    rw [Complex.real_smul]
    calc ((‖w‖⁻¹ : ℝ) : ℂ) * w = ((‖w‖⁻¹ : ℝ) : ℂ) * ((‖w‖ : ℂ) * exp (arg w * I)) := by
          rw [norm_mul_exp_arg_mul_I]
      _ = exp (arg w * I) := by
          push_cast
          rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  rw [h1, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem unitOf_conj {w : ℂ} (hw : w ≠ 0) : unitOf (conj w) = (unitOf w)⁻¹ := by
  apply Circle.ext
  rw [Circle.coe_inv_eq_conj, coe_unitOf hw, coe_unitOf ((map_ne_zero _).mpr hw)]
  rw [Complex.real_smul, Complex.real_smul, map_mul, Complex.conj_ofReal, Complex.norm_conj]

theorem unitOf_circle_mul' (u : Circle) {w : ℂ} (hw : w ≠ 0) :
    unitOf ((u : ℂ) * w) = u * unitOf w := by
  apply Circle.ext
  rw [Circle.coe_mul, coe_unitOf (mul_ne_zero (Circle.coe_ne_zero u) hw), coe_unitOf hw]
  rw [norm_mul, Circle.norm_coe, one_mul, Complex.real_smul, Complex.real_smul]
  ring

namespace ConeShape

variable (σ : ConeShape)

def foldSplit (z : ℂ) : ℝ := z.re * (1 + 1 / normSq z)

def foldChi (z : ℂ) : ℝ := 1 - coneStep (σ.width / 3) (2 * σ.width / 3) (foldSplit z)

def foldPhase (q : ℤ) (z : ℂ) : Circle :=
  Circle.exp (q * ((1 - σ.foldChi z) * arg (coneDisc σ.vertexOne z)))

def foldFar : Set ℂ := {z | 0 < z.im ∧ 2 * σ.width / 3 < foldSplit z}

def foldNear : Set ℂ := {z | 0 < z.im ∧ foldSplit z < σ.width / 3}

theorem foldSplit_refl_zero (z : ℂ) : foldSplit (σ.refl 0 z) = -foldSplit z := by
  simp [foldSplit, refl, Complex.normSq_neg, Complex.normSq_conj]

theorem width_le_half : σ.width ≤ 1 / 2 := by
  have h1 := Real.cos_le_one σ.θ₁
  have h2 := Real.cos_le_one σ.θ₂
  unfold width
  linarith

theorem contDiffAt_foldSplit {z : ℂ} (hz : z ≠ 0) : ContDiffAt ℝ ∞ foldSplit z := by
  have hn : normSq z ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
  unfold foldSplit
  have h1 : ContDiffAt ℝ ∞ (fun w : ℂ => w.re) z := Complex.reCLM.contDiff.contDiffAt
  have h2 : ContDiffAt ℝ ∞ (fun w : ℂ => normSq w) z := by
    have he : (fun w : ℂ => normSq w) = fun w => w.re * w.re + w.im * w.im :=
      funext Complex.normSq_apply
    rw [he]
    exact ((Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)).contDiffAt
  exact h1.mul (contDiffAt_const.add (contDiffAt_const.div h2 hn))

theorem continuousAt_foldSplit {z : ℂ} (hz : z ≠ 0) : ContinuousAt foldSplit z :=
  (contDiffAt_foldSplit hz).continuousAt

theorem ne_zero_of_im_pos {z : ℂ} (hz : 0 < z.im) : z ≠ 0 := by
  rintro rfl
  simp at hz

theorem isOpen_foldFar : IsOpen σ.foldFar := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨hz, hs⟩
  have h1 : {w : ℂ | 0 < w.im} ∈ 𝓝 z := (isOpen_lt continuous_const continuous_im).mem_nhds hz
  have h2 : {w : ℂ | 2 * σ.width / 3 < foldSplit w} ∈ 𝓝 z :=
    (continuousAt_foldSplit (ne_zero_of_im_pos hz)).preimage_mem_nhds (Ioi_mem_nhds hs)
  filter_upwards [h1, h2] with w hw1 hw2
  exact ⟨hw1, hw2⟩

theorem isOpen_foldNear : IsOpen σ.foldNear := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨hz, hs⟩
  have h1 : {w : ℂ | 0 < w.im} ∈ 𝓝 z := (isOpen_lt continuous_const continuous_im).mem_nhds hz
  have h2 : {w : ℂ | foldSplit w < σ.width / 3} ∈ 𝓝 z :=
    (continuousAt_foldSplit (ne_zero_of_im_pos hz)).preimage_mem_nhds (Iio_mem_nhds hs)
  filter_upwards [h1, h2] with w hw1 hw2
  exact ⟨hw1, hw2⟩

theorem foldChi_eq_zero {z : ℂ} (hz : z ∈ σ.foldFar) : σ.foldChi z = 0 := by
  have hW := σ.width_pos
  unfold foldChi
  rw [coneStep_eq_one (by linarith) hz.2.le]
  ring

theorem foldChi_eq_one {z : ℂ} (hz : z ∈ σ.foldNear) : σ.foldChi z = 1 := by
  have hW := σ.width_pos
  unfold foldChi
  rw [coneStep_eq_zero (by linarith) hz.2.le]
  ring

theorem le_foldSplit_of_le_re {z : ℂ} (hz : 0 < z.im) (hx : σ.width ≤ z.re) :
    σ.width ≤ foldSplit z := by
  have hW := σ.width_pos
  have hn : 0 < normSq z := Complex.normSq_pos.mpr (ne_zero_of_im_pos hz)
  have h1 : 1 ≤ 1 + 1 / normSq z := by
    have : 0 < 1 / normSq z := by positivity
    linarith
  unfold foldSplit
  nlinarith

theorem mem_foldFar_of_le_re {z : ℂ} (hz : 0 < z.im) (hx : σ.width ≤ z.re) : z ∈ σ.foldFar := by
  have hW := σ.width_pos
  have := σ.le_foldSplit_of_le_re hz hx
  exact ⟨hz, by linarith⟩

theorem vertexOne_mem_foldFar : σ.vertexOne ∈ σ.foldFar :=
  σ.mem_foldFar_of_le_re σ.vertexOne_im_pos le_rfl

theorem foldSplit_of_wallSide_two (hσ : σ.θ₂ = 0) {z : ℂ} (hz : 0 < z.im)
    (hw : σ.wallSide 2 z = 0) : foldSplit z = z.re + 2 := by
  have hc := σ.cusp_centre hσ
  have hn : 0 < normSq z := Complex.normSq_pos.mpr (ne_zero_of_im_pos hz)
  have hw' : normSq z = z.re / 2 := by
    simp only [wallSide, hc] at hw
    rw [Complex.normSq_apply]
    nlinarith
  have hre : 0 < z.re := by linarith
  unfold foldSplit
  rw [hw']
  field_simp

theorem mem_foldFar_of_wallSide_two (hσ : σ.θ₂ = 0) {z : ℂ} (hz : 0 < z.im)
    (hw : σ.wallSide 2 z = 0) : z ∈ σ.foldFar := by
  have h := σ.foldSplit_of_wallSide_two hσ hz hw
  have hW := σ.width_le_half
  have hn : 0 < normSq z := Complex.normSq_pos.mpr (ne_zero_of_im_pos hz)
  have hc := σ.cusp_centre hσ
  have hre : 0 < z.re := by
    simp only [wallSide, hc] at hw
    rw [Complex.normSq_apply] at hn
    nlinarith
  exact ⟨hz, by linarith⟩

theorem re_lt_width_of_foldSplit_lt {z : ℂ} (hz : 0 < z.im) (h : foldSplit z < σ.width) :
    z.re < σ.width := by
  by_contra hx
  exact absurd (σ.le_foldSplit_of_le_re hz (not_lt.mp hx)) (not_le.mpr h)

theorem coneDisc_mem_slitPlane {z : ℂ} (hx : z.re ≠ σ.width) :
    coneDisc σ.vertexOne z ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  right
  intro him
  have h := σ.im_coneDisc_vertexOne_mul z
  rw [him, zero_mul] at h
  have hy := σ.vertexOne_im_pos
  have hw : σ.wallSide 1 z = 0 := by
    have : 2 * σ.vertexOne.im ≠ 0 := by positivity
    exact (mul_eq_zero.mp h.symm).resolve_left this
  exact hx (by simp only [wallSide] at hw; linarith)

theorem foldPhase_eq_unitOf (q : ℤ) {z : ℂ} (hz : 0 < z.im) (hv : z ≠ σ.vertexOne)
    (hfar : z ∈ σ.foldFar) :
    σ.foldPhase q z = unitOf (coneDisc σ.vertexOne z) ^ q := by
  have hω : coneDisc σ.vertexOne z ≠ 0 := by
    intro h
    apply hv
    have hne := sub_conj_ne_zero σ.vertexOne_im_pos hz
    rw [coneDisc, div_eq_zero_iff] at h
    rcases h with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hne
  rw [foldPhase, σ.foldChi_eq_zero hfar, sub_zero, one_mul, circleExp_int_mul_arg hω]

theorem foldPhase_eq_one (q : ℤ) {z : ℂ} (hnear : z ∈ σ.foldNear) : σ.foldPhase q z = 1 := by
  rw [foldPhase, σ.foldChi_eq_one hnear]
  simp

theorem contMDiffAt_foldChi {z : ℂ} (hz : 0 < z.im) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ σ.foldChi z := by
  have h : ContDiffAt ℝ ∞ σ.foldChi z :=
    contDiffAt_const.sub ((contDiff_coneStep _ _).contDiffAt.comp z
      (contDiffAt_foldSplit (ne_zero_of_im_pos hz)))
  exact h.contMDiffAt

theorem contMDiffAt_arg_coneDisc {z : ℂ} (hz : 0 < z.im) (hx : z.re ≠ σ.width) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ (fun w => arg (coneDisc σ.vertexOne w)) z := by
  have hslit := σ.coneDisc_mem_slitPlane hx
  have hlog : ContDiffAt ℝ ∞ (fun w => Complex.log (coneDisc σ.vertexOne w)) z :=
    ((Complex.contDiffAt_log hslit).comp z
      (contDiffAt_coneDisc σ.vertexOne_im_pos hz)).restrict_scalars ℝ
  have him : ContDiffAt ℝ ∞ (fun w => (Complex.log (coneDisc σ.vertexOne w)).im) z :=
    Complex.imCLM.contDiff.contDiffAt.comp z hlog
  have heq : (fun w => (Complex.log (coneDisc σ.vertexOne w)).im) =
      fun w => arg (coneDisc σ.vertexOne w) := funext fun w => Complex.log_im _
  rw [heq] at him
  exact him.contMDiffAt

theorem contMDiffAt_unitOf_coneDisc_zpow (q : ℤ) {z : ℂ} (hz : 0 < z.im)
    (hv : z ≠ σ.vertexOne) :
    ContMDiffAt 𝓘(ℝ, ℂ) (𝓡 1) ∞ (fun w => unitOf (coneDisc σ.vertexOne w) ^ q) z := by
  have hω : coneDisc σ.vertexOne z ≠ 0 := by
    intro h
    apply hv
    have hne := sub_conj_ne_zero σ.vertexOne_im_pos hz
    rw [coneDisc, div_eq_zero_iff] at h
    rcases h with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hne
  have hd : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (coneDisc σ.vertexOne) z :=
    ((contDiffAt_coneDisc σ.vertexOne_im_pos hz).restrict_scalars ℝ).contMDiffAt
  have hu : ContMDiffAt 𝓘(ℝ, ℂ) (𝓡 1) ∞ (fun w => unitOf (coneDisc σ.vertexOne w)) z :=
    (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hω)).comp z hd
  exact (contMDiff_circle_zpow q).contMDiffAt.comp z hu

theorem contMDiffAt_foldPhase (q : ℤ) {z : ℂ} (hz : 0 < z.im) (hv : z ≠ σ.vertexOne) :
    ContMDiffAt 𝓘(ℝ, ℂ) (𝓡 1) ∞ (σ.foldPhase q) z := by
  have hW := σ.width_pos
  by_cases hfar : 2 * σ.width / 3 < foldSplit z
  · have hmem : σ.foldFar ∈ 𝓝 z := σ.isOpen_foldFar.mem_nhds ⟨hz, hfar⟩
    apply (σ.contMDiffAt_unitOf_coneDisc_zpow q hz hv).congr_of_eventuallyEq
    filter_upwards [hmem, (isOpen_ne : IsOpen {w : ℂ | w ≠ σ.vertexOne}).mem_nhds hv] with w hw hwv
    exact σ.foldPhase_eq_unitOf q hw.1 hwv hw
  · have hlt : foldSplit z < σ.width := by linarith [not_lt.mp hfar]
    have hx : z.re ≠ σ.width := (σ.re_lt_width_of_foldSplit_lt hz hlt).ne
    have harg := σ.contMDiffAt_arg_coneDisc hz hx
    have hchi := σ.contMDiffAt_foldChi hz
    have h : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞
        (fun w => (q : ℝ) * ((1 - σ.foldChi w) * arg (coneDisc σ.vertexOne w))) z :=
      contMDiffAt_const.mul ((contMDiffAt_const.sub hchi).mul harg)
    exact _root_.contMDiff_circleExp.contMDiffAt.comp z h

theorem foldPhase_refl_zero (q : ℤ) {z : ℂ} (hnear : z ∈ σ.foldNear)
    (hnear' : σ.refl 0 z ∈ σ.foldNear) :
    σ.foldPhase q (σ.refl 0 z) = (σ.foldPhase q z)⁻¹ := by
  rw [σ.foldPhase_eq_one q hnear, σ.foldPhase_eq_one q hnear', inv_one]

theorem foldPhase_refl_one (q : ℤ) {z : ℂ} (hz : 0 < z.im) (hv : z ≠ σ.vertexOne)
    (hfar : z ∈ σ.foldFar) (hfar' : σ.refl 1 z ∈ σ.foldFar) :
    σ.foldPhase q (σ.refl 1 z) = (σ.foldPhase q z)⁻¹ := by
  have hz' : 0 < (σ.refl 1 z).im := σ.refl_im_pos hz 1
  have hv' : σ.refl 1 z ≠ σ.vertexOne := by
    intro h
    apply hv
    have := congrArg (σ.refl 1) h
    rw [σ.refl_refl hz 1] at this
    rw [this]
    have hw : σ.wallSide 1 σ.vertexOne = 0 := by simp [wallSide, vertexOne_re]
    exact σ.refl_of_wallSide_eq_zero σ.vertexOne_im_pos hw
  have hω : coneDisc σ.vertexOne z ≠ 0 := by
    intro h
    apply hv
    have hne := sub_conj_ne_zero σ.vertexOne_im_pos hz
    rw [coneDisc, div_eq_zero_iff] at h
    rcases h with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hne
  rw [σ.foldPhase_eq_unitOf q hz' hv' hfar', σ.foldPhase_eq_unitOf q hz hv hfar,
    σ.coneDisc_vertexOne_refl_one, unitOf_conj hω, inv_zpow]

theorem foldPhase_refl_two (q : ℤ) {z : ℂ} (hz : 0 < z.im) (hv : z ≠ σ.vertexOne)
    (hfar : z ∈ σ.foldFar) (hfar' : σ.refl 2 z ∈ σ.foldFar) :
    σ.foldPhase q (σ.refl 2 z) = Circle.exp (q * (2 * σ.θ₁)) * (σ.foldPhase q z)⁻¹ := by
  have hz' : 0 < (σ.refl 2 z).im := σ.refl_im_pos hz 2
  have hv' : σ.refl 2 z ≠ σ.vertexOne := by
    intro h
    apply hv
    have := congrArg (σ.refl 2) h
    rw [σ.refl_refl hz 2] at this
    rw [this]
    have hw : σ.wallSide 2 σ.vertexOne = 0 := by
      have h1 := σ.vertexOne_eq
      simp only [wallSide]
      have hre : σ.vertexOne.re = σ.centre + Real.cos σ.θ₁ / 4 := by
        rw [h1]
        simp [exp_mul_I_eq]
      have him : σ.vertexOne.im = Real.sin σ.θ₁ / 4 := rfl
      rw [hre, him]
      nlinarith [Real.sin_sq_add_cos_sq σ.θ₁]
    exact σ.refl_of_wallSide_eq_zero σ.vertexOne_im_pos hw
  have hω : coneDisc σ.vertexOne z ≠ 0 := by
    intro h
    apply hv
    have hne := sub_conj_ne_zero σ.vertexOne_im_pos hz
    rw [coneDisc, div_eq_zero_iff] at h
    rcases h with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hne
  have hc : z ≠ σ.centre := sub_ne_zero.1 (σ.centre_ne hz)
  rw [σ.foldPhase_eq_unitOf q hz' hv' hfar', σ.foldPhase_eq_unitOf q hz hv hfar,
    σ.coneDisc_vertexOne_refl_two hc]
  have he : exp (2 * (σ.θ₁ : ℂ) * I) = ((Circle.exp (2 * σ.θ₁) : Circle) : ℂ) := by
    rw [Circle.coe_exp]
    push_cast
    ring_nf
  rw [he, unitOf_circle_mul' _ ((map_ne_zero _).mpr hω), unitOf_conj hω, mul_zpow, inv_zpow,
    ← Circle.exp_zsmul, zsmul_eq_mul]

end ConeShape

end GC.Seifert
