import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusMappingClass
import DifferentialGeometry.Topology.Manifold.ChartSupportedIsotopy

/-!
# The chart of the complement of the axes of the torus

Chapter 6, packet K08, lane MC3 of the `TorusMappingClassLinear` programme
(`docs/geometrization/handoffs/20261004-survey-torus-mapping-class.md`, corrected by review 12).

The stereographic coordinate `circleStereo z = Im z / (1 - Re z)` of `Circle \ {1}` is the
tangent of the half angle shifted by `π / 2`, so it is "an angle coordinate followed by a tangent
transformation"; its inverse is `circleStereoInv y = exp ((π - 2 arctan y) i)`, with
`circleStereoInv y = ((y² - 1) + 2 y i) / (y² + 1)` (`coe_circleStereoInv`). Both are smooth for
the model `𝓡 1` of `Circle` and the model `𝓘(ℝ, ℝ)` of `ℝ` (proved through the inclusion
`Circle → ℂ` and `Circle.exp`, not by identifying models).

`axesComplementChart (z, w) = circleStereo z + circleStereo w · i` is an
`OpenPartialHomeomorph Torus ℂ` with source `T² \ (α ∪ β)` and target all of `ℂ`, smooth in both
directions between `torusModel` and `𝓘(ℝ, ℂ)` (`exists_axesComplement_chart`).

Translates: `exists_axesComplement_chart_translate a b` is the same chart for
`T² \ ({w = b} ∪ {z = a})`, through `torusTranslate a b (z, w) = (a⁻¹ z, b⁻¹ w)`.

MC5's disc leaf: a torus diffeomorphism equal to the identity on an open neighbourhood `V` of
`α ∪ β` is isotopic to the identity (`isotopic_refl_of_eqOn_nhds_axes`): `T² \ V` is a compact
subset of the source of the chart, and `exists_isotopy_of_support_in_planar_chart` applies. No
matrix or orientation hypothesis is needed.
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.Seifert

def circleStereo (z : Circle) : ℝ := (z : ℂ).im / (1 - (z : ℂ).re)

def circleStereoInv (y : ℝ) : Circle := Circle.exp (Real.pi - 2 * Real.arctan y)

theorem coe_circleStereoInv (y : ℝ) :
    (circleStereoInv y : ℂ) = ⟨(y ^ 2 - 1) / (y ^ 2 + 1), 2 * y / (y ^ 2 + 1)⟩ := by
  have hc : Real.cos (Real.arctan y) ^ 2 = 1 / (1 + y ^ 2) := Real.cos_sq_arctan y
  have hpos : 0 < Real.cos (Real.arctan y) := Real.cos_arctan_pos y
  have hs : Real.sin (Real.arctan y) = y * Real.cos (Real.arctan y) := by
    have := Real.tan_arctan y
    rw [Real.tan_eq_sin_div_cos] at this
    field_simp at this
    linarith
  have h1 : (1 : ℝ) + y ^ 2 ≠ 0 := by positivity
  have h2 : y ^ 2 + 1 ≠ 0 := by positivity
  apply Complex.ext
  · simp only [circleStereoInv, Circle.coe_exp, Complex.exp_ofReal_mul_I_re]
    rw [Real.cos_pi_sub, Real.cos_two_mul, hc]
    field_simp
    ring
  · simp only [circleStereoInv, Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
    rw [Real.sin_pi_sub, Real.sin_two_mul, hs]
    have : 2 * (y * Real.cos (Real.arctan y)) * Real.cos (Real.arctan y) =
        2 * y * Real.cos (Real.arctan y) ^ 2 := by ring
    rw [this, hc]
    field_simp
    ring

private theorem circle_re_sq_add_im_sq (z : Circle) : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
  have h := Circle.normSq_coe z
  rw [Complex.normSq_apply] at h
  nlinarith [h]

theorem circleStereo_circleStereoInv (y : ℝ) : circleStereo (circleStereoInv y) = y := by
  unfold circleStereo
  rw [coe_circleStereoInv]
  have h2 : y ^ 2 + 1 ≠ 0 := by positivity
  simp only
  field_simp
  ring

private theorem circle_re_lt_one {z : Circle} (hz : z ≠ 1) : (z : ℂ).re < 1 := by
  have h := circle_re_sq_add_im_sq z
  have hle : (z : ℂ).re ≤ 1 := by nlinarith [sq_nonneg (z : ℂ).im, sq_nonneg ((z : ℂ).re - 1)]
  refine lt_of_le_of_ne hle fun heq => hz ?_
  apply Circle.ext
  have him : (z : ℂ).im = 0 := by nlinarith [sq_nonneg (z : ℂ).im]
  apply Complex.ext <;> simp [heq, him]

theorem circleStereoInv_circleStereo {z : Circle} (hz : z ≠ 1) :
    circleStereoInv (circleStereo z) = z := by
  apply Circle.ext
  rw [coe_circleStereoInv]
  have h := circle_re_sq_add_im_sq z
  have hlt := circle_re_lt_one hz
  have hne : 1 - (z : ℂ).re ≠ 0 := by linarith
  have hden : ((z : ℂ).im / (1 - (z : ℂ).re)) ^ 2 + 1 = 2 / (1 - (z : ℂ).re) := by
    field_simp
    nlinarith [h]
  unfold circleStereo
  apply Complex.ext
  · simp only
    rw [hden]
    field_simp
    nlinarith [h]
  · simp only
    rw [hden]
    field_simp

theorem circleStereoInv_ne_one (y : ℝ) : circleStereoInv y ≠ 1 := by
  intro h
  have h2 : y ^ 2 + 1 ≠ 0 := by positivity
  have hre := congrArg (fun z : Circle => (z : ℂ).re) h
  simp only [coe_circleStereoInv, Circle.coe_one, Complex.one_re] at hre
  field_simp at hre
  linarith

theorem contMDiff_circleStereoInv : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ circleStereoInv :=
  contMDiff_circleExp.comp
    ((contDiff_const.sub (contDiff_const.mul Real.contDiff_arctan)).contMDiff)

theorem contMDiffOn_circleStereo :
    ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ circleStereo {z | z ≠ 1} := by
  have : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨Complex.finrank_real_complex⟩
  have hcoe : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun v : Circle => (v : ℂ)) := contMDiff_coe_sphere
  have hf : ContDiffOn ℝ ∞ (fun w : ℂ => w.im / (1 - w.re)) {w | w.re ≠ 1} := by
    apply ContDiffOn.div
    · exact Complex.imCLM.contDiff.contDiffOn
    · exact (contDiff_const.sub Complex.reCLM.contDiff).contDiffOn
    · intro w hw
      exact sub_ne_zero.mpr (Ne.symm hw)
  exact hf.contMDiffOn.comp hcoe.contMDiffOn fun z hz => (circle_re_lt_one hz).ne

def axesComplementSource : Set Torus := {p | p.1 ≠ 1 ∧ p.2 ≠ 1}

def axesComplementChart : OpenPartialHomeomorph Torus ℂ where
  toFun p := (circleStereo p.1 : ℂ) + (circleStereo p.2 : ℂ) * Complex.I
  invFun q := (circleStereoInv q.re, circleStereoInv q.im)
  source := axesComplementSource
  target := univ
  map_source' _ _ := mem_univ _
  map_target' q _ := ⟨circleStereoInv_ne_one _, circleStereoInv_ne_one _⟩
  left_inv' p hp := by
    obtain ⟨h1, h2⟩ := hp
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, Complex.add_im,
      Complex.mul_im, mul_one, zero_add]
    rw [circleStereoInv_circleStereo h1, circleStereoInv_circleStereo h2]
  right_inv' q _ := by
    apply Complex.ext <;>
      simp [circleStereo_circleStereoInv]
  open_source := (isOpen_ne.preimage continuous_fst).inter (isOpen_ne.preimage continuous_snd)
  open_target := isOpen_univ
  continuousOn_toFun := by
    have h1 : ContinuousOn (fun p : Torus => circleStereo p.1) axesComplementSource :=
      contMDiffOn_circleStereo.continuousOn.comp continuous_fst.continuousOn fun p hp => hp.1
    have h2 : ContinuousOn (fun p : Torus => circleStereo p.2) axesComplementSource :=
      contMDiffOn_circleStereo.continuousOn.comp continuous_snd.continuousOn fun p hp => hp.2
    exact (Complex.continuous_ofReal.comp_continuousOn h1).add
      ((Complex.continuous_ofReal.comp_continuousOn h2).mul continuousOn_const)
  continuousOn_invFun :=
    (contMDiff_circleStereoInv.continuous.comp Complex.continuous_re).continuousOn.prodMk
      (contMDiff_circleStereoInv.continuous.comp Complex.continuous_im).continuousOn

theorem axesComplementChart_source :
    axesComplementChart.source = (range alphaCircle ∪ range betaCircle)ᶜ := by
  ext ⟨z, w⟩
  simp only [axesComplementChart, axesComplementSource, mem_ofPred_eq, mem_compl_iff, mem_union,
    mem_range, alphaCircle, betaCircle, Prod.mk.injEq, not_or, not_exists, not_and]
  constructor
  · rintro ⟨hz, hw⟩
    exact ⟨fun _ _ h => hw h.symm, fun _ h _ => hz h.symm⟩
  · rintro ⟨hα, hβ⟩
    exact ⟨fun h => hβ w h.symm rfl, fun h => hα z rfl h.symm⟩

theorem contMDiffOn_axesComplementChart :
    ContMDiffOn torusModel 𝓘(ℝ, ℂ) ∞ axesComplementChart axesComplementChart.source := by
  have h1 : ContMDiffOn torusModel 𝓘(ℝ, ℝ) ∞ (fun p : Torus => circleStereo p.1)
      axesComplementSource :=
    contMDiffOn_circleStereo.comp contMDiff_fst.contMDiffOn fun p hp => hp.1
  have h2 : ContMDiffOn torusModel 𝓘(ℝ, ℝ) ∞ (fun p : Torus => circleStereo p.2)
      axesComplementSource :=
    contMDiffOn_circleStereo.comp contMDiff_snd.contMDiffOn fun p hp => hp.2
  have hlin : ContDiff ℝ ∞ (fun a : ℝ × ℝ => (a.1 : ℂ) + (a.2 : ℂ) * Complex.I) :=
    (Complex.ofRealCLM.contDiff.comp contDiff_fst).add
      ((Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const)
  exact hlin.contMDiff.comp_contMDiffOn (h1.prodMk_space h2)

theorem contMDiffOn_axesComplementChart_symm :
    ContMDiffOn 𝓘(ℝ, ℂ) torusModel ∞ axesComplementChart.symm axesComplementChart.target :=
  ((contMDiff_circleStereoInv.comp Complex.reCLM.contDiff.contMDiff).prodMk
    (contMDiff_circleStereoInv.comp Complex.imCLM.contDiff.contMDiff)).contMDiffOn

theorem exists_axesComplement_chart :
    ∃ e : OpenPartialHomeomorph Torus ℂ,
      e.source = (range alphaCircle ∪ range betaCircle)ᶜ ∧ e.target = univ ∧
      ContMDiffOn torusModel 𝓘(ℝ, ℂ) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℝ, ℂ) torusModel ∞ e.symm e.target :=
  ⟨axesComplementChart, axesComplementChart_source, rfl, contMDiffOn_axesComplementChart,
    contMDiffOn_axesComplementChart_symm⟩

theorem isotopic_refl_of_eqOn_nhds_axes (φ : TDiff) {V : Set Torus} (hV : IsOpen V)
    (hαβ : range alphaCircle ∪ range betaCircle ⊆ V) (hφV : ∀ p ∈ V, φ p = p) :
    IsotopicDiffeomorph φ torusRefl := by
  obtain ⟨e, hsource, htarget, he, hei⟩ := exists_axesComplement_chart
  have hK : IsCompact Vᶜ := hV.isClosed_compl.isCompact
  have hKs : Vᶜ ⊆ e.source := by
    rw [hsource]
    exact compl_subset_compl.mpr hαβ
  obtain ⟨J, hJ, hJi, hJ0, hJ1, -⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_isotopy_of_support_in_planar_chart
      e htarget he hei φ hK hKs fun x hx => hφV x (not_not.mp hx)
  exact ⟨J, hJ, hJi, hJ0, hJ1⟩

def torusTranslate (a b : Circle) : Torus ≃ₜ Torus :=
  (Homeomorph.mulLeft a⁻¹).prodCongr (Homeomorph.mulLeft b⁻¹)

theorem torusTranslate_apply (a b : Circle) (p : Torus) :
    torusTranslate a b p = (a⁻¹ * p.1, b⁻¹ * p.2) := rfl

theorem exists_axesComplement_chart_translate (a b : Circle) :
    ∃ e : OpenPartialHomeomorph Torus ℂ,
      e.source = {p : Torus | p.1 ≠ a ∧ p.2 ≠ b} ∧ e.target = univ ∧
      ContMDiffOn torusModel 𝓘(ℝ, ℂ) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℝ, ℂ) torusModel ∞ e.symm e.target := by
  set T := torusTranslate a b
  have hT : ContMDiff torusModel torusModel ∞ T :=
    (contMDiff_mul_left.comp contMDiff_fst).prodMk (contMDiff_mul_left.comp contMDiff_snd)
  have hTs : ContMDiff torusModel torusModel ∞ T.symm := by
    have : (T.symm : Torus → Torus) = fun p => (a * p.1, b * p.2) := by
      funext p
      apply T.injective
      rw [T.apply_symm_apply, torusTranslate_apply]
      simp
    rw [this]
    exact (contMDiff_mul_left.comp contMDiff_fst).prodMk (contMDiff_mul_left.comp contMDiff_snd)
  refine ⟨T.toOpenPartialHomeomorph.trans axesComplementChart, ?_, ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.trans_source]
    ext p
    simp only [Homeomorph.toOpenPartialHomeomorph_source, Homeomorph.toOpenPartialHomeomorph_apply,
      univ_inter, mem_preimage, axesComplementChart, axesComplementSource, mem_ofPred_eq, T,
      torusTranslate_apply, ne_eq, inv_mul_eq_one]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨fun h => h1 h.symm, fun h => h2 h.symm⟩
  · rw [OpenPartialHomeomorph.trans_target]
    simp [axesComplementChart]
  · intro p hp
    have hp' : T p ∈ axesComplementChart.source := by
      rw [OpenPartialHomeomorph.trans_source] at hp
      exact hp.2
    exact ((contMDiffOn_axesComplementChart (T p) hp').comp p hT.contMDiffAt.contMDiffWithinAt
      (fun q hq => by rw [OpenPartialHomeomorph.trans_source] at hq; exact hq.2))
  · intro q _
    exact (hTs.contMDiffAt.comp q
      ((contMDiffOn_axesComplementChart_symm q (mem_univ q)).contMDiffAt
        (isOpen_univ.mem_nhds (mem_univ q)))).contMDiffWithinAt

end GC.Seifert
