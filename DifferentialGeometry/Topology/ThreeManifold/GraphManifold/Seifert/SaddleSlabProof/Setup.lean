import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabProof.Strip
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabProof.Components
import DifferentialGeometry.Topology.Morse.ModelTransport
import DifferentialGeometry.Topology.Morse.HessianNaturality
import DifferentialGeometry.Topology.Manifold.ModelChangeRoundtrip

/-!
# Gradient-like strips of a one-saddle slab with a prescribed small radius

Lane RG03c. A surface `N` modelled on `E` with `finrank E = 2` is also a manifold for the model
`modelJ I hdim = I.transContinuousLinearEquiv L` on `MorseModel 2`, and smoothness, critical
points, nondegeneracy and the index transfer (`MO/ModelTransport`). For the data of
`OneSaddleSlabUniqueness`, `exists_saddleChart` gives an index-one Morse normal chart at `p`
inside the open slab, and `exists_strip_of_radius` turns it, for every small enough radius `r`,
into a gradient-like strip `D` with `(ch D).r₀ = r`, model radius at least `8 r` and the box
levels `f p ± 2 r²` inside `(a, b)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm)

universe uN

namespace GC.Seifert.SaddleSlabProof

variable {E H : Type} {N : Type uN} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N]
  [T2Space N] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ N]

abbrev modelL (hdim : Module.finrank ℝ E = 2) : E ≃L[ℝ] MorseModel 2 :=
  ContinuousLinearEquiv.ofFinrankEq (by simp [MorseModel, hdim])

abbrev modelJ (I : ModelWithCorners ℝ E H) (hdim : Module.finrank ℝ E = 2) :
    ModelWithCorners ℝ (MorseModel 2) H :=
  I.transContinuousLinearEquiv (modelL hdim)

omit [T2Space N] in
theorem chartHessianAt_modelJ (hdim : Module.finrank ℝ E = 2) {f : N → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : N} (hc : IsCriticalPointAt I f x) :
    chartHessianAt (fun y => f ((extChartAt (modelJ I hdim) x).symm y))
      (extChartAt (modelJ I hdim) x x) =
      (chartHessianAt (fun y => f ((extChartAt I x).symm y)) (extChartAt I x x)).comp
        (modelL hdim).symm.toLinearEquiv.toLinearMap := by
  set e := modelL hdim
  let g : E → ℝ := fun y => f ((extChartAt I x).symm y)
  let z := extChartAt I x x
  have hx : I.IsInteriorPoint x := BoundarylessManifold.isInteriorPoint
  have hg : ContDiffAt ℝ 2 g (e.symm (e z)) := by
    simpa only [e.symm_apply_apply] using
      (DifferentialGeometry.Manifold.contDiffAt_comp_extChartAt_symm_of_isInteriorPoint I hf
        hx).of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hz : fderiv ℝ g (e.symm (e z)) = 0 := by
    rw [e.symm_apply_apply]
    have hd := DifferentialGeometry.Manifold.mfderiv_eq_fderiv_extChartAt_of_isInteriorPoint
      I (hf.mdifferentiableAt (by simp)) hx
    exact hd.symm.trans hc
  have hd := DifferentialGeometry.Morse.fderiv_fderiv_comp_at_critical hg
    e.symm.contDiff.contDiffAt hz
  ext v
  change (fderiv ℝ (fderiv ℝ (g ∘ e.symm)) (e z)) v v =
    (fderiv ℝ (fderiv ℝ g) z) (e.symm v) (e.symm v)
  rw [hd, e.symm.fderiv, e.symm_apply_apply]
  rfl

omit [T2Space N] in
theorem sigNeg_modelJ (hdim : Module.finrank ℝ E = 2) {f : N → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : N} (hc : IsCriticalPointAt I f x) :
    sigNeg (chartHessianAt (fun y => f ((extChartAt (modelJ I hdim) x).symm y))
      (extChartAt (modelJ I hdim) x x)) =
      sigNeg (chartHessianAt (fun y => f ((extChartAt I x).symm y)) (extChartAt I x x)) := by
  rw [chartHessianAt_modelJ hdim hf hc]
  exact QuadraticMap.Equivalent.sigNeg_eq
    ⟨(QuadraticMap.isometryEquivOfCompLinearEquiv _ (modelL hdim).symm.toLinearEquiv).symm⟩

omit [T2Space N] in
theorem isNondegenerate_modelJ (hdim : Module.finrank ℝ E = 2) {f : N → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : N} (hnd : IsNondegenerateCriticalPointAt I f x) :
    IsNondegenerateCriticalPointAt (modelJ I hdim) f x := by
  refine ⟨(isCriticalPointAt_transContinuousLinearEquiv_iff I (modelL hdim) f x).mpr hnd.1, ?_⟩
  rw [chartHessianAt_modelJ hdim hf hnd.1, QuadraticMap.associated_comp]
  have h := hnd.2
  convert! (LinearMap.separatingLeft_congr_iff
    (B := QuadraticMap.associated (R := ℝ)
      (chartHessianAt (fun y => f ((extChartAt I x).symm y)) (extChartAt I x x)))
    (modelL hdim).toLinearEquiv (modelL hdim).toLinearEquiv).mpr h using 1

omit [T2Space N] in
theorem morseStrip_of_data (hdim : Module.finrank ℝ E = 2) {f : N → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (hreg : ∀ x, f x = a ∨ f x = b → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) {p : N}
    (hnd : IsNondegenerateCriticalPointAt I f p)
    (huniq : ∀ x, f x ∈ Icc a b → IsCriticalPointAt I f x → x = p)
    (hcpt : IsCompact (f ⁻¹' Icc a b)) : MorseStrip (modelJ I hdim) f a b where
  smooth := (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left _).mpr hf
  lt := hab
  compact := hcpt
  regular := fun x hx hc => hreg x hx
    ((isCriticalPointAt_transContinuousLinearEquiv_iff I (modelL hdim) f x).mp hc)
  nondegenerate := fun x hx hc => by
    have hxp := huniq x (Ioo_subset_Icc_self hx)
      ((isCriticalPointAt_transContinuousLinearEquiv_iff I (modelL hdim) f x).mp hc)
    subst hxp
    exact isNondegenerate_modelJ hdim hf hnd

omit [T2Space N] in
theorem exists_saddleChart (hdim : Module.finrank ℝ E = 2) {f : N → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (hreg : ∀ x, f x = a ∨ f x = b → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) {p : N}
    (hp : f p ∈ Ioo a b) (hnd : IsNondegenerateCriticalPointAt I f p)
    (hidx : sigNeg (chartHessianAt (fun y => f ((extChartAt I p).symm y))
      (extChartAt I p p)) = 1)
    (huniq : ∀ x, f x ∈ Icc a b → IsCriticalPointAt I f x → x = p)
    (hcpt : IsCompact (f ⁻¹' Icc a b)) :
    ∃ c : MorseNormalChart (modelJ I hdim) f p, c.k = 1 ∧
      c.χ '' Metric.ball 0 c.R' ⊆ f ⁻¹' Ioo a b := by
  have hS := morseStrip_of_data hdim hf hab hreg hnd huniq hcpt
  have hc : IsCriticalPointAt (modelJ I hdim) f p :=
    (isCriticalPointAt_transContinuousLinearEquiv_iff I (modelL hdim) f p).mpr hnd.1
  obtain ⟨c, -, -, hO⟩ := exists_morseNormalChart hS hp hc
    (isOpen_Ioo.preimage hf.continuous) hp one_pos
  refine ⟨c, ?_, hO⟩
  rw [← c.hkidx]
  unfold morseIndex hessianAt
  rw [sigNeg_modelJ hdim hf hnd.1]
  exact hidx

def chartWithRadius {n : ℕ} {H' : Type*} [TopologicalSpace H'] {M : Type*}
    [TopologicalSpace M] [ChartedSpace H' M] {J : ModelWithCorners ℝ (Fin n → ℝ) H'}
    {f : M → ℝ} {p : M} (c : MorseNormalChart J f p) {r : ℝ} (hr : 0 < r) (hrR : 4 * r < c.R) :
    MorseNormalChart J f p :=
  { c with r₀ := r, hr₀ := hr, hr₀R := hrR }

theorem exists_strip_of_radius (hdim : Module.finrank ℝ E = 2) {f : N → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (hreg : ∀ x, f x = a ∨ f x = b → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) {p : N}
    (hp : f p ∈ Ioo a b) (hnd : IsNondegenerateCriticalPointAt I f p)
    (huniq : ∀ x, f x ∈ Icc a b → IsCriticalPointAt I f x → x = p)
    (hcpt : IsCompact (f ⁻¹' Icc a b)) (c : MorseNormalChart (modelJ I hdim) f p)
    (hck : c.k = 1) (hcO : c.χ '' Metric.ball 0 c.R' ⊆ f ⁻¹' Ioo a b) {r : ℝ} (hr : 0 < r)
    (hrR : 16 * r < c.R) (hra : a < f p - 2 * r ^ 2) (hrb : f p + 2 * r ^ 2 < b) :
    ∃ D : GradientLikeStrip (modelJ I hdim) f a b {p}, (ch D).k = 1 ∧ (ch D).r₀ = r ∧
      8 * (ch D).r₀ ≤ rmD D ∧ a < f p - 2 * eps D ∧ f p + 2 * eps D < b := by
  have hS := morseStrip_of_data hdim hf hab hreg hnd huniq hcpt
  set c' := chartWithRadius c hr (by linarith) with hc'
  have hcrit : ∀ x, x ∈ ({p} : Finset N) ↔
      f x ∈ Ioo a b ∧ IsCriticalPointAt (modelJ I hdim) f x := by
    intro x
    rw [Finset.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨hp, (isCriticalPointAt_transContinuousLinearEquiv_iff I (modelL hdim) f x).mpr
        hnd.1⟩
    · rintro ⟨hx, hc⟩
      exact huniq x (Ioo_subset_Icc_self hx)
        ((isCriticalPointAt_transContinuousLinearEquiv_iff I (modelL hdim) f x).mp hc)
  let chart : ∀ q ∈ ({p} : Finset N), MorseNormalChart (modelJ I hdim) f q :=
    fun q hq => (Finset.mem_singleton.mp hq) ▸ c'
  have hchart : ∀ hq, chart p hq = c' := fun hq => rfl
  have hr₀ : ∀ q hq, 8 * (chart q hq).r₀ < (chart q hq).R := by
    intro q hq
    obtain rfl := Finset.mem_singleton.mp hq
    rw [hchart hq]
    change 8 * r < c.R
    linarith
  obtain ⟨D, hDc, hDrm⟩ := exists_gradientLikeStrip_of_charts hS {p} hcrit chart hr₀
    (fun q hq q' hq' hne => by
      obtain rfl := Finset.mem_singleton.mp hq
      obtain rfl := Finset.mem_singleton.mp hq'
      exact absurd rfl hne)
    (fun q hq => by
      obtain rfl := Finset.mem_singleton.mp hq
      rw [hchart hq]
      exact hcO)
  have hch : ch D = c'.halve (hr₀ p (Finset.mem_singleton_self p)) :=
    hDc p (Finset.mem_singleton_self p)
  have hrm : rmD D = c.R / 2 := hDrm p (Finset.mem_singleton_self p)
  have hr₀D : (ch D).r₀ = r := by rw [hch]; rfl
  have heps : eps D = r ^ 2 := by unfold eps; rw [hr₀D]
  refine ⟨D, by rw [hch]; exact hck, hr₀D, by rw [hr₀D, hrm]; linarith, by rw [heps]; exact hra,
    by rw [heps]; exact hrb⟩

end GC.Seifert.SaddleSlabProof
