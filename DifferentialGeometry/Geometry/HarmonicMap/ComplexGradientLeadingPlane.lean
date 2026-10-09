import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import DifferentialGeometry.Analysis.Calculus.Inverse.SmoothLocalInverse
import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientConformality
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

set_option autoImplicit false

noncomputable section

open Set Filter Manifold Bundle DifferentialGeometry
open DifferentialGeometry.Tensor.Coordinates
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Projection onto the two real leading directions using the metric in the
original target chart. Its denominator is proved positive for a nonzero
isotropic leading coefficient. -/
def chartLeadingPlaneProjection
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (p x : M)
    (b : Fin (Module.finrank ℝ E) → ℂ) : E →L[ℝ] ℂ :=
  let A := (chartModelBasis E).equivFunL.symm (fun i => (b i).re)
  let C := (chartModelBasis E).equivFunL.symm (fun i => -(b i).im)
  let Q := chartGramBilin g p x
  (2 * Q A A)⁻¹ •
    (Complex.ofRealCLM.comp (Q A) +
      Complex.I • Complex.ofRealCLM.comp (Q C))

private def leadingRealVector (b : Fin (Module.finrank ℝ E) → ℂ) : E :=
  (chartModelBasis E).equivFunL.symm (fun i => (b i).re)

private def leadingNegImVector (b : Fin (Module.finrank ℝ E) → ℂ) : E :=
  (chartModelBasis E).equivFunL.symm (fun i => -(b i).im)

private def leadingRealDifferential
    (b : Fin (Module.finrank ℝ E) → ℂ) : ℂ →L[ℝ] E :=
  Complex.reCLM.smulRight ((2 : ℝ) • leadingRealVector b) +
    Complex.imCLM.smulRight ((2 : ℝ) • leadingNegImVector b)

private theorem leadingRealDifferential_apply
    (b : Fin (Module.finrank ℝ E) → ℂ) (w : ℂ) :
    leadingRealDifferential b w =
      w.re • ((2 : ℝ) • leadingRealVector b) +
        w.im • ((2 : ℝ) • leadingNegImVector b) := rfl

private theorem continuous_leadingRealDifferential :
    Continuous (leadingRealDifferential (E := E)) := by
  have hA : Continuous (leadingRealVector (E := E)) :=
    (chartModelBasis E).equivFunL.symm.continuous.comp
      (continuous_pi (fun i => Complex.continuous_re.comp (continuous_apply i)))
  have hC : Continuous (leadingNegImVector (E := E)) :=
    (chartModelBasis E).equivFunL.symm.continuous.comp
      (continuous_pi (fun i => (Complex.continuous_im.comp (continuous_apply i)).neg))
  exact ((ContinuousLinearMap.smulRightL ℝ ℂ E Complex.reCLM).continuous.comp
    (continuous_const.smul hA)).add
      ((ContinuousLinearMap.smulRightL ℝ ℂ E Complex.imCLM).continuous.comp
        (continuous_const.smul hC))

private theorem chartModelBasis_repr_equivFunL_symm
    (f : Fin (Module.finrank ℝ E) → ℝ) (i : Fin (Module.finrank ℝ E)) :
    (chartModelBasis E).repr ((chartModelBasis E).equivFunL.symm f) i = f i :=
  congrFun ((chartModelBasis E).equivFunL.apply_symm_apply f) i

private theorem leadingRealDifferential_smul
    (b : Fin (Module.finrank ℝ E) → ℂ) (q w : ℂ) :
    leadingRealDifferential (q • b) w = leadingRealDifferential b (q * w) := by
  apply (chartModelBasis E).equivFunL.injective
  ext i
  simp [leadingRealDifferential, leadingRealVector, leadingNegImVector,
    smul_eq_mul, Complex.mul_re, Complex.mul_im,
    chartModelBasis_repr_equivFunL_symm]
  ring

private theorem chart_fderiv_eq_leadingRealDifferential
    {U : ℂ → M} {z : ℂ}
    (hU : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 U z) {p : M}
    (hsrc : U z ∈ (chartAt E p).source) :
    fderiv ℝ (extChartAt 𝓘(ℝ, E) p ∘ U) z =
      leadingRealDifferential (fun i => chartComplexGradient p U i z) := by
  let X := extChartAt 𝓘(ℝ, E) p ∘ U
  have hX : ContDiffAt ℝ 1 X z :=
    ((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := 1) hsrc).comp z hU).contDiffAt
  have hcoord (i : Fin (Module.finrank ℝ E)) (v : ℂ) :
      fderiv ℝ (fun q => chartCoordCLM E i (X q)) z v =
        chartCoordCLM E i (fderiv ℝ X z v) := by
    have h := congrArg (fun L : ℂ →L[ℝ] ℝ => L v)
      ((chartCoordCLM E i).hasFDerivAt.comp z
        (hX.differentiableAt (by norm_num)).hasFDerivAt).fderiv
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply] using h
  apply ContinuousLinearMap.ext
  intro v
  apply (chartModelBasis E).equivFunL.injective
  ext i
  have hgrad : chartComplexGradient p U i z =
      (⟨chartCoordCLM E i (fderiv ℝ X z 1) / 2,
        -chartCoordCLM E i (fderiv ℝ X z Complex.I) / 2⟩ : ℂ) := by
    change (⟨fderiv ℝ (fun q => chartCoordCLM E i (X q)) z 1 / 2,
      -fderiv ℝ (fun q => chartCoordCLM E i (X q)) z Complex.I / 2⟩ : ℂ) = _
    rw [hcoord, hcoord]
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    apply Complex.ext <;> simp
  have hd : chartCoordCLM E i (fderiv ℝ X z v) =
      v.re * chartCoordCLM E i (fderiv ℝ X z 1) +
        v.im * chartCoordCLM E i (fderiv ℝ X z Complex.I) := by
    conv_lhs => rw [hv]
    simp only [map_add, map_smul, smul_eq_mul]
  change chartCoordCLM E i (fderiv ℝ X z v) = _
  rw [hd]
  simp [leadingRealDifferential, leadingRealVector, leadingNegImVector, hgrad,
    smul_eq_mul, chartCoordCLM_apply, chartModelBasis_repr_equivFunL_symm]
  ring

/-- The coefficient of the same chart gradient is isotropic in the metric at
the original base value. The scalar zero is canceled off the base point,
then continuity supplies the value at the base point. -/
theorem chartComplexGradient_leading_isotropic
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 U s)
    (hconformal : ∀ z ∈ s, DiskMapConformalAt g U z)
    {a : ℂ} (ha : a ∈ s) {p : M}
    (hsrc : U a ∈ (chartAt E p).source)
    {m : ℕ} {B : ℂ → (Fin (Module.finrank ℝ E) → ℂ)}
    (hB : ContinuousAt B a)
    (hfactor : ∀ᶠ z in 𝓝 a,
      (fun i => chartComplexGradient p U i z) = (z - a) ^ m • B z) :
    (∑ i, ∑ j, (chartGramMatrix g p (U a) i j : ℂ) * B a i * B a j) = 0 := by
  classical
  let Q : ℂ → ℂ := fun z =>
    ∑ i, ∑ j, (chartGramMatrix g p (U z) i j : ℂ) * B z i * B z j
  have hUa := (hU.contMDiffAt (hs.mem_nhds ha)).continuousAt
  have hb : U a ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hsrc
  have hG (i j : Fin (Module.finrank ℝ E)) :
      ContinuousAt (fun z => (chartGramMatrix g p (U z) i j : ℂ)) a :=
    Complex.continuous_ofReal.continuousAt.comp
      (((chartGramMatrix_entry_contMDiffOn g p i j).contMDiffAt
        ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).open_baseSet.mem_nhds hb)).continuousAt.comp hUa)
  have hBi (i : Fin (Module.finrank ℝ E)) : ContinuousAt (fun z => B z i) a :=
    (continuous_apply i).continuousAt.comp hB
  have hQ : ContinuousAt Q a := by
    dsimp only [Q]
    fun_prop
  have hchart : ∀ᶠ z in 𝓝 a, U z ∈ (chartAt E p).source :=
    hUa.preimage_mem_nhds ((chartAt E p).open_source.mem_nhds hsrc)
  have hz : ∀ᶠ z in 𝓝[≠] a, Q z = 0 := by
    filter_upwards [hfactor.filter_mono nhdsWithin_le_nhds,
      hchart.filter_mono nhdsWithin_le_nhds,
      nhdsWithin_le_nhds (hs.mem_nhds ha),
      self_mem_nhdsWithin] with z hf hc hzs hza
    have hza' : z - a ≠ 0 := sub_ne_zero.mpr hza
    have hpoint := chartComplexGradient_isotropic g
      (hU.contMDiffAt (hs.mem_nhds hzs)) hc (hconformal z hzs)
    have heval (i : Fin (Module.finrank ℝ E)) :
        chartComplexGradient p U i z = (z - a) ^ m * B z i := by
      simpa only [Pi.smul_apply, smul_eq_mul] using congrFun hf i
    have hmul : ((z - a) ^ m * (z - a) ^ m) * Q z = 0 := by
      calc
        _ = ∑ i, ∑ j, (chartGramMatrix g p (U z) i j : ℂ) *
            chartComplexGradient p U i z * chartComplexGradient p U j z := by
          simp only [Q, Finset.mul_sum, heval]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = 0 := hpoint
    exact (mul_eq_zero.mp hmul).resolve_left
      (mul_ne_zero (pow_ne_zero _ hza') (pow_ne_zero _ hza'))
  have heq : (fun _ : ℂ => (0 : ℂ)) =ᶠ[𝓝[≠] a] Q := by
    filter_upwards [hz] with z hzero using hzero.symm
  have hzero : Tendsto Q (𝓝[≠] a) (𝓝 0) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℂ => (0 : ℂ)) (𝓝[≠] a) (𝓝 0)).congr' heq
  exact tendsto_nhds_unique (hQ.tendsto.mono_left nhdsWithin_le_nhds) hzero

private theorem chartGramBilin_symm
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (p x : M) (v w : E) :
    chartGramBilin g p x v w = chartGramBilin g p x w v := by
  classical
  rw [chartGramBilin_apply, chartGramBilin_apply, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hG : chartGramMatrix g p x j i = chartGramMatrix g p x i j :=
    g.symm x _ _
  rw [hG]
  ring

private theorem chartGramBilin_pos
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {p x : M}
    (hsrc : x ∈ (chartAt E p).source) {v : E} (hv : v ≠ 0) :
    0 < chartGramBilin g p x v v := by
  classical
  have hb : x ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hsrc
  have hc : (chartModelBasis E).equivFun v ≠ 0 := by
    intro hc
    apply hv
    apply (chartModelBasis E).equivFun.injective
    simpa only [map_zero] using hc
  have hpos := (chartGramMatrix_posDef g p hb).dotProduct_mulVec_pos hc
  convert hpos using 1
  rw [chartGramBilin_apply]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem leading_directions_metric
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {p x : M}
    (hsrc : x ∈ (chartAt E p).source)
    {b : Fin (Module.finrank ℝ E) → ℂ} (hb : b ≠ 0)
    (hnull : (∑ i, ∑ j, (chartGramMatrix g p x i j : ℂ) * b i * b j) = 0) :
    let A := leadingRealVector b
    let C := leadingNegImVector b
    let Q := chartGramBilin g p x
    0 < Q A A ∧ Q A A = Q C C ∧ Q A C = 0 ∧ Q C A = 0 := by
  classical
  let A := leadingRealVector b
  let C := leadingNegImVector b
  let Q := chartGramBilin g p x
  let G := chartGramMatrix g p x
  have hA (i : Fin (Module.finrank ℝ E)) :
      (chartModelBasis E).equivFun A i = (b i).re := by
    exact congrFun ((chartModelBasis E).equivFunL.apply_symm_apply
      (fun j => (b j).re)) i
  have hC (i : Fin (Module.finrank ℝ E)) :
      (chartModelBasis E).equivFun C i = -(b i).im := by
    exact congrFun ((chartModelBasis E).equivFunL.apply_symm_apply
      (fun j => -(b j).im)) i
  have hAA : Q A A = ∑ i, ∑ j, G i j * (b i).re * (b j).re := by
    simp only [Q, chartGramBilin_apply, hA, G]
  have hCC : Q C C = ∑ i, ∑ j, G i j * (-(b i).im) * (-(b j).im) := by
    simp only [Q, chartGramBilin_apply, hC, G]
  have hAC : Q A C = ∑ i, ∑ j, G i j * (b i).re * (-(b j).im) := by
    simp only [Q, chartGramBilin_apply, hA, hC, G]
  have hCA : Q C A = ∑ i, ∑ j, G i j * (-(b i).im) * (b j).re := by
    simp only [Q, chartGramBilin_apply, hA, hC, G]
  have htermRe (i j : Fin (Module.finrank ℝ E)) :
      ((G i j : ℂ) * b i * b j).re =
        G i j * (b i).re * (b j).re -
          G i j * (-(b i).im) * (-(b j).im) := by
    simp
  have htermIm (i j : Fin (Module.finrank ℝ E)) :
      ((G i j : ℂ) * b i * b j).im =
        -(G i j * (b i).re * (-(b j).im) +
          G i j * (-(b i).im) * (b j).re) := by
    simp
    ring
  have hre := congrArg Complex.re hnull
  change Complex.reCLM (∑ i, ∑ j, (G i j : ℂ) * b i * b j) = 0 at hre
  simp only [map_sum] at hre
  change (∑ i, ∑ j, ((G i j : ℂ) * b i * b j).re) = 0 at hre
  simp_rw [htermRe] at hre
  simp only [Finset.sum_sub_distrib] at hre
  rw [← hAA, ← hCC] at hre
  have him := congrArg Complex.im hnull
  change Complex.imCLM (∑ i, ∑ j, (G i j : ℂ) * b i * b j) = 0 at him
  simp only [map_sum] at him
  change (∑ i, ∑ j, ((G i j : ℂ) * b i * b j).im) = 0 at him
  simp_rw [htermIm] at him
  simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib] at him
  rw [← hAC, ← hCA] at him
  have hequal : Q A A = Q C C := sub_eq_zero.mp hre
  have hsym : Q A C = Q C A := chartGramBilin_symm g p x A C
  have horth : Q A C = 0 := by linarith
  have horth' : Q C A = 0 := hsym.symm.trans horth
  have hAne : A ≠ 0 := by
    intro hAzero
    have hCzero : C = 0 := by
      by_contra hCne
      have hpos := chartGramBilin_pos g hsrc hCne
      change 0 < Q C C at hpos
      rw [← hequal, hAzero] at hpos
      simp at hpos
    apply hb
    funext i
    change b i = (0 : ℂ)
    apply Complex.ext
    · change (b i).re = 0
      have hz := congrArg (fun v : E => (chartModelBasis E).equivFun v i) hAzero
      simpa only [hA, map_zero, Pi.zero_apply] using hz
    · change (b i).im = 0
      have hz := congrArg (fun v : E => (chartModelBasis E).equivFun v i) hCzero
      have hz' : -(b i).im = 0 := by simpa only [hC, map_zero, Pi.zero_apply] using hz
      exact neg_eq_zero.mp hz'
  exact ⟨chartGramBilin_pos g hsrc hAne, hequal, horth, horth'⟩

private theorem leading_projection_normalization
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {p x : M}
    (hsrc : x ∈ (chartAt E p).source)
    {b : Fin (Module.finrank ℝ E) → ℂ} (hb : b ≠ 0)
    (hnull : (∑ i, ∑ j, (chartGramMatrix g p x i j : ℂ) * b i * b j) = 0) :
    (chartLeadingPlaneProjection g p x b).comp (leadingRealDifferential b) =
      ContinuousLinearMap.id ℝ ℂ := by
  let A := leadingRealVector b
  let C := leadingNegImVector b
  let Q := chartGramBilin g p x
  let proj := chartLeadingPlaneProjection g p x b
  obtain ⟨hpos, hequal, hAC, hCA⟩ := leading_directions_metric g hsrc hb hnull
  change 0 < Q A A at hpos
  change Q A A = Q C C at hequal
  change Q A C = 0 at hAC
  change Q C A = 0 at hCA
  have hne : Q A A ≠ 0 := ne_of_gt hpos
  have hproj (v : E) : proj v =
      ((2 * Q A A)⁻¹ : ℝ) • ((Q A v : ℂ) + Complex.I * (Q C v : ℂ)) := rfl
  have hprojA : proj A = (1 / 2 : ℂ) := by
    rw [hproj, hCA]
    apply Complex.ext
    · simp
      field_simp [hne]
    · simp
  have hprojC : proj C = Complex.I / 2 := by
    rw [hproj, hAC, ← hequal]
    apply Complex.ext
    · simp
    · simp
      field_simp [hne]
  apply ContinuousLinearMap.ext
  intro w
  change proj (leadingRealDifferential b w) = w
  rw [leadingRealDifferential_apply]
  change proj (w.re • ((2 : ℝ) • A) + w.im • ((2 : ℝ) • C)) = w
  rw [map_add, map_smul, map_smul, map_smul, map_smul, hprojA, hprojC]
  apply Complex.ext <;> simp

/-- The metric projection of the original map has an invertible differential
off the base point, with quantitative bounds at the order of the supplied
complex-gradient factor. No sheet, inverse map, or branch removal is assumed. -/
theorem chartComplexGradient_leading_projection_nondegenerate
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 U s)
    (hconformal : ∀ z ∈ s, DiskMapConformalAt g U z)
    {a : ℂ} (ha : a ∈ s) {p : M}
    (hsrc : U a ∈ (chartAt E p).source)
    {m : ℕ} {B : ℂ → (Fin (Module.finrank ℝ E) → ℂ)}
    (hB : ContinuousAt B a) (hBne : B a ≠ 0)
    (hfactor : ∀ᶠ z in 𝓝 a,
      (fun i => chartComplexGradient p U i z) = (z - a) ^ m • B z) :
    let proj := chartLeadingPlaneProjection g p (U a) (B a)
    let F : ℂ → ℂ := fun z => proj (extChartAt 𝓘(ℝ, E) p (U z))
    ∃ r > 0, Metric.ball a r ⊆ s ∧
      (∀ z ∈ Metric.ball a r, U z ∈ (chartAt E p).source) ∧
      ∀ z ∈ Metric.ball a r, z ≠ a →
        (fderiv ℝ F z).IsInvertible ∧
        ∀ v : ℂ,
          (1 / 2 : ℝ) * ‖z - a‖ ^ m * ‖v‖ ≤ ‖fderiv ℝ F z v‖ ∧
          ‖fderiv ℝ F z v‖ ≤ (3 / 2 : ℝ) * ‖z - a‖ ^ m * ‖v‖ := by
  let proj := chartLeadingPlaneProjection g p (U a) (B a)
  let X : ℂ → E := extChartAt 𝓘(ℝ, E) p ∘ U
  let F : ℂ → ℂ := fun z => proj (X z)
  let T : ℂ → ℂ →L[ℝ] ℂ := fun z => proj.comp (leadingRealDifferential (B z))
  have hnull := chartComplexGradient_leading_isotropic g hs hU hconformal ha hsrc hB hfactor
  have hTa : T a = ContinuousLinearMap.id ℝ ℂ :=
    leading_projection_normalization g hsrc hBne hnull
  have hT : ContinuousAt T a :=
    continuousAt_const.clm_comp (continuous_leadingRealDifferential.continuousAt.comp hB)
  have hnear : ∀ᶠ z in 𝓝 a, ‖T z - ContinuousLinearMap.id ℝ ℂ‖ < (1 / 2 : ℝ) := by
    have hnorm : ContinuousAt (fun z => ‖T z - ContinuousLinearMap.id ℝ ℂ‖) a :=
      (hT.sub continuousAt_const).norm
    change (fun z : ℂ => ‖T z - ContinuousLinearMap.id ℝ ℂ‖) ⁻¹'
      Set.Iio (1 / 2 : ℝ) ∈ 𝓝 a
    apply hnorm.preimage_mem_nhds
    exact Iio_mem_nhds (by simp only [hTa, sub_self, norm_zero]; norm_num)
  have hUa := (hU.contMDiffAt (hs.mem_nhds ha)).continuousAt
  have hchart : ∀ᶠ z in 𝓝 a, U z ∈ (chartAt E p).source :=
    hUa.preimage_mem_nhds ((chartAt E p).open_source.mem_nhds hsrc)
  have hall : ∀ᶠ z in 𝓝 a,
      z ∈ s ∧ U z ∈ (chartAt E p).source ∧
        (fun i => chartComplexGradient p U i z) = (z - a) ^ m • B z ∧
        ‖T z - ContinuousLinearMap.id ℝ ℂ‖ < (1 / 2 : ℝ) := by
    filter_upwards [hs.mem_nhds ha, hchart, hfactor, hnear] with z hzs hzc hzf hzt
    exact ⟨hzs, hzc, hzf, hzt⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨r, hr, fun z hz => (hball hz).1, fun z hz => (hball hz).2.1, ?_⟩
  intro z hz hza
  obtain ⟨hzs, hzc, hzf, hzt⟩ := hball hz
  have hUz := hU.contMDiffAt (hs.mem_nhds hzs)
  have hX : ContDiffAt ℝ 1 X z :=
    ((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := 1) hzc).comp z hUz).contDiffAt
  have hFderiv : fderiv ℝ F z = proj.comp (fderiv ℝ X z) :=
    (proj.hasFDerivAt.comp z (hX.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have heval (v : ℂ) : fderiv ℝ F z v = T z ((z - a) ^ m * v) := by
    rw [hFderiv, ContinuousLinearMap.comp_apply]
    have hXD : fderiv ℝ X z =
        leadingRealDifferential (fun i => chartComplexGradient p U i z) :=
      chart_fderiv_eq_leadingRealDifferential hUz hzc
    rw [hXD, hzf, leadingRealDifferential_smul]
    rfl
  have herr (w : ℂ) : ‖T z w - w‖ ≤ (1 / 2 : ℝ) * ‖w‖ := by
    calc
      _ = ‖(T z - ContinuousLinearMap.id ℝ ℂ) w‖ := rfl
      _ ≤ ‖T z - ContinuousLinearMap.id ℝ ℂ‖ * ‖w‖ :=
        (T z - ContinuousLinearMap.id ℝ ℂ).le_opNorm w
      _ ≤ (1 / 2 : ℝ) * ‖w‖ :=
        mul_le_mul_of_nonneg_right hzt.le (norm_nonneg w)
  have hupper (w : ℂ) : ‖T z w‖ ≤ (3 / 2 : ℝ) * ‖w‖ := by
    have ht := norm_le_norm_sub_add (T z w) w
    linarith [herr w]
  have hlower (w : ℂ) : (1 / 2 : ℝ) * ‖w‖ ≤ ‖T z w‖ := by
    have ht := norm_le_norm_sub_add w (T z w)
    rw [norm_sub_rev] at ht
    linarith [herr w]
  have hbounds (v : ℂ) :
      (1 / 2 : ℝ) * ‖z - a‖ ^ m * ‖v‖ ≤ ‖fderiv ℝ F z v‖ ∧
        ‖fderiv ℝ F z v‖ ≤ (3 / 2 : ℝ) * ‖z - a‖ ^ m * ‖v‖ := by
    rw [heval]
    constructor
    · simpa only [norm_mul, norm_pow, mul_assoc] using hlower ((z - a) ^ m * v)
    · simpa only [norm_mul, norm_pow, mul_assoc] using hupper ((z - a) ^ m * v)
  have hkpos : 0 < (1 / 2 : ℝ) * ‖z - a‖ ^ m :=
    mul_pos (by norm_num) (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hza)) _)
  have hinj : Function.Injective (fderiv ℝ F z) := by
    intro v w hvw
    have hzero : fderiv ℝ F z (v - w) = 0 := by
      rw [map_sub, hvw, sub_self]
    have hbound := (hbounds (v - w)).1
    rw [hzero, norm_zero] at hbound
    have hnorm : ‖v - w‖ = 0 := by nlinarith [norm_nonneg (v - w)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  have hbij : Function.Bijective (fderiv ℝ F z) :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj⟩
  let e : ℂ ≃L[ℝ] ℂ :=
    (LinearEquiv.ofBijective (fderiv ℝ F z).toLinearMap hbij).toContinuousLinearEquiv
  have he : (e : ℂ →L[ℝ] ℂ) = fderiv ℝ F z := by
    ext v
    rfl
  exact ⟨⟨e, he⟩, hbounds⟩

/-- A differentiable coefficient gives one additional order in the error of
the original projected differential from its normalized complex monomial. -/
theorem chartComplexGradient_leading_projection_fderiv_error
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 U s)
    (hconformal : ∀ z ∈ s, DiskMapConformalAt g U z)
    {a : ℂ} (ha : a ∈ s) {p : M}
    (hsrc : U a ∈ (chartAt E p).source)
    {m : ℕ} {B : ℂ → (Fin (Module.finrank ℝ E) → ℂ)}
    (hB : ContDiffAt ℝ 1 B a) (hBne : B a ≠ 0)
    (hfactor : ∀ᶠ z in 𝓝 a,
      (fun i => chartComplexGradient p U i z) = (z - a) ^ m • B z) :
    let proj := chartLeadingPlaneProjection g p (U a) (B a)
    let F : ℂ → ℂ := fun z => proj (extChartAt 𝓘(ℝ, E) p (U z))
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ Metric.ball a r ⊆ s ∧
      (∀ z ∈ Metric.ball a r, U z ∈ (chartAt E p).source) ∧
      ∀ z ∈ Metric.ball a r, ∀ v : ℂ,
        ‖fderiv ℝ F z v - (z - a) ^ m * v‖ ≤
          C * ‖z - a‖ ^ (m + 1) * ‖v‖ := by
  let proj := chartLeadingPlaneProjection g p (U a) (B a)
  let X : ℂ → E := extChartAt 𝓘(ℝ, E) p ∘ U
  let F : ℂ → ℂ := fun z => proj (X z)
  let T : ℂ → ℂ →L[ℝ] ℂ := fun z => proj.comp (leadingRealDifferential (B z))
  have hnull := chartComplexGradient_leading_isotropic g hs hU hconformal ha hsrc
    hB.continuousAt hfactor
  have hTa : T a = ContinuousLinearMap.id ℝ ℂ :=
    leading_projection_normalization g hsrc hBne hnull
  have hBd : DifferentiableAt ℝ B a := hB.differentiableAt (by norm_num)
  have hA : DifferentiableAt ℝ (fun z => leadingRealVector (B z)) a :=
    (chartModelBasis E).equivFunL.symm.differentiableAt.comp a
      (differentiableAt_pi.mpr (fun i =>
        Complex.reCLM.differentiableAt.comp a (differentiableAt_pi.mp hBd i)))
  have hC : DifferentiableAt ℝ (fun z => leadingNegImVector (B z)) a :=
    (chartModelBasis E).equivFunL.symm.differentiableAt.comp a
      (differentiableAt_pi.mpr (fun i =>
        (Complex.imCLM.differentiableAt.comp a (differentiableAt_pi.mp hBd i)).neg))
  have hL : DifferentiableAt ℝ (fun z => leadingRealDifferential (B z)) a :=
    ((ContinuousLinearMap.smulRightL ℝ ℂ E Complex.reCLM).differentiableAt.comp a
      (hA.const_smul (2 : ℝ))).add
        ((ContinuousLinearMap.smulRightL ℝ ℂ E Complex.imCLM).differentiableAt.comp a
          (hC.const_smul (2 : ℝ)))
  have hT : DifferentiableAt ℝ T a :=
    (ContinuousLinearMap.compL ℝ ℂ E ℂ proj).differentiableAt.comp a hL
  obtain ⟨C, hCpos, hbound⟩ := Asymptotics.isBigO_iff'.mp hT.isBigO_sub
  have hUa := (hU.contMDiffAt (hs.mem_nhds ha)).continuousAt
  have hchart : ∀ᶠ z in 𝓝 a, U z ∈ (chartAt E p).source :=
    hUa.preimage_mem_nhds ((chartAt E p).open_source.mem_nhds hsrc)
  have hall : ∀ᶠ z in 𝓝 a,
      z ∈ s ∧ U z ∈ (chartAt E p).source ∧
        (fun i => chartComplexGradient p U i z) = (z - a) ^ m • B z ∧
        ‖T z - T a‖ ≤ C * ‖z - a‖ := by
    filter_upwards [hs.mem_nhds ha, hchart, hfactor, hbound] with z hzs hzc hzf hzt
    exact ⟨hzs, hzc, hzf, hzt⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨C, r, hCpos, hr, fun z hz => (hball hz).1,
    fun z hz => (hball hz).2.1, ?_⟩
  intro z hz v
  obtain ⟨hzs, hzc, hzf, hzt⟩ := hball hz
  have hUz := hU.contMDiffAt (hs.mem_nhds hzs)
  have hX : ContDiffAt ℝ 1 X z :=
    ((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := 1) hzc).comp z hUz).contDiffAt
  have hFderiv : fderiv ℝ F z = proj.comp (fderiv ℝ X z) :=
    (proj.hasFDerivAt.comp z (hX.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have heval : fderiv ℝ F z v = T z ((z - a) ^ m * v) := by
    rw [hFderiv, ContinuousLinearMap.comp_apply]
    have hXD : fderiv ℝ X z =
        leadingRealDifferential (fun i => chartComplexGradient p U i z) :=
      chart_fderiv_eq_leadingRealDifferential hUz hzc
    rw [hXD, hzf, leadingRealDifferential_smul]
    rfl
  calc
    ‖fderiv ℝ F z v - (z - a) ^ m * v‖ =
        ‖(T z - T a) ((z - a) ^ m * v)‖ := by
      rw [heval, sub_apply, hTa, ContinuousLinearMap.id_apply]
    _ ≤ ‖T z - T a‖ * ‖(z - a) ^ m * v‖ := (T z - T a).le_opNorm _
    _ ≤ (C * ‖z - a‖) * ‖(z - a) ^ m * v‖ :=
      mul_le_mul_of_nonneg_right hzt (norm_nonneg _)
    _ = C * ‖z - a‖ ^ (m + 1) * ‖v‖ := by
      rw [norm_mul, norm_pow, pow_succ]
      ring

/-- A single normal for the original chart metric gives a scalar graph for every
smooth inverse germ of the actual leading-plane projection in dimension three. -/
theorem chartLeadingPlaneProjection_exists_graph_germs
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hd3 : Module.finrank ℝ E = 3)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    {a : ℂ} (ha : a ∈ s) {p : M}
    (hchart : ∀ z ∈ s, U z ∈ (chartAt E p).source)
    {b : Fin (Module.finrank ℝ E) → ℂ} (hb : b ≠ 0)
    (hnull : (∑ i, ∑ j,
      (chartGramMatrix g p (U a) i j : ℂ) * b i * b j) = 0)
    (hreg : ∀ z ∈ s, z ≠ a →
      (fderiv ℝ (fun w => chartLeadingPlaneProjection g p (U a) b
        (extChartAt 𝓘(ℝ, E) p (U w))) z).IsInvertible) :
    let Q := chartGramBilin g p (U a)
    let proj := chartLeadingPlaneProjection g p (U a) b
    let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
    let F : ℂ → ℂ := fun z => proj (X z)
    let lift : ℂ → E := fun w => (chartModelBasis E).equivFunL.symm
      (fun i => (2 : ℝ) * (w * b i).re)
    ∃ N : E,
      Q N N = 1 ∧ proj N = 0 ∧
      (∀ v : E, v = lift (proj v) + (Q N v) • N) ∧
      ∀ z ∈ s, z ≠ a →
        ∃ e : OpenPartialHomeomorph ℂ ℂ,
          z ∈ e.source ∧ e.source ⊆ s \ {a} ∧
          (e : ℂ → ℂ) = F ∧
          ContDiffOn ℝ ∞ e.symm e.target ∧
          let h : ℂ → ℝ := fun y => Q N (X (e.symm y) - X a)
          ContDiffOn ℝ ∞ h e.target ∧
          ∀ y ∈ e.target,
            X (e.symm y) = X a + lift (y - F a) + h y • N := by
  classical
  let Q := chartGramBilin g p (U a)
  let proj := chartLeadingPlaneProjection g p (U a) b
  let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
  let F : ℂ → ℂ := fun z => proj (X z)
  let lift : ℂ → E := fun w => (chartModelBasis E).equivFunL.symm
    (fun i => (2 : ℝ) * (w * b i).re)
  let L := leadingRealDifferential b
  let A := leadingRealVector b
  let C := leadingNegImVector b
  have hlift (w : ℂ) : lift w = L w := by
    apply (chartModelBasis E).equivFunL.injective
    ext i
    simp [lift, L, leadingRealDifferential, leadingRealVector, leadingNegImVector,
      smul_eq_mul, Complex.mul_re, chartModelBasis_repr_equivFunL_symm]
    ring
  have hnorm : proj.comp L = ContinuousLinearMap.id ℝ ℂ :=
    leading_projection_normalization g (hchart a ha) hb hnull
  have hprojL (w : ℂ) : proj (L w) = w :=
    congrArg (fun T : ℂ →L[ℝ] ℂ => T w) hnorm
  have hsurj : Function.Surjective proj := fun w => ⟨L w, hprojL w⟩
  let K := LinearMap.ker proj.toLinearMap
  have hrange : LinearMap.range proj.toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hKdim : Module.finrank ℝ K = 1 := by
    have hdim := proj.toLinearMap.finrank_range_add_finrank_ker
    rw [hrange, finrank_top, Module.finrank_eq_card_basis Complex.basisOneI,
      Fintype.card_fin, hd3] at hdim
    change 2 + Module.finrank ℝ K = 3 at hdim
    omega
  have hKne : K ≠ ⊥ := by
    intro hzero
    rw [hzero, finrank_bot] at hKdim
    norm_num at hKdim
  obtain ⟨N₀, hN₀K, hN₀ne⟩ := K.ne_bot_iff.mp hKne
  have hN₀proj : proj N₀ = 0 := hN₀K
  have hN₀pos : 0 < Q N₀ N₀ := chartGramBilin_pos g (hchart a ha) hN₀ne
  let t := Real.sqrt (Q N₀ N₀)
  have ht : 0 < t := Real.sqrt_pos.mpr hN₀pos
  have htsq : t * t = Q N₀ N₀ := Real.mul_self_sqrt hN₀pos.le
  let N := t⁻¹ • N₀
  have hNproj : proj N = 0 := by simp [N, hN₀proj]
  have hNN : Q N N = 1 := by
    calc
      Q N N = t⁻¹ * (t⁻¹ * (Q N₀ N₀)) := by simp [N]
      _ = 1 := by
        rw [← htsq]
        field_simp [ne_of_gt ht]
  have hNne : N ≠ 0 := by
    intro hzero
    simp [hzero] at hNN
  have hNK : N ∈ K := hNproj
  have hspan : K = Submodule.span ℝ ({N} : Set E) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hKdim hNK hNne
  obtain ⟨hAA, _, _, _⟩ := leading_directions_metric g (hchart a ha) hb hnull
  change 0 < Q A A at hAA
  have hscale : (2 * Q A A)⁻¹ ≠ 0 :=
    inv_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hAA))
  have hproj (v : E) : proj v =
      ((2 * Q A A)⁻¹ : ℝ) • ((Q A v : ℂ) + Complex.I * (Q C v : ℂ)) := rfl
  have hNcoord := hNproj
  rw [hproj] at hNcoord
  have hre : (2 * Q A A)⁻¹ * Q A N = 0 := by
    simpa using congrArg Complex.re hNcoord
  have him : (2 * Q A A)⁻¹ * Q C N = 0 := by
    simpa using congrArg Complex.im hNcoord
  have hAN : Q A N = 0 := (mul_eq_zero.mp hre).resolve_left hscale
  have hCN : Q C N = 0 := (mul_eq_zero.mp him).resolve_left hscale
  have hNA : Q N A = 0 := (chartGramBilin_symm g p (U a) N A).trans hAN
  have hNC : Q N C = 0 := (chartGramBilin_symm g p (U a) N C).trans hCN
  have hNL (w : ℂ) : Q N (L w) = 0 := by
    change Q N (w.re • ((2 : ℝ) • A) + w.im • ((2 : ℝ) • C)) = 0
    simp only [map_add, map_smul, hNA, hNC, smul_zero, zero_add]
  have hsplit (v : E) : v = L (proj v) + (Q N v) • N := by
    have hrem : v - L (proj v) ∈ K := by
      change proj (v - L (proj v)) = 0
      rw [map_sub, hprojL, sub_self]
    rw [hspan] at hrem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hrem
    have hcQ : c = Q N v := by
      have hq := congrArg (Q N) hc
      simpa only [map_smul, map_sub, hNN, hNL, smul_eq_mul, mul_one, sub_zero]
        using hq
    calc
      v = L (proj v) + (v - L (proj v)) := by abel
      _ = L (proj v) + (Q N v) • N := by rw [← hc, hcQ]
  have hsplit' (v : E) : v = lift (proj v) + (Q N v) • N := by
    rw [hlift]
    exact hsplit v
  refine ⟨N, hNN, hNproj, hsplit', ?_⟩
  intro z hz hza
  have hX : ContDiffOn ℝ ∞ X s := by
    intro w hw
    exact (((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) (hchart w hw)).comp w
      (hU.contMDiffAt (hs.mem_nhds hw))).contDiffAt).contDiffWithinAt
  have hF : ContDiffOn ℝ ∞ F s := proj.contDiff.comp_contDiffOn hX
  have hpunctured : IsOpen (s \ {a}) := hs.sdiff isClosed_singleton
  have hzpunctured : z ∈ s \ {a} := ⟨hz, hza⟩
  obtain ⟨D, hD⟩ := hreg z hz hza
  change (D : ℂ →L[ℝ] ℂ) = fderiv ℝ F z at hD
  have hFD : HasFDerivAt F (D : ℂ →L[ℝ] ℂ) z := by
    rw [hD]
    exact ((hF.contDiffAt (hs.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt
  obtain ⟨e, hze, hes, he, hei⟩ :=
    Analysis.exists_smooth_localInverse hpunctured (hF.mono Set.sdiff_subset)
      hzpunctured D hFD
  refine ⟨e, hze, hes, he, hei, ?_⟩
  let h : ℂ → ℝ := fun y => Q N (X (e.symm y) - X a)
  have hXe : ContDiffOn ℝ ∞ (fun y => X (e.symm y)) e.target :=
    hX.comp hei (fun y hy => (hes (e.map_target hy)).1)
  have hdiff : ContDiffOn ℝ ∞ (fun y => X (e.symm y) - X a) e.target :=
    hXe.sub contDiffOn_const
  have hh : ContDiffOn ℝ ∞ h e.target := (Q N).contDiff.comp_contDiffOn hdiff
  refine ⟨hh, ?_⟩
  intro y hy
  have hright : F (e.symm y) = y := by
    rw [← he]
    exact e.right_inv hy
  have hp : proj (X (e.symm y) - X a) = y - F a := by
    rw [map_sub]
    change F (e.symm y) - F a = y - F a
    rw [hright]
  calc
    X (e.symm y) = X a + (X (e.symm y) - X a) := by abel
    _ = X a + (lift (y - F a) + h y • N) := by
      rw [hsplit' (X (e.symm y) - X a), hp]
    _ = X a + lift (y - F a) + h y • N := (add_assoc _ _ _).symm

/-- The actual chart differential retains one additional order beyond the
leading coefficient of its supplied complex-gradient factor. -/
theorem chartComplexGradient_leading_fderiv_error
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 U s)
    {a : ℂ} (ha : a ∈ s) {p : M}
    (hsrc : U a ∈ (chartAt E p).source)
    {m : ℕ} {B : ℂ → (Fin (Module.finrank ℝ E) → ℂ)}
    (hB : DifferentiableAt ℝ B a)
    (hfactor : ∀ᶠ z in 𝓝 a,
      (fun i => chartComplexGradient p U i z) = (z - a) ^ m • B z) :
    let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
    let lift : ℂ → E := fun w => (chartModelBasis E).equivFunL.symm
      (fun i => (2 : ℝ) * (w * B a i).re)
    ∃ C₀ ρ : ℝ, 0 < C₀ ∧ 0 < ρ ∧ Metric.ball a ρ ⊆ s ∧
      (∀ z ∈ Metric.ball a ρ, U z ∈ (chartAt E p).source) ∧
      ∀ z ∈ Metric.ball a ρ, ∀ v : ℂ,
        ‖fderiv ℝ X z v - lift ((z - a) ^ m * v)‖ ≤
          C₀ * ‖z - a‖ ^ (m + 1) * ‖v‖ := by
  let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
  let lift : ℂ → E := fun w => (chartModelBasis E).equivFunL.symm
    (fun i => (2 : ℝ) * (w * B a i).re)
  let T : ℂ → ℂ →L[ℝ] E := fun z => leadingRealDifferential (B z)
  have hlift (w : ℂ) : lift w = leadingRealDifferential (B a) w := by
    apply (chartModelBasis E).equivFunL.injective
    ext i
    simp [lift, leadingRealDifferential, leadingRealVector, leadingNegImVector,
      smul_eq_mul, Complex.mul_re, chartModelBasis_repr_equivFunL_symm]
    ring
  have hA : DifferentiableAt ℝ (fun z => leadingRealVector (B z)) a :=
    (chartModelBasis E).equivFunL.symm.differentiableAt.comp a
      (differentiableAt_pi.mpr (fun i =>
        Complex.reCLM.differentiableAt.comp a (differentiableAt_pi.mp hB i)))
  have hC : DifferentiableAt ℝ (fun z => leadingNegImVector (B z)) a :=
    (chartModelBasis E).equivFunL.symm.differentiableAt.comp a
      (differentiableAt_pi.mpr (fun i =>
        (Complex.imCLM.differentiableAt.comp a (differentiableAt_pi.mp hB i)).neg))
  have hT : DifferentiableAt ℝ T a :=
    ((ContinuousLinearMap.smulRightL ℝ ℂ E Complex.reCLM).differentiableAt.comp a
      (hA.const_smul (2 : ℝ))).add
        ((ContinuousLinearMap.smulRightL ℝ ℂ E Complex.imCLM).differentiableAt.comp a
          (hC.const_smul (2 : ℝ)))
  obtain ⟨C₀, hC₀, hbound⟩ := Asymptotics.isBigO_iff'.mp hT.isBigO_sub
  have hUa := (hU.contMDiffAt (hs.mem_nhds ha)).continuousAt
  have hchart : ∀ᶠ z in 𝓝 a, U z ∈ (chartAt E p).source :=
    hUa.preimage_mem_nhds ((chartAt E p).open_source.mem_nhds hsrc)
  have hall : ∀ᶠ z in 𝓝 a,
      z ∈ s ∧ U z ∈ (chartAt E p).source ∧
        (fun i => chartComplexGradient p U i z) = (z - a) ^ m • B z ∧
        ‖T z - T a‖ ≤ C₀ * ‖z - a‖ := by
    filter_upwards [hs.mem_nhds ha, hchart, hfactor, hbound] with z hzs hzc hzf hzt
    exact ⟨hzs, hzc, hzf, hzt⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨C₀, ρ, hC₀, hρ, fun z hz => (hball hz).1,
    fun z hz => (hball hz).2.1, ?_⟩
  intro z hz v
  obtain ⟨hzs, hzc, hzf, hzt⟩ := hball hz
  have hXD : fderiv ℝ X z =
      leadingRealDifferential (fun i => chartComplexGradient p U i z) :=
    chart_fderiv_eq_leadingRealDifferential (hU.contMDiffAt (hs.mem_nhds hzs)) hzc
  have heval : fderiv ℝ X z v = T z ((z - a) ^ m * v) := by
    rw [hXD, hzf]
    exact leadingRealDifferential_smul (B z) ((z - a) ^ m) v
  calc
    ‖fderiv ℝ X z v - lift ((z - a) ^ m * v)‖ =
        ‖(T z - T a) ((z - a) ^ m * v)‖ := by
      simp only [heval, hlift, sub_apply, T]
    _ ≤ ‖T z - T a‖ * ‖(z - a) ^ m * v‖ := (T z - T a).le_opNorm _
    _ ≤ (C₀ * ‖z - a‖) * ‖(z - a) ^ m * v‖ :=
      mul_le_mul_of_nonneg_right hzt (norm_nonneg _)
    _ = C₀ * ‖z - a‖ ^ (m + 1) * ‖v‖ := by
      rw [norm_mul, norm_pow, pow_succ]
      ring

/-- The original-metric normal heights of all prescribed local inverse germs
have a uniform linear bound in their source distance from the branch center. -/
theorem chartComplexGradient_leading_graph_slope
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 U s)
    (hconformal : ∀ z ∈ s, DiskMapConformalAt g U z)
    {a : ℂ} (ha : a ∈ s) {p : M}
    (hsrc : U a ∈ (chartAt E p).source)
    {m : ℕ} {B : ℂ → (Fin (Module.finrank ℝ E) → ℂ)}
    (hB : DifferentiableAt ℝ B a) (hBne : B a ≠ 0)
    (hfactor : ∀ᶠ z in 𝓝 a,
      (fun i => chartComplexGradient p U i z) = (z - a) ^ m • B z) :
    let Q := chartGramBilin g p (U a)
    let proj := chartLeadingPlaneProjection g p (U a) (B a)
    let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
    let F : ℂ → ℂ := fun z => proj (X z)
    let lift : ℂ → E := fun w => (chartModelBasis E).equivFunL.symm
      (fun i => (2 : ℝ) * (w * B a i).re)
    ∃ C₀ ρ : ℝ, 0 < C₀ ∧ 0 < ρ ∧ Metric.ball a ρ ⊆ s ∧
      (∀ z ∈ Metric.ball a ρ, U z ∈ (chartAt E p).source) ∧
      (∀ z ∈ Metric.ball a ρ, ∀ v : ℂ,
        ‖fderiv ℝ X z v - lift ((z - a) ^ m * v)‖ ≤
          C₀ * ‖z - a‖ ^ (m + 1) * ‖v‖) ∧
      ∀ N : E, Q N N = 1 →
        (∀ v : E, v = lift (proj v) + (Q N v) • N) →
        ∀ e : OpenPartialHomeomorph ℂ ℂ,
          (e : ℂ → ℂ) = F →
          let h : ℂ → ℝ := fun y => Q N (X (e.symm y) - X a)
          ∀ y ∈ e.target,
            e.symm y ∈ Metric.ball a ρ → e.symm y ≠ a →
            ‖fderiv ℝ h y‖ ≤ (2 * C₀ * ‖Q N‖) * ‖e.symm y - a‖ := by
  let Q := chartGramBilin g p (U a)
  let proj := chartLeadingPlaneProjection g p (U a) (B a)
  let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
  let F : ℂ → ℂ := fun z => proj (X z)
  let lift : ℂ → E := fun w => (chartModelBasis E).equivFunL.symm
    (fun i => (2 : ℝ) * (w * B a i).re)
  have hlift (w : ℂ) : lift w = leadingRealDifferential (B a) w := by
    apply (chartModelBasis E).equivFunL.injective
    ext i
    simp [lift, leadingRealDifferential, leadingRealVector, leadingNegImVector,
      smul_eq_mul, Complex.mul_re, chartModelBasis_repr_equivFunL_symm]
    ring
  obtain ⟨C₀, r₀, hC₀, hr₀, hsub₀, hchart₀, herror⟩ :=
    chartComplexGradient_leading_fderiv_error (E := E) (M := M)
      (U := U) (s := s) hs hU (a := a) ha (p := p) hsrc
      (m := m) (B := B) hB hfactor
  obtain ⟨r₁, hr₁, _, _, hreg⟩ :=
    chartComplexGradient_leading_projection_nondegenerate (E := E) (M := M) g
      (U := U) (s := s) hs hU hconformal (a := a) ha (p := p) hsrc
      (m := m) (B := B) hB.continuousAt hBne hfactor
  let ρ := min r₀ r₁
  have hleft : Metric.ball a ρ ⊆ Metric.ball a r₀ :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hright : Metric.ball a ρ ⊆ Metric.ball a r₁ :=
    Metric.ball_subset_ball (min_le_right _ _)
  have hnull := chartComplexGradient_leading_isotropic (E := E) (M := M) g
    (U := U) (s := s) hs hU hconformal (a := a) ha (p := p) hsrc
    (m := m) (B := B) hB.continuousAt hfactor
  have hnorm : proj.comp (leadingRealDifferential (B a)) =
      ContinuousLinearMap.id ℝ ℂ :=
    leading_projection_normalization g hsrc hBne hnull
  have hprojL (w : ℂ) : proj (lift w) = w := by
    rw [hlift]
    exact congrArg (fun T : ℂ →L[ℝ] ℂ => T w) hnorm
  refine ⟨C₀, ρ, hC₀, lt_min hr₀ hr₁, hleft.trans hsub₀,
    fun z hz => hchart₀ z (hleft hz),
    fun z hz v => herror z (hleft hz) v, ?_⟩
  intro N hunit hsplit e he
  change Q N N = 1 at hunit
  change ∀ v : E, v = lift (proj v) + (Q N v) • N at hsplit
  let h : ℂ → ℝ := fun y => Q N (X (e.symm y) - X a)
  change ∀ y ∈ e.target, e.symm y ∈ Metric.ball a ρ → e.symm y ≠ a →
    ‖fderiv ℝ h y‖ ≤ (2 * C₀ * ‖Q N‖) * ‖e.symm y - a‖
  have hNL (w : ℂ) : Q N (lift w) = 0 := by
    have hv := congrArg (Q N) (hsplit (lift w))
    simp only [hprojL, map_add, map_smul, smul_eq_mul, hunit, mul_one] at hv
    linarith
  intro y hy hz hza
  let z := e.symm y
  have hX : ContDiffAt ℝ 1 X z :=
    ((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := 1) (hchart₀ z (hleft hz))).comp z
      (hU.contMDiffAt (hs.mem_nhds (hsub₀ (hleft hz))))).contDiffAt
  have hF : DifferentiableAt ℝ F z :=
    proj.differentiableAt.comp z (hX.differentiableAt (by norm_num))
  obtain ⟨hinv, hbounds⟩ := hreg z (hright hz) hza
  obtain ⟨D, hD⟩ := hinv
  change (D : ℂ →L[ℝ] ℂ) = fderiv ℝ F z at hD
  have hFD : HasFDerivAt F (D : ℂ →L[ℝ] ℂ) z := by
    rw [hD]
    exact hF.hasFDerivAt
  have hED : HasFDerivAt (e : ℂ → ℂ) (D : ℂ →L[ℝ] ℂ) z := by
    rw [he]
    exact hFD
  have hi : HasFDerivAt e.symm (D.symm : ℂ →L[ℝ] ℂ) y :=
    e.hasFDerivAt_symm hy hED
  have hh : HasFDerivAt h ((Q N).comp
      ((fderiv ℝ X z).comp (D.symm : ℂ →L[ℝ] ℂ))) y :=
    (Q N).hasFDerivAt.comp y
      (((hX.differentiableAt (by norm_num)).hasFDerivAt.comp y hi).sub_const (X a))
  apply (fderiv ℝ h y).opNorm_le_bound (by positivity)
  intro w
  have hlow := (hbounds (D.symm w)).1
  change (1 / 2 : ℝ) * ‖z - a‖ ^ m * ‖D.symm w‖ ≤
    ‖fderiv ℝ F z (D.symm w)‖ at hlow
  rw [← hD] at hlow
  change (1 / 2 : ℝ) * ‖z - a‖ ^ m * ‖D.symm w‖ ≤
    ‖D (D.symm w)‖ at hlow
  rw [D.apply_symm_apply] at hlow
  have hscale : ‖z - a‖ ^ m * ‖D.symm w‖ ≤ 2 * ‖w‖ := by
    nlinarith only [hlow]
  calc
    ‖fderiv ℝ h y w‖ = ‖Q N (fderiv ℝ X z (D.symm w))‖ := by
      simp only [hh.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    _ = ‖Q N (fderiv ℝ X z (D.symm w) -
        lift ((z - a) ^ m * D.symm w))‖ := by
      rw [map_sub, hNL, sub_zero]
    _ ≤ ‖Q N‖ * ‖fderiv ℝ X z (D.symm w) -
        lift ((z - a) ^ m * D.symm w)‖ := (Q N).le_opNorm _
    _ ≤ ‖Q N‖ * (C₀ * ‖z - a‖ ^ (m + 1) * ‖D.symm w‖) :=
      mul_le_mul_of_nonneg_left (herror z (hleft hz) (D.symm w)) (norm_nonneg _)
    _ = (C₀ * ‖Q N‖ * ‖z - a‖) * (‖z - a‖ ^ m * ‖D.symm w‖) := by
      rw [pow_succ]
      ring
    _ ≤ (C₀ * ‖Q N‖ * ‖z - a‖) * (2 * ‖w‖) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = ((2 * C₀ * ‖Q N‖) * ‖e.symm y - a‖) * ‖w‖ := by
      change (C₀ * ‖Q N‖ * ‖z - a‖) * (2 * ‖w‖) =
        ((2 * C₀ * ‖Q N‖) * ‖z - a‖) * ‖w‖
      ring


/- Append inside DifferentialGeometry.Geometry in ComplexGradientLeadingPlane.lean.
   This fragment deliberately reuses that module's existing private metric
   normalization facts. It is not a standalone importable file. -/

/-- A vector killed by the original-metric leading-plane projection annihilates
the same leading complex coefficient under the original metric. -/
theorem chartLeadingPlaneProjection_normal_coefficient_eq_zero
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {p x : M}
    (hsrc : x ∈ (chartAt E p).source)
    {b : Fin (Module.finrank ℝ E) → ℂ} (hb : b ≠ 0)
    (hnull : (∑ i, ∑ j, (chartGramMatrix g p x i j : ℂ) * b i * b j) = 0)
    {N : E} (hN : chartLeadingPlaneProjection g p x b N = 0) :
    ∑ i, (chartGramBilin g p x N (chartModelBasis E i) : ℂ) * b i = 0 := by
  classical
  let A := leadingRealVector b
  let C := leadingNegImVector b
  let Q := chartGramBilin g p x
  obtain ⟨hpos, _, _, _⟩ := leading_directions_metric g hsrc hb hnull
  change 0 < Q A A at hpos
  have hscale : (2 * Q A A)⁻¹ ≠ 0 :=
    inv_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hpos))
  have hproj : chartLeadingPlaneProjection g p x b N =
      ((2 * Q A A)⁻¹ : ℝ) • ((Q A N : ℂ) + Complex.I * (Q C N : ℂ)) := rfl
  rw [hproj] at hN
  have hre : (2 * Q A A)⁻¹ * Q A N = 0 := by
    simpa using congrArg Complex.re hN
  have him : (2 * Q A A)⁻¹ * Q C N = 0 := by
    simpa using congrArg Complex.im hN
  have hAN : Q A N = 0 := (mul_eq_zero.mp hre).resolve_left hscale
  have hCN : Q C N = 0 := (mul_eq_zero.mp him).resolve_left hscale
  have hNA : Q N A = 0 := (chartGramBilin_symm g p x N A).trans hAN
  have hNC : Q N C = 0 := (chartGramBilin_symm g p x N C).trans hCN
  have hA (i : Fin (Module.finrank ℝ E)) :
      (chartModelBasis E).equivFun A i = (b i).re :=
    congrFun ((chartModelBasis E).equivFunL.apply_symm_apply (fun j => (b j).re)) i
  have hC (i : Fin (Module.finrank ℝ E)) :
      (chartModelBasis E).equivFun C i = -(b i).im :=
    congrFun ((chartModelBasis E).equivFunL.apply_symm_apply (fun j => -(b j).im)) i
  have hsumA : ∑ i, Q N (chartModelBasis E i) * (b i).re = 0 := by
    calc
      _ = Q N (∑ i, (chartModelBasis E).equivFun A i • chartModelBasis E i) := by
        simp only [map_sum, map_smul, smul_eq_mul, hA, mul_comm]
      _ = 0 := by rw [(chartModelBasis E).sum_equivFun, hNA]
  have hsumC : ∑ i, Q N (chartModelBasis E i) * (-(b i).im) = 0 := by
    calc
      _ = Q N (∑ i, (chartModelBasis E).equivFun C i • chartModelBasis E i) := by
        simp only [map_sum, map_smul, smul_eq_mul, hC, mul_comm]
      _ = 0 := by rw [(chartModelBasis E).sum_equivFun, hNC]
  have hsumIm : ∑ i, Q N (chartModelBasis E i) * (b i).im = 0 := by
    simpa only [mul_neg, Finset.sum_neg_distrib, neg_eq_zero] using hsumC
  apply Complex.ext
  · change Complex.reCLM (∑ i, (Q N (chartModelBasis E i) : ℂ) * b i) = 0
    simpa only [map_sum, Complex.reCLM_apply, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hsumA
  · change Complex.imCLM (∑ i, (Q N (chartModelBasis E i) : ℂ) * b i) = 0
    simpa only [map_sum, Complex.imCLM_apply, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] using hsumIm


/-- The original leading-plane differential has a literal `C¹` real-linear
coefficient normalized to the identity. The supplied order and coefficient are
retained; the factorization holds on one neighborhood of the same base point. -/
theorem chartComplexGradient_leading_projection_c1_factor
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 U s)
    (hconformal : ∀ z ∈ s, DiskMapConformalAt g U z)
    {a : ℂ} (ha : a ∈ s) {p : M}
    (hsrc : U a ∈ (chartAt E p).source)
    {m : ℕ} {B : ℂ → (Fin (Module.finrank ℝ E) → ℂ)}
    (hB : ContDiffAt ℝ 1 B a) (hBne : B a ≠ 0)
    (hfactor : ∀ᶠ z in 𝓝 a,
      (fun i => chartComplexGradient p U i z) = (z - a) ^ m • B z) :
    let proj := chartLeadingPlaneProjection g p (U a) (B a)
    let F : ℂ → ℂ := fun z => proj (extChartAt 𝓘(ℝ, E) p (U z))
    ∃ T : ℂ → ℂ →L[ℝ] ℂ,
      (∀ z v : ℂ, T z v = proj ((chartModelBasis E).equivFunL.symm
        (fun i => (2 : ℝ) * (v * B z i).re))) ∧
      T a = ContinuousLinearMap.id ℝ ℂ ∧
      ∃ r : ℝ, 0 < r ∧ Metric.ball a r ⊆ s ∧
        (∀ z ∈ Metric.ball a r, U z ∈ (chartAt E p).source) ∧
        ContDiffOn ℝ 1 T (Metric.ball a r) ∧
        ContDiffOn ℝ 1 F (Metric.ball a r) ∧
        ∀ z ∈ Metric.ball a r,
          fderiv ℝ F z = (T z).comp
            ((z - a) ^ m • ContinuousLinearMap.id ℝ ℂ) := by
  let proj := chartLeadingPlaneProjection g p (U a) (B a)
  let X : ℂ → E := extChartAt 𝓘(ℝ, E) p ∘ U
  let F : ℂ → ℂ := fun z => proj (X z)
  let T : ℂ → ℂ →L[ℝ] ℂ := fun z => proj.comp (leadingRealDifferential (B z))
  have hnull := chartComplexGradient_leading_isotropic g hs hU hconformal ha hsrc
    hB.continuousAt hfactor
  have hTa : T a = ContinuousLinearMap.id ℝ ℂ :=
    leading_projection_normalization g hsrc hBne hnull
  have hA : ContDiffAt ℝ 1 (fun z => leadingRealVector (B z)) a :=
    (chartModelBasis E).equivFunL.symm.contDiff.contDiffAt.comp a
      (contDiffAt_pi.mpr (fun i =>
        Complex.reCLM.contDiff.contDiffAt.comp a (contDiffAt_pi.mp hB i)))
  have hC : ContDiffAt ℝ 1 (fun z => leadingNegImVector (B z)) a :=
    (chartModelBasis E).equivFunL.symm.contDiff.contDiffAt.comp a
      (contDiffAt_pi.mpr (fun i =>
        (Complex.imCLM.contDiff.contDiffAt.comp a (contDiffAt_pi.mp hB i)).neg))
  have hL : ContDiffAt ℝ 1 (fun z => leadingRealDifferential (B z)) a :=
    ((ContinuousLinearMap.smulRightL ℝ ℂ E Complex.reCLM).contDiff.contDiffAt.comp a
      (hA.const_smul (2 : ℝ))).add
        ((ContinuousLinearMap.smulRightL ℝ ℂ E Complex.imCLM).contDiff.contDiffAt.comp a
          (hC.const_smul (2 : ℝ)))
  have hT : ContDiffAt ℝ 1 T a :=
    (ContinuousLinearMap.compL ℝ ℂ E ℂ proj).contDiff.contDiffAt.comp a hL
  have hUa := (hU.contMDiffAt (hs.mem_nhds ha)).continuousAt
  have hchart : ∀ᶠ z in 𝓝 a, U z ∈ (chartAt E p).source :=
    hUa.preimage_mem_nhds ((chartAt E p).open_source.mem_nhds hsrc)
  have hall : ∀ᶠ z in 𝓝 a,
      z ∈ s ∧ U z ∈ (chartAt E p).source ∧
        (fun i => chartComplexGradient p U i z) = (z - a) ^ m • B z ∧
        ContDiffAt ℝ 1 T z := by
    filter_upwards [hs.mem_nhds ha, hchart, hfactor, hT.eventually (by norm_num)]
      with z hzs hzc hzf hzt
    exact ⟨hzs, hzc, hzf, hzt⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨T, ?_, hTa, r, hr, fun z hz => (hball hz).1,
    fun z hz => (hball hz).2.1, ?_, ?_, ?_⟩
  · intro z v
    change proj (leadingRealDifferential (B z) v) = _
    congr 1
    apply (chartModelBasis E).equivFunL.injective
    ext i
    simp [leadingRealDifferential, leadingRealVector, leadingNegImVector,
      smul_eq_mul, Complex.mul_re, chartModelBasis_repr_equivFunL_symm]
    ring
  · intro z hz
    exact (hball hz).2.2.2.contDiffWithinAt
  · intro z hz
    obtain ⟨hzs, hzc, _, _⟩ := hball hz
    have hX : ContDiffAt ℝ 1 X z :=
      ((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := 1) hzc).comp z
        (hU.contMDiffAt (hs.mem_nhds hzs))).contDiffAt
    exact (proj.contDiff.contDiffAt.comp z hX).contDiffWithinAt
  · intro z hz
    obtain ⟨hzs, hzc, hzf, _⟩ := hball hz
    have hUz := hU.contMDiffAt (hs.mem_nhds hzs)
    have hX : ContDiffAt ℝ 1 X z :=
      ((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := 1) hzc).comp z hUz).contDiffAt
    have hFderiv : fderiv ℝ F z = proj.comp (fderiv ℝ X z) :=
      (proj.hasFDerivAt.comp z (hX.differentiableAt (by norm_num)).hasFDerivAt).fderiv
    change fderiv ℝ F z = (T z).comp
      ((z - a) ^ m • ContinuousLinearMap.id ℝ ℂ)
    apply ContinuousLinearMap.ext
    intro v
    rw [hFderiv, ContinuousLinearMap.comp_apply]
    have hXD : fderiv ℝ X z =
        leadingRealDifferential (fun i => chartComplexGradient p U i z) :=
      chart_fderiv_eq_leadingRealDifferential hUz hzc
    rw [hXD, hzf, leadingRealDifferential_smul]
    rfl


/-- The literal leading lift and the same unit normal give the exact center
Gram form. In the real and imaginary directions, its slope dependence is
`κ I + p pᵀ` for one positive scalar from the original chart metric. -/
theorem chartLeadingPlaneProjection_lift_normal_gram
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {p x : M}
    (hsrc : x ∈ (chartAt E p).source)
    {b : Fin (Module.finrank ℝ E) → ℂ} (hb : b ≠ 0)
    (hnull : (∑ i, ∑ j, (chartGramMatrix g p x i j : ℂ) * b i * b j) = 0)
    {N : E} (hN : chartLeadingPlaneProjection g p x b N = 0)
    (hunit : chartGramBilin g p x N N = 1) :
    let Q := chartGramBilin g p x
    let lift : ℂ → E := fun w => (chartModelBasis E).equivFunL.symm
      (fun i => (2 : ℝ) * (w * b i).re)
    ∃ κ : ℝ, 0 < κ ∧ ∀ (v w : ℂ) (s t : ℝ),
      Q (lift v + s • N) (lift w + t • N) =
        κ * (v.re * w.re + v.im * w.im) + s * t := by
  classical
  let Q := chartGramBilin g p x
  let A := leadingRealVector b
  let C := leadingNegImVector b
  let lift : ℂ → E := fun w => (chartModelBasis E).equivFunL.symm
    (fun i => (2 : ℝ) * (w * b i).re)
  change ∃ κ : ℝ, 0 < κ ∧ ∀ (v w : ℂ) (s t : ℝ),
    Q (lift v + s • N) (lift w + t • N) =
      κ * (v.re * w.re + v.im * w.im) + s * t
  obtain ⟨hpos, heq, hAC, hCA⟩ := leading_directions_metric g hsrc hb hnull
  change 0 < Q A A at hpos
  change Q A A = Q C C at heq
  change Q A C = 0 at hAC
  change Q C A = 0 at hCA
  have hCC : Q C C = Q A A := heq.symm
  have hscale : (2 * Q A A)⁻¹ ≠ 0 :=
    inv_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hpos))
  have hproj : chartLeadingPlaneProjection g p x b N =
      ((2 * Q A A)⁻¹ : ℝ) • ((Q A N : ℂ) + Complex.I * (Q C N : ℂ)) := rfl
  rw [hproj] at hN
  have hre : (2 * Q A A)⁻¹ * Q A N = 0 := by
    simpa using congrArg Complex.re hN
  have him : (2 * Q A A)⁻¹ * Q C N = 0 := by
    simpa using congrArg Complex.im hN
  have hAN : Q A N = 0 := (mul_eq_zero.mp hre).resolve_left hscale
  have hCN : Q C N = 0 := (mul_eq_zero.mp him).resolve_left hscale
  have hNA : Q N A = 0 := (chartGramBilin_symm g p x N A).trans hAN
  have hNC : Q N C = 0 := (chartGramBilin_symm g p x N C).trans hCN
  have hNN : Q N N = 1 := hunit
  have hlift (w : ℂ) : lift w =
      w.re • ((2 : ℝ) • A) + w.im • ((2 : ℝ) • C) := by
    apply (chartModelBasis E).equivFunL.injective
    ext i
    simp [lift, A, C, leadingRealVector, leadingNegImVector,
      smul_eq_mul, Complex.mul_re, chartModelBasis_repr_equivFunL_symm]
    ring
  refine ⟨4 * Q A A, mul_pos (by norm_num) hpos, ?_⟩
  intro v w s t
  rw [hlift v, hlift w]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul,
    hCC, hAC, hCA, hAN, hCN, hNA, hNC, hNN]
  ring

end DifferentialGeometry.Geometry
