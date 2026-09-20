import DifferentialGeometry.Geometry.Operator.Gradient.PartitionOfUnity
import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensity
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import DifferentialGeometry.Analysis.Integration.Measure.Gradient
import DifferentialGeometry.Analysis.Integration.Lp.Lipschitz
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Integral.Prod
import DifferentialGeometry.Analysis.Sobolev.Manifold.Lipschitz
import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensityContinuity
import DifferentialGeometry.Geometry.Operator.Gradient.Coordinates

noncomputable section
open Bundle Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal
namespace DifferentialGeometry.Analysis.Parabolic
private theorem fderiv_tensor_mul
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {ψ : ℝ → ℝ} {f : V → ℝ} {t : ℝ} {x : V}
    (hψ : DifferentiableAt ℝ ψ t) (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun z : ℝ × V => ψ z.1 * f z.2) (t, x) (1, 0) = deriv ψ t * f x ∧
      ∀ v : V, fderiv ℝ (fun z : ℝ × V => ψ z.1 * f z.2) (t, x) (0, v) =
        ψ t * fderiv ℝ f x v := by
  have hψp : DifferentiableAt ℝ (fun z : ℝ × V => ψ z.1) (t, x) :=
    hψ.comp (t, x) differentiableAt_fst
  have hfp : DifferentiableAt ℝ (fun z : ℝ × V => f z.2) (t, x) :=
    hf.comp (t, x) differentiableAt_snd
  have hd (s : ℝ) (v : V) :
      fderiv ℝ (fun z : ℝ × V => ψ z.1 * f z.2) (t, x) (s, v) =
        ψ t * fderiv ℝ f x v + f x * fderiv ℝ ψ t s := by
    rw [fderiv_fun_mul hψp hfp]
    change ψ t * (fderiv ℝ (f ∘ Prod.snd) (t, x)) (s, v) +
      f x * (fderiv ℝ (ψ ∘ Prod.fst) (t, x)) (s, v) = _
    rw [fderiv_comp (t, x) hf differentiableAt_snd,
      fderiv_comp (t, x) hψ differentiableAt_fst, fderiv_snd, fderiv_fst]
    rfl
  constructor
  · rw [hd, map_zero, mul_zero, zero_add, fderiv_apply_one_eq_deriv]
    exact mul_comm _ _
  · intro v
    rw [hd, map_zero, mul_zero, add_zero]

private theorem integrable_tensor_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [ν.IsAddHaarMeasure]
    {J : Set ℝ} {Ω : Set E} (hJ : IsOpen J) (hΩ : IsOpen Ω)
    {b : ℝ × E → ℝ} (hb : LocallyIntegrableOn b (J ×ˢ Ω) (volume.prod ν))
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ J)
    {f : E → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f)
    (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ Ω)
    (v : ℝ × E) :
    Integrable (fun z => b z * fderiv ℝ (fun z : ℝ × E => ψ z.1 * f z.2) z v)
      (volume.prod ν) ∧
    (fun z : ℝ × E => b z * fderiv ℝ (fun z : ℝ × E => ψ z.1 * f z.2) z v)
      =ᵐ[volume.prod ν] (fun z : ℝ × E => b z *
      (ψ z.1 * fderiv ℝ f z.2 v.2 + deriv ψ z.1 * v.1 * f z.2)) := by
  let φ := fun z : ℝ × E => ψ z.1 * f z.2
  have hφs : tsupport φ ⊆ tsupport ψ ×ˢ tsupport f := by
    apply closure_minimal
    · intro z hz
      exact ⟨subset_tsupport _ (left_ne_zero_of_mul hz),
        subset_tsupport _ (right_ne_zero_of_mul hz)⟩
    · exact (isClosed_tsupport ψ).prod (isClosed_tsupport f)
  have hφc : HasCompactSupport φ :=
    (hψc.prod hfc).of_isClosed_subset (isClosed_tsupport φ) hφs
  have hm : ContDiff ℝ 1 (fun z : ℝ × ℝ => z.1 * z.2) := contDiff_fst.mul contDiff_snd
  have hφ : LocallyLipschitz φ := hm.locallyLipschitz.comp
    ((hψ.comp contDiff_fst).locallyLipschitz.prodMk
      (hf.locallyLipschitz.comp (contDiff_snd : ContDiff ℝ 1 (Prod.snd : ℝ × E → E)).locallyLipschitz))
  have hi := hb.integrable_mul_fderiv_of_hasCompactSupport (hJ.prod hΩ)
    hφ.locallyLipschitzOn hφc (hφs.trans (prod_mono hψs hfs)) v
  refine ⟨hi, ?_⟩
  filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := volume) (ν := ν)).ae hf.ae_differentiableAt] with z hdf
  have hd := fderiv_tensor_mul (hψ.differentiable (by norm_num) z.1) hdf
  have hv : v = v.1 • (1, (0 : E)) + (0, v.2) := by simp
  rw [hv, map_add, map_smul]
  rw [hd.1, hd.2]
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_zero,
    smul_eq_mul, mul_one, add_zero, zero_add]
  ring

private theorem integral_tensor_derivative_time
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [ν.IsAddHaarMeasure]
    {J : Set ℝ} {Ω : Set E} (hJ : IsOpen J) (hΩ : IsOpen Ω)
    {b : ℝ × E → ℝ} (hb : LocallyIntegrableOn b (J ×ˢ Ω) (volume.prod ν))
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ J)
    {f : E → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f)
    (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ Ω) :
    Integrable (fun t => deriv ψ t * ∫ y, b (t, y) * f y ∂ν) volume ∧
    (∫ z, b z * fderiv ℝ (fun z : ℝ × E => ψ z.1 * f z.2) z (1, 0) ∂volume.prod ν) =
      ∫ t, deriv ψ t * ∫ y, b (t, y) * f y ∂ν := by
  obtain ⟨hi, heq⟩ := integrable_tensor_derivative ν hJ hΩ hb hψ hψc hψs hf hfc hfs (1, 0)
  simp only [map_zero, mul_zero, mul_one, zero_add] at heq
  have hi' := hi.congr heq
  have hpoint (t : ℝ) :
      (∫ y, b (t, y) * (deriv ψ t * f y) ∂ν) =
        deriv ψ t * ∫ y, b (t, y) * f y ∂ν := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    ring
  constructor
  · simpa only [hpoint] using hi'.integral_prod_left
  · rw [integral_congr_ae heq, integral_prod _ hi']
    exact integral_congr_ae (.of_forall hpoint)

private theorem sum_integral_tensor_derivative_space
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Fintype ι]
    (ν : Measure E) [ν.IsAddHaarMeasure]
    {J : Set ℝ} {Ω : Set E} (hJ : IsOpen J) (hΩ : IsOpen Ω)
    {b : ι → ℝ × E → ℝ}
    (hb : ∀ i, LocallyIntegrableOn (b i) (J ×ˢ Ω) (volume.prod ν))
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ J)
    {f : E → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f)
    (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ Ω) (v : ι → E) :
    Integrable (fun t => ψ t * ∫ y, ∑ i, b i (t, y) * fderiv ℝ f y (v i) ∂ν) volume ∧
    (∑ i, ∫ z, b i z * fderiv ℝ (fun z : ℝ × E => ψ z.1 * f z.2) z (0, v i) ∂volume.prod ν) =
      ∫ t, ψ t * ∫ y, ∑ i, b i (t, y) * fderiv ℝ f y (v i) ∂ν := by
  classical
  have hi (i) := integrable_tensor_derivative ν hJ hΩ (hb i) hψ hψc hψs hf hfc hfs (0, v i)
  have heq (i) : (fun z => b i z * fderiv ℝ (fun z : ℝ × E => ψ z.1 * f z.2) z (0, v i))
      =ᵐ[volume.prod ν] (fun z => ψ z.1 * (b i z * fderiv ℝ f z.2 (v i))) := by
    filter_upwards [(hi i).2] with z hz
    rw [hz]
    simp only [mul_zero, zero_mul, add_zero]
    ring
  have hi' (i) := (hi i).1.congr (heq i)
  have heqs : (fun z => ∑ i, b i z * fderiv ℝ (fun z : ℝ × E => ψ z.1 * f z.2) z (0, v i))
      =ᵐ[volume.prod ν] (fun z => ψ z.1 * ∑ i, b i z * fderiv ℝ f z.2 (v i)) := by
    filter_upwards [ae_all_iff.mpr heq] with z hz
    simp only [← Finset.mul_sum, hz]
  have his : Integrable (fun z : ℝ × E => ψ z.1 * ∑ i, b i z * fderiv ℝ f z.2 (v i))
      (volume.prod ν) := by
    simpa only [Finset.mul_sum] using integrable_finsetSum Finset.univ (fun i _ => hi' i)
  have hpoint (t : ℝ) :
      (∫ y, ψ t * ∑ i, b i (t, y) * fderiv ℝ f y (v i) ∂ν) =
        ψ t * ∫ y, ∑ i, b i (t, y) * fderiv ℝ f y (v i) ∂ν := integral_const_mul _ _
  constructor
  · simpa only [hpoint] using his.integral_prod_left
  · rw [← integral_finsetSum _ (fun i _ => (hi i).1), integral_congr_ae heqs, integral_prod _ his]
    exact integral_congr_ae (.of_forall hpoint)

end DifferentialGeometry.Analysis.Parabolic

namespace DifferentialGeometry.Analysis.Parabolic
open Geometry.Operator Tensor.Coordinates Integral.DivergenceTheorem Integral.Measure
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private theorem integral_inner_gradFun_eq_chart_full
    (g : SmoothRiemannianMetric I M) (α : M) (u h : M → ℝ)
    (hu : LocallyLipschitzOn (extChartAt I α).target (scalarOnE (I := I) α u))
    (hc : HasCompactSupport h) (hs : tsupport h ⊆ (chartAt H α).source) :
    (∫ x, g.inner x (gradFun g u x) (gradFun g h x)
      ∂riemannianVolumeMeasure (I := I) (M := M) g) =
    ∫ y, ∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      (chartInvGramOnE g α ij.1 ij.2 y * chartDensityOnE g α y) *
        lineDeriv ℝ (scalarOnE (I := I) α u) y (chartModelBasis E ij.2) *
        fderiv ℝ (chartPullZero (I := I) α h) y (chartModelBasis E ij.1)
      ∂modelHaar := by
  rw [integral_inner_gradFun_eq_integral_chartDensity g α u h hu hc hs]
  have hzero (y : E) (hy : y ∉ (extChartAt I α).target) :
      fderiv ℝ (chartPullZero (I := I) α h) y = 0 :=
    fderiv_of_notMem_tsupport ℝ (fun hy' => hy (tsupport_chartPullZero_subset_target α hc hs hy'))
  calc
    _ = ∫ y in (extChartAt I α).target,
        ∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          (chartInvGramOnE g α ij.1 ij.2 y * chartDensityOnE g α y) *
            lineDeriv ℝ (scalarOnE (I := I) α u) y (chartModelBasis E ij.2) *
            fderiv ℝ (chartPullZero (I := I) α h) y (chartModelBasis E ij.1)
          ∂modelHaar := by
      apply setIntegral_congr_fun (isOpen_extChartAt_target (I := I) α).measurableSet
      intro y _
      dsimp only
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y hy => by simp only [hzero y hy, zero_apply, mul_zero, Finset.sum_const_zero])

private theorem integral_mul_eq_chart_full
    (g : SmoothRiemannianMetric I M) (α : M) (u h : C(M, ℝ))
    (hc : HasCompactSupport (h : M → ℝ)) (hs : tsupport (h : M → ℝ) ⊆ (chartAt H α).source) :
    (∫ x, u x * h x ∂riemannianVolumeMeasure (I := I) (M := M) g) =
    ∫ y, chartDensityOnE g α y * scalarOnE (I := I) α u y *
      chartPullZero (I := I) α h y ∂modelHaar := by
  have hi := integral_riemannianVolumeMeasure_eq_chartDensity_of_tsupport_subset g α
    (f := fun x => u x * h x) hc.mul_left (tsupport_mul_subset_right.trans hs)
    (u.continuous.mul h.continuous).aestronglyMeasurable
  calc
    _ = ∫ y in (extChartAt I α).target,
        chartDensity g α ((extChartAt I α).symm y) *
          (u ((extChartAt I α).symm y) * h ((extChartAt I α).symm y)) ∂modelHaar := hi
    _ = ∫ y in (extChartAt I α).target,
        chartDensityOnE g α y * scalarOnE (I := I) α u y *
          chartPullZero (I := I) α h y ∂modelHaar := by
      apply setIntegral_congr_fun (isOpen_extChartAt_target (I := I) α).measurableSet
      intro y hy
      dsimp only
      rw [chartPullZero_mem α h hy]
      change chartDensityOnE g α y * (u ((extChartAt I α).symm y) * h ((extChartAt I α).symm y)) = _
      simp only [scalarOnE_def]
      ring
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y hy => by simp only [chartPullZero_nmem α h hy, mul_zero])

private theorem tensor_weak_le_in_chart
    {J : Set ℝ} (hJ : IsOpen J) (g : ℝ → SmoothRiemannianMetric I M)
    (α : M) (u : ℝ → C(M, ℝ))
    (hu : LocallyLipschitzOn (J ×ˢ (extChartAt I α).target)
      (fun z : ℝ × E => u z.1 ((extChartAt I α).symm z.2)))
    (hρ : ContinuousOn (fun z : ℝ × E => chartDensityOnE (g z.1) α z.2)
      (J ×ˢ (extChartAt I α).target))
    (hA : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (fun z : ℝ × E => chartInvGramOnE (g z.1) α i j z.2)
        (J ×ˢ (extChartAt I α).target))
    (hweak : ∀ φ : ℝ × E → ℝ,
      LocallyLipschitzOn (J ×ˢ (extChartAt I α).target) φ → HasCompactSupport φ →
      tsupport φ ⊆ J ×ˢ (extChartAt I α).target → (∀ z, 0 ≤ φ z) →
      (∑ i, ∑ j, ∫ z, (chartInvGramOnE (g z.1) α i j z.2 * chartDensityOnE (g z.1) α z.2) *
        lineDeriv ℝ (fun w : ℝ × E => u w.1 ((extChartAt I α).symm w.2)) z (0, chartModelBasis E j) *
        fderiv ℝ φ z (0, chartModelBasis E i) ∂volume.prod (modelHaar (E := E))) ≤
        ∫ z, chartDensityOnE (g z.1) α z.2 * u z.1 ((extChartAt I α).symm z.2) *
          fderiv ℝ φ z (1, 0) ∂volume.prod (modelHaar (E := E)))
    (h : C(M, ℝ)) (hc : HasCompactSupport (h : M → ℝ))
    (hs : tsupport (h : M → ℝ) ⊆ (chartAt H α).source) (h0 : ∀ x, 0 ≤ h x)
    {C : ℝ≥0} (hLip : LipschitzWith C (chartPullZero (I := I) α h))
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ J) (hψ0 : ∀ t, 0 ≤ ψ t) :
    Integrable (fun t => ψ t * ∫ x, (g t).inner x (gradFun (g t) (u t) x) (gradFun (g t) h x)
      ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) volume ∧
    Integrable (fun t => deriv ψ t * ∫ x, u t x * h x
      ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) volume ∧
    (∫ t, ψ t * ∫ x, (g t).inner x (gradFun (g t) (u t) x) (gradFun (g t) h x)
      ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) ≤
      ∫ t, deriv ψ t * ∫ x, u t x * h x
        ∂riemannianVolumeMeasure (I := I) (M := M) (g t) := by
  classical
  let Ω := (extChartAt I α).target
  let U : ℝ × E → ℝ := fun z => u z.1 ((extChartAt I α).symm z.2)
  let ρ : ℝ × E → ℝ := fun z => chartDensityOnE (g z.1) α z.2
  let b : (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) → ℝ × E → ℝ :=
    fun ij z => (chartInvGramOnE (g z.1) α ij.1 ij.2 z.2 * ρ z) *
      lineDeriv ℝ U z (0, chartModelBasis E ij.2)
  let f := chartPullZero (I := I) α h
  let φ : ℝ × E → ℝ := fun z => ψ z.1 * f z.2
  have hΩ : IsOpen Ω := isOpen_extChartAt_target (I := I) α
  have hdom : IsOpen (J ×ˢ Ω) := hJ.prod hΩ
  have hfc : HasCompactSupport f := hasCompactSupport_chartPullZero α hc hs
  have hfs : tsupport f ⊆ Ω := tsupport_chartPullZero_subset_target α hc hs
  have hφs : tsupport φ ⊆ tsupport ψ ×ˢ tsupport f := by
    apply closure_minimal
    · intro z hz
      exact ⟨subset_tsupport _ (left_ne_zero_of_mul hz),
        subset_tsupport _ (right_ne_zero_of_mul hz)⟩
    · exact (isClosed_tsupport ψ).prod (isClosed_tsupport f)
  have hφc : HasCompactSupport φ :=
    (hψc.prod hfc).of_isClosed_subset (isClosed_tsupport φ) hφs
  have hm : ContDiff ℝ 1 (fun z : ℝ × ℝ => z.1 * z.2) := contDiff_fst.mul contDiff_snd
  have hφ : LocallyLipschitz φ := hm.locallyLipschitz.comp
    ((hψ.comp contDiff_fst).locallyLipschitz.prodMk
      (hLip.locallyLipschitz.comp (contDiff_snd : ContDiff ℝ 1 (Prod.snd : ℝ × E → E)).locallyLipschitz))
  have hf0 (y : E) : 0 ≤ f y := by
    by_cases hy : y ∈ Ω
    · change 0 ≤ chartPullZero (I := I) α h y
      rw [chartPullZero_mem α h hy]
      exact h0 ((extChartAt I α).symm y)
    · rw [show f y = 0 from chartPullZero_nmem α h hy]
  have hi := hweak φ hφ.locallyLipschitzOn hφc
    (hφs.trans (prod_mono hψs hfs)) (fun z => mul_nonneg (hψ0 z.1) (hf0 z.2))
  have hb (ij) : LocallyIntegrableOn (b ij) (J ×ˢ Ω) (volume.prod (modelHaar (E := E))) := by
    have hd : LocallyIntegrableOn
        (fun z => lineDeriv ℝ U z (0, chartModelBasis E ij.2)) (J ×ˢ Ω)
        (volume.prod (modelHaar (E := E))) := by
      apply (locallyIntegrableOn_iff hdom.isLocallyClosed).mpr
      intro K hKΩ hK
      exact memLp_one_iff_integrable.mp
        (hu.memLp_lineDeriv_of_isCompact hdom hK hKΩ hK.measure_ne_top (0, chartModelBasis E ij.2) 1)
    exact hd.continuousOn_mul ((hA ij.1 ij.2).mul hρ) hdom.isLocallyClosed
  have hb0 : LocallyIntegrableOn (fun z => ρ z * U z) (J ×ˢ Ω)
      (volume.prod (modelHaar (E := E))) :=
    (hρ.mul hu.continuousOn).locallyIntegrableOn hdom.measurableSet
  have hsp := sum_integral_tensor_derivative_space (modelHaar (E := E)) hJ hΩ hb
    hψ hψc hψs hLip hfc hfs (fun ij => chartModelBasis E ij.1)
  have htm := integral_tensor_derivative_time (modelHaar (E := E)) hJ hΩ hb0
    hψ hψc hψs hLip hfc hfs
  have hflux (t : ℝ) :
      (ψ t * ∫ y, ∑ ij, b ij (t, y) * fderiv ℝ f y (chartModelBasis E ij.1) ∂modelHaar) =
        ψ t * ∫ x, (g t).inner x (gradFun (g t) (u t) x) (gradFun (g t) h x)
          ∂riemannianVolumeMeasure (I := I) (M := M) (g t) := by
    by_cases ht : t ∈ J
    · have hus : LocallyLipschitzOn Ω (scalarOnE (I := I) α (u t)) := by
        apply locallyLipschitzOn_iff_restrict.mpr
        have hmap : LipschitzWith 1 (fun x : Ω => (⟨(t, x.1), ht, x.2⟩ : J ×ˢ Ω)) := by
          simpa only [one_mul, Function.comp_apply] using
            ((LipschitzWith.prodMk_left t).comp (LipschitzWith.subtype_val Ω)).subtype_mk
              (fun x => ⟨ht, x.2⟩)
        exact hu.restrict.comp hmap.locallyLipschitz
      rw [integral_inner_gradFun_eq_chart_full (g t) α (u t) h hus hc hs]
      congr 1
      apply integral_congr_ae
      filter_upwards with y
      apply Finset.sum_congr rfl
      intro ij _
      dsimp only [b, ρ, f]
      have hline : lineDeriv ℝ U (t, y) (0, chartModelBasis E ij.2) =
          lineDeriv ℝ (scalarOnE (I := I) α (u t)) y (chartModelBasis E ij.2) := by
        simp only [lineDeriv, Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, U, scalarOnE_def]
      rw [hline]
    · have hz : ψ t = 0 := image_eq_zero_of_notMem_tsupport (fun ht' => ht (hψs ht'))
      simp only [hz, zero_mul]
  have hmass (t : ℝ) :
      (deriv ψ t * ∫ y, (ρ (t, y) * U (t, y)) * f y ∂modelHaar) =
        deriv ψ t * ∫ x, u t x * h x ∂riemannianVolumeMeasure (I := I) (M := M) (g t) := by
    rw [integral_mul_eq_chart_full (g t) α (u t) h hc hs]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · exact hsp.1.congr (.of_forall hflux)
  · exact htm.1.congr (.of_forall hmass)
  · have heqsp := hsp.2.trans (integral_congr_ae (.of_forall hflux))
    have heqtm := htm.2.trans (integral_congr_ae (.of_forall hmass))
    rw [← heqsp, ← heqtm]
    simpa only [Fintype.sum_prod_type] using hi

end DifferentialGeometry.Analysis.Parabolic

namespace DifferentialGeometry.Analysis.Parabolic
open Integral.DivergenceTheorem Sobolev.Chart
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
private theorem exists_lipschitzWith_chartPullZero_compact_mul
    (g : SmoothRiemannianMetric I M) (α : M) {a u : M → ℝ} {L : ℝ≥0}
    (ha : ContMDiff I 𝓘(ℝ) ∞ a)
    (hc : HasCompactSupport (fun x => a x * u x))
    (hs : tsupport (fun x => a x * u x) ⊆ (chartAt H α).source)
    (hu : ∀ x y, edist (u x) (u y) ≤ L * riemannianEDistOf g x y) :
    ∃ C : ℝ≥0, LipschitzWith C (chartPullZero (I := I) α (fun x => a x * u x)) := by
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨K, hK, hinside, hKs⟩ := exists_compact_between hc (chartAt H α).open_source hs
  obtain ⟨η, hη1, hη0, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior (n := (⊤ : ℕ∞))
    I (isClosed_tsupport (fun x => a x * u x)) hinside
  have hηs : tsupport (η : M → ℝ) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hxK
    exact hx (hη0 x hxK)
  have hηc : HasCompactSupport (η : M → ℝ) :=
    hK.of_isClosed_subset (isClosed_tsupport _) hηs
  have heq : (fun x => (η x * a x) * u x) = (fun x => a x * u x) := by
    funext x
    by_cases hx : a x * u x = 0
    · rw [mul_assoc, hx, mul_zero]
    · rw [hη1.self_of_nhdsSet x (subset_tsupport _ hx), one_mul]
  obtain ⟨C, hC⟩ := exists_lipschitzWith_chartPullZero_mul g α (η.contMDiff.mul ha)
    hηc.mul_right (tsupport_mul_subset_left.trans (hηs.trans hKs)) hu
  exact ⟨C, heq ▸ hC⟩
end DifferentialGeometry.Analysis.Parabolic

namespace DifferentialGeometry.Analysis.Parabolic
open Tensor.Coordinates Integral.Measure Geometry.Operator
private theorem matrix_inv_continuousOn {X ι : Type*} [TopologicalSpace X]
    [Fintype ι] [DecidableEq ι] {A : X → Matrix ι ι ℝ} {s : Set X}
    (hA : ContinuousOn A s) (hdet : ∀ x ∈ s, (A x).det ≠ 0) :
    ContinuousOn (fun x => (A x)⁻¹) s := by
  have hd : ContinuousOn (fun x => (A x).det) s :=
    continuous_id.matrix_det.comp_continuousOn hA
  have ha : ContinuousOn (fun x => (A x).adjugate) s :=
    continuous_id.matrix_adjugate.comp_continuousOn hA
  intro x hx
  have h := ((hd x hx).inv₀ (hdet x hx)).smul (ha x hx)
  convert h using 1
  funext y
  ext i j
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Pi.smul_apply', Pi.inv_apply, Matrix.smul_apply]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
private theorem chart_coefficients_continuousOn
    {P : Type*} [TopologicalSpace P] (g : P → SmoothRiemannianMetric I M) {J : Set P}
    (α : M)
    (hg : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (fun p : P × M => chartGramMatrix (g p.1) α p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)) :
    ContinuousOn (fun z : P × E => chartDensityOnE (g z.1) α z.2)
      (J ×ˢ (extChartAt I α).target) ∧
    ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (fun z : P × E => chartInvGramOnE (g z.1) α i j z.2)
        (J ×ˢ (extChartAt I α).target) := by
  classical
  have hmap : ContinuousOn (fun z : P × E => (z.1, (extChartAt I α).symm z.2))
      (J ×ˢ (extChartAt I α).target) := continuousOn_fst.prodMk
        ((continuousOn_extChartAt_symm (I := I) α).comp continuousOn_snd (fun _ hz => hz.2))
  have hmaps : MapsTo (fun z : P × E => (z.1, (extChartAt I α).symm z.2))
      (J ×ˢ (extChartAt I α).target)
      (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
    fun _ hz => ⟨hz.1, extChartAt_symm_mem_trivializationAt_baseSet α hz.2⟩
  have hGram : ContinuousOn (fun p : P × M => chartGramMatrix (g p.1) α p.2)
      (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
    continuousOn_pi.mpr fun i => continuousOn_pi.mpr (hg i)
  have hne (z : P × M)
      (hz : z ∈ J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :
      (chartGramMatrix (g z.1) α z.2).det ≠ 0 :=
    ne_of_gt (chartGramMatrix_det_pos (g z.1) α hz.2)
  have hdensity := (chartDensity_family_continuousOn g α hg).comp hmap hmaps
  refine ⟨hdensity, ?_⟩
  have hinv := matrix_inv_continuousOn hGram hne
  intro i j
  have hentry : ContinuousOn (fun p : P × M =>
      (chartGramMatrix (g p.1) α p.2)⁻¹ i j)
      (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
    continuousOn_pi.mp (continuousOn_pi.mp hinv i) j
  change ContinuousOn (fun z : P × E =>
    (chartGramMatrix (g z.1) α ((extChartAt I α).symm z.2))⁻¹ i j) _
  have hh : ContinuousOn ((fun p : P × M =>
      (chartGramMatrix (g p.1) α p.2)⁻¹ i j) ∘
      (fun z : P × E => (z.1, (extChartAt I α).symm z.2)))
      (J ×ˢ (extChartAt I α).target) := hentry.comp hmap hmaps
  exact hh
end DifferentialGeometry.Analysis.Parabolic
namespace DifferentialGeometry.Analysis.Parabolic
open Geometry.Operator Tensor.Coordinates Integral.DivergenceTheorem Integral.Measure
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem integral_tensor_test_le_of_chart_weak_le
    {J : Set ℝ} (hJ : IsOpen J) (g : ℝ → SmoothRiemannianMetric I M)
    (u : ℝ → C(M, ℝ))
    (hu : ∀ α : M, LocallyLipschitzOn (J ×ˢ (extChartAt I α).target)
      (fun z : ℝ × E => u z.1 ((extChartAt I α).symm z.2)))
    (hgram : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn (fun p : ℝ × M => chartGramMatrix (g p.1) α p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (hweak : ∀ (α : M) (φ : ℝ × E → ℝ),
      LocallyLipschitzOn (J ×ˢ (extChartAt I α).target) φ → HasCompactSupport φ →
      tsupport φ ⊆ J ×ˢ (extChartAt I α).target → (∀ z, 0 ≤ φ z) →
      (∑ i, ∑ j, ∫ z, (chartInvGramOnE (g z.1) α i j z.2 * chartDensityOnE (g z.1) α z.2) *
        lineDeriv ℝ (fun w : ℝ × E => u w.1 ((extChartAt I α).symm w.2)) z (0, chartModelBasis E j) *
        fderiv ℝ φ z (0, chartModelBasis E i) ∂volume.prod (modelHaar (E := E))) ≤
        ∫ z, chartDensityOnE (g z.1) α z.2 * u z.1 ((extChartAt I α).symm z.2) *
          fderiv ℝ φ z (1, 0) ∂volume.prod (modelHaar (E := E)))
    (R : SmoothRiemannianMetric I M) (χ : C(M, ℝ))
    (hχc : HasCompactSupport (χ : M → ℝ)) (hχ0 : ∀ x, 0 ≤ χ x)
    {C : ℝ≥0} (hχ : ∀ x y, edist (χ x) (χ y) ≤ C * riemannianEDistOf R x y)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ J) (hψ0 : ∀ t, 0 ≤ ψ t) :
    Integrable (fun t => ψ t * ∫ x, (g t).inner x (gradFun (g t) (u t) x) (gradFun (g t) χ x)
      ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) volume ∧
    Integrable (fun t => deriv ψ t * ∫ x, u t x * χ x
      ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) volume ∧
    (∫ t, ψ t * ∫ x, (g t).inner x (gradFun (g t) (u t) x) (gradFun (g t) χ x)
      ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) ≤
      ∫ t, deriv ψ t * ∫ x, u t x * χ x
        ∂riemannianVolumeMeasure (I := I) (M := M) (g t) := by
  classical
  let ρ := chartAtlasPOU I M
  let S := ρ.toPartitionOfUnity.fintsupportOn (tsupport (χ : M → ℝ)) hχc
  let f : M → C(M, ℝ) := fun α =>
    ⟨fun x => ρ α x * χ x, (ρ α).contMDiff.continuous.mul χ.continuous⟩
  have hfc (α : M) : HasCompactSupport (f α : M → ℝ) := hχc.mul_left
  have hfs (α : M) : tsupport (f α : M → ℝ) ⊆ (chartAt H α).source :=
    tsupport_mul_subset_left.trans (chartAtlasPOU_isSubordinate I M α)
  have hf0 (α x : M) : 0 ≤ f α x := mul_nonneg (ρ.nonneg α x) (hχ0 x)
  have hfLip (α : M) : ∃ L : ℝ≥0, LipschitzWith L (chartPullZero (I := I) α (f α)) :=
    exists_lipschitzWith_chartPullZero_compact_mul R α (ρ α).contMDiff (hfc α) (hfs α) hχ
  have hcoeff (α : M) := chart_coefficients_continuousOn g α (hgram α)
  have hlocal (α : M) := tensor_weak_le_in_chart hJ g α u (hu α) (hcoeff α).1 (hcoeff α).2
    (hweak α) (f α) (hfc α) (hfs α) (hf0 α) (hfLip α).choose_spec hψ hψc hψs hψ0
  have hsum (x : M) : χ x = ∑ α ∈ S, f α x := by
    change χ x = ∑ α ∈ S, ρ.toPartitionOfUnity α x • χ x
    exact (ρ.toPartitionOfUnity.sum_fintsupportOn_smul hχc (subset_tsupport χ) (subset_univ _) x).symm
  have hslice (t : ℝ) (ht : t ∈ J) (α : M) :
      LocallyLipschitzOn (extChartAt I α).target (scalarOnE (I := I) α (u t)) := by
    apply locallyLipschitzOn_iff_restrict.mpr
    have hmap : LipschitzWith 1 (fun x : (extChartAt I α).target =>
        (⟨(t, x.1), ht, x.2⟩ : J ×ˢ (extChartAt I α).target)) := by
      simpa only [one_mul, Function.comp_apply] using
        ((LipschitzWith.prodMk_left t).comp (LipschitzWith.subtype_val (extChartAt I α).target)).subtype_mk
          (fun x => ⟨ht, x.2⟩)
    exact (hu α).restrict.comp hmap.locallyLipschitz
  have hfscalar (α : M) : LocallyLipschitzOn (extChartAt I α).target (scalarOnE (I := I) α (f α)) := by
    apply locallyLipschitzOn_iff_restrict.mpr
    have heq : ((extChartAt I α).target).domRestrict (scalarOnE (I := I) α (f α)) =
        ((extChartAt I α).target).domRestrict (chartPullZero (I := I) α (f α)) := by
      funext y
      exact (chartPullZero_mem α (f α) y.property).symm
    rw [heq]
    exact (hfLip α).choose_spec.locallyLipschitz.locallyLipschitzOn.restrict
  have hflux (t : ℝ) :
      (ψ t * ∫ x, (g t).inner x (gradFun (g t) (u t) x) (gradFun (g t) χ x)
        ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) =
      ∑ α ∈ S, ψ t * ∫ x, (g t).inner x (gradFun (g t) (u t) x) (gradFun (g t) (f α) x)
        ∂riemannianVolumeMeasure (I := I) (M := M) (g t) := by
    by_cases ht : t ∈ J
    · have hμ : riemannianVolumeMeasure (I := I) (M := M) (g t) ≪
          riemannianVolumeMeasure (I := I) (M := M) R := by
        rw [riemannianVolumeMeasure_eq_withDensity R (g t)]
        exact withDensity_absolutelyContinuous _ _
      have hd := hμ.ae_le (Sobolev.Chart.ae_mdiff_of_lip R hχ)
      have heq : (fun x => (g t).inner x (gradFun (g t) (u t) x) (gradFun (g t) χ x)) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) (g t)]
          (fun x => ∑ α ∈ S, (g t).inner x (gradFun (g t) (u t) x) (gradFun (g t) (f α) x)) := by
        filter_upwards [hd] with x hx
        have hg : gradFun (g t) χ x = ∑ α ∈ S, gradFun (g t) (f α) x :=
          gradientFun_eq_sum_fintsupportOn ρ hχc (g t) (subset_tsupport χ) (subset_univ _) hx
        rw [hg, map_sum]
      rw [integral_congr_ae heq, integral_finsetSum _ (fun α _ =>
        integrable_inner_gradFun_of_locallyLipschitzOn_chart (g t) α (u t) (f α)
          (hslice t ht α) (hfscalar α) (hfc α) (hfs α)), Finset.mul_sum]
    · have hz : ψ t = 0 := image_eq_zero_of_notMem_tsupport (fun ht' => ht (hψs ht'))
      simp only [hz, zero_mul, Finset.sum_const_zero]
  have hmass (t : ℝ) :
      (deriv ψ t * ∫ x, u t x * χ x ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) =
      ∑ α ∈ S, deriv ψ t * ∫ x, u t x * f α x
        ∂riemannianVolumeMeasure (I := I) (M := M) (g t) := by
    let _ := riemannianVolumeMeasure_isFiniteMeasureOnCompacts (g t)
    have hi (α : M) : Integrable (fun x => u t x * f α x)
        (riemannianVolumeMeasure (I := I) (M := M) (g t)) :=
      ((u t).continuous.mul (f α).continuous).integrable_of_hasCompactSupport (hfc α).mul_left
    have heq : (fun x => u t x * χ x) = fun x => ∑ α ∈ S, u t x * f α x := by
      funext x
      rw [← Finset.mul_sum, ← hsum x]
    rw [heq, integral_finsetSum _ (fun α _ => hi α), Finset.mul_sum]
  have hli := integrable_finsetSum S (fun α _ => (hlocal α).1)
  have hri := integrable_finsetSum S (fun α _ => (hlocal α).2.1)
  refine ⟨hli.congr (.of_forall fun t => (hflux t).symm),
    hri.congr (.of_forall fun t => (hmass t).symm), ?_⟩
  rw [integral_congr_ae (.of_forall hflux), integral_finsetSum _ (fun α _ => (hlocal α).1),
    integral_congr_ae (.of_forall hmass), integral_finsetSum _ (fun α _ => (hlocal α).2.1)]
  exact Finset.sum_le_sum fun α _ => (hlocal α).2.2

end DifferentialGeometry.Analysis.Parabolic
