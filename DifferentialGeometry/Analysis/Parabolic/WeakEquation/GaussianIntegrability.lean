import DifferentialGeometry.Analysis.Parabolic.WeakEquation.GaussianCoordinates
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.WeightedSpatialLp
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalCoefficients
import DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Formula

noncomputable section

open Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

local notation "V" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private theorem chartGradientBilin_fderiv_toEuclidean
    (g : SmoothRiemannianMetric I M) (α : M) (f : E → ℝ) (φ : V → ℝ) (y : E) :
    chartGradientBilin g α ((extChartAt I α).symm y)
      (fderiv ℝ f y) (fderiv ℝ (φ ∘ toEuclidean (E := E)) y) =
        ∑ i, ∑ j, invGramOnEuclid g α i j ((toEuclidean (E := E)) y) *
          fderiv ℝ (f ∘ (toEuclidean (E := E)).symm) ((toEuclidean (E := E)) y)
            (EuclideanSpace.single j 1) *
          fderiv ℝ φ ((toEuclidean (E := E)) y) (EuclideanSpace.single i 1) := by
  have hf (j : Fin (Module.finrank ℝ E)) :
      fderiv ℝ (f ∘ (toEuclidean (E := E)).symm) ((toEuclidean (E := E)) y)
          (EuclideanSpace.single j 1) = fderiv ℝ f y (chartModelBasis E j) := by
    rw [(toEuclidean (E := E)).symm.comp_right_fderiv]
    simp only [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, chartModelBasis_apply]
  have hφ (i : Fin (Module.finrank ℝ E)) :
      fderiv ℝ (φ ∘ toEuclidean (E := E)) y (chartModelBasis E i) =
        fderiv ℝ φ ((toEuclidean (E := E)) y) (EuclideanSpace.single i 1) := by
    rw [(toEuclidean (E := E)).comp_right_fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      chartModelBasis_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [chartGradientBilin_apply]
  simp only [hf, hφ, invGramOnEuclid, ContinuousLinearEquiv.symm_apply_apply]

private theorem integrable_toEuclidean_chartGaussianResidual
    (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
    (hg : MetricFamilySmoothOn (I := I) D g) (α : M)
    {a b : ℝ} (hreg : Icc a b ⊆ D.regular)
    {Ω : Set V} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩt : closure Ω ⊆ chartTargetEuclid (I := I) α)
    {f u : ℝ × E → ℝ}
    (hf : LocallyLipschitzOn (Icc a b ×ˢ closure Ω)
      (fun q : ℝ × V => f (q.1, (toEuclidean (E := E)).symm q.2)))
    (hu : LocallyLipschitzOn (Icc a b ×ˢ closure Ω)
      (fun q : ℝ × V => u (q.1, (toEuclidean (E := E)).symm q.2)))
    {φ : ℝ × V → ℝ} (hφ : ContDiff ℝ 1 φ) :
    Integrable (fun q : ℝ × V => densityOnEuclid (I := I) (g q.1) α q.2 *
      u (q.1, (toEuclidean (E := E)).symm q.2) *
      (fderiv ℝ φ q (1, 0) +
        ∑ i, ∑ j, invGramOnEuclid (I := I) (g q.1) α i j q.2 *
          fderiv ℝ (fun y => f (q.1, (toEuclidean (E := E)).symm y)) q.2
            (EuclideanSpace.single j 1) *
          fderiv ℝ φ q (0, EuclideanSpace.single i 1)))
      ((volume.restrict (Icc a b)).prod (volume.restrict Ω)) := by
  let G : MetricConnectionFamilyOn (I := I) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  have hρ : ContinuousOn (fun q : ℝ × V => densityOnEuclid (I := I) (g q.1) α q.2)
      (Icc a b ×ˢ closure Ω) :=
    (densityOnEuclid_family_continuousOn (G := G) hg hreg α).mono
      (prod_mono Subset.rfl hΩt)
  have hA (i j : Fin (Module.finrank ℝ E)) :
      ContinuousOn (fun q : ℝ × V => invGramOnEuclid (I := I) (g q.1) α i j q.2)
        (Icc a b ×ˢ closure Ω) :=
    (invGramOnEuclid_family_continuousOn (G := G) hg hreg α i j).mono
      (prod_mono Subset.rfl hΩt)
  have htime : Integrable
      (fun q : ℝ × V => densityOnEuclid (I := I) (g q.1) α q.2 *
        u (q.1, (toEuclidean (E := E)).symm q.2) * fderiv ℝ φ q (1, 0))
      ((volume.restrict (Icc a b)).prod (volume.restrict Ω)) := by
    have htest : ContinuousOn (fun q : ℝ × V => fderiv ℝ φ q (1, 0))
        (Icc a b ×ˢ closure Ω) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const |>.continuousOn
    have hc : ContinuousOn
        (fun q : ℝ × V => densityOnEuclid (I := I) (g q.1) α q.2 *
          u (q.1, (toEuclidean (E := E)).symm q.2) * fderiv ℝ φ q (1, 0))
        (Icc a b ×ˢ closure Ω) :=
      (hρ.mul hu.continuousOn).mul htest
    rw [Measure.prod_restrict]
    exact (hc.integrableOn_compact (isCompact_Icc.prod hΩc)).mono_set
      (prod_mono Subset.rfl subset_closure)
  have hterm (i j : Fin (Module.finrank ℝ E)) : Integrable
      (fun q : ℝ × V => densityOnEuclid (I := I) (g q.1) α q.2 *
        u (q.1, (toEuclidean (E := E)).symm q.2) *
        invGramOnEuclid (I := I) (g q.1) α i j q.2 *
        fderiv ℝ (fun y => f (q.1, (toEuclidean (E := E)).symm y)) q.2
          (EuclideanSpace.single j 1) *
        fderiv ℝ φ q (0, EuclideanSpace.single i 1))
      ((volume.restrict (Icc a b)).prod (volume.restrict Ω)) := by
    have hdf : MemLp
        (fun q : ℝ × V => fderiv ℝ (fun y => f (q.1, (toEuclidean (E := E)).symm y)) q.2
          (EuclideanSpace.single j 1)) 1
        ((volume.restrict (Icc a b)).prod (volume.restrict Ω)) :=
      memLp_spatial_fderiv_of_locallyLipschitzOn hΩ hΩc hf 1 j
    have htest : ContinuousOn
        (fun q : ℝ × V => fderiv ℝ φ q (0, EuclideanSpace.single i 1))
        (Icc a b ×ˢ closure Ω) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const |>.continuousOn
    have hc : ContinuousOn
        (fun q : ℝ × V => densityOnEuclid (I := I) (g q.1) α q.2 *
          u (q.1, (toEuclidean (E := E)).symm q.2) *
          invGramOnEuclid (I := I) (g q.1) α i j q.2 *
          fderiv ℝ φ q (0, EuclideanSpace.single i 1))
        (Icc a b ×ˢ closure Ω) :=
      ((hρ.mul hu.continuousOn).mul (hA i j)).mul htest
    have hcMem : MemLp
        (fun q : ℝ × V => densityOnEuclid (I := I) (g q.1) α q.2 *
          u (q.1, (toEuclidean (E := E)).symm q.2) *
          invGramOnEuclid (I := I) (g q.1) α i j q.2 *
          fderiv ℝ φ q (0, EuclideanSpace.single i 1)) ∞
        ((volume.restrict (Icc a b)).prod (volume.restrict Ω)) := by
      rw [Measure.prod_restrict]
      exact (hc.memLp_top_of_subset_isCompact (isCompact_Icc.prod hΩc)
        (measurableSet_Icc.prod hΩ.measurableSet) (prod_mono Subset.rfl subset_closure))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      memLp_one_iff_integrable.mp (hdf.fun_mul (r := 1) hcMem)
  have hgrad : Integrable
      (fun q : ℝ × V => densityOnEuclid (I := I) (g q.1) α q.2 *
        u (q.1, (toEuclidean (E := E)).symm q.2) *
        (∑ i, ∑ j, invGramOnEuclid (I := I) (g q.1) α i j q.2 *
          fderiv ℝ (fun y => f (q.1, (toEuclidean (E := E)).symm y)) q.2
            (EuclideanSpace.single j 1) *
          fderiv ℝ φ q (0, EuclideanSpace.single i 1)))
      ((volume.restrict (Icc a b)).prod (volume.restrict Ω)) := by
    have hs : Integrable
        (fun q : ℝ × V => ∑ i, ∑ j, densityOnEuclid (I := I) (g q.1) α q.2 *
          u (q.1, (toEuclidean (E := E)).symm q.2) *
          (invGramOnEuclid (I := I) (g q.1) α i j q.2 *
            fderiv ℝ (fun y => f (q.1, (toEuclidean (E := E)).symm y)) q.2
              (EuclideanSpace.single j 1) *
            fderiv ℝ φ q (0, EuclideanSpace.single i 1)))
        ((volume.restrict (Icc a b)).prod (volume.restrict Ω)) := by
      apply integrable_finsetSum Finset.univ
      intro i _
      apply integrable_finsetSum Finset.univ
      intro j _
      simpa only [mul_assoc] using hterm i j
    convert hs using 1
    funext q
    simp only [Finset.mul_sum, mul_assoc]
  convert htime.add hgrad using 1
  funext q
  simp only [Pi.add_apply, mul_add]

theorem integrable_chartGaussianResidual_of_locallyLipschitzOn
    (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
    (hg : MetricFamilySmoothOn (I := I) D g) (α : M)
    {a b : ℝ} (hreg : Icc a b ⊆ D.regular)
    {Ω : Set V} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩt : closure Ω ⊆ chartTargetEuclid (I := I) α)
    {f u : ℝ × E → ℝ}
    (hf : LocallyLipschitzOn (Icc a b ×ˢ closure Ω)
      (fun q : ℝ × V => f (q.1, (toEuclidean (E := E)).symm q.2)))
    (hu : LocallyLipschitzOn (Icc a b ×ˢ closure Ω)
      (fun q : ℝ × V => u (q.1, (toEuclidean (E := E)).symm q.2)))
    {φ : ℝ × V → ℝ} (hφ : ContDiff ℝ 1 φ) :
    Integrable (fun z : ℝ × E => chartDensity (I := I) (g z.1) α
        ((extChartAt I α).symm z.2) * u z *
      (deriv (fun t => φ (t, (toEuclidean (E := E)) z.2)) z.1 +
        chartGradientBilin (I := I) (g z.1) α ((extChartAt I α).symm z.2)
          (fderiv ℝ (fun y => f (z.1, y)) z.2)
          (fderiv ℝ (fun y => φ (z.1, (toEuclidean (E := E)) y)) z.2)))
      ((volume.restrict (Ioc a b)).prod
        ((modelHaar (E := E)).restrict ((toEuclidean (E := E)) ⁻¹' Ω))) := by
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
  let T : (ℝ × E) ≃L[ℝ] (ℝ × V) :=
    (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (toEuclidean (E := E))
  have hspace : MeasurePreserving (toEuclidean (E := E))
      (modelHaar (E := E)) volume :=
    ⟨(toEuclidean (E := E)).continuous.measurable, map_toEuclidean_modelHaar_eq_volume⟩
  have hspaceR := hspace.restrict_preimage_emb
    (toEuclidean (E := E)).toHomeomorph.measurableEmbedding Ω
  have hT : MeasurePreserving T
      ((volume.restrict (Icc a b)).prod
        ((modelHaar (E := E)).restrict ((toEuclidean (E := E)) ⁻¹' Ω)))
      ((volume.restrict (Icc a b)).prod (volume.restrict Ω)) :=
    (MeasurePreserving.id (volume.restrict (Icc a b))).prod hspaceR
  let R : ℝ × V → ℝ := fun q => densityOnEuclid (I := I) (g q.1) α q.2 *
    u (q.1, (toEuclidean (E := E)).symm q.2) *
    (fderiv ℝ φ q (1, 0) +
      ∑ i, ∑ j, invGramOnEuclid (I := I) (g q.1) α i j q.2 *
        fderiv ℝ (fun y => f (q.1, (toEuclidean (E := E)).symm y)) q.2
          (EuclideanSpace.single j 1) *
        fderiv ℝ φ q (0, EuclideanSpace.single i 1))
  have hRV : Integrable R ((volume.restrict (Icc a b)).prod (volume.restrict Ω)) :=
    integrable_toEuclidean_chartGaussianResidual D g hg α hreg hΩ hΩc hΩt hf hu hφ
  have hRT : Integrable (R ∘ T)
      ((volume.restrict (Icc a b)).prod
        ((modelHaar (E := E)).restrict ((toEuclidean (E := E)) ⁻¹' Ω))) :=
    (hT.integrable_comp_emb T.toHomeomorph.measurableEmbedding).mpr hRV
  apply hRT.congr
  apply Filter.Eventually.of_forall
  intro z
  have hd := hφ.differentiable (by simp) (z.1, (toEuclidean (E := E)) z.2)
  have ht : deriv (fun t => φ (t, (toEuclidean (E := E)) z.2)) z.1 =
      fderiv ℝ φ (z.1, (toEuclidean (E := E)) z.2) (1, 0) := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply] using
      (hd.hasFDerivAt.comp z.1
        (hasFDerivAt_prodMk_left z.1 ((toEuclidean (E := E)) z.2))).hasDerivAt.deriv
  have hs (i : Fin (Module.finrank ℝ E)) :
      fderiv ℝ (fun y : V => φ (z.1, y)) ((toEuclidean (E := E)) z.2)
          (EuclideanSpace.single i 1) =
        fderiv ℝ φ (z.1, (toEuclidean (E := E)) z.2)
          (0, EuclideanSpace.single i 1) := by
    have heq : fderiv ℝ (fun y : V => φ (z.1, y)) ((toEuclidean (E := E)) z.2) =
        (fderiv ℝ φ (z.1, (toEuclidean (E := E)) z.2)).comp
          (ContinuousLinearMap.inr ℝ ℝ V) :=
      (hd.hasFDerivAt.comp ((toEuclidean (E := E)) z.2)
        (hasFDerivAt_prodMk_right z.1 ((toEuclidean (E := E)) z.2))).fderiv
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] using
      congrArg (fun L : V →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) heq
  have hgrad := chartGradientBilin_fderiv_toEuclidean (g z.1) α
    (fun y => f (z.1, y)) (fun y : V => φ (z.1, y)) z.2
  simpa only [R, T, Function.comp_def, ContinuousLinearEquiv.prodCongr_apply,
    ContinuousLinearEquiv.refl_apply, densityOnEuclid,
    ContinuousLinearEquiv.symm_apply_apply, ht, hs] using
      (congrArg (fun r => chartDensity (g z.1) α ((extChartAt I α).symm z.2) * u z *
        (fderiv ℝ φ (z.1, (toEuclidean (E := E)) z.2) (1, 0) + r)) hgrad).symm

end DifferentialGeometry.Analysis.Parabolic
