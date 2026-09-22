import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjugateHeat.Viscosity
import DifferentialGeometry.Analysis.Parabolic.WeakEquationManifold
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedDensityHeatTest
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedLengthLipschitz

noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Integral.Measure Entropy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData (I := I) ancientTimeInterval)
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem ancient_perelmanDensity_weak_le_in_chart
    [MeasurableSpace (ℝ × E)] [BorelSpace (ℝ × E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p a : F.M)
    (μ : Measure (ℝ × E)) [μ.IsAddHaarMeasure]
    {φ : ℝ × E → ℝ} (hφ : LocallyLipschitzOn (Ioi 0 ×ˢ (extChartAt I a).target) φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioi 0 ×ˢ (extChartAt I a).target)
    (hφ0 : ∀ x, 0 ≤ φ x) :
    let u := fun w : ℝ × E => perelmanDensity (Module.finrank ℝ E) w.1
      (fun x => redLength F.S 0 p x w.1) ((extChartAt I a).symm w.2)
    let ρ := fun w : ℝ × E => chartDensityOnE (F.S.base.metric (-w.1)) a w.2
    let A := fun w : ℝ × E => fun i j : Fin (Module.finrank ℝ E) =>
      chartInvGramOnE (F.S.base.metric (-w.1)) a i j w.2;
    (∑ i, ∑ j, ∫ w, (A w i j * ρ w) * lineDeriv ℝ u w (0, chartModelBasis E j) *
      fderiv ℝ φ w (0, chartModelBasis E i) ∂μ) ≤
        ∫ w, ρ w * u w * fderiv ℝ φ w (1, 0) ∂μ := by
  have hu := (ancient_perelmanDensity_locallyLipschitzOn_in_chart F hF p a).mono
    (prod_mono Subset.rfl interior_subset)
  have hreg : ∀ t ∈ Ioi (0 : ℝ), 0 - t ∈ ancientTimeInterval.regular := by
    intro t ht
    simpa only [zero_sub, ancientTimeInterval_regular, mem_Iio] using neg_neg_of_pos ht
  have hs : tsupport φ ⊆ Ioi 0 ×ˢ interior (extChartAt I a).target := by
    simpa only [(isOpen_extChartAt_target (I := I) a).interior_eq] using hφs
  have hh := conjugate_heat_weak_le_in_chart_of_upper_tests F.S F.isSolution 0 isOpen_Ioi hreg a
    hu (fun z hz phi hphi hm => ?_) μ
    (hφ.mono (prod_mono Subset.rfl interior_subset)) hφc hs hφ0
  · simpa only [zero_sub] using hh
  · simpa only [zero_sub] using ancient_perelmanDensity_upper_test_in_chart F hF p a
      ⟨hz.1, interior_subset hz.2⟩ phi hphi hm

theorem ancient_perelmanDensity_tensor_weak_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (R : SmoothRiemannianMetric I F.M)
    (χ : C(F.M, ℝ)) (hχc : HasCompactSupport (χ : F.M → ℝ)) (hχ0 : ∀ x, 0 ≤ χ x)
    {C : ℝ≥0} (hχ : ∀ x y, edist (χ x) (χ y) ≤ C * riemannianEDistOf R x y)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ioi 0) (hψ0 : ∀ t, 0 ≤ ψ t) :
    let u := fun t => perelmanDensity (Module.finrank ℝ E) t
      (fun x => redLength F.S 0 p x t)
    let g := fun t => F.S.base.metric (-t)
    Integrable (fun t => ψ t * ∫ x, (g t).inner x (gradFun (g t) (u t) x) (gradFun (g t) χ x)
      ∂riemannianVolumeMeasure (I := I) (M := F.M) (g t)) volume ∧
    Integrable (fun t => deriv ψ t * ∫ x, u t x * χ x
      ∂riemannianVolumeMeasure (I := I) (M := F.M) (g t)) volume ∧
    (∫ t, ψ t * ∫ x, (g t).inner x (gradFun (g t) (u t) x) (gradFun (g t) χ x)
      ∂riemannianVolumeMeasure (I := I) (M := F.M) (g t)) ≤
      ∫ t, deriv ψ t * ∫ x, u t x * χ x
        ∂riemannianVolumeMeasure (I := I) (M := F.M) (g t) := by
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace F.M := ChartedSpace.locallyCompactSpace H F.M
  let _ : MeasurableSpace E := borel E
  let _ : BorelSpace E := ⟨rfl⟩
  have hc (t : ℝ) : Continuous
      (perelmanDensity (Module.finrank ℝ E) t (fun x => redLength F.S 0 p x t)) := by
    have hl : Continuous (fun x => redLength F.S 0 p x t) := by
      by_cases ht : 0 < t
      · exact continuous_redLength_of_ancient F hF p ht
      · simp only [redLength, Real.sqrt_eq_zero_of_nonpos (le_of_not_gt ht), mul_zero, div_zero]
        exact continuous_const
    exact continuous_const.mul (Real.continuous_exp.comp hl.neg)
  let u : ℝ → C(F.M, ℝ) := fun t =>
    ⟨perelmanDensity (Module.finrank ℝ E) t (fun x => redLength F.S 0 p x t), hc t⟩
  apply Analysis.Parabolic.integral_tensor_test_le_of_chart_weak_le isOpen_Ioi
    (fun t => F.S.base.metric (-t)) u
    (fun alpha => ancient_perelmanDensity_locallyLipschitzOn_in_chart F hF p alpha)
    (fun alpha i j => ?_)
    (fun alpha phi hphi hphic hphis hphi0 => ancient_perelmanDensity_weak_le_in_chart F hF p alpha
      (volume.prod (modelHaar (E := E))) hphi hphic hphis hphi0)
    R χ hχc hχ0 hχ hψ hψc hψs hψ0
  have hmap : ContinuousOn (fun z : ℝ × F.M => (-z.1, z.2))
      (Ioi 0 ×ˢ (trivializationAt E (TangentSpace I) alpha).baseSet) :=
    (continuous_fst.neg.prodMk continuous_snd).continuousOn
  have hmaps : MapsTo (fun z : ℝ × F.M => (-z.1, z.2))
      (Ioi 0 ×ˢ (trivializationAt E (TangentSpace I) alpha).baseSet)
      (ancientTimeInterval.carrier ×ˢ (trivializationAt E (TangentSpace I) alpha).baseSet) :=
    fun z hz => ⟨show -z.1 ≤ 0 from neg_nonpos.mpr hz.1.le, hz.2⟩
  have hgram := (F.isSolution.smoothMetric.chartGramMatrix_continuousOn_carrier alpha i j).comp hmap hmaps
  exact hgram

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
