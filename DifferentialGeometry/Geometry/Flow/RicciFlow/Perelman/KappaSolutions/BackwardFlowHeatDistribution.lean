import DifferentialGeometry.Analysis.Parabolic.WeakEquationManifold
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjugateHeat.Viscosity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjugateHeat.Distribution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardFlowHeatTest
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Potential.Lipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.JointRegularity

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set _root_.MeasureTheory
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Entropy
open scoped _root_.Manifold ContDiff _root_.Topology NNReal Matrix.Norms.Elementwise

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem backward_flow_limit_perelmanDensity_distribution_le_in_chart
    [MeasurableSpace (ℝ × E)] [BorelSpace (ℝ × E)]
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ n, 0 < tau n) (q : ℕ → F.M)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    [PreconnectedSpace L.M]
    {subseq : ℕ → ℕ}
    (Phi : PointedCGHMaps (backwardFlowSequence F tau htau q) (L.atTime 0) subseq)
    (R : SmoothRiemannianMetric I L.M) (G : ℕ → ℝ → SmoothRiemannianMetric I L.M)
    (hG : ∀ K : Set L.M, IsCompact K → ∀ᶠ n in atTop,
      ∃ U : Set L.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Phi.source n ∧
        ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
          (G n t).inner x v w = (((backwardFlowSequence F tau htau q).term (subseq n)).S.base.metric t).inner
            (Phi.map n x) (mfderiv I I (Phi.map n) x v) (mfderiv I I (Phi.map n) x w))
    (hmetric : ∀ a b : ℝ, Icc a b ⊆ Iic 0 → ∀ K : Set L.M, IsCompact K →
      ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc a b,
        metricDerivNormSupOn K r (G n t) (L.S.base.metric t) R < epsilon)
    {T : ℝ} (hT : 1 < T) (ell : C(L.M × Icc (1 : ℝ) T, ℝ))
    (hell : ∀ Q : Set (L.M × Icc (1 : ℝ) T), IsCompact Q → TendstoUniformlyOn
      (fun n w => redLength F.S 0 p (Phi.map n w.1) (tau (subseq n) * w.2)) ell atTop Q)
    (hLip : ∀ B : ℝ, 0 ≤ B → ∃ K : ℝ≥0,
      ∀ x ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint B,
      ∀ y ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint B,
      ∀ s t : Icc (1 : ℝ) T, |ell (x, s) - ell (y, t)| ≤
        (K : ℝ) * ((riemannianEDistOf (L.S.base.metric 0) x y).toReal + |(s : ℝ) - t|))
    (a : L.M) (μ : Measure (ℝ × E)) [μ.IsAddHaarMeasure]
    {φ : ℝ × E → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ioo 1 T ×ˢ (extChartAt I a).target) (hφ0 : ∀ x, 0 ≤ φ x) :
    let u := fun w : ℝ × E => perelmanDensity (Module.finrank ℝ E) w.1
      (fun x => ell (x, projIcc 1 T hT.le w.1)) ((extChartAt I a).symm w.2)
    let A := fun w : ℝ × E => fun i j : Fin (Module.finrank ℝ E) =>
      chartInvGramOnE (I := I) (L.S.base.metric (1 - w.1)) a i j w.2
    let beta := fun w : ℝ × E => fun k : Fin (Module.finrank ℝ E) =>
      ∑ i, ∑ j, A w i j * chartChristoffel (I := I) (L.S.base.metric (1 - w.1)) a i j k w.2;
    -(∑ i, ∑ j, ∫ w, u w * fderiv ℝ (fderiv ℝ (fun z => A z i j * φ z))
        w (0, chartModelBasis E j) (0, chartModelBasis E i) ∂μ) -
      (∫ w, u w * fderiv ℝ φ w (1, 0) ∂μ) -
      (∑ k, ∫ w, u w * fderiv ℝ (fun z => beta z k * φ z) w (0, chartModelBasis E k) ∂μ) +
      (∫ w, (metricScalarAt (L.S.base.metric (1 - w.1)) ((extChartAt I a).symm w.2) * u w) * φ w ∂μ) ≤ 0 := by
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace H L.M
  have hu := (locallyLipschitzOn_perelmanDensity_in_chart_of_spacetime_bounds
    (L.S.base.metric 0) L.basepoint hT.le ell hLip a (Module.finrank ℝ E)).mono
    (fun z (hz : z ∈ Ioo 1 T ×ˢ interior (extChartAt I a).target) =>
      ⟨zero_lt_one.trans hz.1.1, interior_subset hz.2⟩)
  have htests := fun z (hz : z ∈ Ioo 1 T ×ˢ interior (extChartAt I a).target) =>
    backward_flow_limit_perelmanDensity_upper_test_in_chart
      F hF p tau htau q L Phi R G hG hmetric hT ell hell a
      ⟨hz.1, interior_subset hz.2⟩
  have hs : tsupport φ ⊆ Ioo 1 T ×ˢ interior (extChartAt I a).target := by
    simpa only [(isOpen_extChartAt_target (I := I) a).interior_eq] using hφs
  exact conjugate_heat_distribution_le_in_chart_of_upper_tests L.S L.isSolution 1 isOpen_Ioo
    (fun t ht => sub_neg.mpr ht.1) a hu htests μ hφ hφc hs hφ0

theorem backward_flow_limit_perelmanDensity_weak_le_in_chart
    [MeasurableSpace (ℝ × E)] [BorelSpace (ℝ × E)]
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ n, 0 < tau n) (q : ℕ → F.M)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    [PreconnectedSpace L.M]
    {subseq : ℕ → ℕ}
    (Phi : PointedCGHMaps (backwardFlowSequence F tau htau q) (L.atTime 0) subseq)
    (R : SmoothRiemannianMetric I L.M) (G : ℕ → ℝ → SmoothRiemannianMetric I L.M)
    (hG : ∀ K : Set L.M, IsCompact K → ∀ᶠ n in atTop,
      ∃ U : Set L.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Phi.source n ∧
        ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
          (G n t).inner x v w = (((backwardFlowSequence F tau htau q).term (subseq n)).S.base.metric t).inner
            (Phi.map n x) (mfderiv I I (Phi.map n) x v) (mfderiv I I (Phi.map n) x w))
    (hmetric : ∀ a b : ℝ, Icc a b ⊆ Iic 0 → ∀ K : Set L.M, IsCompact K →
      ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc a b,
        metricDerivNormSupOn K r (G n t) (L.S.base.metric t) R < epsilon)
    {T : ℝ} (hT : 1 < T) (ell : C(L.M × Icc (1 : ℝ) T, ℝ))
    (hell : ∀ Q : Set (L.M × Icc (1 : ℝ) T), IsCompact Q → TendstoUniformlyOn
      (fun n w => redLength F.S 0 p (Phi.map n w.1) (tau (subseq n) * w.2)) ell atTop Q)
    (hLip : ∀ B : ℝ, 0 ≤ B → ∃ K : ℝ≥0,
      ∀ x ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint B,
      ∀ y ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint B,
      ∀ s t : Icc (1 : ℝ) T, |ell (x, s) - ell (y, t)| ≤
        (K : ℝ) * ((riemannianEDistOf (L.S.base.metric 0) x y).toReal + |(s : ℝ) - t|))
    (a : L.M) (μ : Measure (ℝ × E)) [μ.IsAddHaarMeasure]
    {φ : ℝ × E → ℝ} (hφ : LocallyLipschitzOn (Ioo 1 T ×ˢ (extChartAt I a).target) φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ioo 1 T ×ˢ (extChartAt I a).target) (hφ0 : ∀ x, 0 ≤ φ x) :
    let u := fun w : ℝ × E => perelmanDensity (Module.finrank ℝ E) w.1
      (fun x => ell (x, projIcc 1 T hT.le w.1)) ((extChartAt I a).symm w.2)
    let ρ := fun w : ℝ × E => chartDensityOnE (L.S.base.metric (1 - w.1)) a w.2
    let A := fun w : ℝ × E => fun i j : Fin (Module.finrank ℝ E) =>
      chartInvGramOnE (L.S.base.metric (1 - w.1)) a i j w.2;
    (∑ i, ∑ j, ∫ w, (A w i j * ρ w) * lineDeriv ℝ u w (0, chartModelBasis E j) *
      fderiv ℝ φ w (0, chartModelBasis E i) ∂μ) ≤
        ∫ w, ρ w * u w * fderiv ℝ φ w (1, 0) ∂μ := by
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace H L.M
  have hu := (locallyLipschitzOn_perelmanDensity_in_chart_of_spacetime_bounds
    (L.S.base.metric 0) L.basepoint hT.le ell hLip a (Module.finrank ℝ E)).mono
    (fun z (hz : z ∈ Ioo 1 T ×ˢ interior (extChartAt I a).target) =>
      ⟨zero_lt_one.trans hz.1.1, interior_subset hz.2⟩)
  have htests := fun z (hz : z ∈ Ioo 1 T ×ˢ interior (extChartAt I a).target) =>
    backward_flow_limit_perelmanDensity_upper_test_in_chart
      F hF p tau htau q L Phi R G hG hmetric hT ell hell a
      ⟨hz.1, interior_subset hz.2⟩
  have hs : tsupport φ ⊆ Ioo 1 T ×ˢ interior (extChartAt I a).target := by
    simpa only [(isOpen_extChartAt_target (I := I) a).interior_eq] using hφs
  exact conjugate_heat_weak_le_in_chart_of_upper_tests L.S L.isSolution 1 isOpen_Ioo
    (fun t ht => sub_neg.mpr ht.1) a hu htests μ (hφ.mono (prod_mono Subset.rfl interior_subset)) hφc hs hφ0

theorem backward_flow_limit_perelmanDensity_tensor_weak_le
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ n, 0 < tau n) (q : ℕ → F.M)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    [PreconnectedSpace L.M]
    {subseq : ℕ → ℕ}
    (Phi : PointedCGHMaps (backwardFlowSequence F tau htau q) (L.atTime 0) subseq)
    (R : SmoothRiemannianMetric I L.M) (G : ℕ → ℝ → SmoothRiemannianMetric I L.M)
    (hG : ∀ K : Set L.M, IsCompact K → ∀ᶠ n in atTop,
      ∃ U : Set L.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Phi.source n ∧
        ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
          (G n t).inner x v w = (((backwardFlowSequence F tau htau q).term (subseq n)).S.base.metric t).inner
            (Phi.map n x) (mfderiv I I (Phi.map n) x v) (mfderiv I I (Phi.map n) x w))
    (hmetric : ∀ a b : ℝ, Icc a b ⊆ Iic 0 → ∀ K : Set L.M, IsCompact K →
      ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc a b,
        metricDerivNormSupOn K r (G n t) (L.S.base.metric t) R < epsilon)
    {T : ℝ} (hT : 1 < T) (ell : C(L.M × Icc (1 : ℝ) T, ℝ))
    (hell : ∀ Q : Set (L.M × Icc (1 : ℝ) T), IsCompact Q → TendstoUniformlyOn
      (fun n w => redLength F.S 0 p (Phi.map n w.1) (tau (subseq n) * w.2)) ell atTop Q)
    (hLip : ∀ B : ℝ, 0 ≤ B → ∃ K : ℝ≥0,
      ∀ x ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint B,
      ∀ y ∈ riemannianClosedBallOf (L.S.base.metric 0) L.basepoint B,
      ∀ s t : Icc (1 : ℝ) T, |ell (x, s) - ell (y, t)| ≤
        (K : ℝ) * ((riemannianEDistOf (L.S.base.metric 0) x y).toReal + |(s : ℝ) - t|))
    (χ : C(L.M, ℝ)) (hχc : HasCompactSupport (χ : L.M → ℝ)) (hχ0 : ∀ x, 0 ≤ χ x)
    {C : ℝ≥0} (hχ : ∀ x y, edist (χ x) (χ y) ≤ C * riemannianEDistOf (L.S.base.metric 0) x y)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ioo 1 T) (hψ0 : ∀ t, 0 ≤ ψ t) :
    let u := fun t => perelmanDensity (Module.finrank ℝ E) t
      (fun x => ell (x, projIcc 1 T hT.le t))
    let g := fun t => L.S.base.metric (1 - t)
    Integrable (fun t => ψ t * ∫ x, (g t).inner x (gradFun (g t) (u t) x) (gradFun (g t) χ x)
      ∂riemannianVolumeMeasure (I := I) (M := L.M) (g t)) volume ∧
    Integrable (fun t => deriv ψ t * ∫ x, u t x * χ x
      ∂riemannianVolumeMeasure (I := I) (M := L.M) (g t)) volume ∧
    (∫ t, ψ t * ∫ x, (g t).inner x (gradFun (g t) (u t) x) (gradFun (g t) χ x)
      ∂riemannianVolumeMeasure (I := I) (M := L.M) (g t)) ≤
      ∫ t, deriv ψ t * ∫ x, u t x * χ x
        ∂riemannianVolumeMeasure (I := I) (M := L.M) (g t) := by
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace H L.M
  let _ : MeasurableSpace E := borel E
  let _ : BorelSpace E := ⟨rfl⟩
  let u : ℝ → C(L.M, ℝ) := fun t =>
    ⟨perelmanDensity (Module.finrank ℝ E) t (fun x => ell (x, projIcc 1 T hT.le t)),
      continuous_const.mul (Real.continuous_exp.comp
        (ell.continuous.comp (continuous_id.prodMk continuous_const)).neg)⟩
  apply Analysis.Parabolic.integral_tensor_test_le_of_chart_weak_le isOpen_Ioo
    (fun t => L.S.base.metric (1 - t)) u
    (fun α => (locallyLipschitzOn_perelmanDensity_in_chart_of_spacetime_bounds
      (L.S.base.metric 0) L.basepoint hT.le ell hLip α (Module.finrank ℝ E)).mono
      (fun _ hw => ⟨zero_lt_one.trans hw.1.1, hw.2⟩))
    (fun α i j => ?_)
    (fun α φ hφ hφc hφs hφ0 => backward_flow_limit_perelmanDensity_weak_le_in_chart
      F hF p tau htau q L Phi R G hG hmetric hT ell hell hLip α
      (volume.prod (modelHaar (E := E))) hφ hφc hφs hφ0)
    (L.S.base.metric 0) χ hχc hχ0 hχ hψ hψc hψs hψ0
  have hmap : ContinuousOn (fun z : ℝ × L.M => (1 - z.1, z.2))
      (Ioo 1 T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
    ((continuous_const.sub continuous_fst).prodMk continuous_snd).continuousOn
  have hmaps : MapsTo (fun z : ℝ × L.M => (1 - z.1, z.2))
      (Ioo 1 T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)
      (ancientTimeInterval.carrier ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
    fun z hz => ⟨show 1 - z.1 ≤ 0 from sub_nonpos.mpr hz.1.1.le, hz.2⟩
  have hc : ContinuousOn
      ((fun z : ℝ × L.M => chartGramMatrix (L.S.base.metric z.1) α z.2 i j) ∘
        (fun z : ℝ × L.M => (1 - z.1, z.2)))
      (Ioo 1 T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
    (L.isSolution.smoothMetric.chartGramMatrix_continuousOn_carrier α i j).comp hmap hmaps
  exact hc


end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
