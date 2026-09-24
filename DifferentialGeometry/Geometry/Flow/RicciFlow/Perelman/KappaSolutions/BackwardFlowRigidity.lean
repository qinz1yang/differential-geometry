import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardFlowDensityRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjugateHeat.WeakEquation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjugateHeat.RicciSoliton

noncomputable section
open Set Filter MeasureTheory
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Entropy
open scoped _root_.Manifold ContDiff _root_.Topology NNReal
universe u uH
variable {n : ℕ} {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H} [I.Boundaryless]
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem backward_flow_limit_perelmanDensity_contMDiffOn
    (F : PointedFlowData.{u, 0, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ n, 0 < tau n) (q : ℕ → F.M)
    (L : PointedFlowData.{u, 0, uH} (I := I) ancientTimeInterval)
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
    (hescape : Tendsto (tau ∘ subseq) atTop atTop)
    (hconv : ∀ t ∈ Icc (1 - T) (0 : ℝ),
      ∃ C : MetricConvergenceData (Phi.atTime
        (X := backwardFlowSequence F tau htau q) (L := L) t),
      ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData
        (Phi.atTime (X := backwardFlowSequence F tau htau q) (L := L) t) i)
    (hcomplete : ∀ t ∈ Icc (1 - T) (0 : ℝ), MetricComplete (L.atTime t))
    : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
      (fun w : ℝ × L.M => perelmanDensity (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) w.1
        (fun x => ell (x, projIcc 1 T hT.le w.1)) w.2) (Ioo 1 T ×ˢ univ) := by
  intro w hw
  apply ContMDiffAt.contMDiffWithinAt
  rw [contMDiffAt_iff_source, ModelWithCorners.Boundaryless.range_eq_univ,
    contMDiffWithinAt_univ]
  have hz : (w.1, extChartAt I w.2 w.2) ∈ Ioo 1 T ×ˢ (extChartAt I w.2).target :=
    ⟨hw.1, mem_extChartAt_target (I := I) w.2⟩
  have h := ((backward_flow_limit_perelmanDensity_contDiffOn_in_chart
    F hF p tau htau q L Phi R G hG hmetric hT ell hell hLip hescape hconv hcomplete w.2).contDiffAt
      ((isOpen_Ioo.prod (isOpen_extChartAt_target (I := I) w.2)).mem_nhds hz)).contMDiffAt
  simpa only [Function.comp_def, extChartAt_prod, PartialEquiv.prod_coe_symm,
    extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
    extChartAt_coe_symm, Function.id_def, PartialEquiv.prod_coe] using h

theorem backward_flow_limit_perelmanDensity_isHeatPotOn
    (F : PointedFlowData.{u, 0, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ n, 0 < tau n) (q : ℕ → F.M)
    (L : PointedFlowData.{u, 0, uH} (I := I) ancientTimeInterval)
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
    (hescape : Tendsto (tau ∘ subseq) atTop atTop)
    (hconv : ∀ t ∈ Icc (1 - T) (0 : ℝ),
      ∃ C : MetricConvergenceData (Phi.atTime
        (X := backwardFlowSequence F tau htau q) (L := L) t),
      ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData
        (Phi.atTime (X := backwardFlowSequence F tau htau q) (L := L) t) i)
    (hcomplete : ∀ t ∈ Icc (1 - T) (0 : ℝ), MetricComplete (L.atTime t))
    : Analysis.Parabolic.IsHeatPotOn
      (RealTimeInterval.openInterval 1 T ((1 + T) / 2) ⟨by linarith, by linarith⟩)
      (reverseFamily (flowG L.S) 1) (fun r x => -L.S.scalar (1 - r) x)
      (fun r => perelmanDensity (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) r
        (fun x => ell (x, projIcc 1 T hT.le r))) := by
  have hu := backward_flow_limit_perelmanDensity_contMDiffOn
    F hF p tau htau q L Phi R G hG hmetric hT ell hell hLip hescape hconv hcomplete
  refine ⟨hu, hu.continuousOn, ?_, ?_⟩
  · intro t ht
    have h := hu.comp (contMDiffOn_const.prodMk contMDiffOn_id)
      (s := (univ : Set L.M)) (fun y _ => ⟨ht, mem_univ y⟩)
    exact contMDiffOn_univ.mp h
  · intro t ht x
    have he := hasDerivAt_of_conjugate_heat_weak_equation L.S L.isSolution 1
      (u := fun r => perelmanDensity (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) r
        (fun x => ell (x, projIcc 1 T hT.le r))) isOpen_Ioo
      (fun r hr => show 1 - r < 0 from sub_neg.mpr hr.1) hu (by
        intro a φ hφ hφc hφs
        exact (backward_flow_limit_perelmanDensity_weak_eq_in_chart
          F hF p tau htau q L Phi R G hG hmetric hT ell hell hLip hescape hconv hcomplete
          a hφ hφc hφs).symm) ht x
    simpa only [neg_mul, sub_eq_add_neg] using he

theorem backward_flow_reducedLength_limit_hamilton_jacobi_eq
    (F : PointedFlowData.{u, 0, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ n, 0 < tau n) (q : ℕ → F.M)
    (L : PointedFlowData.{u, 0, uH} (I := I) ancientTimeInterval)
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
    (hescape : Tendsto (tau ∘ subseq) atTop atTop)
    (hconv : ∀ t ∈ Icc (1 - T) (0 : ℝ),
      ∃ C : MetricConvergenceData (Phi.atTime
        (X := backwardFlowSequence F tau htau q) (L := L) t),
      ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData
        (Phi.atTime (X := backwardFlowSequence F tau htau q) (L := L) t) i)
    (hcomplete : ∀ t ∈ Icc (1 - T) (0 : ℝ), MetricComplete (L.atTime t))
    {t : ℝ} (ht : t ∈ Ioo 1 T) (x : L.M) :
    let f := fun r y => ell (y, projIcc 1 T hT.le r)
    2 * deriv (fun r => f r x) t + normGradSqFun (L.S.base.metric (1 - t)) (f t) x -
      L.S.scalar (1 - t) x + f t x / t = 0 := by
  let f := fun r y => ell (y, projIcc 1 T hT.le r)
  let U := fun w : ℝ × EuclideanSpace ℝ (Fin n) => f w.1 ((extChartAt I x).symm w.2)
  let z := extChartAt I x x
  have hz : z ∈ (extChartAt I x).target := mem_extChartAt_target (I := I) x
  have hi : z ∈ interior (extChartAt I x).target :=
    (isOpen_extChartAt_target (I := I) x).interior_eq.symm ▸ hz
  have hU : DifferentiableAt ℝ U (t, z) :=
    ((backward_flow_reducedLength_limit_contDiffOn_in_chart
      F hF p tau htau q L Phi R G hG hmetric hT ell hell hLip hescape hconv hcomplete x).contDiffAt
        ((isOpen_Ioo.prod (isOpen_extChartAt_target (I := I) x)).mem_nhds ⟨ht, hz⟩)).differentiableAt (by simp)
  have htime : deriv (fun r => f r x) t = fderiv ℝ U (t, z) (1, 0) := by
    have h := hU.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t z))
    simpa only [Function.comp_def, id_eq, U, z, extChartAt_to_inv] using h.deriv
  have hpartial (j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) :
      partialDeriv j (scalarOnE (I := I) x (f t)) z =
        fderiv ℝ U (t, z) (0, chartModelBasis (EuclideanSpace ℝ (Fin n)) j) := by
    have h := Analysis.fderiv_const_prod hU
    change fderiv ℝ (fun y => f t ((extChartAt I x).symm y)) z _ = _
    simpa only [U, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] using
      congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => A (chartModelBasis (EuclideanSpace ℝ (Fin n)) j)) h
  have hgrad := normGradSqFun_eq_chartInvGram_sum (L.S.base.metric (1 - t)) x (f := f t)
    (show x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) x).baseSet from
      by
        rw [trivializationAt_baseSet_eq_chartAt_source]
        exact mem_chart_source H x) hi
  dsimp only [z] at hpartial
  simp_rw [hpartial] at hgrad
  have hchart := backward_flow_reducedLength_limit_hamilton_jacobi_eq_in_chart
    F hF p tau htau q L Phi R G hG hmetric hT ell hell hLip hescape hconv hcomplete x
      (z := (t, z)) ⟨ht, hz⟩
  change fderiv ℝ U (t, z) (1, 0) + (1 / 2 : ℝ) *
    ∑ k, ∑ j, chartInvGramOnE (L.S.base.metric (1 - t)) x k j z *
      fderiv ℝ U (t, z) (0, chartModelBasis (EuclideanSpace ℝ (Fin n)) j) *
      fderiv ℝ U (t, z) (0, chartModelBasis (EuclideanSpace ℝ (Fin n)) k) -
    (1 / 2 : ℝ) * metricScalarAt (L.S.base.metric (1 - t)) ((extChartAt I x).symm z) +
    U (t, z) / (2 * t) = 0 at hchart
  simp only [chartInvGramOnE_def, U, z, extChartAt_to_inv] at hchart
  change 2 * deriv (fun r => f r x) t + normGradSqFun (L.S.base.metric (1 - t)) (f t) x -
    metricScalarAt (L.S.base.metric (1 - t)) x + f t x / t = 0
  rw [htime, hgrad]
  have hdiv : f t x / (2 * t) = f t x / t / 2 := by ring
  rw [hdiv] at hchart
  linarith

theorem backward_flow_reducedLength_limit_gradientRicciSoliton_and_hamiltonNormalized
    (F : PointedFlowData.{u, 0, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ n, 0 < tau n) (q : ℕ → F.M)
    (L : PointedFlowData.{u, 0, uH} (I := I) ancientTimeInterval)
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
    (hescape : Tendsto (tau ∘ subseq) atTop atTop)
    (hconv : ∀ t ∈ Icc (1 - T) (0 : ℝ),
      ∃ C : MetricConvergenceData (Phi.atTime
        (X := backwardFlowSequence F tau htau q) (L := L) t),
      ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData
        (Phi.atTime (X := backwardFlowSequence F tau htau q) (L := L) t) i)
    (hcomplete : ∀ t ∈ Icc (1 - T) (0 : ℝ), MetricComplete (L.atTime t))
    {t : ℝ} (ht : t ∈ Ioo 1 T) :
    ∃ hf : ContMDiff I 𝓘(ℝ) ∞ (fun x => ell (x, projIcc 1 T hT.le t)),
      Geometry.gradientRicciSoliton (L.S.base.metric (1 - t))
        ⟨(fun x => ell (x, projIcc 1 T hT.le t)), hf⟩ (1 / t) ∧
      Geometry.hamiltonNormalized (L.S.base.metric (1 - t))
        ⟨(fun x => ell (x, projIcc 1 T hT.le t)), hf⟩ (1 / t) := by
  have hu := backward_flow_limit_perelmanDensity_isHeatPotOn
    F hF p tau htau q L Phi R G hG hmetric hT ell hell hLip hescape hconv hcomplete
  apply gradientRicciSoliton_and_hamiltonNormalized_of_conjugate_density_and_hamilton_jacobi
    L.S L.isSolution 1 (fun r x => ell (x, projIcc 1 T hT.le r)) hu ht
    (zero_lt_one.trans ht.1) (show 1 - t < 0 from sub_neg.mpr ht.1)
  intro r hr hrpos x
  have h := backward_flow_reducedLength_limit_hamilton_jacobi_eq
    F hF p tau htau q L Phi R G hG hmetric hT ell hell hLip hescape hconv hcomplete hr x
  simpa only [reverseFamily, flowG, normGradSqFun_def, DifferentialGeometry.Geometry.Connection.gradient_eq_gradFun] using h

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
