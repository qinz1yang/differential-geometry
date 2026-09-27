import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedVolumeRigidity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardFlowRigidity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkerMassNonflat

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

theorem backward_flow_reducedLength_limit_normalized_shrinker_and_mass
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
      Geometry.normalizedGradientRicciSoliton
        (scaleMetric t⁻¹ (inv_pos.mpr (zero_lt_one.trans ht.1)) (L.S.base.metric (1 - t)))
        ⟨(fun x => ell (x, projIcc 1 T hT.le t)), hf⟩ ∧
      normalizedShrinkerMass
        (scaleMetric t⁻¹ (inv_pos.mpr (zero_lt_one.trans ht.1)) (L.S.base.metric (1 - t)))
        (fun x => ell (x, projIcc 1 T hT.le t)) = asymptoticReducedVolume F.S 0 p := by
  have htpos := zero_lt_one.trans ht.1
  have hs : 1 - t ∈ Icc (1 - T) (0 : ℝ) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  obtain ⟨hf, hsol, hham⟩ :=
    backward_flow_reducedLength_limit_gradientRicciSoliton_and_hamiltonNormalized
      F hF p tau htau q L Phi R G hG hmetric hT ell hell hLip hescape hconv hcomplete ht
  refine ⟨hf, ?_, ?_⟩
  · have hc : RiemannianMetricComplete (L.S.base.metric (1 - t)) := ⟨hcomplete (1 - t) hs⟩
    simpa only [one_div] using Geometry.normalizedGradientRicciSoliton_scaleMetric_of_hamiltonNormalized
      hc hsol hham (one_div_pos.mpr htpos)
  · rw [normalizedShrinkerMass_scaleMetric_inv_eq_lintegral_perelmanDensity _ htpos]
    obtain ⟨C, hcanonical⟩ := hconv (1 - t) hs
    apply lintegral_perelmanDensity_eq_asymptoticReducedVolume_of_backward_flow_limit
      F hF p tau htau q htpos (L.atTime (1 - t)) hescape
      (Phi.atTime (X := backwardFlowSequence F tau htau q) (L := L) (1 - t))
      C hcanonical (hcomplete (1 - t) hs)
    intro x
    let theta : Icc (1 : ℝ) T := ⟨t, ht.1.le, ht.2.le⟩
    have h := (hell {(x, theta)} isCompact_singleton).tendsto_at (x := (x, theta)) (mem_singleton _)
    change Tendsto (fun i => redLength F.S 0 p (Phi.map i x) (tau (subseq i) * t)) atTop
      (𝓝 (ell (x, projIcc 1 T hT.le t)))
    rw [projIcc_of_mem hT.le ⟨ht.1.le, ht.2.le⟩]
    convert h using 1
    rfl

theorem backward_flow_reducedLength_limit_scalar_pos
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
    0 < metricScalarAt (L.S.base.metric (1 - t)) x := by
  have hmass : asymptoticReducedVolume F.S 0 p ≠ 1 :=
    (ancient_asymptoticReducedVolume_lt_one F hF p).ne
  let _ : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) := neZero_finrank_of_isAncientKappaSolution F hF
  let _ : ConnectedSpace L.M := { toNonempty := ⟨L.basepoint⟩ }
  obtain ⟨hf, hsol, heq⟩ := backward_flow_reducedLength_limit_normalized_shrinker_and_mass
    F hF p tau htau q L Phi R G hG hmetric hT ell hell hLip hescape hconv hcomplete ht
  have hs := scalar_pos_of_normalizedShrinkerMass_ne_one hsol (by
    change normalizedShrinkerMass _ (fun x => ell (x, projIcc 1 T hT.le t)) ≠ 1
    rwa [heq]) x
  rw [metricScalarAt_scaleMetric, inv_inv] at hs
  exact (mul_pos_iff.mp hs).resolve_right (fun h => (not_lt_of_ge (zero_lt_one.trans ht.1).le) h.1) |>.2

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
