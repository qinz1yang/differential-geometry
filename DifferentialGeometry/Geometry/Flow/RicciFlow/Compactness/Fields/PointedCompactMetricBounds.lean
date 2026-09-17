import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PointedExtensionMetricBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Curvature.LocalWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CompactPointedChartControl

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_eventually_pointed_extension_metric_bounds_on_compact
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hD : X.D = ancientTimeInterval) (hcomplete : FlowMetricComplete X)
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} [ConnectedSpace P.M]
    {phi : ℕ → ℕ} (hphi : Tendsto phi atTop atTop)
    (F : PointedRiemannianConvergenceMaps (X.atZero (I := I)) P phi)
    (C : MetricConvergenceData F)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData F i)
    (hPcomplete : MetricComplete P)
    (G : ℕ → ℝ → SmoothRiemannianMetric I P.M)
    (hG : ∀ K : Set P.M, IsCompact K → ∀ᶠ i in atTop,
      ∃ U : Set P.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ F.source i ∧
        ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
          (G i t).inner x v w = ((X.term (phi i)).S.base.metric t).inner (F.map i x)
            (mfderiv I I (F.map i) x v) (mfderiv I I (F.map i) x w))
    (hlocal : ∀ A : ℝ, 0 < A → ∀ T : ℝ, 0 < T → ∃ Q : ℝ, 0 ≤ Q ∧
      ∀ᶠ i in atTop, ∀ t ∈ Icc (-T) 0, ∀ x : (X.term i).M,
        riemannianEDistOf ((X.term i).S.base.metric 0) (X.term i).basepoint x ≤
          ENNReal.ofReal A → (X.term i).rmNormSq t x ≤ Q)
    (hlower : ∀ T : ℝ, 0 < T → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ i in atTop, ∀ t ∈ Icc (-T) 0, ∀ x : (X.term i).M,
        ∀ v : TangentSpace I x,
          c * ((X.term i).S.base.metric 0).inner x v v ≤
            ((X.term i).S.base.metric t).inner x v v) :
    ∀ T : ℝ, 0 < T → ∀ p : ℕ, ∀ K : Set P.M, IsCompact K →
      ∃ C L : ℝ, 0 ≤ C ∧ 0 ≤ L ∧ ∀ᶠ i in atTop,
        (∀ q ≤ p, ∀ t ∈ Icc (-T) 0, ∀ x ∈ K,
          metricCovDerivNorm q (G i t) P.metric x ≤ C) ∧
        (∀ q ≤ p, ∀ s ∈ Icc (-T) 0, ∀ t ∈ Icc (-T) 0, ∀ x ∈ K,
          metricDerivNorm q (G i s) (G i t) P.metric x ≤ L * |s - t|) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  intro T hT p K hK
  have hP : RiemannianMetricComplete P.metric := ⟨MetricComplete.complete P hPcomplete⟩
  obtain ⟨V, hKV, _hVc, A, hA, hVA⟩ :=
    exists_precompact_bounded_comparison_open P.metric hP P.basepoint hK
  have hKA := hKV.trans hVA
  have hcar : Icc (-T) 0 ⊆ X.D.carrier := by
    rw [hD, ancientTimeInterval_carrier]
    exact Icc_subset_Iic_self
  have hreg : Ico (-T) 0 ⊆ X.D.regular := by
    rw [hD, ancientTimeInterval_regular]
    exact Ico_subset_Iio_self
  have hjet := exists_eventually_curvDerivNorm_le_on_window_of_local_curvature_bound
    X hD hcomplete hlocal hlower
  obtain ⟨C₀, L, hC₀, hL, hbound⟩ := exists_eventually_pointed_extension_metric_bounds
    hphi F C hcanonical hPcomplete G hG (neg_neg_of_pos hT) hcar hreg p
    (fun R hR q _ => hjet R hR T hT q) hA.le
  refine ⟨C₀, L, hC₀, hL, hbound.mono fun i hi => ?_⟩
  exact ⟨fun q hq t ht x hx => hi.1 q hq t ht x (hKA hx),
    fun q hq s hs t ht x hx => hi.2 q hq s hs t ht x (hKA hx)⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
