import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionWindowLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ScaledPointedLimitLine
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionWindowProductNeck
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.LineProductSplitting
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PointedSpatialNeckLimit
import DifferentialGeometry.Geometry.Neck.LineNeckSimplyConnected
import DifferentialGeometry.Geometry.Curvature.RicciNonnegativeConvergence
import DifferentialGeometry.Geometry.Curvature.Coordinates.RiemannTensorBridge
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
  (SpatialCanonicalWitness SpatialCanonicalAlternative SpatialNeck neckModelTolerance
    neckModelTolerance_pos neckModelTolerance_le_smallness backgroundJetSmallness_ceil_lt_self
    exists_spatialNeck_of_pointed_spatialNecks_on_compact_ball)
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

theorem exists_tolerance_subseq_neckAlternative_of_isTracedRegion_uniform :
    ∃ etaD : ℝ, 0 < etaD ∧
    ∀ {κ ε C1 C2 Cq qcan : ℝ} {Ctime : ℝ≥0} {phi : ℝ → ℝ}, 0 < κ → 0 < ε → ε ≤ etaD →
      Perelman.AdmissiblePinchingFunction phi →
    ∀ (K : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (K n).horizon)
      (y : ∀ n, ((K n).stageAt (t n)).Carrier) (R : ℕ → ℝ), (∀ n, 0 < R n) →
      (∀ n, metricScalarAt ((K n).stageMetric ((K n).activeStage (t n)) (t n)) (y n) = R n) →
      Tendsto R atTop atTop → (∀ n, (K n).time ((K n).activeStage (t n)) < t n) →
      (∀ n (v : Icc (0 : ℝ) (K n).horizon) (p : ((K n).stageAt v).Carrier) (r : ℝ),
        (v : ℝ) < t n → r ≤ ε → (K n).isParabolicallyRmControlledBall v p r →
        ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((K n).stageAt v).Carrier
            ((K n).stageMetric ((K n).activeStage v) v)
            (riemannianBallOf ((K n).stageMetric ((K n).activeStage v) v) p r)) →
      (∀ n (v : Icc (0 : ℝ) (K n).horizon), (v : ℝ) ≤ t n →
        ∀ x : ((K n).stageAt v).Carrier,
          curvatureOperatorLowerBoundAt ((K n).stageMetric ((K n).activeStage v) v) x
            (metricAlgebraicCurvatureTensorAt ((K n).stageMetric ((K n).activeStage v) v) x)
            (phi (metricScalarAt ((K n).stageMetric ((K n).activeStage v) v) x))) →
      (∀ n, qcan ≤ Cq * R n) →
      (∀ n (v : Icc (0 : ℝ) (K n).horizon), (v : ℝ) ≤ t n →
        (K n).time ((K n).activeStage v) < v → ∀ p : ((K n).stageAt v).Carrier,
          qcan < metricScalarAt ((K n).stageMetric ((K n).activeStage v) v) p →
          ∃ Wt : SpatialCanonicalWitness ((K n).stageMetric ((K n).activeStage v) v) ε C1 C2 p,
            Wt.capTubeHasNeckChart ε) →
      (∀ n (v : Icc (0 : ℝ) (K n).horizon), (v : ℝ) < t n →
        (K n).time ((K n).activeStage v) < v → ∀ p : ((K n).stageAt v).Carrier,
          qcan < metricScalarAt ((K n).stageMetric ((K n).activeStage v) v) p →
          |derivWithin (fun v' => metricScalarAt ((K n).stageMetric ((K n).activeStage v) v') p)
            (Iic (v : ℝ)) v| ≤
            Ctime * metricScalarAt ((K n).stageMetric ((K n).activeStage v) v) p ^ 2) →
      (∀ A c : ℝ, 0 < A → 0 < c → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((K n).stageMetric ((K n).activeStage (t n)) (t n)) (y n)
          (A / Real.sqrt (R n)),
        c * R n ≤ metricScalarAt ((K n).stageMetric ((K n).activeStage (t n)) (t n)) x →
        ∀ W : SpatialCanonicalWitness ((K n).stageMetric ((K n).activeStage (t n)) (t n))
            ε C1 C2 x,
          W.capTubeHasNeckChart ε → ∃ nk, W.alternative = SpatialCanonicalAlternative.neck nk) →
      ∀ (S V W : ∀ n, Set ((K n).stageAt (t n)).Carrier), (∀ n, IsOpen (V n)) →
        (∀ n, IsOpen (W n)) → (∀ n, Disjoint (V n) (W n)) →
        (∀ n, ∀ z ∈ S n,
          riemannianEDistOf ((K n).stageMetric ((K n).activeStage (t n)) (t n)) (y n) z ≤
            ENNReal.ofReal (7 / Real.sqrt (R n))) →
        (∀ A : ℝ, 7 < A → ∀ᶠ n in atTop,
          riemannianClosedBallOf ((K n).stageMetric ((K n).activeStage (t n)) (t n)) (y n)
              (3 * A / Real.sqrt (R n)) \ S n ⊆ V n ∪ W n ∧
          ∃ p ∈ V n, ∃ q ∈ W n,
            ENNReal.ofReal (A / Real.sqrt (R n)) ≤
              riemannianEDistOf ((K n).stageMetric ((K n).activeStage (t n)) (t n)) (y n) p ∧
            riemannianEDistOf ((K n).stageMetric ((K n).activeStage (t n)) (t n)) (y n) p <
              ENNReal.ofReal (3 * A / Real.sqrt (R n)) ∧
            ENNReal.ofReal (A / Real.sqrt (R n)) ≤
              riemannianEDistOf ((K n).stageMetric ((K n).activeStage (t n)) (t n)) (y n) q ∧
            riemannianEDistOf ((K n).stageMetric ((K n).activeStage (t n)) (t n)) (y n) q <
              ENNReal.ofReal (3 * A / Real.sqrt (R n))) →
      ∀ T : ℝ, 0 < T →
        (∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ A T' : ℝ, 0 < A → 0 < T' → T' ≤ T → ∀ᶠ n in atTop,
          (K n).isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (T' / R n) (Kb * R n)) →
        ∀ T' : ℝ, 0 ≤ T' → T' < T → ∀ A c : ℝ, 0 < A → 0 < c →
        ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ᶠ i in atTop,
          ∀ x ∈ riemannianBallOf
            ((K (σ i)).stageMetric ((K (σ i)).activeStage (t (σ i))) (t (σ i))) (y (σ i))
            (A / Real.sqrt (R (σ i))),
          ∀ v : Icc (0 : ℝ) (K (σ i)).horizon, (t (σ i) : ℝ) - T' / R (σ i) ≤ v →
          ∀ hvt : v ≤ t (σ i), (K (σ i)).time ((K (σ i)).activeStage v) < v →
          ∀ B : BackwardPointTrace (K (σ i)) ((K (σ i)).activeStage v)
              ((K (σ i)).activeStage (t (σ i))) ((K (σ i)).activeStage_mono hvt) x,
            c * R (σ i) ≤ metricScalarAt ((K (σ i)).stageMetric ((K (σ i)).activeStage v) v)
              (B.point ((K (σ i)).activeStage v) le_rfl ((K (σ i)).activeStage_mono hvt)) →
            ∀ W : SpatialCanonicalWitness
                ((K (σ i)).stageMetric ((K (σ i)).activeStage v) v) ε C1 C2
                (B.point ((K (σ i)).activeStage v) le_rfl ((K (σ i)).activeStage_mono hvt)),
              W.capTubeHasNeckChart ε →
                ∃ nk, W.alternative = SpatialCanonicalAlternative.neck nk := by
  obtain ⟨D, hD, hlimneck⟩ := exists_spatialNeck_of_pointed_spatialNecks_on_compact_ball.{u}
    (alpha := 1 / 2000) (by norm_num) (by norm_num)
  have hmt : 0 < neckModelTolerance (1 / 2000 : ℝ) := neckModelTolerance_pos (by norm_num)
  have hmt11 : neckModelTolerance (1 / 2000 : ℝ) < 1 / 11 :=
    ((neckModelTolerance_le_smallness (1 / 2000 : ℝ)).trans_lt
      (backgroundJetSmallness_ceil_lt_self _ (by norm_num) (by norm_num))).trans (by norm_num)
  refine ⟨min (1 / 1000) (neckModelTolerance (1 / 2000)), lt_min (by norm_num) hmt, ?_⟩
  intro κ ε C1 C2 Cq qcan Ctime phi hκ hε hεD hphi K t y R hR hscal hRlim htop hnc hpinch hqC
    hwit hderiv htopneck Sset Vset Wset hV hW hVW hS hpoints T hT hprem T' hT'0 hT'T A c hA hc
  obtain ⟨Kb, hKb, hpre⟩ := hprem
  obtain ⟨Wo, h, hblock, hlip, -, -, -, f, hf, P, F, ⟨Cd, hcan⟩, hPc, hconn, -, V', N, hV', hVF, φ,
    hφ, hφF, G, hG0, hG, hcone, hcompl, hbound, hbase, -, ψ, hψ, hconv⟩ :=
    exists_window_pointed_flow_limit_of_isTracedRegion K t y R hR hRlim hT hKb
      (fun A' hA' => hpre A' T hA' hT le_rfl) hκ hε (t₀ := fun n => t n) (by simp) hnc hphi
      hpinch
  obtain ⟨line, hline⟩ := exists_line_of_scaled_pointed_limit_of_separating_set K t y R hR hf
    F Cd hcan hPc hconn Sset Vset Wset hV hW hVW (B := 7) (by norm_num) hS hpoints
  have hT0 : (0 : ℝ) ∈ Ioc (-T) 0 := ⟨neg_lt_zero.mpr hT, le_rfl⟩
  have hbaseP : metricScalarAt P.metric P.basepoint = 1 := hbase hscal
  have hcomplP : RiemannianMetricComplete P.metric := hG0 ▸ hcompl 0 hT0
  have hnecks : ∀ᶠ n in atTop, Nonempty (SpatialNeck
      (scaleMetric (R n) (hR n) ((K n).stageMetric ((K n).activeStage (t n)) (t n)))
      (neckModelTolerance (1 / 2000)) (y n)) := by
    filter_upwards [htopneck 1 (1 / 2) one_pos (by norm_num), hRlim.eventually_gt_atTop qcan]
      with n hn hqn
    obtain ⟨Wt, hWt⟩ := hwit n (t n) le_rfl (htop n) (y n) (by rw [hscal n]; exact hqn)
    have hyball : y n ∈ riemannianBallOf ((K n).stageMetric ((K n).activeStage (t n)) (t n))
        (y n) (1 / Real.sqrt (R n)) := by
      change riemannianEDistOf _ (y n) (y n) < _
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr (div_pos one_pos (Real.sqrt_pos.mpr (hR n)))
    obtain ⟨nk, -⟩ := hn (y n) hyball (by rw [hscal n]; linarith [hR n]) Wt hWt
    exact ⟨(nk.neck.scaleMetric (R n) (hR n)).mono (hεD.trans (min_le_right _ _)) hmt11⟩
  have hnecksf : ∀ᶠ n in atTop, Nonempty (SpatialNeck
      (scaleMetric (R (f n)) (hR (f n))
        ((K (f n)).stageMetric ((K (f n)).activeStage (t (f n))) (t (f n))))
      (neckModelTolerance (1 / 2000)) (F.partialDiffeomorph n P.basepoint)) := by
    filter_upwards [hf.tendsto_atTop.eventually hnecks] with n hn
    rw [F.basepoint_map n]
    exact hn
  have hne : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hcpt : IsCompact (riemannianClosedBallOf P.metric P.basepoint (D + 1)) :=
    hcomplP.closedEBall_isCompact P.basepoint (D + 1)
  obtain ⟨nkP⟩ := hlimneck _ f P F Cd hcan P.basepoint (by rw [hbaseP]; exact one_pos) (D + 1)
    (by linarith) hcpt (by rw [hbaseP, Real.sqrt_one, one_mul]; linarith) hnecksf
  have hRic : ∀ (x : P.M) (v : TangentSpace ThreeModel x), 0 ≤ ricciTensor P.metric x v v :=
    fun x v => ricciTensor_nonnegative_of_curvatureOperator_nonnegative P.metric x
      (by rw [← hG0]; exact hcone 0 hT0 x) v
  have hsc : SimplyConnectedSpace P.M :=
    nkP.simplyConnectedSpace_of_line P.metric hcomplP hRic hline (by norm_num)
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have haT : -T < -((T' + T) / 2) := by linarith
  have ha0 : -((T' + T) / 2) < 0 := by linarith
  have haT' : -((T' + T) / 2) ≤ -T' := by linarith
  obtain ⟨Nf, topN, csN, smN, t2N, sigN, hN, Phi, connN, -, hprod, -, -⟩ :=
    exists_surface_product_on_closed_interval_of_line (I := ThreeModel) (M := P.M)
      ({ base.metric := G } : SolutionOn (I := ThreeModel) (M := P.M)
        (RealTimeInterval.openClosed (-T) 0 0 hT0))
      hG hdim ha0 (fun s hs => ⟨haT.trans_le hs.1, hs.2⟩) (fun s hs => ⟨haT.trans hs.1, hs.2⟩)
      (fun s hs x => hcone s ⟨haT.trans_le hs.1, hs.2⟩ x) (hcompl 0 hT0)
      ⟨Kb ^ 2, by positivity, fun s hs x => hbound s ⟨haT.trans_le hs.1, hs.2⟩ x⟩
      ⟨P.basepoint, fun h0 => by
        have h1 := metricScalarAt_eq_zero_of_metricRm04At_eq_zero (G 0) P.basepoint h0
        rw [hG0, hbaseP] at h1
        exact one_ne_zero h1⟩
      (gamma := line) (fun a b => by
        change riemannianEDistOf (G 0) (line a) (line b) = _
        rw [hG0]
        exact hline a b)
  let _ : TopologicalSpace Nf := topN
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) Nf := csN
  let _ : IsManifold (𝓡 2) ∞ Nf := smN
  let _ : T2Space Nf := t2N
  let _ : SigmaCompactSpace Nf := sigN
  have _ : ConnectedSpace Nf := connN
  refine ⟨f ∘ ψ, hf.comp hψ, ?_⟩
  have h4b := eventually_forall_neckAlternative_of_window_product_structure K t y R hR hT
    (fun k => (hblock k).mono fun n hn => ⟨hn.1, hn.2.2.2.1⟩) hf F Cd hcan hPc hV' hVF hφF hG0
    hcompl hψ hconv hlip hT'0 hT'T Nf hN Phi (fun s hs => hprod s ⟨haT'.trans hs.1, hs.2⟩)
    (C1 := C1) (C2 := C2) (hεD.trans (min_le_left _ _)) A c hA hc
  filter_upwards [h4b] with i hi
  intro x hx v hv hvt _ B hB Wt hWt
  exact hi x hx v hv hvt B hB Wt hWt

theorem exists_tolerance_eventually_neckAlternative_of_isTracedRegion_uniform :
    ∃ etaD : ℝ, 0 < etaD ∧
    ∀ {κ ε C1 C2 Cq qcan : ℝ} {Ctime : ℝ≥0} {phi : ℝ → ℝ}, 0 < κ → 0 < ε → ε ≤ etaD →
      Perelman.AdmissiblePinchingFunction phi →
    ∀ (K : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (K n).horizon)
      (y : ∀ n, ((K n).stageAt (t n)).Carrier) (R : ℕ → ℝ), (∀ n, 0 < R n) →
      (∀ n, metricScalarAt ((K n).stageMetric ((K n).activeStage (t n)) (t n)) (y n) = R n) →
      Tendsto R atTop atTop → (∀ n, (K n).time ((K n).activeStage (t n)) < t n) →
      (∀ n (v : Icc (0 : ℝ) (K n).horizon) (p : ((K n).stageAt v).Carrier) (r : ℝ),
        (v : ℝ) < t n → r ≤ ε → (K n).isParabolicallyRmControlledBall v p r →
        ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((K n).stageAt v).Carrier
            ((K n).stageMetric ((K n).activeStage v) v)
            (riemannianBallOf ((K n).stageMetric ((K n).activeStage v) v) p r)) →
      (∀ n (v : Icc (0 : ℝ) (K n).horizon), (v : ℝ) ≤ t n →
        ∀ x : ((K n).stageAt v).Carrier,
          curvatureOperatorLowerBoundAt ((K n).stageMetric ((K n).activeStage v) v) x
            (metricAlgebraicCurvatureTensorAt ((K n).stageMetric ((K n).activeStage v) v) x)
            (phi (metricScalarAt ((K n).stageMetric ((K n).activeStage v) v) x))) →
      (∀ n, qcan ≤ Cq * R n) →
      (∀ n (v : Icc (0 : ℝ) (K n).horizon), (v : ℝ) ≤ t n →
        (K n).time ((K n).activeStage v) < v → ∀ p : ((K n).stageAt v).Carrier,
          qcan < metricScalarAt ((K n).stageMetric ((K n).activeStage v) v) p →
          ∃ Wt : SpatialCanonicalWitness ((K n).stageMetric ((K n).activeStage v) v) ε C1 C2 p,
            Wt.capTubeHasNeckChart ε) →
      (∀ n (v : Icc (0 : ℝ) (K n).horizon), (v : ℝ) < t n →
        (K n).time ((K n).activeStage v) < v → ∀ p : ((K n).stageAt v).Carrier,
          qcan < metricScalarAt ((K n).stageMetric ((K n).activeStage v) v) p →
          |derivWithin (fun v' => metricScalarAt ((K n).stageMetric ((K n).activeStage v) v') p)
            (Iic (v : ℝ)) v| ≤
            Ctime * metricScalarAt ((K n).stageMetric ((K n).activeStage v) v) p ^ 2) →
      (∀ A c : ℝ, 0 < A → 0 < c → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((K n).stageMetric ((K n).activeStage (t n)) (t n)) (y n)
          (A / Real.sqrt (R n)),
        c * R n ≤ metricScalarAt ((K n).stageMetric ((K n).activeStage (t n)) (t n)) x →
        ∀ W : SpatialCanonicalWitness ((K n).stageMetric ((K n).activeStage (t n)) (t n))
            ε C1 C2 x,
          W.capTubeHasNeckChart ε → ∃ nk, W.alternative = SpatialCanonicalAlternative.neck nk) →
      ∀ (S V W : ∀ n, Set ((K n).stageAt (t n)).Carrier), (∀ n, IsOpen (V n)) →
        (∀ n, IsOpen (W n)) → (∀ n, Disjoint (V n) (W n)) →
        (∀ n, ∀ z ∈ S n,
          riemannianEDistOf ((K n).stageMetric ((K n).activeStage (t n)) (t n)) (y n) z ≤
            ENNReal.ofReal (7 / Real.sqrt (R n))) →
        (∀ A : ℝ, 7 < A → ∀ᶠ n in atTop,
          riemannianClosedBallOf ((K n).stageMetric ((K n).activeStage (t n)) (t n)) (y n)
              (3 * A / Real.sqrt (R n)) \ S n ⊆ V n ∪ W n ∧
          ∃ p ∈ V n, ∃ q ∈ W n,
            ENNReal.ofReal (A / Real.sqrt (R n)) ≤
              riemannianEDistOf ((K n).stageMetric ((K n).activeStage (t n)) (t n)) (y n) p ∧
            riemannianEDistOf ((K n).stageMetric ((K n).activeStage (t n)) (t n)) (y n) p <
              ENNReal.ofReal (3 * A / Real.sqrt (R n)) ∧
            ENNReal.ofReal (A / Real.sqrt (R n)) ≤
              riemannianEDistOf ((K n).stageMetric ((K n).activeStage (t n)) (t n)) (y n) q ∧
            riemannianEDistOf ((K n).stageMetric ((K n).activeStage (t n)) (t n)) (y n) q <
              ENNReal.ofReal (3 * A / Real.sqrt (R n))) →
      ∀ T : ℝ, 0 < T →
        (∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ A T' : ℝ, 0 < A → 0 < T' → T' ≤ T → ∀ᶠ n in atTop,
          (K n).isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (T' / R n) (Kb * R n)) →
        ∀ T' : ℝ, 0 ≤ T' → T' < T → ∀ A c : ℝ, 0 < A → 0 < c → ∀ᶠ n in atTop,
          ∀ x ∈ riemannianBallOf ((K n).stageMetric ((K n).activeStage (t n)) (t n)) (y n)
            (A / Real.sqrt (R n)),
          ∀ v : Icc (0 : ℝ) (K n).horizon, (t n : ℝ) - T' / R n ≤ v →
          ∀ hvt : v ≤ t n, (K n).time ((K n).activeStage v) < v →
          ∀ B : BackwardPointTrace (K n) ((K n).activeStage v) ((K n).activeStage (t n))
              ((K n).activeStage_mono hvt) x,
            c * R n ≤ metricScalarAt ((K n).stageMetric ((K n).activeStage v) v)
              (B.point ((K n).activeStage v) le_rfl ((K n).activeStage_mono hvt)) →
            ∀ W : SpatialCanonicalWitness ((K n).stageMetric ((K n).activeStage v) v) ε C1 C2
                (B.point ((K n).activeStage v) le_rfl ((K n).activeStage_mono hvt)),
              W.capTubeHasNeckChart ε →
                ∃ nk, W.alternative = SpatialCanonicalAlternative.neck nk := by
  obtain ⟨etaD, hetaD, hsub⟩ :=
    exists_tolerance_subseq_neckAlternative_of_isTracedRegion_uniform.{u}
  refine ⟨etaD, hetaD, ?_⟩
  intro κ ε C1 C2 Cq qcan Ctime phi hκ hε hεD hphi K t y R hR hscal hRlim htop hnc hpinch hqC
    hwit hderiv htopneck S V W hV hW hVW hS hpoints T hT hprem T' hT'0 hT'T A c hA hc
  by_contra hnot
  rw [Filter.not_eventually] at hnot
  obtain ⟨σ₀, hσ₀, hbad⟩ := Filter.extraction_of_frequently_atTop hnot
  obtain ⟨Kb, hKb, hpre⟩ := hprem
  obtain ⟨σ, -, hev⟩ := hsub hκ hε hεD hphi (fun i => K (σ₀ i)) (fun i => t (σ₀ i))
    (fun i => y (σ₀ i)) (fun i => R (σ₀ i)) (fun i => hR (σ₀ i)) (fun i => hscal (σ₀ i))
    (hRlim.comp hσ₀.tendsto_atTop) (fun i => htop (σ₀ i)) (fun i => hnc (σ₀ i))
    (fun i => hpinch (σ₀ i)) (fun i => hqC (σ₀ i)) (fun i => hwit (σ₀ i))
    (fun i => hderiv (σ₀ i))
    (fun A' c' hA' hc' => hσ₀.tendsto_atTop.eventually (htopneck A' c' hA' hc'))
    (fun i => S (σ₀ i)) (fun i => V (σ₀ i)) (fun i => W (σ₀ i)) (fun i => hV (σ₀ i))
    (fun i => hW (σ₀ i)) (fun i => hVW (σ₀ i)) (fun i => hS (σ₀ i))
    (fun A' hA' => hσ₀.tendsto_atTop.eventually (hpoints A' hA')) T hT
    ⟨Kb, hKb, fun A' T'' hA' hT'' hle => hσ₀.tendsto_atTop.eventually (hpre A' T'' hA' hT'' hle)⟩
    T' hT'0 hT'T A c hA hc
  obtain ⟨i, hi⟩ := hev.exists
  exact hbad (σ i) hi

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
