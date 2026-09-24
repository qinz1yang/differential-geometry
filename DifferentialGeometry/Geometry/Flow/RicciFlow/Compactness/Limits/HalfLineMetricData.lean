import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PointedCompactMetricBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PointedLowerBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.TimeLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLinePrecompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.HalfLine
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalMetricCompactness
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

section

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_complete_halfLineMetricConvergenceData_of_local_curvature_bound
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hD : X.D = ancientTimeInterval)
    (hcomplete : FlowMetricComplete (I := I) X)
    (hconnected : ∀ i : ℕ,
      let _ : TopologicalSpace (X.term i).M := (X.term i).topology
      ConnectedSpace (X.term i).M)
    (hinj : FlowScaleInjectivityBound (I := I) X)
    (hlocal : ∀ A : ℝ, 0 < A → ∀ T : ℝ, 0 < T → ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (X.term i).M := (X.term i).topology
        let _ : ChartedSpace H (X.term i).M := (X.term i).charted
        let _ : IsManifold I ∞ (X.term i).M := (X.term i).smooth
        ∀ t ∈ Set.Icc (-T) 0, ∀ x : (X.term i).M,
          riemannianEDistOf (I := I) ((X.term i).S.base.metric 0)
              (X.term i).basepoint x ≤ ENNReal.ofReal A →
            (X.term i).rmNormSq (I := I) t x ≤ K)
    (hlower : ∀ T : ℝ, 0 < T → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (X.term i).M := (X.term i).topology
        let _ : ChartedSpace H (X.term i).M := (X.term i).charted
        let _ : IsManifold I ∞ (X.term i).M := (X.term i).smooth
        ∀ t ∈ Set.Icc (-T) 0, ∀ x : (X.term i).M, ∀ v : TangentSpace I x,
          c * ((X.term i).S.base.metric 0).inner x v v ≤
            ((X.term i).S.base.metric t).inner x v v) :
    ∃ (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ),
      StrictMono phi ∧ ∃ (Phi : PointedCGHMaps (I := I) X P phi)
        (R : SmoothRiemannianMetric I P.M),
        R = P.metric ∧ RiemannianMetricComplete R ∧
        ∃ (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi)
          (htgt : TargetIsSigmaCompact Phi)
          (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt),
          ConnectedSpace P.M ∧
            ∀ t : ℝ, t ≤ 0 →
              MetricComplete ({ P with metric := co.gInf t } : PointedRiemannianManifold I) := by
  classical
  have h0 : (0 : ℝ) ∈ X.D.carrier := by
    simp only [hD, ancientTimeInterval_carrier, mem_Iic, le_refl]
  have hjets := exists_eventually_curvDerivNorm_le_on_window_of_local_curvature_bound
    X hD hcomplete hlocal hlower
  obtain ⟨mc, hcanonical, _hreference, hconnectedP⟩ :=
    exists_local_pointed_metric_compactness (X.atZero (I := I))
      (hcomplete.at_time h0) hconnected hinj (fun A hA p => by
        obtain ⟨C, hC, hbound⟩ := hjets A hA 1 zero_lt_one p
        refine ⟨C, hC, hbound.mono fun i hi => ?_⟩
        exact fun x hx => hi 0 ⟨by norm_num, le_rfl⟩ x hx)
  let P := mc.limit
  let : ConnectedSpace P.M := hconnectedP
  let Phi := pointedCGHMapsOfManifold X P mc.subseq mc.maps
  have hsrc : SourceIsSigmaCompact Phi := fun i =>
    DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I (Phi.source_open i)
  have htgt : TargetIsSigmaCompact Phi := fun i =>
    DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I (Phi.target_open i)
  obtain ⟨bf⟩ := nonempty_bumpFamily Phi
  let G := gSeqExt Phi P.metric bf hsrc htgt
  have hG := eventually_gSeqExt_eq_pullback Phi P.metric bf hsrc htgt
  have hbounds := exists_eventually_pointed_extension_metric_bounds_on_compact
    X hD hcomplete mc.strictMono.tendsto_atTop mc.maps mc.convergence.metrics hcanonical
    mc.limit_complete G hG hlocal hlower
  have hlow := exists_eventually_pointed_metric_extension_lower_bound X
    mc.strictMono.tendsto_atTop mc.maps mc.convergence.metrics hcanonical bf hsrc htgt hlower
  have hwindow (n : ℕ) : Icc (-(n : ℝ)) 0 ⊆ Icc (-((n : ℝ) + 1)) 0 :=
    fun _ ht => ⟨by linarith [ht.1], ht.2⟩
  have hind (n i : ℕ) (K : Set P.M) (hK : IsCompact K) (p : ℕ) :
      ∃ L : ℝ, 0 ≤ L ∧ ∀ s ∈ Icc (-(n : ℝ)) 0, ∀ t ∈ Icc (-(n : ℝ)) 0,
        ∀ q ≤ p, ∀ x ∈ K, metricDerivNorm q (G i s) (G i t) P.metric x ≤ L * |s - t| := by
    have hcar : Icc (-((n : ℝ) + 1)) 0 ⊆ X.D.carrier := by
      rw [hD, ancientTimeInterval_carrier]
      exact Icc_subset_Iic_self
    have hreg : Ico (-((n : ℝ) + 1)) 0 ⊆ X.D.regular := by
      rw [hD, ancientTimeInterval_regular]
      exact Ico_subset_Iio_self
    obtain ⟨L, hL, hb⟩ := exists_metric_extension_time_lipschitz_constant_on_closed_interval
      Phi P.metric bf hsrc htgt (neg_neg_of_pos (by positivity)) hcar hreg i K hK p
    exact ⟨L, hL, fun s hs t ht q hq x hx => hb s (hwindow n hs) t (hwindow n ht) q hq x hx⟩
  have hlip (n : ℕ) (K : Set P.M) (hK : IsCompact K) (p : ℕ) :
      ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ i in atTop,
        ∀ s ∈ Icc (-(n : ℝ)) 0, ∀ t ∈ Icc (-(n : ℝ)) 0, ∀ q ≤ p, ∀ x ∈ K,
          metricDerivNorm q (G i s) (G i t) P.metric x ≤ L * |s - t| := by
    obtain ⟨C, L, _hC, hL, hb⟩ := hbounds ((n : ℝ) + 1) (by positivity) p K hK
    exact ⟨L, hL, hb.mono fun _ hi s hs t ht q hq x hx =>
      hi.2 q hq s (hwindow n hs) t (hwindow n ht) x hx⟩
  have hcov (n : ℕ) (t : ℝ) (ht : t ∈ Icc (-(n : ℝ)) 0) (q : ℕ)
      (K : Set P.M) (hK : IsCompact K) :
      ∃ C : ℝ, ∀ᶠ i in atTop, ∀ x ∈ K, metricCovDerivNorm q (G i t) P.metric x ≤ C := by
    obtain ⟨C, L, _hC, _hL, hb⟩ := hbounds ((n : ℝ) + 1) (by positivity) q K hK
    exact ⟨C, hb.mono fun _ hi x hx => hi.1 q le_rfl t (hwindow n ht) x hx⟩
  obtain ⟨co⟩ := exists_halfLineMetricConvergenceData_of_eventual_pointwise_lower
    Phi P.metric bf hsrc htgt hind hlip hcov (fun n t ht x => by
      obtain ⟨c, hc, hb⟩ := hlow ((n : ℝ) + 1) (by positivity)
      exact ⟨c, hc, (hb {x} isCompact_singleton).mono fun _ hi v =>
        hi t (hwindow n ht) x (mem_singleton x) v⟩)
  refine ⟨P, mc.subseq, mc.strictMono, Phi, P.metric, rfl, ?_,
    bf, hsrc, htgt, co, hconnectedP, ?_⟩
  · exact ⟨mc.limit_complete⟩
  · intro t ht0
    obtain ⟨c, hc, hb⟩ := hlow (1 - t) (by linarith)
    apply co.metricComplete_of_eventually_lower Phi mc.limit_complete ht0 hc
    intro x v
    filter_upwards [co.strictMono.tendsto_atTop.eventually (hb {x} isCompact_singleton)]
      with i hi
    exact hi t ⟨by linarith, ht0⟩ x (mem_singleton x) v

end

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
