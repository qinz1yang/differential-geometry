import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PointedCompactMetricBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PointedLowerBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.TimeLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLinePrecompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.HalfLine
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalMetricCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.FlowOfMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedFlowSlices
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Canonical.ReferenceChange
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.InjectivityRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

section

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_local_ancient_flow_compactness_with_uniform_metric_convergence
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
    ∃ (L : PointedFlowData.{u, uE, uH} (I := I) X.D) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi,
        (let _ : TopologicalSpace L.M := L.topology
         ConnectedSpace L.M) ∧
        (∀ t ∈ X.D.carrier, MetricComplete (I := I) (L.atTime (I := I) t)) ∧
        (∀ t ∈ X.D.carrier,
          ∃ C : MetricConvergenceData (I := I) (Phi.atTime (L := L) t),
            (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
              (I := I) (Phi.atTime (L := L) t) k) ∧
            (∀ k,
              let D := C.domain k
              let _ : TopologicalSpace
                (MetricSourceDomain (I := I) (Phi.atTime (L := L) t) k) := D.topology
              let _ : ChartedSpace H
                (MetricSourceDomain (I := I) (Phi.atTime (L := L) t) k) := D.charted
              let _ : IsManifold I ∞
                (MetricSourceDomain (I := I) (Phi.atTime (L := L) t) k) := D.smooth
              D.referenceMetric = D.limitMetric)) ∧
        ∃ (R : SmoothRiemannianMetric I L.M) (G : ℕ → ℝ → SmoothRiemannianMetric I L.M),
          (∀ K : Set L.M, IsCompact K → ∀ᶠ i in atTop,
            ∃ U : Set L.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Phi.source i ∧
              ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
                (G i t).inner x v w = ((X.term (phi i)).S.base.metric t).inner
                  (Phi.map i x) (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x w)) ∧
          (∀ a b : ℝ, Icc a b ⊆ X.D.carrier → ∀ K : Set L.M, IsCompact K →
            ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ i ≥ N,
              ∀ t ∈ Icc a b,
                metricDerivNormSupOn K p (G i t) (L.S.base.metric t) R < epsilon) := by
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
  have hcarrier : X.D.carrier = Iic 0 := by rw [hD, ancientTimeInterval_carrier]
  have hregular : Iio 0 ⊆ X.D.regular := by rw [hD, ancientTimeInterval_regular]
  have hsol := co.isSolutionOn_of_time_lipschitz Phi hcarrier hregular
    (fun n K hK p => by
      obtain ⟨L, _hL, hb⟩ := hlip n K hK p
      exact hb.mono fun _ hi => ⟨L, hi⟩)
  let L := flowOfMetric X.D P co.gInf hsol
  let Psi : PointedCGHMaps X (L.atTime 0) (mc.subseq ∘ co.φ) :=
    { partialDiffeomorph := (Phi.compSubseq co.φ co.strictMono).partialDiffeomorph
      source_exhausts := (Phi.compSubseq co.φ co.strictMono).source_exhausts
      base_mem := (Phi.compSubseq co.φ co.strictMono).base_mem
      basepoint_map := (Phi.compSubseq co.φ co.strictMono).basepoint_map }
  refine ⟨L, mc.subseq ∘ co.φ, mc.strictMono.comp co.strictMono, Psi, hconnectedP, ?_, ?_, ?_⟩
  · intro t ht
    have ht0 : t ≤ 0 := by simpa only [hcarrier, mem_Iic] using ht
    obtain ⟨c, hc, hb⟩ := hlow (1 - t) (by linarith)
    apply co.metricComplete_of_eventually_lower Phi mc.limit_complete ht0 hc
    intro x v
    filter_upwards [co.strictMono.tendsto_atTop.eventually (hb {x} isCompact_singleton)]
      with i hi
    exact hi t ⟨by linarith, ht0⟩ x (mem_singleton x) v
  · intro t ht
    have ht0 : t ≤ 0 := by simpa only [hcarrier, mem_Iic] using ht
    exact co.exists_canonicalMetricConvergenceData Phi ht0
  · refine ⟨P.metric, (fun i t => G (co.φ i) t), ?_, ?_⟩
    · intro K hK
      exact co.strictMono.tendsto_atTop.eventually (hG K hK)
    · intro a b hab K hK p epsilon hepsilon
      obtain ⟨n, hn⟩ := exists_nat_ge (-a)
      obtain ⟨N, hN⟩ := (co.convergenceOn n).convergence K hK p epsilon hepsilon
      refine ⟨N, fun i hi t ht => hN i hi t ?_⟩
      have ht0 : t ≤ 0 := by simpa only [hcarrier, mem_Iic] using hab ht
      exact ⟨by linarith [ht.1], ht0⟩

theorem exists_local_ancient_flow_compactness
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
    ∃ (L : PointedFlowData.{u, uE, uH} (I := I) X.D) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi,
        (let _ : TopologicalSpace L.M := L.topology
         ConnectedSpace L.M) ∧
        (∀ t ∈ X.D.carrier, MetricComplete (I := I) (L.atTime (I := I) t)) ∧
        ∀ t ∈ X.D.carrier,
          ∃ C : MetricConvergenceData (I := I) (Phi.atTime (L := L) t),
            (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
              (I := I) (Phi.atTime (L := L) t) k) ∧
            (∀ k,
              let D := C.domain k
              let _ : TopologicalSpace
                (MetricSourceDomain (I := I) (Phi.atTime (L := L) t) k) := D.topology
              let _ : ChartedSpace H
                (MetricSourceDomain (I := I) (Phi.atTime (L := L) t) k) := D.charted
              let _ : IsManifold I ∞
                (MetricSourceDomain (I := I) (Phi.atTime (L := L) t) k) := D.smooth
              D.referenceMetric = D.limitMetric) := by
  obtain ⟨L, phi, hphi, Phi, hconn, hcomp, hconv, _⟩ :=
    exists_local_ancient_flow_compactness_with_uniform_metric_convergence
      X hD hcomplete hconnected hinj hlocal hlower
  exact ⟨L, phi, hphi, Phi, hconn, hcomp, hconv⟩

end

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem exists_local_ancient_flow_compactness_form_iff
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) :
    (∃ (L : PointedFlowData.{u, uE, uH} (I := I) X.D) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi,
        (let _ : TopologicalSpace L.M := L.topology
         ConnectedSpace L.M) ∧
        (∀ t ∈ X.D.carrier, MetricComplete (I := I) (L.atTime (I := I) t)) ∧
        ∀ t ∈ X.D.carrier,
          ∃ C : MetricConvergenceData (I := I) (Phi.atTime (L := L) t),
            (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
              (I := I) (Phi.atTime (L := L) t) k) ∧
            (∀ k,
              let D := C.domain k
              let _ : TopologicalSpace
                (MetricSourceDomain (I := I) (Phi.atTime (L := L) t) k) := D.topology
              let _ : ChartedSpace H
                (MetricSourceDomain (I := I) (Phi.atTime (L := L) t) k) := D.charted
              let _ : IsManifold I ∞
                (MetricSourceDomain (I := I) (Phi.atTime (L := L) t) k) := D.smooth
              D.referenceMetric = D.limitMetric)) ↔
    (∃ (L : PointedFlowData.{u, uE, uH} (I := I) X.D) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi,
        (let _ : TopologicalSpace L.M := L.topology
         ConnectedSpace L.M) ∧
        (∀ t ∈ X.D.carrier, MetricComplete (I := I) (L.atTime (I := I) t)) ∧
        ∀ t ∈ X.D.carrier,
          ∃ C : MetricConvergenceData (I := I) (Phi.atTime (L := L) t),
            ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
              (I := I) (Phi.atTime (L := L) t) k) := by
  constructor
  · rintro ⟨L, phi, hphi, Phi, hconn, hcomplete, hconv⟩
    exact ⟨L, phi, hphi, Phi, hconn, hcomplete, fun t ht => by
      obtain ⟨C, hC, _⟩ := hconv t ht
      exact ⟨C, hC⟩⟩
  · rintro ⟨L, phi, hphi, Phi, hconn, hcomplete, hconv⟩
    refine ⟨L, phi, hphi, Phi, hconn, hcomplete, fun t ht => ?_⟩
    obtain ⟨C, hC⟩ := hconv t ht
    refine ⟨C, hC, fun k => ?_⟩
    rw [hC k]
    with_unfolding_all
      rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem exists_metricConvergenceData_canonical_at_all_times_iff
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    (L : PointedFlowData.{u, uE, uH} (I := I) X.D) (phi : ℕ → ℕ)
    (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi) :
    (∀ t ∈ X.D.carrier,
      ∃ C : MetricConvergenceData (I := I)
          (Phi.atTime (X := X) (L := L) (phi := phi) t),
        (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
          (I := I) (Phi.atTime (X := X) (L := L) (phi := phi) t) k) ∧
        (∀ k,
          let D := C.domain k
          let _ : TopologicalSpace
            (MetricSourceDomain (I := I)
              (Phi.atTime (X := X) (L := L) (phi := phi) t) k) := D.topology
          let _ : ChartedSpace H
            (MetricSourceDomain (I := I)
              (Phi.atTime (X := X) (L := L) (phi := phi) t) k) := D.charted
          let _ : IsManifold I ∞
            (MetricSourceDomain (I := I)
              (Phi.atTime (X := X) (L := L) (phi := phi) t) k) := D.smooth
          D.referenceMetric = D.limitMetric)) ↔
    (∀ t ∈ X.D.carrier,
      ∀ K : Set (L.atTime (I := I) t).M,
        (let _ : TopologicalSpace (L.atTime (I := I) t).M := L.topology
         IsCompact K) →
        ∀ p : ℕ, ∀ ε : ℝ, 0 < ε →
          ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
            (CanonicalMetricCompactness.canonicalSourceData (I := I)
              (Phi.atTime (X := X) (L := L) (phi := phi) t) k).derivNormSupOn
                (I := I) K p < ε) := by
  refine forall_congr' (fun t => ?_)
  by_cases ht : t ∈ X.D.carrier
  · simp only [ht, true_implies]
    exact exists_metricConvergenceData_canonicalSourceData_iff (I := I)
      (Phi.atTime (X := X) (L := L) (phi := phi) t)
  · simp only [ht, false_implies]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem exists_local_ancient_flow_compactness_iff_canonical_convergence
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) :
    (∃ (L : PointedFlowData.{u, uE, uH} (I := I) X.D) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi,
        (let _ : TopologicalSpace L.M := L.topology
         ConnectedSpace L.M) ∧
        (∀ t ∈ X.D.carrier, MetricComplete (I := I) (L.atTime (I := I) t)) ∧
        ∀ t ∈ X.D.carrier,
          ∃ C : MetricConvergenceData (I := I) (Phi.atTime (L := L) t),
            (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
              (I := I) (Phi.atTime (L := L) t) k) ∧
            (∀ k,
              let D := C.domain k
              let _ : TopologicalSpace
                (MetricSourceDomain (I := I) (Phi.atTime (L := L) t) k) := D.topology
              let _ : ChartedSpace H
                (MetricSourceDomain (I := I) (Phi.atTime (L := L) t) k) := D.charted
              let _ : IsManifold I ∞
                (MetricSourceDomain (I := I) (Phi.atTime (L := L) t) k) := D.smooth
              D.referenceMetric = D.limitMetric)) ↔
    (∃ (L : PointedFlowData.{u, uE, uH} (I := I) X.D) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi,
        (let _ : TopologicalSpace L.M := L.topology
         ConnectedSpace L.M) ∧
        (∀ t ∈ X.D.carrier, MetricComplete (I := I) (L.atTime (I := I) t)) ∧
        ∀ t ∈ X.D.carrier,
          ∀ K : Set (L.atTime (I := I) t).M,
            (let _ : TopologicalSpace (L.atTime (I := I) t).M := L.topology
             IsCompact K) →
            ∀ p : ℕ, ∀ ε : ℝ, 0 < ε →
              ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
                (CanonicalMetricCompactness.canonicalSourceData (I := I)
                  (Phi.atTime (L := L) t) k).derivNormSupOn (I := I) K p < ε) := by
  constructor
  · rintro ⟨L, phi, hphi, Phi, hconn, hcomplete, hconv⟩
    exact ⟨L, phi, hphi, Phi, hconn, hcomplete,
      (exists_metricConvergenceData_canonical_at_all_times_iff L phi Phi).mp hconv⟩
  · rintro ⟨L, phi, hphi, Phi, hconn, hcomplete, hconv⟩
    exact ⟨L, phi, hphi, Phi, hconn, hcomplete,
      (exists_metricConvergenceData_canonical_at_all_times_iff L phi Phi).mpr hconv⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem exists_local_pointed_metric_compactness_of_ancient_flow_limit
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hD : X.D = ancientTimeInterval)
    (L : PointedFlowData.{u, uE, uH} (I := I) X.D) (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi)
    (hconn : let _ : TopologicalSpace L.M := L.topology; ConnectedSpace L.M)
    (hcomp : ∀ t ∈ X.D.carrier, MetricComplete (I := I) (L.atTime (I := I) t))
    (hconv : ∀ t ∈ X.D.carrier,
      ∃ C : MetricConvergenceData (I := I)
          (Phi.atTime (X := X) (L := L) (phi := phi) t),
        (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
          (I := I) (Phi.atTime (X := X) (L := L) (phi := phi) t) k) ∧
        (∀ k,
          let D := C.domain k
          let _ : TopologicalSpace
            (MetricSourceDomain (I := I)
              (Phi.atTime (X := X) (L := L) (phi := phi) t) k) := D.topology
          let _ : ChartedSpace H
            (MetricSourceDomain (I := I)
              (Phi.atTime (X := X) (L := L) (phi := phi) t) k) := D.charted
          let _ : IsManifold I ∞
            (MetricSourceDomain (I := I)
              (Phi.atTime (X := X) (L := L) (phi := phi) t) k) := D.smooth
          D.referenceMetric = D.limitMetric)) :
    ∃ P : MetricCompactLimit (I := I) (X.atZero (I := I)),
      (∀ k, P.convergence.metrics.domain k =
        CanonicalMetricCompactness.canonicalSourceData (I := I) P.maps k) ∧
      (∀ k,
        let D := P.convergence.metrics.domain k
        let _ : TopologicalSpace (MetricSourceDomain (I := I) P.maps k) := D.topology
        let _ : ChartedSpace H (MetricSourceDomain (I := I) P.maps k) := D.charted
        let _ : IsManifold I ∞ (MetricSourceDomain (I := I) P.maps k) := D.smooth
        D.referenceMetric = D.limitMetric) ∧
      (let _ : TopologicalSpace P.limit.M := P.limit.topology
       ConnectedSpace P.limit.M) := by
  have h0 : (0 : ℝ) ∈ X.D.carrier := by
    simp only [hD, ancientTimeInterval_carrier, Set.mem_Iic, le_refl]
  obtain ⟨C, hC, hrefC⟩ := hconv 0 h0
  let P : MetricCompactLimit (I := I) (X.atZero (I := I)) :=
    ⟨phi, hphi, L.atTime (I := I) 0, hcomp 0 h0,
      Phi.atTime (X := X) (L := L) (phi := phi) 0, ⟨C⟩⟩
  refine ⟨P, ?_, ?_, ?_⟩
  · intro k
    exact hC k
  · intro k
    exact hrefC k
  · exact hconn

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
