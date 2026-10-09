import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.ForwardDistance
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.FixedDomain
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Metric.Proper
import DifferentialGeometry.Geometry.Metric.Convergence.Locality
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.BoundedGeometryCanonical
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.CompactGlobalization
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.MetricSeq

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set Filter
open scoped Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

theorem riemannianEDistOf_limit_le_of_source_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
    {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    (C : MetricConvergenceData (I := I) Φ)
    (hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete (I := I) L) [ConnectedSpace L.M] (D : ℝ)
    (hdiam : ∀ k (x y : (X.obj (subseq k)).M),
      riemannianEDistOf (I := I) (X.obj (subseq k)).metric x y ≤ ENNReal.ofReal D)
    (q r : L.M) :
    riemannianEDistOf (I := I) L.metric q r ≤ ENNReal.ofReal D := by
  obtain ⟨P⟩ := exists_proper_metric_on (I := I) L hcomplete inferInstance
  have hne : riemannianEDistOf (I := I) L.metric q r ≠ ⊤ := by
    have hreal := P.realizes q r
    change riemannianEDistOf (I := I) L.metric q r = _ at hreal
    rw [hreal]
    exact ENNReal.ofReal_ne_top
  have htend :=
    PDE.RicciFlow.Perelman.KappaSolutions.tendsto_pointed_map_distance C hreference hcomplete q r
  have hle : (riemannianEDistOf (I := I) L.metric q r).toReal ≤ max D 0 := by
    refine le_of_tendsto' htend (fun k => ?_)
    exact ENNReal.toReal_le_of_le_ofReal (le_max_right D 0)
      ((hdiam k _ _).trans (ENNReal.ofReal_le_ofReal (le_max_left D 0)))
  calc riemannianEDistOf (I := I) L.metric q r
      = ENNReal.ofReal (riemannianEDistOf (I := I) L.metric q r).toReal :=
        (ENNReal.ofReal_toReal hne).symm
    _ ≤ ENNReal.ofReal (max D 0) := ENNReal.ofReal_le_ofReal hle
    _ = ENNReal.ofReal D := by
        rw [ENNReal.ofReal_max, ENNReal.ofReal_zero]
        exact max_eq_left bot_le

theorem compactSpace_limit_of_source_edist_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
    {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    (C : MetricConvergenceData (I := I) Φ)
    (hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete (I := I) L) [ConnectedSpace L.M] (D : ℝ)
    (hdiam : ∀ k (x y : (X.obj (subseq k)).M),
      riemannianEDistOf (I := I) (X.obj (subseq k)).metric x y ≤ ENNReal.ofReal D) :
    CompactSpace L.M := by
  obtain ⟨P⟩ := exists_proper_metric_on (I := I) L hcomplete inferInstance
  have hK := ProperMetricOn.isCompact_riemannianClosedBallOf L P L.basepoint D
  refine ⟨hK.of_isClosed_subset isClosed_univ (fun x _ => ?_)⟩
  exact riemannianEDistOf_limit_le_of_source_le C hreference hcomplete D hdiam L.basepoint x

omit [NeZero (Module.finrank ℝ E)] in
theorem metricCInfConvergenceOnCompacts_whole_pullback_of_canonical
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq)
    (C : MetricConvergenceData (I := I) Φ)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Φ k)
    (N : ℕ) (hsource : ∀ k, Φ.source (k + N) = Set.univ)
    (e : ∀ k, L.M ≃ₘ⟮I, I⟯ (X.obj (subseq (k + N))).M)
    (he : ∀ k x, e k x = Φ.map (k + N) x) :
    MetricCInfConvergenceOnCompacts (I := I)
      (fun k => Diffeomorph.pullbackMetricCross (X.obj (subseq (k + N))).metric (e k))
      L.metric L.metric := by
  let U : TopologicalSpace.Opens L.M := ⊤
  have hσ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  have hU : ∀ k, (U : Set L.M) ⊆ (Φ.partialDiffeomorph (k + N)).source := by
    intro k x _
    change x ∈ Φ.source (k + N)
    rw [hsource k]
    exact mem_univ x
  have hconvU := metricCInfConvergenceOnCompacts_of_pointed_pullback Φ C hcanonical U N hU
    (fun k => (Diffeomorph.pullbackMetricCross (X.obj (subseq (k + N))).metric (e k)).restrictOpen U)
    (by
      intro k x v w
      have hfun : (e k : L.M → (X.obj (subseq (k + N))).M) =
          fun y => Φ.partialDiffeomorph (k + N) y := funext (he k)
      have h1 := Diffeomorph.pullbackMetricCross_inner (X.obj (subseq (k + N))).metric (e k)
        (x : L.M) v w
      rw [hfun] at h1
      exact h1)
  exact metricCInfConvergenceOnCompacts_of_restrict_open_cover (fun _ : Unit => U)
    (fun _ => ⟨(), trivial⟩) _ _ _ (fun _ => hconvU)

theorem exists_compact_whole_pullback_gauge
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
    (p : M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hcomplete : SeqMetricComplete (I := I) (pointedMetricSeq p gSeq))
    (hgeom : SeqBoundedGeometry (I := I) (pointedMetricSeq p gSeq))
    (hinj : BaseInjBound (I := I) (pointedMetricSeq p gSeq))
    (D : ℝ)
    (hdiam : ∀ n (x y : M), riemannianEDistOf (I := I) (gSeq n) x y ≤ ENNReal.ofReal D) :
    ∃ (L : PointedRiemannianManifold.{u, uE, uH} (I := I)) (f : ℕ → ℕ), StrictMono f ∧
      (letI : TopologicalSpace L.M := L.topology
       letI : ChartedSpace H L.M := L.charted
       letI : IsManifold I ∞ L.M := L.smooth
       letI : SigmaCompactSpace L.M := L.sigmaCompact
       letI : T2Space L.M := L.t2
       CompactSpace L.M ∧ ConnectedSpace L.M ∧
         ∃ e : ℕ → Diffeomorph I I L.M M ∞,
           MetricCInfConvergenceOnCompacts (I := I)
             (fun n => Diffeomorph.pullbackMetricCross (gSeq (f n)) (e n))
             L.metric L.metric) := by
  obtain ⟨P, hdom, href, hconn⟩ := exists_canonical_metric_compactness_of_boundedGeometry
    (pointedMetricSeq p gSeq) hcomplete (fun _ => (inferInstance : ConnectedSpace M)) hgeom hinj
  have hconnL : ConnectedSpace P.limit.M := hconn
  have hcpt : CompactSpace P.limit.M :=
    compactSpace_limit_of_source_edist_le P.convergence.metrics href P.limit_complete D
      (fun k x y => hdiam (P.subseq k) x y)
  obtain ⟨k0, hk0⟩ := PDE.RicciFlow.Perelman.KappaSolutions.compactLimit_eventually_globalizes
    P.maps hcpt (fun _ => (inferInstance : ConnectedSpace M))
  have hex : ∀ n : ℕ, ∃ e : P.limit.M ≃ₘ⟮I, I⟯ M, ∀ x, e x = P.maps.map (n + k0) x := by
    intro n
    obtain ⟨-, -, e, he, -⟩ := hk0 (n + k0) (Nat.le_add_left k0 n)
    exact ⟨e, he⟩
  choose e he using hex
  have hsource : ∀ n : ℕ, P.maps.source (n + k0) = univ :=
    fun n => (hk0 (n + k0) (Nat.le_add_left k0 n)).1
  refine ⟨P.limit, fun n => P.subseq (n + k0),
    P.strictMono.comp (fun a b hab => Nat.add_lt_add_right hab k0), hcpt, hconnL, e, ?_⟩
  exact metricCInfConvergenceOnCompacts_whole_pullback_of_canonical P.maps P.convergence.metrics
    hdom k0 hsource e he

end DifferentialGeometry.CheegerGromovCompactness

end
