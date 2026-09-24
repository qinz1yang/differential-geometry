import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.ReferenceGeodesicBounds
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.PullbackLocalIso
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PointedPullbackExtensions

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped Manifold ContDiff Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
  {subseq : ℕ → ℕ}

theorem FlowMetricConvergenceData.exists_eventually_mapped_reference_geodesic_acceleration_bound
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    {a b : ℝ} (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt a b)
    (hG : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      MetricFamilySmoothOn X.D co.gInf)
    (hreg : Icc a b ⊆ X.D.regular)
    {K : Set P.M} (hK : letI : TopologicalSpace P.M := P.topology; IsCompact K) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ k ≥ N,
      letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      letI : ChartedSpace H (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).charted
      letI : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).smooth
      ∀ t ∈ Icc a b, ∀ (beta : ℝ → P.M) (r : ℝ),
        beta r ∈ K → IsGeodesicAt R beta r →
        let g := (X.term (subseq (co.φ k))).S.base.metric t
        let betaMap := fun s ↦ Φ.map (co.φ k) (beta s)
        Real.sqrt (g.inner (betaMap r)
          (covDerivAlong g betaMap (fun s ↦ mfderiv 𝓘(ℝ, ℝ) I betaMap s 1) r)
          (covDerivAlong g betaMap (fun s ↦ mfderiv 𝓘(ℝ, ℝ) I betaMap s 1) r)) ≤
            C * R.inner (beta r)
              (mfderiv 𝓘(ℝ, ℝ) I beta r 1) (mfderiv 𝓘(ℝ, ℝ) I beta r 1) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨C, hC, N₁, hN₁⟩ :=
    FlowMetricConvergenceData.exists_eventually_reference_geodesic_acceleration_bound
      Φ R bf hsrc htgt co hG hreg hK
  have hevent := co.strictMono.tendsto_atTop.eventually
    (DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eventually_gSeqExt_eq_pullback
      Φ R bf hsrc htgt K hK)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hevent
  refine ⟨C, hC, max N₁ N₂, ?_⟩
  intro k hk
  let : TopologicalSpace (X.term (subseq (co.φ k))).M :=
    (X.term (subseq (co.φ k))).topology
  let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
    (X.term (subseq (co.φ k))).charted
  let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
    (X.term (subseq (co.φ k))).smooth
  let : T2Space (X.term (subseq (co.φ k))).M :=
    (X.term (subseq (co.φ k))).t2
  intro t ht beta r hbetaK hbeta
  obtain ⟨U, hU, hKU, hUs, hmetric⟩ := hN₂ k ((le_max_right _ _).trans hk)
  have hf : IsLocalDiffeomorphOn I I ∞ (Φ.map (co.φ k)) U := by
    intro x
    exact (Φ.partialDiffeomorph (co.φ k)).isLocalDiffeomorphAt I I ∞ (hUs x.2)
  have hnorm := covDerivAlong_velocity_norm_map_of_local_isometry_on
    (gSeqExt Φ R bf hsrc htgt (co.φ k) t)
    ((X.term (subseq (co.φ k))).S.base.metric t) hU hf (hmetric t)
    beta (hKU hbetaK) (DifferentialGeometry.Geometry.contMDiffAt_of_isGeodesicAt hbeta)
  exact hnorm.le.trans (hN₁ k ((le_max_left _ _).trans hk) t ht beta r hbetaK hbeta)

end DifferentialGeometry.CheegerGromovCompactness
