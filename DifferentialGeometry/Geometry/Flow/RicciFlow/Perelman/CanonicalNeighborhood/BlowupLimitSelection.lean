import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureModelFrontier

set_option autoImplicit false

noncomputable section

open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem highCurvatureFlowSequence_scalar_base_one {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) (i : ℕ) :
    PointedFlowScalarAtBase (I := I3)
      ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term i) 1 := by
  have hmain : (parabolicSolution (I := I3) (M := M) S (t i) (S.scalar (t i) (x i))
      (hpos i) (htmem i)).scalar 0 (x i) = 1 := by
    have h1 := congrFun (congrFun (parabolicSolution_scalar (I := I3) (M := M) S (t i)
      (S.scalar (t i) (x i)) (hpos i) (htmem i)) 0) (x i)
    have h2 : (parabolicSolution (I := I3) (M := M) S (t i) (S.scalar (t i) (x i))
        (hpos i) (htmem i)).scalar 0 (x i) =
        (S.scalar (t i) (x i))⁻¹ * S.scalar (t i) (x i) := by
      simpa only [parabolicTime_zero] using h1
    exact h2.trans (inv_mul_cancel₀ (ne_of_gt (hpos i)))
  change ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term i).S.scalar 0
    ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term i).basepoint = 1
  exact hmain

def BlowupLimitSelection {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M) (kappa : ℝ) : Prop :=
  ∀ theta : ℝ, 0 < theta →
    ∀ (x : ℕ → M) (t : ℕ → ℝ) (htpos : ∀ i, 0 < t i)
      (htmem0 : ∀ i, t i ∈ Set.Ico (0 : ℝ) T)
      (hpos : ∀ i, 0 < S.scalar (t i) (x i)),
      ∃ (L : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval) (phi : ℕ → ℕ)
        (F : PointedRiemannianConvergenceMaps (I := I3)
          ((highCurvatureFlowSequence hT S hS x t htmem0 htpos hpos).atTime 0)
          (L.atTime (I := I3) 0) phi),
        StrictMono phi ∧
        (letI : TopologicalSpace L.M := L.topology; ConnectedSpace L.M) ∧
        (∀ t' ∈ ancientTimeInterval.carrier,
          MetricComplete (I := I3) (L.atTime (I := I3) t')) ∧
        (∀ t' ∈ ancientTimeInterval.carrier,
          PointedFlowNonnegativeCurvatureOperator (I := I3) L t') ∧
        (∃ C : ℝ, PointedFlowScalarBounded (I := I3) L C) ∧
        PointedFlowNoncollapsedAllScales (I := I3) L kappa ∧
        (∀ t' : ℝ, t' ≤ 0 →
          ∃ Ft : PointedRiemannianConvergenceMaps (I := I3)
            ((highCurvatureFlowSequence hT S hS x t htmem0 htpos hpos).atTime t')
            (L.atTime (I := I3) t') phi,
            ∀ K : Set L.M, IsCompact K → metricSourceConvergesOn (I := I3) Ft
              (CanonicalMetricCompactness.canonicalSourceData (I := I3) Ft) K 2) ∧
        (∀ K : Set L.M, IsCompact K → ∀ A : ℝ, 0 < A →
          ∀ order : ℕ, ∀ eta : ℝ, 0 < eta → ∀ᶠ i in Filter.atTop,
            K ⊆ (F.partialDiffeomorph i).source ∧
            Nonempty (MetricComparisonOn (fun s => L.S.base.metric s)
              (fun s =>
                ((highCurvatureFlowSequence hT S hS x t htmem0 htpos hpos).term
                  (phi i)).S.base.metric s)
              (F.partialDiffeomorph i) K (Set.Icc (-A) 0) order eta)) ∧
        (∀ r : ℝ, 0 < r → ∀ᶠ i in Filter.atTop,
          riemannianBallOf (I := I3)
              (rescaledMetric S (t (phi i)) (S.scalar (t (phi i)) (x (phi i)))
                (hpos (phi i)) 0) (x (phi i)) r ⊆
            (fun a => F.partialDiffeomorph i a) '' (F.partialDiffeomorph i).source) ∧
        (∃ ori : TangentOrientationSection L.M, ∀ i y,
          y ∈ (F.partialDiffeomorph i).source →
          ∃ hf : Function.Bijective (mfderiv I3 I3 (F.partialDiffeomorph i) y),
            PreservesTangentOrientationAt ori o (F.partialDiffeomorph i) y hf)

theorem pointedFlowScalarAtBase_one_of_canonicalMetricSourceConverges {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    {L : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval} {phi : ℕ → ℕ}
    {F : PointedRiemannianConvergenceMaps (I := I3)
      ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).atTime 0)
      (L.atTime (I := I3) 0) phi}
    (hconv : ∀ K : Set L.M, IsCompact K → metricSourceConvergesOn (I := I3) F
      (CanonicalMetricCompactness.canonicalSourceData (I := I3) F) K 2) :
    PointedFlowScalarAtBase (I := I3) L 1 := by
  have hlim :=
    DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalar_tendsto_of_canonical_metric_convergence
      (I := I3)
      (X := (highCurvatureFlowSequence hT S hS x t htmem htpos hpos).atTime 0)
      (L := L.atTime (I := I3) 0) (subseq := phi) (Phi := F) hconv L.basepoint
  have hconst : ∀ k : ℕ, metricScalarAt (I := I3)
      (((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).atTime 0).obj
        (phi k)).metric (F.map k L.basepoint) = 1 := by
    intro k
    have hmap : F.map k L.basepoint =
        (((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).atTime 0).obj
          (phi k)).basepoint := by
      simpa only [PointedRiemannianConvergenceMaps.map, PointedFlowData.atTime]
        using F.basepoint_map k
    rw [hmap]
    exact highCurvatureFlowSequence_scalar_base_one hT S hS x t htmem htpos hpos (phi k)
  rw [funext hconst] at hlim
  have hone : metricScalarAt (I := I3) (L.atTime (I := I3) 0).metric L.basepoint = 1 :=
    (tendsto_nhds_unique tendsto_const_nhds hlim).symm
  change L.S.scalar 0 L.basepoint = 1
  simpa only [PointedFlowData.atTime, SolutionOn.family_metric, SolutionOn.scalar,
    SolutionFamily.scalar] using hone

theorem maximalPointSlabCompactness_of_blowupLimitSelection {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M) {kappa : ℝ} (hkappa : 0 < kappa)
    (h : BlowupLimitSelection hT S hS o kappa) :
    MaximalPointSlabCompactness hT S hS o := by
  refine ⟨kappa, hkappa, fun theta htheta x t htpos htmem0 hpos => ?_⟩
  obtain ⟨L, phi, F, hphi, hconn, hcomplete, hnonneg, hscalar, hnoncoll, hconvT, hcmp,
    hcap, ori, hori⟩ := h theta htheta x t htpos htmem0 hpos
  obtain ⟨Ft, hFt⟩ := hconvT 0 le_rfl
  have hbase : PointedFlowScalarAtBase (I := I3) L 1 :=
    pointedFlowScalarAtBase_one_of_canonicalMetricSourceConverges hT S hS x t htmem0 htpos
      hpos hFt
  have hzero : (0 : ℝ) ∈ ancientTimeInterval.carrier := by
    rw [ancientTimeInterval_carrier]
    exact Set.mem_Iic.mpr le_rfl
  refine ⟨L, phi, F, hphi, ?_, hbase, hconvT, hcmp, hcap, ori, hori⟩
  exact { kappa_pos := hkappa
          carrier_eq := rfl
          regular_eq := rfl
          connected := hconn
          complete := hcomplete
          nonnegativeCurvatureOperator := hnonneg
          globalScalarBound := hscalar
          noncollapsed := hnoncoll
          notFlat := pointedFlowNotFlat_of_scalar_ne_zero (I := I3) L hzero L.basepoint (by
            have h1 : L.S.scalar 0 L.basepoint = 1 := hbase
            rw [h1]
            norm_num) }

theorem exists_blowupLimitSelection_of_maximalPointSlabCompactness {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M)
    (h : MaximalPointSlabCompactness hT S hS o) :
    ∃ kappa : ℝ, 0 < kappa ∧ BlowupLimitSelection hT S hS o kappa := by
  obtain ⟨kappa', hkpos', hmain⟩ := h
  exact ⟨kappa', hkpos', fun theta htheta x t htpos htmem0 hpos => by
    obtain ⟨L, phi, F, hphi, hanc, hbase, hconvT, hcmp, hcap, ori, hori⟩ :=
      hmain theta htheta x t htpos htmem0 hpos
    exact ⟨L, phi, F, hphi, hanc.connected, hanc.complete, hanc.nonnegativeCurvatureOperator,
      hanc.globalScalarBound, hanc.noncollapsed, hconvT, hcmp, hcap, ori, hori⟩⟩

theorem maximalPointSlabCompactness_iff_exists_blowupLimitSelection {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M) :
    MaximalPointSlabCompactness hT S hS o ↔
      ∃ kappa : ℝ, 0 < kappa ∧ BlowupLimitSelection hT S hS o kappa := by
  constructor
  · intro h
    exact exists_blowupLimitSelection_of_maximalPointSlabCompactness hT S hS o h
  · rintro ⟨kappa, hkappa, h⟩
    exact maximalPointSlabCompactness_of_blowupLimitSelection hT S hS o hkappa h

theorem maximal_point_singularity_model_of_blowupLimitSelection
    [CompactSpace M] [ConnectedSpace M] [T2Space (TangentBundle I3 M)] {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M) {kappa : ℝ} (hkappa : 0 < kappa)
    (h : BlowupLimitSelection hT S hS o kappa) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ theta : ℝ, 0 < theta →
      ∀ (x : ℕ → M) (t : ℕ → ℝ), (∀ i, t i ∈ Set.Ico theta T) →
        (∀ i s, s ∈ Set.Icc 0 (t i) → ∀ y, S.scalar s y ≤ S.scalar (t i) (x i)) →
        Filter.Tendsto (fun i => S.scalar (t i) (x i)) Filter.atTop Filter.atTop →
        ∃ L : BlowupLimit S o kappa x t, PointedFlowScalarBounded L.model 1 :=
  maximal_point_singularity_model_of_maximalPointSlabCompactness hT S hS o
    (maximalPointSlabCompactness_of_blowupLimitSelection hT S hS o hkappa h)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
