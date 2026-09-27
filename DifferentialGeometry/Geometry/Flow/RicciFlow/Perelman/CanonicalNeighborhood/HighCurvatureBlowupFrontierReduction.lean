import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureModelFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedScalarConvergence

set_option autoImplicit false

noncomputable section

open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions (SphereAntipodalQuotient)
open scoped _root_.DifferentialGeometry.Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem highCurvatureFlowSequence_scalar_at_base {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) (i : ℕ) :
    PointedFlowScalarAtBase (I := I3)
      ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term i) 1 := by
  dsimp only [PointedFlowScalarAtBase, highCurvatureFlowSequence_basepoint]
  change (parabolicSolution (I := I3) (M := M) S (t i) (S.scalar (t i) (x i)) (hpos i)
    (htmem i)).scalar 0 (x i) = 1
  have hsol : (parabolicSolution (I := I3) (M := M) S (t i) (S.scalar (t i) (x i)) (hpos i)
      (htmem i)).scalar 0 (x i) =
      (S.scalar (t i) (x i))⁻¹ * S.scalar (parabolicTime (t i) (S.scalar (t i) (x i)) 0)
        (x i) :=
    congrFun (congrFun (parabolicSolution_scalar (I := I3) (M := M) S (t i)
      (S.scalar (t i) (x i)) (hpos i) (htmem i)) 0) (x i)
  rw [hsol]
  rw [show parabolicTime (t i) (S.scalar (t i) (x i)) 0 = t i from by
    dsimp only [parabolicTime]
    ring]
  exact inv_mul_cancel₀ (hpos i).ne'

theorem metricScalar_base_eq_one_of_canonical_metricConvergence
    {X : PointedRiemannianSeq.{u, 0, 0} (I := I3)}
    {L : PointedRiemannianManifold.{u, 0, 0} (I := I3)}
    {phi : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps (I := I3) X L phi)
    (hconv : ∀ K : Set L.M, IsCompact K → metricSourceConvergesOn (I := I3) F
      (CanonicalMetricCompactness.canonicalSourceData (I := I3) F) K 2)
    (hbase : ∀ k, metricScalarAt (I := I3) (X.obj (phi k)).metric
      (X.obj (phi k)).basepoint = 1) :
    metricScalarAt (I := I3) L.metric L.basepoint = 1 := by
  have hlim :=
    DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalar_tendsto_of_canonical_metric_convergence
      (I := I3) (Phi := F) hconv L.basepoint
  have hev : (fun k => metricScalarAt (I := I3) (X.obj (phi k)).metric
      (F.map k L.basepoint)) = fun _ : ℕ => (1 : ℝ) := by
    funext k
    have hmap : F.map k L.basepoint = (X.obj (phi k)).basepoint := F.basepoint_map k
    rw [hmap]
    exact hbase k
  rw [hev] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

theorem pointedFlowScalarAtBase_of_metricConvergence_at_zero {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (L : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval) (phi : ℕ → ℕ)
    (F : PointedRiemannianConvergenceMaps (I := I3)
      ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).atTime 0)
      (L.atTime (I := I3) 0) phi)
    (hconv : ∀ K : Set (L.atTime (I := I3) 0).M, IsCompact K →
      metricSourceConvergesOn (I := I3) F
        (CanonicalMetricCompactness.canonicalSourceData (I := I3) F) K 2) :
    PointedFlowScalarAtBase (I := I3) L 1 := by
  have hbase : ∀ k, metricScalarAt (I := I3)
      (((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).atTime 0).obj (phi k)).metric
      (((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).atTime 0).obj (phi k)).basepoint
        = 1 := by
    intro k
    change PointedFlowScalarAtBase (I := I3)
      ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term (phi k)) 1
    exact highCurvatureFlowSequence_scalar_at_base hT S hS x t htmem htpos hpos (phi k)
  have h := metricScalar_base_eq_one_of_canonical_metricConvergence F hconv hbase
  change PointedFlowScalarAtBase (I := I3) L 1
  exact h

def MaximalPointSlabCompactnessWithoutBaseNormalization {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M) : Prop :=
  ∃ kappa : ℝ, 0 < kappa ∧ ∀ theta : ℝ, 0 < theta →
    ∀ (x : ℕ → M) (t : ℕ → ℝ) (htpos : ∀ i, 0 < t i)
      (htmem0 : ∀ i, t i ∈ Set.Ico (0 : ℝ) T)
      (hpos : ∀ i, 0 < S.scalar (t i) (x i)),
      (∀ i, theta ≤ t i) →
      Filter.Tendsto (fun i => S.scalar (t i) (x i)) Filter.atTop Filter.atTop →
      ∃ (L : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval) (phi : ℕ → ℕ)
        (F : PointedRiemannianConvergenceMaps (I := I3)
          ((highCurvatureFlowSequence hT S hS x t htmem0 htpos hpos).atTime 0)
          (L.atTime (I := I3) 0) phi),
        StrictMono phi ∧ IsAncientKappaSolution (I := I3) kappa L ∧
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

theorem maximalPointSlabCompactness_of_withoutBaseNormalization {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M)
    (h : MaximalPointSlabCompactnessWithoutBaseNormalization.{u} hT S hS o) :
    MaximalPointSlabCompactness.{u} hT S hS o := by
  obtain ⟨kappa, hkpos, hmain⟩ := h
  refine ⟨kappa, hkpos, fun theta htheta x t htpos htmem0 hpos htlower hscalar => ?_⟩
  obtain ⟨L, phi, F, hphi, hanc, hconvT, hcmp, hcap, ori, hor⟩ :=
    hmain theta htheta x t htpos htmem0 hpos htlower hscalar
  obtain ⟨F0, hF0⟩ := hconvT 0 le_rfl
  exact ⟨L, phi, F, hphi, hanc,
    pointedFlowScalarAtBase_of_metricConvergence_at_zero hT S hS x t htmem0 htpos hpos L phi F0 hF0,
    hconvT, hcmp, hcap, ori, hor⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
