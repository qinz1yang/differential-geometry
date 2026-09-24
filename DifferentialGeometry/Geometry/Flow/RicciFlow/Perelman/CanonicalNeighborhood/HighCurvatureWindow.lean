import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.WindowCompactnessProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureSequenceEstimates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureInjectivity

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

private theorem atTime_cast {D D' : RealTimeInterval} (h : D = D')
    (F : PointedFlowData.{u, 0, 0} I3 D) (s : ℝ) :
    (h ▸ F).atTime s = F.atTime s := by
  cases h
  rfl

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]

@[simp] theorem highCurvatureArcSeq_atTime [SigmaCompactSpace M] {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) (i : ℕ) (s : ℝ) :
    ((highCurvatureArcSeq hT S hS x t htmem htpos hpos).term i).atTime s =
      ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term i).atTime s := by
  exact atTime_cast (highCurvatureInterval_eq_arcInterval hT S x t htpos hpos i) _ s


theorem exists_highCurvatureArcSeq_window_estimates [CompactSpace M] [ConnectedSpace M]
    [T2Space (TangentBundle I3 M)] {T theta A : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (hmax : ∀ i s, s ∈ Icc 0 (t i) → ∀ y : M,
      S.scalar s y ≤ S.scalar (t i) (x i))
    (htheta : 0 < theta) (htlower : ∀ᶠ i in atTop, theta ≤ t i)
    (hscalar : Tendsto (fun i => S.scalar (t i) (x i)) atTop atTop) (hA : 0 < A) :
    ∃ N : ℕ, ∃ hcov : ∀ k,
        A ≤ ((highCurvatureArcSeq hT S hS x t htmem htpos hpos).tail N).horizon k,
      Nonempty (WindowCompactnessEstimates
        ((highCurvatureArcSeq hT S hS x t htmem htpos hpos).tail N) A hA hcov) ∧
      ∀ k m : ℕ, ∀ s ∈ Icc (-A) 0,
        ∀ y : ((((highCurvatureArcSeq hT S hS x t htmem htpos hpos).tail N).window
            A hA hcov).term k).M,
          curvDerivNorm (I := I3) m
            (((((highCurvatureArcSeq hT S hS x t htmem htpos hpos).tail N).window
              A hA hcov).term k).S.base.metric s) y ≤
            shiLocalUniformBound 3 m 16 4 * 16 := by
  let X := highCurvatureArcSeq hT S hS x t htmem htpos hpos
  obtain ⟨rho, hrho, hinj⟩ := highCurvatureFlowSequence_hasInjRadiusAt_eventually
    hT S hS x t htmem htpos hpos hmax hscalar
  have hwindow := high_curvature_interval_eventually_contains_closed_window
    hT S x t htpos hpos htheta htlower hscalar A
  have hrm := highCurvatureFlowSequence_rmNormSq_eventually_le_of_past_scalar_maximum
    hT S hS x t htmem htpos hpos hmax hscalar
  have hspatial := highCurvatureFlowSequence_curvDerivNorm_eventually_le_on_closed_window
    hT S hS x t htmem htpos hpos hmax htheta htlower hscalar A
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hwindow.and (hrm.and (hinj.and hspatial)))
  have hcov : ∀ k, A ≤ (X.tail N).horizon k := by
    intro k
    have h := ((hN (k + N) (Nat.le_add_left _ _)).1.1
      (show -A ∈ Icc (-A) 0 from ⟨le_rfl, neg_nonpos.mpr hA.le⟩)).1
    change A ≤ t (k + N) * S.scalar (t (k + N)) (x (k + N))
    linarith
  let Y := (X.tail N).window A hA hcov
  have htime (k : ℕ) (s : ℝ) :
      (Y.term k).atTime s =
        ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term (k + N)).atTime s := by
    exact highCurvatureArcSeq_atTime hT S hS x t htmem htpos hpos (k + N) s
  refine ⟨N, hcov, ?_, ?_⟩
  · refine ⟨{ complete := ?_, curvature := ?_, injectivity := ?_, connected := ?_ }⟩
    · refine ⟨fun k s hs => ?_⟩
      change MetricComplete ((Y.term k).atTime s)
      rw [htime]
      exact (RiemannianMetricComplete.of_compact
        (rescaledMetric S (t (k + N)) (S.scalar (t (k + N)) (x (k + N)))
          (hpos (k + N)) s)).complete
    · refine ⟨fun a b hab => ⟨243, by norm_num, fun k s hs => ?_⟩⟩
      let rmBound (P : PointedRiemannianManifold.{u, 0, 0} I3) : Prop :=
        ∀ y : P.M, Tensor0SBundle.normSq0S (I := I3) P.metric y 4
          (metricRm04At P.metric y) ≤ 243
      change rmBound ((Y.term k).atTime s)
      rw [htime]
      have hsi : s ∈ Icc (-A) 0 := by
        have h := hab hs
        change s ∈ (arcInterval A).carrier at h
        rwa [arcInterval_carrier hA] at h
      exact (hN (k + N) (Nat.le_add_left _ _)).2.1 s
        ((hN (k + N) (Nat.le_add_left _ _)).1.1 hsi)
    · refine ⟨rho, hrho, fun k => ?_⟩
      change HasInjRadiusAt ((Y.term k).atTime 0) (((Y.term k).atTime 0).basepoint) rho
      rw [htime]
      exact (hN (k + N) (Nat.le_add_left _ _)).2.2.1 _
    · intro k
      change @ConnectedSpace ((Y.term k).atTime 0).M ((Y.term k).atTime 0).topology
      rw [htime]
      exact ‹ConnectedSpace M›
  · intro k m s hs
    let derivBound (P : PointedRiemannianManifold.{u, 0, 0} I3) : Prop :=
      ∀ y : P.M, curvDerivNorm (I := I3) m P.metric y ≤
        shiLocalUniformBound 3 m 16 4 * 16
    change derivBound ((Y.term k).atTime s)
    rw [htime]
    exact (hN (k + N) (Nat.le_add_left _ _)).2.2.2 m s hs

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
