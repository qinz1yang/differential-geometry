import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Exponential
open CanonicalNeighborhood
open scoped Manifold ContDiff ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem scalarDecay_edist_ne_top [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (p x : M) :
    riemannianEDistOf (I := I) g p x ≠ ⊤ := by
  let _ : RiemannianBundle (fun y : M => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro y v w; rfl⟩⟩
  exact riemannianEDist_ne_top (I := I) p x

variable [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M]

private local instance scalarDecayIsManifoldOne : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

theorem exists_compact_exceptional_ball_of_scalar_decay
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g) (p : M)
    (hdecay : ∀ eps : ℝ, 0 < eps → ∃ D : ℝ, 0 < D ∧
      ∀ x : M, D ≤ (riemannianEDistOf (I := I) g p x).toReal →
        metricScalarAt (I := I) g x ≤ eps)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ D : ℝ, 0 < D ∧ IsCompact (riemannianClosedBallOf (I := I) g p D) ∧
      ∀ x : M, x ∉ riemannianClosedBallOf (I := I) g p D →
        metricScalarAt (I := I) g x ≤ eps := by
  obtain ⟨D, hD, hfar⟩ := hdecay eps heps
  refine ⟨D, hD, hcomplete.closedEBall_isCompact p D, ?_⟩
  intro x hx
  apply hfar x
  by_contra hdist
  apply hx
  change riemannianEDistOf (I := I) g p x ≤ ENNReal.ofReal D
  calc
    riemannianEDistOf (I := I) g p x =
        ENNReal.ofReal ((riemannianEDistOf (I := I) g p x).toReal) :=
      (ENNReal.ofReal_toReal (scalarDecay_edist_ne_top g p x)).symm
    _ ≤ ENNReal.ofReal D := ENNReal.ofReal_le_ofReal (lt_of_not_ge hdist).le

theorem exists_scalar_decay_compact_and_global_bound
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g) (p : M)
    (hdecay : ∀ eps : ℝ, 0 < eps → ∃ D : ℝ, 0 < D ∧
      ∀ x : M, D ≤ (riemannianEDistOf (I := I) g p x).toReal →
        metricScalarAt (I := I) g x ≤ eps) :
    ∃ D : ℝ, 0 < D ∧ ∃ B : ℝ,
      IsCompact (riemannianClosedBallOf (I := I) g p D) ∧
      (∀ x : M, x ∈ riemannianClosedBallOf (I := I) g p D →
        metricScalarAt (I := I) g x ≤ B) ∧
      (∀ x : M, x ∉ riemannianClosedBallOf (I := I) g p D →
        metricScalarAt (I := I) g x ≤ 1) ∧
      (∀ x : M, metricScalarAt (I := I) g x ≤ max 1 B) := by
  classical
  obtain ⟨D, hD, hcompact, houtside⟩ :=
    exists_compact_exceptional_ball_of_scalar_decay g hcomplete p hdecay (eps := 1) one_pos
  have hcontinuous : Continuous (fun x : M => metricScalarAt (I := I) g x) :=
    (metricScalar_smooth (I := I) g).continuous
  obtain ⟨B, hB⟩ := hcompact.bddAbove_image hcontinuous.continuousOn
  have hinside (x : M) (hx : x ∈ riemannianClosedBallOf (I := I) g p D) :
      metricScalarAt (I := I) g x ≤ B := hB ⟨x, hx, rfl⟩
  refine ⟨D, hD, B, hcompact, hinside, houtside, ?_⟩
  intro x
  by_cases hx : x ∈ riemannianClosedBallOf (I := I) g p D
  · exact (hinside x hx).trans (le_max_right 1 B)
  · exact (houtside x hx).trans (le_max_left 1 B)

theorem metricScalar_bddAbove_of_decay
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g) (p : M)
    (hdecay : ∀ eps : ℝ, 0 < eps → ∃ D : ℝ, 0 < D ∧
      ∀ x : M, D ≤ (riemannianEDistOf (I := I) g p x).toReal →
        metricScalarAt (I := I) g x ≤ eps) :
    BddAbove (Set.range (fun x : M => metricScalarAt (I := I) g x)) := by
  obtain ⟨_D, _hD, B, _hcompact, _hinside, _houtside, hglobal⟩ :=
    exists_scalar_decay_compact_and_global_bound g hcomplete p hdecay
  refine ⟨max 1 B, ?_⟩
  rintro y ⟨x, rfl⟩
  exact hglobal x

theorem metricScalar_sSup_bounds_of_decay
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g) (p : M)
    (hscalar : ∀ x : M, 0 ≤ metricScalarAt (I := I) g x)
    (hdecay : ∀ eps : ℝ, 0 < eps → ∃ D : ℝ, 0 < D ∧
      ∀ x : M, D ≤ (riemannianEDistOf (I := I) g p x).toReal →
        metricScalarAt (I := I) g x ≤ eps) :
    0 ≤ sSup (Set.range (fun x : M => metricScalarAt (I := I) g x)) ∧
      ∀ x : M, metricScalarAt (I := I) g x ≤
        sSup (Set.range (fun y : M => metricScalarAt (I := I) g y)) := by
  have hbounded := metricScalar_bddAbove_of_decay g hcomplete p hdecay
  have hupper (x : M) : metricScalarAt (I := I) g x ≤
      sSup (Set.range (fun y : M => metricScalarAt (I := I) g y)) :=
    le_csSup hbounded ⟨x, rfl⟩
  exact ⟨(hscalar p).trans (hupper p), hupper⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
