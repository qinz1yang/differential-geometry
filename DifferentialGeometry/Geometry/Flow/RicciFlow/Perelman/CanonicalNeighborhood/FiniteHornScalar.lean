import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornRadialNeighborhood
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornStructure
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonScalarCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonComposition

noncomputable section
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W]

theorem metricScalarAt_tendsto_atTop_of_tendsto_endpoint
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g)
    {α : Type v} {l : Filter α} {w : α → W}
    (hw : Filter.Tendsto (fun i => (w i : UniformSpace.Completion W)) l (nhds H.endpoint)) :
    Filter.Tendsto (fun i => metricScalarAt g (w i)) l Filter.atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro C
  obtain ⟨j, hj⟩ := H.curvature_diverges C
  obtain ⟨δ, hδ, hball⟩ := finiteHorn_ball_subset_subend g H j
  filter_upwards [hw.eventually (Metric.ball_mem_nhds H.endpoint hδ)] with i hi
  exact (hj _ (hball _ hi)).le

theorem EndRay.metricScalarAt_tendsto_atTop
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) (a : EndRay H.endpoint)
    {α : Type v} {l : Filter α} {d : α → ℝ}
    (hd : ∀ᶠ i in l, d i ∈ Set.Ioc 0 a.length)
    (hzero : Filter.Tendsto d l (nhds 0)) :
    Filter.Tendsto (fun i => metricScalarAt g (a.point (d i))) l Filter.atTop := by
  apply metricScalarAt_tendsto_atTop_of_tendsto_endpoint H
  apply Metric.tendsto_nhds.2
  intro δ hδ
  filter_upwards [hd, hzero.eventually (eventually_lt_nhds hδ)] with i hi hsmall
  rw [a.radial (d i) hi]
  exact hsmall

attribute [local instance] FiniteHorn.ambientMetric

theorem not_continuousAt_ambient_scalar_extension
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g)
    (f : H.ambient → ℝ) (j : ℕ)
    (hscalar : ∀ w ∈ H.subend j, f (H.inclusion w) = metricScalarAt g w) :
    ¬ ContinuousAt f H.ambientEnd := by
  intro hcont
  let d : ℕ → ℝ := fun i => H.axial.length / ((i : ℝ) + 1)
  have hd : ∀ i, d i ∈ Set.Ioc 0 H.axial.length := by
    intro i
    dsimp [d]
    constructor
    · exact div_pos H.axial.length_pos (by positivity)
    · rw [div_le_iff₀ (by positivity : (0 : ℝ) < (i : ℝ) + 1)]
      nlinarith [H.axial.length_pos, (show (0 : ℝ) ≤ (i : ℝ) from Nat.cast_nonneg i)]
  have hzero : Filter.Tendsto d Filter.atTop (nhds 0) := by
    simpa [d, div_eq_mul_inv, mul_comm, mul_left_comm] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul H.axial.length
  have hpoint : Filter.Tendsto
      (fun i => H.inclusion (H.axial.point (d i)))
      Filter.atTop (nhds H.ambientEnd) := by
    apply Metric.tendsto_nhds.2
    intro δ hδ
    filter_upwards [hzero.eventually (eventually_lt_nhds hδ)] with i hi
    rw [H.ambient_axial (d i) (hd i)]
    exact hi
  have hmem : ∀ᶠ i in Filter.atTop, H.axial.point (d i) ∈ H.subend j := by
    obtain ⟨δ, hδ, _, htail⟩ := H.cofinal_axial j
    filter_upwards [hzero.eventually (eventually_lt_nhds hδ)] with i hi
    exact htail _ ⟨(hd i).1, hi.le⟩
  have hlarge := (H.axial.metricScalarAt_tendsto_atTop H (Filter.Eventually.of_forall hd)
    hzero).eventually_gt_atTop (f H.ambientEnd + 1)
  have hsmall := (hcont.tendsto.comp hpoint).eventually
    (eventually_lt_nhds (show f H.ambientEnd < f H.ambientEnd + 1 by linarith))
  obtain ⟨i, hi, hsc, hmemi⟩ := (hlarge.and (hsmall.and hmem)).exists
  change f (H.inclusion (H.axial.point (d i))) < f H.ambientEnd + 1 at hsc
  rw [hscalar _ hmemi] at hsc
  exact (not_lt_of_ge hi.le) hsc

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact RealizedFiniteHorn.metricSpace
  RealizedFiniteHorn.charted RealizedFiniteHorn.smooth RealizedFiniteHorn.sigmaCompact
  FiniteHorn.ambientMetric

theorem RealizedFiniteHorn.scalar_tendsto {X : FlowSequence.{u}}
    (H : RealizedFiniteHorn X) (x : H.space) :
    Tendsto (fun i => metricScalarAt ((X.term (H.subseq i)).S.base.metric 0) (H.maps i x))
      atTop (nhds (metricScalarAt H.metric x)) := by
  let _ : LocallyCompactSpace H.space := ChartedSpace.locallyCompactSpace ThreeSpace H.space
  obtain ⟨K, hK, hxK⟩ := exists_compact_mem_nhds x
  obtain ⟨U, hUK, hUopen, hxU⟩ := mem_nhds_iff.1 hxK
  let V : TopologicalSpace.Opens H.space := ⟨U, hUopen⟩
  apply tendsto_metricScalarAt_of_comparisons (fun _ => H.metric)
    (fun i _ => (X.term (H.subseq i)).S.base.metric 0) H.maps V
    (s := 0) (times := {0}) (by simp) (order := 2) le_rfl hxU
  · filter_upwards [H.convergence K hK 2 1 one_pos] with i hi
    exact hUK.trans hi.1
  · intro δ hδ
    filter_upwards [H.convergence K hK 2 δ hδ] with i hi
    exact hi.2.map fun C => C.mono hUK le_rfl le_rfl

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness

universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  RealizedFiniteHorn.metricSpace RealizedFiniteHorn.charted RealizedFiniteHorn.smooth
  RealizedFiniteHorn.sigmaCompact

theorem RealizedFiniteHorn.exists_center_scalar_threshold
    {X : FlowSequence.{u}} (H : RealizedFiniteHorn X) (x : ℕ → H.space)
    (hQ : ∀ n, 0 < metricScalarAt H.metric (x n)) (error : ℕ → ℝ)
    (herror : ∀ n, 0 < error n) :
    ∃ threshold : ℕ → ℕ, ∀ n j, threshold n ≤ j →
      |metricScalarAt ((X.term (H.subseq j)).S.base.metric 0) (H.maps j (x n)) /
        metricScalarAt H.metric (x n) - 1| < error n := by
  have hconv (n : ℕ) : Tendsto
      (fun j => metricScalarAt ((X.term (H.subseq j)).S.base.metric 0) (H.maps j (x n)) /
        metricScalarAt H.metric (x n)) atTop (𝓝 1) := by
    simpa only [div_self (hQ n).ne'] using (H.scalar_tendsto (x n)).div_const
      (metricScalarAt H.metric (x n))
  have hbound : ∀ n, ∃ threshold : ℕ, ∀ j, threshold ≤ j →
      |metricScalarAt ((X.term (H.subseq j)).S.base.metric 0) (H.maps j (x n)) /
        metricScalarAt H.metric (x n) - 1| < error n := by
    intro n
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hconv n) (error n) (herror n)
    exact ⟨N, fun j hj => by simpa only [Real.dist_eq] using hN j hj⟩
  choose threshold hthreshold using hbound
  exact ⟨threshold, hthreshold⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
