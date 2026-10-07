import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84PrefixTransfer_S74
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84Sub86Top_O12
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroLowPoint_S33

/-!
# CH12-S87 G1: the top scalar bound of `hsub86N` on the tower history over the whole prefix

`canonical_prefix_neck_S87`: `Hp.canonical` (with the cap-tube neck chart) on
`N.stageMetric (N.activeStage v) v`, `v ≤ s.time`, `N := sliceTowerHistory_CX2 s`
(the neck chart is what `scalar_le_of_almost_euclidean_O10` needs; `canonical_prefix_S74` drops it).
`top_scalar_le_S87`: vol premise at `r0/2` ⇒ `R(x0) ≤ 4A/r0²` at the active stage metric at `u ≤ s.time`.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

theorem slice_canonical_neck_S87 {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}
    (Hp : AnalyticSurgeryProfile F δ) (s : RegularSlice F.observation)
    (v : Icc (0 : ℝ) s.history.horizon) :
    ∀ x, (Hp.parameters.neckRadius v ^ 2)⁻¹ <
        metricScalarAt (s.history.stageMetric (s.history.activeStage v) v) x →
      ∃ W : SpatialCanonicalWitness (s.history.stageMetric (s.history.activeStage v) v)
        Hp.epsilon Hp.C1 Hp.C2 x, W.capTubeHasNeckChart Hp.epsilon := by
  have hv0 : (0 : ℝ) ≤ v := v.2.1
  have hvs : (v : ℝ) ≤ s.time := v.2.2
  let t : Icc (0 : ℝ) (v : ℝ) := ⟨v, hv0, le_rfl⟩
  have hst := F.observation.observe_slice_stage v s.time hv0 s.positive.le hvs t
  have hmet := F.observation.observe_slice_metric v s.time hv0 s.positive.le hvs t
  obtain ⟨hs0, hm0⟩ := postData_observe_O3 F.observation v hv0
  have hlast : (F.observation.observe v hv0).activeStage t =
      Fin.last (F.observation.observe v hv0).eventCount :=
    (F.observation.observe v hv0).activeStage_at_horizon
  have hst' : postStage F.observation v = s.history.stageAt v := by
    refine hs0.trans ?_
    have h1 : (F.observation.observe v hv0).stageAt t =
        (F.observation.observe v hv0).stage (Fin.last _) := by
      change (F.observation.observe v hv0).stage ((F.observation.observe v hv0).activeStage t) = _
      rw [hlast]
    exact h1.symm.trans hst
  have hm' : HEq (postMetric F.observation v)
      (s.history.stageMetric (s.history.activeStage v) v) := by
    refine hm0.trans ?_
    refine (stageMetric_heq_of_index_eq_O3 _ hlast.symm (v : ℝ)).trans ?_
    exact hmet
  exact stageMetric_transport_O3 hst' hm'
    (fun Q m => ∀ x : Q.Carrier, (Hp.parameters.neckRadius v ^ 2)⁻¹ < metricScalarAt m x →
      ∃ W : SpatialCanonicalWitness m Hp.epsilon Hp.C1 Hp.C2 x, W.capTubeHasNeckChart Hp.epsilon)
    (fun x hx => Hp.canonical v hv0 x hx)

theorem canonical_prefix_neck_S87 {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}
    (Hp : AnalyticSurgeryProfile F δ) (s : RegularSlice F.observation)
    (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hvs : (v : ℝ) ≤ s.time) :
    ∀ x : ((sliceTowerHistory_CX2 s).stage ((sliceTowerHistory_CX2 s).activeStage v)).Carrier,
      (Hp.parameters.neckRadius v ^ 2)⁻¹ <
        metricScalarAt ((sliceTowerHistory_CX2 s).stageMetric
          ((sliceTowerHistory_CX2 s).activeStage v) v) x →
      ∃ W : SpatialCanonicalWitness ((sliceTowerHistory_CX2 s).stageMetric
        ((sliceTowerHistory_CX2 s).activeStage v) v) Hp.epsilon Hp.C1 Hp.C2 x,
        W.capTubeHasNeckChart Hp.epsilon := by
  obtain ⟨v1, h0, h1⟩ := v
  set N := sliceTowerHistory_CX2 s
  set cut := sliceTowerTime_CX2 s
  let v' : Icc (0 : ℝ) s.history.horizon := ⟨v1, h0, hvs⟩
  have hst : s.history.stage (s.history.activeStage v') =
      N.stage (N.activeStage (restrictTime_CX2 N cut v')) := N.restrict_stageAt cut v'
  have hm : HEq (s.history.stageMetric (s.history.activeStage v') v')
      (N.stageMetric (N.activeStage (restrictTime_CX2 N cut v')) (restrictTime_CX2 N cut v')) :=
    N.restrict_sliceMetric cut v'
  exact stageMetric_transport_O3 hst hm
    (fun Q m => ∀ x : Q.Carrier, (Hp.parameters.neckRadius v1 ^ 2)⁻¹ < metricScalarAt m x →
      ∃ W : SpatialCanonicalWitness m Hp.epsilon Hp.C1 Hp.C2 x, W.capTubeHasNeckChart Hp.epsilon)
    (slice_canonical_neck_S87 Hp s v')

/-- The top scalar bound of `hsub86N`: Euclidean volume premise on the `r0/2`-subballs of `B(x0,r0/2)`
gives `R(x0) ≤ 4A/r0²` (`A` from `scalar_le_of_almost_euclidean_O10`; any `ε ≤ 3/4`). -/
theorem top_scalar_le_S87 {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}
    (Hp : AnalyticSurgeryProfile F δ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (s : RegularSlice F.observation)
      (u : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon), (u : ℝ) ≤ s.time →
      ∀ (x0 : ((sliceTowerHistory_CX2 s).stageAt u).Carrier) {r0 : ℝ}, 0 < r0 →
        r0 ≤ Hp.parameters.neckRadius u → ∀ {ε : ℝ}, ε ≤ 3 / 4 →
        (∀ z ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) x0 (r0 / 2),
          ∀ ρ : ℝ, 0 < ρ → ρ ≤ r0 / 2 →
            ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤
              ballVolume ((sliceTowerHistory_CX2 s).stageMetric
                ((sliceTowerHistory_CX2 s).activeStage u) u) z ρ) →
        metricScalarAt ((sliceTowerHistory_CX2 s).stageMetric
          ((sliceTowerHistory_CX2 s).activeStage u) u) x0 ≤ 4 * A / r0 ^ 2 := by
  obtain ⟨A, hA, hS⟩ := scalar_le_of_almost_euclidean_O10.{u} Hp.C1 Hp.C2
  refine ⟨A, hA, fun s u hus x0 r0 hr0 hrad ε hε hEuc => ?_⟩
  have hg : RiemannianMetricComplete (I := I3) ((sliceTowerHistory_CX2 s).stageMetric
      ((sliceTowerHistory_CX2 s).activeStage u) u) :=
    RiemannianMetricComplete.of_compact _
  have h := hS ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage u) u)
    hg Hp.epsilon_small
    ((Hp.parameters.neckRadius u ^ 2)⁻¹)
    (fun z hz => canonical_prefix_neck_S87 Hp s u hus z hz) hε x0 (half_pos hr0) hEuc x0
    (mem_riemannianBallOf_self_S33 _ _ (by positivity))
  refine h.trans (max_le ?_ ?_)
  · have hsq : r0 ^ 2 ≤ Hp.parameters.neckRadius u ^ 2 := pow_le_pow_left₀ hr0.le hrad 2
    calc (Hp.parameters.neckRadius u ^ 2)⁻¹ ≤ (r0 ^ 2)⁻¹ := inv_anti₀ (by positivity) hsq
      _ = 1 / r0 ^ 2 := by rw [one_div]
      _ ≤ 4 * A / r0 ^ 2 := div_le_div_of_nonneg_right (by linarith) (by positivity)
  · apply le_of_eq
    field_simp
    ring

end GC.LongTime.Ch12
