import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84Sub86RmBoundSlice_O22
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceDistortionThreshold

/-!
# CH12-S141, group 1: pointwise-in-time scalar bound on a ball of the slice history from the gradient estimate

`ball_scalar_le_four_S141`: at every time `v` of the slice history, if `scalar(y) ≤ N`, `(neckRadius v ^ 2)⁻¹ ≤ N` and
`C2 · r · √N ≤ 1/4` then `scalar ≤ 4 N` on the `r`-ball about `y` (spatial gradient bound `Hp.canonical … W.gradient`,
bridged to `s.history.stageMetric` as in `slice_history_region_O16`; then the flow-level
`scalar_le_four_mul_of_gradient_bound` on the active slab).  No events, no barrier, no first exit (finding F-S141-1).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
  DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Perelman DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}

/-- The bridge `postStage/postMetric ↔ s.history` at an arbitrary stage index `j` with `activeStage v = j`
(the proof of `slice_history_region_O16`). -/
theorem slice_post_bridge_S141 (s : RegularSlice F.observation) (v : Icc (0 : ℝ) s.history.horizon)
    (j : Fin (s.history.eventCount + 1)) (hj : s.history.activeStage v = j) :
    postStage F.observation v = s.history.stage j ∧
      HEq (postMetric F.observation v) (s.history.stageMetric j v) := by
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
  subst hj
  exact ⟨hst', hm'⟩

/-- **G1 (`ball_scalar_le_four_S141`).** -/
theorem ball_scalar_le_four_S141 (Hp : AnalyticSurgeryProfile F δ) (s : RegularSlice F.observation)
    (v : Icc (0 : ℝ) s.history.horizon) {N r : ℝ} (hN : 0 < N)
    (hq : (Hp.parameters.neckRadius v ^ 2)⁻¹ ≤ N) (hr : Hp.C2 * r * Real.sqrt N ≤ 1 / 4)
    (y : (s.history.stage (s.history.activeStage v)).Carrier)
    (hy : metricScalarAt (s.history.stageMetric (s.history.activeStage v) v) y ≤ N) :
    ∀ x ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage v) v) y r,
      metricScalarAt (s.history.stageMetric (s.history.activeStage v) v) x ≤ 4 * N := by
  have hv0 : (0 : ℝ) ≤ v := v.2.1
  have hC2 : (0 : ℝ) ≤ Hp.C2 := by linarith [Hp.C2_ge_one]
  have key : ∀ (j : Fin (s.history.eventCount + 1)) (hj : s.history.activeStage v = j),
      ∀ x : (s.history.stage j).Carrier,
        (Hp.parameters.neckRadius v ^ 2)⁻¹ < metricScalarAt (s.history.stageMetric j v) x →
        ∀ w : TangentSpace I3 x, |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ)
            (metricScalarAt (s.history.stageMetric j v)) x w)| ≤
          Hp.C2 * metricScalarAt (s.history.stageMetric j v) x *
            Real.sqrt (metricScalarAt (s.history.stageMetric j v) x) *
            Real.sqrt ((s.history.stageMetric j v).inner x w w) := by
    intro j hj
    obtain ⟨hst, hm⟩ := slice_post_bridge_S141 s v j hj
    exact stageMetric_transport_O3 hst hm
      (fun Q m => ∀ x : Q.Carrier, (Hp.parameters.neckRadius v ^ 2)⁻¹ < metricScalarAt m x →
        ∀ w : TangentSpace I3 x, |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt m) x w)| ≤
          Hp.C2 * metricScalarAt m x * Real.sqrt (metricScalarAt m x) *
            Real.sqrt (m.inner x w w))
      (fun x hx w => by
        obtain ⟨W, -⟩ := Hp.canonical v hv0 x hx
        exact W.gradient w)
  have main : ∀ (j : Fin (s.history.eventCount + 1)) (y : (s.history.stage j).Carrier),
      (∀ x : (s.history.stage j).Carrier,
        (Hp.parameters.neckRadius v ^ 2)⁻¹ < metricScalarAt (s.history.stageMetric j v) x →
        ∀ w : TangentSpace I3 x, |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ)
            (metricScalarAt (s.history.stageMetric j v)) x w)| ≤
          Hp.C2 * metricScalarAt (s.history.stageMetric j v) x *
            Real.sqrt (metricScalarAt (s.history.stageMetric j v) x) *
            Real.sqrt ((s.history.stageMetric j v).inner x w w)) →
      metricScalarAt (s.history.stageMetric j v) y ≤ N →
      ∀ x ∈ riemannianBallOf (s.history.stageMetric j v) y r,
        metricScalarAt (s.history.stageMetric j v) x ≤ 4 * N := by
    intro j y hk hy
    by_cases hne : j = Fin.last s.history.eventCount
    · subst hne
      have hlt : s.history.time (Fin.last s.history.eventCount) < s.history.horizon := s.preceding
      intro x hx
      rw [ObservedHistory.stageMetric_last_of_lt (h := hlt)] at hy hx hk ⊢
      have hx' : x ∈ riemannianClosedBallOf ((s.history.finalSlab hlt).flow.base.metric v) y r :=
        le_of_lt (α := ENNReal) hx
      have : IsManifold I3 1 (s.history.stage (Fin.last s.history.eventCount)).Carrier :=
        IsManifold.of_le (n := ∞) (by decide)
      exact Perelman.CanonicalNeighborhood.scalar_le_four_mul_of_gradient_bound
        (s.history.finalSlab hlt).flow (Cgrad := ⟨Hp.C2, hC2⟩)
        (qcan := (Hp.parameters.neckRadius v ^ 2)⁻¹)
        (fun w hw u => hk w hw u) hN hy hq hr hx'
    · obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hne
      intro x hx
      rw [ObservedHistory.stageMetric_castSucc_apply] at hy hx hk ⊢
      have hx' : x ∈ riemannianClosedBallOf ((s.history.event i).incoming.flow.base.metric v) y r :=
        le_of_lt (α := ENNReal) hx
      have : IsManifold I3 1 (s.history.stage i.castSucc).Carrier :=
        IsManifold.of_le (n := ∞) (by decide)
      exact Perelman.CanonicalNeighborhood.scalar_le_four_mul_of_gradient_bound
        (s.history.event i).incoming.flow (Cgrad := ⟨Hp.C2, hC2⟩)
        (qcan := (Hp.parameters.neckRadius v ^ 2)⁻¹)
        (fun w hw u => hk w hw u) hN hy hq hr hx'
  exact main _ y (key _ rfl) hy

end GC.LongTime.Ch12
