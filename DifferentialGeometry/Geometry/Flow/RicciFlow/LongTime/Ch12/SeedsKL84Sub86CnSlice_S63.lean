import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84Sub86CnSpread_S63
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84Pinch_O16

/-!
# CH12-S63 G1 (s2): `Hp.canonical` on the active stage of the slice history

Same transport as `slice_history_region_O16` (`observe_slice_stage` / `observe_slice_metric` +
`postData_observe_O3`): at every time `v` of the slice history, every point of the active stage
with scalar curvature `> (neckRadius v ^ 2)⁻¹` has a `SpatialCanonicalWitness` of the profile's
constants `(Hp.epsilon, Hp.C1, Hp.C2)`.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- (s2) `Hp.canonical` transported to the active stage of the slice history at time `v`. -/
theorem slice_canonical_S63 {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}
    (Hp : AnalyticSurgeryProfile F δ) (s : RegularSlice F.observation)
    (v : Icc (0 : ℝ) s.history.horizon) :
    ∀ x, (Hp.parameters.neckRadius v ^ 2)⁻¹ <
        metricScalarAt (s.history.stageMetric (s.history.activeStage v) v) x →
      Nonempty (SpatialCanonicalWitness (s.history.stageMetric (s.history.activeStage v) v)
        Hp.epsilon Hp.C1 Hp.C2 x) := by
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
      Nonempty (SpatialCanonicalWitness m Hp.epsilon Hp.C1 Hp.C2 x))
    (fun x hx => by
      obtain ⟨W, -⟩ := Hp.canonical v hv0 x hx
      exact ⟨W⟩)

/-- (s1)+(s2) on the slice history: `R(x) ≤ Mb` and `(neckRadius v ^ 2)⁻¹ ≤ Mb` give
`R < 2 C2 Mb` on the `g_v`-ball `B(x, (2 C2 Mb)^{-1/2})`. -/
theorem slice_scalar_spread_S63 {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}
    (Hp : AnalyticSurgeryProfile F δ) (s : RegularSlice F.observation)
    (v : Icc (0 : ℝ) s.history.horizon)
    (x : (s.history.stage (s.history.activeStage v)).Carrier) {Mb : ℝ} (hMb : 0 < Mb)
    (hNM : (Hp.parameters.neckRadius v ^ 2)⁻¹ ≤ Mb)
    (hx : metricScalarAt (s.history.stageMetric (s.history.activeStage v) v) x ≤ Mb) :
    ∀ y ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage v) v) x
        (Real.sqrt (2 * Hp.C2 * Mb))⁻¹,
      metricScalarAt (s.history.stageMetric (s.history.activeStage v) v) y < 2 * Hp.C2 * Mb :=
  cn_scalar_spread_S63 _ Hp.C2_ge_one (slice_canonical_S63 Hp s v) x hMb hNM hx

end GC.LongTime.Ch12
