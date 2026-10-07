import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862EnlargeTower_O37

/-!
# CH12-O37 G2c: sectional lower bound from a scalar bound on the tower prefix

Tower-history form of `slice_history_sectional_of_scalar_CX12`: on the whole prefix `v ≤ s.time` of
`N := sliceTowerHistory_CX2 s`, a scalar bound `R ≤ K / r²` at a scale `r ≤ b √v` gives
`sec ≥ −r⁻²`. In Sublemma 86.6 this turns the `K`-independent scalar bound of `hKL82` at earlier
times into the sectional premises of `hKL82` and of the Child induction hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow

namespace GC.LongTime.Ch12

universe u

/-- The fixed Hamilton–Ivey region on the whole prefix of the slice's own tower history. -/
theorem fixedHI_prefix_O37
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ) (s : RegularSlice F.observation)
    (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hvs : (v : ℝ) ≤ s.time) :
    ∀ x, InFixedHamiltonIveyRegion
      ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v)
      (Hp.pinchingShift + v) x := by
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
    (fun Q m => ∀ x : Q.Carrier, InFixedHamiltonIveyRegion m (Hp.pinchingShift + v1) x)
    (slice_history_fixedHI_CX12 Hp s v')

/-- Scalar bound at scale `r ≤ b √v` ⇒ sectional lower bound `−r⁻²`, on the tower prefix. -/
theorem sectional_of_scalar_prefix_O37
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ) {K : ℝ} (hK : 0 ≤ K) :
    ∃ b : ℝ, 0 < b ∧ ∀ (s : RegularSlice F.observation)
      (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon), (v : ℝ) ≤ s.time →
      ∀ (x : ((sliceTowerHistory_CX2 s).stageAt v).Carrier) (r : ℝ),
      0 < r → r ≤ b * Real.sqrt v →
      metricScalarAt ((sliceTowerHistory_CX2 s).stageMetric
        ((sliceTowerHistory_CX2 s).activeStage v) v) x ≤ K / r ^ 2 →
      SectionalBoundedBelowAt ((sliceTowerHistory_CX2 s).stageMetric
        ((sliceTowerHistory_CX2 s).activeStage v) v) x (-(r ^ 2)⁻¹) := by
  obtain ⟨b, hb, hscale⟩ := exists_HI_scale_CX12 K
  refine ⟨b, hb, fun s v hvs x r hr hsize hR => ?_⟩
  exact sectional_of_fixedHI_small_scale_CX12 _ x hr hK
    ((hscale v r v.2.1 hr.le hsize).trans
      (le_add_of_nonneg_left Hp.pinchingShift_pos.le))
    (fixedHI_prefix_O37 Hp s v hvs x) hR

end GC.LongTime.Ch12
