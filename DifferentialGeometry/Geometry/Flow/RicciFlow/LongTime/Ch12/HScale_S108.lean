import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HAbs_S105

/-!
# CH12-S108, group 2: the `hscale` comparison

The three `hscale` binders (S94 `hsub86N_S94`, S89 `hlift_Ioo_of_Ico_S89`, MicroGlueLateRecords:421) all read
`scale / 2 ≤ metricScalarAt witness.metric (witness.cap z)` for every `z : ThreeBall`.  From S105's
`window_scalar_lower_S105` (`c₀ * scale ≤ scalar_out (window x)`) the following adapter removes the two
*shape* differences (cap point instead of window point, `witness.metric` instead of `outputMetric`);
the remaining differences are the constant (`c₀` instead of `1/2`) and the hypotheses
`ε ≤ ε₀`, `4 ≤ m`, `transitionEnd < D`, `hasCanonicalWindow` (see DELIVERY CH12-S108 G2).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- The scalar curvature of the witness metric is that of the output metric at the image under `inclusion`. -/
theorem metricScalarAt_witness_S108 {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    {E : MetricCutCapEvent P Q a s} {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    {b : E.RetainedBoundaryIndex} (S : E.PresentedStaticCap fixed D m ε b) (y : S.witness.Output) :
    metricScalarAt S.witness.metric y = metricScalarAt E.outputMetric (S.inclusion y) := by
  have hloc : IsLocalDiffeomorph ThreeModel ThreeModel ∞ S.inclusion :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv S.inclusion
      S.inclusion_smooth.contMDiff
      (fun p => (S.inclusion_smooth.isImmersion.isImmersionAt p).mfderiv_injective (by simp)) rfl
  have hg : S.witness.metric = localPullMetric E.outputMetric S.inclusion hloc := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [localPullMetric_inner]
    exact S.inclusion_metric x v w
  rw [hg, metricScalarAt_localPull]

/-- Cap-point form of the cap scalar lower bound (the `witness.metric` / `witness.cap z` shape of the three
`hscale` binders, with the absolute constant `c₀` of `window_scalar_lower_S105` in place of `1/2`). -/
theorem hscale_cap_S108 : ∃ ε₀ c₀ : ℝ, 0 < ε₀ ∧ 0 < c₀ ∧
    ∀ {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
      {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
      (S : E.PresentedStaticCap fixed D m ε b), ε ≤ ε₀ → 4 ≤ m → StandardCap.transitionEnd < D →
      S.hasCanonicalWindow → ∀ z : ThreeBall,
        c₀ * S.neck.scale ≤ metricScalarAt S.witness.metric (S.witness.cap z) := by
  obtain ⟨ε₀, c₀, hε₀, hc₀, h⟩ := window_scalar_lower_S105.{u}
  refine ⟨ε₀, c₀, hε₀, hc₀, fun S hε hm hD hcan z => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, h3⟩ := hcan
  obtain ⟨x, hx, hxe⟩ := h3 z
  rw [metricScalarAt_witness_S108, ← hxe]
  exact h S hε hm x (lt_of_le_of_lt hx hD)

/-- Record form: for every record whose parameters have `modelAccuracy ≤ ε₀`, `4 ≤ modelOrder`,
`transitionEnd < modelRadius` and canonical windows. -/
theorem hscale_record_cap_S108 : ∃ ε₀ c₀ : ℝ, 0 < ε₀ ∧ 0 < c₀ ∧
    ∀ {H : ObservedHistory.{u}} {pp : CutoffParameters} {i : Fin H.eventCount},
      pp.modelAccuracy ≤ ε₀ → 4 ≤ pp.modelOrder → StandardCap.transitionEnd < pp.modelRadius →
      ∀ (R : GeometricCutoffRecord H i pp) (b : (H.event i).RetainedBoundaryIndex),
        (R.static b).hasCanonicalWindow → ∀ z : ThreeBall,
          c₀ * (R.static b).neck.scale ≤
            metricScalarAt (R.static b).witness.metric ((R.static b).witness.cap z) := by
  obtain ⟨ε₀, c₀, hε₀, hc₀, h⟩ := hscale_cap_S108.{u}
  exact ⟨ε₀, c₀, hε₀, hc₀, fun hε hm hD R b hcan z => h (R.static b) hε hm hD hcan z⟩

end GC.LongTime.Ch12
