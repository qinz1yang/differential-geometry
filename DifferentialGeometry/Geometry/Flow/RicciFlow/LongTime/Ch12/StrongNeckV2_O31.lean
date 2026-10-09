import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.StrongNeckTrace_O31

/-!
# CH12-O31, group 5b: `hStrong v2 ⇒ hStrong v1` (`[FROZEN v2] CH12-O31 hStrong`)

The neck branch of hStrong v2 carries a regular open backward trace `E` of `U` on the window
`[a, s.time]`, `a = s.time − R(x)⁻¹`, with `S.base.metric v = E(v)^* g_H(v)` for every `v` in the
window (surgery allowed outside `U`), the terminal identification and the strong neck.  Dropping
the window data gives the old `[FROZEN] CH12-O23 hStrong`, so every delivered v1 consumer is fed
from v2.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set Filter
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- **hStrong v2 ⇒ hStrong v1** (`[FROZEN v2] CH12-O31 hStrong`). -/
theorem hStrong_v1_of_v2_O31 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hStrong2 : ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ x : s.stage.Carrier,
      ∀ hR : (Hp.parameters.neckRadius s.time ^ 2)⁻¹ < metricScalarAt s.metric x,
      ∃ W : SpatialCanonicalWitness s.metric Hp.epsilon Hp.C1 Hp.C2 x,
        W.capTubeHasNeckChart Hp.epsilon ∧
        ∀ nk, W.alternative = SpatialCanonicalAlternative.neck nk →
          ∃ (U : TopologicalSpace.Opens s.stage.Carrier) (hxU : x ∈ U)
            (a : Icc (0 : ℝ) s.history.horizon)
            (E : RegularOpenBackwardTrace_O31 s.history (s.history.activeStage a) U)
            (S : SolutionOn (I := ThreeModel) (M := U)
              (RealTimeInterval.closed (s.time - (metricScalarAt s.metric x)⁻¹) s.time
                (sub_le_self _ (inv_nonneg.mpr
                  (lt_of_le_of_lt (inv_nonneg.mpr (sq_nonneg _)) hR).le)))),
            (a : ℝ) = s.time - (metricScalarAt s.metric x)⁻¹ ∧
            IsSolutionOn S ∧
            (∀ v : Icc (0 : ℝ) s.history.horizon, ∀ hav : a ≤ v,
              S.base.metric v =
                localPullMetric (s.history.stageMetric (s.history.activeStage v) v)
                  (E.atStage (s.history.activeStage v) (s.history.activeStage_mono hav)
                    (Fin.le_last _))
                  (E.atStage_isLocalDiffeomorph _ _ _)) ∧
            S.base.metric s.time = s.metric.restrictOpen U ∧
            Nonempty (StrongNeck S Hp.epsilon ⟨x, hxU⟩ s.time))
    :
    ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ x : s.stage.Carrier,
      ∀ hR : (Hp.parameters.neckRadius s.time ^ 2)⁻¹ < metricScalarAt s.metric x,
      ∃ W : SpatialCanonicalWitness s.metric Hp.epsilon Hp.C1 Hp.C2 x,
        W.capTubeHasNeckChart Hp.epsilon ∧
        ∀ nk, W.alternative = SpatialCanonicalAlternative.neck nk →
          ∃ (U : TopologicalSpace.Opens s.stage.Carrier) (hxU : x ∈ U)
            (S : SolutionOn (I := ThreeModel) (M := U)
              (RealTimeInterval.closed (s.time - (metricScalarAt s.metric x)⁻¹) s.time
                (sub_le_self _ (inv_nonneg.mpr
                  (lt_of_le_of_lt (inv_nonneg.mpr (sq_nonneg _)) hR).le)))),
            IsSolutionOn S ∧ S.base.metric s.time = s.metric.restrictOpen U ∧
            Nonempty (StrongNeck S Hp.epsilon ⟨x, hxU⟩ s.time) := by
  obtain ⟨T, hT⟩ := hStrong2
  refine ⟨T, fun s hs x hR => ?_⟩
  obtain ⟨W, hchart, hnk⟩ := hT s hs x hR
  refine ⟨W, hchart, fun nk hnk' => ?_⟩
  obtain ⟨U, hxU, _a, _E, S, -, hS, -, hterm, hneck⟩ := hnk nk hnk'
  exact ⟨U, hxU, S, hS, hterm, hneck⟩

end GC.LongTime.Ch12
