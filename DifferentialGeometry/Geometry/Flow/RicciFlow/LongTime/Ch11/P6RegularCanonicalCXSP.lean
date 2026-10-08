import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedPresentationCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedRestrictionCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.S15.SliceBridgeC11S15
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HK03Bridge_S132

set_option autoImplicit false

/-!
# CX-SPINE G23：exact RegularSlice hb 给同一 history 的正年龄空间供给

先取hb原来的K₁/T，再将实际small seed整体限制并运输到同时间RegularSlice。
球、体积、scalar及带capTube chart的witness由同一presentation的metric识别搬回。
K₁/T/A/r/ε/C1/C2不变；正stage-age显式保留，不声称出生时刻或full Good。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

/-- exact regular-slice供给接回任意观测history的正stage-age时刻，保留原常数。 -/
theorem regular_history_canonical_of_supply_CXSP
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {ε C1 C2 : ℝ} (hb : LargerBallCanonicalLateSupply_C11E F ε C1 C2)
    {A : ℝ} (hA : 0 < A) :
    ∃ K₁ T : ℝ, 0 < K₁ ∧ 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
          T ≤ (t : ℝ) → H.time (H.activeStage t) < (t : ℝ) →
          2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
          ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
          ∀ y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
            K₁ * (r ^ 2)⁻¹ ≤ metricScalarAt (H.stageMetric (H.activeStage t) t) y →
            ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage t) t) ε C1 C2 y,
              W.capTubeHasNeckChart ε := by
  obtain ⟨K₁, T, hK₁, hT, hbody⟩ := hb A hA
  refine ⟨K₁, T, hK₁, hT, ?_⟩
  intro n H t p r hTt hage htime hsmall hvol y hy hR
  have htpos : 0 < (t : ℝ) := (H.time_nonneg _).trans_lt hage
  have htn : (t : ℝ) ≤ (n : ℝ) := t.2.2.trans_eq (F.tower.horizon_eq n)
  have hnotH : (t : ℝ) ∉ H.eventTimes :=
    (Ch12.regular_iff_not_mem_eventTimes_S74 htpos).mp hage
  have hnot : (t : ℝ) ∉ F.observation.eventTimes := fun he =>
    hnotH ((Ch12.mem_eventTimes_history_iff_S132 (T := F.observation) n htpos htn).mp he)
  have hpreceding : (F.observation.observe t htpos.le).time
      (Fin.last (F.observation.observe t htpos.le).eventCount) < (t : ℝ) := by
    obtain ⟨s₀, hs₀⟩ := Ch12.regularSlice_exists_of_not_eventTime_S37 F.observation t htpos hnot
    rcases s₀ with ⟨u, _hu, _hureg, hupre⟩
    change u = (t : ℝ) at hs₀
    subst u
    exact hupre
  let s : RegularSlice F.observation := ⟨t, htpos, hnot, hpreceding⟩
  let K := H.restrict t
  let uK : Icc (0 : ℝ) K.horizon := ⟨t, t.2.1, le_rfl⟩
  let us : Icc (0 : ℝ) s.history.horizon := ⟨t, htpos.le, le_rfl⟩
  have R : s.history.SamePresentation K :=
    F.observation.observe_eq_atIndex n t htpos.le htn
  have eR : s.history.stageAt us = K.stageAt uK := R.stageAt_eq us
  have eK : K.stageAt uK = H.stageAt t := H.restrict_stageAt t uK
  have e : s.history.stageAt us = H.stageAt t := eR.trans eK
  have hm : HEq (s.history.stageMetric (s.history.activeStage us) us)
      (H.stageMetric (H.activeStage t) t) :=
    (R.sliceMetric_heq us).trans (H.restrict_sliceMetric t uK)
  let pK : (K.stageAt uK).Carrier := cast (congrArg OrientedThreeStage.Carrier eK.symm) p
  let pS : (s.history.stageAt us).Carrier :=
    cast (congrArg OrientedThreeStage.Carrier eR.symm) pK
  have hpK : HEq pK p := cast_heq _ _
  have hpSK : HEq pS pK := cast_heq _ _
  have hpS : HEq pS p := hpSK.trans hpK
  have hpLift : Ch12.restrictPoint_CX2 H t uK pK = p :=
    eq_of_heq ((Ch12.restrictPoint_heq_CX2 H t uK pK).trans hpK)
  have hseedK : hasSmallParabolicCurvature K uK pK r := by
    apply smallParabolicCurvature_restrict_iff_CXSP.mpr
    rw [hpLift]
    exact hsmall
  have hseedS := smallParabolicCurvature_of_samePresentation_CXSP R us pS pK hpSK.symm r hseedK
  let yS : (s.history.stageAt us).Carrier := cast (congrArg OrientedThreeStage.Carrier e.symm) y
  have hyS : HEq yS y := cast_heq _ _
  have hvolS : ENNReal.ofReal (A⁻¹ * r ^ 3) ≤
      ballVolume (s.history.stageMetric (s.history.activeStage us) us) pS r :=
    hvol.trans_eq (Ch12.ballVolume_heq_CX2 e hm hpS r).symm
  have hyBall : yS ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage us) us)
      pS (A * r) := (Ch12.metricBall_heq_CX2 e hm hpS hyS (A * r)).mpr hy
  have hRS : K₁ * (r ^ 2)⁻¹ ≤
      metricScalarAt (s.history.stageMetric (s.history.activeStage us) us) yS :=
    hR.trans_eq (metricScalarAt_heq_C11S15 e hm hyS).symm
  have hWS := hbody s hTt pS r htime hseedS hvolS yS hyBall hRS
  exact canonicalWitness_heq_C11S15 e.symm hm.symm hyS.symm hWS

end GC.LongTime.Ch11
