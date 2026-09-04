import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.Minimality.InitialSegment
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.Matching.SameChartMomentum
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Chart.OverlapDerivative
import DifferentialGeometry.Topology.Manifold.CurveChart.InitialSegment
import DifferentialGeometry.Geometry.Operator.Family.Gram

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Function MeasureTheory Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] in
private theorem nodeMatch_toFun_cast {a b : Real} (h : a = b) (v : timeH1 E b) :
    ((h.symm ▸ v : timeH1 E a).toFun) = v.toFun := by
  subst b
  rfl

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
    [CompactSpace M] in
private theorem nodeMatch_act_cast {a b : Real} (h : a = b)
    (S : SolutionOn (I := I) (M := M) D) (T s : Real) (p : M)
    (v : timeH1 E b) :
    lChartAction S T s p (h.symm ▸ v : timeH1 E a) = lChartAction S T s p v := by
  subst b
  rfl

omit [CompactSpace M] in
theorem lRegAction_minimizer_momentum_pairing_eq
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (t : Fin 3 → Real) (p : Fin 2 → M) (gamma : Real → M)
    (u : (i : Fin 2) → timeH1 E (partitionIntervalLength t i))
    (hpos : ∀ i : Fin 2, t i.castSucc < t i.succ)
    (hsrc : ∀ i, MapsTo gamma
      (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source)
    (hrep : ∀ i, EqOn (u i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (Icc (0 : Real) (partitionIntervalLength t i)))
    (hreg : ∀ s ∈ Icc (t 0) (t (Fin.last 2)), T - s ^ 2 ∈ D.regular)
    (hmin : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta (t 0) = gamma (t 0) →
      delta (t (Fin.last 2)) = gamma (t (Fin.last 2)) →
      lRegAction S T gamma (t 0) (t (Fin.last 2)) ≤
        lRegAction S T delta (t 0) (t (Fin.last 2))) :
    ∀ z : E,
      inner Real
          (chartGramOp (I := I) S.family (p 0)
            (T - (t 1) ^ 2, extChartAt I (p 0) (gamma (t 1)))
            (derivWithin (u 0).toFun
              (Icc (0 : Real) (partitionIntervalLength t 0)) (partitionIntervalLength t 0))) z =
        inner Real
          (chartGramOp (I := I) S.family (p 1)
            (T - (t 1) ^ 2, extChartAt I (p 1) (gamma (t 1)))
            (derivWithin (u 1).toFun
              (Icc (0 : Real) (partitionIntervalLength t 1)) 0))
          (tangentCoordChange I (p 0) (p 1) (gamma (t 1)) z) := by
  classical
  have hfin0c : (0 : Fin 2).castSucc = (0 : Fin 3) := rfl
  have hfin0s : (0 : Fin 2).succ = (1 : Fin 3) := rfl
  have hfin1c : (1 : Fin 2).castSucc = (1 : Fin 3) := rfl
  have hfin1s : (1 : Fin 2).succ = Fin.last 2 := rfl
  have ht01 : t 0 < t 1 := by
    simpa only [hfin0c, hfin0s] using hpos 0
  have ht12 : t 1 < t (Fin.last 2) := by
    simpa only [hfin1c, hfin1s] using hpos 1
  have htmono : Monotone t := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact (hpos i).le
  have hchart : ∀ i, MapsTo (u i).toFun
      (Icc (0 : Real) (partitionIntervalLength t i))
      (interior (extChartAt I (p i)).target) := by
    intro i r hr
    rw [hrep i hr]
    rw [(isOpen_extChartAt_target (I := I) (p i)).interior_eq]
    apply (extChartAt I (p i)).map_source
    rw [extChartAt_source]
    exact hsrc i ⟨by linarith [hr.1], by
      have hr2 : r ≤ t i.succ - t i.castSucc := by
        simpa only [partitionIntervalLength] using hr.2
      linarith⟩
  have hrecover (i : Fin 2) (r : Real)
      (hr : r ∈ Icc (0 : Real) (partitionIntervalLength t i)) :
      (extChartAt I (p i)).symm ((u i).toFun r) =
        gamma (t i.castSucc + r) := by
    rw [hrep i hr]
    apply (extChartAt I (p i)).left_inv
    rw [extChartAt_source]
    exact hsrc i ⟨by linarith [hr.1], by
      have hr2 : r ≤ t i.succ - t i.castSucc := by
        simpa only [partitionIntervalLength] using hr.2
      linarith⟩
  have hnode : (extChartAt I (p 0)).symm
        ((u 0).toFun (partitionIntervalLength t 0)) =
      (extChartAt I (p 1)).symm ((u 1).toFun 0) := by
    rw [hrecover 0 (partitionIntervalLength t 0)
        ⟨by simpa only [partitionIntervalLength, hfin0s] using sub_nonneg.mpr (hpos 0).le, le_rfl⟩,
      hrecover 1 0 ⟨le_rfl, by
        simpa only [partitionIntervalLength, hfin1c, hfin1s] using sub_nonneg.mpr (hpos 1).le⟩]
    simp only [partitionIntervalLength, hfin0c, hfin0s, hfin1c, add_sub_cancel, add_zero]
  let hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  have hcmp : ∀ v : (i : Fin 2) → timeH1 E (partitionIntervalLength t i),
      (∀ i, MapsTo (v i).toFun (Icc (0 : Real) (partitionIntervalLength t i))
        (extChartAt I (p i)).target) →
      (extChartAt I (p 0)).symm ((v 0).toFun 0) =
        (extChartAt I (p 0)).symm ((u 0).toFun 0) →
      (extChartAt I (p 1)).symm ((v 1).toFun (partitionIntervalLength t 1)) =
        (extChartAt I (p 1)).symm ((u 1).toFun (partitionIntervalLength t 1)) →
      (extChartAt I (p 0)).symm ((v 0).toFun (partitionIntervalLength t 0)) =
        (extChartAt I (p 1)).symm ((v 1).toFun 0) →
      (∑ i : Fin 2, lChartAction S T (t i.castSucc) (p i) (u i)) ≤
        ∑ i : Fin 2, lChartAction S T (t i.castSucc) (p i) (v i) := by
    intro v hvtar hv0 hv2 hvnode
    have hu0 : (extChartAt I (p 0)).symm ((u 0).toFun 0) = gamma (t 0) := by
      simpa only [hfin0c, add_zero] using hrecover 0 0 ⟨le_rfl, by
        simpa only [partitionIntervalLength, hfin0s] using sub_nonneg.mpr (hpos 0).le⟩
    have hu2 : (extChartAt I (p 1)).symm
        ((u 1).toFun (partitionIntervalLength t 1)) = gamma (t (Fin.last 2)) := by
      have h := hrecover 1 (partitionIntervalLength t 1)
        ⟨by simpa only [partitionIntervalLength, hfin1c, hfin1s] using
            sub_nonneg.mpr (hpos 1).le, le_rfl⟩
      simpa only [partitionIntervalLength, hfin1c, hfin1s, add_sub_cancel] using h
    exact lChartAction_pair_le_of_lRegAction_minimizer (I := I) S hS.smoothMetric hSc T t htmono p gamma u
      hsrc hrep hreg hmin v hvtar (hv0.trans hu0) (hv2.trans hu2) hvnode
  have hlocal1 : IsLocalMinOn
      (lChartAction S T (t 1) (p 1)) (sameTimeEnds (u 1)) (u 1) :=
    lChartAction_isLocalMinOn_of_pair_minimality (I := I) S T t p u hchart hnode hcmp 1
  have hreg1 : ∀ r, r ∈ Icc (0 : Real) (partitionIntervalLength t 1) →
      T - (t 1 + r) ^ 2 ∈ D.regular := by
    intro r hr
    apply hreg (t 1 + r)
    constructor
    · exact (hpos 0).le.trans (le_add_of_nonneg_right hr.1)
    · have hr2 : r ≤ t (Fin.last 2) - t 1 := by
        simpa only [partitionIntervalLength, hfin1c, hfin1s] using hr.2
      linarith
  obtain ⟨q1, _P1, hq1c, hq1ae, hu1c1, hu1d, _hP1c1, _hP1eq, _hP1d⟩ :=
    lChartAction_minimizer_momentum_contDiffOn_one (I := I) S hS T (t 1) (p 1)
      (by simpa only [partitionIntervalLength, hfin1c, hfin1s] using sub_pos.mpr (hpos 1))
      (u 1) hreg1 (hchart 1) hlocal1
  have hgamma1 : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
      (Icc (t 1) (t (Fin.last 2))) :=
    curve_c1_local I (p 1) gamma (u 1) (hsrc 1) (hrep 1) hu1c1
  have hpNode : gamma (t 1) ∈ (chartAt H (p 0)).source := by
    exact hsrc 0 (by simpa using (show t 1 ∈ Icc (t 0) (t 1) from
      ⟨(hpos 0).le, le_rfl⟩))
  obtain ⟨c, h1c0, hc20, hsrcHead'⟩ :=
    DifferentialGeometry.Geometry.exists_chart_initial_segment (H := H)
      (hpos 1) hgamma1.continuousOn hpNode
  have h1c : t 1 < c := by simpa only [hfin1c] using h1c0
  have hc2 : c ≤ t (Fin.last 2) := by simpa only [hfin1s] using hc20
  have hsrcHead : MapsTo gamma (Icc (t 1) c)
      (chartAt H (p 0)).source := by
    simpa only [hfin1c] using hsrcHead'
  have hsrcTail : MapsTo gamma (Icc c (t (Fin.last 2)))
      (chartAt H (p 1)).source :=
    fun s hs ↦ hsrc 1 ⟨h1c.le.trans hs.1, hs.2⟩
  let gammaHead : Real → M := fun r ↦ gamma (t 1 + r)
  let gammaTail : Real → M := fun r ↦ gamma (c + r)
  have hshiftHead : MapsTo (fun r : Real ↦ t 1 + r)
      (Icc (0 : Real) (c - t 1)) (Icc (t 1) (t (Fin.last 2))) := by
    intro r hr
    exact ⟨le_add_of_nonneg_right hr.1, by linarith [hr.2, hc2]⟩
  have hshiftTail : MapsTo (fun r : Real ↦ c + r)
      (Icc (0 : Real) (t (Fin.last 2) - c))
      (Icc (t 1) (t (Fin.last 2))) := by
    intro r hr
    exact ⟨h1c.le.trans (le_add_of_nonneg_right hr.1), by linarith [hr.2]⟩
  have hgammaHead : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gammaHead
      (Icc (0 : Real) (c - t 1)) := by
    exact hgamma1.comp
      (contDiffOn_const.add contDiffOn_id).contMDiffOn hshiftHead
  have hgammaTail : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gammaTail
      (Icc (0 : Real) (t (Fin.last 2) - c)) := by
    exact hgamma1.comp
      (contDiffOn_const.add contDiffOn_id).contMDiffOn hshiftTail
  have hsrcHead0 : MapsTo gammaHead (Icc (0 : Real) (c - t 1))
      (chartAt H (p 0)).source := by
    intro r hr
    exact hsrcHead ⟨le_add_of_nonneg_right hr.1, by linarith [hr.2]⟩
  have hsrcTail0 : MapsTo gammaTail
      (Icc (0 : Real) (t (Fin.last 2) - c))
      (chartAt H (p 1)).source := by
    intro r hr
    exact hsrcTail ⟨le_add_of_nonneg_right hr.1, by linarith [hr.2]⟩
  let uHead : timeH1 E (c - t 1) :=
    chartTimeH1 I (sub_nonneg.mpr h1c.le) (p 0) gammaHead hgammaHead hsrcHead0
  let uTail : timeH1 E (t (Fin.last 2) - c) :=
    chartTimeH1 I (sub_nonneg.mpr hc2) (p 1) gammaTail hgammaTail hsrcTail0
  have huHead : EqOn uHead.toFun ((extChartAt I (p 0)) ∘ gammaHead)
      (Icc (0 : Real) (c - t 1)) :=
    chartTimeH1_toFun I (sub_nonneg.mpr h1c.le) (p 0) gammaHead hgammaHead hsrcHead0
  have huTail : EqOn uTail.toFun ((extChartAt I (p 1)) ∘ gammaTail)
      (Icc (0 : Real) (t (Fin.last 2) - c)) :=
    chartTimeH1_toFun I (sub_nonneg.mpr hc2) (p 1) gammaTail hgammaTail hsrcTail0
  have huHeadC1 : ContDiffOn Real 1 uHead.toFun (Icc (0 : Real) (c - t 1)) := by
    exact (chartCoord_contDiff I (p 0) gammaHead hgammaHead hsrcHead0).congr
      (fun r hr ↦ huHead hr)
  have hcmpHead : ∀ v0 : timeH1 E (t 1 - t 0),
      ∀ v1 : timeH1 E (c - t 1),
      MapsTo v0.toFun (Icc (0 : Real) (t 1 - t 0))
          (extChartAt I (p 0)).target →
      MapsTo v1.toFun (Icc (0 : Real) (c - t 1))
          (extChartAt I (p 0)).target →
      (extChartAt I (p 0)).symm (v0.toFun 0) = gamma (t 0) →
      (extChartAt I (p 0)).symm (v1.toFun (c - t 1)) = gamma c →
      (extChartAt I (p 0)).symm (v0.toFun (t 1 - t 0)) =
        (extChartAt I (p 0)).symm (v1.toFun 0) →
      lChartAction S T (t 0) (p 0) (u 0) +
          lChartAction S T (t 1) (p 0) uHead ≤
        lChartAction S T (t 0) (p 0) v0 +
          lChartAction S T (t 1) (p 0) v1 := by
    intro v0 v1 hv0tar hv1tar hv0 hv2 hvnode
    exact lChartAction_initial_pair_le_of_lRegAction_minimizer (I := I) S hS.smoothMetric hSc T
      (t 0) (t 1) c (t (Fin.last 2)) (hpos 0).le h1c.le hc2
      (p 0) (p 1) gamma (u 0) uHead uTail
      (hsrc 0) hsrcHead hsrcTail (hrep 0)
      (by simpa only [gammaHead, Function.comp_def] using huHead)
      (by simpa only [gammaTail, Function.comp_def] using huTail)
      hreg hmin v0 v1 hv0tar hv1tar hv0 hv2 hvnode
  let th : Fin 3 → Real := fun i ↦
    if i = 0 then t 0 else if i = 1 then t 1 else c
  have hth0 : th 0 = t 0 := by simp [th]
  have hth1 : th 1 = t 1 := by simp [th]
  have hth2 : th 2 = c := by simp [th]
  have hthLen0 : partitionIntervalLength th 0 = partitionIntervalLength t 0 := by
    simp only [partitionIntervalLength, hth0, hth1, hfin0c, hfin0s]
  have hthLen1 : partitionIntervalLength th 1 = c - t 1 := by
    rw [partitionIntervalLength, hfin1c, hfin1s,
      show Fin.last 2 = (2 : Fin 3) by rfl, hth1, hth2]
  have hthLen0' : partitionIntervalLength th 0 = t 1 - t 0 := by
    simpa only [partitionIntervalLength, hfin0c, hfin0s] using hthLen0
  let uh0 : timeH1 E (partitionIntervalLength th 0) := hthLen0.symm ▸ u 0
  let uh1 : timeH1 E (partitionIntervalLength th 1) := hthLen1.symm ▸ uHead
  let uh : (i : Fin 2) → timeH1 E (partitionIntervalLength th i) :=
    Fin.cases uh0 (Fin.cases uh1 (fun i ↦ Fin.elim0 i))
  have huh0 : uh 0 = uh0 := by rfl
  have huh1 : uh 1 = uh1 := by
    change uh (Fin.succ 0) = uh1
    rfl
  have huh0Fun : (uh 0).toFun = (u 0).toFun := by
    rw [huh0]
    exact nodeMatch_toFun_cast hthLen0 (u 0)
  have huh1Fun : (uh 1).toFun = uHead.toFun := by
    rw [huh1]
    exact nodeMatch_toFun_cast hthLen1 uHead
  have hthpos : ∀ i : Fin 2, th i.castSucc < th i.succ := by
    intro i
    fin_cases i
    · simpa [th] using hpos 0
    · simpa [th] using h1c
  have hthreg : ∀ i r, r ∈ Icc (0 : Real) (partitionIntervalLength th i) →
      T - (th i.castSucc + r) ^ 2 ∈ D.regular := by
    intro i r hr
    fin_cases i
    · apply hreg (t 0 + r)
      have hr2 : r ≤ t 1 - t 0 := by
        simpa [th, partitionIntervalLength] using hr.2
      exact ⟨by linarith [hr.1], by linarith [hr2, h1c.le, hc2]⟩
    · apply hreg (t 1 + r)
      have hr2 : r ≤ c - t 1 := by
        simpa [th, partitionIntervalLength] using hr.2
      exact ⟨by linarith [hr.1, ht01.le], by linarith [hr2, hc2]⟩
  have huhchart : ∀ i, MapsTo (uh i).toFun
      (Icc (0 : Real) (partitionIntervalLength th i))
      (interior (extChartAt I (p 0)).target) := by
    intro i r hr
    fin_cases i
    · change (uh 0).toFun r ∈ interior (extChartAt I (p 0)).target
      change r ∈ Icc (0 : Real) (partitionIntervalLength th 0) at hr
      rw [huh0Fun]
      rw [hthLen0] at hr
      exact hchart 0 hr
    · change (uh 1).toFun r ∈ interior (extChartAt I (p 0)).target
      change r ∈ Icc (0 : Real) (partitionIntervalLength th 1) at hr
      rw [huh1Fun]
      have hr' : r ∈ Icc (0 : Real) (c - t 1) := by
        rwa [hthLen1] at hr
      have htarget : uHead.toFun r ∈
          interior (extChartAt I (p 0)).target := by
        rw [(isOpen_extChartAt_target (I := I) (p 0)).interior_eq,
          huHead hr']
        apply (extChartAt I (p 0)).map_source
        rw [extChartAt_source]
        exact hsrcHead0 hr'
      exact htarget
  have huhnode : (extChartAt I (p 0)).symm
        ((uh 0).toFun (partitionIntervalLength th 0)) =
      (extChartAt I (p 0)).symm ((uh 1).toFun 0) := by
    have hleft := hrecover 0 (partitionIntervalLength t 0)
      ⟨by simpa only [partitionIntervalLength, hfin0s] using sub_nonneg.mpr (hpos 0).le, le_rfl⟩
    have hleft' : (extChartAt I (p 0)).symm
        ((u 0).toFun (partitionIntervalLength t 0)) = gamma (t 1) := by
      simpa only [partitionIntervalLength, hfin0c, hfin0s, add_sub_cancel] using hleft
    have hright : (extChartAt I (p 0)).symm (uHead.toFun 0) = gamma (t 1) := by
      rw [huHead ⟨le_rfl, sub_nonneg.mpr h1c.le⟩]
      simpa only [Function.comp_apply, gammaHead, add_zero] using
        (extChartAt I (p 0)).left_inv (by
        rw [extChartAt_source]
        simpa only [gammaHead, add_zero] using
          hsrcHead0 ⟨le_rfl, sub_nonneg.mpr h1c.le⟩)
    rw [huh0Fun, huh1Fun, hthLen0]
    exact hleft'.trans hright.symm
  have huhcmp : ∀ v : (i : Fin 2) → timeH1 E (partitionIntervalLength th i),
      (∀ i, MapsTo (v i).toFun (Icc (0 : Real) (partitionIntervalLength th i))
        (extChartAt I (p 0)).target) →
      (extChartAt I (p 0)).symm ((v 0).toFun 0) =
        (extChartAt I (p 0)).symm ((uh 0).toFun 0) →
      (extChartAt I (p 0)).symm ((v 1).toFun (partitionIntervalLength th 1)) =
        (extChartAt I (p 0)).symm ((uh 1).toFun (partitionIntervalLength th 1)) →
      (extChartAt I (p 0)).symm ((v 0).toFun (partitionIntervalLength th 0)) =
        (extChartAt I (p 0)).symm ((v 1).toFun 0) →
      (∑ i : Fin 2, lChartAction S T (th i.castSucc) (p 0) (uh i)) ≤
        ∑ i : Fin 2, lChartAction S T (th i.castSucc) (p 0) (v i) := by
    intro v hvtar hv0 hv2 hvnode
    have hv0' : (extChartAt I (p 0)).symm ((v 0).toFun 0) = gamma (t 0) := by
      rw [hv0, huh0Fun]
      simpa only [hfin0c, add_zero] using hrecover 0 0
        ⟨le_rfl, by
          simpa only [partitionIntervalLength, hfin0s] using sub_nonneg.mpr (hpos 0).le⟩
    have hv2' : (extChartAt I (p 0)).symm
        ((v 1).toFun (c - t 1)) = gamma c := by
      have hv2a : (extChartAt I (p 0)).symm
          ((v 1).toFun (c - t 1)) =
          (extChartAt I (p 0)).symm (uHead.toFun (c - t 1)) := by
        calc
          (extChartAt I (p 0)).symm ((v 1).toFun (c - t 1)) =
              (extChartAt I (p 0)).symm ((v 1).toFun (partitionIntervalLength th 1)) := by
            exact congrArg
              (fun r : Real ↦ (extChartAt I (p 0)).symm ((v 1).toFun r))
              hthLen1.symm
          _ = (extChartAt I (p 0)).symm
              ((uh 1).toFun (partitionIntervalLength th 1)) := hv2
          _ = (extChartAt I (p 0)).symm
              (uHead.toFun (partitionIntervalLength th 1)) := by rw [huh1Fun]
          _ = (extChartAt I (p 0)).symm (uHead.toFun (c - t 1)) := by
            rw [hthLen1]
      have huc : (extChartAt I (p 0)).symm (uHead.toFun (c - t 1)) = gamma c := by
        rw [huHead ⟨sub_nonneg.mpr h1c.le, le_rfl⟩]
        simpa only [Function.comp_apply, gammaHead, add_sub_cancel] using
          (extChartAt I (p 0)).left_inv (by
          rw [extChartAt_source]
          simpa only [gammaHead, add_sub_cancel] using
            hsrcHead0 ⟨sub_nonneg.mpr h1c.le, le_rfl⟩)
      exact hv2a.trans huc
    let v0 : timeH1 E (t 1 - t 0) := hthLen0' ▸ v 0
    let v1 : timeH1 E (c - t 1) := hthLen1 ▸ v 1
    have hv0Fun : v0.toFun = (v 0).toFun := by
      exact nodeMatch_toFun_cast hthLen0'.symm (v 0)
    have hv1Fun : v1.toFun = (v 1).toFun := by
      exact nodeMatch_toFun_cast hthLen1.symm (v 1)
    have hv0tar : MapsTo v0.toFun (Icc (0 : Real) (t 1 - t 0))
        (extChartAt I (p 0)).target := by
      rw [hv0Fun]
      intro r hr
      exact hvtar 0 (by rwa [hthLen0'])
    have hv1tar : MapsTo v1.toFun (Icc (0 : Real) (c - t 1))
        (extChartAt I (p 0)).target := by
      rw [hv1Fun]
      intro r hr
      exact hvtar 1 (by rwa [hthLen1])
    have hvnode' : (extChartAt I (p 0)).symm (v0.toFun (t 1 - t 0)) =
        (extChartAt I (p 0)).symm (v1.toFun 0) := by
      calc
        (extChartAt I (p 0)).symm (v0.toFun (t 1 - t 0)) =
            (extChartAt I (p 0)).symm ((v 0).toFun (t 1 - t 0)) := by
          rw [hv0Fun]
        _ = (extChartAt I (p 0)).symm
            ((v 0).toFun (partitionIntervalLength th 0)) := by
          exact congrArg
            (fun r : Real ↦ (extChartAt I (p 0)).symm ((v 0).toFun r))
            hthLen0'.symm
        _ = (extChartAt I (p 0)).symm ((v 1).toFun 0) := hvnode
        _ = (extChartAt I (p 0)).symm (v1.toFun 0) := by rw [hv1Fun]
    have hhead := hcmpHead v0 v1 hv0tar hv1tar
      (by rw [hv0Fun]; exact hv0')
      (by rw [hv1Fun]; exact hv2') hvnode'
    have huh0Act : lChartAction S T (t 0) (p 0) (uh 0) =
        lChartAction S T (t 0) (p 0) (u 0) := by
      rw [huh0]
      exact nodeMatch_act_cast hthLen0 S T (t 0) (p 0) (u 0)
    have huh1Act : lChartAction S T (t 1) (p 0) (uh 1) =
        lChartAction S T (t 1) (p 0) uHead := by
      rw [huh1]
      exact nodeMatch_act_cast hthLen1 S T (t 1) (p 0) uHead
    have hv0Act : lChartAction S T (t 0) (p 0) v0 =
        lChartAction S T (t 0) (p 0) (v 0) := by
      exact nodeMatch_act_cast hthLen0'.symm S T (t 0) (p 0) (v 0)
    have hv1Act : lChartAction S T (t 1) (p 0) v1 =
        lChartAction S T (t 1) (p 0) (v 1) := by
      exact nodeMatch_act_cast hthLen1.symm S T (t 1) (p 0) (v 1)
    simpa only [Fin.sum_univ_two, hfin0c, hfin1c, hth0, hth1, huh0Act,
      huh1Act, hv0Act, hv1Act] using hhead
  have hmom := lChartAction_momentum_eq_of_pair_minimality (I := I) S hS T th (p 0) uh hthpos hthreg
    huhchart huhnode huhcmp
  have hmom' : chartGramOp (I := I) S.family (p 0)
        (T - (t 1) ^ 2, (u 0).toFun (partitionIntervalLength t 0))
        (derivWithin (u 0).toFun
          (Icc (0 : Real) (partitionIntervalLength t 0)) (partitionIntervalLength t 0)) =
      chartGramOp (I := I) S.family (p 0)
        (T - (t 1) ^ 2, uHead.toFun 0)
        (derivWithin uHead.toFun (Icc (0 : Real) (c - t 1)) 0) := by
    simpa only [hth1, huh0Fun, huh1Fun, hthLen0, hthLen1] using hmom
  have hheadDeriv : derivWithin (u 1).toFun
        (Icc (0 : Real) (partitionIntervalLength t 1)) 0 =
      tangentCoordChange I (p 0) (p 1) (gamma (t 1))
        (derivWithin uHead.toFun (Icc (0 : Real) (c - t 1)) 0) := by
    have hchange := chartDeriv_head I (sub_pos.mpr h1c)
      (by simpa [partitionIntervalLength, hfin1c, hfin1s] using
        sub_le_sub_right hc2 (t 1))
      (p 0) (p 1) gammaHead uHead (u 1)
      hsrcHead0
      (fun r hr ↦ hsrc 1 ⟨by simpa only [hfin1c] using
          (show t 1 ≤ t 1 + r from le_add_of_nonneg_right hr.1), by
        have hr2 : r ≤ c - t 1 := by
          simpa only [hfin1c] using hr.2
        simpa only [hfin1s] using (show t 1 + r ≤ t (Fin.last 2) by
          linarith [hr2, hc2])⟩)
      huHead (by
        intro r hr
        have hr' : r ∈ Icc (0 : Real) (partitionIntervalLength t 1) := by
          constructor
          · exact hr.1
          · have hr2 : r ≤ c - t 1 := by simpa only [hfin1c] using hr.2
            simpa only [partitionIntervalLength, hfin1c, hfin1s] using
              (show r ≤ t (Fin.last 2) - t 1 by linarith [hr2, hc2])
        simpa only [gammaHead, Function.comp_apply, hfin1c] using hrep 1 hr')
      huHeadC1 hu1c1
    simpa only [gammaHead, add_zero, hfin1c] using
      hchange ⟨le_rfl, sub_nonneg.mpr h1c.le⟩
  intro z
  have hpSrc : gamma (t 1) ∈ (extChartAt I (p 0)).source := by
    rw [extChartAt_source]
    exact hpNode
  have hqSrc : gamma (t 1) ∈ (extChartAt I (p 1)).source := by
    rw [extChartAt_source]
    exact hsrc 1 (by simpa using
      (show t 1 ∈ Icc (t 1) (t (Fin.last 2)) from ⟨le_rfl, (hpos 1).le⟩))
  have hu0Node : (u 0).toFun (partitionIntervalLength t 0) = extChartAt I (p 0) (gamma (t 1)) := by
    rw [hrep 0 ⟨by
      simpa only [partitionIntervalLength, hfin0s] using sub_nonneg.mpr (hpos 0).le, le_rfl⟩]
    simp only [partitionIntervalLength, hfin0s, add_sub_cancel]
  have huHead0 : uHead.toFun 0 = extChartAt I (p 0) (gamma (t 1)) := by
    simpa only [gammaHead, Function.comp_apply, add_zero] using
      huHead ⟨le_rfl, sub_nonneg.mpr h1c.le⟩
  have hu10 : (u 1).toFun 0 = extChartAt I (p 1) (gamma (t 1)) := by
    simpa only [add_zero, hfin1c] using
      hrep 1 ⟨le_rfl, by
        simpa only [partitionIntervalLength, hfin1c, hfin1s] using sub_nonneg.mpr (hpos 1).le⟩
  calc
    inner Real
        (chartGramOp (I := I) S.family (p 0)
          (T - (t 1) ^ 2, extChartAt I (p 0) (gamma (t 1)))
          (derivWithin (u 0).toFun
            (Icc (0 : Real) (partitionIntervalLength t 0)) (partitionIntervalLength t 0))) z =
      inner Real
        (chartGramOp (I := I) S.family (p 0)
          (T - (t 1) ^ 2, (u 0).toFun (partitionIntervalLength t 0))
          (derivWithin (u 0).toFun
            (Icc (0 : Real) (partitionIntervalLength t 0)) (partitionIntervalLength t 0))) z := by
        rw [hu0Node]
    _ = inner Real
        (chartGramOp (I := I) S.family (p 0)
          (T - (t 1) ^ 2, uHead.toFun 0)
          (derivWithin uHead.toFun (Icc (0 : Real) (c - t 1)) 0)) z := by
        rw [hmom']
    _ = inner Real
        (chartGramOp (I := I) S.family (p 0)
          (T - (t 1) ^ 2, extChartAt I (p 0) (gamma (t 1)))
          (derivWithin uHead.toFun (Icc (0 : Real) (c - t 1)) 0)) z := by
        rw [huHead0]
    _ = inner Real
        (chartGramOp (I := I) S.family (p 1)
          (T - (t 1) ^ 2, extChartAt I (p 1) (gamma (t 1)))
          (tangentCoordChange I (p 0) (p 1) (gamma (t 1))
            (derivWithin uHead.toFun (Icc (0 : Real) (c - t 1)) 0)))
        (tangentCoordChange I (p 0) (p 1) (gamma (t 1)) z) :=
      chartGramOp_change (I := I) S.family hpSrc hqSrc
        (T - (t 1) ^ 2)
        (derivWithin uHead.toFun (Icc (0 : Real) (c - t 1)) 0) z
    _ = inner Real
        (chartGramOp (I := I) S.family (p 1)
          (T - (t 1) ^ 2, extChartAt I (p 1) (gamma (t 1)))
          (derivWithin (u 1).toFun
            (Icc (0 : Real) (partitionIntervalLength t 1)) 0))
        (tangentCoordChange I (p 0) (p 1) (gamma (t 1)) z) := by
      rw [hheadDeriv]

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
