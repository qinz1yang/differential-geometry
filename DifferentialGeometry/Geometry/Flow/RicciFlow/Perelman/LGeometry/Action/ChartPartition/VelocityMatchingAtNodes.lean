import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.RefinedSegmentMinimality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.SameChartMomentumMatching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.VelocityRegularity
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Chart.OverlapDerivative
import DifferentialGeometry.Topology.Manifold.CurveChart.InitialSegment
import DifferentialGeometry.Geometry.Operator.MetricFamilyGram

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

omit [CompactSpace M] in
theorem lRegAction_minimizer_velocity_eq_at_partition_nodes
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T a b : Real) {m : Nat} (t : Fin (m + 3) → Real)
    (ht0 : t 0 = a) (htlast : t (Fin.last (m + 2)) = b)
    (p : Fin (m + 2) → M) (gamma : Real → M) (hgamma : Continuous gamma)
    (u : (k : Fin (m + 2)) → timeH1 E (partitionIntervalLength t k))
    (hpos : ∀ k : Fin (m + 2), t k.castSucc < t k.succ)
    (hsrc : ∀ k, MapsTo gamma
      (Icc (t k.castSucc) (t k.succ)) (chartAt H (p k)).source)
    (hrep : ∀ k, EqOn (u k).toFun
      (fun r ↦ extChartAt I (p k) (gamma (t k.castSucc + r)))
      (Icc (0 : Real) (partitionIntervalLength t k)))
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular)
    (hmin : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta a = gamma a → delta b = gamma b →
      lRegAction S T gamma a b ≤ lRegAction S T delta a b)
    (q : Fin (m + 1)) :
    tangentCoordChange I (p q.castSucc) (p q.succ)
        (gamma (t q.succ.castSucc))
        (derivWithin (u q.castSucc).toFun
          (Icc (0 : Real) (partitionIntervalLength t q.castSucc))
          (partitionIntervalLength t q.castSucc)) =
      derivWithin (u q.succ).toFun
        (Icc (0 : Real) (partitionIntervalLength t q.succ)) 0 := by
  classical
  let i : Fin (m + 2) := q.castSucc
  let j : Fin (m + 2) := q.succ
  have hij : i.succ = j.castSucc := rfl
  have hpos0 : t i.castSucc < t i.succ := hpos i
  have hpos1 : t j.castSucc < t j.succ := hpos j
  have htmono : Monotone t := by
    apply Fin.monotone_iff_le_succ.mpr
    intro k
    exact (hpos k).le
  have hleft (k : Fin (m + 2)) : a ≤ t k.castSucc := by
    rw [← ht0]
    exact htmono (Fin.zero_le _)
  have hright (k : Fin (m + 2)) : t k.succ ≤ b := by
    rw [← htlast]
    exact htmono (Fin.le_last _)
  have hchart : ∀ k, MapsTo (u k).toFun
      (Icc (0 : Real) (partitionIntervalLength t k))
      (interior (extChartAt I (p k)).target) := by
    intro k r hr
    rw [hrep k hr]
    rw [(isOpen_extChartAt_target (I := I) (p k)).interior_eq]
    apply (extChartAt I (p k)).map_source
    rw [extChartAt_source]
    exact hsrc k ⟨by linarith [hr.1], by
      have hr2 : r ≤ t k.succ - t k.castSucc := by
        simpa only [partitionIntervalLength] using hr.2
      linarith⟩
  have hrecover (k : Fin (m + 2)) (r : Real)
      (hr : r ∈ Icc (0 : Real) (partitionIntervalLength t k)) :
      (extChartAt I (p k)).symm ((u k).toFun r) =
        gamma (t k.castSucc + r) := by
    rw [hrep k hr]
    apply (extChartAt I (p k)).left_inv
    rw [extChartAt_source]
    exact hsrc k ⟨by linarith [hr.1], by
      have hr2 : r ≤ t k.succ - t k.castSucc := by
        simpa only [partitionIntervalLength] using hr.2
      linarith⟩
  let hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  have hlocal1 : IsLocalMinOn
      (lChartAction S T (t j.castSucc) (p j))
      (sameTimeEnds (u j)) (u j) :=
    lChartAction_isLocalMinOn_of_lRegAction_minimizer (I := I) S hS.smoothMetric hSc T a b t htmono ht0 htlast
      p gamma hgamma u hsrc hrep hreg hmin j hpos1
  have hreg1 : ∀ r, r ∈ Icc (0 : Real) (partitionIntervalLength t j) →
      T - (t j.castSucc + r) ^ 2 ∈ D.regular := by
    intro r hr
    apply hreg (t j.castSucc + r)
    constructor
    · linarith [hleft j, hr.1]
    · have hr2 : r ≤ t j.succ - t j.castSucc := by
        simpa only [partitionIntervalLength] using hr.2
      linarith [hright j]
  obtain ⟨q1, _hq1c, _hq1ae, hu1c1, _hu1d⟩ :=
    lChartAction_minimizer_contDiffOn_one (I := I) S hS T (t j.castSucc) (p j)
      (by simpa only [partitionIntervalLength] using sub_pos.mpr hpos1)
      (u j) hreg1 (hchart j) hlocal1
  have hgamma1 : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
      (Icc (t j.castSucc) (t j.succ)) :=
    curve_c1_local I (p j) gamma (u j) (hsrc j) (hrep j) hu1c1
  have hpNode : gamma (t j.castSucc) ∈ (chartAt H (p i)).source := by
    apply hsrc i
    rw [← hij]
    exact ⟨hpos0.le, le_rfl⟩
  let d : Real := (t j.castSucc + t j.succ) / 2
  have hjd : t j.castSucc < d := by
    dsimp only [d]
    linarith
  have hdj : d < t j.succ := by
    dsimp only [d]
    linarith
  have hgammaMid : ContinuousOn gamma (Icc (t j.castSucc) d) :=
    hgamma1.continuousOn.mono (Icc_subset_Icc le_rfl hdj.le)
  obtain ⟨c, hc0, hcd, hsrcHead⟩ :=
    DifferentialGeometry.Geometry.exists_chart_initial_segment (H := H)
      hjd hgammaMid hpNode
  have hc1 : c < t j.succ := hcd.trans_lt hdj
  let gammaHead : Real → M := fun r ↦ gamma (t j.castSucc + r)
  have hshiftHead : MapsTo (fun r : Real ↦ t j.castSucc + r)
      (Icc (0 : Real) (c - t j.castSucc))
      (Icc (t j.castSucc) (t j.succ)) := by
    intro r hr
    exact ⟨le_add_of_nonneg_right hr.1, by linarith [hr.2, hc1.le]⟩
  have hgammaHead : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gammaHead
      (Icc (0 : Real) (c - t j.castSucc)) :=
    hgamma1.comp (contDiffOn_const.add contDiffOn_id).contMDiffOn hshiftHead
  have hsrcHead0 : MapsTo gammaHead
      (Icc (0 : Real) (c - t j.castSucc))
      (chartAt H (p i)).source := by
    intro r hr
    exact hsrcHead ⟨le_add_of_nonneg_right hr.1, by linarith [hr.2]⟩
  let uHead : timeH1 E (c - t j.castSucc) :=
    chartTimeH1 I (sub_nonneg.mpr hc0.le) (p i) gammaHead hgammaHead hsrcHead0
  have huHead : EqOn uHead.toFun ((extChartAt I (p i)) ∘ gammaHead)
      (Icc (0 : Real) (c - t j.castSucc)) :=
    chartTimeH1_toFun I (sub_nonneg.mpr hc0.le) (p i)
      gammaHead hgammaHead hsrcHead0
  have huHeadC1 : ContDiffOn Real 1 uHead.toFun
      (Icc (0 : Real) (c - t j.castSucc)) :=
    (chartCoord_contDiff I (p i) gammaHead hgammaHead hsrcHead0).congr
      (fun r hr ↦ huHead hr)
  let th : Fin 3 → Real :=
    Fin.cases (t i.castSucc)
      (Fin.cases (t j.castSucc) (Fin.cases c fun k ↦ Fin.elim0 k))
  let uh : (k : Fin 2) → timeH1 E (partitionIntervalLength th k) :=
    Fin.cases (u i) (Fin.cases uHead fun k ↦ Fin.elim0 k)
  have hth0c : th (0 : Fin 2).castSucc = t i.castSucc := rfl
  have hth0s : th (0 : Fin 2).succ = t j.castSucc := rfl
  have hth1c : th (1 : Fin 2).castSucc = t j.castSucc := by
    change th (Fin.succ 0) = t j.castSucc
    rfl
  have hth1s : th (1 : Fin 2).succ = c := by
    change th (Fin.succ (Fin.succ 0)) = c
    rfl
  have hthMid : th (1 : Fin 3) = t j.castSucc := rfl
  have hth1cStep : th (Fin.succ (0 : Fin 1)).castSucc = t j.castSucc := rfl
  have hth1sStep : th (Fin.succ (0 : Fin 1)).succ = c := rfl
  have hthLen0 : partitionIntervalLength th 0 = partitionIntervalLength t i := by
    simp only [partitionIntervalLength]
    rw [hth0c, hth0s, ← congrArg t hij]
  have hthLen1 : partitionIntervalLength th 1 = c - t j.castSucc := by
    simp only [partitionIntervalLength]
    rw [hth1c, hth1s]
  have huh0 : (uh 0).toFun = (u i).toFun := rfl
  have huh1 : (uh 1).toFun = uHead.toFun := by
    change (uh (Fin.succ 0)).toFun = uHead.toFun
    rfl
  have huh0Step : (uh (0 : Fin 2)).toFun = (u i).toFun := rfl
  have huh1Step : (uh (Fin.succ (0 : Fin 1))).toFun = uHead.toFun := rfl
  have hthpos : ∀ k : Fin 2, th k.castSucc < th k.succ := by
    intro k
    exact Fin.cases
      (by rw [hth0c, hth0s]; exact hpos0)
      (Fin.cases (by rw [hth1cStep, hth1sStep]; exact hc0)
        fun z ↦ Fin.elim0 z) k
  have hthreg : ∀ k r, r ∈ Icc (0 : Real) (partitionIntervalLength th k) →
      T - (th k.castSucc + r) ^ 2 ∈ D.regular := by
    intro k r hr
    fin_cases k
    · change r ∈ Icc (0 : Real) (partitionIntervalLength th 0) at hr
      change T - (t i.castSucc + r) ^ 2 ∈ D.regular
      apply hreg (t i.castSucc + r)
      have hr2 : r ≤ t j.castSucc - t i.castSucc := by
        rw [hthLen0] at hr
        simpa only [partitionIntervalLength, congrArg t hij] using hr.2
      have hnodeRight : t j.castSucc ≤ b := by
        rw [← hij]
        exact hright i
      exact ⟨by linarith [hleft i, hr.1], by linarith [hr2, hnodeRight]⟩
    · change r ∈ Icc (0 : Real) (partitionIntervalLength th 1) at hr
      change T - (t j.castSucc + r) ^ 2 ∈ D.regular
      apply hreg (t j.castSucc + r)
      have hr2 : r ≤ c - t j.castSucc := by
        rw [hthLen1] at hr
        exact hr.2
      exact ⟨by linarith [hleft j, hr.1], by
        linarith [hr2, hc1.le, hright j]⟩
  have huhchart : ∀ k, MapsTo (uh k).toFun
      (Icc (0 : Real) (partitionIntervalLength th k))
      (interior (extChartAt I (p i)).target) := by
    intro k r hr
    fin_cases k
    · change r ∈ Icc (0 : Real) (partitionIntervalLength th 0) at hr
      change (uh 0).toFun r ∈ interior (extChartAt I (p i)).target
      rw [hthLen0] at hr
      rw [huh0]
      exact hchart i hr
    · change r ∈ Icc (0 : Real) (partitionIntervalLength th 1) at hr
      change (uh 1).toFun r ∈ interior (extChartAt I (p i)).target
      rw [hthLen1] at hr
      rw [huh1]
      rw [(isOpen_extChartAt_target (I := I) (p i)).interior_eq, huHead hr]
      apply (extChartAt I (p i)).map_source
      rw [extChartAt_source]
      exact hsrcHead0 hr
  have huhnode : (extChartAt I (p i)).symm
        ((uh 0).toFun (partitionIntervalLength th 0)) =
      (extChartAt I (p i)).symm ((uh 1).toFun 0) := by
    have hleftNode := hrecover i (partitionIntervalLength t i)
      ⟨by simpa only [partitionIntervalLength] using sub_nonneg.mpr hpos0.le, le_rfl⟩
    have hleftNode' : (extChartAt I (p i)).symm
        ((u i).toFun (partitionIntervalLength t i)) = gamma (t j.castSucc) := by
      simpa only [partitionIntervalLength, hij, add_sub_cancel] using hleftNode
    have hrightNode : (extChartAt I (p i)).symm (uHead.toFun 0) =
        gamma (t j.castSucc) := by
      rw [huHead ⟨le_rfl, sub_nonneg.mpr hc0.le⟩]
      simpa only [Function.comp_apply, gammaHead, add_zero] using
        (extChartAt I (p i)).left_inv (by
          rw [extChartAt_source]
          simpa only [gammaHead, add_zero] using
            hsrcHead0 ⟨le_rfl, sub_nonneg.mpr hc0.le⟩)
    rw [huh0, huh1, hthLen0]
    exact hleftNode'.trans hrightNode.symm
  have huhcmp : ∀ v : (k : Fin 2) → timeH1 E (partitionIntervalLength th k),
      (∀ k, MapsTo (v k).toFun (Icc (0 : Real) (partitionIntervalLength th k))
        (extChartAt I (p i)).target) →
      (extChartAt I (p i)).symm ((v 0).toFun 0) =
        (extChartAt I (p i)).symm ((uh 0).toFun 0) →
      (extChartAt I (p i)).symm ((v 1).toFun (partitionIntervalLength th 1)) =
        (extChartAt I (p i)).symm ((uh 1).toFun (partitionIntervalLength th 1)) →
      (extChartAt I (p i)).symm ((v 0).toFun (partitionIntervalLength th 0)) =
        (extChartAt I (p i)).symm ((v 1).toFun 0) →
      (∑ k : Fin 2, lChartAction S T (th k.castSucc) (p i) (uh k)) ≤
        ∑ k : Fin 2, lChartAction S T (th k.castSucc) (p i) (v k) := by
    intro v hvtar hv0 hv2 hvnode
    have hv0' : (extChartAt I (p i)).symm ((v 0).toFun 0) =
        gamma (t i.castSucc) := by
      rw [hv0]
      rw [huh0]
      simpa only [add_zero] using hrecover i 0 ⟨le_rfl, by
        simpa only [partitionIntervalLength] using sub_nonneg.mpr hpos0.le⟩
    have hv2' : (extChartAt I (p i)).symm
        ((v 1).toFun (c - t j.castSucc)) = gamma c := by
      have hv2a : (extChartAt I (p i)).symm
          ((v 1).toFun (c - t j.castSucc)) =
          (extChartAt I (p i)).symm (uHead.toFun (c - t j.castSucc)) := by
        have hv2u : (extChartAt I (p i)).symm
              ((v 1).toFun (partitionIntervalLength th 1)) =
            (extChartAt I (p i)).symm (uHead.toFun (partitionIntervalLength th 1)) := by
          rw [← huh1]
          exact hv2
        exact (congrArg (fun r ↦ (extChartAt I (p i)).symm ((v 1).toFun r))
          hthLen1.symm).trans (hv2u.trans
            (congrArg (fun r ↦ (extChartAt I (p i)).symm (uHead.toFun r))
              hthLen1))
      have huc : (extChartAt I (p i)).symm
          (uHead.toFun (c - t j.castSucc)) = gamma c := by
        rw [huHead ⟨sub_nonneg.mpr hc0.le, le_rfl⟩]
        simpa only [Function.comp_apply, gammaHead, add_sub_cancel] using
          (extChartAt I (p i)).left_inv (by
            rw [extChartAt_source]
            simpa only [gammaHead, add_sub_cancel] using
              hsrcHead0 ⟨sub_nonneg.mpr hc0.le, le_rfl⟩)
      exact hv2a.trans huc
    have hcast_toFun {x y : Real} (hxy : x = y) (w : timeH1 E x) :
        (hxy ▸ w : timeH1 E y).toFun = w.toFun := by
      subst y
      rfl
    let v0t : timeH1 E (partitionIntervalLength t i) := hthLen0 ▸ v 0
    let v1t : timeH1 E (c - t j.castSucc) := hthLen1 ▸ v 1
    have hv0tf : v0t.toFun = (v 0).toFun := hcast_toFun hthLen0 (v 0)
    have hv1tf : v1t.toFun = (v 1).toFun := hcast_toFun hthLen1 (v 1)
    have hvtar0 : MapsTo v0t.toFun (Icc (0 : Real) (partitionIntervalLength t i))
        (extChartAt I (p i)).target := by
      rw [hv0tf, ← hthLen0]
      exact hvtar 0
    have hvtar1 : MapsTo v1t.toFun (Icc (0 : Real) (c - t j.castSucc))
        (extChartAt I (p i)).target := by
      rw [hv1tf, ← hthLen1]
      exact hvtar 1
    have hv0t : (extChartAt I (p i)).symm (v0t.toFun 0) =
        gamma (t i.castSucc) := by
      rw [hv0tf]
      exact hv0'
    have hv2t : (extChartAt I (p i)).symm
        (v1t.toFun (c - t j.castSucc)) = gamma c := by
      rw [hv1tf]
      exact hv2'
    have hvnodet : (extChartAt I (p i)).symm
          (v0t.toFun (partitionIntervalLength t i)) =
        (extChartAt I (p i)).symm (v1t.toFun 0) := by
      rw [hv0tf, hv1tf, ← hthLen0]
      exact hvnode
    have hcast_act {x y : Real} (hxy : x = y) (s : Real) (p0 : M)
        (w : timeH1 E x) :
        lChartAction S T s p0 (hxy ▸ w : timeH1 E y) =
          lChartAction S T s p0 w := by
      subst y
      rfl
    have hcmp := lChartAction_refined_adjacent_pair_le_of_lRegAction_minimizer (I := I) S hS.smoothMetric hSc T a b t htmono
      ht0 htlast p gamma hgamma u hsrc hrep hreg hmin q c hpos0 hc0 hc1
      uHead hsrcHead
      (by
        intro r hr
        simpa only [i, j, gammaHead, Function.comp_apply] using huHead hr)
      (by simpa only [i] using v0t)
      (by simpa only [j] using v1t)
      (by simpa only [i] using hvtar0)
      (by simpa only [i, j] using hvtar1)
      (by simpa only [i] using hv0t)
      (by simpa only [i, j] using hv2t)
      (by simpa only [i, j] using hvnodet)
    have hv0act : lChartAction S T (t i.castSucc) (p i) v0t =
        lChartAction S T (t i.castSucc) (p i) (v 0) :=
      hcast_act hthLen0 (t i.castSucc) (p i) (v 0)
    have hv1act : lChartAction S T (t j.castSucc) (p i) v1t =
        lChartAction S T (t j.castSucc) (p i) (v 1) :=
      hcast_act hthLen1 (t j.castSucc) (p i) (v 1)
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    change lChartAction S T (t i.castSucc) (p i) (u i) +
        lChartAction S T (t j.castSucc) (p i) uHead ≤
      lChartAction S T (t i.castSucc) (p i) (v 0) +
        lChartAction S T (t j.castSucc) (p i) (v 1)
    rw [← hv0act, ← hv1act]
    simpa only [i, j] using hcmp
  have hmom := lChartAction_momentum_eq_of_pair_minimality (I := I) S hS T th (p i) uh hthpos hthreg
    huhchart huhnode huhcmp
  have hmom' : chartGramOp (I := I) S.family (p i)
        (T - (t j.castSucc) ^ 2, (u i).toFun (partitionIntervalLength t i))
        (derivWithin (u i).toFun
          (Icc (0 : Real) (partitionIntervalLength t i)) (partitionIntervalLength t i)) =
      chartGramOp (I := I) S.family (p i)
        (T - (t j.castSucc) ^ 2, uHead.toFun 0)
        (derivWithin uHead.toFun
          (Icc (0 : Real) (c - t j.castSucc)) 0) := by
    have hmom' := hmom
    rw [huh0, huh1, hthLen0, hthLen1, hthMid] at hmom'
    exact hmom'
  have hheadDeriv : derivWithin (u j).toFun
        (Icc (0 : Real) (partitionIntervalLength t j)) 0 =
      tangentCoordChange I (p i) (p j) (gamma (t j.castSucc))
        (derivWithin uHead.toFun
          (Icc (0 : Real) (c - t j.castSucc)) 0) := by
    have hchange := chartDeriv_head I (sub_pos.mpr hc0)
      (by simpa only [partitionIntervalLength] using sub_le_sub_right hc1.le (t j.castSucc))
      (p i) (p j) gammaHead uHead (u j) hsrcHead0
      (fun r hr ↦ hsrc j ⟨le_add_of_nonneg_right hr.1, by
        have hr2 : r ≤ c - t j.castSucc := hr.2
        linarith [hr2, hc1.le]⟩)
      huHead (by
        intro r hr
        have hr' : r ∈ Icc (0 : Real) (partitionIntervalLength t j) := by
          exact ⟨hr.1, by
            simpa only [partitionIntervalLength] using
              (show r ≤ t j.succ - t j.castSucc by linarith [hr.2, hc1.le])⟩
        simpa only [gammaHead, Function.comp_apply] using hrep j hr')
      huHeadC1 hu1c1
    simpa only [gammaHead, add_zero] using
      hchange ⟨le_rfl, sub_nonneg.mpr hc0.le⟩
  have hpSrc : gamma (t j.castSucc) ∈ (extChartAt I (p i)).source := by
    rw [extChartAt_source]
    exact hpNode
  have hqSrc : gamma (t j.castSucc) ∈ (extChartAt I (p j)).source := by
    rw [extChartAt_source]
    exact hsrc j ⟨le_rfl, hpos1.le⟩
  have hu0Node : (u i).toFun (partitionIntervalLength t i) =
      extChartAt I (p i) (gamma (t j.castSucc)) := by
    rw [hrep i ⟨by
      simpa only [partitionIntervalLength] using sub_nonneg.mpr hpos0.le, le_rfl⟩]
    simp only [partitionIntervalLength, hij, add_sub_cancel]
  have huHead0 : uHead.toFun 0 =
      extChartAt I (p i) (gamma (t j.castSucc)) := by
    simpa only [gammaHead, Function.comp_apply, add_zero] using
      huHead ⟨le_rfl, sub_nonneg.mpr hc0.le⟩
  let v₀ := derivWithin (u i).toFun
    (Icc (0 : Real) (partitionIntervalLength t i)) (partitionIntervalLength t i)
  let vh := derivWithin uHead.toFun (Icc (0 : Real) (c - t j.castSucc)) 0
  let v₁ := derivWithin (u j).toFun (Icc (0 : Real) (partitionIntervalLength t j)) 0
  let J := tangentCoordChange I (p i) (p j) (gamma (t j.castSucc))
  let Jrev := tangentCoordChange I (p j) (p i) (gamma (t j.castSucc))
  have hheadDeriv' : v₁ = J vh := by
    simpa only [v₁, J, vh] using hheadDeriv
  have hJrev (y : E) : J (Jrev y) = y := by
    calc
      J (Jrev y) =
          tangentCoordChange I (p j) (p j) (gamma (t j.castSucc)) y :=
        tangentCoordChange_comp (I := I) (w := p j) (x := p i)
          (y := p j) (z := gamma (t j.castSucc)) ⟨⟨hqSrc, hpSrc⟩, hqSrc⟩
      _ = y := tangentCoordChange_self (I := I) hqSrc
  have hmomCoord : chartGramOp (I := I) S.family (p i)
        (T - (t j.castSucc) ^ 2, extChartAt I (p i) (gamma (t j.castSucc))) v₀ =
      chartGramOp (I := I) S.family (p i)
        (T - (t j.castSucc) ^ 2, extChartAt I (p i) (gamma (t j.castSucc))) vh := by
    simpa only [v₀, vh, hu0Node, huHead0] using hmom'
  have hGram : chartGramOp (I := I) S.family (p j)
        (T - (t j.castSucc) ^ 2, extChartAt I (p j) (gamma (t j.castSucc)))
        (J v₀) =
      chartGramOp (I := I) S.family (p j)
        (T - (t j.castSucc) ^ 2, extChartAt I (p j) (gamma (t j.castSucc)))
        v₁ := by
    apply ext_inner_right Real
    intro y
    let z := Jrev y
    have hzy : J z = y := hJrev y
    calc
      inner Real
          (chartGramOp (I := I) S.family (p j)
            (T - (t j.castSucc) ^ 2, extChartAt I (p j) (gamma (t j.castSucc)))
            (J v₀)) y =
        inner Real
          (chartGramOp (I := I) S.family (p j)
            (T - (t j.castSucc) ^ 2, extChartAt I (p j) (gamma (t j.castSucc)))
            (J v₀)) (J z) := by rw [hzy]
      _ = inner Real
          (chartGramOp (I := I) S.family (p i)
            (T - (t j.castSucc) ^ 2, extChartAt I (p i) (gamma (t j.castSucc)))
            v₀) z :=
        (chartGramOp_change (I := I) S.family hpSrc hqSrc
          (T - (t j.castSucc) ^ 2) v₀ z).symm
      _ = inner Real
          (chartGramOp (I := I) S.family (p i)
            (T - (t j.castSucc) ^ 2, extChartAt I (p i) (gamma (t j.castSucc)))
            vh) z := by rw [hmomCoord]
      _ = inner Real
          (chartGramOp (I := I) S.family (p j)
            (T - (t j.castSucc) ^ 2, extChartAt I (p j) (gamma (t j.castSucc)))
            (J vh)) (J z) :=
        chartGramOp_change (I := I) S.family hpSrc hqSrc
          (T - (t j.castSucc) ^ 2) vh z
      _ = inner Real
          (chartGramOp (I := I) S.family (p j)
            (T - (t j.castSucc) ^ 2, extChartAt I (p j) (gamma (t j.castSucc)))
            v₁) y := by
        rw [← hzy, hheadDeriv']
  have htreg : T - (t j.castSucc) ^ 2 ∈ D.regular :=
    hreg (t j.castSucc) ⟨hleft j, (hpos1.le.trans (hright j))⟩
  have htarget : extChartAt I (p j) (gamma (t j.castSucc)) ∈
      interior (extChartAt I (p j)).target := by
    rw [(isOpen_extChartAt_target (I := I) (p j)).interior_eq]
    exact (extChartAt I (p j)).map_source hqSrc
  have hunit : IsUnit
      (chartGramOp (I := I) S.family (p j)
        (T - (t j.castSucc) ^ 2, extChartAt I (p j) (gamma (t j.castSucc)))) :=
    chartGramOp_unit (I := I) hS.smoothMetric
      (J := {T - (t j.castSucc) ^ 2})
      (by simpa only [singleton_subset_iff] using htreg)
      (p j) (K := {extChartAt I (p j) (gamma (t j.castSucc))})
      (by simpa only [singleton_subset_iff] using htarget) _ (by simp)
  have hinj : Function.Injective
      (chartGramOp (I := I) S.family (p j)
        (T - (t j.castSucc) ^ 2, extChartAt I (p j) (gamma (t j.castSucc)))) :=
    (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).1
  simpa only [i, j, J, v₀, v₁] using hinj hGram

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
