import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.VelocityMatching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.PieceLocalMinimality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularity
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.ChartTimeC1Overlap
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.CurveC1Glue

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
theorem lRegAction_minimizer_contMDiffOn_one_of_two_chart_pieces
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (t : Fin 3 → Real) (p : Fin 2 → M) (gamma : Real → M)
    (u : (i : Fin 2) → timeH1 E (lSegLen t i))
    (hpos : ∀ i : Fin 2, t i.castSucc < t i.succ)
    (hsrc : ∀ i, MapsTo gamma
      (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source)
    (hrep : ∀ i, EqOn (u i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (Icc (0 : Real) (lSegLen t i)))
    (hreg : ∀ s ∈ Icc (t 0) (t (Fin.last 2)), T - s ^ 2 ∈ D.regular)
    (hmin : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta (t 0) = gamma (t 0) →
      delta (t (Fin.last 2)) = gamma (t (Fin.last 2)) →
      lRegAction S T gamma (t 0) (t (Fin.last 2)) ≤
        lRegAction S T delta (t 0) (t (Fin.last 2))) :
    ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
      (Icc (t 0) (t (Fin.last 2))) := by
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
      (Icc (0 : Real) (lSegLen t i))
      (interior (extChartAt I (p i)).target) := by
    intro i r hr
    rw [hrep i hr, (isOpen_extChartAt_target (I := I) (p i)).interior_eq]
    apply (extChartAt I (p i)).map_source
    rw [extChartAt_source]
    exact hsrc i ⟨by linarith [hr.1], by
      have hr2 : r ≤ t i.succ - t i.castSucc := by
        simpa only [lSegLen] using hr.2
      linarith⟩
  have hrecover (i : Fin 2) (r : Real)
      (hr : r ∈ Icc (0 : Real) (lSegLen t i)) :
      (extChartAt I (p i)).symm ((u i).toFun r) =
        gamma (t i.castSucc + r) := by
    rw [hrep i hr]
    apply (extChartAt I (p i)).left_inv
    rw [extChartAt_source]
    exact hsrc i ⟨by linarith [hr.1], by
      have hr2 : r ≤ t i.succ - t i.castSucc := by
        simpa only [lSegLen] using hr.2
      linarith⟩
  have hnode : (extChartAt I (p 0)).symm
        ((u 0).toFun (lSegLen t 0)) =
      (extChartAt I (p 1)).symm ((u 1).toFun 0) := by
    rw [hrecover 0 (lSegLen t 0)
        ⟨by simpa only [lSegLen, hfin0s] using sub_nonneg.mpr (hpos 0).le,
          le_rfl⟩,
      hrecover 1 0 ⟨le_rfl, by
        simpa only [lSegLen, hfin1c, hfin1s] using sub_nonneg.mpr (hpos 1).le⟩]
    simp only [lSegLen, hfin0c, hfin0s, hfin1c, add_sub_cancel, add_zero]
  let hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  have hcmp : ∀ v : (i : Fin 2) → timeH1 E (lSegLen t i),
      (∀ i, MapsTo (v i).toFun (Icc (0 : Real) (lSegLen t i))
        (extChartAt I (p i)).target) →
      (extChartAt I (p 0)).symm ((v 0).toFun 0) =
        (extChartAt I (p 0)).symm ((u 0).toFun 0) →
      (extChartAt I (p 1)).symm ((v 1).toFun (lSegLen t 1)) =
        (extChartAt I (p 1)).symm ((u 1).toFun (lSegLen t 1)) →
      (extChartAt I (p 0)).symm ((v 0).toFun (lSegLen t 0)) =
        (extChartAt I (p 1)).symm ((v 1).toFun 0) →
      (∑ i : Fin 2, lChartAct S T (t i.castSucc) (p i) (u i)) ≤
        ∑ i : Fin 2, lChartAct S T (t i.castSucc) (p i) (v i) := by
    intro v hvtar hv0 hv2 hvnode
    have hu0 : (extChartAt I (p 0)).symm ((u 0).toFun 0) = gamma (t 0) := by
      simpa only [hfin0c, add_zero] using hrecover 0 0 ⟨le_rfl, by
        simpa only [lSegLen, hfin0s] using sub_nonneg.mpr (hpos 0).le⟩
    have hu2 : (extChartAt I (p 1)).symm
        ((u 1).toFun (lSegLen t 1)) = gamma (t (Fin.last 2)) := by
      have h := hrecover 1 (lSegLen t 1)
        ⟨by simpa only [lSegLen, hfin1c, hfin1s] using
            sub_nonneg.mpr (hpos 1).le, le_rfl⟩
      simpa only [lSegLen, hfin1c, hfin1s, add_sub_cancel] using h
    exact lChartAct_pair_le_of_lRegAction_minimizer (I := I) S hS.smoothMetric hSc T t htmono p gamma u
      hsrc hrep hreg hmin v hvtar (hv0.trans hu0) (hv2.trans hu2) hvnode
  have hlocal0 : IsLocalMinOn
      (lChartAct S T (t 0) (p 0)) (sameTimeEnds (u 0)) (u 0) :=
    lChartAct_isLocalMinOn_of_pair_minimality (I := I) S T t p u hchart hnode hcmp 0
  have hlocal1 : IsLocalMinOn
      (lChartAct S T (t 1) (p 1)) (sameTimeEnds (u 1)) (u 1) :=
    lChartAct_isLocalMinOn_of_pair_minimality (I := I) S T t p u hchart hnode hcmp 1
  have hreg0 : ∀ r, r ∈ Icc (0 : Real) (lSegLen t 0) →
      T - (t 0 + r) ^ 2 ∈ D.regular := by
    intro r hr
    apply hreg (t 0 + r)
    have hr2 : r ≤ t 1 - t 0 := by
      simpa only [lSegLen, hfin0c, hfin0s] using hr.2
    exact ⟨le_add_of_nonneg_right hr.1, by linarith [hr2, ht12.le]⟩
  have hreg1 : ∀ r, r ∈ Icc (0 : Real) (lSegLen t 1) →
      T - (t 1 + r) ^ 2 ∈ D.regular := by
    intro r hr
    apply hreg (t 1 + r)
    have hr2 : r ≤ t (Fin.last 2) - t 1 := by
      simpa only [lSegLen, hfin1c, hfin1s] using hr.2
    exact ⟨ht01.le.trans (le_add_of_nonneg_right hr.1), by linarith⟩
  obtain ⟨q0, _hq0, _hq0ae, hu0c1, _hu0d⟩ :=
    lChart_min_c1 (I := I) S hS T (t 0) (p 0)
      (by simpa only [lSegLen, hfin0c, hfin0s] using sub_pos.mpr ht01)
      (u 0) hreg0 (hchart 0) hlocal0
  obtain ⟨q1, _hq1, _hq1ae, hu1c1, _hu1d⟩ :=
    lChart_min_c1 (I := I) S hS T (t 1) (p 1)
      (by simpa only [lSegLen, hfin1c, hfin1s] using sub_pos.mpr ht12)
      (u 1) hreg1 (hchart 1) hlocal1
  have hgamma0 : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
      (Icc (t 0) (t 1)) :=
    curve_c1_local I (p 0) gamma (u 0) (hsrc 0) (hrep 0) hu0c1
  have hgamma1 : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
      (Icc (t 1) (t (Fin.last 2))) :=
    curve_c1_local I (p 1) gamma (u 1) (hsrc 1) (hrep 1) hu1c1
  have hp0der : derivWithin ((extChartAt I (p 0)) ∘ gamma)
        (Icc (t 0) (t 1)) (t 1) =
      derivWithin (u 0).toFun
        (Icc (0 : Real) (lSegLen t 0)) (lSegLen t 0) := by
    have hshift := chartDeriv_shift
      (a := t (0 : Fin 2).castSucc) (b := t (0 : Fin 2).succ)
      (r := lSegLen t 0) ((extChartAt I (p 0)) ∘ gamma) (u 0)
      (by
        intro r hr
        change (u 0).toFun r =
          ((extChartAt I (p 0)) ∘ gamma) (t (0 : Fin 2).castSucc + r)
        exact hrep 0 hr)
      ⟨sub_nonneg.mpr (hpos 0).le, le_rfl⟩
    simpa only [hfin0c, hfin0s, lSegLen, add_sub_cancel] using hshift
  have hp1der : derivWithin ((extChartAt I (p 1)) ∘ gamma)
        (Icc (t 1) (t (Fin.last 2))) (t 1) =
      derivWithin (u 1).toFun (Icc (0 : Real) (lSegLen t 1)) 0 := by
    have hshift := chartDeriv_shift
      (a := t (1 : Fin 2).castSucc) (b := t (1 : Fin 2).succ)
      (r := 0) ((extChartAt I (p 1)) ∘ gamma) (u 1)
      (by
        intro r hr
        change (u 1).toFun r =
          ((extChartAt I (p 1)) ∘ gamma) (t (1 : Fin 2).castSucc + r)
        exact hrep 1 hr)
      ⟨le_rfl, sub_nonneg.mpr (hpos 1).le⟩
    simpa only [hfin1c, hfin1s, lSegLen, add_zero] using hshift
  have hp0src : gamma (t 1) ∈ (chartAt H (p 0)).source :=
    hsrc 0 ⟨ht01.le, le_rfl⟩
  have hp1src : gamma (t 1) ∈ (chartAt H (p 1)).source :=
    hsrc 1 ⟨le_rfl, ht12.le⟩
  have hnodesrc : gamma (t 1) ∈ (chartAt H (gamma (t 1))).source :=
    mem_chart_source H (gamma (t 1))
  have hp0ext : gamma (t 1) ∈ (extChartAt I (p 0)).source := by
    rw [extChartAt_source]
    exact hp0src
  have hp1ext : gamma (t 1) ∈ (extChartAt I (p 1)).source := by
    rw [extChartAt_source]
    exact hp1src
  have hnodeext : gamma (t 1) ∈
      (extChartAt I (gamma (t 1))).source := by
    rw [extChartAt_source]
    exact hnodesrc
  have hchange0 := chartDeriv_change I (p 0) (gamma (t 1)) gamma
    hgamma0 ⟨ht01.le, le_rfl⟩
    (uniqueDiffOn_Icc ht01 (t 1) ⟨ht01.le, le_rfl⟩)
    (hsrc 0) hnodesrc
  have hchange1 := chartDeriv_change I (p 1) (gamma (t 1)) gamma
    hgamma1 ⟨le_rfl, ht12.le⟩
    (uniqueDiffOn_Icc ht12 (t 1) ⟨le_rfl, ht12.le⟩)
    (hsrc 1) hnodesrc
  have hvel := lRegAction_minimizer_velocity_eq_under_chart_change (I := I) S hS T t p gamma u
    hpos hsrc hrep hreg hmin
  have hder :
      derivWithin ((extChartAt I (gamma (t 1))) ∘ gamma)
          (Icc (t 0) (t 1)) (t 1) =
        derivWithin ((extChartAt I (gamma (t 1))) ∘ gamma)
          (Icc (t 1) (t (Fin.last 2))) (t 1) := by
    rw [hchange0, hchange1, hp0der, hp1der, ← hvel]
    exact (tangentCoordChange_comp (I := I) (w := p 0) (x := p 1)
      (y := gamma (t 1)) (z := gamma (t 1))
      ⟨⟨hp0ext, hp1ext⟩, hnodeext⟩).symm
  exact curve_c1_join ht01 ht12 hgamma0 hgamma1 hder

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
