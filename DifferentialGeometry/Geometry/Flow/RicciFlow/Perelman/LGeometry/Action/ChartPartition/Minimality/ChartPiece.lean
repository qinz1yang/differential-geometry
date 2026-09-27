import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.LocalMinimality

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Function Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable {D : RealTimeInterval}

theorem lChartAction_isLocalMinOn_of_pair_minimality
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (t : Fin 3 → Real) (p : Fin 2 → M)
    (u : (i : Fin 2) → timeH1 E (partitionIntervalLength t i))
    (hchart : ∀ i, MapsTo (u i).toFun
      (Icc (0 : Real) (partitionIntervalLength t i))
      (interior (extChartAt I (p i)).target))
    (hnode : (extChartAt I (p 0)).symm
        ((u 0).toFun (partitionIntervalLength t 0)) =
      (extChartAt I (p 1)).symm ((u 1).toFun 0))
    (hcmp : ∀ v : (i : Fin 2) → timeH1 E (partitionIntervalLength t i),
      (∀ i, MapsTo (v i).toFun
        (Icc (0 : Real) (partitionIntervalLength t i)) (extChartAt I (p i)).target) →
      (extChartAt I (p 0)).symm ((v 0).toFun 0) =
        (extChartAt I (p 0)).symm ((u 0).toFun 0) →
      (extChartAt I (p 1)).symm ((v 1).toFun (partitionIntervalLength t 1)) =
        (extChartAt I (p 1)).symm ((u 1).toFun (partitionIntervalLength t 1)) →
      (extChartAt I (p 0)).symm ((v 0).toFun (partitionIntervalLength t 0)) =
        (extChartAt I (p 1)).symm ((v 1).toFun 0) →
      (∑ i : Fin 2, lChartAction S T (t i.castSucc) (p i) (u i)) ≤
        ∑ i : Fin 2, lChartAction S T (t i.castSucc) (p i) (v i))
    (i : Fin 2) :
    IsLocalMinOn (lChartAction S T (t i.castSucc) (p i))
      (sameTimeEnds (u i)) (u i) := by
  classical
  fin_cases i
  · change IsLocalMinOn (lChartAction S T (t 0) (p 0))
      (sameTimeEnds (u 0)) (u 0)
    let K : Set E := (u 0).toFun '' Icc (0 : Real) (partitionIntervalLength t 0)
    have hKc : IsCompact K :=
      isCompact_Icc.image_of_continuousOn (u 0).continuousOn_toFun
    have hKtar : K ⊆ (extChartAt I (p 0)).target := by
      rintro _ ⟨r, hr, rfl⟩
      exact interior_subset (hchart 0 hr)
    obtain ⟨d, hd, hdsub⟩ := hKc.exists_thickening_subset_open
      (isOpen_extChartAt_target (I := I) (p 0)) hKtar
    let c : Real := 1 + Real.sqrt (partitionIntervalLength t 0)
    have hc : 0 < c := by
      dsimp only [c]
      positivity
    let eps : Real := d / c
    have heps : 0 < eps := div_pos hd hc
    rw [IsLocalMinOn, IsMinFilter]
    filter_upwards
      [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (u 0) heps),
        self_mem_nhdsWithin] with v hvball hvends
    have hvnorm : ‖v - u 0‖ < eps := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hvball
    have hvtar : MapsTo v.toFun
        (Icc (0 : Real) (partitionIntervalLength t 0)) (extChartAt I (p 0)).target := by
      intro r hr
      apply hdsub
      rw [Metric.mem_thickening_iff]
      refine ⟨(u 0).toFun r, ⟨r, hr, rfl⟩, ?_⟩
      have hfun : (v - u 0).toFun r = v.toFun r - (u 0).toFun r := by
        calc
          (v - u 0).toFun r = (v + -(u 0)).toFun r := by
            rw [sub_eq_add_neg]
          _ = v.toFun r + (-(u 0)).toFun r :=
            timeH1.toFun_add v (-(u 0)) hr
          _ = v.toFun r + (-1 : Real) • (u 0).toFun r := by
            rw [show -(u 0) = (-1 : Real) • u 0 by
              simp only [neg_one_smul], timeH1.toFun_smul (-1 : Real) (u 0) hr]
          _ = v.toFun r - (u 0).toFun r := by
            simp only [neg_one_smul, sub_eq_add_neg]
      calc
        dist (v.toFun r) ((u 0).toFun r) = ‖(v - u 0).toFun r‖ := by
          rw [dist_eq_norm, hfun]
        _ ≤ c * ‖v - u 0‖ := by
          simpa only [c] using (v - u 0).norm_toFun_le_norm hr
        _ < c * eps := mul_lt_mul_of_pos_left hvnorm hc
        _ = d := by
          dsimp only [eps]
          exact mul_div_cancel₀ d hc.ne'
    let w : (j : Fin 2) → timeH1 E (partitionIntervalLength t j) :=
      Fin.cases (by simpa using v)
        (Fin.cases (by simpa using u 1) (fun j ↦ Fin.elim0 j))
    have hw0eq : w 0 = v := rfl
    have hw1eq : w 1 = u 1 := rfl
    have hwtar : ∀ j, MapsTo (w j).toFun
        (Icc (0 : Real) (partitionIntervalLength t j)) (extChartAt I (p j)).target := by
      intro j
      refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun j ↦ Fin.elim0 j) j) j
      · exact hvtar
      · exact (hchart 1).mono_right interior_subset
    have hw0 : (extChartAt I (p 0)).symm ((w 0).toFun 0) =
        (extChartAt I (p 0)).symm ((u 0).toFun 0) := by
      rw [hw0eq]
      simpa only [← timeH1.toFun_zero] using
        congrArg (extChartAt I (p 0)).symm hvends.1
    have hw2 : (extChartAt I (p 1)).symm
        ((w 1).toFun (partitionIntervalLength t 1)) =
        (extChartAt I (p 1)).symm ((u 1).toFun (partitionIntervalLength t 1)) := by
      rw [hw1eq]
    have hwnode : (extChartAt I (p 0)).symm
        ((w 0).toFun (partitionIntervalLength t 0)) =
        (extChartAt I (p 1)).symm ((w 1).toFun 0) := by
      rw [hw0eq, hw1eq]
      simpa only [← timeH1.toFun_zero] using
        (congrArg (extChartAt I (p 0)).symm hvends.2).trans hnode
    have hc' := hcmp w hwtar hw0 hw2 hwnode
    simp only [Fin.sum_univ_two] at hc'
    change
      lChartAction S T (t 0) (p 0) (u 0) +
          lChartAction S T (t 1) (p 1) (u 1) ≤
        lChartAction S T (t 0) (p 0) (w 0) +
          lChartAction S T (t 1) (p 1) (w 1) at hc'
    rw [hw0eq, hw1eq] at hc'
    linarith
  · change IsLocalMinOn (lChartAction S T (t 1) (p 1))
      (sameTimeEnds (u 1)) (u 1)
    let K : Set E := (u 1).toFun '' Icc (0 : Real) (partitionIntervalLength t 1)
    have hKc : IsCompact K :=
      isCompact_Icc.image_of_continuousOn (u 1).continuousOn_toFun
    have hKtar : K ⊆ (extChartAt I (p 1)).target := by
      rintro _ ⟨r, hr, rfl⟩
      exact interior_subset (hchart 1 hr)
    obtain ⟨d, hd, hdsub⟩ := hKc.exists_thickening_subset_open
      (isOpen_extChartAt_target (I := I) (p 1)) hKtar
    let c : Real := 1 + Real.sqrt (partitionIntervalLength t 1)
    have hc : 0 < c := by
      dsimp only [c]
      positivity
    let eps : Real := d / c
    have heps : 0 < eps := div_pos hd hc
    rw [IsLocalMinOn, IsMinFilter]
    filter_upwards
      [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (u 1) heps),
        self_mem_nhdsWithin] with v hvball hvends
    have hvnorm : ‖v - u 1‖ < eps := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hvball
    have hvtar : MapsTo v.toFun
        (Icc (0 : Real) (partitionIntervalLength t 1)) (extChartAt I (p 1)).target := by
      intro r hr
      apply hdsub
      rw [Metric.mem_thickening_iff]
      refine ⟨(u 1).toFun r, ⟨r, hr, rfl⟩, ?_⟩
      have hfun : (v - u 1).toFun r = v.toFun r - (u 1).toFun r := by
        calc
          (v - u 1).toFun r = (v + -(u 1)).toFun r := by
            rw [sub_eq_add_neg]
          _ = v.toFun r + (-(u 1)).toFun r :=
            timeH1.toFun_add v (-(u 1)) hr
          _ = v.toFun r + (-1 : Real) • (u 1).toFun r := by
            rw [show -(u 1) = (-1 : Real) • u 1 by
              simp only [neg_one_smul], timeH1.toFun_smul (-1 : Real) (u 1) hr]
          _ = v.toFun r - (u 1).toFun r := by
            simp only [neg_one_smul, sub_eq_add_neg]
      calc
        dist (v.toFun r) ((u 1).toFun r) = ‖(v - u 1).toFun r‖ := by
          rw [dist_eq_norm, hfun]
        _ ≤ c * ‖v - u 1‖ := by
          simpa only [c] using (v - u 1).norm_toFun_le_norm hr
        _ < c * eps := mul_lt_mul_of_pos_left hvnorm hc
        _ = d := by
          dsimp only [eps]
          exact mul_div_cancel₀ d hc.ne'
    let w : (j : Fin 2) → timeH1 E (partitionIntervalLength t j) :=
      Fin.cases (by simpa using u 0)
        (Fin.cases (by simpa using v) (fun j ↦ Fin.elim0 j))
    have hw0eq : w 0 = u 0 := rfl
    have hw1eq : w 1 = v := rfl
    have hwtar : ∀ j, MapsTo (w j).toFun
        (Icc (0 : Real) (partitionIntervalLength t j)) (extChartAt I (p j)).target := by
      intro j
      refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun j ↦ Fin.elim0 j) j) j
      · exact (hchart 0).mono_right interior_subset
      · exact hvtar
    have hw0 : (extChartAt I (p 0)).symm ((w 0).toFun 0) =
        (extChartAt I (p 0)).symm ((u 0).toFun 0) := by
      rw [hw0eq]
    have hw2 : (extChartAt I (p 1)).symm
        ((w 1).toFun (partitionIntervalLength t 1)) =
        (extChartAt I (p 1)).symm ((u 1).toFun (partitionIntervalLength t 1)) := by
      rw [hw1eq]
      exact congrArg (extChartAt I (p 1)).symm hvends.2
    have hwnode : (extChartAt I (p 0)).symm
        ((w 0).toFun (partitionIntervalLength t 0)) =
        (extChartAt I (p 1)).symm ((w 1).toFun 0) := by
      rw [hw0eq, hw1eq]
      have hzero : (u 1).toFun 0 = v.toFun 0 := by
        rw [timeH1.toFun_zero, timeH1.toFun_zero]
        exact hvends.1.symm
      exact hnode.trans (congrArg (extChartAt I (p 1)).symm hzero)
    have hc' := hcmp w hwtar hw0 hw2 hwnode
    simp only [Fin.sum_univ_two] at hc'
    change
      lChartAction S T (t 0) (p 0) (u 0) +
          lChartAction S T (t 1) (p 1) (u 1) ≤
        lChartAction S T (t 0) (p 0) (w 0) +
          lChartAction S T (t 1) (p 1) (w 1) at hc'
    rw [hw0eq, hw1eq] at hc'
    linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman
