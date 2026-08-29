import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ActionAttain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ActionEuler
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ActionSplice
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeNonlinearAction

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Function MeasureTheory Set
open scoped ContDiff Manifold Topology Interval NNReal

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [NeZero (Module.finrank Real E)] [T2Space M] [CompactSpace M] in
theorem lChartAct_split
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a : Real) (p : M) {L : Real} (hL : 0 ≤ L) (u : timeH1 E L)
    (htar : ∀ r ∈ Icc (0 : Real) L, u.toFun r ∈ (extChartAt I p).target)
    (hreg : ∀ r ∈ Icc (0 : Real) L, T - (a + r) ^ 2 ∈ D.regular) :
    lChartAct S T a p u =
      (∫ r in (0 : Real)..L, (1 / 2 : Real) * inner Real
        (chartGramOp (I := I) S.family p
          (T - (a + r) ^ 2, u.toFun r) (u.deriv r)) (u.deriv r)) +
      ∫ r in (0 : Real)..L, 2 * (a + r) ^ 2 *
        S.scalar (T - (a + r) ^ 2) ((extChartAt I p).symm (u.toFun r)) := by
  let τ : Real → Real := fun r ↦ T - (a + r) ^ 2
  let K : Set E := u.toFun '' Icc (0 : Real) L
  let J : Set Real := τ '' Icc (0 : Real) L
  have hτc : ContinuousOn τ (Icc (0 : Real) L) :=
    (continuous_const.sub ((continuous_const.add continuous_id).pow 2)).continuousOn
  have hKc : IsCompact K :=
    isCompact_Icc.image_of_continuousOn u.continuousOn_toFun
  have hJc : IsCompact J := isCompact_Icc.image_of_continuousOn hτc
  have hJreg : J ⊆ D.regular := by
    rintro _ ⟨r, hr, rfl⟩
    exact hreg r hr
  have hKchart : K ⊆ interior (extChartAt I p).target := by
    rw [(isOpen_extChartAt_target (I := I) p).interior_eq]
    rintro _ ⟨r, hr, rfl⟩
    exact htar r hr
  let A : Real → E →L[Real] E := fun r ↦
    (1 / 2 : Real) • chartGramOp (I := I) S.family p (τ r, u.toFun r)
  have hpair : ContinuousOn (fun r ↦ (τ r, u.toFun r)) (Icc (0 : Real) L) :=
    hτc.prodMk u.continuousOn_toFun
  have hAc : ContinuousOn A (Icc (0 : Real) L) := by
    have h := (chartGramOp_cont (I := I) hMet hJreg p hKchart).comp hpair
      fun r hr ↦ ⟨⟨r, hr, rfl⟩, ⟨r, hr, rfl⟩⟩
    exact (h.const_smul (1 / 2 : Real)).congr fun _ _ ↦ rfl
  have hAmeas : AEStronglyMeasurable A (timeMeasure L) := by
    simpa only [timeMeasure] using
      hAc.aestronglyMeasurable measurableSet_Icc
  obtain ⟨C, hCraw⟩ := chartGramOp_bound (I := I) hMet hJreg hJc p
    hKchart hKc
  have hC : ∀ᵐ r ∂timeMeasure L, ‖A r‖ ≤ (C : Real) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    dsimp only [A]
    rw [norm_smul]
    have hb := hCraw (τ r, u.toFun r) ⟨⟨r, hr, rfl⟩, ⟨r, hr, rfl⟩⟩
    have hhalf : ‖(1 / 2 : Real)‖ = (1 / 2 : Real) := by norm_num
    rw [hhalf]
    exact (mul_le_mul_of_nonneg_left hb (by norm_num)).trans (by
      have hC0 := NNReal.coe_nonneg C
      linarith)
  have hkin : IntervalIntegrable
      (fun r ↦ inner Real (A r (u.deriv r)) (u.deriv r)) volume 0 L :=
    timeQuad_int A hAmeas C hC hL u.deriv
  have hinv : ContinuousOn (fun r ↦ (extChartAt I p).symm (u.toFun r))
      (Icc (0 : Real) L) :=
    (continuousOn_extChartAt_symm (I := I) p).comp
      u.continuousOn_toFun htar
  have hscal : ContinuousOn (fun r ↦
      S.scalar (τ r) ((extChartAt I p).symm (u.toFun r))) (Icc (0 : Real) L) := by
    rw [continuousOn_iff_continuous_domRestrict]
    let τ' : Icc (0 : Real) L → {q : Real // q ∈ D.carrier} := fun r ↦
      ⟨τ r.1, D.regular_subset (hreg r.1 r.2)⟩
    have hτ' : Continuous τ' := by
      exact continuous_induced_rng.mpr hτc.domRestrict
    have hinv' : Continuous (fun r : Icc (0 : Real) L ↦
        (extChartAt I p).symm (u.toFun r.1)) := hinv.domRestrict
    exact (hSc.continuous_subtype.comp (hτ'.prodMk hinv')).congr fun _ ↦ rfl
  have hpot : IntervalIntegrable (fun r ↦
      2 * (a + r) ^ 2 * S.scalar (τ r) ((extChartAt I p).symm (u.toFun r)))
      volume 0 L := by
    apply ContinuousOn.intervalIntegrable_of_Icc hL
    have hw : Continuous (fun r : Real ↦ 2 * (a + r) ^ 2) :=
      continuous_const.mul ((continuous_const.add continuous_id).pow 2)
    exact hw.continuousOn.mul hscal
  unfold lChartAct lChartLag
  rw [intervalIntegral.integral_add]
  · congr 1
    simp only [smul_apply, real_inner_smul_left]
  · simpa only [A, τ, smul_apply,
      real_inner_smul_left] using hkin
  · simpa only [τ] using hpot

omit [NeZero (Module.finrank Real E)] [T2Space M] [CompactSpace M] in
theorem lRegAction_chart_sum
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : Real) {m : Nat} (t : Fin (m + 1) → Real)
    (htmono : Monotone t) (ht0 : t 0 = a)
    (htlast : t (Fin.last m) = b)
    (p : Fin m → M) (gamma : Real → M)
    (u : (i : Fin m) → timeH1 E (lSegLen t i))
    (hsrc : ∀ i, MapsTo gamma
      (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source)
    (hrep : ∀ i, EqOn (u i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (Icc (0 : Real) (lSegLen t i)))
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular) :
    lRegAction S T gamma a b =
      ∑ i : Fin m, lChartAct S T (t i.castSucc) (p i) (u i) := by
  classical
  rw [lRegAction_chart S hMet hSc T a b t htmono ht0 htlast p gamma u
    hsrc hrep hreg]
  apply Finset.sum_congr rfl
  intro i _hi
  have hseg : t i.castSucc ≤ t i.succ :=
    htmono Fin.castSucc_lt_succ.le
  have hleft : a ≤ t i.castSucc := by
    rw [← ht0]
    exact htmono (Fin.zero_le _)
  have hright : t i.succ ≤ b := by
    rw [← htlast]
    exact htmono (Fin.le_last _)
  have hshift : MapsTo (fun r : Real ↦ t i.castSucc + r)
      (Icc (0 : Real) (lSegLen t i))
      (Icc (t i.castSucc) (t i.succ)) := by
    intro r hr
    change r ∈ Icc (0 : Real) (t i.succ - t i.castSucc) at hr
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have htar (r : Real) (hr : r ∈ Icc (0 : Real) (lSegLen t i)) :
      (u i).toFun r ∈ (extChartAt I (p i)).target := by
    rw [hrep i hr]
    exact (extChartAt I (p i)).map_source (by
      simpa only [extChartAt_source] using hsrc i (hshift hr))
  have hregi (r : Real) (hr : r ∈ Icc (0 : Real) (lSegLen t i)) :
      T - (t i.castSucc + r) ^ 2 ∈ D.regular := by
    apply hreg (t i.castSucc + r)
    exact ⟨hleft.trans (hshift hr).1, (hshift hr).2.trans hright⟩
  have hinv (r : Real) (hr : r ∈ Icc (0 : Real) (lSegLen t i)) :
      (extChartAt I (p i)).symm ((u i).toFun r) =
        gamma (t i.castSucc + r) := by
    rw [hrep i hr]
    exact (extChartAt I (p i)).left_inv (by
      simpa only [extChartAt_source] using hsrc i (hshift hr))
  have hpot :
      (∫ r in (0 : Real)..lSegLen t i, 2 * (t i.castSucc + r) ^ 2 *
        S.scalar (T - (t i.castSucc + r) ^ 2)
          ((extChartAt I (p i)).symm ((u i).toFun r))) =
      ∫ s in t i.castSucc..t i.succ,
        2 * s ^ 2 * S.scalar (T - s ^ 2) (gamma s) := by
    calc
      (∫ r in (0 : Real)..lSegLen t i, 2 * (t i.castSucc + r) ^ 2 *
        S.scalar (T - (t i.castSucc + r) ^ 2)
          ((extChartAt I (p i)).symm ((u i).toFun r))) =
          ∫ r in (0 : Real)..lSegLen t i, 2 * (t i.castSucc + r) ^ 2 *
            S.scalar (T - (t i.castSucc + r) ^ 2)
              (gamma (t i.castSucc + r)) := by
            apply intervalIntegral.integral_congr
            intro r hr
            change 2 * (t i.castSucc + r) ^ 2 *
                S.scalar (T - (t i.castSucc + r) ^ 2)
                  ((extChartAt I (p i)).symm ((u i).toFun r)) =
              2 * (t i.castSucc + r) ^ 2 *
                S.scalar (T - (t i.castSucc + r) ^ 2)
                  (gamma (t i.castSucc + r))
            rw [hinv r (by
              have hL : 0 ≤ lSegLen t i := by
                exact sub_nonneg.mpr hseg
              rw [uIcc_of_le hL] at hr
              exact hr)]
      _ = ∫ s in t i.castSucc..t i.succ,
          2 * s ^ 2 * S.scalar (T - s ^ 2) (gamma s) := by
        have hend : t i.castSucc + lSegLen t i = t i.succ := by
          simp only [lSegLen]
          ring
        simpa only [add_zero, hend] using
          (intervalIntegral.integral_comp_add_left
          (f := fun s ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (gamma s))
          (a := (0 : Real)) (b := lSegLen t i) (t i.castSucc))
  rw [← hpot]
  symm
  exact lChartAct_split S hMet hSc T (t i.castSucc) (p i)
    (sub_nonneg.mpr hseg) (u i) htar hregi

omit [NeZero (Module.finrank Real E)] [T2Space M] [CompactSpace M] in
theorem lChartAct_local
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : Real) {m : Nat} (t : Fin (m + 1) → Real)
    (htmono : Monotone t) (ht0 : t 0 = a)
    (htlast : t (Fin.last m) = b)
    (p : Fin m → M) (gamma : Real → M) (hgamma : Continuous gamma)
    (u : (j : Fin m) → timeH1 E (lSegLen t j))
    (hsrc : ∀ j, MapsTo gamma
      (Icc (t j.castSucc) (t j.succ)) (chartAt H (p j)).source)
    (hrep : ∀ j, EqOn (u j).toFun
      (fun r ↦ extChartAt I (p j) (gamma (t j.castSucc + r)))
      (Icc (0 : Real) (lSegLen t j)))
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular)
    (hmin : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta a = gamma a → delta b = gamma b →
      lRegAction S T gamma a b ≤ lRegAction S T delta a b)
    (i : Fin m) (hpos : t i.castSucc < t i.succ) :
    IsLocalMinOn (lChartAct S T (t i.castSucc) (p i))
      (sameTimeEnds (u i)) (u i) := by
  classical
  let L : Real := lSegLen t i
  have hL : 0 ≤ L := by
    dsimp only [L, lSegLen]
    exact sub_nonneg.mpr hpos.le
  have hshift : MapsTo (fun r : Real ↦ t i.castSucc + r)
      (Icc (0 : Real) L) (Icc (t i.castSucc) (t i.succ)) := by
    intro r hr
    dsimp only [L, lSegLen] at hr
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hutar (r : Real) (hr : r ∈ Icc (0 : Real) L) :
      (u i).toFun r ∈ (extChartAt I (p i)).target := by
    rw [hrep i (by simpa only [L] using hr)]
    exact (extChartAt I (p i)).map_source (by
      simpa only [extChartAt_source] using hsrc i (hshift hr))
  let K : Set E := range fun r : Icc (0 : Real) L ↦ (u i).toFun r.1
  have hKc : IsCompact K :=
    isCompact_range (u i).continuousOn_toFun.domRestrict
  have hKtar : K ⊆ (extChartAt I (p i)).target := by
    rintro _ ⟨r, rfl⟩
    exact hutar r.1 r.2
  obtain ⟨d, hd, hdsub⟩ := hKc.exists_thickening_subset_open
    (isOpen_extChartAt_target (I := I) (p i)) hKtar
  let c : Real := 1 + Real.sqrt L
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  let eps : Real := d / c
  have heps : 0 < eps := div_pos hd hc
  rw [IsLocalMinOn, IsMinFilter]
  filter_upwards
    [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (u i) heps),
      self_mem_nhdsWithin] with v hvball hvends
  have hvnorm : ‖v - u i‖ < eps := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hvball
  have hvtar : MapsTo v.toFun (Icc (0 : Real) L)
      (extChartAt I (p i)).target := by
    intro r hr
    apply hdsub
    rw [Metric.mem_thickening_iff]
    refine ⟨(u i).toFun r, ⟨⟨r, hr⟩, rfl⟩, ?_⟩
    have hfun : (v - u i).toFun r = v.toFun r - (u i).toFun r := by
      calc
        (v - u i).toFun r = (v + -u i).toFun r := by
          rw [sub_eq_add_neg]
        _ = v.toFun r + (-u i).toFun r :=
          timeH1.toFun_add v (-u i) hr
        _ = v.toFun r + (-1 : Real) • (u i).toFun r := by
          rw [show -u i = (-1 : Real) • u i by simp only [neg_one_smul],
            timeH1.toFun_smul (-1 : Real) (u i) hr]
        _ = v.toFun r - (u i).toFun r := by simp only [neg_one_smul, sub_eq_add_neg]
    calc
      dist (v.toFun r) ((u i).toFun r) = ‖(v - u i).toFun r‖ := by
        rw [dist_eq_norm, hfun]
      _ ≤ c * ‖v - u i‖ := by
        simpa only [c] using (v - u i).norm_toFun_le_norm hr
      _ < c * eps := mul_lt_mul_of_pos_left hvnorm hc
      _ = d := by
        dsimp only [eps]
        exact mul_div_cancel₀ d hc.ne'
  obtain ⟨gammaV, hgammaV, hVa0, hVab, hsrcV, hrepV⟩ :=
    exists_chart_splice (I := I) t htmono p gamma hgamma u hsrc hrep i hpos v
      hvends (by simpa only [L] using hvtar)
  have hVa : gammaV a = gamma a := by
    rw [← ht0]
    exact hVa0
  have hVb : gammaV b = gamma b := by
    rw [← htlast]
    exact hVab
  obtain ⟨alpha, w, halpha, halphaa, halphab, _hsrcA, _hrepA, _hw,
      _hunif, hact⟩ :=
    lAction_c1_dense (I := I) S hMet hSc T a b t htmono ht0 htlast p
      gammaV (Function.update u i v) hsrcV hrepV hreg
  have hneg : Tendsto (fun n ↦ -lRegAction S T (alpha n) a b) atTop
      (nhds (-lRegAction S T gammaV a b)) :=
    continuousAt_neg.tendsto.comp hact
  have hglobal : lRegAction S T gamma a b ≤ lRegAction S T gammaV a b := by
    have hlim := le_of_tendsto' hneg fun n ↦ neg_le_neg
      (hmin (alpha n) (halpha n) ((halphaa n).trans hVa)
        ((halphab n).trans hVb))
    linarith
  let F : Fin m → Real := fun j ↦
    lChartAct S T (t j.castSucc) (p j) (u j)
  let G : Fin m → Real := fun j ↦
    lChartAct S T (t j.castSucc) (p j) ((Function.update u i v) j)
  have hsum : ∑ j, F j ≤ ∑ j, G j := by
    rw [show (∑ j, F j) = lRegAction S T gamma a b from
      (lRegAction_chart_sum S hMet hSc T a b t htmono ht0 htlast p gamma
        u hsrc hrep hreg).symm]
    rw [show (∑ j, G j) = lRegAction S T gammaV a b from
      (lRegAction_chart_sum S hMet hSc T a b t htmono ht0 htlast p gammaV
        (Function.update u i v) hsrcV hrepV hreg).symm]
    exact hglobal
  have hrest : ∑ j ∈ Finset.univ.erase i, G j =
      ∑ j ∈ Finset.univ.erase i, F j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp only [G, F, Function.update_of_ne hji]
  have hcancel : F i ≤ G i := by
    apply (add_le_add_iff_left (∑ j ∈ Finset.univ.erase i, F j)).mp
    calc
      (∑ j ∈ Finset.univ.erase i, F j) + F i = ∑ j, F j :=
        Finset.sum_erase_add _ _ (Finset.mem_univ i)
      _ ≤ ∑ j, G j := hsum
      _ = (∑ j ∈ Finset.univ.erase i, F j) + G i := by
        rw [← hrest]
        exact (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
  simpa only [F, G, Function.update_self] using hcancel

end DifferentialGeometry.PDE.RicciFlow.Perelman
