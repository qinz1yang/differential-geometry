import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.TwoPieceSplicing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.LocalMinimum

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Function MeasureTheory Set
open scoped ContDiff Manifold Topology

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

private theorem seg_before {m : Nat} {i j : Fin m} (hij : i < j) :
    i.succ ≤ j.castSucc := by
  exact Fin.succ_le_castSucc_iff.mpr hij

omit [NeZero (Module.finrank Real E)] [T2Space M] [CompactSpace M] in
theorem lChartAct_adjacent_pair_le_of_lRegAction_minimizer
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : Real) {m : Nat} (t : Fin (m + 3) → Real)
    (htmono : Monotone t) (ht0 : t 0 = a)
    (htlast : t (Fin.last (m + 2)) = b)
    (p : Fin (m + 2) → M) (gamma : Real → M) (hgamma : Continuous gamma)
    (u : (k : Fin (m + 2)) → timeH1 E (lSegLen t k))
    (hsrc : ∀ k, MapsTo gamma
      (Icc (t k.castSucc) (t k.succ)) (chartAt H (p k)).source)
    (hrep : ∀ k, EqOn (u k).toFun
      (fun r ↦ extChartAt I (p k) (gamma (t k.castSucc + r)))
      (Icc (0 : Real) (lSegLen t k)))
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular)
    (hmin : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta a = gamma a → delta b = gamma b →
      lRegAction S T gamma a b ≤ lRegAction S T delta a b)
    (q : Fin (m + 1))
    (hpos0 : t q.castSucc.castSucc < t q.castSucc.succ)
    (hpos1 : t q.succ.castSucc < t q.succ.succ)
    (v0 : timeH1 E (lSegLen t q.castSucc))
    (v1 : timeH1 E (lSegLen t q.succ))
    (htar0 : MapsTo v0.toFun (Icc (0 : Real) (lSegLen t q.castSucc))
      (extChartAt I (p q.castSucc)).target)
    (htar1 : MapsTo v1.toFun (Icc (0 : Real) (lSegLen t q.succ))
      (extChartAt I (p q.succ)).target)
    (hv0 : (extChartAt I (p q.castSucc)).symm (v0.toFun 0) =
      gamma (t q.castSucc.castSucc))
    (hv2 : (extChartAt I (p q.succ)).symm
      (v1.toFun (lSegLen t q.succ)) = gamma (t q.succ.succ))
    (hvnode : (extChartAt I (p q.castSucc)).symm
        (v0.toFun (lSegLen t q.castSucc)) =
      (extChartAt I (p q.succ)).symm (v1.toFun 0)) :
    lChartAct S T (t q.castSucc.castSucc) (p q.castSucc) (u q.castSucc) +
        lChartAct S T (t q.succ.castSucc) (p q.succ) (u q.succ) ≤
      lChartAct S T (t q.castSucc.castSucc) (p q.castSucc) v0 +
        lChartAct S T (t q.succ.castSucc) (p q.succ) v1 := by
  classical
  let i : Fin (m + 2) := q.castSucc
  let j : Fin (m + 2) := q.succ
  change lChartAct S T (t i.castSucc) (p i) (u i) +
      lChartAct S T (t j.castSucc) (p j) (u j) ≤
    lChartAct S T (t i.castSucc) (p i) v0 +
      lChartAct S T (t j.castSucc) (p j) v1
  have hij : i.val + 1 = j.val := rfl
  change timeH1 E (lSegLen t i) at v0
  change timeH1 E (lSegLen t j) at v1
  change MapsTo v0.toFun (Icc (0 : Real) (lSegLen t i))
    (extChartAt I (p i)).target at htar0
  change MapsTo v1.toFun (Icc (0 : Real) (lSegLen t j))
    (extChartAt I (p j)).target at htar1
  change (extChartAt I (p i)).symm (v0.toFun 0) = gamma (t i.castSucc) at hv0
  change (extChartAt I (p j)).symm (v1.toFun (lSegLen t j)) =
    gamma (t j.succ) at hv2
  change (extChartAt I (p i)).symm (v0.toFun (lSegLen t i)) =
    (extChartAt I (p j)).symm (v1.toFun 0) at hvnode
  change t i.castSucc < t i.succ at hpos0
  change t j.castSucc < t j.succ at hpos1
  let hposi := hpos0
  let hposj := hpos1
  have hij' : i < j := by
    exact Fin.mk_lt_mk.mpr (by omega)
  have hijne : i ≠ j := ne_of_lt hij'
  have hmid : t i.succ = t j.castSucc := by rfl
  let tw : Fin 3 → Real :=
    Fin.cases (t i.castSucc)
      (Fin.cases (t j.castSucc) (Fin.cases (t j.succ) fun k ↦ Fin.elim0 k))
  let pw : Fin 2 → M := Fin.cases (p i) (Fin.cases (p j) fun k ↦ Fin.elim0 k)
  let vw : (k : Fin 2) → timeH1 E (lSegLen tw k) :=
    Fin.cases v0 (Fin.cases v1 fun k ↦ Fin.elim0 k)
  have htw0 : tw 0 = t i.castSucc := rfl
  have htw1 : tw 1 = t j.castSucc := by
    rw [show (1 : Fin 3) = Fin.succ 0 by rfl]
    rfl
  have htw2 : tw 2 = t j.succ := by
    rw [show (2 : Fin 3) = Fin.succ (Fin.succ 0) by rfl]
    rfl
  have hpw0 : pw 0 = p i := rfl
  have hpw1 : pw 1 = p j := by
    rw [show (1 : Fin 2) = Fin.succ 0 by rfl]
    rfl
  have htw0c : tw (0 : Fin 2).castSucc = t i.castSucc := rfl
  have htw0s : tw (0 : Fin 2).succ = t j.castSucc := rfl
  have htw1c : tw (1 : Fin 2).castSucc = t j.castSucc := by
    change tw (Fin.succ 0) = t j.castSucc
    rfl
  have htw1s : tw (1 : Fin 2).succ = t j.succ := by
    change tw (Fin.succ (Fin.succ 0)) = t j.succ
    rfl
  have htw1cStep : tw (Fin.succ (0 : Fin 1)).castSucc = t j.castSucc := rfl
  have htw1sStep : tw (Fin.succ (0 : Fin 1)).succ = t j.succ := rfl
  have htwLast : tw (Fin.last 2) = t j.succ := rfl
  have hvw0 : (vw 0).toFun = v0.toFun := rfl
  have hvw1 : (vw 1).toFun = v1.toFun := by
    change (vw (Fin.succ 0)).toFun = v1.toFun
    rfl
  have hvw1Step : (vw (Fin.succ (0 : Fin 1))).toFun = v1.toFun := rfl
  have hpw1Step : pw (Fin.succ (0 : Fin 1)) = p j := rfl
  have htw : Monotone tw := by
    apply Fin.monotone_iff_le_succ.mpr
    intro k
    exact Fin.cases
      (by rw [htw0c, htw0s]; exact hposi.le)
      (Fin.cases (by rw [htw1cStep, htw1sStep]; exact hposj.le)
        fun z ↦ Fin.elim0 z) k
  have hvwtar : ∀ k, MapsTo (vw k).toFun
      (Icc (0 : Real) (lSegLen tw k)) (extChartAt I (pw k)).target := by
    intro k
    exact Fin.cases
      (by
        rw [hvw0, hpw0]
        simp only [lSegLen]
        rw [htw0c, htw0s]
        exact htar0)
      (Fin.cases (by
          rw [hvw1Step, hpw1Step]
          simp only [lSegLen]
          rw [htw1cStep, htw1sStep]
          exact htar1)
        fun z ↦ Fin.elim0 z) k
  have hvwnode : (extChartAt I (pw 0)).symm
        ((vw 0).toFun (lSegLen tw 0)) =
      (extChartAt I (pw 1)).symm ((vw 1).toFun 0) := by
    rw [hvw0, hvw1, hpw0, hpw1]
    simp only [lSegLen]
    rw [htw0c, htw0s]
    exact hvnode
  have hregw : ∀ s ∈ Icc (tw 0) (tw (Fin.last 2)),
      T - s ^ 2 ∈ D.regular := by
    intro s hs
    apply hreg s
    constructor
    · rw [← ht0]
      exact (htmono (Fin.zero_le i.castSucc)).trans hs.1
    · rw [← htlast]
      exact hs.2.trans (htmono (Fin.le_last j.succ))
  obtain ⟨gammaW, hgammaW, hsrcW, hrepW, hW0, hW2, _alphaW, _wW,
      _halphaW, _halphaW0, _halphaW2, _hsrcAW, _hrepAW, _hwW, _hunifW,
      _hactW⟩ :=
    exists_contMDiff_one_lRegAction_approximation_of_compatible_chartH1_pair (I := I) S hMet hSc T tw htw pw vw hvwtar hvwnode hregw
  have hWleft : gammaW (t i.castSucc) = gamma (t i.castSucc) := by
    have hW0' := hW0
    rw [htw0, hpw0, hvw0] at hW0'
    exact hW0'.trans hv0
  have hWright : gammaW (t j.succ) = gamma (t j.succ) := by
    have hW2' := hW2
    rw [htwLast, hpw1, hvw1] at hW2'
    simp only [lSegLen] at hW2'
    rw [htw1c, htw1s] at hW2'
    exact hW2'.trans hv2
  let win : Set Real := Icc (t i.castSucc) (t j.succ)
  let gammaV : Real → M := Set.piecewise win gammaW gamma
  have hwinle : t i.castSucc ≤ t j.succ :=
    hposi.le.trans (hmid.le.trans hposj.le)
  have hgammaV : Continuous gammaV := by
    apply hgammaW.piecewise (s := win)
    · intro s hs
      have hs' : s ∈ ({t i.castSucc, t j.succ} : Set Real) := by
        simpa only [win, frontier_Icc hwinle] using hs
      rcases hs' with hs | hs
      · simpa only [hs] using hWleft
      · have hse : s = t j.succ := by simpa only [mem_singleton_iff] using hs
        simpa only [hse] using hWright
    · exact hgamma
  have hgammaV_win {s : Real} (hs : s ∈ win) : gammaV s = gammaW s :=
    win.piecewise_eq_of_mem gammaW gamma hs
  have hgammaV_out {s : Real} (hs : s ∉ win) : gammaV s = gamma s :=
    win.piecewise_eq_of_notMem gammaW gamma hs
  have hgammaV_left : gammaV (t i.castSucc) = gamma (t i.castSucc) := by
    rw [hgammaV_win ⟨le_rfl, hwinle⟩, hWleft]
  have hgammaV_right : gammaV (t j.succ) = gamma (t j.succ) := by
    rw [hgammaV_win ⟨hwinle, le_rfl⟩, hWright]
  have hother (k : Fin (m + 2)) (hki : k ≠ i) (hkj : k ≠ j) {s : Real}
      (hs : s ∈ Icc (t k.castSucc) (t k.succ)) : gammaV s = gamma s := by
    by_cases hsw : s ∈ win
    · have hcases : k < i ∨ j < k := by
        rcases lt_or_gt_of_ne hki with hlt | hgt
        · exact Or.inl hlt
        · have hik : i.val < k.val := hgt
          have hkjv : k.val ≠ j.val := by
            intro heq
            apply hkj
            exact Fin.ext heq
          have hjk : j.val < k.val := by
            change q.val < k.val at hik
            change k.val ≠ q.val + 1 at hkjv
            change q.val + 1 < k.val
            omega
          exact Or.inr (Fin.mk_lt_mk.mpr hjk)
      rcases hcases with hleft | hright
      · have hle : t k.succ ≤ t i.castSucc := htmono (seg_before hleft)
        have heq : s = t i.castSucc := le_antisymm (hs.2.trans hle) hsw.1
        simpa only [heq] using hgammaV_left
      · have hle : t j.succ ≤ t k.castSucc := htmono (seg_before hright)
        have heq : s = t j.succ := le_antisymm hsw.2 (hle.trans hs.1)
        simpa only [heq] using hgammaV_right
    · exact hgammaV_out hsw
  let uv : (k : Fin (m + 2)) → timeH1 E (lSegLen t k) :=
    Function.update (Function.update u i v0) j v1
  have huv_i : uv i = v0 := by
    dsimp only [uv]
    rw [Function.update_of_ne hijne, Function.update_self]
  have huv_j : uv j = v1 := by
    dsimp only [uv]
    rw [Function.update_self]
  have huv_other (k : Fin (m + 2)) (hki : k ≠ i) (hkj : k ≠ j) :
      uv k = u k := by
    dsimp only [uv]
    rw [Function.update_of_ne hkj, Function.update_of_ne hki]
  have hsrcV : ∀ k, MapsTo gammaV
      (Icc (t k.castSucc) (t k.succ)) (chartAt H (p k)).source := by
    intro k s hs
    by_cases hki : k = i
    · subst k
      rw [hgammaV_win ⟨hs.1, hs.2.trans (hmid.le.trans hposj.le)⟩]
      exact hsrcW 0 (by rw [htw0c, htw0s]; exact hs)
    · by_cases hkj : k = j
      · subst k
        have hleft : t i.castSucc ≤ s :=
          hposi.le.trans (hmid.le.trans hs.1)
        rw [hgammaV_win ⟨hleft, hs.2⟩]
        exact hsrcW 1 (by rw [htw1c, htw1s]; exact hs)
      · rw [hother k hki hkj hs]
        exact hsrc k hs
  have hrepV : ∀ k, EqOn (uv k).toFun
      (fun r ↦ extChartAt I (p k) (gammaV (t k.castSucc + r)))
      (Icc (0 : Real) (lSegLen t k)) := by
    intro k r hr
    have hs : t k.castSucc + r ∈ Icc (t k.castSucc) (t k.succ) := by
      change r ∈ Icc (0 : Real) (t k.succ - t k.castSucc) at hr
      exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
    by_cases hki : k = i
    · subst k
      rw [huv_i]
      change v0.toFun r =
        extChartAt I (p i) (gammaV (t i.castSucc + r))
      rw [hgammaV_win ⟨hs.1, hs.2.trans (hmid.le.trans hposj.le)⟩]
      rw [← hvw0, ← hpw0, ← htw0c]
      exact hrepW 0 hr
    · by_cases hkj : k = j
      · subst k
        have hleft : t i.castSucc ≤ t j.castSucc + r :=
          hposi.le.trans (hmid.le.trans hs.1)
        rw [huv_j]
        change v1.toFun r =
          extChartAt I (p j) (gammaV (t j.castSucc + r))
        rw [hgammaV_win ⟨hleft, hs.2⟩]
        rw [← hvw1, ← hpw1, ← htw1c]
        exact hrepW 1 hr
      · rw [huv_other k hki hkj]
        change (u k).toFun r =
          extChartAt I (p k) (gammaV (t k.castSucc + r))
        rw [hother k hki hkj hs]
        exact hrep k hr
  have hstart : gammaV a = gamma a := by
    by_cases hs : a ∈ win
    · have haleft : a ≤ t i.castSucc := by
        rw [← ht0]
        exact htmono (Fin.zero_le i.castSucc)
      have heq : a = t i.castSucc := le_antisymm haleft hs.1
      simpa only [heq] using hgammaV_left
    · exact hgammaV_out hs
  have hend : gammaV b = gamma b := by
    by_cases hs : b ∈ win
    · have hrightb : t j.succ ≤ b := by
        rw [← htlast]
        exact htmono (Fin.le_last j.succ)
      have heq : b = t j.succ := le_antisymm hs.2 hrightb
      simpa only [heq] using hgammaV_right
    · exact hgammaV_out hs
  obtain ⟨alpha, _w, halpha, halphaa, halphab, _hsrcA, _hrepA, _hw,
      _hunif, hact⟩ :=
    lAction_c1_dense (I := I) S hMet hSc T a b t htmono ht0 htlast p
      gammaV uv hsrcV hrepV hreg
  have hneg : Tendsto (fun n ↦ -lRegAction S T (alpha n) a b) atTop
      (nhds (-lRegAction S T gammaV a b)) :=
    continuousAt_neg.tendsto.comp hact
  have hglobal : lRegAction S T gamma a b ≤ lRegAction S T gammaV a b := by
    have hlim := le_of_tendsto' hneg fun n ↦ neg_le_neg
      (hmin (alpha n) (halpha n) ((halphaa n).trans hstart)
        ((halphab n).trans hend))
    linarith
  let F : Fin (m + 2) → Real := fun k ↦
    lChartAct S T (t k.castSucc) (p k) (u k)
  let G : Fin (m + 2) → Real := fun k ↦
    lChartAct S T (t k.castSucc) (p k) (uv k)
  have hsum : ∑ k, F k ≤ ∑ k, G k := by
    rw [show (∑ k, F k) = lRegAction S T gamma a b from
      (lRegAction_chart_sum S hMet hSc T a b t htmono ht0 htlast p gamma
        u hsrc hrep hreg).symm]
    rw [show (∑ k, G k) = lRegAction S T gammaV a b from
      (lRegAction_chart_sum S hMet hSc T a b t htmono ht0 htlast p gammaV
        uv hsrcV hrepV hreg).symm]
    exact hglobal
  let R : Finset (Fin (m + 2)) := (Finset.univ.erase i).erase j
  have hjmem : j ∈ Finset.univ.erase i :=
    Finset.mem_erase.mpr ⟨hijne.symm, Finset.mem_univ j⟩
  have hFsum : ∑ k, F k = (∑ k ∈ R, F k) + F i + F j := by
    rw [show (∑ k, F k) = (∑ k ∈ Finset.univ.erase i, F k) + F i from
      (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm]
    rw [show (∑ k ∈ Finset.univ.erase i, F k) =
        (∑ k ∈ R, F k) + F j from (Finset.sum_erase_add _ _ hjmem).symm]
    ring
  have hGsum : ∑ k, G k = (∑ k ∈ R, G k) + G i + G j := by
    rw [show (∑ k, G k) = (∑ k ∈ Finset.univ.erase i, G k) + G i from
      (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm]
    rw [show (∑ k ∈ Finset.univ.erase i, G k) =
        (∑ k ∈ R, G k) + G j from (Finset.sum_erase_add _ _ hjmem).symm]
    ring
  have hrest : (∑ k ∈ R, G k) = ∑ k ∈ R, F k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hki : k ≠ i := by
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    simp only [G, F, huv_other k hki hkj]
  rw [hFsum, hGsum, hrest] at hsum
  have hGi : G i = lChartAct S T (t i.castSucc) (p i) v0 := by
    simp only [G, huv_i]
  have hGj : G j = lChartAct S T (t j.castSucc) (p j) v1 := by
    simp only [G, huv_j]
  rw [hGi, hGj] at hsum
  dsimp only [F] at hsum
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
