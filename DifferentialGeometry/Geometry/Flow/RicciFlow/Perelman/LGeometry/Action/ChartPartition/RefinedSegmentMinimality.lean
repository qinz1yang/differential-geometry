import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.AdjacentSegmentMinimality
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Slice

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Function MeasureTheory Set
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

omit [NeZero (Module.finrank Real E)] in
omit [FiniteDimensional ℝ E] in
private theorem toFun_cast {a b : Real} (h : a = b) (v : timeH1 E b) :
    ((h.symm ▸ v : timeH1 E a).toFun) = v.toFun := by
  subst b
  rfl

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
    [CompactSpace M] in
private theorem act_cast {a b : Real} (h : a = b)
    (S : SolutionOn (I := I) (M := M) D) (T s : Real) (p : M)
    (v : timeH1 E b) :
    lChartAction S T s p (h.symm ▸ v : timeH1 E a) = lChartAction S T s p v := by
  subst b
  rfl

private theorem ins_cast_of_ne {m : Nat} (j k : Fin (m + 2)) (hkj : k ≠ j) :
    ((j.castSucc).succAbove k).castSucc =
      (j.castSucc.succ).succAbove k.castSucc := by
  apply Fin.ext
  simp only [Fin.val_castSucc, Fin.succAbove]
  split_ifs <;> simp_all <;> omega

private theorem ins_succ {m : Nat} (j k : Fin (m + 2)) :
    ((j.castSucc).succAbove k).succ =
      (j.castSucc.succ).succAbove k.succ := by
  apply Fin.ext
  simp only [Fin.val_succ, Fin.succAbove]
  split_ifs
  all_goals simp_all
  omega

omit [NeZero (Module.finrank Real E)] [T2Space M] [CompactSpace M] in
theorem lChartAction_refined_adjacent_pair_le_of_lRegAction_minimizer
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : Real) {m : Nat} (t : Fin (m + 3) → Real)
    (htmono : Monotone t) (ht0 : t 0 = a)
    (htlast : t (Fin.last (m + 2)) = b)
    (p : Fin (m + 2) → M) (gamma : Real → M) (hgamma : Continuous gamma)
    (u : (k : Fin (m + 2)) → timeH1 E (partitionIntervalLength t k))
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
    (q : Fin (m + 1)) (c : Real)
    (hpos0 : t q.castSucc.castSucc < t q.castSucc.succ)
    (hc0 : t q.succ.castSucc < c) (hc1 : c < t q.succ.succ)
    (uHead : timeH1 E (c - t q.succ.castSucc))
    (hsrcHead : MapsTo gamma (Icc (t q.succ.castSucc) c)
      (chartAt H (p q.castSucc)).source)
    (hrepHead : EqOn uHead.toFun
      (fun r ↦ extChartAt I (p q.castSucc)
        (gamma (t q.succ.castSucc + r)))
      (Icc (0 : Real) (c - t q.succ.castSucc)))
    (v0 : timeH1 E (partitionIntervalLength t q.castSucc))
    (v1 : timeH1 E (c - t q.succ.castSucc))
    (htar0 : MapsTo v0.toFun (Icc (0 : Real) (partitionIntervalLength t q.castSucc))
      (extChartAt I (p q.castSucc)).target)
    (htar1 : MapsTo v1.toFun
      (Icc (0 : Real) (c - t q.succ.castSucc))
      (extChartAt I (p q.castSucc)).target)
    (hv0 : (extChartAt I (p q.castSucc)).symm (v0.toFun 0) =
      gamma (t q.castSucc.castSucc))
    (hv2 : (extChartAt I (p q.castSucc)).symm
      (v1.toFun (c - t q.succ.castSucc)) = gamma c)
    (hvnode : (extChartAt I (p q.castSucc)).symm
        (v0.toFun (partitionIntervalLength t q.castSucc)) =
      (extChartAt I (p q.castSucc)).symm (v1.toFun 0)) :
    lChartAction S T (t q.castSucc.castSucc) (p q.castSucc) (u q.castSucc) +
        lChartAction S T (t q.succ.castSucc) (p q.castSucc) uHead ≤
      lChartAction S T (t q.castSucc.castSucc) (p q.castSucc) v0 +
        lChartAction S T (t q.succ.castSucc) (p q.castSucc) v1 := by
  classical
  let i : Fin (m + 2) := q.castSucc
  let j : Fin (m + 2) := q.succ
  have hij : i < j := by
    change q.val < q.val + 1
    omega
  let head : Fin (m + 3) := j.castSucc
  let node : Fin (m + 4) := head.succ
  let tr : Fin (m + 4) → Real := Fin.insertNth node c t
  let pr : Fin (m + 3) → M := Fin.insertNth head (p i) p
  have hheadNode : head.castSucc = node.succAbove j.castSucc := by
    change j.castSucc.castSucc = j.castSucc.succ.succAbove j.castSucc
    exact (Fin.succAbove_succ_self j.castSucc).symm
  have htailIdx : head.succAbove j = j.succ := by
    exact Fin.succAbove_castSucc_self j
  have htailNode : (head.succAbove j).castSucc = node := by
    rw [htailIdx]
    apply Fin.ext
    rfl
  have htrHead0 : tr head.castSucc = t j.castSucc := by
    rw [hheadNode]
    simp only [tr, Fin.insertNth_apply_succAbove]
  have htrHead1 : tr head.succ = c := by
    simp only [tr, node, Fin.insertNth_apply_same]
  have htrTail0 : tr (head.succAbove j).castSucc = c := by
    rw [htailNode]
    simp only [tr, Fin.insertNth_apply_same]
  have htrTail1 : tr (head.succAbove j).succ = t j.succ := by
    rw [show (head.succAbove j).succ = node.succAbove j.succ by
      simpa only [head, node] using ins_succ j j]
    simp only [tr, Fin.insertNth_apply_succAbove]
  have htrOld0 (k : Fin (m + 2)) (hkj : k ≠ j) :
      tr (head.succAbove k).castSucc = t k.castSucc := by
    rw [show (head.succAbove k).castSucc = node.succAbove k.castSucc by
      simpa only [head, node] using ins_cast_of_ne j k hkj]
    simp only [tr, Fin.insertNth_apply_succAbove]
  have htrOld1 (k : Fin (m + 2)) :
      tr (head.succAbove k).succ = t k.succ := by
    rw [show (head.succAbove k).succ = node.succAbove k.succ by
      simpa only [head, node] using ins_succ j k]
    simp only [tr, Fin.insertNth_apply_succAbove]
  have haTail : 0 ≤ c - t j.castSucc := sub_nonneg.mpr hc0.le
  let uTail0 : timeH1 E (partitionIntervalLength t j - (c - t j.castSucc)) :=
    timeH1.slice (u j) (c - t j.castSucc) (partitionIntervalLength t j) haTail le_rfl
  have hHeadLen : partitionIntervalLength tr head = c - t j.castSucc := by
    simp only [partitionIntervalLength, htrHead0, htrHead1]
  have hTailLen : partitionIntervalLength tr (head.succAbove j) =
      partitionIntervalLength t j - (c - t j.castSucc) := by
    simp only [partitionIntervalLength, htrTail0, htrTail1]
    ring
  have hOldLen (k : Fin (m + 2)) (hkj : k ≠ j) :
      partitionIntervalLength tr (head.succAbove k) = partitionIntervalLength t k := by
    simp only [partitionIntervalLength, htrOld0 k hkj, htrOld1 k]
  let ur : (k : Fin (m + 3)) → timeH1 E (partitionIntervalLength tr k) :=
    Fin.insertNth head (hHeadLen.symm ▸ uHead) fun k ↦
      if hkj : k = j then by
        subst k
        exact hTailLen.symm ▸ uTail0
      else (hOldLen k hkj).symm ▸ u k
  have hprHead : pr head = p i := by
    simp only [pr, Fin.insertNth_apply_same]
  have hprOld (k : Fin (m + 2)) : pr (head.succAbove k) = p k := by
    simp only [pr, Fin.insertNth_apply_succAbove]
  have hurHead : ur head = hHeadLen.symm ▸ uHead := by
    simp only [ur, Fin.insertNth_apply_same]
  have hurTail : ur (head.succAbove j) = hTailLen.symm ▸ uTail0 := by
    simp only [ur, Fin.insertNth_apply_succAbove]
    split
    · rfl
    · contradiction
  have hurOld (k : Fin (m + 2)) (hkj : k ≠ j) :
      ur (head.succAbove k) = (hOldLen k hkj).symm ▸ u k := by
    simp only [ur, Fin.insertNth_apply_succAbove, dif_neg hkj]
  have htrMono : Monotone tr := by
    apply Fin.monotone_iff_le_succ.mpr
    intro k
    induction k using head.succAboveCases with
    | x =>
        apply sub_nonneg.mp
        change 0 ≤ partitionIntervalLength tr head
        rw [hHeadLen]
        exact sub_nonneg.mpr hc0.le
    | p k =>
        by_cases hkj : k = j
        · subst k
          apply sub_nonneg.mp
          change 0 ≤ partitionIntervalLength tr (head.succAbove j)
          rw [hTailLen]
          simp only [partitionIntervalLength]
          linarith
        · apply sub_nonneg.mp
          change 0 ≤ partitionIntervalLength tr (head.succAbove k)
          rw [hOldLen k hkj]
          exact sub_nonneg.mpr (htmono Fin.castSucc_lt_succ.le)
  have hsrcR : ∀ k, MapsTo gamma
      (Icc (tr k.castSucc) (tr k.succ)) (chartAt H (pr k)).source := by
    intro k
    induction k using head.succAboveCases with
    | x =>
        rw [htrHead0, htrHead1, hprHead]
        exact hsrcHead
    | p k =>
        by_cases hkj : k = j
        · subst k
          rw [htrTail0, htrTail1, hprOld]
          intro s hs
          exact hsrc j ⟨hc0.le.trans hs.1, hs.2⟩
        · rw [htrOld0 k hkj, htrOld1 k, hprOld]
          exact hsrc k
  have hrepR : ∀ k, EqOn (ur k).toFun
      (fun r ↦ extChartAt I (pr k) (gamma (tr k.castSucc + r)))
      (Icc (0 : Real) (partitionIntervalLength tr k)) := by
    intro k r hr
    induction k using head.succAboveCases with
    | x =>
        have hr' : r ∈ Icc (0 : Real) (c - t j.castSucc) := by
          simpa only [hHeadLen] using hr
        have hh := hrepHead hr'
        rw [hurHead, htrHead0, hprHead]
        rw [toFun_cast hHeadLen uHead]
        simpa only [i, j] using hh
    | p k =>
        by_cases hkj : k = j
        · subst k
          have hr' : r ∈ Icc (0 : Real)
              (partitionIntervalLength t j - (c - t j.castSucc)) := by
            simpa only [hTailLen] using hr
          have hs := timeH1.slice_toFun (u j) (c - t j.castSucc)
            (partitionIntervalLength t j) haTail le_rfl hr'
          have harg : c - t j.castSucc + r ∈ Icc (0 : Real) (partitionIntervalLength t j) := by
            constructor
            · linarith [hc0.le, hr'.1]
            · linarith [hr'.2]
          have hu := hrep j harg
          rw [hurTail, htrTail0, hprOld]
          rw [toFun_cast hTailLen uTail0]
          rw [hs, hu]
          change extChartAt I (p j) (gamma
              (t j.castSucc + (c - t j.castSucc + r))) =
            extChartAt I (p j) (gamma (c + r))
          rw [show t j.castSucc + (c - t j.castSucc + r) = c + r by ring]
        · have hr' : r ∈ Icc (0 : Real) (partitionIntervalLength t k) := by
            simpa only [hOldLen k hkj] using hr
          have hu := hrep k hr'
          rw [hurOld k hkj, htrOld0 k hkj, hprOld]
          rw [toFun_cast (hOldLen k hkj) (u k)]
          exact hu
  have hjne0 : (0 : Fin (m + 2)) ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero, j, Fin.val_succ] at hv
    omega
  have hheadZero : head.succAbove (0 : Fin (m + 2)) = 0 := by
    apply Fin.ext
    simp only [head, j, Fin.val_zero, Fin.succAbove]
    split_ifs <;> simp_all
  have htr0 : tr 0 = t 0 := by
    have hz := htrOld0 (0 : Fin (m + 2)) hjne0
    simpa only [hheadZero, Fin.castSucc_zero] using hz
  have hnodeNeLast : node ≠ Fin.last (m + 3) := by
    apply Fin.ne_of_lt
    change q.val + 2 < m + 3
    omega
  have hlastMap : node.succAbove (Fin.last (m + 2)) = Fin.last (m + 3) :=
    Fin.succAbove_ne_last_last hnodeNeLast
  have htrLast : tr (Fin.last (m + 3)) = t (Fin.last (m + 2)) := by
    rw [← hlastMap]
    simp only [tr, Fin.insertNth_apply_succAbove]
  have hine : i ≠ j := ne_of_lt hij
  have hleftIdx : head.succAbove i = i.castSucc := by
    simpa only [head] using Fin.succAbove_castSucc_of_lt j i hij
  have hheadIdx : i.succ = head := by
    apply Fin.ext
    rfl
  have htrLeft0 : tr i.castSucc.castSucc = t i.castSucc := by
    calc
      tr i.castSucc.castSucc = tr (head.succAbove i).castSucc := by
        rw [hleftIdx]
      _ = t i.castSucc := htrOld0 i hine
  have htrLeft1 : tr i.castSucc.succ = t i.succ := by
    rw [← hleftIdx]
    exact htrOld1 i
  have hprLeft : pr i.castSucc = p i := by
    rw [← hleftIdx]
    exact hprOld i
  have hLeftLen : partitionIntervalLength tr i.castSucc = partitionIntervalLength t i := by
    rw [← hleftIdx]
    exact hOldLen i hine
  have hHeadLen' : partitionIntervalLength tr i.succ = c - t j.castSucc := by
    rw [hheadIdx]
    exact hHeadLen
  have htrHead0' : tr i.succ.castSucc = t j.castSucc := by
    rw [hheadIdx]
    exact htrHead0
  have hprHead' : pr i.succ = p i := by
    rw [hheadIdx]
    exact hprHead
  have hurLeft : ur i.castSucc = hLeftLen.symm ▸ u i := by
    have hsigma := congrArg (fun k ↦ Sigma.mk k (ur k)) hleftIdx
    have hindex : HEq (ur (head.succAbove i)) (ur i.castSucc) :=
      (Sigma.mk.inj_iff.mp hsigma).2
    have hcastOld : HEq ((hOldLen i hine).symm ▸ u i) (u i) :=
      eqRec_heq (hOldLen i hine).symm (u i)
    have hcastLeft : HEq (hLeftLen.symm ▸ u i) (u i) :=
      eqRec_heq hLeftLen.symm (u i)
    apply eq_of_heq
    exact hindex.symm.trans (heq_of_eq (hurOld i hine)) |>.trans
      hcastOld |>.trans hcastLeft.symm
  let v0r : timeH1 E (partitionIntervalLength tr i.castSucc) := hLeftLen.symm ▸ v0
  let v1r : timeH1 E (partitionIntervalLength tr i.succ) := hHeadLen'.symm ▸ v1
  have hv0rFun : v0r.toFun = v0.toFun := by
    exact toFun_cast hLeftLen v0
  have hv1rFun : v1r.toFun = v1.toFun := by
    exact toFun_cast hHeadLen' v1
  have htar0r : MapsTo v0r.toFun (Icc (0 : Real) (partitionIntervalLength tr i.castSucc))
      (extChartAt I (pr i.castSucc)).target := by
    rw [hv0rFun, hLeftLen, hprLeft]
    simpa only [i] using htar0
  have htar1r : MapsTo v1r.toFun (Icc (0 : Real) (partitionIntervalLength tr i.succ))
      (extChartAt I (pr i.succ)).target := by
    rw [hv1rFun, hHeadLen', hheadIdx, hprHead]
    simpa only [i, j] using htar1
  have hv0r : (extChartAt I (pr i.castSucc)).symm (v0r.toFun 0) =
      gamma (tr i.castSucc.castSucc) := by
    rw [hv0rFun, hprLeft, htrLeft0]
    simpa only [i] using hv0
  have hv2r : (extChartAt I (pr i.succ)).symm
      (v1r.toFun (partitionIntervalLength tr i.succ)) = gamma (tr i.succ.succ) := by
    rw [hv1rFun, hHeadLen', hheadIdx, hprHead, htrHead1]
    simpa only [i, j] using hv2
  have hvnoder : (extChartAt I (pr i.castSucc)).symm
        (v0r.toFun (partitionIntervalLength tr i.castSucc)) =
      (extChartAt I (pr i.succ)).symm (v1r.toFun 0) := by
    rw [hv0rFun, hv1rFun, hLeftLen, hprLeft, hheadIdx, hprHead]
    simpa only [i] using hvnode
  have hposLeft : tr i.castSucc.castSucc < tr i.castSucc.succ := by
    rw [htrLeft0, htrLeft1]
    simpa only [i] using hpos0
  have hposHead : tr i.succ.castSucc < tr i.succ.succ := by
    rw [hheadIdx, htrHead0, htrHead1]
    simpa only [j] using hc0
  have hcmpR := lChartAction_adjacent_pair_le_of_lRegAction_minimizer (I := I) S hMet hSc T a b
    (m := m + 1) tr htrMono (htr0.trans ht0) (htrLast.trans htlast)
    pr gamma hgamma ur hsrcR hrepR hreg hmin i hposLeft hposHead
    v0r v1r htar0r htar1r hv0r hv2r hvnoder
  have hActLeft :
      lChartAction S T (tr i.castSucc.castSucc) (pr i.castSucc) (ur i.castSucc) =
        lChartAction S T (t i.castSucc) (p i) (u i) := by
    rw [htrLeft0, hprLeft, hurLeft]
    exact act_cast hLeftLen S T (t i.castSucc) (p i) (u i)
  have hActHead :
      lChartAction S T (tr i.succ.castSucc) (pr i.succ) (ur i.succ) =
        lChartAction S T (t j.castSucc) (p i) uHead := by
    rw [hheadIdx, htrHead0, hprHead, hurHead]
    exact act_cast hHeadLen S T (t j.castSucc) (p i) uHead
  have hActV0 :
      lChartAction S T (tr i.castSucc.castSucc) (pr i.castSucc) v0r =
        lChartAction S T (t i.castSucc) (p i) v0 := by
    rw [htrLeft0, hprLeft]
    exact act_cast hLeftLen S T (t i.castSucc) (p i) v0
  have hActV1 :
      lChartAction S T (tr i.succ.castSucc) (pr i.succ) v1r =
        lChartAction S T (t j.castSucc) (p i) v1 := by
    rw [htrHead0', hprHead']
    exact act_cast hHeadLen' S T (t j.castSucc) (p i) v1
  rw [hActLeft, hActHead, hActV0, hActV1] at hcmpR
  simpa only [i, j] using hcmpR

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
