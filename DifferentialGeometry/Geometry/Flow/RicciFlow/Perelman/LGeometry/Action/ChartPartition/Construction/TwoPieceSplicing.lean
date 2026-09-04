import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.ActionDensity
import DifferentialGeometry.Topology.Manifold.CurveChart.Subdivision

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
variable {M : Type u} [UniformSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [I.Boundaryless] [CompactSpace M] in
theorem exists_chartH1_join
    (a c b : Real) (hac : a < c) (hcb : c < b)
    (gamma0 gamma1 : Real → M)
    (hgamma0 : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma0
      (Icc a c))
    (hgamma1 : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma1
      (Icc c b))
    (hnode : gamma0 c = gamma1 c) :
    ∃ (gamma : Real → M) (m : Nat) (t : Fin (m + 1) → Real)
      (p : Fin m → M) (u : (i : Fin m) → timeH1 E (partitionIntervalLength t i)),
      EqOn gamma gamma0 (Icc a c) ∧
      EqOn gamma gamma1 (Icc c b) ∧
      Monotone t ∧ t 0 = a ∧ t (Fin.last m) = b ∧
      (∃ q, t q = c) ∧
      (∀ i, MapsTo gamma (Icc (t i.castSucc) (t i.succ))
        (chartAt H (p i)).source) ∧
      (∀ i, EqOn (u i).toFun
        (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
        (Icc (0 : Real) (partitionIntervalLength t i))) := by
  classical
  obtain ⟨s0, hs00, hs0mono, ⟨m0, hs0last⟩, hp0⟩ :=
    DifferentialGeometry.Geometry.exists_chart_subdivision (H := H) hac.le
      hgamma0.continuousOn
  obtain ⟨s1, hs10, hs1mono, ⟨m1, hs1last⟩, hp1⟩ :=
    DifferentialGeometry.Geometry.exists_chart_subdivision (H := H) hcb.le
      hgamma1.continuousOn
  let t0 : Fin (m0 + 1) → Real := fun i ↦ s0 i
  let t1 : Fin (m1 + 1) → Real := fun i ↦ s1 i
  have ht00 : t0 0 = a := by
    simpa only [t0, Fin.val_zero] using congrArg Subtype.val hs00
  have ht0last : t0 (Fin.last m0) = c := by
    simpa only [t0, Fin.val_last] using congrArg Subtype.val (hs0last m0 le_rfl)
  have ht10 : t1 0 = c := by
    simpa only [t1, Fin.val_zero] using congrArg Subtype.val hs10
  have ht1last : t1 (Fin.last m1) = b := by
    simpa only [t1, Fin.val_last] using congrArg Subtype.val (hs1last m1 le_rfl)
  let p0 : Fin m0 → M := fun i ↦ Classical.choose (hp0 i)
  let p1 : Fin m1 → M := fun i ↦ Classical.choose (hp1 i)
  have hsrc0 (i : Fin m0) : MapsTo gamma0
      (Icc (t0 i.castSucc) (t0 i.succ)) (chartAt H (p0 i)).source := by
    simpa only [p0, t0, Fin.val_castSucc, Fin.val_succ] using
      Classical.choose_spec (hp0 i)
  have hsrc1 (i : Fin m1) : MapsTo gamma1
      (Icc (t1 i.castSucc) (t1 i.succ)) (chartAt H (p1 i)).source := by
    simpa only [p1, t1, Fin.val_castSucc, Fin.val_succ] using
      Classical.choose_spec (hp1 i)
  let gamma : Real → M := Set.piecewise (Iic c) gamma0 gamma1
  have hgamma0_eq : EqOn gamma gamma0 (Icc a c) := by
    intro s hs
    exact (Iic c).piecewise_eq_of_mem gamma0 gamma1 (mem_Iic.mpr hs.2)
  have hgamma1_eq : EqOn gamma gamma1 (Icc c b) := by
    intro s hs
    by_cases hsc : s = c
    · subst s
      simpa only [gamma, Set.piecewise, Set.mem_Iic, if_pos le_rfl] using hnode
    · exact (Iic c).piecewise_eq_of_notMem gamma0 gamma1 (by
        rw [mem_Iic]
        exact not_le.mpr (lt_of_le_of_ne hs.1 (Ne.symm hsc)))
  let ta : Fin ((m0 + 1) + (m1 + 1)) → Real := Fin.append t0 t1
  let t : Fin ((m0 + 1 + m1) + 1) → Real :=
    fun i ↦ ta ⟨i.1, by omega⟩
  have ht_left (i : Fin ((m0 + 1 + m1) + 1)) (hi : i.1 < m0 + 1) :
      t i = t0 ⟨i.1, hi⟩ := by
    let i0 : Fin (m0 + 1) := ⟨i.1, hi⟩
    have heq : (⟨i.1, by omega⟩ : Fin ((m0 + 1) + (m1 + 1))) =
        Fin.castAdd (m1 + 1) i0 := by
      apply Fin.ext
      rfl
    change Fin.append t0 t1 ⟨i.1, by omega⟩ = t0 i0
    rw [heq, Fin.append_left]
  have ht_right (i : Fin ((m0 + 1 + m1) + 1))
      (hi : m0 + 1 ≤ i.1) :
      t i = t1 ⟨i.1 - (m0 + 1), by omega⟩ := by
    let i1 : Fin (m1 + 1) := ⟨i.1 - (m0 + 1), by omega⟩
    have heq : (⟨i.1, by omega⟩ : Fin ((m0 + 1) + (m1 + 1))) =
        Fin.natAdd (m0 + 1) i1 := by
      apply Fin.ext
      simp only [i1, Fin.natAdd, Fin.val_mk]
      omega
    change Fin.append t0 t1 ⟨i.1, by omega⟩ = t1 i1
    rw [heq, Fin.append_right]
  have htmono : Monotone t := by
    intro i j hij
    rcases lt_or_ge i.1 (m0 + 1) with hi | hi
    · rcases lt_or_ge j.1 (m0 + 1) with hj | hj
      · let i0 : Fin (m0 + 1) := ⟨i.1, hi⟩
        let j0 : Fin (m0 + 1) := ⟨j.1, hj⟩
        have hij0 : i0 ≤ j0 := by
          change i.1 ≤ j.1
          exact hij
        rw [ht_left i hi, ht_left j hj]
        exact hs0mono hij0
      · let i0 : Fin (m0 + 1) := ⟨i.1, hi⟩
        let j1 : Fin (m1 + 1) := ⟨j.1 - (m0 + 1), by omega⟩
        calc
          t i = t0 i0 := ht_left i hi
          _ ≤ t0 (Fin.last m0) := hs0mono (Fin.le_last _)
          _ = t1 0 := ht0last.trans ht10.symm
          _ ≤ t1 j1 := hs1mono (Fin.zero_le _)
          _ = t j := (ht_right j hj).symm
    · have hj : m0 + 1 ≤ j.1 := Nat.le_trans hi hij
      let i1 : Fin (m1 + 1) := ⟨i.1 - (m0 + 1), by omega⟩
      let j1 : Fin (m1 + 1) := ⟨j.1 - (m0 + 1), by omega⟩
      have hij1 : i1 ≤ j1 := by
        change i.1 - (m0 + 1) ≤ j.1 - (m0 + 1)
        exact Nat.sub_le_sub_right hij _
      rw [ht_right i hi, ht_right j hj]
      exact hs1mono hij1
  let p : Fin (m0 + 1 + m1) → M := Fin.addCases
    (fun i ↦ if hi : i.1 < m0 then p0 ⟨i.1, hi⟩ else gamma0 c) p1
  have hlen0 (i0 : Fin (m0 + 1)) (hi : i0.1 < m0) :
      partitionIntervalLength t (Fin.castAdd m1 i0) = partitionIntervalLength t0 ⟨i0.1, hi⟩ := by
    have hs : (Fin.castAdd m1 i0).castSucc.1 < m0 + 1 := by
      simp only [Fin.val_castSucc, Fin.val_castAdd]
      omega
    have he : (Fin.castAdd m1 i0).succ.1 < m0 + 1 := by
      simp only [Fin.val_succ, Fin.val_castAdd]
      omega
    simp only [partitionIntervalLength]
    rw [ht_left _ he, ht_left _ hs]
    rfl
  have hlenMid : partitionIntervalLength t (Fin.castAdd m1 (Fin.last m0)) = 0 := by
    have hs : (Fin.castAdd m1 (Fin.last m0)).castSucc.1 < m0 + 1 := by
      simp only [Fin.val_castSucc, Fin.val_castAdd, Fin.val_last]
      omega
    have he : m0 + 1 ≤ (Fin.castAdd m1 (Fin.last m0)).succ.1 := by
      simp only [Fin.val_succ, Fin.val_castAdd, Fin.val_last]
      exact le_rfl
    simp only [partitionIntervalLength]
    rw [ht_left _ hs, ht_right _ he]
    have hleft : (⟨(Fin.castAdd m1 (Fin.last m0)).castSucc.1, hs⟩ :
        Fin (m0 + 1)) = Fin.last m0 := by
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.val_castAdd]
    have hright : (⟨(Fin.castAdd m1 (Fin.last m0)).succ.1 - (m0 + 1),
        by omega⟩ : Fin (m1 + 1)) = 0 := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_castAdd, Fin.val_last, Fin.val_zero]
      omega
    rw [hleft, hright, ht0last, ht10, sub_self]
  have hlen1 (i : Fin m1) :
      partitionIntervalLength t (Fin.natAdd (m0 + 1) i) = partitionIntervalLength t1 i := by
    have hs : m0 + 1 ≤ (Fin.natAdd (m0 + 1) i).castSucc.1 := by
      simp only [Fin.val_castSucc, Fin.val_natAdd]
      omega
    have he : m0 + 1 ≤ (Fin.natAdd (m0 + 1) i).succ.1 := by
      simp only [Fin.val_succ, Fin.val_natAdd]
      omega
    simp only [partitionIntervalLength]
    rw [ht_right _ he, ht_right _ hs]
    congr 2 <;> apply Fin.ext <;>
      simp only [Fin.val_succ, Fin.val_natAdd, Fin.val_castSucc] <;> omega
  have ht0mem (i : Fin (m0 + 1)) : t0 i ∈ Icc a c := by
    simpa only [t0] using (s0 i.1).2
  have ht1mem (i : Fin (m1 + 1)) : t1 i ∈ Icc c b := by
    simpa only [t1] using (s1 i.1).2
  have toFun_cast {x y : Real} (hxy : x = y) (v : timeH1 E y) :
      ((hxy.symm ▸ v : timeH1 E x).toFun) = v.toFun := by
    subst y
    rfl
  have hlen0_nonneg (j : Fin m0) : 0 ≤ partitionIntervalLength t0 j := by
    exact sub_nonneg.mpr (hs0mono (Fin.castSucc_le_succ j))
  have hshift0 (j : Fin m0) : MapsTo
      (fun r : Real ↦ t0 j.castSucc + r)
      (Icc (0 : Real) (partitionIntervalLength t0 j)) (Icc a c) := by
    intro r hr
    have hr' : r ≤ t0 j.succ - t0 j.castSucc := by
      simpa only [partitionIntervalLength] using hr.2
    exact ⟨(ht0mem j.castSucc).1.trans (le_add_of_nonneg_right hr.1),
      (by linarith [(ht0mem j.succ).2, hr'])⟩
  have hshift0_segment (j : Fin m0) : MapsTo
      (fun r : Real ↦ t0 j.castSucc + r)
      (Icc (0 : Real) (partitionIntervalLength t0 j))
      (Icc (t0 j.castSucc) (t0 j.succ)) := by
    intro r hr
    have hr' : r ≤ t0 j.succ - t0 j.castSucc := by
      simpa only [partitionIntervalLength] using hr.2
    exact ⟨le_add_of_nonneg_right hr.1, by linarith⟩
  have hmd0 (j : Fin m0) : ContMDiffOn
      (modelWithCornersSelf Real Real) I 1
      (fun r : Real ↦ gamma0 (t0 j.castSucc + r))
      (Icc (0 : Real) (partitionIntervalLength t0 j)) :=
    hgamma0.comp (contMDiff_const.add contMDiff_id).contMDiffOn (hshift0 j)
  have hsrc0_shift (j : Fin m0) : MapsTo
      (fun r : Real ↦ gamma0 (t0 j.castSucc + r))
      (Icc (0 : Real) (partitionIntervalLength t0 j)) (chartAt H (p0 j)).source :=
    (hsrc0 j).comp (hshift0_segment j)
  let v0 (j : Fin m0) : timeH1 E (partitionIntervalLength t0 j) :=
    chartTimeH1 I (hlen0_nonneg j) (p0 j)
      (fun r ↦ gamma0 (t0 j.castSucc + r))
      (hmd0 j) (hsrc0_shift j)
  have hv0 (j : Fin m0) : EqOn (v0 j).toFun
      (fun r ↦ extChartAt I (p0 j) (gamma0 (t0 j.castSucc + r)))
      (Icc (0 : Real) (partitionIntervalLength t0 j)) := by
    intro r hr
    exact chartTimeH1_toFun I (hlen0_nonneg j) (p0 j)
      (fun r ↦ gamma0 (t0 j.castSucc + r)) (hmd0 j) (hsrc0_shift j) hr
  let vMid : timeH1 E 0 :=
    chartTimeH1 I (by norm_num) (gamma0 c) (fun _ ↦ gamma0 c)
      contMDiff_const.contMDiffOn (by
        intro _ _
        exact mem_chart_source H (gamma0 c))
  have hvMid : EqOn vMid.toFun
      (fun _ ↦ extChartAt I (gamma0 c) (gamma0 c)) (Icc (0 : Real) 0) := by
    intro r hr
    exact chartTimeH1_toFun I (by norm_num) (gamma0 c) (fun _ ↦ gamma0 c)
      contMDiff_const.contMDiffOn (by
        intro _ _
        exact mem_chart_source H (gamma0 c)) hr
  have hlen1_nonneg (j : Fin m1) : 0 ≤ partitionIntervalLength t1 j := by
    exact sub_nonneg.mpr (hs1mono (Fin.castSucc_le_succ j))
  have hshift1 (j : Fin m1) : MapsTo
      (fun r : Real ↦ t1 j.castSucc + r)
      (Icc (0 : Real) (partitionIntervalLength t1 j)) (Icc c b) := by
    intro r hr
    have hr' : r ≤ t1 j.succ - t1 j.castSucc := by
      simpa only [partitionIntervalLength] using hr.2
    exact ⟨(ht1mem j.castSucc).1.trans (le_add_of_nonneg_right hr.1),
      (by linarith [(ht1mem j.succ).2, hr'])⟩
  have hshift1_segment (j : Fin m1) : MapsTo
      (fun r : Real ↦ t1 j.castSucc + r)
      (Icc (0 : Real) (partitionIntervalLength t1 j))
      (Icc (t1 j.castSucc) (t1 j.succ)) := by
    intro r hr
    have hr' : r ≤ t1 j.succ - t1 j.castSucc := by
      simpa only [partitionIntervalLength] using hr.2
    exact ⟨le_add_of_nonneg_right hr.1, by linarith⟩
  have hmd1 (j : Fin m1) : ContMDiffOn
      (modelWithCornersSelf Real Real) I 1
      (fun r : Real ↦ gamma1 (t1 j.castSucc + r))
      (Icc (0 : Real) (partitionIntervalLength t1 j)) :=
    hgamma1.comp (contMDiff_const.add contMDiff_id).contMDiffOn (hshift1 j)
  have hsrc1_shift (j : Fin m1) : MapsTo
      (fun r : Real ↦ gamma1 (t1 j.castSucc + r))
      (Icc (0 : Real) (partitionIntervalLength t1 j)) (chartAt H (p1 j)).source :=
    (hsrc1 j).comp (hshift1_segment j)
  let v1 (j : Fin m1) : timeH1 E (partitionIntervalLength t1 j) :=
    chartTimeH1 I (hlen1_nonneg j) (p1 j)
      (fun r ↦ gamma1 (t1 j.castSucc + r))
      (hmd1 j) (hsrc1_shift j)
  have hv1 (j : Fin m1) : EqOn (v1 j).toFun
      (fun r ↦ extChartAt I (p1 j) (gamma1 (t1 j.castSucc + r)))
      (Icc (0 : Real) (partitionIntervalLength t1 j)) := by
    intro r hr
    exact chartTimeH1_toFun I (hlen1_nonneg j) (p1 j)
      (fun r ↦ gamma1 (t1 j.castSucc + r)) (hmd1 j) (hsrc1_shift j) hr
  have hlast0 (i0 : Fin (m0 + 1)) (hi : ¬ i0.1 < m0) :
      i0 = Fin.last m0 := by
    apply Fin.ext
    simp only [Fin.val_last]
    omega
  have hlenMid0 (i0 : Fin (m0 + 1)) (hi : ¬ i0.1 < m0) :
      partitionIntervalLength t (Fin.castAdd m1 i0) = 0 := by
    simpa only [hlast0 i0 hi] using hlenMid
  let u : (i : Fin (m0 + 1 + m1)) → timeH1 E (partitionIntervalLength t i) := Fin.addCases
    (fun i0 ↦ if hi : i0.1 < m0 then
      (hlen0 i0 hi).symm ▸ v0 ⟨i0.1, hi⟩
      else
      (hlenMid0 i0 hi).symm ▸ vMid)
    (fun i1 ↦ (hlen1 i1).symm ▸ v1 i1)
  refine ⟨gamma, m0 + 1 + m1, t, p, u, hgamma0_eq, hgamma1_eq, htmono, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ht_left 0 (by simp)]
    exact ht00
  · rw [ht_right (Fin.last (m0 + 1 + m1)) (by
      simp only [Fin.val_last]
      omega)]
    convert ht1last using 1
    apply congrArg t1
    apply Fin.ext
    simp only [Fin.val_last]
    omega
  · refine ⟨Fin.castAdd (m1 + 1) (Fin.last m0), ?_⟩
    rw [ht_left _ (by
      simp only [Fin.val_castAdd, Fin.val_last]
      omega)]
    exact ht0last
  · intro i
    refine Fin.addCases (fun i0 ↦ ?_) (fun i1 ↦ ?_) i
    · by_cases hi : i0.1 < m0
      · let j : Fin m0 := ⟨i0.1, hi⟩
        have hseg : Icc (t (Fin.castAdd m1 i0).castSucc)
            (t (Fin.castAdd m1 i0).succ) = Icc (t0 j.castSucc) (t0 j.succ) := by
          apply congrArg₂ Icc
          · rw [ht_left _ (by
              simp only [Fin.val_castSucc, Fin.val_castAdd]
              omega)]
            apply congrArg t0
            apply Fin.ext
            rfl
          · rw [ht_left _ (by
              simp only [Fin.val_succ, Fin.val_castAdd]
              omega)]
            apply congrArg t0
            apply Fin.ext
            rfl
        rw [show p (Fin.castAdd m1 i0) = p0 j by
          simp only [p, Fin.addCases_left, dif_pos hi, j]]
        rw [hseg]
        intro s hs
        have hsac : s ∈ Icc a c := ⟨(ht0mem j.castSucc).1.trans hs.1,
          hs.2.trans (ht0mem j.succ).2⟩
        rw [hgamma0_eq hsac]
        exact hsrc0 j hs
      · have hiLast := hlast0 i0 hi
        subst i0
        simp only [p, Fin.addCases_left, dif_neg (by omega)]
        intro s hs
        have hstart : t (Fin.castAdd m1 (Fin.last m0)).castSucc = c := by
          rw [ht_left _ (by
            simp only [Fin.val_castSucc, Fin.val_castAdd, Fin.val_last]
            omega)]
          rw [show (⟨(Fin.castAdd m1 (Fin.last m0)).castSucc.1, by
              simp only [Fin.val_castSucc, Fin.val_castAdd, Fin.val_last]
              omega⟩ :
              Fin (m0 + 1)) = Fin.last m0 by
            apply Fin.ext
            rfl]
          exact ht0last
        have hend : t (Fin.castAdd m1 (Fin.last m0)).succ = c := by
          rw [ht_right _ (by
            simp only [Fin.val_succ, Fin.val_castAdd, Fin.val_last]
            omega)]
          have hidx : (⟨(Fin.castAdd m1 (Fin.last m0)).succ.1 - (m0 + 1),
              by omega⟩ : Fin (m1 + 1)) = 0 := by
            apply Fin.ext
            simp only [Fin.val_succ, Fin.val_castAdd, Fin.val_last, Fin.val_zero]
            omega
          rw [hidx, ht10]
        have hsC : s = c := by
          rw [hstart, hend] at hs
          exact le_antisymm hs.2 hs.1
        rw [hsC]
        rw [hgamma0_eq ⟨hac.le, le_rfl⟩]
        exact mem_chart_source H (gamma0 c)
    · have hseg : Icc (t (Fin.natAdd (m0 + 1) i1).castSucc)
          (t (Fin.natAdd (m0 + 1) i1).succ) =
          Icc (t1 i1.castSucc) (t1 i1.succ) := by
        apply congrArg₂ Icc
        · rw [ht_right _ (by
            simp only [Fin.val_castSucc, Fin.val_natAdd]
            omega)]
          apply congrArg t1
          apply Fin.ext
          simp only [Fin.val_castSucc, Fin.val_natAdd]
          omega
        · rw [ht_right _ (by
            simp only [Fin.val_succ, Fin.val_natAdd]
            omega)]
          apply congrArg t1
          apply Fin.ext
          simp only [Fin.val_succ, Fin.val_natAdd]
          omega
      rw [show p (Fin.natAdd (m0 + 1) i1) = p1 i1 by
        simp only [p, Fin.addCases_right]]
      rw [hseg]
      intro s hs
      have hscb : s ∈ Icc c b := ⟨(ht1mem i1.castSucc).1.trans hs.1,
        hs.2.trans (ht1mem i1.succ).2⟩
      rw [hgamma1_eq hscb]
      exact hsrc1 i1 hs
  · intro i
    refine Fin.addCases (fun i0 ↦ ?_) (fun i1 ↦ ?_) i
    · by_cases hi : i0.1 < m0
      · let j : Fin m0 := ⟨i0.1, hi⟩
        intro r hr
        have hr' : r ∈ Icc (0 : Real) (partitionIntervalLength t0 j) := by
          simpa only [hlen0 i0 hi] using hr
        have hu : u (Fin.castAdd m1 i0) =
            (hlen0 i0 hi).symm ▸ v0 j := by
          simp only [u, Fin.addCases_left, dif_pos hi, j]
        have hp0eq : p (Fin.castAdd m1 i0) = p0 j := by
          simp only [p, Fin.addCases_left, dif_pos hi, j]
        have ht0eq : t (Fin.castAdd m1 i0).castSucc = t0 j.castSucc := by
          rw [ht_left _ (by
            simp only [Fin.val_castSucc, Fin.val_castAdd]
            omega)]
          apply congrArg t0
          apply Fin.ext
          rfl
        rw [hu, toFun_cast (hlen0 i0 hi) (v0 j), hv0 j hr', hp0eq, ht0eq]
        exact congrArg (extChartAt I (p0 j))
          (hgamma0_eq (hshift0 j hr')).symm
      · have hiLast := hlast0 i0 hi
        subst i0
        intro r hr
        have hnot : ¬ (Fin.last m0).1 < m0 := by
          simp only [Fin.val_last]
          omega
        have hmid := hlenMid0 (Fin.last m0) hnot
        have hr0 : r = 0 := by
          have hrle : r ≤ 0 := by
            simpa only [hmid] using hr.2
          exact le_antisymm hrle hr.1
        subst r
        have hu : u (Fin.castAdd m1 (Fin.last m0)) = hmid.symm ▸ vMid := by
          simp only [u, Fin.addCases_left, dif_neg hnot]
        have hpMid : p (Fin.castAdd m1 (Fin.last m0)) = gamma0 c := by
          simp only [p, Fin.addCases_left, dif_neg hnot]
        have htMid : t (Fin.castAdd m1 (Fin.last m0)).castSucc = c := by
          rw [ht_left _ (by
            simp only [Fin.val_castSucc, Fin.val_castAdd, Fin.val_last]
            omega)]
          rw [show (⟨(Fin.castAdd m1 (Fin.last m0)).castSucc.1, by
              simp only [Fin.val_castSucc, Fin.val_castAdd, Fin.val_last]
              omega⟩ :
              Fin (m0 + 1)) = Fin.last m0 by
            apply Fin.ext
            rfl]
          exact ht0last
        rw [hu, toFun_cast hmid vMid, hvMid ⟨le_rfl, le_rfl⟩,
          hpMid, htMid]
        simp only [add_zero]
        exact congrArg (extChartAt I (gamma0 c)) (hgamma0_eq
          ⟨hac.le, le_rfl⟩).symm
    · intro r hr
      have hr' : r ∈ Icc (0 : Real) (partitionIntervalLength t1 i1) := by
        simpa only [hlen1 i1] using hr
      have hu : u (Fin.natAdd (m0 + 1) i1) =
          (hlen1 i1).symm ▸ v1 i1 := by
        simp only [u, Fin.addCases_right]
      have hp1eq : p (Fin.natAdd (m0 + 1) i1) = p1 i1 := by
        simp only [p, Fin.addCases_right]
      have ht1eq : t (Fin.natAdd (m0 + 1) i1).castSucc = t1 i1.castSucc := by
        rw [ht_right _ (by
          simp only [Fin.val_castSucc, Fin.val_natAdd]
          omega)]
        apply congrArg t1
        apply Fin.ext
        simp only [Fin.val_castSucc, Fin.val_natAdd]
        omega
      rw [hu, toFun_cast (hlen1 i1) (v1 i1), hv1 i1 hr', hp1eq, ht1eq]
      exact congrArg (extChartAt I (p1 i1))
        (hgamma1_eq (hshift1 i1 hr')).symm

omit [CompactSpace M] in
theorem exists_contMDiff_one_lRegularizedAction_approximation_of_compatible_chartH1_pair
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T : Real) (t : Fin 3 → Real) (htmono : Monotone t)
    (p : Fin 2 → M)
    (v : (i : Fin 2) → timeH1 E (partitionIntervalLength t i))
    (htar : ∀ i, MapsTo (v i).toFun
      (Icc (0 : Real) (partitionIntervalLength t i)) (extChartAt I (p i)).target)
    (hnode : (extChartAt I (p 0)).symm
        ((v 0).toFun (partitionIntervalLength t 0)) =
      (extChartAt I (p 1)).symm ((v 1).toFun 0))
    (hreg : ∀ s ∈ Icc (t 0) (t (Fin.last 2)), T - s ^ 2 ∈ D.regular) :
    ∃ gamma : Real → M,
      Continuous gamma ∧
      (∀ i, MapsTo gamma
        (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source) ∧
      (∀ i, EqOn (v i).toFun
        (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
        (Icc (0 : Real) (partitionIntervalLength t i))) ∧
      gamma (t 0) = (extChartAt I (p 0)).symm ((v 0).toFun 0) ∧
      gamma (t (Fin.last 2)) = (extChartAt I (p 1)).symm
        ((v 1).toFun (partitionIntervalLength t 1)) ∧
      ∃ alpha : Nat → Real → M,
        ∃ w : (i : Fin 2) → Nat → timeH1 E (partitionIntervalLength t i),
          (∀ n, ContMDiff (modelWithCornersSelf Real Real) I 1 (alpha n)) ∧
          (∀ n, alpha n (t 0) = gamma (t 0)) ∧
          (∀ n, alpha n (t (Fin.last 2)) = gamma (t (Fin.last 2))) ∧
          (∀ i n, MapsTo (alpha n)
            (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source) ∧
          (∀ i n, EqOn (w i n).toFun
            (fun r ↦ extChartAt I (p i) (alpha n (t i.castSucc + r)))
            (Icc (0 : Real) (partitionIntervalLength t i))) ∧
          (∀ i, Tendsto (w i) atTop (nhds (v i))) ∧
          TendstoUniformly
            (fun n (s : Icc (t 0) (t (Fin.last 2))) ↦ alpha n s.1)
            (fun s ↦ gamma s.1) atTop ∧
          Tendsto (fun n ↦ lRegularizedAction S T (alpha n) (t 0) (t (Fin.last 2)))
            atTop (nhds (lRegularizedAction S T gamma (t 0) (t (Fin.last 2)))) := by
  classical
  have hseg (i : Fin 2) : t i.castSucc ≤ t i.succ :=
    htmono Fin.castSucc_lt_succ.le
  have hlen (i : Fin 2) : 0 ≤ partitionIntervalLength t i :=
    sub_nonneg.mpr (hseg i)
  let pr (i : Fin 2) (s : Real) : Real :=
    ((Set.projIcc (0 : Real) (partitionIntervalLength t i) (hlen i) s :
      Icc (0 : Real) (partitionIntervalLength t i)) : Real)
  have hpr_mem (i : Fin 2) (s : Real) :
      pr i s ∈ Icc (0 : Real) (partitionIntervalLength t i) :=
    (Set.projIcc (0 : Real) (partitionIntervalLength t i) (hlen i) s).2
  have hpr_cont (i : Fin 2) : Continuous (pr i) :=
    continuous_subtype_val.comp continuous_projIcc
  have hpr_shift (i : Fin 2) {s : Real}
      (hs : s ∈ Icc (t i.castSucc) (t i.succ)) :
      pr i (s - t i.castSucc) = s - t i.castSucc := by
    simp only [pr]
    exact congrArg Subtype.val (Set.projIcc_of_mem (hlen i) ⟨
      sub_nonneg.mpr hs.1, by
        simpa only [partitionIntervalLength] using sub_le_sub_right hs.2 (t i.castSucc)⟩)
  let lift (i : Fin 2) (s : Real) : M :=
    (extChartAt I (p i)).symm ((v i).toFun (pr i (s - t i.castSucc)))
  have hlift_cont (i : Fin 2) : Continuous (lift i) := by
    rw [← continuousOn_univ]
    exact (continuousOn_extChartAt_symm (I := I) (p i)).comp
      ((v i).continuousOn_toFun.comp_continuous
        ((hpr_cont i).comp (continuous_id.sub continuous_const))
        (fun s ↦ hpr_mem i (s - t i.castSucc))).continuousOn
      (fun s _ ↦ htar i (hpr_mem i (s - t i.castSucc)))
  have hlift_coord (i : Fin 2) {s : Real}
      (hs : s ∈ Icc (t i.castSucc) (t i.succ)) :
      extChartAt I (p i) (lift i s) = (v i).toFun (s - t i.castSucc) := by
    simp only [lift]
    rw [hpr_shift i hs]
    exact (extChartAt I (p i)).right_inv (htar i ⟨
      sub_nonneg.mpr hs.1, by
        simpa only [partitionIntervalLength] using sub_le_sub_right hs.2 (t i.castSucc)⟩)
  have hleft_node : lift 0 (t 1) =
      (extChartAt I (p 0)).symm ((v 0).toFun (partitionIntervalLength t 0)) := by
    simp only [lift]
    rw [hpr_shift 0 (by
      constructor
      · simpa using hseg 0
      · simp)]
    congr 2
  have hright_node : lift 1 (t 1) =
      (extChartAt I (p 1)).symm ((v 1).toFun 0) := by
    simp only [lift]
    rw [hpr_shift 1 (by
      constructor
      · simp
      · simpa using hseg 1)]
    congr 2
    rw [show (1 : Fin 2).castSucc = (1 : Fin 3) by rfl, sub_self]
  have hlifts_node : lift 0 (t 1) = lift 1 (t 1) :=
    hleft_node.trans (hnode.trans hright_node.symm)
  let gamma : Real → M := Set.piecewise (Iic (t 1)) (lift 0) (lift 1)
  have hgamma : Continuous gamma := by
    apply (hlift_cont 0).piecewise (s := Iic (t 1))
    · intro s hs
      have hst : s = t 1 := by
        simpa only [frontier_Iic, mem_singleton_iff] using hs
      simpa only [hst] using hlifts_node
    · exact hlift_cont 1
  have hgamma_piece (i : Fin 2) {s : Real}
      (hs : s ∈ Icc (t i.castSucc) (t i.succ)) : gamma s = lift i s := by
    fin_cases i
    · exact (Iic (t 1)).piecewise_eq_of_mem _ _ (by simpa using hs.2)
    · by_cases hst : s = t 1
      · subst s
        simp only [gamma]
        rw [(Iic (t 1)).piecewise_eq_of_mem _ _ (mem_Iic.mpr le_rfl)]
        exact hlifts_node
      · exact (Iic (t 1)).piecewise_eq_of_notMem _ _ (by
          rw [mem_Iic]
          intro hle
          have hge : t 1 ≤ s := by simpa using hs.1
          exact hst (le_antisymm hle hge))
  have hsrc (i : Fin 2) : MapsTo gamma
      (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source := by
    intro s hs
    rw [hgamma_piece i hs]
    simpa only [lift, extChartAt_source] using
      (extChartAt I (p i)).map_target
        (htar i (hpr_mem i (s - t i.castSucc)))
  have hrep (i : Fin 2) : EqOn (v i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (Icc (0 : Real) (partitionIntervalLength t i)) := by
    intro r hr
    have hs : t i.castSucc + r ∈ Icc (t i.castSucc) (t i.succ) := by
      constructor
      · linarith [hr.1]
      · have hr' := hr.2
        simp only [partitionIntervalLength] at hr'
        linarith
    change (v i).toFun r =
      extChartAt I (p i) (gamma (t i.castSucc + r))
    rw [hgamma_piece i hs, hlift_coord i hs]
    congr 2
    ring
  have hgamma_left : gamma (t 0) =
      (extChartAt I (p 0)).symm ((v 0).toFun 0) := by
    rw [hgamma_piece 0 (by
      constructor
      · simp
      · simpa using hseg 0)]
    simp only [lift]
    rw [hpr_shift 0 (by
      constructor
      · simp
      · simpa using hseg 0)]
    congr 2
    rw [show (0 : Fin 2).castSucc = (0 : Fin 3) by rfl, sub_self]
  have hgamma_right : gamma (t (Fin.last 2)) =
      (extChartAt I (p 1)).symm ((v 1).toFun (partitionIntervalLength t 1)) := by
    rw [hgamma_piece 1 (by
      constructor
      · simpa using hseg 1
      · simp)]
    simp only [lift]
    rw [hpr_shift 1 (by
      constructor
      · simpa using hseg 1
      · simp)]
    congr 2
  obtain ⟨alpha, w, halpha, halpha0, halphaL, hsrcA, hrepA, hw,
      huniform, hact⟩ :=
    lAction_c1_dense S hMet hSc T (t 0) (t (Fin.last 2)) t htmono rfl rfl
      p gamma v hsrc hrep hreg
  exact ⟨gamma, hgamma, hsrc, hrep, hgamma_left, hgamma_right, alpha, w,
    halpha, halpha0, halphaL, hsrcA, hrepA, hw, huniform, hact⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
