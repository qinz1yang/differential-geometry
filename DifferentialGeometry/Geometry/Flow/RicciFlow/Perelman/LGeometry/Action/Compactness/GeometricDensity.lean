import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Chart.Density
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Curve.Partition

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Filter Function Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

universe u uE uH

private theorem flatJoin_stable
    {X : Type*} (x : X) (t : Nat → Real) (f : Nat → Real → X)
    (ht : Monotone t) {k n : Nat} (hkn : k ≤ n) {s : Real}
    (hs : s ≤ t k) :
    flatJoin x t f n s = flatJoin x t f k s := by
  induction n with
  | zero => simp only [Nat.le_zero.mp hkn, flatJoin]
  | succ n hn =>
      rcases hkn.eq_or_lt with rfl | hkn
      · rfl
      · rw [flatJoin, (Iic (t n)).piecewise_eq_of_mem]
        · exact hn (Nat.le_of_lt_succ hkn)
        · exact hs.trans (ht (Nat.le_of_lt_succ hkn))

private theorem flatJoin_node
    {X : Type*} (x : X) (t : Nat → Real) (f : Nat → Real → X)
    (ht : Monotone t) (hzero : x = f 0 (t 0))
    (hnode : ∀ i, f i (t (i + 1)) = f (i + 1) (t (i + 1)))
    {n i : Nat} (hi : i < n) :
    flatJoin x t f n (t i) = f i (t i) := by
  have hbase : ∀ j, flatJoin x t f j (t j) = f j (t j) := by
    intro j
    induction j with
    | zero => simpa only [flatJoin] using hzero
    | succ j hj =>
        rw [flatJoin]
        by_cases heq : t (j + 1) ≤ t j
        · have hnodes : t (j + 1) = t j :=
            le_antisymm heq (ht (Nat.le_succ j))
          rw [(Iic (t j)).piecewise_eq_of_mem _ _ heq]
          simpa only [hnodes] using hj.trans (by simpa only [hnodes] using hnode j)
        · exact ((Iic (t j)).piecewise_eq_of_notMem _ _ heq).trans (hnode j)
  calc
    flatJoin x t f n (t i) = flatJoin x t f i (t i) :=
      flatJoin_stable x t f ht (Nat.le_of_lt hi) le_rfl
    _ = f i (t i) := hbase i

private theorem flatJoin_closed
    {X : Type*} (x : X) (t : Nat → Real) (f : Nat → Real → X)
    (ht : Monotone t) (hzero : x = f 0 (t 0))
    (hnode : ∀ i, f i (t (i + 1)) = f (i + 1) (t (i + 1)))
    {n i : Nat} (hi : i < n) {s : Real}
    (hs : s ∈ Icc (t i) (t (i + 1))) :
    flatJoin x t f n s = f i s := by
  rcases hs.1.eq_or_lt with rfl | hlt
  · exact flatJoin_node x t f ht hzero hnode hi
  · exact flatJoin_eq x t f ht hi hlt hs.2

private theorem exists_fin_segment
    {m : Nat} (hm : 0 < m) (t : Fin (m + 1) → Real)
    (ht : Monotone t) {a b s : Real} (ht0 : t 0 = a)
    (htlast : t (Fin.last m) = b) (hs : s ∈ Icc a b) :
    ∃ i : Fin m, s ∈ Icc (t i.castSucc) (t i.succ) := by
  let P : Nat → Prop := fun k ↦ ∃ hk : k < m + 1, s ≤ t ⟨k, hk⟩
  have hP : ∃ k, P k := by
    refine ⟨m, Nat.lt_succ_self m, ?_⟩
    have hlast : t ⟨m, Nat.lt_succ_self m⟩ = b := by
      simpa only [Fin.last] using htlast
    simpa only [hlast] using hs.2
  let k := Nat.find hP
  rcases Nat.find_spec hP with ⟨hklt, hks⟩
  by_cases hk0 : k = 0
  · let i : Fin m := ⟨0, hm⟩
    refine ⟨i, ?_⟩
    have hsa : s = a := by
      apply le_antisymm
      · have hidx : (⟨k, hklt⟩ : Fin (m + 1)) = 0 := by
          ext
          exact hk0
        rw [hidx, ht0] at hks
        exact hks
      · exact hs.1
    subst s
    constructor
    · have hidx : i.castSucc = (0 : Fin (m + 1)) := by ext; rfl
      rw [hidx, ht0]
    · rw [← ht0]
      exact ht (Fin.zero_le _)
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hkle : k ≤ m := Nat.le_of_lt_succ hklt
    let i : Fin m := ⟨k - 1, by omega⟩
    have hprev : ¬ P (k - 1) := Nat.find_min hP (by omega)
    refine ⟨i, ?_⟩
    constructor
    · have hnot : ¬ s ≤ t ⟨k - 1, by omega⟩ := by
        intro hle
        exact hprev ⟨by omega, hle⟩
      exact le_of_lt (lt_of_not_ge hnot)
    · have hidx : i.succ = (⟨k, hklt⟩ : Fin (m + 1)) := by
        ext
        change k - 1 + 1 = k
        omega
      rw [hidx]
      exact hks

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [UniformSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

omit [CompleteSpace E] in
theorem exists_c1_of_flat
    {m : Nat} (a b : Real) (t : Fin (m + 1) → Real)
    (htmono : Monotone t) (ht0 : t 0 = a)
    (htlast : t (Fin.last m) = b)
    (p : Fin m → M) (gamma : Real → M)
    (uLim : (i : Fin m) → timeH1 E (partitionIntervalLength t i))
    (hsrcLim : ∀ i, MapsTo gamma
      (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source)
    (hrepLim : ∀ i, EqOn (uLim i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (Icc (0 : Real) (partitionIntervalLength t i)))
    (K : Fin m → Set E) (hKc : ∀ i, IsCompact (K i))
    (hKtar : ∀ i, K i ⊆ (extChartAt I (p i)).target)
    (v : (i : Fin m) → Nat → Real → E)
    (hvC1 : ∀ i n, ContDiff Real 1 (v i n))
    (hvleft : ∀ i n, v i n =ᶠ[nhds (0 : Real)] fun _ ↦ v i n 0)
    (hvright : ∀ i n, v i n =ᶠ[nhds (partitionIntervalLength t i)]
      fun _ ↦ v i n (partitionIntervalLength t i))
    (hvzero : ∀ i n, v i n 0 = (uLim i).toFun 0)
    (hvlast : ∀ i n, v i n (partitionIntervalLength t i) =
      (uLim i).toFun (partitionIntervalLength t i))
    (hvK : ∀ i n (r : Icc (0 : Real) (partitionIntervalLength t i)), v i n r.1 ∈ K i)
    (huLimK : ∀ i (r : Icc (0 : Real) (partitionIntervalLength t i)),
      (uLim i).toFun r.1 ∈ K i)
    (hvlim : ∀ i, TendstoUniformly
      (fun n (r : Icc (0 : Real) (partitionIntervalLength t i)) ↦ v i n r.1)
      (fun r ↦ (uLim i).toFun r.1) atTop) :
    ∃ alpha : Nat → Real → M,
      (∀ n, ContMDiff (modelWithCornersSelf Real Real) I 1 (alpha n)) ∧
      (∀ n, alpha n a = gamma a) ∧
      (∀ n, alpha n b = gamma b) ∧
      (∀ i n, EqOn (v i n)
        (fun r ↦ extChartAt I (p i) (alpha n (t i.castSucc + r)))
        (Icc (0 : Real) (partitionIntervalLength t i))) ∧
      (∀ i n, MapsTo (alpha n) (Icc (t i.castSucc) (t i.succ))
        (chartAt H (p i)).source) ∧
      TendstoUniformly
        (fun n (s : Icc a b) ↦ alpha n s.1)
        (fun s ↦ gamma s.1) atTop := by
  classical
  have hseg (i : Fin m) : t i.castSucc ≤ t i.succ :=
    htmono Fin.castSucc_lt_succ.le
  have hlen (i : Fin m) : 0 ≤ partitionIntervalLength t i :=
    sub_nonneg.mpr (hseg i)
  have hleft (i : Fin m) : a ≤ t i.castSucc := by
    rw [← ht0]
    exact htmono (Fin.zero_le _)
  have hright (i : Fin m) : t i.succ ≤ b := by
    rw [← htlast]
    exact htmono (Fin.le_last _)
  have hlim_lift (i : Fin m) (r : Icc (0 : Real) (partitionIntervalLength t i)) :
      (extChartAt I (p i)).symm ((uLim i).toFun r.1) =
        gamma (t i.castSucc + r.1) := by
    have hs : t i.castSucc + r.1 ∈ Icc (t i.castSucc) (t i.succ) := by
      constructor
      · linarith [r.2.1]
      · calc
          t i.castSucc + r.1 ≤ t i.castSucc + partitionIntervalLength t i :=
            add_le_add_right r.2.2 _
          _ = t i.succ := by simp only [partitionIntervalLength]; ring
    rw [hrepLim i r.2]
    exact (extChartAt I (p i)).left_inv (by
      simpa only [extChartAt_source] using hsrcLim i hs)
  let tNat : Nat → Real := fun k ↦
    t ⟨min k m, Nat.lt_succ_of_le (Nat.min_le_right k m)⟩
  have htNat : Monotone tNat := by
    intro k l hkl
    apply htmono
    apply Fin.mk_le_mk.mpr
    omega
  have htNat_of_le {k : Nat} (hk : k ≤ m) :
      tNat k = t ⟨k, Nat.lt_succ_of_le hk⟩ := by
    simp only [tNat, Nat.min_eq_left hk]
  have htNat_zero : tNat 0 = a := by
    rw [htNat_of_le (Nat.zero_le m)]
    exact ht0
  have htNat_m : tNat m = b := by
    rw [htNat_of_le le_rfl]
    exact htlast
  let lift (i : Fin m) (n : Nat) : Real → M :=
    chartFlatLift I (p i) (fun s ↦ v i n (s - t i.castSucc))
      (t i.castSucc) (t i.succ)
  have hshift_left (i : Fin m) (n : Nat) :
      (fun s ↦ v i n (s - t i.castSucc)) =ᶠ[nhds (t i.castSucc)]
        fun _ ↦ v i n 0 := by
    have htend : Tendsto (fun s : Real ↦ s - t i.castSucc)
        (nhds (t i.castSucc)) (nhds 0) := by
      simpa only [id_eq, sub_self] using
        (tendsto_id.sub tendsto_const_nhds : Tendsto
          (fun s : Real ↦ s - t i.castSucc) (nhds (t i.castSucc))
          (nhds (t i.castSucc - t i.castSucc)))
    exact (hvleft i n).comp_tendsto htend
  have hshift_right (i : Fin m) (n : Nat) :
      (fun s ↦ v i n (s - t i.castSucc)) =ᶠ[nhds (t i.succ)]
        fun _ ↦ v i n (partitionIntervalLength t i) := by
    have htend : Tendsto (fun s : Real ↦ s - t i.castSucc)
        (nhds (t i.succ)) (nhds (partitionIntervalLength t i)) := by
      simpa only [id_eq, partitionIntervalLength] using
        (tendsto_id.sub tendsto_const_nhds : Tendsto
          (fun s : Real ↦ s - t i.castSucc) (nhds (t i.succ))
          (nhds (t i.succ - t i.castSucc)))
    exact (hvright i n).comp_tendsto htend
  have hmaps (i : Fin m) (n : Nat) :
      MapsTo (fun s ↦ v i n (s - t i.castSucc))
        (Icc (t i.castSucc) (t i.succ)) (extChartAt I (p i)).target := by
    intro s hs
    apply hKtar i
    exact hvK i n ⟨s - t i.castSucc, ⟨by linarith [hs.1], by
      simpa only [partitionIntervalLength] using sub_le_sub_right hs.2 (t i.castSucc)⟩⟩
  have hlift_c1 (i : Fin m) (n : Nat) :
      ContMDiff (modelWithCornersSelf Real Real) I 1 (lift i n) := by
    apply chartLift_contMDiff I (p i)
      (fun s ↦ v i n (s - t i.castSucc)) (hseg i)
    · exact (hvC1 i n).comp (contDiff_id.sub contDiff_const)
    · simpa using hshift_left i n
    · simpa only [partitionIntervalLength] using hshift_right i n
    · exact hmaps i n
  have hlift_left (i : Fin m) (n : Nat) :
      lift i n =ᶠ[nhds (t i.castSucc)] fun _ ↦ gamma (t i.castSucc) := by
    have h := chartLift_left I (p i)
      (fun s ↦ v i n (s - t i.castSucc)) (hseg i)
      (by simpa using hshift_left i n)
    have hval : (extChartAt I (p i)).symm (v i n 0) =
        gamma (t i.castSucc) := by
      rw [hvzero i n]
      simpa using hlim_lift i ⟨0, ⟨le_rfl, hlen i⟩⟩
    have h' : lift i n =ᶠ[nhds (t i.castSucc)]
        fun _ ↦ (extChartAt I (p i)).symm (v i n 0) := by
      simpa only [lift, sub_self] using h
    exact h'.trans (Eventually.of_forall fun _ ↦ hval)
  have hlift_right (i : Fin m) (n : Nat) :
      lift i n =ᶠ[nhds (t i.succ)] fun _ ↦ gamma (t i.succ) := by
    have h := chartLift_right I (p i)
      (fun s ↦ v i n (s - t i.castSucc)) (hseg i)
      (by simpa only [partitionIntervalLength] using hshift_right i n)
    have hval : (extChartAt I (p i)).symm (v i n (partitionIntervalLength t i)) =
        gamma (t i.succ) := by
      rw [hvlast i n]
      have hr : (partitionIntervalLength t i : Real) ∈ Icc (0 : Real) (partitionIntervalLength t i) :=
        ⟨hlen i, le_rfl⟩
      have hadd : t i.castSucc + partitionIntervalLength t i = t i.succ := by
        simp only [partitionIntervalLength]
        ring
      simpa only [hadd] using hlim_lift i ⟨partitionIntervalLength t i, hr⟩
    have h' : lift i n =ᶠ[nhds (t i.succ)]
        fun _ ↦ (extChartAt I (p i)).symm (v i n (partitionIntervalLength t i)) := by
      simpa only [lift, partitionIntervalLength] using h
    exact h'.trans (Eventually.of_forall fun _ ↦ hval)
  let pieces (n k : Nat) : Real → M :=
    if hk : k < m then lift ⟨k, hk⟩ n else fun _ ↦ gamma b
  have hpieces_c1 (n k : Nat) :
      ContMDiff (modelWithCornersSelf Real Real) I 1 (pieces n k) := by
    by_cases hk : k < m
    · simpa only [pieces, dif_pos hk] using hlift_c1 ⟨k, hk⟩ n
    · simp only [pieces, dif_neg hk]
      exact contMDiff_const
  have hpieces_zero (n : Nat) :
      (fun _ : Real ↦ gamma a) =ᶠ[nhds (tNat 0)] pieces n 0 := by
    by_cases hm : 0 < m
    · have h := (hlift_left ⟨0, hm⟩ n).symm
      have hnode : t (⟨0, hm⟩ : Fin m).castSucc = a := by
        rw [← ht0]
        congr
      rw [htNat_zero]
      simp only [pieces, dif_pos hm]
      simpa only [hnode] using h
    · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
      have hab : a = b := by
        subst m
        simpa only [Fin.last_zero] using ht0.symm.trans htlast
      simp only [pieces, dif_neg hm]
      with_unfolding_all exact
        (Eventually.of_forall fun _ : Real ↦ congrArg gamma hab)
  have hpieces_join (n k : Nat) :
      pieces n k =ᶠ[nhds (tNat (k + 1))] pieces n (k + 1) := by
    by_cases hk : k < m
    · by_cases hks : k + 1 < m
      · let i : Fin m := ⟨k, hk⟩
        let j : Fin m := ⟨k + 1, hks⟩
        have hnode : tNat (k + 1) = t i.succ := by
          rw [htNat_of_le (Nat.le_of_lt hks)]
          congr
        have hleftNode : t j.castSucc = t i.succ := by congr
        rw [hnode]
        have hr := hlift_right i n
        have hl := hlift_left j n
        rw [hleftNode] at hl
        simpa only [pieces, dif_pos hk, dif_pos hks] using hr.trans hl.symm
      · have hkm : k + 1 = m := by omega
        let i : Fin m := ⟨k, hk⟩
        have hnode : tNat (k + 1) = b := by simpa only [hkm] using htNat_m
        have hiRight : t i.succ = b := by
          rw [← htlast]
          congr
          ext
          simpa only [i, Fin.last, hkm]
        rw [hnode]
        have hr := hlift_right i n
        rw [hiRight] at hr
        simpa only [pieces, dif_pos hk, dif_neg hks] using hr
    · have hks : ¬ k + 1 < m := by omega
      simp only [pieces, dif_neg hk, dif_neg hks, EventuallyEq.rfl]
  let alpha : Nat → Real → M := fun n ↦
    flatJoin (gamma a) tNat (pieces n) m
  have halpha_c1 (n : Nat) :
      ContMDiff (modelWithCornersSelf Real Real) I 1 (alpha n) := by
    exact flatJoin_contMDiff I (gamma a) tNat (pieces n) htNat
      (hpieces_c1 n) (hpieces_zero n) (hpieces_join n) m
  have hzero_val (n : Nat) : gamma a = pieces n 0 (tNat 0) :=
    (hpieces_zero n).eq_of_nhds
  have hnode_val (n k : Nat) :
      pieces n k (tNat (k + 1)) = pieces n (k + 1) (tNat (k + 1)) :=
    (hpieces_join n k).eq_of_nhds
  have halpha_piece (i : Fin m) (n : Nat) {s : Real}
      (hs : s ∈ Icc (t i.castSucc) (t i.succ)) :
      alpha n s = lift i n s := by
    have hti : tNat i = t i.castSucc := by
      rw [htNat_of_le (Nat.le_of_lt i.2)]
      congr
    have htis : tNat (i + 1) = t i.succ := by
      rw [htNat_of_le (Nat.succ_le_of_lt i.2)]
      congr
    have hclosed := flatJoin_closed (gamma a) tNat (pieces n) htNat
      (hzero_val n) (hnode_val n) i.2
      (show s ∈ Icc (tNat i) (tNat (i + 1)) by simpa only [hti, htis] using hs)
    simpa only [alpha, pieces, dif_pos i.2] using hclosed
  have halpha_left (n : Nat) : alpha n a = gamma a := by
    have hstable := flatJoin_stable (gamma a) tNat (pieces n) htNat
      (Nat.zero_le m) (s := a) (by rw [htNat_zero])
    simpa only [alpha, flatJoin] using hstable
  have halpha_right (n : Nat) : alpha n b = gamma b := by
    by_cases hm : 0 < m
    · let i : Fin m := ⟨m - 1, by omega⟩
      have hib : t i.succ = b := by
        rw [← htlast]
        congr
        ext
        change m - 1 + 1 = m
        omega
      have hia : t i.castSucc ≤ b := (hseg i).trans_eq hib
      have hp := halpha_piece i n (s := b) ⟨hia, hib.ge⟩
      have hr := (hlift_right i n).eq_of_nhds
      rw [hib] at hr
      exact hp.trans hr
    · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
      have hab : a = b := by
        subst m
        simpa only [Fin.last_zero] using ht0.symm.trans htlast
      rw [← hab, halpha_left]
  have halpha_rep (i : Fin m) (n : Nat) : EqOn (v i n)
      (fun r ↦ extChartAt I (p i) (alpha n (t i.castSucc + r)))
      (Icc (0 : Real) (partitionIntervalLength t i)) := by
    intro r hr
    have hs : t i.castSucc + r ∈ Icc (t i.castSucc) (t i.succ) := by
      constructor
      · linarith [hr.1]
      · have hr' := hr.2
        rw [partitionIntervalLength] at hr'
        linarith
    change v i n r = extChartAt I (p i) (alpha n (t i.castSucc + r))
    rw [halpha_piece i n hs]
    have hcoord := chartLift_coord I (p i)
      (fun s ↦ v i n (s - t i.castSucc)) (hmaps i n) hs
    simpa only [Function.comp_apply, sub_self, add_sub_cancel_left] using hcoord.symm
  have halpha_source (i : Fin m) (n : Nat) : MapsTo (alpha n)
      (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source := by
    intro s hs
    have htarget := hmaps i n hs
    have hin := (extChartAt I (p i)).map_target htarget
    have hlift : lift i n s = (extChartAt I (p i)).symm
        (v i n (s - t i.castSucc)) := by
      simp only [lift, chartFlatLift, Function.comp_apply,
        flatExtend_of_mem (fun q ↦ v i n (q - t i.castSucc)) hs]
    rw [halpha_piece i n hs, hlift]
    simpa only [extChartAt_source] using hin
  have hinv_uniform (i : Fin m) : TendstoUniformly
      (fun n (r : Icc (0 : Real) (partitionIntervalLength t i)) ↦
        (extChartAt I (p i)).symm (v i n r.1))
      (fun r ↦ gamma (t i.castSucc + r.1)) atTop := by
    have hcont : ContinuousOn (extChartAt I (p i)).symm (K i) :=
      (continuousOn_extChartAt_symm (I := I) (p i)).mono (hKtar i)
    have huc := (hKc i).uniformContinuousOn_of_continuous hcont
    have hcomp := huc.comp_tendstoUniformly (hvK i) (huLimK i) (hvlim i)
    intro U hU
    filter_upwards [hcomp U hU] with n hn
    intro r
    simpa only [hlim_lift i r] using hn r
  have halpha_uniform : TendstoUniformly
      (fun n (s : Icc a b) ↦ alpha n s.1)
      (fun s ↦ gamma s.1) atTop := by
    by_cases hm : 0 < m
    · intro U hU
      have hall : ∀ᶠ n in atTop, ∀ i : Fin m,
          ∀ r : Icc (0 : Real) (partitionIntervalLength t i),
            (gamma (t i.castSucc + r.1),
              (extChartAt I (p i)).symm (v i n r.1)) ∈ U := by
        exact Filter.eventually_all.mpr fun i ↦ hinv_uniform i U hU
      filter_upwards [hall] with n hn
      intro s
      obtain ⟨i, hs⟩ := exists_fin_segment hm t htmono ht0 htlast s.2
      let r : Icc (0 : Real) (partitionIntervalLength t i) :=
        ⟨s.1 - t i.castSucc, by
          constructor
          · linarith [hs.1]
          · simpa only [partitionIntervalLength] using sub_le_sub_right hs.2 (t i.castSucc)⟩
      have hpiece := halpha_piece i n hs
      have hlift : lift i n s.1 = (extChartAt I (p i)).symm (v i n r.1) := by
        simp only [lift, chartFlatLift, Function.comp_apply,
          flatExtend_of_mem (fun q ↦ v i n (q - t i.castSucc)) hs]
        congr 2
      have htime : t i.castSucc + r.1 = s.1 := by
        simp only [r]
        ring
      rw [hpiece, hlift, ← htime]
      exact hn i r
    · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
      have hab : a = b := by
        subst m
        simpa only [Fin.last_zero] using ht0.symm.trans htlast
      intro U hU
      filter_upwards [] with n
      intro s
      have hsval : s.1 = a := le_antisymm (hab ▸ s.2.2) s.2.1
      rw [hsval, halpha_left]
      exact refl_mem_uniformity hU
  exact ⟨alpha, halpha_c1, halpha_left, halpha_right, halpha_rep,
    halpha_source, halpha_uniform⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
