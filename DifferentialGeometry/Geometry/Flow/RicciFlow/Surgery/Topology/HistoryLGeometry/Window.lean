import DifferentialGeometry.Analysis.Calculus.Manifold.AbsolutelyContinuous
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction.AbsoluteContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurvivorMetricSeam
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Topology Manifold ContDiff BigOperators

private theorem absolutelyContinuousOnInterval_same {X : Type*} [PseudoMetricSpace X]
    (f : ℝ → X) (t : ℝ) : AbsolutelyContinuousOnInterval f t t := by
  apply LipschitzOnWith.absolutelyContinuousOnInterval (K := 0)
  intro x hx y hy
  rw [uIcc_self, mem_singleton_iff] at hx hy
  simp [hx, hy]

theorem AbsolutelyContinuousOnInterval.of_forall_nhds {X : Type*} [PseudoMetricSpace X]
    {f : ℝ → X} {c d : ℝ} (hcd : c ≤ d)
    (h : ∀ t ∈ Icc c d, ∃ U ∈ 𝓝 t, ∀ x y, x ≤ y → Icc x y ⊆ U → Icc x y ⊆ Icc c d →
      AbsolutelyContinuousOnInterval f x y) :
    AbsolutelyContinuousOnInterval f c d := by
  choose U hU hP using h
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (isCompact_Icc (a := c) (b := d))
    (c := fun t : Icc c d => interior (U t.1 t.2)) (fun _ => isOpen_interior)
    (fun t ht => mem_iUnion.2 ⟨⟨t, ht⟩, mem_interior_iff_mem_nhds.2 (hU t ht)⟩)
  obtain ⟨N, hN⟩ := exists_nat_gt ((d - c) / δ)
  have hNpos : (0 : ℝ) < N := (div_nonneg (sub_nonneg.2 hcd) hδ.le).trans_lt hN
  set w := (d - c) / N with hw
  have hw0 : 0 ≤ w := div_nonneg (sub_nonneg.2 hcd) hNpos.le
  have hwδ : w < δ := by
    rw [hw, div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hδ] at hN
    linarith
  have hend : c + N * w = d := by
    rw [hw]
    field_simp
    ring
  have hstep : ∀ k : ℕ, k < N →
      AbsolutelyContinuousOnInterval f (c + k * w) (c + (k + 1) * w) := by
    intro k hk
    have hk' : ((k : ℝ) + 1) ≤ N := by exact_mod_cast hk
    have hkw : ((k : ℝ) + 1) * w ≤ N * w := mul_le_mul_of_nonneg_right hk' hw0
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hx : c + k * w ∈ Icc c d := ⟨by nlinarith, by nlinarith⟩
    obtain ⟨i, hi⟩ := hball _ hx
    apply hP i.1 i.2 _ _ (by nlinarith)
    · intro y hy
      apply interior_subset
      apply hi
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> nlinarith [hy.1, hy.2]
    · intro y hy
      exact ⟨by nlinarith [hy.1], by nlinarith [hy.2]⟩
  have hall : ∀ k : ℕ, k ≤ N → AbsolutelyContinuousOnInterval f c (c + k * w) := by
    intro k
    induction k with
    | zero =>
      intro _
      simpa only [Nat.cast_zero, zero_mul, add_zero] using absolutelyContinuousOnInterval_same f c
    | succ k ih =>
      intro hk
      have hk' : k < N := hk
      have hj := AbsolutelyContinuousOnInterval.piecewise_Iic
        (by nlinarith [Nat.cast_nonneg (α := ℝ) k] : c ≤ c + k * w)
        (by nlinarith : c + k * w ≤ c + (k + 1) * w) (ih hk'.le) (hstep k hk') rfl
      rw [piecewise_same] at hj
      simpa only [Nat.cast_succ] using hj
  simpa only [hend] using hall N le_rfl

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

private theorem absolutelyContinuousOnInterval_same (γ : ℝ → M) (t : ℝ) :
    absolutelyContinuousOnInterval I γ t t := by
  refine ⟨by rw [uIcc_self]; exact continuousOn_singleton _ _, fun p c d hsub _ => ?_⟩
  have hc : c = t := by simpa using hsub left_mem_uIcc
  have hd : d = t := by simpa using hsub right_mem_uIcc
  subst hc hd
  apply LipschitzOnWith.absolutelyContinuousOnInterval (K := 0)
  intro x hx y hy
  rw [uIcc_self, mem_singleton_iff] at hx hy
  simp [hx, hy]

theorem absolutelyContinuousOnInterval_of_forall_left_right {γ : ℝ → M} {c d : ℝ}
    (hcd : c ≤ d)
    (hleft : ∀ t ∈ Ioc c d, ∃ s < t, absolutelyContinuousOnInterval I γ s t)
    (hright : ∀ t ∈ Ico c d, ∃ s, t < s ∧ absolutelyContinuousOnInterval I γ t s) :
    absolutelyContinuousOnInterval I γ c d := by
  have hL : ∀ t ∈ Icc c d, ∃ s < t, ∀ x y, s ≤ x → y ≤ t → x ≤ y → c ≤ x →
      absolutelyContinuousOnInterval I γ x y := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · refine ⟨t - 1, by linarith, fun x y _ hy hxy hx => ?_⟩
      have hxy' : x = y := by linarith
      subst hxy'
      exact absolutelyContinuousOnInterval_same γ x
    · obtain ⟨s, hs, hac⟩ := hleft t ⟨h, ht.2⟩
      refine ⟨s, hs, fun x y hx hy hxy _ => absolutelyContinuousOnInterval_mono hac ?_⟩
      rw [uIcc_of_le hxy, uIcc_of_le hs.le]
      exact Icc_subset_Icc hx hy
  have hR : ∀ t ∈ Icc c d, ∃ s, t < s ∧ ∀ x y, t ≤ x → y ≤ s → x ≤ y → y ≤ d →
      absolutelyContinuousOnInterval I γ x y := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with h | h
    · refine ⟨t + 1, by linarith, fun x y hx _ hxy hy => ?_⟩
      have hxy' : x = y := by linarith
      subst hxy'
      exact absolutelyContinuousOnInterval_same γ x
    · obtain ⟨s, hs, hac⟩ := hright t ⟨ht.1, h⟩
      refine ⟨s, hs, fun x y hx hy hxy _ => absolutelyContinuousOnInterval_mono hac ?_⟩
      rw [uIcc_of_le hxy, uIcc_of_le hs.le]
      exact Icc_subset_Icc hx hy
  choose sL hsL hPL using hL
  choose sR hsR hPR using hR
  refine ⟨?_, fun p c' d' hsub hsrc => ?_⟩
  · rw [uIcc_of_le hcd]
    intro t ht
    have hl : ContinuousWithinAt γ (Icc c t) t := by
      have hle := max_le (hsL t ht).le ht.1
      have hac := hPL t ht (max (sL t ht) c) t (le_max_left _ _) le_rfl hle (le_max_right _ _)
      have hc := hac.1 t (by rw [uIcc_of_le hle]; exact ⟨hle, le_rfl⟩)
      rw [uIcc_of_le hle] at hc
      exact hc.mono_of_mem_nhdsWithin (mem_nhdsWithin.2 ⟨Ioi (sL t ht), isOpen_Ioi,
        hsL t ht, fun y hy => ⟨max_le hy.1.le hy.2.1, hy.2.2⟩⟩)
    have hr : ContinuousWithinAt γ (Icc t d) t := by
      have hle := le_min (hsR t ht).le ht.2
      have hac := hPR t ht t (min (sR t ht) d) le_rfl (min_le_left _ _) hle (min_le_right _ _)
      have hc := hac.1 t (by rw [uIcc_of_le hle]; exact ⟨le_rfl, hle⟩)
      rw [uIcc_of_le hle] at hc
      exact hc.mono_of_mem_nhdsWithin (mem_nhdsWithin.2 ⟨Iio (sR t ht), isOpen_Iio,
        hsR t ht, fun y hy => ⟨hy.2.1, le_min hy.1.le hy.2.2⟩⟩)
    have hu := hl.union hr
    rwa [Icc_union_Icc_eq_Icc ht.1 ht.2] at hu
  have hmain : ∀ c' d', c' ≤ d' → Icc c' d' ⊆ Icc c d →
      MapsTo γ (Icc c' d') (chartAt H p).source →
      AbsolutelyContinuousOnInterval ((extChartAt I p) ∘ γ) c' d' := by
    intro c' d' hcd' hsub' hsrc'
    have heuc : ∀ x y, x ≤ y → Icc x y ⊆ Icc c' d' →
        absolutelyContinuousOnInterval I γ x y →
        AbsolutelyContinuousOnInterval ((extChartAt I p) ∘ γ) x y := by
      intro x y hxy hxy' hac
      exact hac.2 p x y subset_rfl (by rw [uIcc_of_le hxy]; exact hsrc'.mono_left hxy')
    apply AbsolutelyContinuousOnInterval.of_forall_nhds hcd'
    intro t ht
    have htc := hsub' ht
    refine ⟨Ioo (sL t htc) (sR t htc), Ioo_mem_nhds (hsL t htc) (hsR t htc),
      fun x y hxy hU hI => ?_⟩
    have hx : x ∈ Icc x y := left_mem_Icc.2 hxy
    have hy : y ∈ Icc x y := right_mem_Icc.2 hxy
    have hxc : c ≤ x := (hsub' (hI hx)).1
    have hyd : y ≤ d := (hsub' (hI hy)).2
    by_cases hyt : y ≤ t
    · exact heuc x y hxy hI (hPL t htc x y (hU hx).1.le hyt hxy hxc)
    by_cases htx : t ≤ x
    · exact heuc x y hxy hI (hPR t htc x y htx (hU hy).2.le hxy hyd)
    rw [not_le] at hyt htx
    have h1 := heuc x t htx.le (fun r hr => hI ⟨hr.1, hr.2.trans hyt.le⟩)
      (hPL t htc x t (hU hx).1.le le_rfl htx.le hxc)
    have h2 := heuc t y hyt.le (fun r hr => hI ⟨htx.le.trans hr.1, hr.2⟩)
      (hPR t htc t y le_rfl (hU hy).2.le hyt.le hyd)
    have hj := AbsolutelyContinuousOnInterval.piecewise_Iic htx.le hyt.le h1 h2 rfl
    rwa [piecewise_same] at hj
  rcases le_total c' d' with h | h
  · exact hmain c' d' h (by rw [← uIcc_of_le h, ← uIcc_of_le hcd]; exact hsub)
      (by rw [← uIcc_of_le h]; exact hsrc)
  · exact (hmain d' c' h (by rw [← uIcc_of_le h, ← uIcc_of_le hcd, uIcc_comm]; exact hsub)
      (by rw [← uIcc_of_le h, uIcc_comm]; exact hsrc)).symm

theorem absolutelyContinuousOnInterval_of_subset_iUnion_Icc {ι : Type*} [Finite ι]
    (l r : ι → ℝ) {γ : ℝ → M} {c d : ℝ} (hcd : c ≤ d)
    (hcover : Icc c d ⊆ ⋃ j, Icc (l j) (r j))
    (hac : ∀ j, absolutelyContinuousOnInterval I γ (l j) (r j)) :
    absolutelyContinuousOnInterval I γ c d := by
  classical
  apply absolutelyContinuousOnInterval_of_forall_left_right hcd
  · intro t ht
    let A : ι → Set ℝ := fun j => if r j < t then Icc (l j) (r j) else ∅
    have hA : IsClosed (⋃ j, A j) := isClosed_iUnion_of_finite (fun j => by
      simp only [A]
      split_ifs
      exacts [isClosed_Icc, isClosed_empty])
    have htA : t ∉ ⋃ j, A j := by
      simp only [A, mem_iUnion]
      rintro ⟨j, hj⟩
      split_ifs at hj with h
      exacts [(not_le.2 h) hj.2, hj]
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hA.isOpen_compl t htA
    set s := max c (t - ε / 2)
    have hst : s < t := max_lt ht.1 (by linarith)
    have hs : s ∈ Icc c d := ⟨le_max_left _ _, hst.le.trans ht.2⟩
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hcover hs)
    have hrt : t ≤ r j := by
      by_contra h
      apply hball (show s ∈ Metric.ball t ε from ?_)
      · exact mem_iUnion.2 ⟨j, by simp only [A, if_pos (not_le.1 h)]; exact hj⟩
      · rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [le_max_right c (t - ε / 2)]
    refine ⟨s, hst, absolutelyContinuousOnInterval_mono (hac j) ?_⟩
    rw [uIcc_of_le hst.le, uIcc_of_le (hj.1.trans (hst.le.trans hrt))]
    exact Icc_subset_Icc hj.1 hrt
  · intro t ht
    let A : ι → Set ℝ := fun j => if t < l j then Icc (l j) (r j) else ∅
    have hA : IsClosed (⋃ j, A j) := isClosed_iUnion_of_finite (fun j => by
      simp only [A]
      split_ifs
      exacts [isClosed_Icc, isClosed_empty])
    have htA : t ∉ ⋃ j, A j := by
      simp only [A, mem_iUnion]
      rintro ⟨j, hj⟩
      split_ifs at hj with h
      exacts [(not_le.2 h) hj.1, hj]
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hA.isOpen_compl t htA
    set s := min d (t + ε / 2)
    have hst : t < s := lt_min ht.2 (by linarith)
    have hs : s ∈ Icc c d := ⟨ht.1.trans hst.le, min_le_left _ _⟩
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hcover hs)
    have hlt : l j ≤ t := by
      by_contra h
      apply hball (show s ∈ Metric.ball t ε from ?_)
      · exact mem_iUnion.2 ⟨j, by simp only [A, if_pos (not_le.1 h)]; exact hj⟩
      · rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [min_le_right d (t + ε / 2)]
    refine ⟨s, hst, absolutelyContinuousOnInterval_mono (hac j) ?_⟩
    rw [uIcc_of_le hst.le, uIcc_of_le (hlt.trans (hst.le.trans hj.2))]
    exact Icc_subset_Icc hlt hj.2

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

theorem absolutelyContinuousOnInterval_comp_of_contMDiffOn [I.Boundaryless]
    [IsManifold I 1 M] [IsManifold J 1 N] {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I J 1 f U) {γ : ℝ → M} {a b : ℝ}
    (hγ : absolutelyContinuousOnInterval I γ a b) (hmaps : MapsTo γ (uIcc a b) U) :
    absolutelyContinuousOnInterval J (f ∘ γ) a b := by
  refine ⟨hf.continuousOn.comp hγ.1 hmaps, fun p c d hsub hsrc => ?_⟩
  have hmain : ∀ c d, c ≤ d → uIcc c d ⊆ uIcc a b →
      MapsTo (f ∘ γ) (Icc c d) (chartAt G p).source →
      AbsolutelyContinuousOnInterval ((extChartAt J p) ∘ f ∘ γ) c d := by
    intro c d hcd hsub hsrc
    apply AbsolutelyContinuousOnInterval.of_forall_nhds hcd
    intro t ht
    have htab : t ∈ uIcc a b := hsub (by rw [uIcc_of_le hcd]; exact ht)
    have hfq : ContMDiffAt I J 1 f (γ t) := hf.contMDiffAt (hU.mem_nhds (hmaps htab))
    have hsm := (contMDiffAt_iff_of_mem_source (mem_chart_source H (γ t)) (hsrc ht)).1 hfq
    rw [I.range_eq_univ, contDiffWithinAt_univ] at hsm
    obtain ⟨K, V, hV, hLip⟩ := hsm.2.exists_lipschitzOnWith
    have hS : (chartAt H (γ t)).source ∩ extChartAt I (γ t) ⁻¹' V ∈ 𝓝 (γ t) :=
      inter_mem ((chartAt H (γ t)).open_source.mem_nhds (mem_chart_source H (γ t)))
        ((continuousAt_extChartAt (γ t)).preimage_mem_nhds hV)
    have hcw : ContinuousWithinAt γ (Icc c d) t :=
      (hγ.1 t htab).mono (by rw [← uIcc_of_le hcd]; exact hsub)
    obtain ⟨W, hW, hWsub⟩ :=
      mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (hcw.preimage_mem_nhdsWithin hS)
    refine ⟨W, hW, fun x y hxy hxW hxI => ?_⟩
    have hmapsW : MapsTo γ (uIcc x y)
        ((chartAt H (γ t)).source ∩ extChartAt I (γ t) ⁻¹' V) := by
      rw [uIcc_of_le hxy]
      exact fun r hr => hWsub ⟨hxW hr, hxI hr⟩
    have hsubxy : uIcc x y ⊆ uIcc a b := by
      rw [uIcc_of_le hxy]
      exact hxI.trans (by rw [← uIcc_of_le hcd]; exact hsub)
    have hac := hγ.2 (γ t) x y hsubxy (fun r hr => (hmapsW hr).1)
    have hcomp := hLip.comp_absolutelyContinuousOnInterval hac (fun r hr => (hmapsW hr).2)
    apply AbsolutelyContinuousOnInterval.congr hcomp
    intro r hr
    have hsrc' : γ r ∈ (extChartAt I (γ t)).source := by
      rw [extChartAt_source]
      exact (hmapsW hr).1
    simp only [Function.comp_apply, (extChartAt I (γ t)).left_inv hsrc']
  rcases le_total c d with h | h
  · exact hmain c d h hsub (by rw [← uIcc_of_le h]; exact hsrc)
  · exact (hmain d c h (by rw [uIcc_comm]; exact hsub)
      (by rw [← uIcc_of_le h, uIcc_comm]; exact hsrc)).symm

end Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u v
variable (H : ObservedHistory.{u})

structure LWindow (lo hi : Fin (H.eventCount + 1)) (T : ℝ) where
  X : Type u
  [top : TopologicalSpace X]
  [charts : ChartedSpace ThreeSpace X]
  [smooth : IsManifold ThreeModel ∞ X]
  [t2 : T2Space X]
  [sigma : SigmaCompactSpace X]
  a : ℝ
  b : ℝ
  nonneg : 0 ≤ a
  lt : a < b
  le : lo ≤ hi
  upper : T - a ^ 2 ∈ H.stageDomain hi
  lower : T - b ^ 2 ∈ H.stageDomain lo
  D : RealTimeInterval
  S : SolutionOn (I := ThreeModel) (M := X) D
  solution : IsSolutionOn S
  regular : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular
  f : (j : H.StageInterval lo hi) → X → (H.stage j.val).Carrier
  localDiffeomorph : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j)
  injective : ∀ j, Function.Injective (f j)
  crossing : ∀ (i : Fin H.eventCount) (hl : lo ≤ i.castSucc) (hh : i.succ ≤ hi) (z : X),
    (H.event i).RegularCrossing (f ⟨i.castSucc, hl, i.castSucc_lt_succ.le.trans hh⟩ z)
      (f ⟨i.succ, hl.trans i.castSucc_lt_succ.le, hh⟩ z)
  metric : ∀ j : H.StageInterval lo hi,
    ∀ s ∈ Ioo (H.regularizedStageStart T a j.val) (H.regularizedStageEnd T b j.val),
      S.base.metric (T - s ^ 2) =
        localPullMetric (H.stageMetric j.val (T - s ^ 2)) (f j) (localDiffeomorph j)

attribute [instance] LWindow.top LWindow.charts LWindow.smooth LWindow.t2 LWindow.sigma

variable {H}

theorem regularizedStageStart_le_of_le {T a a' : ℝ} (ha : 0 ≤ a) (haa' : a ≤ a')
    (j : Fin (H.eventCount + 1)) :
    H.regularizedStageStart T a j ≤ H.regularizedStageStart T a' j := by
  apply Real.sqrt_le_sqrt
  apply sub_le_sub_left
  apply min_le_min_right
  exact sub_le_sub_left (pow_le_pow_left₀ ha haa' 2) T

theorem regularizedStageEnd_le_of_le {T b b' : ℝ} (hb : 0 ≤ b') (hbb' : b' ≤ b)
    (j : Fin (H.eventCount + 1)) :
    H.regularizedStageEnd T b' j ≤ H.regularizedStageEnd T b j := by
  apply Real.sqrt_le_sqrt
  apply sub_le_sub_left
  apply max_le_max_right
  exact sub_le_sub_left (pow_le_pow_left₀ hb hbb' 2) T

private theorem sum_stageInterval_upper {A : Type v} [AddCommMonoid A]
    {first last k : Fin (H.eventCount + 1)} (hfk : first ≤ k)
    (G : H.StageInterval first last → A) (F : H.StageInterval k last → A)
    (hGF : ∀ j (h : k ≤ j.val), G j = F ⟨j.val, h, j.property.2⟩) :
    ∑ j : H.StageInterval first last, (if k ≤ j.val then G j else 0) =
      ∑ j : H.StageInterval k last, F j := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype (fun j : H.StageInterval first last => k ≤ j.val)]
  have hz : (∑ j : {j : H.StageInterval first last // ¬ k ≤ j.val},
      (if k ≤ j.val.val then G j.val else 0)) = 0 :=
    Finset.sum_eq_zero (fun j _ => if_neg j.property)
  rw [hz, add_zero]
  exact Fintype.sum_equiv
    { toFun := fun j => ⟨j.val.val, j.property, j.val.property.2⟩
      invFun := fun j => ⟨⟨j.val, hfk.trans j.property.1, j.property.2⟩, j.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } _ _
    (fun j => (if_pos j.property).trans (hGF j.val j.property))

private theorem sum_stageInterval_lower {A : Type v} [AddCommMonoid A]
    {first last k : Fin (H.eventCount + 1)} (hkl : k ≤ last)
    (G : H.StageInterval first last → A) (F : H.StageInterval first k → A)
    (hGF : ∀ j (h : j.val ≤ k), G j = F ⟨j.val, j.property.1, h⟩) :
    ∑ j : H.StageInterval first last, (if j.val ≤ k then G j else 0) =
      ∑ j : H.StageInterval first k, F j := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype (fun j : H.StageInterval first last => j.val ≤ k)]
  have hz : (∑ j : {j : H.StageInterval first last // ¬ j.val ≤ k},
      (if j.val.val ≤ k then G j.val else 0)) = 0 :=
    Finset.sum_eq_zero (fun j _ => if_neg j.property)
  rw [hz, add_zero]
  exact Fintype.sum_equiv
    { toFun := fun j => ⟨j.val.val, j.val.property.1, j.property⟩
      invFun := fun j => ⟨⟨j.val, j.property.1, j.property.2.trans hkl⟩, j.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } _ _
    (fun j => (if_pos j.property).trans (hGF j.val j.property))

theorem stageEndTime_le_time_of_lt {k j : Fin (H.eventCount + 1)} (h : k < j) :
    H.stageEndTime k ≤ H.time j := by
  cases k using Fin.lastCases with
  | last => exact absurd h (not_lt.2 (Fin.le_last j))
  | cast i =>
    rw [H.stageEndTime_castSucc]
    exact H.time_strictMono.monotone (Fin.castSucc_lt_iff_succ_le.1 h)

theorem regularizedStageEnd_eq_of_lt {k j : Fin (H.eventCount + 1)} {T c v : ℝ}
    (hc : T - c ^ 2 ∈ H.stageDomain k) (hkj : k < j) (hcv : c ^ 2 ≤ v ^ 2) :
    H.regularizedStageEnd T c j = H.regularizedStageEnd T v j := by
  have h := (H.le_stageEndTime_of_mem_stageDomain hc).trans (H.stageEndTime_le_time_of_lt hkj)
  simp only [regularizedStageEnd, max_eq_right h, max_eq_right ((sub_le_sub_left hcv T).trans h)]

theorem regularizedStageStart_eq_of_lt {k j : Fin (H.eventCount + 1)} {T u c : ℝ}
    (hc : T - c ^ 2 ∈ H.stageDomain k) (hjk : j < k) (huc : u ^ 2 ≤ c ^ 2) :
    H.regularizedStageStart T c j = H.regularizedStageStart T u j := by
  have h := (H.stageEndTime_le_time_of_lt hjk).trans (H.time_le_of_mem_stageDomain hc)
  simp only [regularizedStageStart, min_eq_right h, min_eq_right (h.trans (sub_le_sub_left huc T))]

private theorem stageExtendedAction_split (j k : Fin (H.eventCount + 1)) {T B u v c : ℝ}
    (hu : 0 ≤ u) (huc : u ≤ c) (hcv : c ≤ v) (hc : T - c ^ 2 ∈ H.stageDomain k)
    (α : ℝ → (H.stage j).Carrier)
    (hα : j = k → Manifold.absolutelyContinuousOnInterval ThreeModel α
      (H.regularizedStageStart T u j) (H.regularizedStageEnd T v j))
    (hscalar : j = k → ∀ t ∈ Ioo (H.regularizedStageStart T u j) (H.regularizedStageEnd T v j),
      ∀ x : (H.stage j).Carrier, -B ≤ metricScalarAt (H.stageMetric j (T - t ^ 2)) x) :
    H.stageRegularizedExtendedAction j T B α
        (H.regularizedStageStart T u j) (H.regularizedStageEnd T v j) =
      (if k ≤ j then H.stageRegularizedExtendedAction j T B α
        (H.regularizedStageStart T u j) (H.regularizedStageEnd T c j) else 0) +
      (if j ≤ k then H.stageRegularizedExtendedAction j T B α
        (H.regularizedStageStart T c j) (H.regularizedStageEnd T v j) else 0) := by
  have hc0 : 0 ≤ c := hu.trans huc
  rcases lt_trichotomy j k with hjk | rfl | hkj
  · rw [if_neg (not_le.2 hjk), if_pos hjk.le, zero_add,
      H.regularizedStageStart_eq_of_lt hc hjk (pow_le_pow_left₀ hu huc 2)]
  · rw [if_pos le_rfl, if_pos le_rfl, H.regularizedStageEnd_eq_of_mem_stageDomain hc0 hc,
      H.regularizedStageStart_eq_of_mem_Icc hc0
        ⟨H.time_le_of_mem_stageDomain hc, H.le_stageEndTime_of_mem_stageDomain hc⟩]
    apply H.stageRegularizedExtendedAction_add_of_absolutelyContinuousOnInterval j T B u v c α
    · rw [← H.regularizedStageStart_eq_of_mem_Icc hc0
        ⟨H.time_le_of_mem_stageDomain hc, H.le_stageEndTime_of_mem_stageDomain hc⟩]
      exact regularizedStageStart_le_of_le hu huc j
    · rw [← H.regularizedStageEnd_eq_of_mem_stageDomain hc0 hc]
      exact regularizedStageEnd_le_of_le hc0 hcv j
    · exact hα rfl
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact hscalar rfl t ht (α t)
  · rw [if_pos hkj.le, if_neg (not_le.2 hkj), add_zero,
      H.regularizedStageEnd_eq_of_lt hc hkj (pow_le_pow_left₀ (hu.trans huc) hcv 2)]

variable (H)

variable {H} in
theorem regularizedExtendedAction_eq_add_at_parameter {first last : Fin (H.eventCount + 1)}
    (k : Fin (H.eventCount + 1)) (hfk : first ≤ k) (hkl : k ≤ last) {T B u v c : ℝ}
    (hu : 0 ≤ u) (huc : u ≤ c) (hcv : c ≤ v) (hc : T - c ^ 2 ∈ H.stageDomain k)
    (hscalar : ∀ t ∈ Ioo (H.regularizedStageStart T u k) (H.regularizedStageEnd T v k),
      ∀ x : (H.stage k).Carrier, -B ≤ metricScalarAt (H.stageMetric k (T - t ^ 2)) x)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) :
    H.regularizedExtendedAction first last T B u v α =
      H.regularizedExtendedAction k last T B u c
          (fun j => α ⟨j.val, hfk.trans j.property.1, j.property.2⟩) +
        H.regularizedExtendedAction first k T B c v
          (fun j => α ⟨j.val, j.property.1, j.property.2.trans hkl⟩) := by
  classical
  rw [regularizedExtendedAction, regularizedExtendedAction, regularizedExtendedAction,
    ← H.sum_stageInterval_upper hfk (fun j => H.stageRegularizedExtendedAction j.val T B (α j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T c j.val)) _ (fun _ _ => rfl),
    ← H.sum_stageInterval_lower hkl (fun j => H.stageRegularizedExtendedAction j.val T B (α j)
      (H.regularizedStageStart T c j.val) (H.regularizedStageEnd T v j.val)) _ (fun _ _ => rfl),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine H.stageExtendedAction_split j.val k hu huc hcv hc (α j) (fun _ => hα j) (fun h => ?_)
  obtain ⟨jv, hj1, hj2⟩ := j
  change jv = k at h
  subst h
  exact hscalar

variable {H} in
theorem mem_regularizedActionValues_upper_restrict {first last : Fin (H.eventCount + 1)}
    (k : Fin (H.eventCount + 1)) (hfk : first ≤ k) (hkl : k ≤ last) {T B u v c : ℝ}
    (hu : 0 ≤ u) (huc : u ≤ c) (hcv : c ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first) (hc : T - c ^ 2 ∈ H.stageDomain k)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hnode : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ))) :
    H.regularizedExtendedAction k last T B u c
        (fun j => α ⟨j.val, hfk.trans j.property.1, j.property.2⟩) ∈
      H.regularizedActionValues k last hkl T B u c (α ⟨last, hfk.trans hkl, le_rfl⟩ u)
        (α ⟨k, hfk, hkl⟩ c) := by
  refine ⟨hu, huc, hupper, hc, _, fun j => ?_, rfl, rfl,
    fun i hl hh => hnode i (hfk.trans hl) hh, rfl⟩
  have hb := H.regularizedStage_bounds hu huc hupper hc j
  apply Manifold.absolutelyContinuousOnInterval_mono (hα _)
  rw [uIcc_of_le hb.2.1, uIcc_of_le (H.regularizedStage_bounds hu (huc.trans hcv) hupper hlower
    ⟨j.val, hfk.trans j.property.1, j.property.2⟩).2.1]
  exact Icc_subset_Icc le_rfl (regularizedStageEnd_le_of_le (hu.trans huc) hcv j.val)

variable {H} in
theorem mem_regularizedActionValues_lower_restrict {first last : Fin (H.eventCount + 1)}
    (k : Fin (H.eventCount + 1)) (hfk : first ≤ k) (hkl : k ≤ last) {T B u v c : ℝ}
    (hu : 0 ≤ u) (huc : u ≤ c) (hcv : c ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first) (hc : T - c ^ 2 ∈ H.stageDomain k)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hnode : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ))) :
    H.regularizedExtendedAction first k T B c v
        (fun j => α ⟨j.val, j.property.1, j.property.2.trans hkl⟩) ∈
      H.regularizedActionValues first k hfk T B c v (α ⟨k, hfk, hkl⟩ c)
        (α ⟨first, le_rfl, hfk.trans hkl⟩ v) := by
  have hc0 : 0 ≤ c := hu.trans huc
  have hcIcc : T - c ^ 2 ∈ Icc (H.time k) (H.stageEndTime k) :=
    ⟨H.time_le_of_mem_stageDomain hc, H.le_stageEndTime_of_mem_stageDomain hc⟩
  refine ⟨hc0, hcv, hcIcc, hlower, _, fun j => ?_, rfl, rfl,
    fun i hl hh => hnode i hl (hh.trans hkl), rfl⟩
  have hb := H.regularizedStage_bounds hc0 hcv hcIcc hlower j
  apply Manifold.absolutelyContinuousOnInterval_mono (hα _)
  rw [uIcc_of_le hb.2.1, uIcc_of_le (H.regularizedStage_bounds hu (huc.trans hcv) hupper hlower
    ⟨j.val, j.property.1, j.property.2.trans hkl⟩).2.1]
  exact Icc_subset_Icc (regularizedStageStart_le_of_le hu huc j.val) le_rfl

private theorem split_parameter_forward {first last : Fin (H.eventCount + 1)} (hle : first ≤ last)
    (k : Fin (H.eventCount + 1)) (hfk : first ≤ k) (hkl : k ≤ last) {T B u v c : ℝ}
    {A : WithTop ℝ} (hu : 0 ≤ u) (huc : u ≤ c) (hcv : c ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first) (hc : T - c ^ 2 ∈ H.stageDomain k)
    (hscalar : ∀ t ∈ Ioo (H.regularizedStageStart T u k) (H.regularizedStageEnd T v k),
      ∀ x : (H.stage k).Carrier, -B ≤ metricScalarAt (H.stageMetric k (T - t ^ 2)) x)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier)
    (hA : A ∈ H.regularizedActionValues first last hle T B u v p q) :
    ∃ x : (H.stage k).Carrier, ∃ A₁ A₂ : WithTop ℝ,
      A₁ ∈ H.regularizedActionValues k last hkl T B u c p x ∧
      A₂ ∈ H.regularizedActionValues first k hfk T B c v x q ∧ A₁ + A₂ = A := by
  rcases hA with ⟨_, _, _, _, α, hα, rfl, rfl, hnode, rfl⟩
  exact ⟨_, _, _, mem_regularizedActionValues_upper_restrict k hfk hkl hu huc hcv hupper hlower
      hc α hα hnode, mem_regularizedActionValues_lower_restrict k hfk hkl hu huc hcv hupper
      hlower hc α hα hnode,
    (regularizedExtendedAction_eq_add_at_parameter k hfk hkl hu huc hcv hc hscalar α hα).symm⟩

private theorem split_parameter_backward {first last : Fin (H.eventCount + 1)}
    (hle : first ≤ last) (k : Fin (H.eventCount + 1)) (hfk : first ≤ k) (hkl : k ≤ last)
    {T B u v c : ℝ} {A : WithTop ℝ} (hu : 0 ≤ u) (huc : u ≤ c) (hcv : c ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first) (hc : T - c ^ 2 ∈ H.stageDomain k)
    (hscalar : ∀ t ∈ Ioo (H.regularizedStageStart T u k) (H.regularizedStageEnd T v k),
      ∀ x : (H.stage k).Carrier, -B ≤ metricScalarAt (H.stageMetric k (T - t ^ 2)) x)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier)
    (hsplit : ∃ x : (H.stage k).Carrier, ∃ A₁ A₂ : WithTop ℝ,
      A₁ ∈ H.regularizedActionValues k last hkl T B u c p x ∧
      A₂ ∈ H.regularizedActionValues first k hfk T B c v x q ∧ A₁ + A₂ = A) :
    A ∈ H.regularizedActionValues first last hle T B u v p q := by
  classical
  obtain ⟨x, A₁, A₂, ⟨_, _, _, _, α₁, hα₁, hp₁, hx₁, hn₁, hs₁⟩,
    ⟨_, _, _, _, α₂, hα₂, hx₂, hq₂, hn₂, hs₂⟩, hsum⟩ := hsplit
  have hc0 : 0 ≤ c := hu.trans huc
  have hcIcc : T - c ^ 2 ∈ Icc (H.time k) (H.stageEndTime k) :=
    ⟨H.time_le_of_mem_stageDomain hc, H.le_stageEndTime_of_mem_stageDomain hc⟩
  have hEk : H.regularizedStageEnd T c k = c := H.regularizedStageEnd_eq_of_mem_stageDomain hc0 hc
  have hSk : H.regularizedStageStart T c k = c := H.regularizedStageStart_eq_of_mem_Icc hc0 hcIcc
  let α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier := fun j =>
    if h₁ : k < j.val then α₁ ⟨j.val, h₁.le, j.property.2⟩
    else if h₂ : j.val < k then α₂ ⟨j.val, j.property.1, h₂.le⟩
    else piecewise (Iic c) (α₁ ⟨j.val, not_lt.1 h₂, j.property.2⟩)
      (α₂ ⟨j.val, j.property.1, not_lt.1 h₁⟩)
  have hup (j : H.StageInterval first last) (h : k < j.val) :
      α j = α₁ ⟨j.val, h.le, j.property.2⟩ := by simp only [α, dif_pos h]
  have hlow (j : H.StageInterval first last) (h : j.val < k) :
      α j = α₂ ⟨j.val, j.property.1, h.le⟩ := by
    simp only [α, dif_neg (not_lt.2 h.le), dif_pos h]
  have hmid : α ⟨k, hfk, hkl⟩ = piecewise (Iic c) (α₁ ⟨k, le_rfl, hkl⟩) (α₂ ⟨k, hfk, le_rfl⟩) := by
    simp only [α, lt_irrefl, dif_neg, not_false_eq_true]
  have hmidL : EqOn (α ⟨k, hfk, hkl⟩) (α₁ ⟨k, le_rfl, hkl⟩) (Iic c) := fun t ht => by
    rw [hmid, piecewise_eq_of_mem _ _ _ ht]
  have hmidR : EqOn (α ⟨k, hfk, hkl⟩) (α₂ ⟨k, hfk, le_rfl⟩) (Ici c) := fun t ht => by
    rcases eq_or_lt_of_le (show c ≤ t from ht) with h | h
    · subst h
      rw [hmidL (mem_Iic.2 le_rfl)]
      exact hx₁.trans hx₂.symm
    · rw [hmid, piecewise_eq_of_notMem (Iic c) _ _ (show t ∉ Iic c from not_le.2 h)]
  have hmidAC : Manifold.absolutelyContinuousOnInterval ThreeModel (α ⟨k, hfk, hkl⟩)
      (H.regularizedStageStart T u k) (H.regularizedStageEnd T v k) := by
    have h₁ := hα₁ ⟨k, le_rfl, hkl⟩
    have h₂ := hα₂ ⟨k, hfk, le_rfl⟩
    have hb₁ := (H.regularizedStage_bounds hu huc hupper hc ⟨k, le_rfl, hkl⟩).2.1
    have hb₂ := (H.regularizedStage_bounds hc0 hcv hcIcc hlower ⟨k, hfk, le_rfl⟩).2.1
    change H.regularizedStageStart T u k ≤ H.regularizedStageEnd T c k at hb₁
    change H.regularizedStageStart T c k ≤ H.regularizedStageEnd T v k at hb₂
    change Manifold.absolutelyContinuousOnInterval ThreeModel _
      (H.regularizedStageStart T u k) (H.regularizedStageEnd T c k) at h₁
    change Manifold.absolutelyContinuousOnInterval ThreeModel _
      (H.regularizedStageStart T c k) (H.regularizedStageEnd T v k) at h₂
    rw [hEk] at h₁ hb₁
    rw [hSk] at h₂ hb₂
    rw [hmid]
    exact Manifold.absolutelyContinuousOnInterval_piecewise_Iic h₁ h₂ hb₁ hb₂
      (hx₁.trans hx₂.symm)
  have hAC (j : H.StageInterval first last) : Manifold.absolutelyContinuousOnInterval ThreeModel
      (α j) (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) := by
    rcases lt_trichotomy j.val k with h | h | h
    · rw [hlow j h, ← H.regularizedStageStart_eq_of_lt hc h (pow_le_pow_left₀ hu huc 2)]
      exact hα₂ _
    · obtain ⟨jv, hj1, hj2⟩ := j
      change jv = k at h
      subst h
      exact hmidAC
    · rw [hup j h, ← H.regularizedStageEnd_eq_of_lt hc h (pow_le_pow_left₀ hc0 hcv 2)]
      exact hα₁ _
  have hsplitj (j : H.StageInterval first last) :
      H.stageRegularizedExtendedAction j.val T B (α j)
          (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) =
        (if k ≤ j.val then H.stageRegularizedExtendedAction j.val T B (α j)
          (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T c j.val) else 0) +
        (if j.val ≤ k then H.stageRegularizedExtendedAction j.val T B (α j)
          (H.regularizedStageStart T c j.val) (H.regularizedStageEnd T v j.val) else 0) := by
    apply H.stageExtendedAction_split j.val k hu huc hcv hc (α j) (fun _ => hAC j)
    intro h
    obtain ⟨jv, hj1, hj2⟩ := j
    change jv = k at h
    subst h
    exact hscalar
  have hwk (i : Fin H.eventCount) (hik : i.succ = k) : c ≤ Real.sqrt (T - H.time i.succ) := by
    rw [hik]
    exact Real.le_sqrt_of_sq_le (by linarith [hcIcc.1])
  have hwk' (i : Fin H.eventCount) (hik : i.castSucc = k) : Real.sqrt (T - H.time i.succ) ≤ c := by
    have hlt : T - c ^ 2 < H.time i.succ := by
      rw [← hik] at hc
      simp only [stageDomain, Fin.lastCases_castSucc, mem_Ico] at hc
      exact hc.2
    rw [← Real.sqrt_sq hc0]
    exact Real.sqrt_le_sqrt (by linarith)
  refine ⟨hu, huc.trans hcv, hupper, hlower, α, hAC, ?_, ?_, ?_, ?_⟩
  · by_cases h : k < last
    · rw [hup _ h]
      exact hp₁
    · obtain rfl : k = last := le_antisymm hkl (not_lt.1 h)
      exact (hmidL (mem_Iic.2 huc)).trans hp₁
  · by_cases h : first < k
    · rw [hlow _ h]
      exact hq₂
    · obtain rfl : first = k := le_antisymm hfk (not_lt.1 h)
      exact (hmidR (mem_Ici.2 hcv)).trans hq₂
  · intro i hf hl
    rcases le_or_gt k i.castSucc with hki | hik
    · obtain ⟨z, h1, h2⟩ := hn₁ i hki hl
      refine ⟨z, h1.trans ?_, h2.trans ?_⟩
      · rcases eq_or_lt_of_le hki with h | h
        · subst h
          exact (hmidL (mem_Iic.2 (hwk' i rfl))).symm
        · rw [hup _ h]
      · rw [hup _ (hki.trans_lt i.castSucc_lt_succ)]
    · have hsk : i.succ ≤ k := Fin.castSucc_lt_iff_succ_le.1 hik
      obtain ⟨z, h1, h2⟩ := hn₂ i hf hsk
      refine ⟨z, h1.trans ?_, h2.trans ?_⟩
      · rw [hlow _ hik]
      · rcases eq_or_lt_of_le hsk with h | h
        · subst h
          exact (hmidR (mem_Ici.2 (hwk i rfl))).symm
        · rw [hlow _ h]
  · rw [← hsum, ← hs₁, ← hs₂, regularizedExtendedAction]
    rw [Finset.sum_congr rfl (fun j _ => hsplitj j), Finset.sum_add_distrib]
    congr 1
    · apply H.sum_stageInterval_upper hfk
      intro j h
      rcases eq_or_lt_of_le h with h' | h'
      · obtain ⟨jv, hj1, hj2⟩ := j
        change k = jv at h'
        subst h'
        apply H.stageRegularizedExtendedAction_congr
        intro t ht
        apply hmidL
        rw [hEk] at ht
        exact mem_Iic.2 ht.2.le
      · rw [hup j h']
    · apply H.sum_stageInterval_lower hkl
      intro j h
      rcases eq_or_lt_of_le h with h' | h'
      · obtain ⟨jv, hj1, hj2⟩ := j
        change jv = k at h'
        subst h'
        apply H.stageRegularizedExtendedAction_congr
        intro t ht
        apply hmidR
        rw [hSk] at ht
        exact mem_Ici.2 ht.1.le
      · rw [hlow j h']

theorem mem_regularizedActionValues_split_at_parameter {first last : Fin (H.eventCount + 1)}
    (hle : first ≤ last) (k : Fin (H.eventCount + 1)) (hfk : first ≤ k) (hkl : k ≤ last)
    {T B u v c : ℝ} {A : WithTop ℝ} (hu : 0 ≤ u) (huc : u ≤ c) (hcv : c ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first) (hc : T - c ^ 2 ∈ H.stageDomain k)
    (hscalar : ∀ t ∈ Ioo (H.regularizedStageStart T u k) (H.regularizedStageEnd T v k),
      ∀ x : (H.stage k).Carrier, -B ≤ metricScalarAt (H.stageMetric k (T - t ^ 2)) x)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) :
    A ∈ H.regularizedActionValues first last hle T B u v p q ↔
      ∃ x : (H.stage k).Carrier, ∃ A₁ A₂ : WithTop ℝ,
        A₁ ∈ H.regularizedActionValues k last hkl T B u c p x ∧
        A₂ ∈ H.regularizedActionValues first k hfk T B c v x q ∧ A₁ + A₂ = A :=
  ⟨H.split_parameter_forward hle k hfk hkl hu huc hcv hupper hlower hc hscalar p q,
    H.split_parameter_backward hle k hfk hkl hu huc hcv hupper hlower hc hscalar p q⟩

theorem mem_Icc_of_mem_regularizedStage_Icc {first last : Fin (H.eventCount + 1)}
    {T u v s : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first) (j : H.StageInterval first last)
    (hs : s ∈ Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) :
    T - s ^ 2 ∈ Icc (H.time j.val) (H.stageEndTime j.val) := by
  have hb := H.regularizedStage_bounds hu huv hupper hlower j
  have hs0 : 0 ≤ s := hu.trans (hb.1.trans hs.1)
  have hy₁ : 0 ≤ T - min (T - u ^ 2) (H.stageEndTime j.val) := by
    have := min_le_left (T - u ^ 2) (H.stageEndTime j.val)
    nlinarith [sq_nonneg u]
  have hjT : H.time j.val ≤ T - u ^ 2 := (H.time_strictMono.monotone j.property.2).trans hupper.1
  have hy₂ : 0 ≤ T - max (T - v ^ 2) (H.time j.val) := by
    have := max_le (show T - v ^ 2 ≤ T by nlinarith [sq_nonneg v])
      (hjT.trans (show T - u ^ 2 ≤ T by nlinarith [sq_nonneg u]))
    linarith
  have h₁ := (Real.sqrt_le_left hs0).1 hs.1
  have h₂ := (Real.le_sqrt hs0 hy₂).1 hs.2
  constructor
  · have := le_max_right (T - v ^ 2) (H.time j.val)
    linarith
  · have := min_le_right (T - u ^ 2) (H.stageEndTime j.val)
    linarith

namespace LWindow

variable {H} {lo hi : Fin (H.eventCount + 1)} {T : ℝ} (W : H.LWindow lo hi T)

theorem upper_mem_Icc : T - W.a ^ 2 ∈ Icc (H.time hi) (H.stageEndTime hi) :=
  ⟨H.time_le_of_mem_stageDomain W.upper, H.le_stageEndTime_of_mem_stageDomain W.upper⟩

theorem mem_carrier {s : ℝ} (hs : s ∈ Icc W.a W.b) : T - s ^ 2 ∈ W.D.carrier :=
  W.D.regular_subset (W.regular s hs)

def restrict {lo' hi' : Fin (H.eventCount + 1)} (hlo : lo ≤ lo') (hhi : hi' ≤ hi)
    (hle : lo' ≤ hi') {a' b' : ℝ} (ha : W.a ≤ a') (hab : a' < b') (hb : b' ≤ W.b)
    (hup : T - a' ^ 2 ∈ H.stageDomain hi') (hdown : T - b' ^ 2 ∈ H.stageDomain lo') :
    H.LWindow lo' hi' T where
  X := W.X
  a := a'
  b := b'
  nonneg := W.nonneg.trans ha
  lt := hab
  le := hle
  upper := hup
  lower := hdown
  D := W.D
  S := W.S
  solution := W.solution
  regular := fun s hs => W.regular s ⟨ha.trans hs.1, hs.2.trans hb⟩
  f := fun j => W.f ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩
  localDiffeomorph := fun _ => W.localDiffeomorph _
  injective := fun _ => W.injective _
  crossing := fun i hl hh z => W.crossing i (hlo.trans hl) (hh.trans hhi) z
  metric := fun j s hs => W.metric _ s
    ⟨(regularizedStageStart_le_of_le W.nonneg ha j.val).trans_lt hs.1,
      hs.2.trans_le (regularizedStageEnd_le_of_le
        ((W.nonneg.trans ha).trans hab.le) hb j.val)⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem coe_lRegularizedAction_mem_regularizedActionValues {B : ℝ}
    (hscalar : ∀ j : H.StageInterval lo hi,
      ∀ t ∈ Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (γ : ℝ → W.X) (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ) :
    (lRegularizedAction W.S T γ W.a W.b : WithTop ℝ) ∈
      H.regularizedActionValues lo hi W.le T B W.a W.b
        (W.f ⟨hi, W.le, le_rfl⟩ (γ W.a)) (W.f ⟨lo, le_rfl, W.le⟩ (γ W.b)) :=
  H.coe_mem_regularizedActionValues_of_mem_regularizedC1ActionValues lo hi W.le hscalar _ _
    (H.action_mem_regularizedC1ActionValues_of_common_curve lo hi W.le W.f W.localDiffeomorph
      W.crossing W.S W.solution T W.nonneg W.lt.le W.upper_mem_Icc W.lower
      (fun _ hs => W.mem_carrier hs) W.metric γ hγ)

theorem mem_Icc_of_mem_piece (j : H.StageInterval lo hi) {s : ℝ}
    (hs : s ∈ Icc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val)) :
    T - s ^ 2 ∈ Icc (H.time j.val) (H.stageEndTime j.val) :=
  H.mem_Icc_of_mem_regularizedStage_Icc W.nonneg W.lt.le W.upper_mem_Icc W.lower j hs

theorem piece_subset (j : H.StageInterval lo hi) :
    Icc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val) ⊆
      Icc W.a W.b := by
  have hb := H.regularizedStage_bounds W.nonneg W.lt.le W.upper_mem_Icc W.lower j
  exact Icc_subset_Icc hb.1 hb.2.2

theorem exists_mem_piece {s : ℝ} (hs : s ∈ Icc W.a W.b) :
    ∃ j : H.StageInterval lo hi,
      s ∈ Icc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val) :=
  H.exists_mem_regularizedStage_Icc lo hi W.le W.nonneg (H.time_le_of_mem_stageDomain W.lower)
    (H.le_stageEndTime_of_mem_stageDomain W.upper) hs

theorem contMDiffOn_invFun (j : H.StageInterval lo hi) [Nonempty W.X] :
    ContMDiffOn ThreeModel ThreeModel 1 (Function.invFun (W.f j)) (range (W.f j)) := by
  rintro _ ⟨x, rfl⟩
  have hx := W.localDiffeomorph j x
  have hev : Function.invFun (W.f j) =ᶠ[𝓝 (W.f j x)] hx.localInverse := by
    filter_upwards [hx.localInverse_open_source.mem_nhds hx.localInverse_mem_source] with y hy
    apply W.injective j
    rw [Function.invFun_eq ⟨_, hx.localInverse_right_inv hy⟩, hx.localInverse_right_inv hy]
  exact ((hx.localInverse_contMDiffAt.of_le (by decide)).congr_of_eventuallyEq
    hev).contMDiffWithinAt

theorem invFun_eq_of_mem_piece_of_mem_piece [Nonempty W.X]
    (α : (j : H.StageInterval lo hi) → ℝ → (H.stage j.val).Carrier)
    (hnode : ∀ (i : Fin H.eventCount) (hl : lo ≤ i.castSucc) (hh : i.succ ≤ hi),
      ∃ z : (H.event i).old,
        z.val.val = α ⟨i.castSucc, hl, i.castSucc_lt_succ.le.trans hh⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = α ⟨i.succ, hl.trans i.castSucc_lt_succ.le, hh⟩
          (Real.sqrt (T - H.time i.succ)))
    (hrange : ∀ j, MapsTo (α j)
      (Icc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val))
      (range (W.f j)))
    {s : ℝ} (j k : H.StageInterval lo hi) (hjk : j.val < k.val)
    (hj : s ∈ Icc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val))
    (hk : s ∈ Icc (H.regularizedStageStart T W.a k.val) (H.regularizedStageEnd T W.b k.val)) :
    Function.invFun (W.f j) (α j s) = Function.invFun (W.f k) (α k s) := by
  have h₁ := (W.mem_Icc_of_mem_piece j hj).2
  have h₂ := (W.mem_Icc_of_mem_piece k hk).1
  have h₃ := H.stageEndTime_le_time_of_lt hjk
  obtain ⟨jv, hj1, hj2⟩ := j
  obtain ⟨kv, hk1, hk2⟩ := k
  change jv < kv at hjk
  cases jv using Fin.lastCases with
  | last => exact absurd hjk (not_lt.2 (Fin.le_last kv))
  | cast i =>
    change H.stageEndTime i.castSucc ≤ H.time kv at h₃
    change H.time kv ≤ T - s ^ 2 at h₂
    change T - s ^ 2 ≤ H.stageEndTime i.castSucc at h₁
    rw [H.stageEndTime_castSucc] at h₁ h₃
    have hkv : kv = i.succ := H.time_strictMono.injective (by linarith)
    subst hkv
    have hs0 : 0 ≤ s := W.nonneg.trans ((W.piece_subset _ hj).1)
    have hsw : s = Real.sqrt (T - H.time i.succ) := by
      rw [show T - H.time i.succ = s ^ 2 by linarith, Real.sqrt_sq hs0]
    subst hsw
    obtain ⟨z, hz1, hz2⟩ := hnode i hj1 hk2
    set x := Function.invFun (W.f ⟨i.castSucc, hj1, hj2⟩)
      (α ⟨i.castSucc, hj1, hj2⟩ (Real.sqrt (T - H.time i.succ)))
    have hx : W.f ⟨i.castSucc, hj1, hj2⟩ x =
        α ⟨i.castSucc, hj1, hj2⟩ (Real.sqrt (T - H.time i.succ)) :=
      Function.invFun_eq (hrange _ hj)
    obtain ⟨z', _, hz'1, hz'2⟩ := W.crossing i hj1 hk2 x
    have hzz : z' = z := Subtype.ext (Subtype.ext (hz'1.trans (hx.trans hz1.symm)))
    subst hzz
    have hnew : W.f ⟨i.succ, hk1, hk2⟩ x =
        α ⟨i.succ, hk1, hk2⟩ (Real.sqrt (T - H.time i.succ)) := hz'2.symm.trans hz2
    rw [← hnew, Function.leftInverse_invFun (W.injective _) x]

theorem exists_lift (α : (j : H.StageInterval lo hi) → ℝ → (H.stage j.val).Carrier)
    (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val))
    (hnode : ∀ (i : Fin H.eventCount) (hl : lo ≤ i.castSucc) (hh : i.succ ≤ hi),
      ∃ z : (H.event i).old,
        z.val.val = α ⟨i.castSucc, hl, i.castSucc_lt_succ.le.trans hh⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = α ⟨i.succ, hl.trans i.castSucc_lt_succ.le, hh⟩
          (Real.sqrt (T - H.time i.succ)))
    (hrange : ∀ j, MapsTo (α j)
      (Icc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val))
      (range (W.f j))) :
    ∃ γ : ℝ → W.X, Continuous γ ∧
      Manifold.absolutelyContinuousOnInterval ThreeModel γ W.a W.b ∧
      ∀ j, EqOn (W.f j ∘ γ) (α j)
        (Icc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val)) := by
  classical
  obtain ⟨j₀, hj₀⟩ := W.exists_mem_piece (left_mem_Icc.2 W.lt.le)
  obtain ⟨x₀, -⟩ := hrange j₀ hj₀
  have : Nonempty W.X := ⟨x₀⟩
  let P : H.StageInterval lo hi → Set ℝ := fun j =>
    Icc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val)
  have hcons : ∀ j k s, s ∈ P j → s ∈ P k →
      Function.invFun (W.f j) (α j s) = Function.invFun (W.f k) (α k s) := by
    intro j k s hj hk
    rcases lt_trichotomy j.val k.val with h | h | h
    · exact W.invFun_eq_of_mem_piece_of_mem_piece α hnode hrange j k h hj hk
    · rw [Subtype.ext h]
    · exact (W.invFun_eq_of_mem_piece_of_mem_piece α hnode hrange k j h hk hj).symm
  let γ₀ : ℝ → W.X := fun s =>
    if h : ∃ j, s ∈ P j then Function.invFun (W.f h.choose) (α h.choose s) else x₀
  have hγ₀ : ∀ j, ∀ s ∈ P j, γ₀ s = Function.invFun (W.f j) (α j s) := by
    intro j s hs
    have h : ∃ j, s ∈ P j := ⟨j, hs⟩
    simp only [γ₀, dif_pos h]
    exact hcons _ _ s h.choose_spec hs
  have hAC₀ : Manifold.absolutelyContinuousOnInterval ThreeModel γ₀ W.a W.b := by
    apply Manifold.absolutelyContinuousOnInterval_of_subset_iUnion_Icc
      (fun j : H.StageInterval lo hi => H.regularizedStageStart T W.a j.val)
      (fun j => H.regularizedStageEnd T W.b j.val) W.lt.le
      (fun s hs => mem_iUnion.2 (W.exists_mem_piece hs))
    intro j
    have hb := (H.regularizedStage_bounds W.nonneg W.lt.le W.upper_mem_Icc W.lower j).2.1
    have hcomp := Manifold.absolutelyContinuousOnInterval_comp_of_contMDiffOn
      (W.localDiffeomorph j).isOpen_range (W.contMDiffOn_invFun j) (hα j)
      (by rw [uIcc_of_le hb]; exact hrange j)
    exact Manifold.absolutelyContinuousOnInterval_congr hcomp
      (fun s hs => (hγ₀ j s (by rwa [uIcc_of_le hb] at hs)).symm)
  let γ : ℝ → W.X := fun s => γ₀ (projIcc W.a W.b W.lt.le s)
  have heq : EqOn γ₀ γ (Icc W.a W.b) := fun s hs => by
    simp only [γ, projIcc_of_mem W.lt.le hs]
  refine ⟨γ, ?_, Manifold.absolutelyContinuousOnInterval_congr hAC₀
    (by rw [uIcc_of_le W.lt.le]; exact heq), fun j s hs => ?_⟩
  · have hc := hAC₀.1
    rw [uIcc_of_le W.lt.le] at hc
    exact hc.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      (fun s => (projIcc W.a W.b W.lt.le s).2)
  · change W.f j (γ s) = α j s
    rw [← heq (W.piece_subset j hs), hγ₀ j s hs]
    exact Function.invFun_eq (hrange j hs)

theorem stageRegularizedLagrangian_ae_eq
    (α : (j : H.StageInterval lo hi) → ℝ → (H.stage j.val).Carrier) (γ : ℝ → W.X)
    (hγ : Manifold.absolutelyContinuousOnInterval ThreeModel γ W.a W.b)
    (heq : ∀ j, EqOn (W.f j ∘ γ) (α j)
      (Icc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val)))
    (j : H.StageInterval lo hi) :
    H.stageRegularizedLagrangian j.val T (α j) =ᵐ[volume.restrict
      (Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val))]
      lRegularizedLagrangian W.S T γ := by
  have hdiff := ae_restrict_of_ae_restrict_of_subset
    (show Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val) ⊆
      uIcc W.a W.b by
        rw [uIcc_of_le W.lt.le]
        exact Ioo_subset_Icc_self.trans (W.piece_subset j))
    (Manifold.absolutelyContinuousOnInterval_ae_mdifferentiableAt hγ)
  filter_upwards [hdiff, ae_restrict_mem measurableSet_Ioo] with t hdt ht
  have hev : α j =ᶠ[𝓝 t] W.f j ∘ γ := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    exact (heq j (Ioo_subset_Icc_self hr)).symm
  have hvel : lVelocity (I := ThreeModel) (α j) t = lVelocity (I := ThreeModel) (W.f j ∘ γ) t := by
    have hmf := Filter.EventuallyEq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel) hev
    with_unfolding_all exact congrArg (fun L => L (1 : ℝ)) hmf
  have hval : α j t = (W.f j ∘ γ) t := hev.self_of_nhds
  rw [← H.stageRegularizedLagrangian_comp_eq_of_localPullMetric j.val W.S (W.f j)
    (W.localDiffeomorph j) T hdt (W.metric j t ht)]
  unfold stageRegularizedLagrangian
  rw [hval, hvel]

theorem absolutelyContinuousOnInterval_of_eqOn_comp
    (α : (j : H.StageInterval lo hi) → ℝ → (H.stage j.val).Carrier) (γ : ℝ → W.X)
    (hγ : Manifold.absolutelyContinuousOnInterval ThreeModel γ W.a W.b)
    (heq : ∀ j, EqOn (W.f j ∘ γ) (α j)
      (Icc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val)))
    (j : H.StageInterval lo hi) :
    Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val) := by
  have hb := (H.regularizedStage_bounds W.nonneg W.lt.le W.upper_mem_Icc W.lower j).2.1
  have hsub : uIcc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val) ⊆
      uIcc W.a W.b := by
    rw [uIcc_of_le hb, uIcc_of_le W.lt.le]
    exact W.piece_subset j
  have hcomp := Manifold.absolutelyContinuousOnInterval_comp_of_contMDiffOn isOpen_univ
    ((W.localDiffeomorph j).contMDiff.contMDiffOn.of_le (by decide))
    (Manifold.absolutelyContinuousOnInterval_mono hγ hsub) (mapsTo_univ _ _)
  exact Manifold.absolutelyContinuousOnInterval_congr hcomp
    (by rw [uIcc_of_le hb]; exact heq j)

private theorem intervalIntegrable_stage_iff
    (α : (j : H.StageInterval lo hi) → ℝ → (H.stage j.val).Carrier) (γ : ℝ → W.X)
    (hγ : Manifold.absolutelyContinuousOnInterval ThreeModel γ W.a W.b)
    (heq : ∀ j, EqOn (W.f j ∘ γ) (α j)
      (Icc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val))) :
    (∀ j : H.StageInterval lo hi, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (α j))
      volume (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val)) ↔
      IntervalIntegrable (lRegularizedLagrangian W.S T γ) volume W.a W.b := by
  have hb (j : H.StageInterval lo hi) :=
    (H.regularizedStage_bounds W.nonneg W.lt.le W.upper_mem_Icc W.lower j).2.1
  constructor
  · intro hall
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le W.lt.le]
    have hU : IntegrableOn (lRegularizedLagrangian W.S T γ) (⋃ j : H.StageInterval lo hi,
        Icc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val)) :=
      integrableOn_finite_iUnion.2 fun j => (integrableOn_Icc_iff_integrableOn_Ioo
        (f := lRegularizedLagrangian W.S T γ)).2
        (((intervalIntegrable_iff_integrableOn_Ioo_of_le (hb j)).1 (hall j)).congr_fun_ae
          (W.stageRegularizedLagrangian_ae_eq α γ hγ heq j))
    exact hU.mono_set fun s hs => mem_iUnion.2 (W.exists_mem_piece hs)
  · intro hint j
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (hb j)]
    have hsub : uIcc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val) ⊆
        uIcc W.a W.b := by
      rw [uIcc_of_le (hb j), uIcc_of_le W.lt.le]
      exact W.piece_subset j
    exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le (hb j)).1
      (hint.mono_set hsub)).congr_fun_ae (W.stageRegularizedLagrangian_ae_eq α γ hγ heq j).symm

theorem regularizedExtendedAction_eq_coe {B : ℝ}
    (hscalar : ∀ j : H.StageInterval lo hi,
      ∀ t ∈ Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (α : (j : H.StageInterval lo hi) → ℝ → (H.stage j.val).Carrier) (γ : ℝ → W.X)
    (hγ : Manifold.absolutelyContinuousOnInterval ThreeModel γ W.a W.b)
    (heq : ∀ j, EqOn (W.f j ∘ γ) (α j)
      (Icc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val)))
    (hint : IntervalIntegrable (lRegularizedLagrangian W.S T γ) volume W.a W.b) :
    H.regularizedExtendedAction lo hi T B W.a W.b α =
      (lRegularizedAction W.S T γ W.a W.b : WithTop ℝ) := by
  have hb (j : H.StageInterval lo hi) :=
    (H.regularizedStage_bounds W.nonneg W.lt.le W.upper_mem_Icc W.lower j).2.1
  rw [H.regularizedExtendedAction_eq_sum_action lo hi W.nonneg W.lt.le W.upper_mem_Icc W.lower α
    ((W.intervalIntegrable_stage_iff α γ hγ heq).2 hint)
    (fun j => by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact hscalar j t ht _)]
  congr 1
  have hint' (c d : ℝ) (hc : c ∈ Icc W.a W.b) (hd : d ∈ Icc W.a W.b) :
      IntervalIntegrable (lRegularizedLagrangian W.S T γ) volume c d :=
    hint.mono_set (uIcc_subset_uIcc (by rwa [uIcc_of_le W.lt.le]) (by rwa [uIcc_of_le W.lt.le]))
  have hsum := H.sum_regularizedStage_sub (fun t => ∫ s in W.a..t, lRegularizedLagrangian W.S T γ s)
    W.le W.nonneg W.lt.le W.upper_mem_Icc W.lower
  simp only [intervalIntegral.integral_same, sub_zero] at hsum
  rw [lRegularizedAction, ← hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj := W.piece_subset j
  rw [intervalIntegral.integral_interval_sub_left
      (hint' _ _ (left_mem_Icc.2 W.lt.le) (hj (right_mem_Icc.2 (hb j))))
      (hint' _ _ (left_mem_Icc.2 W.lt.le) (hj (left_mem_Icc.2 (hb j)))),
    stageRegularizedAction, intervalIntegral.integral_of_le (hb j),
    intervalIntegral.integral_of_le (hb j), integral_Ioc_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo]
  exact integral_congr_ae (W.stageRegularizedLagrangian_ae_eq α γ hγ heq j)

theorem regularizedExtendedAction_eq_top_iff {B : ℝ}
    (hscalar : ∀ j : H.StageInterval lo hi,
      ∀ t ∈ Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (α : (j : H.StageInterval lo hi) → ℝ → (H.stage j.val).Carrier) (γ : ℝ → W.X)
    (hγ : Manifold.absolutelyContinuousOnInterval ThreeModel γ W.a W.b)
    (heq : ∀ j, EqOn (W.f j ∘ γ) (α j)
      (Icc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val))) :
    H.regularizedExtendedAction lo hi T B W.a W.b α = ⊤ ↔
      ¬ IntervalIntegrable (lRegularizedLagrangian W.S T γ) volume W.a W.b := by
  rw [H.regularizedExtendedAction_eq_top_iff lo hi W.nonneg W.lt.le W.upper_mem_Icc W.lower α
    (W.absolutelyContinuousOnInterval_of_eqOn_comp α γ hγ heq)
    (fun j => by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact hscalar j t ht _),
    ← (W.intervalIntegrable_stage_iff α γ hγ heq), not_forall]

theorem exists_splice {first last : Fin (H.eventCount + 1)} (hle : first ≤ last)
    (hlo : first ≤ lo) (hhi : hi ≤ last) {B u v : ℝ} (hu : 0 ≤ u) (hua : u ≤ W.a)
    (hbv : W.b ≤ v) (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hnode : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hfin : H.regularizedExtendedAction first last T B u v α ≠ ⊤)
    (γ : ℝ → W.X) (hγ : Manifold.absolutelyContinuousOnInterval ThreeModel γ W.a W.b)
    (heq : ∀ j : H.StageInterval lo hi,
      EqOn (W.f j ∘ γ) (α ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩)
        (Icc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val)))
    (δ : ℝ → W.X) (hδ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 δ) (hδa : δ W.a = γ W.a)
    (hδb : δ W.b = γ W.b) :
    ∃ A ∈ H.regularizedActionValues first last hle T B u v (α ⟨last, hle, le_rfl⟩ u)
        (α ⟨first, le_rfl, hle⟩ v),
      A + (lRegularizedAction W.S T γ W.a W.b : WithTop ℝ) =
        H.regularizedExtendedAction first last T B u v α +
          (lRegularizedAction W.S T δ W.a W.b : WithTop ℝ) := by
  have hsc (j : Fin (H.eventCount + 1)) (u' v' : ℝ) :
      ∀ t ∈ Ioo (H.regularizedStageStart T u' j) (H.regularizedStageEnd T v' j),
        ∀ x : (H.stage j).Carrier, -B ≤ metricScalarAt (H.stageMetric j (T - t ^ 2)) x :=
    fun t ht x => hfloor j _ (H.mapsTo_regularizedStage_Ioo T u' v' j ht) x
  have hscW : ∀ j : H.StageInterval lo hi,
      ∀ t ∈ Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val),
        ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x :=
    fun j => hsc j.val W.a W.b
  have hav : W.a ≤ v := W.lt.le.trans hbv
  have h1 := regularizedExtendedAction_eq_add_at_parameter hi (hlo.trans W.le) hhi hu hua hav
    W.upper (hsc hi u v) α hα
  have hα' : ∀ j : H.StageInterval first hi, Manifold.absolutelyContinuousOnInterval ThreeModel
      (α ⟨j.val, j.property.1, j.property.2.trans hhi⟩)
      (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T v j.val) := by
    intro j
    have hb := (H.regularizedStage_bounds W.nonneg hav W.upper_mem_Icc hlower j).2.1
    apply Manifold.absolutelyContinuousOnInterval_mono (hα _)
    rw [uIcc_of_le hb, uIcc_of_le (H.regularizedStage_bounds hu (hua.trans hav) hupper hlower
      ⟨j.val, j.property.1, j.property.2.trans hhi⟩).2.1]
    exact Icc_subset_Icc (regularizedStageStart_le_of_le hu hua j.val) le_rfl
  have h2 := regularizedExtendedAction_eq_add_at_parameter lo hlo W.le W.nonneg W.lt.le hbv
    W.lower (hsc lo W.a v) _ hα'
  have hE2 : H.regularizedExtendedAction lo hi T B W.a W.b
      (fun j => α ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩) ≠ ⊤ := by
    intro h
    apply hfin
    rw [h1, h2]
    rw [h, top_add, add_top]
  have hint := not_not.1 fun hn => hE2 ((W.regularizedExtendedAction_eq_top_iff hscW _ γ hγ
    heq).2 hn)
  have hmid := W.regularizedExtendedAction_eq_coe hscW _ γ hγ heq hint
  have M1 := mem_regularizedActionValues_upper_restrict (B := B) hi (hlo.trans W.le) hhi hu hua hav
    hupper hlower W.upper α hα hnode
  have M3 := mem_regularizedActionValues_lower_restrict (B := B) lo hlo W.le W.nonneg W.lt.le hbv
    W.upper_mem_Icc hlower W.lower _ hα' (fun i hf hl => hnode i hf (hl.trans hhi))
  have Mδ := W.coe_lRegularizedAction_mem_regularizedActionValues hscW δ hδ
  have hbhi := (H.regularizedStage_bounds W.nonneg W.lt.le W.upper_mem_Icc W.lower
    ⟨hi, W.le, le_rfl⟩).2.1
  have hblo := (H.regularizedStage_bounds W.nonneg W.lt.le W.upper_mem_Icc W.lower
    ⟨lo, le_rfl, W.le⟩).2.1
  have hSa : H.regularizedStageStart T W.a hi = W.a :=
    H.regularizedStageStart_eq_of_mem_Icc W.nonneg W.upper_mem_Icc
  have hEb : H.regularizedStageEnd T W.b lo = W.b :=
    H.regularizedStageEnd_eq_of_mem_stageDomain (W.nonneg.trans W.lt.le) W.lower
  have hpa : W.f ⟨hi, W.le, le_rfl⟩ (δ W.a) = α ⟨hi, hlo.trans W.le, hhi⟩ W.a := by
    rw [hδa]
    exact heq ⟨hi, W.le, le_rfl⟩ ⟨hSa.le, hSa.symm.trans_le hbhi⟩
  have hqb : W.f ⟨lo, le_rfl, W.le⟩ (δ W.b) = α ⟨lo, hlo, W.le.trans hhi⟩ W.b := by
    rw [hδb]
    exact heq ⟨lo, le_rfl, W.le⟩ ⟨hblo.trans_eq hEb, hEb.ge⟩
  rw [hpa, hqb] at Mδ
  have hA' := (H.mem_regularizedActionValues_split_at_parameter (hlo.trans W.le) lo hlo W.le
    W.nonneg W.lt.le hbv W.upper_mem_Icc hlower W.lower (hsc lo W.a v)
    (α ⟨hi, hlo.trans W.le, hhi⟩ W.a) (α ⟨first, le_rfl, hle⟩ v)).2 ⟨_, _, _, Mδ, M3, rfl⟩
  have hA := (H.mem_regularizedActionValues_split_at_parameter hle hi (hlo.trans W.le) hhi hu
    hua hav hupper hlower W.upper (hsc hi u v) (α ⟨last, hle, le_rfl⟩ u)
    (α ⟨first, le_rfl, hle⟩ v)).2 ⟨_, _, _, M1, hA', rfl⟩
  refine ⟨_, hA, ?_⟩
  rw [h1, h2, hmid]
  ac_rfl

theorem lRegularizedAction_le_of_regularizedCost_eq {first last : Fin (H.eventCount + 1)}
    (hle : first ≤ last) (hlo : first ≤ lo) (hhi : hi ≤ last) {B u v : ℝ} (hu : 0 ≤ u)
    (hua : u ≤ W.a) (hbv : W.b ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hnode : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hmin : H.regularizedExtendedAction first last T B u v α =
      H.regularizedCost first last hle T B u v (α ⟨last, hle, le_rfl⟩ u)
        (α ⟨first, le_rfl, hle⟩ v))
    (hfin : H.regularizedExtendedAction first last T B u v α ≠ ⊤)
    (γ : ℝ → W.X) (hγ : Manifold.absolutelyContinuousOnInterval ThreeModel γ W.a W.b)
    (heq : ∀ j : H.StageInterval lo hi,
      EqOn (W.f j ∘ γ) (α ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩)
        (Icc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val)))
    (δ : ℝ → W.X) (hδ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 δ) (hδa : δ W.a = γ W.a)
    (hδb : δ W.b = γ W.b) :
    lRegularizedAction W.S T γ W.a W.b ≤ lRegularizedAction W.S T δ W.a W.b := by
  obtain ⟨A, hA, hAeq⟩ := W.exists_splice hle hlo hhi hu hua hbv hupper hlower hfloor α hα hnode
    hfin γ hγ heq δ hδ hδa hδb
  have hc := H.regularizedCost_le_of_competitor first last hle T B u v _ _ hA
  rw [← hmin] at hc
  have hle' : H.regularizedExtendedAction first last T B u v α +
      (lRegularizedAction W.S T γ W.a W.b : WithTop ℝ) ≤
      H.regularizedExtendedAction first last T B u v α +
        (lRegularizedAction W.S T δ W.a W.b : WithTop ℝ) := by
    rw [← hAeq]
    exact add_le_add_left hc _
  exact WithTop.coe_le_coe.1 ((WithTop.add_le_add_iff_left hfin).1 hle')

end LWindow

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.LWindow

open TopologicalSpace

universe u
variable {H : ObservedHistory.{u}} {T : ℝ}

def ofStage (j : Fin (H.eventCount + 1)) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hup : T - a ^ 2 ∈ H.stageDomain j) (hdown : T - b ^ 2 ∈ H.stageDomain j)
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := (H.stage j).Carrier) D)
    (hS : IsSolutionOn S) (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular)
    (hmetric : ∀ s ∈ Ioo a b, S.base.metric (T - s ^ 2) = H.stageMetric j (T - s ^ 2))
    (U : TopologicalSpace.Opens (H.stage j).Carrier) : H.LWindow j j T :=
  letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)
  { X := U
    a := a
    b := b
    nonneg := ha
    lt := hab
    le := le_rfl
    upper := hup
    lower := hdown
    D := D
    S := CheegerGromovCompactness.solutionOnRestrictOpen S U
    solution := CheegerGromovCompactness.isSolutionOn_restrictOpen S hS U
    regular := hreg
    f := fun k => (le_antisymm k.property.1 k.property.2) ▸ (Subtype.val : U → (H.stage j).Carrier)
    localDiffeomorph := fun k => by
      obtain ⟨k, h1, h2⟩ := k
      obtain rfl := le_antisymm h1 h2
      exact isLocalDiffeomorph_subtype_val U
    injective := fun k => by
      obtain ⟨k, h1, h2⟩ := k
      obtain rfl := le_antisymm h1 h2
      exact Subtype.val_injective
    crossing := fun i hl hh _ =>
      absurd (hl.trans_lt (i.castSucc_lt_succ.trans_le hh)) (lt_irrefl j)
    metric := fun k s hs => by
      obtain ⟨k, h1, h2⟩ := k
      obtain rfl := le_antisymm h1 h2
      change (S.base.metric (T - s ^ 2)).restrictOpen U = localPullMetric
        (H.stageMetric j (T - s ^ 2)) (Subtype.val : U → (H.stage j).Carrier)
        (isLocalDiffeomorph_subtype_val U)
      rw [H.regularizedStageStart_eq_of_mem_Icc ha ⟨H.time_le_of_mem_stageDomain hup,
        H.le_stageEndTime_of_mem_stageDomain hup⟩,
        H.regularizedStageEnd_eq_of_mem_stageDomain (ha.trans hab.le) hdown] at hs
      rw [localPullMetric_subtype_val, hmetric s hs] }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_seam (i : Fin H.eventCount) {e : ℝ}
    (G : (H.stage i.succ).IncomingSlab (H.time i.succ) e)
    (hG : G.flow.base.metric (H.time i.succ) = (H.event i).outputMetric)
    (hGstage : ∀ t ∈ Ioo (H.time i.succ) e, H.stageMetric i.succ t = G.flow.base.metric t)
    (W : Opens (H.event i).incoming.terminalRegularOpen) (x₀ : W)
    (hW : ∀ x ∈ W, x.val ∈ interior (Subtype.val '' (H.event i).old))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hup : T - a ^ 2 ∈ H.stageDomain i.succ)
    (hupe : T - a ^ 2 < e) (hdown₀ : H.time i.castSucc < T - b ^ 2)
    (hdown₁ : T - b ^ 2 < H.time i.succ) :
    ∃ Wn : H.LWindow i.castSucc i.succ T, Wn.a = a ∧ Wn.b = b ∧
      range (Wn.f ⟨i.castSucc, le_rfl, i.castSucc_lt_succ.le⟩) =
        Subtype.val '' (W : Set (H.event i).incoming.terminalRegularOpen) := by
  classical
  have : SigmaCompactSpace (H.event i).incoming.terminalRegularOpen :=
    isSigmaCompact_iff_sigmaCompactSpace.mp (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen
      ThreeModel (H.event i).incoming.terminalRegularOpen.isOpen)
  have : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel W.isOpen)
  have hsa : H.time i.succ ≤ T - a ^ 2 := H.time_le_of_mem_stageDomain hup
  obtain ⟨F, Splus, hFsrc, _, hFcross, _, hpull, _, hS, _, _⟩ :=
    (H.event i).exists_survivor_solution_across_event G hG W x₀ hW
      (c := (H.time i.castSucc + (T - b ^ 2)) / 2) (d := (T - a ^ 2 + e) / 2)
      (by linarith) (by linarith) (by linarith) (by linarith)
  let fo : W → (H.stage i.castSucc).Carrier := fun z => z.val.val
  let fn : W → (H.stage i.succ).Carrier := fun z => F z.val
  have hfo : IsLocalDiffeomorph ThreeModel ThreeModel ∞ fo :=
    isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val _) (isLocalDiffeomorph_subtype_val W)
  have hfn : IsLocalDiffeomorph ThreeModel ThreeModel ∞ fn := fun z =>
    (isLocalDiffeomorph_subtype_val W z).comp ThreeModel _ ⟨F, hFsrc ▸ z.property, fun _ _ => rfl⟩
  have hval (k : H.StageInterval i.castSucc i.succ) (h : ¬ k.val = i.castSucc) :
      i.succ = k.val := by
    obtain ⟨k, h1, h2⟩ := k
    change i.val ≤ k.val at h1
    change k.val ≤ i.val + 1 at h2
    apply Fin.ext
    have h' : k.val ≠ i.val := fun h' => h (Fin.ext h')
    change i.val + 1 = k.val
    omega
  obtain ⟨f, hf₀, hf₁⟩ :
      ∃ f : (k : H.StageInterval i.castSucc i.succ) → W → (H.stage k.val).Carrier,
      (∀ h1 h2, f ⟨i.castSucc, h1, h2⟩ = fo) ∧ (∀ h1 h2, f ⟨i.succ, h1, h2⟩ = fn) :=
    ⟨fun k => if h : k.val = i.castSucc then h.symm ▸ fo else (hval k h) ▸ fn,
      fun _ _ => dif_pos rfl, fun _ _ => dif_neg (ne_of_gt i.castSucc_lt_succ)⟩
  have hcases (k : H.StageInterval i.castSucc i.succ) :
      k.val = i.castSucc ∨ k.val = i.succ := by
    by_cases h : k.val = i.castSucc
    exacts [Or.inl h, Or.inr (hval k h).symm]
  have hloc : ∀ k, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f k) := by
    rintro ⟨k, h1, h2⟩
    rcases hcases ⟨k, h1, h2⟩ with h | h <;> change k = _ at h <;> subst h
    · rw [hf₀ h1 h2]
      exact hfo
    · rw [hf₁ h1 h2]
      exact hfn
  have hinj : ∀ k, Function.Injective (f k) := by
    rintro ⟨k, h1, h2⟩
    rcases hcases ⟨k, h1, h2⟩ with h | h <;> change k = _ at h <;> subst h
    · rw [hf₀ h1 h2]
      exact Subtype.val_injective.comp Subtype.val_injective
    · rw [hf₁ h1 h2]
      intro z y hzy
      exact Subtype.ext (F.toPartialEquiv.injOn (hFsrc ▸ z.property) (hFsrc ▸ y.property) hzy)
  have hSa : H.regularizedStageStart T a i.castSucc = Real.sqrt (T - H.time i.succ) := by
    simp only [regularizedStageStart, H.stageEndTime_castSucc, min_eq_right hsa]
  have hEb : H.regularizedStageEnd T b i.succ = Real.sqrt (T - H.time i.succ) := by
    simp only [regularizedStageEnd, max_eq_right hdown₁.le]
  refine ⟨{
    X := W
    a := a
    b := b
    nonneg := ha
    lt := hab
    le := i.castSucc_lt_succ.le
    upper := hup
    lower := ?_
    D := _
    S := _
    solution := hS
    regular := ?_
    f := f
    localDiffeomorph := hloc
    injective := hinj
    crossing := ?_
    metric := ?_ }, rfl, rfl, ?_⟩
  · simp only [stageDomain, Fin.lastCases_castSucc, mem_Ico]
    exact ⟨hdown₀.le, hdown₁⟩
  · intro t ht
    have h₁ : a ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ ha ht.1 2
    have h₂ : t ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (ha.trans ht.1) ht.2 2
    exact ⟨by linarith, by linarith⟩
  · intro i' hl hh z
    obtain rfl : i' = i := by
      apply Fin.ext
      change i.val ≤ i'.val at hl
      change i'.val + 1 ≤ i.val + 1 at hh
      omega
    rw [hf₀ le_rfl i'.castSucc_lt_succ.le, hf₁ i'.castSucc_lt_succ.le le_rfl]
    exact hFcross z.val z.property
  · rintro ⟨k, h1, h2⟩ t ht
    rcases hcases ⟨k, h1, h2⟩ with h | h <;> change k = _ at h <;> subst h
    · change H.regularizedStageStart T a i.castSucc < t ∧ _ at ht
      rw [hSa] at ht
      have hts : T - t ^ 2 < H.time i.succ := by
        have := (Real.sqrt_lt' ((Real.sqrt_nonneg _).trans_lt ht.1)).1 ht.1
        linarith
      apply SmoothRiemannianMetric.ext_inner
      intro z v w
      rw [localPullMetric_inner, hf₀ h1 h2]
      change ((if T - t ^ 2 ≤ H.time i.succ then
        ((H.event i).terminal.extendedMetric (T - t ^ 2)).restrictOpen W else
        Splus.base.metric (T - t ^ 2)).inner z v w) = _
      rw [if_pos hts.le, (H.event i).terminal.extendedMetric_before hts]
      have hd : mfderiv ThreeModel ThreeModel fo z = ContinuousLinearMap.id ℝ ThreeSpace :=
        (mfderiv_subtypeVal_comp (I := ThreeModel) (J := ThreeModel)
          (Subtype.val : W → (H.event i).incoming.terminalRegularOpen) z).trans
          (mfderiv_subtype_val W z)
      rw [hd, show H.stageMetric i.castSucc (T - t ^ 2) =
        (H.event i).incoming.flow.base.metric (T - t ^ 2) by
          simp only [stageMetric, Fin.lastCases_castSucc]]
      rfl
    · change _ ∧ t < H.regularizedStageEnd T b i.succ at ht
      rw [hEb] at ht
      have ht0 : 0 ≤ t := (Real.sqrt_nonneg _).trans ht.1.le
      have hts : H.time i.succ < T - t ^ 2 := by
        have := (Real.lt_sqrt ht0).1 ht.2
        linarith
      have hte : T - t ^ 2 < e := by
        have hat : a ≤ t := (H.regularizedStage_bounds ha hab.le
          ⟨H.time_le_of_mem_stageDomain hup, H.le_stageEndTime_of_mem_stageDomain hup⟩
          (by simp only [stageDomain, Fin.lastCases_castSucc, mem_Ico]; exact ⟨hdown₀.le, hdown₁⟩)
          (⟨i.succ, i.castSucc_lt_succ.le, le_rfl⟩ :
            H.StageInterval i.castSucc i.succ)).1.trans ht.1.le
        nlinarith
      apply SmoothRiemannianMetric.ext_inner
      intro z v w
      rw [localPullMetric_inner, hf₁ h1 h2, hGstage _ ⟨hts, hte⟩]
      change ((if T - t ^ 2 ≤ H.time i.succ then
        ((H.event i).terminal.extendedMetric (T - t ^ 2)).restrictOpen W else
        Splus.base.metric (T - t ^ 2)).inner z v w) = _
      rw [if_neg (not_le.2 hts), hpull]
      have hd := mfderiv_restrict_open (I := ThreeModel) (J := ThreeModel)
        (F : (H.event i).incoming.terminalRegularOpen → (H.stage i.succ).Carrier) W z
      change mfderiv ThreeModel ThreeModel fn z = mfderiv ThreeModel ThreeModel F z.val at hd
      rw [hd]
      rfl
  · change range (f ⟨i.castSucc, le_rfl, i.castSucc_lt_succ.le⟩) = _
    rw [hf₀ le_rfl i.castSucc_lt_succ.le]
    ext p
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z.val, z.property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.LWindow
