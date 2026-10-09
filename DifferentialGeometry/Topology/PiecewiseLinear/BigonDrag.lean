/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BranchSlideConjugation
import DifferentialGeometry.Topology.PiecewiseLinear.ChartSlide

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem slideMap_fst_le_of_tent {p : ℝ × ℝ × ℝ} (h2 : p.2.2 = 0)
    (h1 : p.1 = (1 / 2 - |p.2.1|) / 2) : (slideMap p).1 ≤ -1 / 4 := by
  have hfst : (slideMap p).1 = p.1 - slideAmount p := rfl
  rw [hfst]
  rcases le_total |p.2.1| 1 with hu | hu
  · have hp1 : |p.1| ≤ 1 / 4 := by
      rw [h1, abs_le]
      constructor <;> linarith [abs_nonneg p.2.1]
    have hw : slideWidth p = 1 - |p.2.1| := by simp [slideWidth, h2]
    have ht : slideWidth p ≤ slideTaper p := by
      rw [hw, slideTaper]
      linarith [abs_nonneg p.2.1]
    have ha : slideAmount p = 1 - |p.2.1| := by
      rw [slideAmount, min_eq_left ht, hw,
        max_eq_right (show (0 : ℝ) ≤ 1 - |p.2.1| by linarith)]
    rw [ha, h1]
    linarith
  · have ha : slideAmount p = 0 :=
      slideAmount_eq_zero_of_width (by rw [h2, abs_zero, add_zero]; exact hu)
    rw [ha, h1]
    linarith

noncomputable def slideMapAt (t : ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (p.1 - t * slideAmount p, p.2.1, p.2.2)

theorem continuous_slideAmount : Continuous slideAmount := by
  have h : slideAmount = fun p => p.1 - (slideMap p).1 := by
    funext p
    change slideAmount p = p.1 - (p.1 - slideAmount p)
    ring
  rw [h]
  exact continuous_fst.sub (continuous_fst.comp continuous_slideMap)

theorem continuous_slideMapAt :
    Continuous fun q : ℝ × (ℝ × ℝ × ℝ) => slideMapAt q.1 q.2 := by
  unfold slideMapAt
  have hA : Continuous fun q : ℝ × (ℝ × ℝ × ℝ) => slideAmount q.2 :=
    continuous_slideAmount.comp continuous_snd
  exact ((continuous_fst.comp continuous_snd).sub (continuous_fst.mul hA)).prodMk
    ((continuous_fst.comp (continuous_snd.comp continuous_snd)).prodMk
      (continuous_snd.comp (continuous_snd.comp continuous_snd)))

theorem slideAmount_eq_zero_of_notMem {p : ℝ × ℝ × ℝ} (hp : p ∉ slideSupport) :
    slideAmount p = 0 := by
  have h : slideMap p = p := eqOn_slideMap_id_compl hp
  have h1 : p.1 - slideAmount p = p.1 := congrArg Prod.fst h
  linarith

theorem slideMapAt_eq_self_of_notMem (t : ℝ) {p : ℝ × ℝ × ℝ} (hp : p ∉ slideSupport) :
    slideMapAt t p = p := by
  simp [slideMapAt, slideAmount_eq_zero_of_notMem hp]

theorem slideMapAt_zero (p : ℝ × ℝ × ℝ) : slideMapAt 0 p = p := by
  simp [slideMapAt]

theorem slideMapAt_one (p : ℝ × ℝ × ℝ) : slideMapAt 1 p = slideMap p := by
  simp [slideMapAt, slideMap]

theorem slideMapAt_snd (t : ℝ) (p : ℝ × ℝ × ℝ) : (slideMapAt t p).2 = p.2 := rfl

theorem mapsTo_slideMapAt_of_subset {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {T : Set (ℝ × ℝ × ℝ)} (hT : slideSupport ⊆ T) : MapsTo (slideMapAt t) T T := by
  intro p hp
  by_cases hs : p ∈ slideSupport
  · refine hT ⟨hs.1, ?_⟩
    have hm := mapsTo_slideMap_slideSupport hs
    have hnn := slideAmount_nonneg p
    have hfst : (slideMap p).1 = p.1 - slideAmount p := rfl
    have hlo := (abs_le.mp hm.2).1
    have hhi := (abs_le.mp hs.2).2
    rw [hfst] at hlo
    change |p.1 - t * slideAmount p| ≤ 3
    rw [abs_le]
    have h1 : 0 ≤ (1 - t) * slideAmount p := mul_nonneg (by linarith) hnn
    have h2 : 0 ≤ t * slideAmount p := mul_nonneg ht0 hnn
    constructor
    · nlinarith
    · nlinarith
  · rw [slideMapAt_eq_self_of_notMem t hs]
    exact hp

theorem exists_bigonDrag {X : Type*} [TopologicalSpace X] [T2Space X]
    (e : OpenPartialHomeomorph X (ℝ × ℝ × ℝ)) (hsupp : slideSupport ⊆ e.target)
    {Sf Y C Tr : Set X} (hSf : ∀ x ∈ e.source, x ∈ Sf ↔ (e x).2.2 = 0)
    (hY : ∀ x ∈ e.source, x ∈ Y ↔ 0 ≤ (e x).2.2)
    (hC : ∀ x ∈ e.source, x ∈ C ↔ (e x).1 = 0 ∧ (e x).2.2 = 0)
    (hTr : ∀ x ∈ e.source, x ∈ Tr ↔ (e x).2.2 = 0 ∧ (e x).1 = (1 / 2 - |(e x).2.1|) / 2) :
    ∃ H : X × unitInterval → X, Continuous H ∧ (∀ x, H (x, 0) = x) ∧
      (∀ x, H (x, 1) = e.conjugateMap slideMap x) ∧
      (∀ x t, x ∉ e.symm '' slideSupport → H (x, t) = x) ∧
      (∀ x t, H (x, t) ∈ Sf ↔ x ∈ Sf) ∧ (∀ x t, H (x, t) ∈ Y ↔ x ∈ Y) ∧
      Function.Bijective (e.conjugateMap slideMap) ∧
      e.conjugateMap slideMap '' Tr ∩ C = (Tr ∩ C) \ e.source := by
  classical
  have hK : IsCompact (e.symm '' slideSupport) :=
    isCompact_slideSupport.image_of_continuousOn (e.continuousOn_symm.mono hsupp)
  have hKc : IsClosed (e.symm '' slideSupport) := hK.isClosed
  have hmapAt : ∀ t : unitInterval, MapsTo (slideMapAt t) e.target e.target :=
    fun t => mapsTo_slideMapAt_of_subset t.2.1 t.2.2 hsupp
  let H : X × unitInterval → X := fun q => e.conjugateMap (slideMapAt q.2) q.1
  have hHsrc : ∀ x (t : unitInterval), x ∈ e.source →
      H (x, t) = e.symm (slideMapAt t (e x)) := fun x t hx => e.conjugateMap_of_mem _ hx
  have hHout : ∀ x (t : unitInterval), x ∉ e.symm '' slideSupport → H (x, t) = x := by
    intro x t hx
    by_cases hxs : x ∈ e.source
    · rw [hHsrc x t hxs]
      have hex : e x ∉ slideSupport := fun h => hx ⟨e x, h, e.left_inv hxs⟩
      rw [slideMapAt_eq_self_of_notMem t hex, e.left_inv hxs]
    · exact e.conjugateMap_of_notMem _ hxs
  have hcoord : ∀ {A : Set X} {Bm : Set (ℝ × ℝ × ℝ)},
      (∀ x ∈ e.source, x ∈ A ↔ e x ∈ Bm) → (∀ p (t : unitInterval), slideMapAt t p ∈ Bm ↔ p ∈ Bm) →
      ∀ x (t : unitInterval), H (x, t) ∈ A ↔ x ∈ A := by
    intro A Bm hA hB x t
    exact e.conjugateMap_mem_iff (hmapAt t) hA (fun y _ => hB y t) x
  refine ⟨H, ?_, ?_, ?_, hHout, ?_, ?_, ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    rintro ⟨x, t⟩
    by_cases hxs : x ∈ e.source
    · have hc : ContinuousAt (fun q : X × unitInterval =>
          e.symm (slideMapAt (q.2 : ℝ) (e q.1))) (x, t) := by
        have h1 : ContinuousAt (fun q : X × unitInterval => ((q.2 : ℝ), e q.1)) (x, t) :=
          (continuous_subtype_val.comp continuous_snd).continuousAt.prodMk
            ((e.continuousAt hxs).comp continuous_fst.continuousAt)
        have h2 : ContinuousAt (fun q : X × unitInterval => slideMapAt (q.2 : ℝ) (e q.1))
            (x, t) :=
          ContinuousAt.comp (f := fun q : X × unitInterval => ((q.2 : ℝ), e q.1))
            (g := fun r : ℝ × (ℝ × ℝ × ℝ) => slideMapAt r.1 r.2)
            continuous_slideMapAt.continuousAt h1
        exact ContinuousAt.comp (f := fun q : X × unitInterval => slideMapAt (q.2 : ℝ) (e q.1))
          (g := e.symm) (e.continuousAt_symm (hmapAt t (e.map_source hxs))) h2
      apply hc.congr_of_eventuallyEq
      filter_upwards [(e.open_source.prod isOpen_univ).mem_nhds ⟨hxs, mem_univ t⟩] with q hq
      exact hHsrc q.1 q.2 hq.1
    · have hxK : x ∉ e.symm '' slideSupport := by
        rintro ⟨y, hy, rfl⟩
        exact hxs (e.map_target (hsupp hy))
      apply continuous_fst.continuousAt.congr_of_eventuallyEq
      filter_upwards [(hKc.isOpen_compl.prod isOpen_univ).mem_nhds ⟨hxK, mem_univ t⟩] with q hq
      exact hHout q.1 q.2 hq.1
  · intro x
    by_cases hxs : x ∈ e.source
    · rw [hHsrc x 0 hxs]
      change e.symm (slideMapAt 0 (e x)) = x
      rw [slideMapAt_zero, e.left_inv hxs]
    · exact e.conjugateMap_of_notMem _ hxs
  · intro x
    change e.conjugateMap (slideMapAt 1) x = e.conjugateMap slideMap x
    congr 1
    funext p
    exact slideMapAt_one p
  · exact hcoord hSf (Bm := {p | p.2.2 = 0}) fun p t => Iff.rfl
  · exact hcoord hY (Bm := {p | 0 ≤ p.2.2}) fun p t => Iff.rfl
  · have hmap : MapsTo slideMap e.target e.target := mapsTo_slideMap_of_subset hsupp
    refine ⟨e.injective_conjugateMap injective_slideMap hmap, fun y => ?_⟩
    by_cases hys : y ∈ e.source
    · obtain ⟨p, hp⟩ := surjective_slideMap (e y)
      have hpt : p ∈ e.target := by
        by_cases hps : p ∈ slideSupport
        · exact hsupp hps
        · have hfix : slideMap p = p := eqOn_slideMap_id_compl hps
          rw [hfix] at hp
          rw [hp]
          exact e.map_source hys
      refine ⟨e.symm p, ?_⟩
      rw [e.conjugateMap_of_mem _ (e.map_target hpt), e.right_inv hpt, hp, e.left_inv hys]
    · exact ⟨y, e.conjugateMap_of_notMem _ hys⟩
  · have hmap : MapsTo slideMap e.target e.target := mapsTo_slideMap_of_subset hsupp
    ext z
    constructor
    · rintro ⟨⟨x, hxTr, rfl⟩, hzC⟩
      by_cases hxs : x ∈ e.source
      · exfalso
        have hin : e.conjugateMap slideMap x ∈ e.source := by
          rw [e.conjugateMap_of_mem _ hxs]
          exact e.map_target (hmap (e.map_source hxs))
        have hval : e (e.conjugateMap slideMap x) = slideMap (e x) := by
          rw [e.conjugateMap_of_mem _ hxs, e.right_inv (hmap (e.map_source hxs))]
        have h1 := ((hC _ hin).mp hzC).1
        rw [hval] at h1
        obtain ⟨h2, h3⟩ := (hTr x hxs).mp hxTr
        have := slideMap_fst_le_of_tent h2 h3
        linarith
      · rw [e.conjugateMap_of_notMem _ hxs] at hzC ⊢
        exact ⟨⟨hxTr, hzC⟩, hxs⟩
    · rintro ⟨⟨hzTr, hzC⟩, hzs⟩
      exact ⟨⟨z, hzTr, e.conjugateMap_of_notMem _ hzs⟩, hzC⟩

end DifferentialGeometry.Topology.PiecewiseLinear
