/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Filter Set Topology

noncomputable section

universe u v

namespace DifferentialGeometry.Topology

def realNormalSide (t : ℝ) : Bool :=
  decide (t < 0)

@[simp]
theorem realNormalSide_eq_true_iff {t : ℝ} : realNormalSide t = true ↔ t < 0 := by
  simp [realNormalSide]

@[simp]
theorem realNormalSide_eq_false_iff {t : ℝ} : realNormalSide t = false ↔ 0 ≤ t := by
  simp [realNormalSide]

theorem realNormalSide_eq_false_of_pos {t : ℝ} (ht : 0 < t) :
    realNormalSide t = false := by
  simp [ht.le]

theorem realNormalSide_eq_true_of_neg {t : ℝ} (ht : t < 0) :
    realNormalSide t = true := by
  simp [ht]

def HasNormalSideFlipAt
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph (X × ℝ) (Y × ℝ)) (x : X) (flip : Bool) : Prop :=
  ∀ᶠ q in 𝓝 (x, 0), q.2 ≠ 0 →
    q ∈ e.source ∧ realNormalSide (e q).2 = Bool.xor (realNormalSide q.2) flip

namespace OpenPartialHomeomorph

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (e : OpenPartialHomeomorph (X × ℝ) (Y × ℝ))

theorem existsUnique_hasNormalSideFlipAt
    {x : X} (hx : (x, 0) ∈ e.source)
    (hzero : ∀ q ∈ e.source, (e q).2 = 0 ↔ q.2 = 0) :
    ∃! flip : Bool, HasNormalSideFlipAt e x flip := by
  obtain ⟨U, hU, V, hV, hUV⟩ :=
    mem_nhds_prod_iff.mp (e.open_source.mem_nhds hx)
  obtain ⟨l, r, hzeroIoo, hIooV⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp hV
  have hxU : x ∈ U := mem_of_mem_nhds hU
  have hrectangle : U ×ˢ Ioo l r ⊆ e.source := by
    rintro ⟨y, t⟩ ⟨hy, ht⟩
    exact hUV ⟨hy, hIooV ht⟩
  let tP : ℝ := r / 2
  let tN : ℝ := l / 2
  have htP : tP ∈ Ioo (0 : ℝ) r := by
    dsimp [tP]
    constructor <;> linarith [hzeroIoo.2]
  have htPIoo : tP ∈ Ioo l r := ⟨hzeroIoo.1.trans htP.1, htP.2⟩
  have htN : tN ∈ Ioo l (0 : ℝ) := by
    dsimp [tN]
    constructor <;> linarith [hzeroIoo.1]
  have htNIoo : tN ∈ Ioo l r := ⟨htN.1, htN.2.trans hzeroIoo.2⟩
  have hxtP : (x, tP) ∈ e.source := hrectangle ⟨hxU, htPIoo⟩
  have hxtN : (x, tN) ∈ e.source := hrectangle ⟨hxU, htNIoo⟩
  have hePne : (e (x, tP)).2 ≠ 0 := by
    intro h
    exact htP.1.ne' ((hzero (x, tP) hxtP).mp h)
  have heNne : (e (x, tN)).2 ≠ 0 := by
    intro h
    exact htN.2.ne ((hzero (x, tN) hxtN).mp h)
  have hePcont : ContinuousAt (fun y : X ↦ (e (y, tP)).2) x := by
    have hpair : ContinuousAt (fun y : X ↦ e (y, tP)) x :=
      (e.continuousAt hxtP).comp₂ continuousAt_id continuousAt_const
    exact hpair.snd
  have heNcont : ContinuousAt (fun y : X ↦ (e (y, tN)).2) x := by
    have hpair : ContinuousAt (fun y : X ↦ e (y, tN)) x :=
      (e.continuousAt hxtN).comp₂ continuousAt_id continuousAt_const
    exact hpair.snd
  have positive_fiber_pos
      {y : X} (hy : y ∈ U) (hsample : 0 < (e (y, tP)).2)
      {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) r) : 0 < (e (y, t)).2 := by
    have hmaps : MapsTo (fun s : ℝ ↦ (y, s)) (Ioo (0 : ℝ) r) e.source := by
      intro s hs
      exact hrectangle ⟨hy, ⟨hzeroIoo.1.trans hs.1, hs.2⟩⟩
    have hcont : ContinuousOn (fun s : ℝ ↦ (e (y, s)).2) (Ioo (0 : ℝ) r) := by
      exact (e.continuousOn.comp (continuousOn_const.prodMk continuousOn_id) hmaps).snd
    have hne : ∀ s ∈ Ioo (0 : ℝ) r, (e (y, s)).2 ≠ 0 := by
      intro s hs h
      exact hs.1.ne' ((hzero (y, s) (hmaps hs)).mp h)
    exact isPreconnected_Ioo.lt_of_ne hcont hne ⟨tP, htP, hsample⟩ ht
  have positive_fiber_neg
      {y : X} (hy : y ∈ U) (hsample : (e (y, tP)).2 < 0)
      {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) r) : (e (y, t)).2 < 0 := by
    have hmaps : MapsTo (fun s : ℝ ↦ (y, s)) (Ioo (0 : ℝ) r) e.source := by
      intro s hs
      exact hrectangle ⟨hy, ⟨hzeroIoo.1.trans hs.1, hs.2⟩⟩
    have hcont : ContinuousOn (fun s : ℝ ↦ (e (y, s)).2) (Ioo (0 : ℝ) r) := by
      exact (e.continuousOn.comp (continuousOn_const.prodMk continuousOn_id) hmaps).snd
    have hne : ∀ s ∈ Ioo (0 : ℝ) r, (e (y, s)).2 ≠ 0 := by
      intro s hs h
      exact hs.1.ne' ((hzero (y, s) (hmaps hs)).mp h)
    exact isPreconnected_Ioo.gt_of_ne hcont hne ⟨tP, htP, hsample⟩ ht
  have negative_fiber_pos
      {y : X} (hy : y ∈ U) (hsample : 0 < (e (y, tN)).2)
      {t : ℝ} (ht : t ∈ Ioo l (0 : ℝ)) : 0 < (e (y, t)).2 := by
    have hmaps : MapsTo (fun s : ℝ ↦ (y, s)) (Ioo l (0 : ℝ)) e.source := by
      intro s hs
      exact hrectangle ⟨hy, ⟨hs.1, hs.2.trans hzeroIoo.2⟩⟩
    have hcont : ContinuousOn (fun s : ℝ ↦ (e (y, s)).2) (Ioo l (0 : ℝ)) := by
      exact (e.continuousOn.comp (continuousOn_const.prodMk continuousOn_id) hmaps).snd
    have hne : ∀ s ∈ Ioo l (0 : ℝ), (e (y, s)).2 ≠ 0 := by
      intro s hs h
      exact hs.2.ne ((hzero (y, s) (hmaps hs)).mp h)
    exact isPreconnected_Ioo.lt_of_ne hcont hne ⟨tN, htN, hsample⟩ ht
  have negative_fiber_neg
      {y : X} (hy : y ∈ U) (hsample : (e (y, tN)).2 < 0)
      {t : ℝ} (ht : t ∈ Ioo l (0 : ℝ)) : (e (y, t)).2 < 0 := by
    have hmaps : MapsTo (fun s : ℝ ↦ (y, s)) (Ioo l (0 : ℝ)) e.source := by
      intro s hs
      exact hrectangle ⟨hy, ⟨hs.1, hs.2.trans hzeroIoo.2⟩⟩
    have hcont : ContinuousOn (fun s : ℝ ↦ (e (y, s)).2) (Ioo l (0 : ℝ)) := by
      exact (e.continuousOn.comp (continuousOn_const.prodMk continuousOn_id) hmaps).snd
    have hne : ∀ s ∈ Ioo l (0 : ℝ), (e (y, s)).2 ≠ 0 := by
      intro s hs h
      exact hs.2.ne ((hzero (y, s) (hmaps hs)).mp h)
    exact isPreconnected_Ioo.gt_of_ne hcont hne ⟨tN, htN, hsample⟩ ht
  have himageZero : (e (x, 0)).2 = 0 := (hzero (x, 0) hx).mpr rfl
  have target_preimages (A : Set X) (hA : A ∈ 𝓝 x) :
      ∃ a b : ℝ, 0 ∈ Ioo a b ∧
        ∀ {s : ℝ}, s ∈ Ioo a b →
          ((e (x, 0)).1, s) ∈ e.target ∧
            e.symm ((e (x, 0)).1, s) ∈ A ×ˢ Ioo l r ∧
            e (e.symm ((e (x, 0)).1, s)) = ((e (x, 0)).1, s) := by
    have hrectangle_mem : A ×ˢ Ioo l r ∈ 𝓝 (x, 0) :=
      prod_mem_nhds hA (Ioo_mem_nhds hzeroIoo.1 hzeroIoo.2)
    have hinverse_rectangle : e.symm ⁻¹' (A ×ˢ Ioo l r) ∈ 𝓝 (e (x, 0)) :=
      e.tendsto_symm hx hrectangle_mem
    have htarget_inverse :
        e.target ∩ e.symm ⁻¹' (A ×ˢ Ioo l r) ∈ 𝓝 (e (x, 0)) :=
      inter_mem (e.open_target.mem_nhds (e.map_source hx)) hinverse_rectangle
    obtain ⟨W, hW, Z, hZ, hWZ⟩ := mem_nhds_prod_iff.mp htarget_inverse
    change Z ∈ 𝓝 (e (x, 0)).2 at hZ
    rw [himageZero] at hZ
    obtain ⟨a, b, hzeroTarget, hIooZ⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp hZ
    have hbaseW : (e (x, 0)).1 ∈ W := mem_of_mem_nhds hW
    refine ⟨a, b, hzeroTarget, ?_⟩
    intro s hs
    have hsZ : s ∈ Z := hIooZ hs
    have hsWZ : ((e (x, 0)).1, s) ∈ W ×ˢ Z := ⟨hbaseW, hsZ⟩
    have hmem := hWZ hsWZ
    exact ⟨hmem.1, hmem.2, e.right_inv hmem.1⟩
  have hexists : ∃ flip : Bool, HasNormalSideFlipAt e x flip := by
    rcases lt_or_gt_of_ne hePne with hePneg | hePpos
    · have hePevent : ∀ᶠ y in 𝓝 x, (e (y, tP)).2 < 0 :=
        hePcont.eventually_lt_const hePneg
      rcases lt_or_gt_of_ne heNne with heNneg | heNpos
      · exfalso
        have heNevent : ∀ᶠ y in 𝓝 x, (e (y, tN)).2 < 0 :=
          heNcont.eventually_lt_const heNneg
        let A : Set X :=
          {y | y ∈ U ∧ (e (y, tP)).2 < 0 ∧ (e (y, tN)).2 < 0}
        have hA : A ∈ 𝓝 x := by
          filter_upwards [hU, hePevent, heNevent] with y hy hpy hny
          exact ⟨hy, hpy, hny⟩
        obtain ⟨a, b, hzeroTarget, target_preimage⟩ := target_preimages A hA
        let s : ℝ := b / 2
        have hs : s ∈ Ioo a b := by
          dsimp [s]
          constructor <;> linarith [hzeroTarget.1, hzeroTarget.2]
        have hspos : 0 < s := by
          dsimp [s]
          linarith [hzeroTarget.2]
        obtain ⟨hzTarget, hqRect, hright⟩ := target_preimage hs
        let q := e.symm ((e (x, 0)).1, s)
        have hqSource : q ∈ e.source := e.map_target hzTarget
        have hqne : q.2 ≠ 0 := by
          intro hqzero
          have houtzero := (hzero q hqSource).mpr hqzero
          rw [hright] at houtzero
          exact hspos.ne' (by simpa only [Prod.snd] using houtzero)
        rcases lt_or_gt_of_ne hqne with hqneg | hqpos
        · have houtneg :=
            negative_fiber_neg hqRect.1.1 hqRect.1.2.2 ⟨hqRect.2.1, hqneg⟩
          rw [hright] at houtneg
          exact (not_lt_of_ge hspos.le) (by simpa only [Prod.snd] using houtneg)
        · have houtneg :=
            positive_fiber_neg hqRect.1.1 hqRect.1.2.1 ⟨hqpos, hqRect.2.2⟩
          rw [hright] at houtneg
          exact (not_lt_of_ge hspos.le) (by simpa only [Prod.snd] using houtneg)
      · have heNevent : ∀ᶠ y in 𝓝 x, 0 < (e (y, tN)).2 :=
          heNcont.eventually_const_lt heNpos
        refine ⟨true, ?_⟩
        have hbase : ∀ᶠ y in 𝓝 x,
            y ∈ U ∧ (e (y, tP)).2 < 0 ∧ 0 < (e (y, tN)).2 := by
          filter_upwards [hU, hePevent, heNevent] with y hy hpy hny
          exact ⟨hy, hpy, hny⟩
        filter_upwards [hbase.prod_nhds (Ioo_mem_nhds hzeroIoo.1 hzeroIoo.2)]
          with q hq hqne
        refine ⟨hrectangle ⟨hq.1.1, hq.2⟩, ?_⟩
        rcases lt_or_gt_of_ne hqne with hqneg | hqpos
        · have hout := negative_fiber_pos hq.1.1 hq.1.2.2 ⟨hq.2.1, hqneg⟩
          rw [realNormalSide_eq_true_of_neg hqneg,
            realNormalSide_eq_false_of_pos hout]
          decide
        · have hout := positive_fiber_neg hq.1.1 hq.1.2.1 ⟨hqpos, hq.2.2⟩
          rw [realNormalSide_eq_false_of_pos hqpos,
            realNormalSide_eq_true_of_neg hout]
          decide
    · have hePevent : ∀ᶠ y in 𝓝 x, 0 < (e (y, tP)).2 :=
        hePcont.eventually_const_lt hePpos
      rcases lt_or_gt_of_ne heNne with heNneg | heNpos
      · have heNevent : ∀ᶠ y in 𝓝 x, (e (y, tN)).2 < 0 :=
          heNcont.eventually_lt_const heNneg
        refine ⟨false, ?_⟩
        have hbase : ∀ᶠ y in 𝓝 x,
            y ∈ U ∧ 0 < (e (y, tP)).2 ∧ (e (y, tN)).2 < 0 := by
          filter_upwards [hU, hePevent, heNevent] with y hy hpy hny
          exact ⟨hy, hpy, hny⟩
        filter_upwards [hbase.prod_nhds (Ioo_mem_nhds hzeroIoo.1 hzeroIoo.2)]
          with q hq hqne
        refine ⟨hrectangle ⟨hq.1.1, hq.2⟩, ?_⟩
        rcases lt_or_gt_of_ne hqne with hqneg | hqpos
        · have hout := negative_fiber_neg hq.1.1 hq.1.2.2 ⟨hq.2.1, hqneg⟩
          rw [realNormalSide_eq_true_of_neg hqneg,
            realNormalSide_eq_true_of_neg hout]
          decide
        · have hout := positive_fiber_pos hq.1.1 hq.1.2.1 ⟨hqpos, hq.2.2⟩
          rw [realNormalSide_eq_false_of_pos hqpos,
            realNormalSide_eq_false_of_pos hout]
          decide
      · exfalso
        have heNevent : ∀ᶠ y in 𝓝 x, 0 < (e (y, tN)).2 :=
          heNcont.eventually_const_lt heNpos
        let A : Set X :=
          {y | y ∈ U ∧ 0 < (e (y, tP)).2 ∧ 0 < (e (y, tN)).2}
        have hA : A ∈ 𝓝 x := by
          filter_upwards [hU, hePevent, heNevent] with y hy hpy hny
          exact ⟨hy, hpy, hny⟩
        obtain ⟨a, b, hzeroTarget, target_preimage⟩ := target_preimages A hA
        let s : ℝ := a / 2
        have hs : s ∈ Ioo a b := by
          dsimp [s]
          constructor <;> linarith [hzeroTarget.1, hzeroTarget.2]
        have hsneg : s < 0 := by
          dsimp [s]
          linarith [hzeroTarget.1]
        obtain ⟨hzTarget, hqRect, hright⟩ := target_preimage hs
        let q := e.symm ((e (x, 0)).1, s)
        have hqSource : q ∈ e.source := e.map_target hzTarget
        have hqne : q.2 ≠ 0 := by
          intro hqzero
          have houtzero := (hzero q hqSource).mpr hqzero
          rw [hright] at houtzero
          exact hsneg.ne (by simpa only [Prod.snd] using houtzero)
        rcases lt_or_gt_of_ne hqne with hqneg | hqpos
        · have houtpos :=
            negative_fiber_pos hqRect.1.1 hqRect.1.2.2 ⟨hqRect.2.1, hqneg⟩
          rw [hright] at houtpos
          exact (not_lt_of_ge hsneg.le) (by simpa only [Prod.snd] using houtpos)
        · have houtpos :=
            positive_fiber_pos hqRect.1.1 hqRect.1.2.1 ⟨hqpos, hqRect.2.2⟩
          rw [hright] at houtpos
          exact (not_lt_of_ge hsneg.le) (by simpa only [Prod.snd] using houtpos)
  obtain ⟨flip, hflip⟩ := hexists
  refine ⟨flip, hflip, ?_⟩
  intro other hother
  have hboth := hflip.and hother
  have htime : ∀ᶠ t in 𝓝 (0 : ℝ),
      (t ≠ 0 →
        (x, t) ∈ e.source ∧
          realNormalSide (e (x, t)).2 = Bool.xor (realNormalSide t) flip) ∧
      (t ≠ 0 →
        (x, t) ∈ e.source ∧
          realNormalSide (e (x, t)).2 = Bool.xor (realNormalSide t) other) :=
    hboth.curry_nhds.self_of_nhds
  obtain ⟨c, d, hzeroCD, hCD⟩ := htime.exists_Ioo_subset
  let t : ℝ := d / 2
  have ht : t ∈ Ioo c d := by
    dsimp [t]
    constructor <;> linarith [hzeroCD.1, hzeroCD.2]
  have htne : t ≠ 0 := by
    dsimp [t]
    linarith [hzeroCD.2]
  obtain ⟨hflipAt, hotherAt⟩ := hCD ht
  obtain ⟨_, hflipEq⟩ := hflipAt htne
  obtain ⟨_, hotherEq⟩ := hotherAt htne
  have heq : Bool.xor (realNormalSide t) flip =
      Bool.xor (realNormalSide t) other := hflipEq.symm.trans hotherEq
  cases realNormalSide t <;> simpa using heq.symm

theorem hasNormalSideFlipAt_of_eqOn
    (f : OpenPartialHomeomorph (X × ℝ) (Y × ℝ))
    {x : X} {flip : Bool}
    (hfx : (x, 0) ∈ f.source)
    (heq : ∀ q, q ∈ e.source → q ∈ f.source → e q = f q)
    (he : HasNormalSideFlipAt e x flip) :
    HasNormalSideFlipAt f x flip := by
  filter_upwards [he, f.open_source.mem_nhds hfx] with q heqSide hqf hqne
  obtain ⟨hqe, hside⟩ := heqSide hqne
  refine ⟨hqf, ?_⟩
  rw [← heq q hqe hqf]
  exact hside

theorem zeroLocus_iff_zero_trans
    {Z : Type*} [TopologicalSpace Z]
    (f : OpenPartialHomeomorph (Y × ℝ) (Z × ℝ))
    (he : ∀ q ∈ e.source, (e q).2 = 0 ↔ q.2 = 0)
    (hf : ∀ q ∈ f.source, (f q).2 = 0 ↔ q.2 = 0) :
    ∀ q ∈ (e.trans f).source, ((e.trans f) q).2 = 0 ↔ q.2 = 0 := by
  intro q hq
  rw [OpenPartialHomeomorph.trans_source] at hq
  exact (hf (e q) hq.2).trans (he q hq.1)

theorem hasNormalSideFlipAt_trans
    {Z : Type*} [TopologicalSpace Z]
    (f : OpenPartialHomeomorph (Y × ℝ) (Z × ℝ))
    {x : X} {flipE flipF : Bool}
    (hx : (x, 0) ∈ e.source)
    (heZero : ∀ q ∈ e.source, (e q).2 = 0 ↔ q.2 = 0)
    (he : HasNormalSideFlipAt e x flipE)
    (hf : HasNormalSideFlipAt f (e (x, 0)).1 flipF) :
    HasNormalSideFlipAt (e.trans f) x (Bool.xor flipE flipF) := by
  have himageZero : (e (x, 0)).2 = 0 := (heZero (x, 0) hx).mpr rfl
  have hcenter : ((e (x, 0)).1, 0) = e (x, 0) := by
    exact Prod.ext rfl himageZero.symm
  unfold HasNormalSideFlipAt at hf
  rw [hcenter] at hf
  have hfpull : ∀ᶠ q in 𝓝 (x, 0),
      (e q).2 ≠ 0 →
        e q ∈ f.source ∧
          realNormalSide (f (e q)).2 = Bool.xor (realNormalSide (e q).2) flipF :=
    (e.continuousAt hx).eventually hf
  filter_upwards [he, hfpull] with q heq hfq hqne
  obtain ⟨hqSource, hqSide⟩ := heq hqne
  have heqne : (e q).2 ≠ 0 := by
    intro h
    exact hqne ((heZero q hqSource).mp h)
  obtain ⟨heqSource, heqSide⟩ := hfq heqne
  constructor
  · rw [OpenPartialHomeomorph.trans_source]
    exact ⟨hqSource, heqSource⟩
  · change realNormalSide (f (e q)).2 =
      Bool.xor (realNormalSide q.2) (Bool.xor flipE flipF)
    rw [heqSide, hqSide, Bool.xor_assoc]

def zeroSectionSource : Set X :=
  {x | (x, 0) ∈ e.source}

theorem isOpen_zeroSectionSource : IsOpen (zeroSectionSource e) := by
  exact (e.open_source).preimage (continuous_id.prodMk continuous_const)

noncomputable def normalSideFlipAt
    (hzero : ∀ q ∈ e.source, (e q).2 = 0 ↔ q.2 = 0)
    (x : zeroSectionSource e) : Bool :=
  Classical.choose (existsUnique_hasNormalSideFlipAt e x.2 hzero)

theorem hasNormalSideFlipAt_normalSideFlipAt
    (hzero : ∀ q ∈ e.source, (e q).2 = 0 ↔ q.2 = 0)
    (x : zeroSectionSource e) :
    HasNormalSideFlipAt e x.1 (normalSideFlipAt e hzero x) :=
  (Classical.choose_spec (existsUnique_hasNormalSideFlipAt e x.2 hzero)).1

theorem isLocallyConstant_normalSideFlipAt
    (hzero : ∀ q ∈ e.source, (e q).2 = 0 ↔ q.2 = 0) :
    IsLocallyConstant (normalSideFlipAt e hzero) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  have hxflip := hasNormalSideFlipAt_normalSideFlipAt e hzero x
  obtain ⟨U, V, hUopen, hxU, hVopen, hzeroV, hUV⟩ :=
    mem_nhds_prod_iff'.mp hxflip
  let USub : Set (zeroSectionSource e) := Subtype.val ⁻¹' U
  have hUSubOpen : IsOpen USub := hUopen.preimage continuous_subtype_val
  have hxUSub : x ∈ USub := hxU
  refine ⟨USub, hUSubOpen, hxUSub, ?_⟩
  intro y hy
  have hcandidate : HasNormalSideFlipAt e y.1 (normalSideFlipAt e hzero x) := by
    apply mem_of_superset
      (prod_mem_nhds (hUopen.mem_nhds hy) (hVopen.mem_nhds hzeroV))
    intro q hq
    exact hUV hq
  have hcanonical := hasNormalSideFlipAt_normalSideFlipAt e hzero y
  exact (existsUnique_hasNormalSideFlipAt e y.2 hzero).unique hcanonical hcandidate

end OpenPartialHomeomorph

end DifferentialGeometry.Topology
