/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.External.Schoenflies.PolyArcRealize
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.CompactGluing
import DifferentialGeometry.Topology.PlanarJordan.RegularCurve
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph

open Set Topology

namespace Schoenflies

theorem exists_hasArcCollars_of_polygonal_subarc
    {f : ℝ → Plane} (hf : ContinuousOn f unitInterval) (hi : InjOn f unitInterval)
    {a b : ℝ} (ha : a ∈ unitInterval) (hb : b ∈ unitInterval) (hab : a < b)
    (hpoly : IsPolygonal (f '' Icc a b)) {U : Set Plane} (hU : IsOpen U)
    (hsub : f '' Ioo a b ⊆ U) :
    ∃ V : Set Plane, IsOpen V ∧ V ⊆ U ∧ f '' Ioo a b ⊆ V ∧
      V ∩ f '' unitInterval = f '' Ioo a b ∧ HasArcCollars V (f '' unitInterval) := by
  let Z := f '' Icc 0 a ∪ f '' Icc b 1
  have hZ : IsClosed Z :=
    ((isCompact_Icc.image_of_continuousOn (hf.mono (Icc_subset_Icc_right ha.2))).union
      (isCompact_Icc.image_of_continuousOn (hf.mono (Icc_subset_Icc_left hb.1)))).isClosed
  let V := U \ Z
  have hV : IsOpen V := hU.sdiff hZ
  have hIV : f '' Ioo a b ⊆ V := by
    rintro x ⟨t, ht, rfl⟩
    have htI : t ∈ unitInterval := ⟨ha.1.trans ht.1.le, ht.2.le.trans hb.2⟩
    refine ⟨hsub (mem_image_of_mem f ht), ?_⟩
    rintro (⟨s, hs, heq⟩ | ⟨s, hs, heq⟩)
    · have hst := hi ⟨hs.1, hs.2.trans ha.2⟩ htI heq
      exact ht.1.not_ge (hst ▸ hs.2)
    · have hst := hi ⟨hb.1.trans hs.1, hs.2⟩ htI heq
      exact ht.2.not_ge (hst ▸ hs.1)
  have hVA : V ∩ f '' unitInterval = f '' Ioo a b := by
    apply Subset.antisymm
    · rintro x ⟨hx, t, ht, rfl⟩
      refine mem_image_of_mem f ⟨?_, ?_⟩
      · by_contra h
        exact hx.2 (Or.inl (mem_image_of_mem f ⟨ht.1, not_lt.mp h⟩))
      · by_contra h
        exact hx.2 (Or.inr (mem_image_of_mem f ⟨not_lt.mp h, ht.2⟩))
    · intro x hx
      exact ⟨hIV hx, (image_mono (Ioo_subset_Icc_self.trans (Icc_subset_Icc ha.1 hb.2))) hx⟩
  have hfa : f a ∉ V := fun hx => hx.2 (Or.inl (mem_image_of_mem f ⟨ha.1, le_rfl⟩))
  have hfb : f b ∉ V := fun hx => hx.2 (Or.inr (mem_image_of_mem f ⟨le_rfl, hb.2⟩))
  have hP : IsArcBetween (f '' Icc a b) (f a) (f b) := by
    simpa only [uIcc_of_le hab.le] using isArcBetween_subarc_of_injOn_I hf hi ha hb hab.ne
  have hPD : (f '' Icc a b) \ {f a, f b} ⊆ V := by
    rintro x ⟨⟨t, ht, rfl⟩, hends⟩
    apply hIV
    refine mem_image_of_mem f ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩
    · intro hat
      exact hends (Or.inl (congrArg f hat.symm))
    · intro htb
      exact hends (Or.inr (congrArg f htb))
  have hlocal := hasArcCollars_of_isPolygonal hV hfa hfb hPD hP hpoly
  refine ⟨V, hV, sdiff_subset, hIV, hVA, ?_⟩
  intro K hK hKcompact hKconn hKnt
  have hKP : K ⊆ V ∩ f '' Icc a b := fun x hx =>
    ⟨(hK hx).1, image_mono Ioo_subset_Icc_self (hVA.subset (hK hx))⟩
  obtain ⟨C⟩ := hlocal K hKP hKcompact hKconn hKnt
  have hdiff : C.nbhd \ f '' unitInterval = C.nbhd \ f '' Icc a b := by
    apply Subset.antisymm
    · exact sdiff_subset_sdiff Subset.rfl (image_mono (Icc_subset_Icc ha.1 hb.2))
    · rintro x ⟨hx, hnot⟩
      refine ⟨hx, fun hA => hnot ?_⟩
      exact image_mono Ioo_subset_Icc_self (hVA.subset ⟨C.nbhd_subset hx, hA⟩)
  exact ⟨{
    nbhd := C.nbhd
    left := C.left
    right := C.right
    isOpen_nbhd := C.isOpen_nbhd
    subset_nbhd := C.subset_nbhd
    nbhd_subset := C.nbhd_subset
    nbhd_diff := hdiff.trans C.nbhd_diff
    isConnected_left := C.isConnected_left
    isConnected_right := C.isConnected_right
    subset_closure_left := C.subset_closure_left
    subset_closure_right := C.subset_closure_right }⟩

open Classical in
theorem ArcCollar.exists_isOpen_connected_chain
    {P : Set Plane} (hP : IsClosed P) {D K : ℕ → Set Plane}
    (hD : ∀ n, IsOpen (D n)) (C : ∀ n, ArcCollar (D n) P (K n))
    (hK : ∀ n, (K n ∩ K (n + 1)).Nonempty) :
    ∃ O : ℕ → Set Plane,
      (∀ n, IsOpen (O n) ∧ IsConnected (O n) ∧ O n ⊆ D n \ P ∧ K n ⊆ closure (O n)) ∧
      ∀ n, (O n ∩ O (n + 1)).Nonempty := by
  let T (n : ℕ) (b : Bool) : Set Plane := Bool.rec (C n).left (C n).right b
  have hT (n : ℕ) (b : Bool) :
      IsConnected (T n b) ∧ T n b ⊆ D n \ P ∧ K n ⊆ closure (T n b) := by
    cases b with
    | false => exact ⟨(C n).isConnected_left, (C n).left_subset_diff, (C n).subset_closure_left⟩
    | true => exact ⟨(C n).isConnected_right, (C n).right_subset_diff, (C n).subset_closure_right⟩
  have hstep (n : ℕ) (b : Bool) : ∃ c : Bool, (T n b ∩ T (n + 1) c).Nonempty := by
    obtain ⟨x, hx, hx'⟩ := hK n
    obtain ⟨y, hyN, hyT⟩ := mem_closure_iff.mp ((hT n b).2.2 hx)
      (C (n + 1)).nbhd (C (n + 1)).isOpen_nbhd ((C (n + 1)).subset_nbhd hx')
    have hy := (C (n + 1)).nbhd_diff.subset ⟨hyN, ((hT n b).2.1 hyT).2⟩
    rcases hy with hy | hy
    · exact ⟨false, y, hyT, hy⟩
    · exact ⟨true, y, hyT, hy⟩
  choose next hnext using hstep
  let b : ℕ → Bool := Nat.rec false (fun n c => next n c)
  choose z hz using fun n => (hT n (b n)).1.nonempty
  let O (n : ℕ) := connectedComponentIn (D n \ P) (z n)
  have hTO (n : ℕ) : T n (b n) ⊆ O n :=
    (hT n (b n)).1.isPreconnected.subset_connectedComponentIn (hz n) (hT n (b n)).2.1
  refine ⟨O, ?_, ?_⟩
  · intro n
    exact ⟨Plane.isOpen_connectedComponentIn ((hD n).sdiff hP),
      isConnected_connectedComponentIn_iff.mpr ((hT n (b n)).2.1 (hz n)),
      connectedComponentIn_subset _ _, (hT n (b n)).2.2.trans (closure_mono (hTO n))⟩
  · intro n
    have hmeet : (T n (b n) ∩ T (n + 1) (b (n + 1))).Nonempty := hnext n (b n)
    exact hmeet.mono (inter_subset_inter (hTO n) (hTO (n + 1)))
end Schoenflies

open Schoenflies
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.PlanarJordan

private theorem exists_neighborhood_inside_iff_of_nonneg
    {C U : Set Plane} {a : Plane} {f : Plane → ℝ}
    (hC : IsSeparating C) (hU : IsOpen U) (haC : a ∈ C) (haU : a ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (hzero : ∀ x ∈ U, x ∈ C ↔ f x = 0)
    (hr : fderiv ℝ f a ≠ 0)
    (hside : ∀ x ∈ U ∩ inside C, 0 ≤ f x) :
    ∃ V : Set Plane, IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧
      (∀ x ∈ V, x ∈ inside C ↔ 0 < f x) ∧
      (∀ x ∈ V, x ∈ closure (inside C) ↔ 0 ≤ f x) := by
  obtain ⟨V, g, hVo, haV, hVU, hchoice, _, _, _, hgin⟩ :=
    exists_signed_regular_defining_function hC hU haC haU hf hzero hr
  have hgf : g = f := by
    rcases hchoice with h | h
    · exact h
    · have haCl : a ∈ closure (inside C) :=
        frontier_subset_closure (hC.frontier_inside.symm ▸ haC)
      obtain ⟨x, hxV, hxin⟩ := mem_closure_iff.mp haCl V hVo haV
      have hn := hside x ⟨hVU hxV, hxin⟩
      have hp := (hgin x hxV).mp hxin
      simp only [h, Pi.neg_apply] at hp
      exact (not_lt_of_ge hn (neg_pos.mp hp)).elim
  subst g
  refine ⟨V, hVo, haV, hVU, hgin, ?_⟩
  intro x hx
  rw [(IsRegionOf.inside C).closure_eq hC, mem_union, hgin x hx,
    hzero x (hVU hx)]
  exact ⟨fun h => h.elim le_of_lt (fun h => h.ge), fun h => h.eq_or_lt.elim
    (fun h => Or.inr h.symm) Or.inl⟩

private theorem exists_bottom_arc_side_neighborhood
    (D : _root_.PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Plane) (ℝ × ℝ) Plane ∞)
    {β : ℝ → Plane} {f : Plane → ℝ} {a l r u : ℝ} {C N O : Set Plane}
    (hC : IsSeparating C) (hN : IsClosed N) (hCeq : C = N ∪ β '' Icc l r)
    (hbase : {a} ×ˢ Icc l r ⊆ D.source)
    (hDbase : ∀ v ∈ Icc l r, D (a, v) = β v)
    (hDO : D.target ⊆ O) (hf : ContDiffOn ℝ ∞ f O)
    (hDf : ∀ p ∈ D.source, f (D p) = p.1)
    (hu : u ∈ Ioo l r) (huN : β u ∉ N) (hreg : fderiv ℝ f (β u) ≠ 0)
    (hside : ∀ x ∈ inside C, a ≤ f x) :
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧ (a, u) ∈ V ∧ V ⊆ D.source ∧
      ∀ p ∈ V, D p ∈ closure (inside C) ↔ a ≤ p.1 := by
  let V : Set (ℝ × ℝ) := D.source ∩ (D ⁻¹' Nᶜ) ∩ (Prod.snd ⁻¹' Ioo l r)
  have hV : IsOpen V :=
    (D.toOpenPartialHomeomorph.isOpen_inter_preimage hN.isOpen_compl).inter
      (isOpen_Ioo.preimage continuous_snd)
  have hVs : V ⊆ D.source := fun p hp => hp.1.1
  have hau : (a, u) ∈ V :=
    ⟨⟨hbase ⟨rfl, hu.1.le, hu.2.le⟩, by
      change D (a, u) ∉ N;
      rw [hDbase u ⟨hu.1.le, hu.2.le⟩];
      exact huN⟩, hu⟩
  let U := D '' V
  have hU : IsOpen U := D.toOpenPartialHomeomorph.isOpen_image_of_subset_source hV hVs
  have hUO : U ⊆ O := by
    rintro x ⟨p, hp, rfl⟩
    exact hDO (D.map_source (hVs hp))
  have hβU : β u ∈ U := ⟨(a, u), hau, hDbase u ⟨hu.1.le, hu.2.le⟩⟩
  have hzero : ∀ x ∈ U, x ∈ C ↔ f x - a = 0 := by
    rintro x ⟨p, hp, rfl⟩
    rw [hDf p (hVs hp), sub_eq_zero, hCeq]
    constructor
    · rintro (hn | ⟨v, hv, heq⟩)
      · exact (hp.1.2 hn).elim
      · have he : D (a, v) = D p := (hDbase v hv).trans heq
        have hpp := D.toPartialEquiv.injOn
          (hbase (show (a, v) ∈ {a} ×ˢ Icc l r from ⟨rfl, hv⟩)) (hVs hp) he
        exact (congrArg Prod.fst hpp).symm
    · intro ht
      right
      refine ⟨p.2, ⟨hp.2.1.le, hp.2.2.le⟩, ?_⟩
      have he : (a, p.2) = p := Prod.ext ht.symm rfl
      exact (hDbase p.2 ⟨hp.2.1.le, hp.2.2.le⟩).symm.trans (congrArg D he)
  obtain ⟨W, hW, huW, hWU, _, hWin⟩ := exists_neighborhood_inside_iff_of_nonneg
    hC hU (hCeq ▸ Or.inr ⟨u, ⟨hu.1.le, hu.2.le⟩, rfl⟩) hβU
    ((hf.mono hUO).sub contDiffOn_const) hzero
    (by simpa only [fderiv_sub_const] using hreg)
    (fun x hx => sub_nonneg.mpr (hside x hx.2))
  refine ⟨D.source ∩ D ⁻¹' W, D.toOpenPartialHomeomorph.isOpen_inter_preimage hW,
    ⟨hbase ⟨rfl, hu.1.le, hu.2.le⟩, ?_⟩, inter_subset_left, ?_⟩
  · change D (a, u) ∈ W
    rwa [hDbase u ⟨hu.1.le, hu.2.le⟩]
  · intro p hp
    rw [hWin _ hp.2, sub_nonneg, hDf p hp.1]

theorem exists_partialDiffeomorph_isImage_level_arc
    (D χ : _root_.PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Plane) (ℝ × ℝ) Plane ∞)
    {β : ℝ → Plane} {f : Plane → ℝ} {a l r : ℝ} {C N O : Set Plane}
    {H : ℝ → ℝ} (hH : Continuous H) (hlr : l < r)
    (hHinner : ∀ u ∈ Ioo l r, a < H u)
    (hC : IsSeparating C) (hcut : IsCutPair C (β l) (β r) N (β '' Icc l r))
    (hβinj : InjOn β (Icc l r))
    (hbase : {a} ×ˢ Icc l r ⊆ D.source)
    (hDbase : ∀ u ∈ Icc l r, D (a, u) = β u)
    (hDO : D.target ⊆ O) (hf : ContDiffOn ℝ ∞ f O)
    (hDf : ∀ p ∈ D.source, f (D p) = p.1)
    (hreg : ∀ u ∈ Icc l r, fderiv ℝ f (β u) ≠ 0)
    (hside : ∀ x ∈ inside C, a ≤ f x)
    (hχ : χ.toOpenPartialHomeomorph.IsImage {p : ℝ × ℝ | a ≤ p.1 ∧ p.1 ≤ H p.2}
      (closure (inside C)))
    (hcorners : ∀ u ∈ ({l, r} : Set ℝ), (a, u) ∈ χ.source ∧
      (D : (ℝ × ℝ) → Plane) =ᶠ[𝓝 (a, u)] χ) :
    ∃ E : _root_.PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Plane) (ℝ × ℝ) Plane ∞,
      {a} ×ˢ Icc l r ⊆ E.source ∧ E.source ⊆ D.source ∧ E.target ⊆ D.target ∧
      (E : (ℝ × ℝ) → Plane) = D ∧
      E.toOpenPartialHomeomorph.IsImage {p : ℝ × ℝ | a ≤ p.1 ∧ p.1 ≤ H p.2}
        (closure (inside C)) := by
  classical
  have hlocal (u : ℝ) (hu : u ∈ Icc l r) :
      ∃ V : Set (ℝ × ℝ), IsOpen V ∧ (a, u) ∈ V ∧ V ⊆ D.source ∧
        ∀ p ∈ V, D p ∈ closure (inside C) ↔ a ≤ p.1 ∧ p.1 ≤ H p.2 := by
    have hau : (a, u) ∈ D.source := hbase ⟨rfl, hu⟩
    by_cases hend : u ∈ ({l, r} : Set ℝ)
    · obtain ⟨huχ, hDeq⟩ := hcorners u hend
      have hgood : ∀ᶠ p in 𝓝 (a, u), p ∈ D.source ∧
          (D p ∈ closure (inside C) ↔ a ≤ p.1 ∧ p.1 ≤ H p.2) := by
        filter_upwards [hDeq, χ.open_source.mem_nhds huχ,
          D.open_source.mem_nhds hau] with p he hpχ hpD
        exact ⟨hpD, he ▸ hχ hpχ⟩
      obtain ⟨V, hVs, hV, hauV⟩ := mem_nhds_iff.mp hgood
      exact ⟨V, hV, hauV, fun p hp => (hVs hp).1, fun p hp => (hVs hp).2⟩
    · have hul : u ≠ l := fun h => hend (Or.inl h)
      have hur : u ≠ r := fun h => hend (Or.inr h)
      have hui : u ∈ Ioo l r := ⟨lt_of_le_of_ne hu.1 hul.symm, lt_of_le_of_ne hu.2 hur⟩
      have huN : β u ∉ N := by
        intro huN
        have hpair : β u ∈ ({β l, β r} : Set Plane) := hcut.inter_eq ▸
          (show β u ∈ N ∩ β '' Icc l r from ⟨huN, ⟨u, hu, rfl⟩⟩)
        rcases hpair with he | he
        · exact hul (hβinj hu ⟨le_rfl, hlr.le⟩ he)
        · exact hur (hβinj hu ⟨hlr.le, le_rfl⟩ he)
      obtain ⟨V, hV, hauV, hVs, hVin⟩ := exists_bottom_arc_side_neighborhood D hC
        hcut.fst.isArc.isClosed hcut.union_eq.symm hbase hDbase hDO hf hDf hui huN (hreg u hu) hside
      refine ⟨V ∩ {p : ℝ × ℝ | p.1 < H p.2},
        hV.inter (isOpen_lt continuous_fst (hH.comp continuous_snd)),
        ⟨hauV, hHinner u hui⟩, fun p hp => hVs hp.1, ?_⟩
      intro p hp
      exact (hVin p hp.1).trans ⟨fun ha => ⟨ha, hp.2.le⟩, And.left⟩
  choose V hV hauV _ hVin using fun u : Icc l r => hlocal u u.property
  let U := ⋃ u : Icc l r, V u
  have hU : IsOpen U := isOpen_iUnion hV
  let E := DifferentialGeometry.Topology.PartialDiffeomorph.restrict D U hU
  refine ⟨E, ?_, inter_subset_left, inter_subset_left, rfl, ?_⟩
  · rintro ⟨t, u⟩ ⟨ht, hu⟩
    have ht' : t = a := ht
    subst t
    exact ⟨hbase ⟨rfl, hu⟩, mem_iUnion.mpr ⟨⟨u, hu⟩, hauV ⟨u, hu⟩⟩⟩
  · intro p hp
    obtain ⟨u, hu⟩ := mem_iUnion.mp hp.2
    exact hVin u p hu

theorem exists_partialDiffeomorph_of_band_boundary_collars
    (χ D : _root_.PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Plane) (ℝ × ℝ) Plane ∞)
    {a l r : ℝ} {H : ℝ → ℝ} (hlr : l < r) (hH : Continuous H)
    (hHl : H l = a) (hHr : H r = a) (hHinner : ∀ u ∈ Ioo l r, a < H u)
    {C N B Y : Set Plane} {f : Plane → ℝ}
    (hcut : IsCutPair C (χ (a, l)) (χ (a, r)) N B) :
    let K₀ := (fun u => (H u, u)) '' Icc l r
    let K₁ := {a} ×ˢ Icc l r
    let X := {p : ℝ × ℝ | a ≤ p.1 ∧ p.1 ≤ H p.2}
    K₀ ⊆ χ.source → K₁ ⊆ D.source → χ '' K₀ = N → D '' K₁ = B →
    χ.toOpenPartialHomeomorph.IsImage X Y → D.toOpenPartialHomeomorph.IsImage X Y →
    (∀ p ∈ χ.source, f (χ p) = p.1) → (∀ p ∈ D.source, f (D p) = p.1) →
    (∀ u ∈ ({l, r} : Set ℝ), (D : (ℝ × ℝ) → Plane) =ᶠ[𝓝 (a, u)] χ) →
    ∃ η : _root_.PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Plane) (ℝ × ℝ) Plane ∞,
      K₀ ∪ K₁ ⊆ η.source ∧ η '' (K₀ ∪ K₁) = C ∧
      η.toOpenPartialHomeomorph.IsImage X Y ∧
      (∀ p ∈ η.source, f (η p) = p.1) ∧
      (∀ p ∈ K₀, (η : (ℝ × ℝ) → Plane) =ᶠ[𝓝 p] χ) ∧
      (∀ p ∈ K₁, (η : (ℝ × ℝ) → Plane) =ᶠ[𝓝 p] D) := by
  intro K₀ K₁ X hχs hDs hχN hDB hχimage hDimage hχf hDf hcorners
  have hKl : (a, l) ∈ K₀ ∩ K₁ :=
    ⟨⟨l, ⟨le_rfl, hlr.le⟩, Prod.ext hHl rfl⟩, rfl, le_rfl, hlr.le⟩
  have hKr : (a, r) ∈ K₀ ∩ K₁ :=
    ⟨⟨r, ⟨hlr.le, le_rfl⟩, Prod.ext hHr rfl⟩, rfl, hlr.le, le_rfl⟩
  have hKinter : K₀ ∩ K₁ ⊆ ({(a, l), (a, r)} : Set (ℝ × ℝ)) := by
    rintro p ⟨⟨u, hu, rfl⟩, ha, _⟩
    have he : H u = a := ha
    by_cases hul : u = l
    · subst u; exact Or.inl (Prod.ext hHl rfl)
    by_cases hur : u = r
    · subst u; exact Or.inr (Prod.ext hHr rfl)
    exact ((hHinner u ⟨lt_of_le_of_ne hu.1 (Ne.symm hul), lt_of_le_of_ne hu.2 hur⟩).ne' he).elim
  obtain ⟨U, hUeq, hU, hlU⟩ := mem_nhds_iff.mp (hcorners l (by simp)).symm
  obtain ⟨V, hVeq, hV, hrV⟩ := mem_nhds_iff.mp (hcorners r (by simp)).symm
  have hKO : K₀ ∩ K₁ ⊆ U ∪ V := by
    intro p hp
    rcases hKinter hp with he | he
    · exact Or.inl (he ▸ hlU)
    · have he' : p = (a, r) := he
      exact Or.inr (he' ▸ hrV)
  have heq : EqOn χ D (U ∪ V) := fun p hp => hp.elim (fun hp => hUeq hp) (fun hp => hVeq hp)
  have himage : χ '' K₀ ∩ D '' K₁ ⊆ χ '' (K₀ ∩ K₁) := by
    intro y hy
    have hyends : y ∈ ({χ (a, l), χ (a, r)} : Set Plane) := by
      rw [hχN, hDB, hcut.inter_eq] at hy
      exact hy
    rcases hyends with he | he
    · exact ⟨(a, l), hKl, he.symm⟩
    · have he' : y = χ (a, r) := he
      exact ⟨(a, r), hKr, he'.symm⟩
  obtain ⟨ψ, U₀, U₁, hU₀, hU₁, hK₀U, hK₁U, hUs, hψχ, hψD⟩ :=
    _root_.PartialDiffeomorph.exists_eqOn_neighborhoods_of_isCompact χ D
      (isCompact_Icc.image (hH.prodMk continuous_id)) (isCompact_singleton.prod isCompact_Icc)
      hχs hDs (hU.union hV) hKO heq himage
  let W₀ := U₀ ∩ χ.source
  let W₁ := U₁ ∩ D.source
  have hW₀ : IsOpen W₀ := hU₀.inter χ.open_source
  have hW₁ : IsOpen W₁ := hU₁.inter D.open_source
  have hK₀W : K₀ ⊆ W₀ := fun p hp => ⟨hK₀U hp, hχs hp⟩
  have hK₁W : K₁ ⊆ W₁ := fun p hp => ⟨hK₁U hp, hDs hp⟩
  let η := DifferentialGeometry.Topology.PartialDiffeomorph.restrict ψ (W₀ ∪ W₁) (hW₀.union hW₁)
  have hηsrc : K₀ ∪ K₁ ⊆ η.source := by
    intro p hp
    rcases hp with hp | hp
    · exact ⟨hUs (Or.inl (hK₀U hp)), Or.inl (hK₀W hp)⟩
    · exact ⟨hUs (Or.inr (hK₁U hp)), Or.inr (hK₁W hp)⟩
  have hηχ : EqOn η χ W₀ := fun p hp => hψχ hp.1
  have hηD : EqOn η D W₁ := fun p hp => hψD hp.1
  refine ⟨η, hηsrc, ?_, ?_, ?_, ?_, ?_⟩
  · rw [image_union, image_congr (fun p hp => hηχ (hK₀W hp)),
      image_congr (fun p hp => hηD (hK₁W hp)), hχN, hDB, hcut.union_eq]
  · intro p hp
    rcases hp.2 with hp | hp
    · change η p ∈ Y ↔ p ∈ X
      rw [hηχ hp]
      exact hχimage hp.2
    · change η p ∈ Y ↔ p ∈ X
      rw [hηD hp]
      exact hDimage hp.2
  · intro p hp
    rcases hp.2 with hp | hp
    · rw [hηχ hp]; exact hχf p hp.2
    · rw [hηD hp]; exact hDf p hp.2
  · intro p hp
    exact Filter.eventuallyEq_of_mem (hW₀.mem_nhds (hK₀W hp)) (fun q hq => hηχ hq)
  · intro p hp
    exact Filter.eventuallyEq_of_mem (hW₁.mem_nhds (hK₁W hp)) (fun q hq => hηD hq)

end DifferentialGeometry.Topology.PlanarJordan
