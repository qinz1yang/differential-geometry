import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.CompactGluing
import DifferentialGeometry.Topology.PlanarJordan.RegularCurve
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph

open Set Schoenflies
open scoped ContDiff Manifold Topology

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
