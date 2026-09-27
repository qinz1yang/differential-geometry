/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ChartCellConjugation
import DifferentialGeometry.Topology.PiecewiseLinear.ChartCrossingConjugation
import DifferentialGeometry.Topology.PiecewiseLinear.ChartSupportedHomology
import DifferentialGeometry.Topology.PiecewiseLinear.Section34BigonInvariantUpdate
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TraceTransport
import DifferentialGeometry.Topology.PiecewiseLinear.SupportedCurveCrossings

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {H : Finset Ea → Set M₂}

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_section34BigonSlide_of_model_move
    {tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂}
    {tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
    {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H tgtV tgtEBd fbl fblBd)
    (s : Section34SimplexIndex 𝒦 3) {w v : Section34VertexIndex 𝒦 𝒦'}
    (hwi : Section34Incident w.1 s.1) (hvi : Section34Incident v.1 s.1)
    {c : OpenPartialHomeomorph M₂ E3} (hc : c ∈ (plGroupoid 3).maximalAtlas M₂)
    (hfc : fbl s ⊆ c.source) (hTc : section34FaceTorus tgtV s ⊆ c.source)
    {O : Set M₂} (hOc : O ⊆ c.source)
    (hOV : O ∩ (⋃ z, tgtV z) = O ∩ (tgtV w ∪ tgtV v))
    (hOT : O ∩ section34FaceTorus tgtV s = O ∩ (tgtV w ∪ tgtV v))
    (hOH : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 →
      O ⊆ interior (H t.1))
    (hOf : Disjoint O (⋃ s' ≠ s, fbl s'))
    (hOrim : Disjoint O (h '' simplexRim 𝒦 s.1))
    (hforeign : ∀ z : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident z.1 s.1 →
      Disjoint O (tgtV z))
    (Φ : E3 ≃ₜ E3) (hΦ : IsPLHomeomorphOn Φ univ univ)
    {K : Set E3} (hK : IsCompact K) (hKO : K ⊆ c '' O) (hfix : EqOn Φ id Kᶜ)
    (hΦT : ∀ z, Φ z ∈ c '' section34FaceTorus tgtV s ↔
      z ∈ c '' section34FaceTorus tgtV s)
    (G : E3 × unitInterval → E3) (hG : Continuous G)
    (hG0 : ∀ z, G (z, 0) = z) (hG1 : ∀ z, G (z, 1) = Φ z)
    (hGfix : ∀ t, EqOn (fun z => G (z, t)) id Kᶜ)
    (hGK : ∀ t, MapsTo (fun z => G (z, t)) K K)
    (hGT : ∀ z t, z ∈ c '' section34FaceTorus tgtV s →
      G (z, t) ∈ c '' section34FaceTorus tgtV s)
    (hdelete : (Φ '' (c '' fblBd s)) ∩ (c '' ((⋃ e, tgtEBd e) ∩ c.source)) =
      ((c '' fblBd s) ∩ (c '' ((⋃ e, tgtEBd e) ∩ c.source))) \ K)
    (hdrop : ((Φ '' (c '' fblBd s)) ∩ (c '' ((⋃ e, tgtEBd e) ∩ c.source))).ncard + 2 =
      ((c '' fblBd s) ∩ (c '' ((⋃ e, tgtEBd e) ∩ c.source))).ncard) :
    ∃ fbl' fblBd' : Section34SimplexIndex 𝒦 3 → Set M₂,
      Section34FaceBallInvariants 𝒦 𝒦' h H tgtV tgtEBd fbl' fblBd' ∧
      (∀ s', s' ≠ s → fbl' s' = fbl s' ∧ fblBd' s' = fblBd s') ∧
      section34TraceCount tgtV fblBd' s = section34TraceCount tgtV fblBd s ∧
      section34CrossingCount tgtEBd fblBd' s + 2 =
        section34CrossingCount tgtEBd fblBd s := by
  classical
  obtain ⟨hf1, -, -, -, hf5, hf6, hf7, hf8, hf9, -⟩ := id hinv
  have hKc : K ⊆ c.target := hKO.trans (by
    rintro _ ⟨x, hx, rfl⟩
    exact c.map_source (hOc hx))
  let Ψ := c.conjugateHomeomorph Φ hK hKc hfix
  have hmap : MapsTo Φ c.target c.target := mapsTo_of_injective_eqOn_compl Φ.injective
    (hfix.mono (compl_subset_compl.mpr hKc))
  have hΨc : MapsTo Ψ c.source c.source := by
    intro x hx
    change c.conjugateMap Φ x ∈ c.source
    rw [c.conjugateMap_of_mem Φ hx]
    exact c.map_target (hmap (c.map_source hx))
  have hKO' : c.symm '' K ⊆ O := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hKO hz
    rwa [c.left_inv (hOc hx)]
  have hΨfix : EqOn Ψ id (c.symm '' K)ᶜ := c.conjugateMap_eqOn_compl hfix
  have hΨfixO : EqOn Ψ id Oᶜ := hΨfix.mono (compl_subset_compl.mpr hKO')
  have hTcoord : ∀ x ∈ c.source, x ∈ section34FaceTorus tgtV s ↔
      c x ∈ c '' section34FaceTorus tgtV s :=
    fun _ hx => (c.injOn.mem_image_iff hTc hx).symm
  have hΨT : ∀ x, Ψ x ∈ section34FaceTorus tgtV s ↔ x ∈ section34FaceTorus tgtV s :=
    c.conjugateMap_mem_iff hmap hTcoord (fun z _ => hΦT z)
  have hTimage : Ψ '' section34FaceTorus tgtV s = section34FaceTorus tgtV s := by
    ext x
    rw [Ψ.image_eq_preimage_symm]
    simpa only [mem_preimage, Ψ.apply_symm_apply] using (hΨT (Ψ.symm x)).symm
  have hOimage : Ψ '' O = O :=
    image_eq_of_homeomorph_eqOn_compl_of_subset Ψ hΨfixO Subset.rfl
  have hΨO : ∀ x, Ψ x ∈ O ↔ x ∈ O := by
    intro x
    conv_lhs => rw [← hOimage]
    exact Ψ.injective.mem_set_image
  have hlocal : ∀ x ∈ O, x ∈ (⋃ z, tgtV z) ↔ x ∈ section34FaceTorus tgtV s := by
    intro x hx
    have heq := Set.ext_iff.mp (hOV.trans hOT.symm) x
    exact ⟨fun hxV => (heq.mp ⟨hx, hxV⟩).2, fun hxT => (heq.mpr ⟨hx, hxT⟩).2⟩
  have hΨV : ∀ x, Ψ x ∈ (⋃ z, tgtV z) ↔ x ∈ (⋃ z, tgtV z) := by
    intro x
    by_cases hxO : x ∈ O
    · rw [hlocal _ ((hΨO x).mpr hxO), hlocal _ hxO, hΨT]
    · rw [hΨfixO hxO]
      rfl
  have hV : Ψ '' (⋃ z, tgtV z) = ⋃ z, tgtV z := by
    ext x
    rw [Ψ.image_eq_preimage_symm]
    simpa only [mem_preimage, Ψ.apply_symm_apply] using (hΨV (Ψ.symm x)).symm
  have hSf : Ψ '' frontier (⋃ z, tgtV z) = frontier (⋃ z, tgtV z) := by
    rw [Ψ.image_frontier, hV]
  have hBsrc : fblBd s ⊆ c.source := (hf1 s).boundary_subset.trans hfc
  have hnewsrc : Ψ '' fblBd s ⊆ c.source := by
    rintro _ ⟨x, hx, rfl⟩
    exact hΨc (hBsrc hx)
  have hBimage : c '' (Ψ '' fblBd s) = Φ '' (c '' fblBd s) := by
    have heq := c.image_conjugateMap_inter_source hmap (fblBd s)
    change c '' (Ψ '' fblBd s ∩ c.source) = Φ '' (c '' (fblBd s ∩ c.source)) at heq
    rwa [inter_eq_left.mpr hnewsrc, inter_eq_left.mpr hBsrc] at heq
  have hcrossimg : ∀ A ⊆ c.source,
      c '' (A ∩ ⋃ e, tgtEBd e) = (c '' A) ∩ (c '' ((⋃ e, tgtEBd e) ∩ c.source)) := by
    intro A hAc
    rw [← c.injOn.image_inter hAc inter_subset_right, ← inter_assoc,
      inter_eq_left.mpr (inter_subset_left.trans hAc)]
  have holdimg := hcrossimg (fblBd s) hBsrc
  have hnewimg := hcrossimg (Ψ '' fblBd s) hnewsrc
  rw [hBimage] at hnewimg
  have hnewdisj : Disjoint ((Ψ '' fblBd s) ∩ ⋃ e, tgtEBd e) (c.symm '' K) := by
    refine disjoint_left.mpr ?_
    intro x hx hxK
    have hcx := hnewimg ▸ mem_image_of_mem c hx
    rw [hdelete] at hcx
    apply hcx.2
    obtain ⟨z, hz, rfl⟩ := hxK
    rwa [c.right_inv (hKc hz)]
  have h8 : ((Ψ '' fblBd s) ∩ ⋃ e, tgtEBd e).Finite := by
    apply (finite_image_iff (c.injOn.mono (inter_subset_left.trans hnewsrc))).mp
    rw [hnewimg, hdelete, ← holdimg]
    exact ((hf8 s).image c).subset sdiff_subset
  have hcount : ((Ψ '' fblBd s) ∩ ⋃ e, tgtEBd e).ncard + 2 =
      (fblBd s ∩ ⋃ e, tgtEBd e).ncard := by
    have holdcard : (c '' (fblBd s ∩ ⋃ e, tgtEBd e)).ncard =
        (fblBd s ∩ ⋃ e, tgtEBd e).ncard :=
      (c.injOn.mono (inter_subset_left.trans hBsrc)).ncard_image
    have hnewcard : (c '' ((Ψ '' fblBd s) ∩ ⋃ e, tgtEBd e)).ncard =
        ((Ψ '' fblBd s) ∩ ⋃ e, tgtEBd e).ncard :=
      (c.injOn.mono (inter_subset_left.trans hnewsrc)).ncard_image
    rw [holdimg] at holdcard
    rw [hnewimg] at hnewcard
    rw [← hnewcard, ← holdcard]
    exact hdrop
  have h6 := fun e => exists_chart_hasPLCurveCrossingOnAt_supported_image Ψ
    (B := fblBd s) (Sf := frontier (⋃ z, tgtV z)) (C := tgtEBd e)
    (hK.image_of_continuousOn (c.continuousOn_symm.mono hKc)).isClosed hΨfix
    (Disjoint.mono_left (show (Ψ '' fblBd s) ∩ tgtEBd e ⊆
      (Ψ '' fblBd s) ∩ ⋃ e, tgtEBd e from
        fun _ hx => ⟨hx.1, mem_iUnion.mpr ⟨e, hx.2⟩⟩) hnewdisj) (hf6 s e)
  have h7 := (hf7 s).conjugate_image_of_supported_homotopy c Φ hK hKc hfix
    G hG hG0 hG1 hGfix hGK hTcoord hGT
  rw [image_inter Ψ.injective, Ψ.image_frontier, hTimage] at h7
  have h9 : (section34TraceComponents tgtV
      (Function.update fblBd s (Ψ '' fblBd s)) s).Finite := by
    rw [section34TraceComponents_update_image tgtV fblBd s Ψ hSf]
    exact (hf9 s).image _
  refine ⟨Function.update fbl s (Ψ '' fbl s), Function.update fblBd s (Ψ '' fblBd s),
    section34FaceBallInvariants_update_of_supported_image hinv hwi hvi Ψ hΨfixO hV hOV
      hOH hOf hOrim hforeign ((hf1 s).image_conjugateHomeomorph hc hfc Φ hΦ hK hKc hfix)
      (exists_chart_hasPLCrossingAt_conjugate_image hc hBsrc Φ hΦ hK hKc hfix hSf (hf5 s))
      h6 h7 h8 ?_, ?_, section34TraceCount_update_image tgtV fblBd s Ψ hSf, ?_⟩
  · simpa only [section34TraceComponents, Function.update_self] using h9
  · intro s' hs'
    simp only [Function.update_of_ne hs', and_self]
  · simpa only [section34CrossingCount, Function.update_self] using hcount

end DifferentialGeometry.Topology.PiecewiseLinear
