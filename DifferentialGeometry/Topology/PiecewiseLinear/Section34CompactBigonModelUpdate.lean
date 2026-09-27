/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactBigonExterior
import DifferentialGeometry.Topology.PiecewiseLinear.CurveCrossingGeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.FirstHomologyCarrying
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TraceTransport

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K K' : Geometry.SimplicialComplex ℝ E3} {h : E3 → E3}
  {H : Finset E3 → Set E3}

theorem exists_compactBigonSlide_of_model_move
    {tgtV : Section34CompactVertexIndex K K' → Set E3}
    {tgtEBd : Section34CompactEdgeIndex K K' → Set E3}
    {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}
    (hinv : Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd fbl fblBd)
    (hmarkers : ∀ z : Section34CompactVertexIndex K K', h '' (z.1 : Set E3) ⊆ tgtV z)
    (s : Section34CompactSimplexIndex K 3) {w v : Section34CompactVertexIndex K K'}
    (hwi : Section34Incident w.1 s.1) (hvi : Section34Incident v.1 s.1)
    {O : Set E3} (hOV : O ∩ (⋃ z, tgtV z) = O ∩ (tgtV w ∪ tgtV v))
    (hOT : O ∩ section34CompactFaceTorus tgtV s = O ∩ (tgtV w ∪ tgtV v))
    (hOH : ∀ t : Section34CompactSimplexIndex K 4, Section34Incident s.1 t.1 →
      O ⊆ interior (H t.1))
    (hOf : Disjoint O (⋃ s' ≠ s, fbl s'))
    (hOrim : Disjoint O (h '' section34CompactSimplexRim s.1))
    (hforeign : ∀ z : Section34CompactVertexIndex K K', ¬ Section34Incident z.1 s.1 →
      Disjoint O (tgtV z))
    (Φ : E3 ≃ₜ E3) (hΦ : IsPLHomeomorphOn Φ univ univ)
    {L : Set E3} (hL : IsCompact L) (hLO : L ⊆ O) (hfix : EqOn Φ id Lᶜ)
    (hΦT : ∀ z, Φ z ∈ section34CompactFaceTorus tgtV s ↔
      z ∈ section34CompactFaceTorus tgtV s)
    (G : E3 × unitInterval → E3) (hG : Continuous G)
    (hG0 : ∀ z, G (z, 0) = z) (hG1 : ∀ z, G (z, 1) = Φ z)
    (hGT : ∀ z t, z ∈ section34CompactFaceTorus tgtV s →
      G (z, t) ∈ section34CompactFaceTorus tgtV s)
    (hdelete : (Φ '' fblBd s) ∩ (⋃ e, tgtEBd e) = ((fblBd s) ∩ (⋃ e, tgtEBd e)) \ L)
    (hdrop : ((Φ '' fblBd s) ∩ (⋃ e, tgtEBd e)).ncard + 2 =
      ((fblBd s) ∩ (⋃ e, tgtEBd e)).ncard) :
    ∃ fbl' fblBd' : Section34CompactSimplexIndex K 3 → Set E3,
      Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd fbl' fblBd' ∧
      (∀ s', s' ≠ s → fbl' s' = fbl s' ∧ fblBd' s' = fblBd s') ∧
      section34CompactTraceCount tgtV fblBd' s = section34CompactTraceCount tgtV fblBd s ∧
      section34CompactCrossingCount tgtEBd fblBd' s + 2 =
        section34CompactCrossingCount tgtEBd fblBd s := by
  classical
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11⟩ := id hinv
  have hfixO : EqOn Φ id Oᶜ := hfix.mono (compl_subset_compl.mpr hLO)
  have hmem : ∀ x ∈ Lᶜ, x ∈ Φ '' fbl s ↔ x ∈ fbl s := by
    intro x hx
    exact ⟨fun ⟨z, hz, hzx⟩ => Φ.injective (hzx.trans (hfix hx).symm) ▸ hz,
      fun hxF => ⟨x, hxF, hfix hx⟩⟩
  have hmemBd : ∀ x ∈ Lᶜ, x ∈ Φ '' fblBd s ↔ x ∈ fblBd s := by
    intro x hx
    exact ⟨fun ⟨z, hz, hzx⟩ => Φ.injective (hzx.trans (hfix hx).symm) ▸ hz,
      fun hxF => ⟨x, hxF, hfix hx⟩⟩
  have hT : Φ '' section34CompactFaceTorus tgtV s = section34CompactFaceTorus tgtV s := by
    ext x
    rw [Φ.image_eq_preimage_symm]
    simpa only [mem_preimage, Φ.apply_symm_apply] using (hΦT (Φ.symm x)).symm
  have hO : Φ '' O = O := image_eq_of_homeomorph_eqOn_compl_of_subset Φ hfixO Subset.rfl
  have hΦO : ∀ x, Φ x ∈ O ↔ x ∈ O := by
    intro x
    conv_lhs => rw [← hO]
    exact Φ.injective.mem_set_image
  have hlocal : ∀ x ∈ O, x ∈ (⋃ z, tgtV z) ↔ x ∈ section34CompactFaceTorus tgtV s := by
    intro x hx
    have heq := Set.ext_iff.mp (hOV.trans hOT.symm) x
    exact ⟨fun hxV => (heq.mp ⟨hx, hxV⟩).2, fun hxT => (heq.mpr ⟨hx, hxT⟩).2⟩
  have hΦV : ∀ x, Φ x ∈ (⋃ z, tgtV z) ↔ x ∈ (⋃ z, tgtV z) := by
    intro x
    by_cases hxO : x ∈ O
    · rw [hlocal _ ((hΦO x).mpr hxO), hlocal _ hxO, hΦT]
    · rw [hfixO hxO]
      rfl
  have hV : Φ '' (⋃ z, tgtV z) = ⋃ z, tgtV z := by
    ext x
    rw [Φ.image_eq_preimage_symm]
    simpa only [mem_preimage, Φ.apply_symm_apply] using (hΦV (Φ.symm x)).symm
  have hSf : Φ '' frontier (⋃ z, tgtV z) = frontier (⋃ z, tgtV z) := by
    rw [Φ.image_frontier, hV]
  have hcell : IsPLCellOn 3 (Φ '' fbl s) (Φ '' fblBd s) := by
    apply (hf1 s).image
    apply isPLHomeomorphInto_of_isPLHomeomorphOn_of_subset
      (P := fbl s) (N := univ) _ (hf1 s).isPolyhedron (subset_univ _)
    simpa only [image_univ, Φ.surjective.range_eq] using hΦ
  have h5 : ∀ y ∈ (Φ '' fblBd s) ∩ frontier (⋃ z, tgtV z),
      HasPLCrossingAt (Φ '' fblBd s) (frontier (⋃ z, tgtV z)) y := by
    rintro _ ⟨⟨x, hx, rfl⟩, hxSf⟩
    have hxSf' : x ∈ frontier (⋃ z, tgtV z) := by
      obtain ⟨z, hz, hzx⟩ := hSf.symm ▸ hxSf
      exact Φ.injective hzx ▸ hz
    have hc := (hf5 s x ⟨hx, hxSf'⟩).image_openPartialHomeomorph
      Φ.toOpenPartialHomeomorph hΦ.isPiecewiseAffineOn (mem_univ _)
    change HasPLCrossingAt (Φ '' (univ ∩ fblBd s))
      (Φ '' (univ ∩ frontier (⋃ z, tgtV z))) (Φ x) at hc
    simpa only [univ_inter, hSf] using hc
  have h6 : ∀ e : Section34CompactEdgeIndex K K', ∀ y ∈ (Φ '' fblBd s) ∩ tgtEBd e,
      HasPLSurfaceCurveCrossingAt (frontier (⋃ z, tgtV z))
        ((Φ '' fblBd s) ∩ frontier (⋃ z, tgtV z)) (tgtEBd e) y := by
    intro e y hy
    have hyL : y ∈ Lᶜ := (hdelete ▸
      (show y ∈ (Φ '' fblBd s) ∩ ⋃ e, tgtEBd e from
        ⟨hy.1, mem_iUnion.mpr ⟨e, hy.2⟩⟩)).2
    have hc : HasPLCurveCrossingOnAt (frontier (⋃ z, tgtV z))
        (fblBd s ∩ frontier (⋃ z, tgtV z)) (tgtEBd e) y :=
      hf6 s e y ⟨(hmemBd y hyL).mp hy.1, hy.2⟩
    change HasPLCurveCrossingOnAt _ _ _ _
    refine hc.congr (Filter.Eventually.of_forall (fun _ => Iff.rfl)) ?_
      (Filter.Eventually.of_forall (fun _ => Iff.rfl))
    filter_upwards [hL.isClosed.isOpen_compl.mem_nhds hyL] with x hx
    exact and_congr (hmemBd x hx).symm Iff.rfl
  have h7 : CarriesIntegralFirstHomologyOnto
      ((Φ '' fblBd s) ∩ frontier (section34CompactFaceTorus tgtV s))
      (section34CompactFaceTorus tgtV s) := by
    have hcarry : CarriesFirstHomologyOnto
        (fblBd s ∩ frontier (section34CompactFaceTorus tgtV s))
        (section34CompactFaceTorus tgtV s) := hf7 s
    let J := fblBd s ∩ frontier (section34CompactFaceTorus tgtV s)
    have himage : Φ '' J ⊆ section34CompactFaceTorus tgtV s := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← hG1 x]
      exact hGT x 1 (hcarry.1 hx)
    let g : C(J, Φ '' J) :=
      ⟨fun x => ⟨Φ x, x, x.2, rfl⟩,
        (Φ.continuous.comp continuous_subtype_val).subtype_mk _⟩
    have hc : CarriesFirstHomologyOnto (Φ '' J) (section34CompactFaceTorus tgtV s) := by
      apply hcarry.of_homotopic himage g
      refine ⟨{ toFun := fun q => ⟨G (q.2.1, q.1), hGT q.2.1 q.1 (hcarry.1 q.2.2)⟩
                continuous_toFun := ?_
                map_zero_left := fun x => Subtype.ext (hG0 x)
                map_one_left := fun x => Subtype.ext (hG1 x) }⟩
      exact (hG.comp ((continuous_subtype_val.comp continuous_snd).prodMk
        continuous_fst)).subtype_mk _
    change CarriesFirstHomologyOnto _ _
    simpa only [J, image_inter Φ.injective, Φ.image_frontier, hT] using hc
  have h8 : ((Φ '' fblBd s) ∩ ⋃ e, tgtEBd e).Finite := by
    rw [hdelete]
    exact (hf8 s).subset sdiff_subset
  have htrace : (Φ '' fblBd s) ∩ frontier (⋃ z, tgtV z) =
      Φ '' (fblBd s ∩ frontier (⋃ z, tgtV z)) := by rw [image_inter Φ.injective, hSf]
  have h9 : ((fun y => connectedComponentIn
      ((Φ '' fblBd s) ∩ frontier (⋃ z, tgtV z)) y) ''
        ((Φ '' fblBd s) ∩ frontier (⋃ z, tgtV z))).Finite := by
    rw [htrace, ← Φ.image_connectedComponentIn_family]
    exact (hf9 s).image _
  have hinter : ∀ s', s' ≠ s → (Φ '' fbl s) ∩ fbl s' = fbl s ∩ fbl s' := by
    intro s' hs'
    ext x
    have hxL : x ∈ fbl s' → x ∈ Lᶜ := fun hx hxL =>
      disjoint_left.mp hOf (hLO hxL) (mem_iUnion₂.mpr ⟨s', hs', hx⟩)
    exact ⟨fun hx => ⟨(hmem x (hxL hx.2)).mp hx.1, hx.2⟩,
      fun hx => ⟨(hmem x (hxL hx.2)).mpr hx.1, hx.2⟩⟩
  refine ⟨Function.update fbl s (Φ '' fbl s), Function.update fblBd s (Φ '' fblBd s),
    ?_, ?_, ?_, ?_⟩
  · refine ⟨fun s' => ?_, fun s' => ?_, fun s' z hz => ?_, fun s₁ s₂ hne => ?_,
      fun s' => ?_, fun s' e => ?_, fun s' => ?_, fun s' => ?_, fun s' => ?_,
      fun s' t hst => ?_, hf11.update_image_of_supported hmarkers hwi hvi Φ hfixO hV hOV hOf⟩
    · rcases eq_or_ne s' s with rfl | hs
      · simpa only [Function.update_self] using hcell
      · simpa only [Function.update_of_ne hs] using hf1 s'
    · rcases eq_or_ne s' s with rfl | hs
      · rw [Function.update_self, ← Φ.image_interior]
        intro x hx
        exact ⟨x, hf2 s' hx, hfixO (fun hxO => disjoint_left.mp hOrim hxO hx)⟩
      · simpa only [Function.update_of_ne hs] using hf2 s'
    · rcases eq_or_ne s' s with rfl | hs
      · rw [Function.update_self]
        refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
        have hxL : x ∈ Lᶜ := fun hxL => disjoint_left.mp (hforeign z hz) (hLO hxL) hx.2
        exact notMem_empty x ((hf3 s' z hz) ▸ ⟨(hmem x hxL).mp hx.1, hx.2⟩)
      · simpa only [Function.update_of_ne hs] using hf3 s' z hz
    · rcases eq_or_ne s₁ s with rfl | hs₁
      · have hs₂ : s₂ ≠ s₁ := Ne.symm hne
        rw [Function.update_self, Function.update_of_ne hs₂, hinter s₂ hs₂]
        exact hf4 s₁ s₂ hne
      · rcases eq_or_ne s₂ s with rfl | hs₂
        · rw [Function.update_of_ne hs₁, Function.update_self, inter_comm,
            hinter s₁ hs₁, inter_comm]
          exact hf4 s₁ s₂ hne
        · simpa only [Function.update_of_ne hs₁, Function.update_of_ne hs₂] using hf4 s₁ s₂ hne
    · rcases eq_or_ne s' s with rfl | hs
      · simpa only [Function.update_self] using h5
      · simpa only [Function.update_of_ne hs] using hf5 s'
    · rcases eq_or_ne s' s with rfl | hs
      · simpa only [Function.update_self] using h6 e
      · simpa only [Function.update_of_ne hs] using hf6 s' e
    · rcases eq_or_ne s' s with rfl | hs
      · simpa only [Function.update_self] using h7
      · simpa only [Function.update_of_ne hs] using hf7 s'
    · rcases eq_or_ne s' s with rfl | hs
      · simpa only [Function.update_self] using h8
      · simpa only [Function.update_of_ne hs] using hf8 s'
    · rcases eq_or_ne s' s with rfl | hs
      · simpa only [section34CompactTraceComponents, Function.update_self] using h9
      · simpa only [section34CompactTraceComponents, Function.update_of_ne hs] using hf9 s'
    · rcases eq_or_ne s' s with rfl | hs
      · rw [Function.update_self,
          ← image_eq_of_homeomorph_eqOn_compl_of_subset Φ hfixO (hOH t hst)]
        exact image_mono (hf10 s' t hst)
      · simpa only [Function.update_of_ne hs] using hf10 s' t hst
  · intro s' hs'
    simp only [Function.update_of_ne hs', and_self]
  · simp only [section34CompactTraceCount, section34CompactTraceComponents, Function.update_self]
    rw [htrace, ← Φ.image_connectedComponentIn_family]
    exact ncard_image_of_injective _ Φ.injective.image_injective
  · simpa only [section34CompactCrossingCount, Function.update_self] using hdrop

end DifferentialGeometry.Topology.PiecewiseLinear
