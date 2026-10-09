/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexBallStar
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteSupportedModification

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {H : Finset Ea → Set M₂}

theorem exists_isOpen_section34BigonCarrierInterior [FiniteDimensional ℝ Ea]
    (hh : IsEmbedding (U.domRestrict h))
    {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {η : M₁ → ℝ}
    {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hctrl : Section34CarrierControl U 𝒦 h η H)
    (hgraph : Section34GraphFrame U U h η H 𝒦 𝒦' src cr f₁)
    {s : Section34SimplexIndex 𝒦 3} {w : Section34VertexIndex 𝒦 𝒦'}
    (hwi : Section34Incident w.1 s.1) {D : Set M₂}
    (hDw : D ⊆ section34VertexBallImage src f₁ w) :
    ∃ O : Set M₂, IsOpen O ∧ D ⊆ O ∧
      ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 →
        O ⊆ interior (H t.1) := by
  classical
  let j : Section34SimplexIndex 𝒦 4 → 𝒦.complex.faces := fun t => ⟨t.1, t.2.1⟩
  have hj : Function.Injective j := fun _ _ he =>
    Subtype.ext (congrArg (fun z : 𝒦.complex.faces => z.1) he)
  have hfin : {t : Section34SimplexIndex 𝒦 4 | Section34Incident s.1 t.1}.Finite := by
    apply ((𝒦.cofaces_finite s.2.1).preimage hj.injOn).subset
    intro t hst a ha
    exact mem_of_mem_convexHull_of_singleton_mem 𝒦.complex
      (𝒦.complex.down_closed s.2.1 (Finset.singleton_subset_iff.mpr ha)
        (Finset.singleton_nonempty a)) t.2.1 (hst (Finset.mem_coe.mpr ha))
  refine ⟨⋂ t ∈ {t : Section34SimplexIndex 𝒦 4 | Section34Incident s.1 t.1},
    interior (H t.1), hfin.isOpen_biInter (fun _ _ => isOpen_interior), ?_, ?_⟩
  · intro x hx
    refine mem_iInter₂.mpr fun t hst => ?_
    exact image_vertexBall_subset_interior_of_incident hh hcut hctrl hgraph w t.2.1
      (hwi.trans (convexHull_min hst (convex_convexHull ℝ _))) (hDw hx)
  · intro t hst
    exact iInter₂_subset t hst

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] in
open Classical in
theorem Section34Exterior.update_image_of_supported
    {tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂}
    {fbl : Section34SimplexIndex 𝒦 3 → Set M₂}
    (hext : Section34Exterior 𝒦 𝒦' h H tgtV fbl)
    {s : Section34SimplexIndex 𝒦 3} {w v : Section34VertexIndex 𝒦 𝒦'}
    (hwi : Section34Incident w.1 s.1) (hvi : Section34Incident v.1 s.1)
    (Ψ : M₂ ≃ₜ M₂) {O : Set M₂} (hfix : EqOn Ψ id Oᶜ)
    (hV : Ψ '' (⋃ z, tgtV z) = ⋃ z, tgtV z)
    (hOV : O ∩ (⋃ z, tgtV z) = O ∩ (tgtV w ∪ tgtV v))
    (hOH : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 →
      O ⊆ interior (H t.1))
    (hOf : Disjoint O (⋃ s' ≠ s, fbl s')) :
    Section34Exterior 𝒦 𝒦' h H tgtV (Function.update fbl s (Ψ '' fbl s)) := by
  let fbl' := Function.update fbl s (Ψ '' fbl s)
  have hO : Ψ '' O = O := image_eq_of_homeomorph_eqOn_compl_of_subset Ψ hfix Subset.rfl
  have hΨO : ∀ x, Ψ x ∈ O ↔ x ∈ O := by
    intro x
    conv_lhs => rw [← hO]
    exact Ψ.injective.mem_set_image
  have hΨV : ∀ x, Ψ x ∈ ⋃ z, tgtV z ↔ x ∈ ⋃ z, tgtV z := by
    intro x
    conv_lhs => rw [← hV]
    exact Ψ.injective.mem_set_image
  have hother : ∀ s', s' ≠ s → Ψ '' fbl s' = fbl s' := by
    intro s' hs'
    apply Set.EqOn.image_eq_self
    intro x hx
    exact hfix (fun hxO => disjoint_left.mp hOf hxO (mem_iUnion₂.mpr ⟨s', hs', hx⟩))
  have hface : ∀ s', Ψ '' fbl s' = fbl' s' := by
    intro s'
    by_cases hs' : s' = s
    · subst s'
      simp [fbl']
    · simp [fbl', hs', hother s' hs']
  have hverts : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 →
      Ψ '' (⋃ (a : Section34PatchIndex 𝒦 𝒦') (_ : a.1.1 = t), tgtV a.1.2) =
        ⋃ (a : Section34PatchIndex 𝒦 𝒦') (_ : a.1.1 = t), tgtV a.1.2 := by
    intro t hst
    let Vt := ⋃ (a : Section34PatchIndex 𝒦 𝒦') (_ : a.1.1 = t), tgtV a.1.2
    have hpair : tgtV w ∪ tgtV v ⊆ Vt := by
      refine union_subset ?_ ?_
      · exact subset_iUnion₂ (s := fun (a : Section34PatchIndex 𝒦 𝒦') (_ : a.1.1 = t) => tgtV a.1.2)
          ⟨⟨t, w⟩, hwi.trans (convexHull_min hst (convex_convexHull ℝ _))⟩ rfl
      · exact subset_iUnion₂ (s := fun (a : Section34PatchIndex 𝒦 𝒦') (_ : a.1.1 = t) => tgtV a.1.2)
          ⟨⟨t, v⟩, hvi.trans (convexHull_min hst (convex_convexHull ℝ _))⟩ rfl
    have hsub : Vt ⊆ ⋃ z, tgtV z := by
      rintro x hx
      obtain ⟨a, _, hxa⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion.mpr ⟨a.1.2, hxa⟩
    have hlocal : ∀ x ∈ O, x ∈ Vt ↔ x ∈ ⋃ z, tgtV z := by
      intro x hx
      exact ⟨fun hxV => hsub hxV, fun hxV =>
        hpair ((Set.ext_iff.mp hOV x).mp ⟨hx, hxV⟩).2⟩
    change Ψ '' Vt = Vt
    apply Set.ext
    intro x
    rw [Ψ.image_eq_preimage_symm]
    change Ψ.symm x ∈ Vt ↔ x ∈ Vt
    by_cases hxO : x ∈ O
    · have hxiO : Ψ.symm x ∈ O := (hΨO _).mp (by simpa)
      rw [hlocal _ hxiO, hlocal _ hxO]
      exact (hΨV (Ψ.symm x)).symm.trans (by simp)
    · have hxi : Ψ.symm x = x := by
        apply Ψ.injective
        rw [Ψ.apply_symm_apply, hfix hxO]
        rfl
      rw [hxi]
  have hobs : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 →
      Ψ '' section34TetraObstacle tgtV fbl t = section34TetraObstacle tgtV fbl' t := by
    intro t hst
    simp only [section34TetraObstacle, image_union, image_iUnion, hverts t hst, hface]
  have hunchanged : ∀ t : Section34SimplexIndex 𝒦 4, ¬ Section34Incident s.1 t.1 →
      section34TetraObstacle tgtV fbl' t = section34TetraObstacle tgtV fbl t := by
    intro t hst
    unfold section34TetraObstacle
    congr 1
    apply iUnion₂_congr
    intro s' hs'
    have hne : s' ≠ s := fun he => hst (he ▸ hs')
    simp [fbl', hne]
  obtain ⟨hext1, hext2, hext3⟩ := hext
  refine ⟨?_, hext2, ?_⟩
  · intro t
    by_cases hst : Section34Incident s.1 t.1
    · have hH := image_eq_of_homeomorph_eqOn_compl_of_subset Ψ hfix (hOH t hst)
      rw [← hobs t hst, ← hH]
      exact image_mono (hext1 t)
    · rw [hunchanged t hst]
      exact hext1 t
  · intro t z hzt y hy hyH
    obtain ⟨hyobs, x, hxcomp, hxfr⟩ := hext3 t z hzt y hy hyH
    by_cases hst : Section34Incident s.1 t.1
    · have hyO : y ∉ O := by
        intro hyO
        have hypair : y ∈ tgtV w ∪ tgtV v :=
          ((Set.ext_iff.mp hOV y).mp ⟨hyO, mem_iUnion.mpr ⟨z,
            interior_subset (hext2 z hy)⟩⟩).2
        apply hyobs
        apply Or.inl
        rcases hypair with hyw | hyv
        · exact mem_iUnion₂.mpr ⟨⟨⟨t, w⟩,
            hwi.trans (convexHull_min hst (convex_convexHull ℝ _))⟩, rfl, hyw⟩
        · exact mem_iUnion₂.mpr ⟨⟨⟨t, v⟩,
            hvi.trans (convexHull_min hst (convex_convexHull ℝ _))⟩, rfl, hyv⟩
      have hyfix : Ψ y = y := hfix hyO
      have hH : Ψ '' H t.1 = H t.1 :=
        image_eq_of_homeomorph_eqOn_compl_of_subset Ψ hfix
          ((hOH t hst).trans interior_subset)
      have hcomp : Ψ '' (H t.1 \ section34TetraObstacle tgtV fbl t) =
          H t.1 \ section34TetraObstacle tgtV fbl' t := by
        rw [image_sdiff Ψ.injective, hH, hobs t hst]
      refine ⟨?_, Ψ x, ?_, ?_⟩
      · intro hyobs'
        rw [← hobs t hst] at hyobs'
        obtain ⟨a, ha, hay⟩ := hyobs'
        exact hyobs (Ψ.injective (hay.trans hyfix.symm) ▸ ha)
      · have himg := Ψ.continuous.continuousOn.image_connectedComponentIn_subset
          (show y ∈ H t.1 \ section34TetraObstacle tgtV fbl t from ⟨hyH, hyobs⟩)
        rw [hcomp, hyfix] at himg
        exact himg (mem_image_of_mem Ψ hxcomp)
      · rw [← hH, ← Ψ.image_frontier]
        exact mem_image_of_mem Ψ hxfr
    · rw [hunchanged t hst]
      exact ⟨hyobs, x, hxcomp, hxfr⟩

end DifferentialGeometry.Topology.PiecewiseLinear
