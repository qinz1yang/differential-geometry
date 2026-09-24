import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCollar

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
noncomputable def section34AnnularCollarBase (H : Geometry.SimplicialComplex ℝ E)
    (d : Finset {v : E // ({v} : Finset E) ∈ H.faces}) : Set E :=
  ⋃ v ∈ d, (dualCell H {v.1} v.2).space

open Classical in
theorem exists_annular_collar_extension_of_initial_cells
    (K H R₀ : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] [Finite H.faces] [Finite R₀.faces]
    (hH : IsCombinatorialManifoldWithBoundary 2 H)
    (hHK : H.space ⊆ (boundaryComplex 3 K).space)
    (d₀ : Finset {v : E // ({v} : Finset E) ∈ H.faces})
    {a b : ℝ} (hab : a < b) {W₀ : Set E} {ρ₀ : E × ℝ → E}
    (hW₀K : W₀ ⊆ K.space)
    (hρ₀ : IsPLHomeomorphOn ρ₀ (section34AnnularCollarBase H d₀ ×ˢ Icc a b) W₀)
    (hbottom₀ : ∀ x ∈ section34AnnularCollarBase H d₀, ρ₀ (x, a) = x)
    (htrace₀ : W₀ ∩ (boundaryComplex 3 K).space = section34AnnularCollarBase H d₀)
    (hR₀ : IsCombinatorialManifoldWithBoundary 3 R₀)
    (hR₀space : R₀.space = closure (K.space \ W₀))
    (hW₀R₀ : W₀ ∩ R₀.space ⊆ (boundaryComplex 3 R₀).space)
    (hBR₀ : (boundaryComplex 3 K).space ∩ R₀.space ⊆ (boundaryComplex 3 R₀).space)
    (hattach₀ : ∀ v ∉ d₀, (dualCell H {v.1} v.2).space ∪
      ρ₀ '' (((dualCell H {v.1} v.2).space ∩ section34AnnularCollarBase H d₀) ×ˢ Icc a b) ⊆
        (boundaryComplex 3 R₀).space) :
    ∃ (W : Set E) (ρ : E × ℝ → E) (R : Geometry.SimplicialComplex ℝ E),
      IsPolyhedron W ∧ W₀ ⊆ W ∧ W ⊆ K.space ∧
      IsPLHomeomorphOn ρ (H.space ×ˢ Icc a b) W ∧
      EqOn ρ ρ₀ (section34AnnularCollarBase H d₀ ×ˢ Icc a b) ∧
      (∀ x ∈ H.space, ρ (x, a) = x) ∧ W ∩ (boundaryComplex 3 K).space = H.space ∧
      MapsTo ρ (H.space ×ˢ Ioc a b) (K.space \ (boundaryComplex 3 K).space) ∧
      R.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R ∧
      R.space = closure (K.space \ W) ∧
      W ∩ R.space ⊆ (boundaryComplex 3 R).space ∧
      (boundaryComplex 3 K).space ∩ R.space ⊆ (boundaryComplex 3 R).space := by
  let V := {v : E // ({v} : Finset E) ∈ H.faces}
  let _ : Finite V :=
    (Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite H.faces)).to_subtype
  let _ : Fintype V := Fintype.ofFinite V
  let D : V → Geometry.SimplicialComplex ℝ E := fun v => dualCell H {v.1} v.2
  let _ (v : V) : Finite (D v).faces := (dualCell_faces_finite H v.2).to_subtype
  let P := section34AnnularCollarBase H
  have hD : ∀ v : V, IsPLBall 2 (D v).space := fun v =>
    hH.isPLBall_dualCell H v.2 (k := 0) (Finset.card_singleton v.1) (by norm_num)
  have hDB : ∀ v : V, (D v).space ⊆ (boundaryComplex 3 K).space := by
    intro v x hx
    apply hHK
    rw [← iUnion_dualCell_singleton_space H]
    exact mem_iUnion.mpr ⟨v, hx⟩
  have hPinsert : ∀ (v : V) (d : Finset V), P (insert v d) = P d ∪ (D v).space := by
    intro v d
    simp [P, section34AnnularCollarBase, D, union_comm]
  have hP : ∀ d : Finset V, IsPolyhedron (P d) := by
    intro d
    induction d using Finset.induction_on with
    | empty => simpa [P, section34AnnularCollarBase] using IsPolyhedron.empty (E := E)
    | @insert v d hv ih => rw [hPinsert]; exact ih.union (hD v).isPolyhedron
  have hW₀ : IsPolyhedron W₀ := by
    rw [← hρ₀.image_eq]
    exact ((hP d₀).prod isHPolytope_Icc.isPolyhedron).image_of_isPiecewiseAffineOn
      hρ₀.isPiecewiseAffineOn hρ₀.bijOn.injOn
  have hind : ∀ d : Finset V,
      ∃ (W : Set E) (ρ : E × ℝ → E) (R : Geometry.SimplicialComplex ℝ E),
        IsPolyhedron W ∧ W ⊆ K.space ∧
        IsPLHomeomorphOn ρ (P (d₀ ∪ d) ×ˢ Icc a b) W ∧
        (∀ x ∈ P (d₀ ∪ d), ρ (x, a) = x) ∧
        W ∩ (boundaryComplex 3 K).space = P (d₀ ∪ d) ∧
        R.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R ∧
        R.space = closure (K.space \ W) ∧
        W ∩ R.space ⊆ (boundaryComplex 3 R).space ∧
        (boundaryComplex 3 K).space ∩ R.space ⊆ (boundaryComplex 3 R).space ∧
        EqOn ρ ρ₀ (P d₀ ×ˢ Icc a b) ∧
        ∀ v ∉ d₀ ∪ d, (D v).space ∪ ρ '' (((D v).space ∩ P (d₀ ∪ d)) ×ˢ Icc a b) ⊆
          (boundaryComplex 3 R).space := by
    intro d
    induction d using Finset.induction_on with
    | empty =>
      simpa only [Finset.union_empty] using
        (show ∃ (W : Set E) (ρ : E × ℝ → E) (R : Geometry.SimplicialComplex ℝ E),
          IsPolyhedron W ∧ W ⊆ K.space ∧ IsPLHomeomorphOn ρ (P d₀ ×ˢ Icc a b) W ∧
          (∀ x ∈ P d₀, ρ (x, a) = x) ∧ W ∩ (boundaryComplex 3 K).space = P d₀ ∧
          R.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R ∧
          R.space = closure (K.space \ W) ∧
          W ∩ R.space ⊆ (boundaryComplex 3 R).space ∧
          (boundaryComplex 3 K).space ∩ R.space ⊆ (boundaryComplex 3 R).space ∧
          EqOn ρ ρ₀ (P d₀ ×ˢ Icc a b) ∧
          ∀ v ∉ d₀, (D v).space ∪ ρ '' (((D v).space ∩ P d₀) ×ˢ Icc a b) ⊆
            (boundaryComplex 3 R).space from
          ⟨W₀, ρ₀, R₀, hW₀, hW₀K, hρ₀, hbottom₀, htrace₀, Set.toFinite R₀.faces,
            hR₀, hR₀space, hW₀R₀, hBR₀, fun _ _ => rfl, hattach₀⟩)
    | @insert v d _ ih =>
      by_cases hv : v ∈ d₀ ∪ d
      · simpa only [Finset.union_insert, Finset.insert_eq_of_mem hv] using ih
      obtain ⟨W, ρ, R, hW, hWK, hρ, hbottom, hWB, hRfin, hR, hRspace,
        hWR, hBR, hfix, hfuture⟩ := ih
      let _ : Finite R.faces := hRfin.to_subtype
      obtain ⟨e, -, hE, hcover⟩ :=
        hH.exists_boundary_arcs_cover_inter_dualCell_iUnion H (d₀ ∪ d) hv
      obtain ⟨C, σ, R', hC, hCR, -, hσ, hσρ, hbase, htrace, -, hR'fin, hR', hR'space,
        hWR', hBR', hσC, hCtrace, hCB, hWC⟩ :=
        exists_collar_extension_of_boundary_arcs (D v) R (hD v) hR (hP (d₀ ∪ d))
          (hDB v) hab hρ hbottom hWB e (fun w => (D v).space ∩ (D w).space)
          (fun w hw => (hE w hw).1) (fun w hw => (hE w hw).2) hcover
          (hfuture v hv) hWR hBR (U := univ) Filter.univ_mem
      let _ : Finite R'.faces := hR'fin.to_subtype
      have hRK : R.space ⊆ K.space := by
        rw [hRspace]
        exact closure_minimal sdiff_subset (isPolyhedron_space K).isClosed
      have hR'global : R'.space = closure (K.space \ (W ∪ C)) := by
        rw [hR'space, hRspace]
        have heq : closure (closure (K.space \ W) \ C) = closure ((K.space \ W) \ C) := by
          apply Subset.antisymm
          · apply closure_minimal _ isClosed_closure
            have h := closure_sdiff (s := K.space \ W) (t := C)
            rwa [hC.isPolyhedron.isClosed.closure_eq] at h
          · exact closure_mono (sdiff_subset_sdiff_left subset_closure)
        rw [heq, Set.sdiff_sdiff]
      refine ⟨W ∪ C, σ, R', hW.union hC.isPolyhedron, union_subset hWK (hCR.trans hRK),
        ?_, ?_, ?_, hR'fin, hR', hR'global, hWR', hBR', ?_, ?_⟩
      · rwa [Finset.union_insert, hPinsert]
      · rwa [Finset.union_insert, hPinsert]
      · rwa [Finset.union_insert, hPinsert]
      · intro z hz
        have hzP : z.1 ∈ P (d₀ ∪ d) := by
          obtain ⟨w, hw, hzw⟩ := mem_iUnion₂.mp hz.1
          exact mem_iUnion₂.mpr ⟨w, Finset.mem_union_left d hw, hzw⟩
        exact (hσρ ⟨hzP, hz.2⟩).trans (hfix hz)
      · intro u hu
        rw [Finset.union_insert] at hu ⊢
        have hud : u ∉ d₀ ∪ d := fun hud => hu (Finset.mem_insert_of_mem hud)
        have huv : u ≠ v := fun heq => hu (heq ▸ Finset.mem_insert_self v (d₀ ∪ d))
        have huv' : u.1 ≠ v.1 := fun heq => huv (Subtype.ext heq)
        have hJD : IsPLBall 1 ((D u).space ∩ (D v).space) ∨
            Disjoint (D u).space (D v).space := by
          by_cases hface : ({u.1, v.1} : Finset E) ∈ H.faces
          · exact Or.inl (hH.isPLBall_inter_dualCell_singleton H u.2 v.2 huv' hface)
          · exact Or.inr (disjoint_dualCell_space H u.2 v.2 (by
              simpa only [Finset.singleton_union] using hface))
        have hJDb : (D u).space ∩ (D v).space ⊆ (boundaryComplex 2 (D v)).space := by
          rcases hJD with hball | hdis
          · have hface := union_mem_faces_of_nonempty_dualCell_inter H u.2 v.2 hball.nonempty
            rw [inter_comm]
            exact hH.inter_dualCell_singleton_subset_boundaryComplex H v.2 u.2 huv'.symm
              (by simpa only [Finset.singleton_union, Finset.pair_comm] using hface)
          · rw [hdis.inter_eq]
            exact empty_subset _
        obtain ⟨e', -, hE', hcover'⟩ :=
          hH.exists_boundary_arcs_cover_inter_dualCell_iUnion H (d₀ ∪ d) hud
        obtain ⟨G, hGfin, hGspace⟩ := hC.isPolyhedron.exists_simplicialComplex
        let _ : Finite G.faces := hGfin.to_subtype
        have hpersist := collar_disk_subset_boundaryComplex_complement (D v) R G R'
          (hD v) hR (hGspace.symm ▸ hCR) hR' (hGspace.symm ▸ hR'space)
          (hP (d₀ ∪ d)) (hD u) (hDB u) hJD hJDb
          (hH.finite_inter_dualCell_singleton_iUnion H (d₀ ∪ d) huv hud hv)
          e' (fun w => (D u).space ∩ (D w).space) (fun w hw => (hE' w hw).1) hcover'
          hab hρ (hGspace.symm ▸ hσC) hσρ (hfuture u hud)
          (hGspace.symm ▸ hCtrace) (hGspace.symm ▸ hCB) (hGspace.symm ▸ hWC)
        rwa [hPinsert]
  have hPall : P (d₀ ∪ Finset.univ) = H.space := by
    rw [Finset.union_eq_right.mpr (Finset.subset_univ d₀)]
    simp only [P, section34AnnularCollarBase, Finset.mem_univ, iUnion_true]
    exact iUnion_dualCell_singleton_space H
  obtain ⟨W, ρ, R, hW, hWK, hρ, hbottom, hWB, hRfin, hR, hRspace,
    hWR, hBR, hfix, -⟩ := hind Finset.univ
  rw [hPall] at hρ hbottom hWB
  have hW₀W : W₀ ⊆ W := by
    rintro x hx
    obtain ⟨z, hz, rfl⟩ := hρ₀.bijOn.surjOn hx
    rw [← hfix hz]
    apply hρ.bijOn.mapsTo
    refine ⟨?_, hz.2⟩
    obtain ⟨v, -, hv⟩ := mem_iUnion₂.mp hz.1
    rw [← iUnion_dualCell_singleton_space H]
    exact mem_iUnion.mpr ⟨v, hv⟩
  refine ⟨W, ρ, R, hW, hW₀W, hWK, hρ, hfix, hbottom, hWB,
    ?_, hRfin, hR, hRspace, hWR, hBR⟩
  intro z hz
  have hzW := hρ.bijOn.mapsTo ⟨hz.1, hz.2.1.le, hz.2.2⟩
  refine ⟨hWK hzW, ?_⟩
  intro hzB
  have hxbase : ρ z ∈ H.space := hWB ▸ ⟨hzW, hzB⟩
  have heq : z = (ρ z, a) := hρ.bijOn.injOn ⟨hz.1, hz.2.1.le, hz.2.2⟩
    ⟨hxbase, le_rfl, hab.le⟩ (hbottom (ρ z) hxbase).symm
  exact hz.2.1.ne' (congrArg Prod.snd heq)

end DifferentialGeometry.Topology.PiecewiseLinear
