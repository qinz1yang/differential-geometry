import DifferentialGeometry.Topology.PiecewiseLinear.Section34DiskContactControl
import DifferentialGeometry.Topology.PiecewiseLinear.Section34InnerSheetSupport

open Set Topology

theorem IsClosed.subset_of_frontier_subset_of_disjoint_frontier
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] {C A : Set X}
    (hC : IsClosed C) (hfront : frontier C ⊆ A)
    (hdis : Disjoint C (frontier A)) (hA : A.Nonempty) : C ⊆ A := by
  have hclopen : IsClopen (C \ A) := by
    apply isClopen_iff_frontier_eq_empty.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hx' : x ∈ frontier (C ∩ Aᶜ) := hx
    rcases frontier_inter_subset C Aᶜ hx' with hx | hx
    · have hxA := hfront hx.1
      have hxnot : x ∉ interior A := by
        simpa only [closure_compl, mem_compl_iff] using hx.2
      exact disjoint_left.mp hdis (hC.frontier_subset hx.1) ⟨subset_closure hxA, hxnot⟩
    · exact disjoint_left.mp hdis (hC.closure_eq ▸ hx.1)
        (frontier_compl A ▸ hx.2)
  rcases isClopen_iff.mp hclopen with hempty | huniv
  · exact sdiff_eq_empty.mp hempty
  · obtain ⟨x, hx⟩ := hA
    exact False.elim ((show x ∈ C \ A from huniv.symm ▸ mem_univ x).2 hx)

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.inter_subset_annulus_of_frontier_inter_subset
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {S B A A₀ A₁ C : Set M}
    (hS : IsPLCellOn 3 S B) (hA : IsAnnulusOn A A₀ A₁) (hAB : A ⊆ B)
    (hC : IsClosed C) (hfront : frontier C ∩ B ⊆ A)
    (hends : Disjoint C (A₀ ∪ A₁)) : C ∩ B ⊆ A := by
  obtain ⟨hchart⟩ := hS.nonempty_chartedSpace_boundary
  let _ := hchart
  let _ := hS.boundary_simplyConnectedSpace
  let A' := (Subtype.val : B → M) ⁻¹' A
  let C' := (Subtype.val : B → M) ⁻¹' C
  have hsub : C' ⊆ A' := by
    apply (hC.preimage continuous_subtype_val).subset_of_frontier_subset_of_disjoint_frontier
    · intro x hx
      exact hfront ⟨continuous_subtype_val.frontier_preimage_subset C hx, x.property⟩
    · exact disjoint_left.mpr fun x hx hxfront => disjoint_left.mp hends hx
        ((hA.preimage_subtype hAB).frontier_subset hxfront)
    · obtain ⟨x, hx⟩ := hA.isConnected.nonempty
      exact ⟨⟨x, hAB hx⟩, hx⟩
  exact fun x hx => hsub (show (⟨x, hx.2⟩ : B) ∈ C' from hx.1)

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

theorem section34_disk_filling_second_contact_subset_annulus
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {C D F : Set M₂}
    (hC : IsPLCellOn 3 C (D ∪ F)) (hCT : C ⊆ Tp e)
    (hDB : D ⊆ G (ends e).2 '' Bb e) (hFA : F ⊆ G (ends e).1 '' Aa e) :
    C ∩ G (ends e).2 '' CpBd (ends e).2 ⊆ G (ends e).2 '' Bb e := by
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, hAa, hBb, -⟩ := id hprep
  obtain ⟨-, -, -, -, -, -, hcross, -, hBrim, -, hGp, -⟩ := id hpack
  have hann := (section34_piercing_annuli hprep hpack e).2
  apply ((hCp _).image (hGp _)).inter_subset_annulus_of_frontier_inter_subset hann
    (image_mono (hBb e).1) hC.isCompact.isClosed
  · rw [← hC.boundary_eq_frontier]
    rintro x ⟨hxD | hxF, hxB⟩
    · exact hDB hxD
    · exact image_mono sdiff_subset (hcross e
        ⟨image_mono ((hAa e).1 ▸ inter_subset_left) (hFA hxF), hxB⟩).1.2
  · rw [← image_union]
    exact (hBrim e).2.symm.mono_left hCT

theorem exists_section34_disk_filling_second_contact_support
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {C D F : Set M₂}
    (hC : IsPLCellOn 3 C (D ∪ F)) (hCT : C ⊆ Tp e)
    (hDT : D ⊆ G (ends e).2 '' Bb e ∩ interior (Tp e))
    (hFA : F ⊆ G (ends e).1 '' Aa e) :
    ∃ O : Set M₂, IsOpen O ∧ IsCompact (closure O) ∧
      C ∩ G (ends e).2 '' CpBd (ends e).2 ⊆ O ∧
      closure O ⊆ interior (Tp e) ∩ G (ends e).2 '' interior (Sn e) ∧
      closure O ⊆ interior (Sp e) ∩ interior (Q (ends e).1) ∩ interior (Q (ends e).2) ∧
      Disjoint (closure O) (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)) ∧
      Disjoint (closure O) (G (ends e).2 '' (Bb₀ e ∪ Bb₁ e)) ∧
      ∀ d, d ≠ e → ((ends e).2 = (ends d).1 ∨ (ends e).2 = (ends d).2) →
        Disjoint (closure O) (G (ends e).2 '' Sn d) := by
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, hAa, -⟩ := id hprep
  obtain ⟨-, -, -, -, -, -, hcross, -, -, -, hGp, -⟩ := id hpack
  have hBclosed : IsClosed (G (ends e).2 '' CpBd (ends e).2) := by
    rw [((hCp _).image (hGp _)).boundary_eq_frontier]
    exact isClosed_frontier
  have hcontact := section34_disk_filling_second_contact_subset_annulus hprep hpack e hC hCT
    (hDT.trans inter_subset_left) hFA
  have hinner : C ∩ G (ends e).2 '' CpBd (ends e).2 ⊆ interior (Tp e) :=
    hC.inter_subset_interior_of_boundary_inter_subset hCT (hDT.trans inter_subset_right)
      (fun x hx => (hcross e
        ⟨image_mono ((hAa e).1 ▸ inter_subset_left) (hFA hx.1), hx.2⟩).2)
  exact exists_section34_inner_sheet_support hprep hpack e (hC.isCompact.inter_right hBclosed)
    (subset_inter hcontact hinner)

end DifferentialGeometry.Topology.PiecewiseLinear
