import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingDiskComponents
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingSeparator

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.isConnected_sdiff_boundary {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {d : ℕ} {S B : Set M}
    (hS : IsPLCellOn (d + 1) S B) : IsConnected (S \ B) := by
  obtain ⟨P, r, u, hr, hu, rfl, rfl⟩ := hS
  have hJ : r '' stdSimplexBoundary (d + 1) ⊆ P :=
    image_subset_iff.mpr fun _ hx => hr.bijOn.mapsTo hx.1
  rw [← hu.injOn.image_sdiff_subset hJ]
  exact hr.isConnected_sdiff_image_stdSimplexBoundary.image u
    (hu.continuousOn.mono sdiff_subset)

theorem IsPLCellOn.exists_boundary_disk_complement {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {S B D J : Set M}
    (hS : IsPLCellOn 3 S B) (hD : IsPLCellOn 2 D J) (hDB : D ⊆ B) :
    ∃ E : Set M, IsPLCellOn 2 E J ∧ D ∪ E = B ∧ D ∩ E = J := by
  obtain ⟨P, r, u, hr, hu, -, hB⟩ := hS
  have hP : IsPLBall 3 P := ⟨r, hr⟩
  have hfront : frontier P ⊆ P := hP.isPolyhedron.isClosed.frontier_subset
  rw [hr.image_stdSimplexBoundary_eq_frontier] at hB
  have hDP : D ⊆ u '' P := hDB.trans (hB ▸ image_mono hfront)
  let δ := Function.invFunOn u P '' D
  obtain ⟨q, hq, hqb⟩ := hD.exists_isPLHomeomorphOn_invFunOn hu hDP
  have hδS : δ ⊆ frontier P := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, hz, rfl⟩ : x ∈ u '' frontier P := hB ▸ hDB hx
    rw [hu.injOn.leftInvOn_invFunOn (hfront hz)]
    exact hz
  let E := closure (frontier P \ δ)
  have hES : E ⊆ frontier P := closure_minimal sdiff_subset isClosed_frontier
  have hball : IsPLBall 2 E := hP.isPLSphere_frontier.isPLBall_closure_sdiff ⟨q, hq⟩ hδS
  obtain ⟨v, hv⟩ := hball
  have hcover : δ ∪ E = frontier P := by
    apply Subset.antisymm (union_subset hδS hES)
    intro x hx
    by_cases hxδ : x ∈ δ
    · exact Or.inl hxδ
    · exact Or.inr (subset_closure ⟨hx, hxδ⟩)
  have hmeet : δ ∩ E = Function.invFunOn u P '' J :=
    (hP.isPLSphere_frontier.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hδS).trans
      hqb.symm
  have hvb : v '' stdSimplexBoundary 2 = Function.invFunOn u P '' J := by
    rw [← hP.isPLSphere_frontier.inter_closure_sdiff_eq_image_stdSimplexBoundary hv hES]
    change E ∩ closure (frontier P \ closure (frontier P \ δ)) = _
    rw [hP.isPLSphere_frontier.closure_sdiff_closure_sdiff_eq ⟨q, hq⟩ hδS,
      inter_comm, hmeet]
  have hback (X : Set M) (hXP : X ⊆ u '' P) :
      u '' (Function.invFunOn u P '' X) = X := by
    rw [image_image]
    exact (image_congr fun x hx =>
      hu.injOn.bijOn_image.invOn_invFunOn.2 (hXP hx)).trans (image_id' X)
  have hpoly : IsPolyhedron E := IsPLBall.isPolyhedron ⟨v, hv⟩
  have huE : IsPLHomeomorphInto 3 u E :=
    (hu.isPLOn.mono_of_isPolyhedron hpoly (hES.trans hfront)).isPLHomeomorphInto_model
      hpoly.isCompact (hu.injOn.mono (hES.trans hfront))
  have hcell := (isPLCellOn_id_of_isPLBall hv).image huE
  rw [hvb, hback J (hD.boundary_subset.trans hDP)] at hcell
  refine ⟨u '' E, hcell, ?_, ?_⟩
  · rw [← hback D hDP, ← image_union, hcover, ← hB]
  · rw [← hback D hDP, ← hu.injOn.image_inter (hδS.trans hfront) (hES.trans hfront),
      hmeet, hback J (hD.boundary_subset.trans hDP)]

theorem IsPLCellOn.end_subset_disk_of_separates {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {S B D J H K : Set M}
    (hS : IsPLCellOn 3 S B) (hD : IsPLCellOn 2 D J) (hDB : D ⊆ B)
    (hHB : H ⊆ B) (hKB : K ⊆ B)
    (hsep : DifferentialGeometry.Topology.Separates
      ((Subtype.val : B → M) ⁻¹' J) (Subtype.val ⁻¹' H) (Subtype.val ⁻¹' K)) :
    H ⊆ D ∨ K ⊆ D := by
  obtain ⟨E, hE, hcover, -⟩ := hS.exists_boundary_disk_complement hD hDB
  by_contra hn
  obtain ⟨hH, hK⟩ := not_or.mp hn
  obtain ⟨x, hxH, hxD⟩ := not_subset.mp hH
  obtain ⟨y, hyK, hyD⟩ := not_subset.mp hK
  have hEB : E ⊆ B := hcover ▸ subset_union_right
  have hconn : IsPreconnected ((Subtype.val : B → M) ⁻¹' (E \ J)) := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr (sdiff_subset.trans hEB)]
    exact hE.isConnected_sdiff_boundary.isPreconnected
  have hxE : x ∈ E \ J :=
    ⟨(hcover.symm ▸ hHB hxH).resolve_left hxD, fun hxJ => hxD (hD.boundary_subset hxJ)⟩
  have hyE : y ∈ E \ J :=
    ⟨(hcover.symm ▸ hKB hyK).resolve_left hyD, fun hyJ => hyD (hD.boundary_subset hyJ)⟩
  exact hsep.not_mem_connectedComponentIn (x := ⟨x, hHB hxH⟩) (y := ⟨y, hKB hyK⟩)
    hxH hyK (hconn.subset_connectedComponentIn hxE (fun _ hz => hz.2) hyE)

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

theorem exists_section34_piercing_circle_essential_in_first_annulus
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') :
    ∃ i < cnt e, DifferentialGeometry.Topology.Separates
      ((Subtype.val : (G (ends e).1 '' CpBd (ends e).1) → M₂) ⁻¹' Pg e i)
      (Subtype.val ⁻¹' (G (ends e).1 '' Ab₀ e))
      (Subtype.val ⁻¹' (G (ends e).1 '' Ab₁ e)) ∧
      ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).1 '' Aa e := by
  obtain ⟨i, hi, hsep⟩ := exists_section34_piercing_circle_separating_first_ends hprep hpack e
  have hann := (section34_piercing_annuli hprep hpack e).1
  have hends {D : Set M₂} (hD : IsPLCellOn 2 D (Pg e i)) (hDT : D ⊆ Tp e) :=
    section34_piercing_ends_not_in_inner_cell hprep hpack e hD hDT
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, hAa, -⟩ := hprep
  obtain ⟨-, -, -, hEq, -, -, -, -, -, -, hG, -⟩ := hpack
  have hAS : G (ends e).1 '' Aa e ⊆ G (ends e).1 '' CpBd (ends e).1 :=
    image_mono ((hAa e).1 ▸ inter_subset_left)
  have hAT : G (ends e).1 '' Aa e ⊆ Tp e := by
    rw [(hEq e).2]
    exact image_mono ((hAa e).1 ▸ inter_subset_right)
  refine ⟨i, hi, hsep, ?_⟩
  rintro ⟨D, hD, hDA⟩
  have hno := hends hD (hDA.trans hAT)
  rcases ((hCp (ends e).1).image (hG (ends e).1)).end_subset_disk_of_separates
    hD (hDA.trans hAS) (hann.first_subset.trans hAS) (hann.second_subset.trans hAS)
    hsep with h | h
  · exact hno.1 h
  · exact hno.2 h

end DifferentialGeometry.Topology.PiecewiseLinear
