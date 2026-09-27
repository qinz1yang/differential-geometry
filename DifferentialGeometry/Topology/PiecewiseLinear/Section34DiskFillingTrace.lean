import DifferentialGeometry.Topology.PiecewiseLinear.Section34ProtectedDiskFilling
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingDiskTraceDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ProtectedCellMotion

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.isConnected_boundary_sdiff_disk {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B D J : Set M} (hS : IsPLCellOn 3 S B) (hD : IsPLCellOn 2 D J) (hDB : D ⊆ B) :
    IsConnected (B \ D) := by
  obtain ⟨P, r, u, hr, hu, -, hB⟩ := hS
  have hP : IsPLBall 3 P := ⟨r, hr⟩
  have hfront : frontier P ⊆ P := hP.isPolyhedron.isClosed.frontier_subset
  rw [hr.image_stdSimplexBoundary_eq_frontier] at hB
  have hDP : D ⊆ u '' P := hDB.trans (hB ▸ image_mono hfront)
  let δ := Function.invFunOn u P '' D
  obtain ⟨q, hq, -⟩ := hD.exists_isPLHomeomorphOn_invFunOn hu hDP
  have hδS : δ ⊆ frontier P := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, hz, rfl⟩ : x ∈ u '' frontier P := hB ▸ hDB hx
    rw [hu.injOn.leftInvOn_invFunOn (hfront hz)]
    exact hz
  have hback : u '' δ = D := by
    rw [image_image]
    exact (image_congr fun x hx => hu.injOn.bijOn_image.invOn_invFunOn.2 (hDP hx)).trans
      (image_id' D)
  have hconn := (hP.isPLSphere_frontier.isConnected_sdiff_of_isPLBall_two ⟨q, hq⟩ hδS).image u
    (hu.continuousOn.mono (sdiff_subset.trans hfront))
  rw [(hu.injOn.mono hfront).image_sdiff_subset hδS, hback, ← hB] at hconn
  exact hconn

theorem IsPLCellOn.inter_eq_disk_of_frontier_inter_subset {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B C F J : Set M} (hS : IsPLCellOn 3 S B) (hF : IsPLCellOn 2 F J)
    (hFB : F ⊆ B) (hFC : F ⊆ C) (hfront : frontier C ∩ B ⊆ F)
    (houtside : (B \ C).Nonempty) : B ∩ C = F := by
  have hconn := (hS.isConnected_boundary_sdiff_disk hF hFB).isPreconnected
  have havoid : Disjoint (B \ F) (frontier Cᶜ) := by
    rw [frontier_compl]
    exact disjoint_left.mpr fun _ hx hxC => hx.2 (hfront ⟨hxC, hx.1⟩)
  obtain ⟨z, hzB, hzC⟩ := houtside
  have hsub : B \ F ⊆ Cᶜ := IsPreconnected.subset_of_disjoint_frontier hconn
    ⟨z, ⟨hzB, fun hzF => hzC (hFC hzF)⟩, hzC⟩ havoid
  apply Subset.antisymm
  · intro x hx
    by_contra hxF
    exact hsub ⟨hx.1, hxF⟩ hx.2
  · exact subset_inter hFB hFC

theorem IsPLCellOn.subset_or_inter_eq_of_boundary_inter_eq {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {A Ab B Bb F : Set M} (hA : IsPLCellOn 3 A Ab) (hB : IsPLCellOn 3 B Bb)
    (hmeet : Ab ∩ B = F) (hFB : F ⊆ Bb) : B ⊆ A ∨ B ∩ A = F := by
  have hclosed := hA.isCompact.isClosed
  have hreg : closure (interior B) = B := by
    rw [← hB.sdiff_boundary_eq_interior]
    exact hB.closure_sdiff_boundary
  have havoid : Disjoint (interior B) Ab := by
    refine disjoint_left.mpr fun x hx hxA => ?_
    have hxBb := hFB (hmeet.subset ⟨hxA, interior_subset hx⟩)
    rw [hB.boundary_eq_frontier] at hxBb
    exact hxBb.2 hx
  have hcover : interior B ⊆ interior A ∪ Aᶜ := by
    intro x hx
    by_cases hxA : x ∈ interior A
    · exact Or.inl hxA
    · exact Or.inr fun hmem => disjoint_left.mp havoid hx
        (hA.boundary_eq_frontier.symm ▸ And.intro (subset_closure hmem) hxA)
  rcases hB.isConnected_interior.isPreconnected.subset_or_subset isOpen_interior
    hclosed.isOpen_compl (disjoint_compl_right.mono_left interior_subset) hcover with hin | hout
  · exact Or.inl (hreg ▸ closure_minimal (hin.trans interior_subset) hclosed)
  · have hBC : B ⊆ closure Aᶜ := hreg ▸ closure_mono hout
    refine Or.inr (Subset.antisymm ?_ ?_)
    · intro x hx
      have hxnot : x ∉ interior A := by
        have h := hBC hx.1
        rwa [closure_compl] at h
      exact hmeet.subset ⟨
        hA.boundary_eq_frontier.symm ▸ And.intro (subset_closure hx.2) hxnot, hx.1⟩
    · intro x hx
      have h := hmeet.superset hx
      exact ⟨h.2, hA.boundary_subset h.1⟩

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

theorem exists_section34_filling_with_exact_first_trace
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {i : ℕ} (hi : i < cnt e)
    {D : Set M₂} (hD : IsPLCellOn 2 D (Pg e i))
    (hDT : D ⊆ G (ends e).2 '' Bb e ∩ Tp e)
    (htrace : D ∩ G (ends e).1 '' CpBd (ends e).1 = Pg e i) :
    ∃ F B : Set M₂, IsPLCellOn 2 F (Pg e i) ∧ F ⊆ G (ends e).1 '' Aa e ∧
      IsPLCellOn 3 B (D ∪ F) ∧ B ⊆ Tp e ∧
      G (ends e).1 '' CpBd (ends e).1 ∩ B = F ∧
      closure (frontier B \ G (ends e).1 '' CpBd (ends e).1) = D ∧
      (B ⊆ G (ends e).1 '' Cp (ends e).1 ∨ B ∩ G (ends e).1 '' Cp (ends e).1 = F) := by
  obtain ⟨F, hF, hFA, hFD, hFT, -⟩ :=
    exists_section34_matching_disk_pair hprep hpack e hi hD hDT htrace
  obtain ⟨B, hB, hBT⟩ := exists_section34_filling_of_disk_pair hprep hpack e hD hF
    (hDT.trans inter_subset_right) (subset_union_left.trans hFT) (inter_comm D F ▸ hFD)
  obtain ⟨k, hk, -, hgen, -⟩ := exists_section34_piercing_circle_carrying_generators hprep hpack e
  have htor := (section34_tubes_are_topological_solid_tori hprep hpack e).2
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, hAa, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hG, -, -, -, -, -, -, hPg, -⟩ := hpack
  have hFA' : F ⊆ G (ends e).1 '' CpBd (ends e).1 :=
    hFA.trans (image_mono ((hAa e).1 ▸ inter_subset_left))
  have hJne : (Pg e k).Nonempty := by
    obtain ⟨T, hT⟩ := (hPg e k hk).1
    exact T.piece.bijOn.image_eq ▸ hT.nonempty.image T.piece.map
  have hnot : ¬ Pg e k ⊆ B := fun hsub =>
    htor.not_carriesFundamentalGroupOnto_of_subset_isPLCellOn hB hBT hJne hsub hgen
  obtain ⟨z, hzJ, hzB⟩ := not_subset.mp hnot
  have hzA : z ∈ G (ends e).1 '' CpBd (ends e).1 :=
    image_mono (((hAa e).1 ▸ inter_subset_left) : Aa e ⊆ CpBd (ends e).1)
      (image_mono sdiff_subset ((hPg e k hk).2 hzJ).1)
  have hfront : frontier B ∩ G (ends e).1 '' CpBd (ends e).1 ⊆ F := by
    rw [← hB.boundary_eq_frontier]
    rintro x ⟨hxD | hxF, hxA⟩
    · exact hF.boundary_subset (htrace ▸ ⟨hxD, hxA⟩)
    · exact hxF
  have hmeet := ((hCp _).image (hG _)).inter_eq_disk_of_frontier_inter_subset hF hFA'
    (fun _ hxF => hB.boundary_subset (Or.inr hxF)) hfront ⟨z, hzA, hzB⟩
  have hside := ((hCp _).image (hG _)).subset_or_inter_eq_of_boundary_inter_eq hB hmeet
    subset_union_right
  refine ⟨F, B, hF, hFA, hB, hBT, hmeet, ?_, hside⟩
  have hdiff : frontier B \ G (ends e).1 '' CpBd (ends e).1 = D \ Pg e i := by
    rw [← hB.boundary_eq_frontier]
    ext x
    constructor
    · rintro ⟨hxD | hxF, hxA⟩
      · exact ⟨hxD, fun hxJ => hxA (htrace.superset hxJ).2⟩
      · exact (hxA (hFA' hxF)).elim
    · rintro ⟨hxD, hxJ⟩
      exact ⟨Or.inl hxD, fun hxA => hxJ (htrace ▸ ⟨hxD, hxA⟩)⟩
  rw [hdiff]
  exact hD.closure_sdiff_boundary

end DifferentialGeometry.Topology.PiecewiseLinear
