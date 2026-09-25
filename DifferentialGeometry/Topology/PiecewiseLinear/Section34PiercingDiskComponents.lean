import DifferentialGeometry.Topology.PiecewiseLinear.Section34InnermostAnnulusDisk
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnClosure

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem connectedComponentIn_sdiff_eq_of_closed_partition {M : Type*} [TopologicalSpace M]
    {S A D E J T : Set M} (hD : IsClosed D) (hE : IsClosed E)
    (hcover : D ∪ E = S) (hboundary : D ∩ E = J) (hAS : A ⊆ S) (hDA : D ⊆ A)
    (htrace : D ∩ T = J) (hconn : IsPreconnected (D \ J)) {x : M} (hx : x ∈ D \ J) :
    connectedComponentIn (A \ T) x = D \ J := by
  have hJT : J ⊆ T := htrace ▸ inter_subset_right
  have hsub : D \ J ⊆ A \ T := fun y hy =>
    ⟨hDA hy.1, fun hyT => hy.2 (htrace ▸ ⟨hy.1, hyT⟩)⟩
  have hCS : connectedComponentIn (A \ T) x ⊆ S :=
    (connectedComponentIn_subset _ _).trans (sdiff_subset.trans hAS)
  have hCJ : Disjoint (connectedComponentIn (A \ T) x) J :=
    disjoint_left.mpr fun y hy hyJ => (connectedComponentIn_subset _ _ hy).2 (hJT hyJ)
  have hCD : connectedComponentIn (A \ T) x ⊆ D := by
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp isPreconnected_connectedComponentIn
      D E hD hE (hcover ▸ hCS) (by rw [hboundary]; exact hCJ.inter_eq) with h | h
    · exact h
    · exact (hx.2 (hboundary ▸ ⟨hx.1, h (mem_connectedComponentIn (hsub hx))⟩)).elim
  apply Subset.antisymm
  · exact fun y hy => ⟨hCD hy, fun hyJ => disjoint_left.mp hCJ hy hyJ⟩
  · exact hconn.subset_connectedComponentIn hx hsub

theorem IsPLCellOn.exists_closed_boundary_disk_complement {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B D J : Set M} (hS : IsPLCellOn 3 S B) (hD : IsPLCellOn 2 D J) (hDB : D ⊆ B) :
    ∃ E : Set M, IsClosed E ∧ D ∪ E = B ∧ D ∩ E = J := by
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
  have hEcompact : IsCompact E :=
    hP.isPLSphere_frontier.isPolyhedron.isCompact.of_isClosed_subset isClosed_closure hES
  have hcover : δ ∪ E = frontier P := by
    apply Subset.antisymm (union_subset hδS hES)
    intro x hx
    by_cases hxδ : x ∈ δ
    · exact Or.inl hxδ
    · exact Or.inr (subset_closure ⟨hx, hxδ⟩)
  have hmeet : δ ∩ E = Function.invFunOn u P '' J :=
    (hP.isPLSphere_frontier.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hδS).trans
      hqb.symm
  have hback (X : Set M) (hXP : X ⊆ u '' P) :
      u '' (Function.invFunOn u P '' X) = X := by
    rw [image_image]
    exact (image_congr fun x hx =>
      hu.injOn.bijOn_image.invOn_invFunOn.2 (hXP hx)).trans (image_id' X)
  refine ⟨u '' E,
    (hEcompact.image_of_continuousOn (hu.continuousOn.mono (hES.trans hfront))).isClosed, ?_, ?_⟩
  · rw [← hback D hDP, ← image_union, hcover, ← hB]
  · rw [← hback D hDP, ← hu.injOn.image_inter (hδS.trans hfront) (hES.trans hfront),
      hmeet, hback J (hD.boundary_subset.trans hDP)]

theorem IsPLCellOn.connectedComponentIn_sdiff_eq_disk {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B A D J T : Set M} (hS : IsPLCellOn 3 S B) (hD : IsPLCellOn 2 D J)
    (hAB : A ⊆ B) (hDA : D ⊆ A) (htrace : D ∩ T = J)
    (hconn : IsPreconnected (D \ J)) {x : M} (hx : x ∈ D \ J) :
    connectedComponentIn (A \ T) x = D \ J := by
  obtain ⟨E, hE, hcover, hboundary⟩ :=
    hS.exists_closed_boundary_disk_complement hD (hDA.trans hAB)
  exact connectedComponentIn_sdiff_eq_of_closed_partition hD.isCompact.isClosed hE
    hcover hboundary hAB hDA htrace hconn hx

theorem IsPLCellOn.closure_connectedComponentIn_sdiff_eq_disk {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B A D J T : Set M} (hS : IsPLCellOn 3 S B) (hD : IsPLCellOn 2 D J)
    (hAB : A ⊆ B) (hDA : D ⊆ A) (htrace : D ∩ T = J)
    (hconn : IsPreconnected (D \ J)) {x : M} (hx : x ∈ D \ J) :
    closure (connectedComponentIn (A \ T) x) = D := by
  rw [hS.connectedComponentIn_sdiff_eq_disk hD hAB hDA htrace hconn hx]
  exact hD.closure_sdiff_boundary

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

theorem exists_section34_innermost_disk_component
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    (hexists : ∃ i < cnt e, ∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧
      D ⊆ G (ends e).2 '' Bb e) :
    ∃ (i : ℕ) (D : Set M₂), i < cnt e ∧ IsPLCellOn 2 D (Pg e i) ∧
      D ⊆ G (ends e).2 '' Bb e ∧ D ∩ G (ends e).1 '' CpBd (ends e).1 = Pg e i ∧
      IsConnected (D \ Pg e i) ∧
      (D \ Pg e i ⊆ interior (G (ends e).1 '' Cp (ends e).1) ∨
        Disjoint (D \ Pg e i) (G (ends e).1 '' Cp (ends e).1)) ∧
      ∀ x ∈ D \ Pg e i,
        connectedComponentIn (G (ends e).2 '' Bb e \ G (ends e).1 '' CpBd (ends e).1) x =
          D \ Pg e i := by
  obtain ⟨i, D, hi, hD, hDA, hmeet, hconn, hside⟩ :=
    exists_section34_innermost_disk_in_annulus hprep hpack e hexists
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, -, hBb, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGcp, -⟩ := hpack
  refine ⟨i, D, hi, hD, hDA, hmeet, hconn, hside, ?_⟩
  intro x hx
  exact ((hCp (ends e).2).image (hGcp (ends e).2)).connectedComponentIn_sdiff_eq_disk
    hD (image_mono (hBb e).1) hDA hmeet hconn.isPreconnected hx

end DifferentialGeometry.Topology.PiecewiseLinear
