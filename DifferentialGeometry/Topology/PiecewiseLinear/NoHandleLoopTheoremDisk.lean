/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.SeparatorLocation
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsIsPLBallSupersetOfExteriorCompression
import DifferentialGeometry.Topology.PiecewiseLinear.HandlePieceEulerChar
import DifferentialGeometry.Topology.PiecewiseLinear.HandlePiecePushOff
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeHandlePieces
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedronLocalConnectedness
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCompressionSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.TubeSurfaceTransfer

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Compression

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd Ec Eint Ebd : Finset E3 → Set E3} {h : E3 → E3} {Cpp : E3 → Set E3}
  {XK : Geometry.SimplicialComplex ℝ E3}

theorem IsPolyhedralTubeNeighborhood.exists_hasConnectedHandlePieces_of_isConnected
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
    (h34 : HasSinglePolygonTraces K h Ec XK.space) (hXc : IsConnected XK.space)
    (hFc : IsConnected (frontier XK.space)) :
    ∃ AK : E3 → Geometry.SimplicialComplex ℝ E3, HasConnectedHandlePieces K Ec Cpp XK.space AK := by
  classical
  have hKX : h '' K.space ⊆ XK.space :=
    (subset_interior_iff_mem_nhdsSet.mpr h2.isNeighborhood).trans interior_subset
  have hconn : IsConnected K.space :=
    hd.tube.isConnected_space_of_isConnected hXc (h2.subsetInterior.trans interior_subset) hKX
  have hex := fun v (hv : v ∈ K.vertices) => h2.exists_handlePieceSurface hd h34 hFc hconn hv
  let AK : E3 → Geometry.SimplicialComplex ℝ E3 :=
    fun v => if hv : v ∈ K.vertices then (hex v hv).choose else XK
  refine ⟨AK, hXc, hFc, fun v hv => ?_⟩
  obtain ⟨hA1, hA2, hA3, hA4, hA5⟩ := (hex v hv).choose_spec
  have hAK : AK v = (hex v hv).choose := dite_eq_left hv
  rw [hAK]
  refine ⟨hA1, hA2, hA3, hA4, ?_⟩
  convert hA5 using 3

theorem IsPolyhedralTubeNeighborhood.exists_bettiOne_lt_of_isLoopTheoremDisk
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
    (h34 : HasSinglePolygonTraces K h Ec XK.space) (hXc : IsConnected XK.space)
    (hFc : IsConnected (frontier XK.space)) {Δ : Set E3}
    (hΔ : IsLoopTheoremDisk (h '' K.space) N' (frontier XK.space) Δ)
    (hΔE : Disjoint Δ (⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e)) :
    ∃ XK' : Geometry.SimplicialComplex ℝ E3,
      IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK' ∧
        HasSinglePolygonTraces K h Ec XK'.space ∧ IsConnected XK'.space ∧
          IsConnected (frontier XK'.space) ∧
            Homology.bettiOne (frontier XK'.space) < Homology.bettiOne (frontier XK.space) := by
  classical
  have : Finite XK.faces := h2.facesFinite.to_subtype
  have ht := hd.tube
  have hXcl : IsClosed XK.space := (isPolyhedron_space XK).isClosed
  have hKX : h '' K.space ⊆ XK.space :=
    (subset_interior_iff_mem_nhdsSet.mpr h2.isNeighborhood).trans interior_subset
  have hconn : IsConnected K.space :=
    ht.isConnected_space_of_isConnected hXc (h2.subsetInterior.trans interior_subset) hKX
  have hKN : K.space ⊆ N :=
    (subset_interior_iff_mem_nhdsSet.mpr ht.isNeighborhood).trans interior_subset
  have hKpre : IsPreconnected (h '' K.space) :=
    (hconn.image h (ht.continuousOn.mono hKN)).isPreconnected
  have hTpre : IsPreconnected (interior N')ᶜ :=
    (hd.isConnected_compl_interior hconn).isPreconnected
  obtain ⟨r, hr, hΔsub, hΔB, hb, hnull⟩ := hΔ
  obtain ⟨S, hSfin, hSm, hSeq⟩ :=
    h2.isManifold.exists_isCombinatorialManifold_space_eq_frontier (n := 2)
      finrank_euclideanSpace_fin
  have : Finite S.faces := hSfin.to_subtype
  have hScl : IsClosed S.space := (isPolyhedron_space S).isClosed
  have hSc : IsConnected S.space := by
    rw [hSeq]
    exact hFc
  have hmeet : Δ ∩ S.space = r '' stdSimplexBoundary 2 := by
    rw [hSeq]
    exact hΔB
  have hnon : ∀ T : Set E3, T = frontier XK.space → ∀ hbT : r '' stdSimplexBoundary 2 ⊆ T,
      ¬ (⟨Set.inclusion hbT, continuous_inclusion hbT⟩ :
        C(r '' stdSimplexBoundary 2, T)).Nullhomotopic := by
    rintro T rfl hbT
    exact hnull
  set A := ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e with hAdef
  have hfin : {f : Finset E3 | f ∈ K.faces ∧ f.card = 2}.Finite :=
    ht.facesFinite.subset fun f hf => hf.1
  have hAc : IsClosed A := hfin.isClosed_biUnion fun f hf => (hd.pseudoCell f hf.1 hf.2).isClosed
  have hKc : IsClosed (h '' K.space) := ht.isCompact_image_space.isClosed
  have hU : IsOpen (interior N' \ (h '' K.space ∪ A)) := isOpen_interior.sdiff (hKc.union hAc)
  have hΔU : Δ ⊆ interior N' \ (h '' K.space ∪ A) := fun y hy =>
    ⟨(hΔsub hy).1, fun hy' => hy'.elim (hΔsub hy).2 (Set.disjoint_left.mp hΔE hy)⟩
  obtain ⟨Nb, W, D₀, D₁, _, ρ, r₀, r₁, hNb, hNbU, _, _, _, _, _, _, hwall, _, _, _,
    hρ, hzero, _, hr₀, hr₁, hdis, hfront, hmeet₀, hmeet₁, hbd₀, hbd₁⟩ :=
    hSm.exists_compression_neighborhood_of_spanning_disk S hSc finrank_euclideanSpace_fin hr hmeet
      hU hΔU
  have hsep : Separates S.space (h '' K.space) (interior N')ᶜ := by
    rw [hSeq]
    refine separates_frontier (subset_interior_iff_mem_nhdsSet.mpr h2.isNeighborhood) ?_
    rw [hXcl.isOpen_compl.interior_eq]
    exact compl_subset_compl.mpr h2.subsetInterior
  obtain ⟨P, hPfin, hPm, hPc, _, _, hPC, hPsep, hβ, hPcomp⟩ :=
    hSm.exists_separating_component_bettiOne_lt_of_spanning_disk S hSc finrank_euclideanSpace_fin
      hr hmeet (hnon S.space hSeq _) hρ hzero hNb hwall hr₀ hr₁ hdis hfront hmeet₀ hmeet₁ hbd₀
      hbd₁ hKpre hTpre hsep (fun y hy hyN => (hNbU hyN).2 (Or.inl hy))
      (fun y hy hyN => hy (hNbU hyN).1)
  have : Finite P.faces := hPfin.to_subtype
  have hNbcl : IsClosed Nb := hNb.isPolyhedron.isClosed
  have hcaps : D₀ ∪ D₁ ⊆ Nb := by
    intro y hy
    apply hNbcl.frontier_subset
    rw [hfront]
    exact hy.elim (fun h' => Or.inl (Or.inr h')) Or.inr
  have hrest : closure (S.space \ W) ⊆ S.space := closure_minimal sdiff_subset hScl
  have hEN : ∀ e ∈ K.faces, e.card = 2 → ∀ y ∈ Ec e, y ∉ Nb := fun e he hcard y hy hyN =>
    (hNbU hyN).2 (Or.inr (mem_iUnion₂.mpr ⟨e, ⟨he, hcard⟩, hy⟩))
  have hPS : ∀ y ∈ P.space, y ∉ Nb → y ∈ S.space := by
    intro y hy hyN
    rcases hPC hy with (hy' | hy') | hy'
    · exact hrest hy'
    · exact absurd (hcaps (Or.inl hy')) hyN
    · exact absurd (hcaps (Or.inr hy')) hyN
  have hBE : ∀ e ∈ K.faces, e.card = 2 → Ec e ∩ P.space ⊆ frontier XK.space := by
    rintro e he hcard y ⟨hye, hyP⟩
    rw [← hSeq]
    exact hPS y hyP (hEN e he hcard y hye)
  have hloc : ∀ e ∈ K.faces, e.card = 2 → ∀ x ∈ Ec e ∩ P.space,
      ∀ᶠ y in 𝓝 x, y ∈ P.space ↔ y ∈ frontier XK.space := by
    rintro e he hcard x ⟨hxe, hxP⟩
    have hxN := hEN e he hcard x hxe
    have hxS : x ∈ S.space := hPS x hxP hxN
    let _ : LocallyConnectedSpace S.space := locallyConnectedSpace_space S
    have hF : IsOpen ((Subtype.val : S.space → E3) ⁻¹' Nbᶜ) :=
      hNbcl.isOpen_compl.preimage continuous_subtype_val
    have hxF : (⟨x, hxS⟩ : S.space) ∈ (Subtype.val : S.space → E3) ⁻¹' Nbᶜ := hxN
    obtain ⟨G, hG, hGQ⟩ := isOpen_induced_iff.mp (hF.connectedComponentIn (x := ⟨x, hxS⟩))
    have hxG : x ∈ G := by
      have hx' := mem_connectedComponentIn hxF
      rw [← hGQ] at hx'
      exact hx'
    have hQP : Subtype.val '' connectedComponentIn ((Subtype.val : S.space → E3) ⁻¹' Nbᶜ)
        ⟨x, hxS⟩ ⊆ P.space := by
      rw [← hPcomp x hxP]
      refine (isPreconnected_connectedComponentIn.image _
        continuous_subtype_val.continuousOn).subset_connectedComponentIn
        ⟨⟨x, hxS⟩, mem_connectedComponentIn hxF, rfl⟩ ?_
      rintro _ ⟨q, hq, rfl⟩
      have hqN : (q : E3) ∉ Nb := connectedComponentIn_subset _ _ hq
      exact Or.inl (Or.inl (subset_closure ⟨q.2, fun hqW => hqN (hwall.symm.subset hqW).2⟩))
    filter_upwards [hG.mem_nhds hxG, hNbcl.isOpen_compl.mem_nhds hxN] with y hyG hyN
    constructor
    · intro hyP
      rw [← hSeq]
      exact hPS y hyP hyN
    · intro hyF
      have hyS : y ∈ S.space := by
        rw [hSeq]
        exact hyF
      apply hQP
      refine ⟨⟨y, hyS⟩, ?_, rfl⟩
      rw [← hGQ]
      exact hyG
  obtain ⟨XK', h2', h34', hX', hfr'⟩ :=
    h2.exists_of_separating_surface hd hconn h34 P hPm hPc hPsep hBE hloc
  refine ⟨XK', h2', h34', hX', ?_, ?_⟩
  · rw [hfr']
    exact hPc
  · rw [hfr', ← hSeq]
    exact hβ

end Compression

section Leaves

variable {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {N N' : Set (EuclideanSpace ℝ (Fin 3))}
  {C Cpp : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3))}
  {D Dbd Ec Eint Ebd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
  {XK : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {AK : EuclideanSpace ℝ (Fin 3) → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}

theorem exists_hasNoHandleLoopTheoremDisk
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
    (h34 : HasSinglePolygonTraces K h Ec XK.space)
    (h56 : HasConnectedHandlePieces K Ec Cpp XK.space AK) :
    ∃ (XK' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (AK' : EuclideanSpace ℝ (Fin 3) → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))),
      IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK' ∧
      HasSinglePolygonTraces K h Ec XK'.space ∧
      HasConnectedHandlePieces K Ec Cpp XK'.space AK' ∧
      HasNoHandleLoopTheoremDisk K h N' Cpp XK'.space := by
  classical
  have hex : ∃ n : ℕ, ∃ (XK' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (AK' : EuclideanSpace ℝ (Fin 3) → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))),
      IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK' ∧
      HasSinglePolygonTraces K h Ec XK'.space ∧
      HasConnectedHandlePieces K Ec Cpp XK'.space AK' ∧
      Homology.bettiOne (frontier XK'.space) = n := ⟨_, XK, AK, h2, h34, h56, rfl⟩
  obtain ⟨XK₀, AK₀, h2₀, h34₀, h56₀, hn₀⟩ := Nat.find_spec hex
  refine ⟨XK₀, AK₀, h2₀, h34₀, h56₀, fun v hv Δ hΔ hΔC => ?_⟩
  obtain ⟨Δ', hΔ', -, hΔ'E⟩ := h2₀.exists_isLoopTheoremDisk_disjoint_pseudoCells hd hv hΔ hΔC
  obtain ⟨XK₁, h2₁, h34₁, hX₁, hF₁, hlt⟩ :=
    h2₀.exists_bettiOne_lt_of_isLoopTheoremDisk hd h34₀ h56₀.1 h56₀.2.1 hΔ' hΔ'E
  obtain ⟨AK₁, h56₁⟩ := h2₁.exists_hasConnectedHandlePieces_of_isConnected hd h34₁ hX₁ hF₁
  refine Nat.find_min hex (m := Homology.bettiOne (frontier XK₁.space)) ?_
    ⟨XK₁, AK₁, h2₁, h34₁, h56₁, rfl⟩
  rw [← hn₀]
  exact hlt

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
