/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement
import DifferentialGeometry.Topology.PiecewiseLinear.SphereSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.SpanningDiskAnnulus
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitLocalTrace
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitRealization
import DifferentialGeometry.Topology.Connected.Separation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

namespace IsCombinatorialManifoldWithBoundary

open Classical in
theorem exists_surface_split_and_cap_of_spanning_disk_avoiding
    (M K : Geometry.SimplicialComplex ℝ E) [Finite M.faces] [Finite K.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifold 2 K) (hor : IsOrientable 2 K)
    {Δ U : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ)
    (hmeet : Δ ∩ K.space = r '' stdSimplexBoundary 2)
    (hKM : K.space ⊆ M.space) (hΔM : Δ ⊆ M.space)
    (hΔboundary : Disjoint Δ (boundaryComplex 3 M).space)
    (hU : U ∈ 𝓝ˢ[K.space] (r '' stdSimplexBoundary 2))
    {Z : Set E} (hZclosed : IsClosed Z) (hΔZ : Disjoint Δ Z) :
    ∃ (source split result B : Geometry.SimplicialComplex ℝ E)
      (cap₀ cap₁ : Set E) (p₀ p₁ : (Fin 3 → ℝ) → E),
      source.faces.Finite ∧ split.faces.Finite ∧ result.faces.Finite ∧
      IsSubdivision source K ∧ IsCombinatorialManifoldWithBoundary 2 split ∧
      IsCombinatorialManifold 2 result ∧
      IsPLHomeomorphOn p₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) cap₀ ∧
      IsPLHomeomorphOn p₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) cap₁ ∧
      Disjoint cap₀ cap₁ ∧
      split.space ∩ cap₀ = p₀ '' stdSimplexBoundary 2 ∧
      split.space ∩ cap₁ = p₁ '' stdSimplexBoundary 2 ∧
      (boundaryComplex 2 split).space =
        p₀ '' stdSimplexBoundary 2 ∪ p₁ '' stdSimplexBoundary 2 ∧
       result.space = split.space ∪ cap₀ ∪ cap₁ ∧
       Nonempty (SurfaceSplitAndCap source split result) ∧
       B.faces.Finite ∧ IsPLBall 3 B.space ∧ B.space ⊆ Zᶜ ∧
       (K.space ∪ Δ) \ B.space = result.space \ B.space ∧
       (boundaryComplex 3 B).space \ result.space ⊆ (K.space ∪ Δ)ᶜ ∧
       IsPathConnected ((boundaryComplex 3 B).space \ result.space) := by
  let hΔ : IsPLBall 2 Δ := ⟨r, hr⟩
  obtain ⟨R, hRfin, hR, -, -, W, ρ, D₀, D₁, q₀, q₁,
      -, hWK, -, -, hρ, -, -, -, hRD, hq₀, hq₁, hΔopen₀, hΔopen₁,
      hD₀D₁, -, -, hq₀boundary, hq₁boundary, hRmeet₀, hRmeet₁,
       hRboundary, hWR, hcover, hpairUnion, htotal, -, hpairNhds, -⟩ :=
    hK.exists_annulus_complement_of_spanning_disk K hor hr hmeet hU
  let _ : Finite R.faces := hRfin.to_subtype
  let C := K.space ∪ Δ
  have hCM : C ⊆ M.space := union_subset hKM hΔM
  have hpairC : D₀ ∪ D₁ ⊆ C := by
    rw [hpairUnion]
    exact union_subset subset_union_right (hWK.trans subset_union_left)
  have hD₀C : D₀ ⊆ C := subset_union_left.trans hpairC
  have hD₁C : D₁ ⊆ C := subset_union_right.trans hpairC
  have hD₀M : D₀ ⊆ M.space := hD₀C.trans hCM
  have hD₁M : D₁ ⊆ M.space := hD₁C.trans hCM
  have hΔD₀ : Δ ⊆ D₀ := hΔopen₀.trans
    ((image_mono openSimplex_stdVertices_subset_stdSimplex).trans hq₀.image_eq.subset)
  have hΔD₁ : Δ ⊆ D₁ := hΔopen₁.trans
    ((image_mono openSimplex_stdVertices_subset_stdSimplex).trans hq₁.image_eq.subset)
  let V := (R.spaceᶜ ∩ (boundaryComplex 3 M).spaceᶜ) ∩ Zᶜ
  have hRclosed : IsClosed R.space := (isPolyhedron_space R).isClosed
  have hMboundaryClosed : IsClosed (boundaryComplex 3 M).space :=
    (isPolyhedron_space (boundaryComplex 3 M)).isClosed
  have hVopen : IsOpen V :=
    (hRclosed.isOpen_compl.inter hMboundaryClosed.isOpen_compl).inter hZclosed.isOpen_compl
  have hΔV : Δ ⊆ V := by
    intro x hxΔ
    exact ⟨⟨fun hxR => disjoint_left.mp hRD hxR hxΔ,
      fun hxBoundary => disjoint_left.mp hΔboundary hxΔ hxBoundary⟩,
      fun hxZ => disjoint_left.mp hΔZ hxΔ hxZ⟩
  have hV : V ∈ 𝓝ˢ[M.space] Δ := Filter.mem_inf_of_left <|
    mem_nhdsSet_iff_forall.mpr fun x hx => hVopen.mem_nhds (hΔV hx)
  have hVdis : Disjoint V (boundaryComplex 3 M).space := by
    rw [disjoint_left]
    intro x hxV hxBoundary
    exact hxV.1.2 hxBoundary
  obtain ⟨N, B, g, q, A₁, Δ₁, C', hBfin, hN, hB, hΔN, -, hNV,
      -, hBN, hg, hmiddleB, -, -, -, -, -, -, -, hCtrace, -, -, hq,
      hinnerSide, hinnerBoundary, hinnerMiddleDisjoint, hinnerMeet, houterInClosure,
      hA₁boundary⟩ :=
    hM.exists_surface_split_local_traces_with_side_trace hΔ hq₀ hq₁
      hΔopen₀ hΔopen₁ hΔD₀ hΔD₁ hD₀D₁ hD₀M hD₁M hD₀C hD₁C
      (by simpa only [C] using hpairNhds) hV hVdis
  let _ : Finite B.faces := hBfin.to_subtype
  have hNR : Disjoint N R.space := by
    rw [disjoint_left]
    intro x hxN hxR
    exact (hNV hxN).1.1 hxR
  have hmiddleBall : IsPLBall 2 (D₁ ∩ N) := ⟨g, hg⟩
  have hboundarySphere : IsPLSphere 2 (boundaryComplex 3 B).space :=
    isPLSphere_boundaryComplex_space_of_isPLBall B hB
  have hinnerSphere : IsPLSphere 1 (q '' stdSimplexBoundary 2) :=
    hq.isPLSphere_image_stdSimplexBoundary
  obtain ⟨Q, qQ, hqQ, hQboundary, hmiddleQ, hqQboundary⟩ :=
    hmiddleBall.exists_disjoint_isPLBall_with_boundary_of_isPLSphere_two
      hboundarySphere hmiddleB hinnerSphere hinnerBoundary hinnerMiddleDisjoint.symm
  have hstdBoundary : stdSimplexBoundary 2 ⊆ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) := by
    intro x hx
    have hx' : x ∈
        (simplexBoundary (stdVertices 1) (stdVertices_affineIndependent 1)).space := by
      rwa [simplexBoundary_stdVertices_space]
    exact simplexBoundary_stdVertices_space_subset 1 hx'
  have hqQboundaryQ : qQ '' stdSimplexBoundary 2 ⊆ Q :=
    (image_mono hstdBoundary).trans hqQ.image_eq.subset
  let P := closure (D₀ \ (D₀ ∩ N))
  have hD₀ball : IsPLBall 2 D₀ := ⟨q₀, hq₀⟩
  have hinnerBall : IsPLBall 2 (D₀ ∩ N) := ⟨q, hq⟩
  have hPpoly : IsPolyhedron P := hD₀ball.isPolyhedron.closure_sdiff hinnerBall.isPolyhedron
  have hPD₀ : P ⊆ D₀ := closure_minimal sdiff_subset hD₀ball.isPolyhedron.isClosed
  have hinnerD₀ : D₀ ∩ N ⊆ D₀ := inter_subset_left
  have hPcover : P ∪ (D₀ ∩ N) = D₀ := by
    apply Subset.antisymm
    · exact union_subset hPD₀ hinnerD₀
    · intro x hxD₀
      by_cases hxInner : x ∈ D₀ ∩ N
      · exact Or.inr hxInner
      · exact Or.inl (subset_closure ⟨hxD₀, hxInner⟩)
  have hPinner : P ∩ (D₀ ∩ N) = q '' stdSimplexBoundary 2 := by
    simpa only [P] using hinnerMeet
  have hPQ : P ∩ Q = q '' stdSimplexBoundary 2 := by
    apply Subset.antisymm
    · rintro x ⟨hxP, hxQ⟩
      have hxB : x ∈ B.space :=
        boundaryComplex_space_subset 3 B (hQboundary hxQ)
      have hxInner : x ∈ D₀ ∩ N := hinnerSide.subset ⟨hPD₀ hxP, hxB⟩
      exact hPinner.subset ⟨hxP, hxInner⟩
    · intro x hx
      have hxMeet := hPinner.symm.subset hx
      exact ⟨hxMeet.1, hqQboundaryQ (hqQboundary.symm.subset hx)⟩
  obtain ⟨H, hH, hHP⟩ := exists_isPLHomeomorphOn_replace_ball hPpoly hq hqQ
    rfl hqQboundary hPinner hPQ
  let cap₀ := P ∪ Q
  have hHD₀ : IsPLHomeomorphOn H D₀ cap₀ := by
    change IsPLHomeomorphOn H D₀ (P ∪ Q)
    rw [← hPcover]
    exact hH
  let p₀ := H ∘ q₀
  have hp₀ : IsPLHomeomorphOn p₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) cap₀ := hq₀.trans hHD₀
  have hp₀boundary : p₀ '' stdSimplexBoundary 2 = q₀ '' stdSimplexBoundary 2 := by
    calc
      p₀ '' stdSimplexBoundary 2 = H '' (q₀ '' stdSimplexBoundary 2) := by
        change (fun x => H (q₀ x)) '' stdSimplexBoundary 2 =
          H '' (q₀ '' stdSimplexBoundary 2)
        exact (image_image H q₀ (stdSimplexBoundary 2)).symm
      _ = id '' (q₀ '' stdSimplexBoundary 2) :=
        (hHP.mono houterInClosure).image_eq
      _ = q₀ '' stdSimplexBoundary 2 := image_id _
  have hPdisjointD₁ : Disjoint P D₁ := by
    rw [disjoint_left]
    intro x hxP hxD₁
    have hxΔ : x ∈ Δ := hD₀D₁.subset ⟨hPD₀ hxP, hxD₁⟩
    have hxInner : x ∈ D₀ ∩ N := ⟨hΔD₀ hxΔ, hΔN hxΔ⟩
    have hxBoundary : x ∈ q '' stdSimplexBoundary 2 := hPinner.subset ⟨hxP, hxInner⟩
    exact disjoint_left.mp hinnerMiddleDisjoint hxBoundary ⟨hxD₁, hΔN hxΔ⟩
  have hQdisjointD₁ : Disjoint Q D₁ := by
    rw [disjoint_left]
    intro x hxQ hxD₁
    have hxN : x ∈ N := hBN (boundaryComplex_space_subset 3 B (hQboundary hxQ))
    exact disjoint_left.mp hmiddleQ ⟨hxD₁, hxN⟩ hxQ
  have hcapDisjoint : Disjoint cap₀ D₁ := by
    rw [disjoint_left]
    intro x hxCap hxD₁
    rcases hxCap with hxP | hxQ
    · exact disjoint_left.mp hPdisjointD₁ hxP hxD₁
    · exact disjoint_left.mp hQdisjointD₁ hxQ hxD₁
  have hRP : R.space ∩ P = q₀ '' stdSimplexBoundary 2 := by
    apply Subset.antisymm
    · intro x hx
      exact hRmeet₀.subset ⟨hx.1, hPD₀ hx.2⟩
    · intro x hx
      have hxMeet := hRmeet₀.symm.subset hx
      exact ⟨hxMeet.1, houterInClosure hx⟩
  have hRQ : R.space ∩ Q = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro x hx
    have hxN : x ∈ N := hBN (boundaryComplex_space_subset 3 B (hQboundary hx.2))
    exact disjoint_left.mp hNR hxN hx.1
  have hRcap₀ : R.space ∩ cap₀ = p₀ '' stdSimplexBoundary 2 := by
    change R.space ∩ (P ∪ Q) = p₀ '' stdSimplexBoundary 2
    rw [inter_union_distrib_left, hRP, hRQ, union_empty, hp₀boundary]
  have hWRρ : W ∩ R.space = ρ '' ((r '' stdSimplexBoundary 2) ×ˢ {(-1 : ℝ), 1}) := by
    rw [hWR, hq₀boundary, hq₁boundary, ← image_union, ← prod_union, singleton_union]
  have hJ : IsPLSphere 1 (r '' stdSimplexBoundary 2) :=
    hr.isPLSphere_image_stdSimplexBoundary
  obtain ⟨source, split, hsourcefin, hsplitfin, hsourceK, hsplitR,
      hsplitMan, ⟨hsplitData⟩⟩ :=
    exists_surface_split_along_polygon_of_annulus_complement K R hR hJ hρ
      hcover hWRρ
  let _ : Finite split.faces := hsplitfin.to_subtype
  have hsplitCap₀ : split.space ∩ cap₀ = p₀ '' stdSimplexBoundary 2 := by
    rw [hsplitR.space_eq, hRcap₀]
  have hsplitCap₁ : split.space ∩ D₁ = q₁ '' stdSimplexBoundary 2 := by
    rw [hsplitR.space_eq, hRmeet₁]
  have hsplitBoundary : (boundaryComplex 2 split).space =
      p₀ '' stdSimplexBoundary 2 ∪ q₁ '' stdSimplexBoundary 2 := by
    rw [boundaryComplex_space_of_isSubdivision R split hR hsplitR,
      hRboundary, hp₀boundary]
  obtain ⟨split', result, hsplit'fin, hresultfin, hsplit'split,
      hresultMan, hresultSpace, hcapData⟩ :=
    hsplitData.exists_surface_split_and_cap_of_disk_pair source split hsplitMan
      hp₀ hq₁ hcapDisjoint hsplitCap₀ hsplitCap₁ hsplitBoundary
  let _ : Finite split'.faces := hsplit'fin.to_subtype
  let _ : Finite result.faces := hresultfin.to_subtype
  have hsplit'Man : IsCombinatorialManifoldWithBoundary 2 split' :=
    hsplitMan.of_isSubdivision hsplit'split
  have hsplit'Cap₀ : split'.space ∩ cap₀ = p₀ '' stdSimplexBoundary 2 := by
    rw [hsplit'split.space_eq, hsplitCap₀]
  have hsplit'Cap₁ : split'.space ∩ D₁ = q₁ '' stdSimplexBoundary 2 := by
    rw [hsplit'split.space_eq, hsplitCap₁]
  have hsplit'Boundary : (boundaryComplex 2 split').space =
      p₀ '' stdSimplexBoundary 2 ∪ q₁ '' stdSimplexBoundary 2 := by
    rw [boundaryComplex_space_of_isSubdivision split split' hsplitMan hsplit'split,
      hsplitBoundary]
  have hresultSpace' : result.space = split'.space ∪ cap₀ ∪ D₁ := by
    rwa [hsplit'split.space_eq]
  have hsplit'R : split'.space = R.space := hsplit'split.space_eq.trans hsplitR.space_eq
  have hBZ : B.space ⊆ Zᶜ := fun x hxB => (hNV (hBN hxB)).2
  have houtside : (K.space ∪ Δ) \ B.space = result.space \ B.space := by
    ext x
    constructor
    · rintro ⟨hxC, hxB⟩
      have hxTotal : x ∈ R.space ∪ D₀ ∪ D₁ := htotal.symm.subset hxC
      refine ⟨hresultSpace'.symm.subset ?_, hxB⟩
      rcases hxTotal with (hxR | hxD₀) | hxD₁
      · exact Or.inl (Or.inl (hsplit'R.symm.subset hxR))
      · rcases hPcover.symm.subset hxD₀ with hxP | hxInner
        · exact Or.inl (Or.inr (show x ∈ cap₀ from Or.inl hxP))
        · exact (hxB (hinnerSide.symm.subset hxInner).2).elim
      · exact Or.inr hxD₁
    · rintro ⟨hxResult, hxB⟩
      have hxTarget := hresultSpace'.subset hxResult
      refine ⟨htotal.subset ?_, hxB⟩
      rcases hxTarget with (hxSplit | hxCap) | hxD₁
      · exact Or.inl (Or.inl (hsplit'R.subset hxSplit))
      · change x ∈ P ∪ Q at hxCap
        rcases hxCap with hxP | hxQ
        · exact Or.inl (Or.inr (hPcover.subset (Or.inl hxP)))
        · exact (hxB (boundaryComplex_space_subset 3 B (hQboundary hxQ))).elim
      · exact Or.inr hxD₁
  have hD₁result : D₁ ⊆ result.space := by
    intro x hxD₁
    exact hresultSpace'.symm.subset (Or.inr hxD₁)
  have hQresult : Q ⊆ result.space := by
    intro x hxQ
    apply hresultSpace'.symm.subset
    exact Or.inl (Or.inr (show x ∈ cap₀ from Or.inr hxQ))
  have hqresult : q '' stdSimplexBoundary 2 ⊆ result.space := by
    intro x hxq
    exact hQresult (hqQboundaryQ (hqQboundary.symm.subset hxq))
  have hboundarySafe : (boundaryComplex 3 B).space \ result.space ⊆
      (K.space ∪ Δ)ᶜ := by
    intro x hx hxC
    have hxB : x ∈ B.space := boundaryComplex_space_subset 3 B hx.1
    have hxTrace : x ∈ (D₁ ∩ N) ∪ A₁ := by
      exact hCtrace.subset ⟨hxC, hxB⟩
    rcases hxTrace with hxMiddle | hxA₁
    · exact hx.2 (hD₁result hxMiddle.1)
    · rcases hA₁boundary ⟨hxA₁, hx.1⟩ with hxMiddle | hxq
      · exact hx.2 (hD₁result hxMiddle.1)
      · exact hx.2 (hqresult hxq)
  have hboundarySdiff : (boundaryComplex 3 B).space \ result.space =
      (boundaryComplex 3 B).space \ ((D₁ ∩ N) ∪ Q) := by
    ext x
    constructor
    · rintro ⟨hxBoundary, hxResult⟩
      refine ⟨hxBoundary, ?_⟩
      rintro (hxMiddle | hxQ)
      · exact hxResult (hD₁result hxMiddle.1)
      · exact hxResult (hQresult hxQ)
    · rintro ⟨hxBoundary, hxRemove⟩
      refine ⟨hxBoundary, ?_⟩
      intro hxResult
      have hxTarget := hresultSpace'.subset hxResult
      have hxB : x ∈ B.space := boundaryComplex_space_subset 3 B hxBoundary
      have hxN : x ∈ N := hBN hxB
      rcases hxTarget with (hxSplit | hxCap) | hxD₁
      · exact disjoint_left.mp hNR hxN (hsplit'R.subset hxSplit)
      · change x ∈ P ∪ Q at hxCap
        rcases hxCap with hxP | hxQ
        · have hxInner : x ∈ D₀ ∩ N := hinnerSide.subset ⟨hPD₀ hxP, hxB⟩
          have hxq : x ∈ q '' stdSimplexBoundary 2 := hPinner.subset ⟨hxP, hxInner⟩
          exact hxRemove (Or.inr (hqQboundaryQ (hqQboundary.symm.subset hxq)))
        · exact hxRemove (Or.inr hxQ)
      · exact hxRemove (Or.inl ⟨hxD₁, hxN⟩)
  have hQball : IsPLBall 2 Q := ⟨qQ, hqQ⟩
  have hboundaryPath : IsPathConnected ((boundaryComplex 3 B).space \ result.space) := by
    rw [hboundarySdiff]
    exact hboundarySphere.isPathConnected_sdiff_union_of_disjoint_isPLBall_two
      hmiddleBall hmiddleB hQball hQboundary hmiddleQ
  exact ⟨source, split', result, B, cap₀, D₁, p₀, q₁, hsourcefin, hsplit'fin,
    hresultfin, hsourceK, hsplit'Man, hresultMan, hp₀, hq₁, hcapDisjoint,
    hsplit'Cap₀, hsplit'Cap₁, hsplit'Boundary, hresultSpace', hcapData,
    hBfin, hB, hBZ, houtside, hboundarySafe, hboundaryPath⟩

open Classical in
theorem exists_surface_split_and_cap_of_spanning_disk
    (M K : Geometry.SimplicialComplex ℝ E) [Finite M.faces] [Finite K.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifold 2 K) (hor : IsOrientable 2 K)
    {Δ U : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ)
    (hmeet : Δ ∩ K.space = r '' stdSimplexBoundary 2)
    (hKM : K.space ⊆ M.space) (hΔM : Δ ⊆ M.space)
    (hΔboundary : Disjoint Δ (boundaryComplex 3 M).space)
    (hU : U ∈ 𝓝ˢ[K.space] (r '' stdSimplexBoundary 2)) :
    ∃ (source split result : Geometry.SimplicialComplex ℝ E)
      (cap₀ cap₁ : Set E) (p₀ p₁ : (Fin 3 → ℝ) → E),
      source.faces.Finite ∧ split.faces.Finite ∧ result.faces.Finite ∧
      IsSubdivision source K ∧ IsCombinatorialManifoldWithBoundary 2 split ∧
      IsCombinatorialManifold 2 result ∧
      IsPLHomeomorphOn p₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) cap₀ ∧
      IsPLHomeomorphOn p₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) cap₁ ∧
      Disjoint cap₀ cap₁ ∧
      split.space ∩ cap₀ = p₀ '' stdSimplexBoundary 2 ∧
      split.space ∩ cap₁ = p₁ '' stdSimplexBoundary 2 ∧
      (boundaryComplex 2 split).space =
        p₀ '' stdSimplexBoundary 2 ∪ p₁ '' stdSimplexBoundary 2 ∧
      result.space = split.space ∪ cap₀ ∪ cap₁ ∧
      Nonempty (SurfaceSplitAndCap source split result) := by
  obtain ⟨source, split, result, B, cap₀, cap₁, p₀, p₁, hsourcefin, hsplitfin,
      hresultfin, hsource, hsplit, hresult, hp₀, hp₁, hdisjoint,
      hsplitCap₀, hsplitCap₁, hsplitBoundary, hresultSpace, hcap, -, -, -, -, -, -⟩ :=
    hM.exists_surface_split_and_cap_of_spanning_disk_avoiding M K hK hor hr hmeet hKM hΔM
      hΔboundary hU isClosed_empty (by simp)
  exact ⟨source, split, result, cap₀, cap₁, p₀, p₁, hsourcefin, hsplitfin,
    hresultfin, hsource, hsplit, hresult, hp₀, hp₁, hdisjoint,
    hsplitCap₀, hsplitCap₁, hsplitBoundary, hresultSpace, hcap⟩

open Classical in
theorem exists_surface_split_and_cap_of_spanning_disk_preserving_separation
    (M K : Geometry.SimplicialComplex ℝ E) [Finite M.faces] [Finite K.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifold 2 K) (hor : IsOrientable 2 K)
    (hdim : Module.finrank ℝ E = 3)
    {Δ U : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ)
    (hmeet : Δ ∩ K.space = r '' stdSimplexBoundary 2)
    (hKM : K.space ⊆ M.space) (hΔM : Δ ⊆ M.space)
    (hΔboundary : Disjoint Δ (boundaryComplex 3 M).space)
    (hU : U ∈ 𝓝ˢ[K.space] (r '' stdSimplexBoundary 2))
    {H T : Set E} (hHclosed : IsClosed H) (hTclosed : IsClosed T)
    (hH : IsPreconnected H) (hT : IsPreconnected T)
    (hsep : Separates (K.space ∪ Δ) H T) :
    ∃ (source split result : Geometry.SimplicialComplex ℝ E)
      (cap₀ cap₁ : Set E) (p₀ p₁ : (Fin 3 → ℝ) → E),
      source.faces.Finite ∧ split.faces.Finite ∧ result.faces.Finite ∧
      IsSubdivision source K ∧ IsCombinatorialManifoldWithBoundary 2 split ∧
      IsCombinatorialManifold 2 result ∧
      IsPLHomeomorphOn p₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) cap₀ ∧
      IsPLHomeomorphOn p₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) cap₁ ∧
      Disjoint cap₀ cap₁ ∧
      split.space ∩ cap₀ = p₀ '' stdSimplexBoundary 2 ∧
      split.space ∩ cap₁ = p₁ '' stdSimplexBoundary 2 ∧
      (boundaryComplex 2 split).space =
        p₀ '' stdSimplexBoundary 2 ∪ p₁ '' stdSimplexBoundary 2 ∧
      result.space = split.space ∪ cap₀ ∪ cap₁ ∧
      Nonempty (SurfaceSplitAndCap source split result) ∧
      Separates result.space H T := by
  have hΔtargets : Disjoint Δ (H ∪ T) := by
    rw [disjoint_left]
    intro x hxΔ hxTarget
    rcases hxTarget with hxH | hxT
    · exact hsep.left_subset_compl hxH (Or.inr hxΔ)
    · exact hsep.right_subset_compl hxT (Or.inr hxΔ)
  obtain ⟨source, split, result, B, cap₀, cap₁, p₀, p₁, hsourcefin, hsplitfin,
      hresultfin, hsource, hsplit, hresult, hp₀, hp₁, hdisjoint,
      hsplitCap₀, hsplitCap₁, hsplitBoundary, hresultSpace, hcap,
      hBfin, hB, hBtargets, houtside, hboundarySafe, hboundaryPath⟩ :=
    hM.exists_surface_split_and_cap_of_spanning_disk_avoiding M K hK hor hr hmeet hKM hΔM
      hΔboundary hU (hHclosed.union hTclosed) hΔtargets
  let _ : Finite B.faces := hBfin.to_subtype
  let _ : Finite result.faces := hresultfin.to_subtype
  have hfrontier : frontier B.space = (boundaryComplex 3 B).space :=
    frontier_space_eq_boundaryComplex_space_of_finrank (n := 2) (by simpa using hdim) B
      hB.isCombinatorialManifoldWithBoundary
  have hfrontierSafe : frontier B.space \ result.space ⊆ (K.space ∪ Δ)ᶜ := by
    rwa [hfrontier]
  have hfrontierPath : IsPathConnected (frontier B.space \ result.space) := by
    rwa [hfrontier]
  have hHB : H ⊆ B.spaceᶜ := fun x hxH hxB => hBtargets hxB (Or.inl hxH)
  have hTB : T ⊆ B.spaceᶜ := fun x hxT hxB => hBtargets hxB (Or.inr hxT)
  have hresultSep : Separates result.space H T :=
    hsep.of_frontier_replacement
      (fun U hU hconn => hU.isConnected_iff_isPathConnected.mp hconn)
      (isPolyhedron_space result).isClosed hB.isPolyhedron.isClosed houtside
      hfrontierSafe hfrontierPath hH hT hHB hTB
  exact ⟨source, split, result, cap₀, cap₁, p₀, p₁, hsourcefin, hsplitfin,
    hresultfin, hsource, hsplit, hresult, hp₀, hp₁, hdisjoint,
    hsplitCap₀, hsplitCap₁, hsplitBoundary, hresultSpace, hcap, hresultSep⟩

end IsCombinatorialManifoldWithBoundary

end DifferentialGeometry.Topology.PiecewiseLinear
