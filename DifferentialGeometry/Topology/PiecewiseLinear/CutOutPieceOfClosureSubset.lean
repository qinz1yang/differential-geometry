/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularCell
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodManifold
import DifferentialGeometry.Topology.PiecewiseLinear.FrontierBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.GeneratedSubcomplex
import DifferentialGeometry.Topology.PiecewiseLinear.DualCells
import DifferentialGeometry.Topology.PiecewiseLinear.Triangulation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Carrier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_convexHull_subset_face_of_mem_derivedNeighborhood [DecidableEq E]
    {K L : Geometry.SimplicialComplex ℝ E} {u : Finset E}
    (hu : u ∈ (derivedNeighborhood K L).faces) :
    ∃ σ ∈ K.faces, ∃ τ ∈ L.faces, τ.centroid ℝ id ∈ convexHull ℝ (σ : Set E) ∧
      convexHull ℝ (u : Set E) ⊆ convexHull ℝ (σ : Set E) := by
  obtain ⟨d, hd, hne, hL, rfl⟩ := (mem_derivedNeighborhood_faces_iff K L).mp hu
  obtain ⟨e, he, htop⟩ := hd.exists_top hne
  obtain ⟨τ, hτ, hτe⟩ := hL e he
  obtain ⟨σ, hσ, heσ⟩ :=
    (barycentricSubdivision_isSubdivision K).exists_face_subset (hd.mem_faces he)
  exact ⟨σ, hσ, τ, hτ, heσ (subset_convexHull ℝ (e : Set E) (Finset.mem_coe.mpr hτe)),
    (convexHull_image_subset (barycentricSubdivision K)
      (centroid_mem_openSimplex_of_mem_faces _) hd htop).trans heσ⟩

end Carrier

section Ambient

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem SingularTwoCell.exists_cutOutPiece_of_closure_subset [T2Space M] (D : SingularTwoCell M)
    {V₀ V : Set M} (hV : IsOpen V) (hV₀ : closure V₀ ⊆ V) :
    ∃ (Rc Lc Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
      (Ω Nb : Set (EuclideanSpace ℝ (Fin 2))),
      Rc.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 2 Rc ∧
        Lc.faces ⊆ Rc.faces ∧ Ac.faces ⊆ Rc.faces ∧
        Rc.space ⊆ D.domain ∧ Rc.space ⊆ ⇑D ⁻¹' V ∧
        Lc.space = Rc.space ∩ frontier D.domain ∧
        IsOpen Ω ∧ D.domain ∩ ⇑D ⁻¹' closure V₀ ⊆ Ω ∧ D.domain ∩ Ω ⊆ Rc.space ∧
        IsOpen Nb ∧ Rc.space \ Ω ⊆ Nb ∧ Rc.space ∩ Nb ⊆ Ac.space ∧
        Disjoint Ac.space (⇑D ⁻¹' closure V₀) := by
  let _ := ‹T2Space M›
  let : DecidableEq (EuclideanSpace ℝ (Fin 2)) := fun a b => Classical.propDecidable (a = b)
  have hPc : IsCompact D.domain := D.isPLBall_domain.isPolyhedron.isCompact
  have hK₀c : IsCompact (D.domain ∩ ⇑D ⁻¹' closure V₀) :=
    hPc.of_isClosed_subset
      (D.continuousOn.preimage_isClosed_of_isClosed hPc.isClosed isClosed_closure)
      inter_subset_left
  have hBc : IsCompact (D.domain ∩ ⇑D ⁻¹' Vᶜ) :=
    hPc.of_isClosed_subset
      (D.continuousOn.preimage_isClosed_of_isClosed hPc.isClosed hV.isClosed_compl)
      inter_subset_left
  obtain ⟨δ, hδ, hδsub⟩ := hK₀c.exists_thickening_subset_open hBc.isClosed.isOpen_compl
    (fun x hx hxB => hxB.2 (hV₀ hx.2))
  obtain ⟨T₀, hT₀fin, hT₀sp⟩ := D.isPLBall_domain.isPolyhedron.exists_simplicialComplex
  have : Finite T₀.faces := hT₀fin.to_subtype
  obtain ⟨T, hT, hTfin, -, hTdiam⟩ := exists_isSubdivision_diam_lt T₀
    (fun s hs => card_le_finrank_succ_of_mem_faces T₀ hs) (half_pos hδ)
  have : Finite T.faces := hTfin.to_subtype
  have hTsp : T.space = D.domain := hT.space_eq.trans hT₀sp
  have hTman : IsCombinatorialManifoldWithBoundary (1 + 1) T :=
    IsPLBall.isCombinatorialManifoldWithBoundary (by rw [hTsp]; exact D.isPLBall_domain)
  obtain ⟨B, hBT, hBsp⟩ : ∃ B : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)),
      B.faces ⊆ T.faces ∧ frontier D.domain = B.space := by
    have hfr := frontier_space_eq_boundaryComplex_space hTman
    rw [hTsp] at hfr
    refine ⟨_, ?_, hfr⟩
    exact fun s hs => hs.1
  let K₀ := D.domain ∩ ⇑D ⁻¹' closure V₀
  let L := subcomplexGeneratedBy T {σ | (convexHull ℝ (σ : Set _) ∩ K₀).Nonempty}
  have hLT : L.faces ⊆ T.faces := subcomplexGeneratedBy_faces_subset T _
  have hK₀L : K₀ ⊆ L.space := by
    intro x hx
    obtain ⟨σ, hσ, hxσ⟩ := T.mem_space_iff.mp (hTsp ▸ hx.1)
    rw [subcomplexGeneratedBy_space]
    exact mem_iUnion₂.mpr ⟨σ, ⟨hσ, x, hxσ, hx⟩, hxσ⟩
  let Rc := derivedNeighborhood T L
  let Ω := interior (Rc.space ∪ D.domainᶜ)
  have hLΩ : L.space ⊆ Ω := by
    intro x hx
    have h := derivedNeighborhood_mem_nhdsWithin hLT hx
    rw [hTsp] at h
    obtain ⟨O, hO, hxO, hOsub⟩ := mem_nhdsWithin.mp h
    refine mem_interior.mpr ⟨O, fun y hy => ?_, hO, hxO⟩
    by_cases hyP : y ∈ D.domain
    · exact Or.inl (hOsub ⟨hy, hyP⟩)
    · exact Or.inr hyP
  have hRcP : Rc.space ⊆ D.domain := fun x hx => hTsp ▸ derivedNeighborhood_space_subset T L hx
  have hRcV : Rc.space ⊆ ⇑D ⁻¹' V := by
    intro x hx
    obtain ⟨u, hu, hxu⟩ := Rc.mem_space_iff.mp hx
    obtain ⟨σ, hσ, τ, hτ, hτσ, huσ⟩ := exists_convexHull_subset_face_of_mem_derivedNeighborhood hu
    obtain ⟨σ', ⟨hσ'T, q, hqσ', hqK₀⟩, hτσ', hτne⟩ := hτ
    have hcτ : τ.centroid ℝ id ∈ convexHull ℝ (σ' : Set _) :=
      convexHull_mono (Finset.coe_subset.mpr hτσ')
        (openSimplex_subset_convexHull τ (centroid_mem_openSimplex hτne))
    have hd₁ : dist x (τ.centroid ℝ id) < δ / 2 :=
      (Metric.dist_le_diam_of_mem (σ.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isBounded (huσ hxu)
        hτσ).trans_lt (hTdiam σ hσ)
    have hd₂ : dist (τ.centroid ℝ id) q < δ / 2 :=
      (Metric.dist_le_diam_of_mem (σ'.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isBounded hcτ
        hqσ').trans_lt (hTdiam σ' hσ'T)
    have hxt : x ∈ Metric.thickening δ K₀ :=
      Metric.mem_thickening_iff.mpr
        ⟨q, hqK₀, by linarith [dist_triangle x (τ.centroid ℝ id) q]⟩
    by_contra hxV
    exact hδsub hxt ⟨hRcP hx, hxV⟩
  let F := Rc.space \ Ω
  let Lc := subcomplexGeneratedBy Rc {u | convexHull ℝ (u : Set _) ⊆ frontier D.domain}
  let Ac := subcomplexGeneratedBy Rc {u | (convexHull ℝ (u : Set _) ∩ F).Nonempty}
  let Nb := (⋃ u ∈ Rc.faces ∩ {u | ¬ (convexHull ℝ (u : Set _) ∩ F).Nonempty},
    convexHull ℝ (u : Set (EuclideanSpace ℝ (Fin 2))))ᶜ
  have hLc : Lc.space = Rc.space ∩ frontier D.domain := by
    rw [subcomplexGeneratedBy_space]
    apply Subset.antisymm
    · intro x hx
      obtain ⟨u, ⟨hu, hfu⟩, hxu⟩ := mem_iUnion₂.mp hx
      exact ⟨Rc.convexHull_subset_space hu hxu, hfu hxu⟩
    · rintro x ⟨hxR, hxF⟩
      obtain ⟨u, hu, hxu⟩ := Rc.mem_space_iff.mp hxR
      have hu₂ : u ∈ (secondDerived T).faces := derivedNeighborhood_faces_subset T L hu
      obtain ⟨u₀, hu₀, hxu₀⟩ := exists_face_mem_openSimplex (secondDerived T)
        ((secondDerived T).convexHull_subset_space hu₂ hxu)
      have hu₀u : u₀ ⊆ u :=
        face_subset_of_mem_openSimplex_of_mem_convexHull _ hu₀ hu₂ hxu₀ hxu
      have hu₀R : u₀ ∈ Rc.faces :=
        Rc.down_closed hu hu₀u ((secondDerived T).nonempty_of_mem_faces hu₀)
      have hxB : x ∈ (secondDerived B).space := by
        rw [(secondDerived_isSubdivision B).space_eq, ← hBsp]
        exact hxF
      have hu₀B : u₀ ∈ (secondDerived B).faces :=
        mem_faces_of_mem_openSimplex_of_mem_space (secondDerived_faces_subset hBT) hu₀ hxu₀ hxB
      refine mem_iUnion₂.mpr ⟨u₀, ⟨hu₀R, ?_⟩, openSimplex_subset_convexHull u₀ hxu₀⟩
      rw [hBsp, ← (secondDerived_isSubdivision B).space_eq]
      exact (secondDerived B).convexHull_subset_space hu₀B
  refine ⟨Rc, Lc, Ac, Ω, Nb, derivedNeighborhood_faces_finite T L,
    hTman.derivedNeighborhood L, subcomplexGeneratedBy_faces_subset Rc _,
    subcomplexGeneratedBy_faces_subset Rc _, hRcP, hRcV, hLc, isOpen_interior,
    hK₀L.trans hLΩ, fun x hx => (interior_subset hx.2).resolve_right fun h => h hx.1, ?_, ?_,
    ?_, ?_⟩
  · refine isOpen_compl_iff.mpr (Set.Finite.isClosed_biUnion
      ((derivedNeighborhood_faces_finite T L).subset inter_subset_left) fun u _ => ?_)
    exact (u.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isClosed
  · intro x hxF hxU
    obtain ⟨u, ⟨-, hne⟩, hxu⟩ := mem_iUnion₂.mp hxU
    exact hne ⟨x, hxu, hxF⟩
  · rintro x ⟨hxR, hxN⟩
    obtain ⟨u, hu, hxu⟩ := Rc.mem_space_iff.mp hxR
    by_cases h : (convexHull ℝ (u : Set _) ∩ F).Nonempty
    · rw [subcomplexGeneratedBy_space]
      exact mem_iUnion₂.mpr ⟨u, ⟨hu, h⟩, hxu⟩
    · exact absurd (mem_iUnion₂.mpr ⟨u, ⟨hu, h⟩, hxu⟩) hxN
  · rw [Set.disjoint_left]
    intro x hxA hxV₀
    rw [subcomplexGeneratedBy_space] at hxA
    obtain ⟨u, ⟨hu, y, hyu, hyF⟩, hxu⟩ := mem_iUnion₂.mp hxA
    obtain ⟨σ, hσ, -, -, -, huσ⟩ := exists_convexHull_subset_face_of_mem_derivedNeighborhood hu
    have hσL : σ ∈ L.faces :=
      ⟨σ, ⟨hσ, x, huσ hxu, hTsp ▸ T.convexHull_subset_space hσ (huσ hxu), hxV₀⟩,
        Finset.Subset.rfl, T.nonempty_of_mem_faces hσ⟩
    exact hyF.2 (hLΩ (L.convexHull_subset_space hσL (huσ hyu)))

end Ambient

end DifferentialGeometry.Topology.PiecewiseLinear
