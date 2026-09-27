/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSurfaceSubsurface
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSurfaceEssentialSeams

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' a b : E3}

theorem IsCanonicalSurface.component_boundary_empty_or_annulus [d : DecidableEq E3]
    {X : ℤ → Geometry.SimplicialComplex ℝ E3}
    (hX : IsCanonicalSurface X (fun j => φ '' S j) T'' I P' a b)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (h286 : Moise286) (h314 : Moise314) (i : ℤ)
    (hmodel : HasEssentialBoundaryPLEmbeddings (X i) (T'' (2 * i + 1)))
    (hzero₀ : nullTraceCount ((X (i - 1)).space ∪ (X i).space) (T'' (2 * i)) = 0)
    (hzero₁ : nullTraceCount ((X i).space ∪ (X (i + 1)).space) (T'' (2 * (i + 1))) = 0)
    (c : ConnectedComponents (X i).space) :
    (boundaryComplex 2 (connectedComponentComplex (X i) c)).space = ∅ ∨
      ∃ J₀ J₁ : Set E3, IsPLAnnulusWithEnds (connectedComponentComplex (X i) c).space J₀ J₁ ∧
        Disjoint J₀ J₁ ∧
        (J₀ ∈ traceCircles (connectedComponentComplex (X i) c).space (T'' (2 * i)) ∨
          J₀ ∈ traceCircles (connectedComponentComplex (X i) c).space (T'' (2 * (i + 1)))) ∧
        (J₁ ∈ traceCircles (connectedComponentComplex (X i) c).space (T'' (2 * i)) ∨
          J₁ ∈ traceCircles (connectedComponentComplex (X i) c).space (T'' (2 * (i + 1)))) ∧
        ¬ boundsDiskIn J₀ (T'' (2 * i + 1)) ∧ ¬ boundsDiskIn J₁ (T'' (2 * i + 1)) := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  classical
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  let _ : Finite (X i).faces := (hX.finiteFaces i).to_subtype
  let L := connectedComponentComplex (X i) c
  let _ : Finite L.faces := (connectedComponentComplex_faces_finite (X i) c).to_subtype
  have hsub : L.space ⊆ (X i).space :=
    (subset_iUnion (fun d => (connectedComponentComplex (X i) d).space) c).trans
      (iUnion_connectedComponentComplex_space (X i)).subset
  have hlo := (hX.lowerTrace i).of_connected_component (X i) c
  have hhi := (hX.upperTrace i).of_connected_component (X i) c
  let Γ := traceCircles L.space (T'' (2 * i)) ∪ traceCircles L.space (T'' (2 * (i + 1)))
  have hfinite : Γ.Finite := hlo.finiteTrace.union hhi.finiteTrace
  have hboundary : (boundaryComplex 2 L).space =
      L.space ∩ (T'' (2 * i) ∪ T'' (2 * (i + 1))) := by
    dsimp only [L]
    rw [boundaryComplex_space_connectedComponentComplex, hX.boundary i]
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1.2⟩, fun hx => ⟨⟨hsub hx.1, hx.2⟩, hx.1⟩⟩
  have hcover : (boundaryComplex 2 L).space = ⋃ G ∈ Γ, G := by
    rw [hboundary, inter_union_distrib_left, hlo.traceCover, hhi.traceCover]
    ext x
    simp only [Γ, L, mem_union, mem_iUnion, exists_prop, or_and_right, exists_or]
  have hsphere : ∀ G ∈ Γ, IsPLSphere 1 G := by
    intro G hG
    rcases hG with hG | hG
    · exact traceCircles_isPLSphere hG
    · exact traceCircles_isPLSphere hG
  have hessential : ∀ G ∈ Γ, ¬ boundsDiskIn G (T'' (2 * i + 1)) := by
    intro G hG
    rcases hG with hG | hG
    · have hrow := traceCircles_subset_of_inter_subset (hX.lowerTrace i).traceCover
        (fun _ hx => ⟨hsub hx.1, hx.2⟩) hG
      exact hX.lower_seam_not_boundsDiskIn htw h314 i hzero₀ hrow
    · have hrow := traceCircles_subset_of_inter_subset (hX.upperTrace i).traceCover
        (fun _ hx => ⟨hsub hx.1, hx.2⟩) hG
      exact hX.upper_seam_not_boundsDiskIn htw h314 i hzero₁ hrow
  have hTdis : Disjoint (T'' (2 * i)) (T'' (2 * (i + 1))) :=
    (htw.apart (2 * i) (2 * (i + 1)) (by rw [le_abs]; omega)).mono
      (htw.boundary_subset_outer _) (htw.boundary_subset_outer _)
  have hdis : ∀ G ∈ Γ, ∀ H ∈ Γ, G ≠ H → Disjoint G H := by
    intro G hG H hH hGH
    rcases hG with hG | hG <;> rcases hH with hH | hH
    · exact pairwiseDisjoint_traceCircles _ _ hG hH hGH
    · exact hTdis.mono ((traceCircles_subset hG).trans inter_subset_right)
        ((traceCircles_subset hH).trans inter_subset_right)
    · exact hTdis.symm.mono ((traceCircles_subset hG).trans inter_subset_right)
        ((traceCircles_subset hH).trans inter_subset_right)
    · exact pairwiseDisjoint_traceCircles _ _ hG hH hGH
  by_cases hclosed : (boundaryComplex 2 L).space = ∅
  · exact Or.inl hclosed
  · right
    obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr hclosed
    obtain ⟨H, hH, -⟩ := mem_iUnion₂.mp (hcover.subset hx)
    have hHbd : H ⊆ (boundaryComplex 2 L).space :=
      fun y hy => hcover.symm.subset (mem_iUnion₂.mpr ⟨H, hH, hy⟩)
    have hmodelL := hmodel c H (hsphere H hH) hHbd (hessential H hH)
    let _ : Finite Γ := hfinite.to_subtype
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin Γ
    let G : Fin n → Set E3 := fun k => (e.symm k).val
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) (e ⟨H, hH⟩).isLt
    have hGmem (k : Fin n) : G k ∈ Γ := (e.symm k).property
    have hGdis : Pairwise fun j k => Disjoint (G j) (G k) := by
      intro j k hjk
      exact hdis _ (hGmem j) _ (hGmem k) fun heq => hjk (e.symm.injective (Subtype.ext heq))
    have hGcover : (boundaryComplex 2 L).space = ⋃ k, G k := by
      ext y
      constructor
      · intro hy
        obtain ⟨G', hG', hyG⟩ := mem_iUnion₂.mp (hcover.subset hy)
        exact mem_iUnion.mpr ⟨e ⟨G', hG'⟩, by simpa only [G, Equiv.symm_apply_apply] using hyG⟩
      · intro hy
        obtain ⟨k, hyG⟩ := mem_iUnion.mp hy
        exact hcover.symm.subset (mem_iUnion₂.mpr ⟨G k, hGmem k, hyG⟩)
    have hS : IsCombinatorialSolidTorus (S'' (2 * i + 1)) := by
      simpa using (htw.config (2 * i + 1)).isPolyhedralSolidTorus 0
    rw [htw.boundary_eq (2 * i + 1)] at hmodelL
    obtain ⟨j, k, hjk, hann⟩ := hmodelL.exists_annulus_of_essential_boundary L
      ((hX.manifold i).connectedComponentComplex c)
      (isConnected_connectedComponentComplex_space _ _)
      hS h286 n G hn (fun k => hsphere _ (hGmem k)) hGdis hGcover (fun k => by
        rw [← htw.boundary_eq (2 * i + 1)]
        exact hessential _ (hGmem k))
    exact ⟨G j, G k, hann, hGdis hjk, hGmem j, hGmem k,
      hessential _ (hGmem j), hessential _ (hGmem k)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
