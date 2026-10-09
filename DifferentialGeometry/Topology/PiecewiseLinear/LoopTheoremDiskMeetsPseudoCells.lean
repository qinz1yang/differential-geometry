/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskVocabulary

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section MeetsPseudoCells

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd Ec Eint Ebd : Finset E3 → Set E3} {h : E3 → E3} {Cpp : E3 → Set E3}

theorem IsHandleDecompositionOfTube.exists_subset_handlePiece
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp) {Z : Set E3}
    (hZ : IsPreconnected Z) (hZne : Z.Nonempty) (hZN : Z ⊆ interior N')
    (hZE : Disjoint Z (⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e)) :
    ∃ v ∈ K.vertices, Z ⊆ Cpp v := by
  classical
  set A := ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e with hAdef
  have hfin : {f : Finset E3 | f ∈ K.faces ∧ f.card = 2}.Finite :=
    hd.tube.facesFinite.subset fun f hf => hf.1
  have hAc : IsClosed A := hfin.isClosed_biUnion fun f hf => by
    rw [(hd.pseudoCell f hf.1 hf.2).carrierEq, ← (hd.pseudoCell f hf.1 hf.2).closureEq]
    exact isClosed_closure
  obtain ⟨z, hz⟩ := hZne
  have hO : IsOpen (interior N' \ A) := isOpen_interior.sdiff hAc
  have hZO : Z ⊆ interior N' \ A := fun y hy => ⟨hZN hy, Set.disjoint_left.mp hZE hy⟩
  have hW : IsOpen (connectedComponentIn (interior N' \ A) z) := hO.connectedComponentIn
  have hZW : Z ⊆ connectedComponentIn (interior N' \ A) z := hZ.subset_connectedComponentIn hz hZO
  have hzN : z ∈ N' := interior_subset (hZN hz)
  rw [hd.coversTube] at hzN
  obtain ⟨v, hv, hzv⟩ := mem_iUnion₂.mp hzN
  refine ⟨v, hv, ?_⟩
  have hcl := hd.componentClosure v hv
  rw [hcl] at hzv ⊢
  obtain ⟨w, hwW, hwV⟩ := mem_closure_iff.mp hzv _ hW (hZW hz)
  have hsub : connectedComponentIn (interior N' \ A) z ⊆ N' \ A := fun y hy =>
    ⟨interior_subset (connectedComponentIn_subset _ _ hy).1,
      (connectedComponentIn_subset _ _ hy).2⟩
  have hWV : connectedComponentIn (interior N' \ A) z ⊆ connectedComponentIn (N' \ A) (h v) := by
    rw [connectedComponentIn_eq hwV]
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn hwW hsub
  exact hZW.trans (hWV.trans subset_closure)

theorem HasNoHandleLoopTheoremDisk.inter_pseudoCells_nonempty
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp) {X : Set E3}
    (h7 : HasNoHandleLoopTheoremDisk K h N' Cpp X) {Δ : Set E3}
    (hΔ : IsLoopTheoremDisk (h '' K.space) N' (frontier X) Δ) :
    (Δ ∩ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e).Nonempty := by
  by_contra hne
  obtain ⟨r, hr, hΔsub, -⟩ := id hΔ
  have hpre : IsPreconnected Δ := by
    rw [← hr.image_eq]
    exact (Convexity.StdSimplex.convex_coordinateSet ℝ (Fin 3)).isPreconnected.image r
      hr.isPiecewiseAffineOn.continuousOn
  have hΔne : Δ.Nonempty := by
    rw [← hr.image_eq]
    exact ⟨r _, mem_image_of_mem r (Convexity.StdSimplex.single_mem_coordinateSet ℝ (0 : Fin 3))⟩
  obtain ⟨v, hv, hΔv⟩ := hd.exists_subset_handlePiece hpre hΔne (fun y hy => (hΔsub hy).1)
    (Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hne))
  exact h7 v hv Δ hΔ hΔv

end MeetsPseudoCells

end DifferentialGeometry.Topology.PiecewiseLinear
