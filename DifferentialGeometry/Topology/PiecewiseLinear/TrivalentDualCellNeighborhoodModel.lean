/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DualCellPiercingNeighborhoods
import DifferentialGeometry.Topology.PiecewiseLinear.GeneratedSubcomplex
import DifferentialGeometry.Topology.PiecewiseLinear.StdSimplexCone

/-!
# A trivalent graph model with common dual-cell piercing neighborhoods
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_trivalent_graph_subcomplex_model :
    ∃ (K L : Geometry.SimplicialComplex ℝ (Fin 5 → ℝ))
        (v : Fin 5 → ℝ) (w : Fin 3 → Fin 5 → ℝ),
      K.faces.Finite ∧ L.faces.Finite ∧ IsCombinatorialManifold 3 K ∧
      L.faces ⊆ K.faces ∧ (∀ s ∈ L.faces, s.card ≤ 2) ∧
      Function.Injective w ∧ (∀ i, v ≠ w i) ∧
      ∀ u, u ≠ v →
        (@insert (Fin 5 → ℝ) (Finset (Fin 5 → ℝ))
          (@Finset.instInsert (Fin 5 → ℝ) (Classical.decEq _)) v {u} ∈ L.faces ↔
          u ∈ Set.range w) := by
  let _ : DecidableEq (Fin 5 → ℝ) := Classical.decEq _
  let p : Fin 5 → Fin 5 → ℝ := fun i => Pi.single i 1
  let ι : Fin 3 → Fin 5 := fun i => ⟨i.1 + 1, by omega⟩
  let v := p 0
  let w : Fin 3 → Fin 5 → ℝ := fun i => p (ι i)
  let T := stdVertices 3
  let K := simplexBoundary T (stdVertices_affineIndependent 3)
  let edgeFamily : Set (Finset (Fin 5 → ℝ)) :=
    {s | ∃ i, s = {v, w i}}
  let L := subcomplexGeneratedBy K edgeFamily
  have hι : Function.Injective ι := by
    intro i j hij
    apply Fin.ext
    have hval := congrArg Fin.val hij
    change i.1 + 1 = j.1 + 1 at hval
    omega
  have hwinj : Function.Injective w := by
    exact (stdVertex_injective 3).comp hι
  have hvw : ∀ i, v ≠ w i := by
    intro i hvi
    have hi : (0 : Fin 5) = ι i := stdVertex_injective 3 hvi
    have hval := congrArg Fin.val hi
    change 0 = i.1 + 1 at hval
    omega
  have hpT (i : Fin 5) : p i ∈ T := by
    simp [p, T, stdVertices]
  have hTcard : T.card = 5 := by
    simpa [T] using card_stdVertices 3
  have hedgeK (i : Fin 3) : {v, w i} ∈ K.faces := by
    apply mem_simplexBoundary_faces_iff.mpr
    refine ⟨?_, Finset.insert_nonempty _ _, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hpT 0
      · exact hpT (ι i)
    · intro heq
      have hcardEq := congrArg Finset.card heq
      rw [Finset.card_pair (hvw i), hTcard] at hcardEq
      omega
  have hKfin : K.faces.Finite := simplexBoundary_faces_finite T (stdVertices_affineIndependent 3)
  let _ : Finite K.faces := hKfin.to_subtype
  have hLfin : L.faces.Finite := subcomplexGeneratedBy_faces_finite K edgeFamily
  have hLK : L.faces ⊆ K.faces := subcomplexGeneratedBy_faces_subset K edgeFamily
  have hcard : ∀ s ∈ L.faces, s.card ≤ 2 := by
    rintro s ⟨t, ht, hst, -⟩
    obtain ⟨i, rfl⟩ := ht.2
    calc
      s.card ≤ ({v, w i} : Finset (Fin 5 → ℝ)).card := Finset.card_le_card hst
      _ = 2 := Finset.card_pair (hvw i)
  have hedgeL (i : Fin 3) : {v, w i} ∈ L.faces :=
    ⟨{v, w i}, ⟨hedgeK i, ⟨i, rfl⟩⟩, Finset.Subset.rfl, Finset.insert_nonempty _ _⟩
  have hneighbors : ∀ u, u ≠ v → ({v, u} ∈ L.faces ↔ u ∈ Set.range w) := by
    intro u huv
    constructor
    · rintro ⟨t, ht, hsub, -⟩
      obtain ⟨i, rfl⟩ := ht.2
      have hu : u ∈ ({v, w i} : Finset (Fin 5 → ℝ)) := hsub (by simp)
      have huw : u = w i := by simpa [huv] using hu
      exact ⟨i, huw.symm⟩
    · rintro ⟨i, rfl⟩
      exact hedgeL i
  exact ⟨K, L, v, w, hKfin, hLfin,
    (isPLSphere_simplexBoundary_std 3).isCombinatorialManifold,
    hLK, hcard, hwinj, hvw, hneighbors⟩

open Classical in
theorem exists_trivalent_graphDualCell_piercing_neighborhood_model :
    ∃ (K L : Geometry.SimplicialComplex ℝ (Fin 5 → ℝ))
        (v : Fin 5 → ℝ) (w : Fin 3 → Fin 5 → ℝ)
        (J C : Fin 3 → Set (Fin 5 → ℝ))
        (f : Fin 3 → (Fin 5 → ℝ) → Fin 5 → ℝ)
        (A B : Fin 3 → Set (Fin 5 → ℝ)),
      K.faces.Finite ∧ L.faces.Finite ∧ IsCombinatorialManifold 3 K ∧
      L.faces ⊆ K.faces ∧ (∀ s ∈ L.faces, s.card ≤ 2) ∧
      Function.Injective w ∧ (∀ i, v ≠ w i) ∧
      (∀ u, u ≠ v →
        (@insert (Fin 5 → ℝ) (Finset (Fin 5 → ℝ))
          (@Finset.instInsert (Fin 5 → ℝ) (Classical.decEq _)) v {u} ∈ L.faces ↔
          u ∈ Set.range w)) ∧
      (∀ i,
        IsPLSphere 1 (J i) ∧
        IsPLHomeomorphOn (f i) (graphDualCell K L (w i)).space (C i) ∧
        C i ⊆ (graphDualCell K L (w i)).space ∧ EqOn (f i) id (J i) ∧
        IsPLBall 3 (C i) ∧ (graphDualCell K L v).space ∩ C i = J i ∧
        IsNestedCommonAnnularDerivedNeighborhood K (A i) (B i) (J i)
          (@boundaryComplex (Fin 5 → ℝ) _ _ (Classical.decEq _) 3
            (graphDualCell K L v)).space
          (f i '' (@boundaryComplex (Fin 5 → ℝ) _ _ (Classical.decEq _) 3
            (graphDualCell K L (w i))).space)) ∧
      Pairwise fun i j => Disjoint (J i) (J j) := by
  let _ : DecidableEq (Fin 5 → ℝ) := Classical.decEq _
  obtain ⟨K, L, v, w, hKfin, hLfin, hK, hLK, hcard, hwinj, hvw, hneighbors⟩ :=
    exists_trivalent_graph_subcomplex_model
  let _ : Finite K.faces := hKfin.to_subtype
  obtain ⟨J, C, f, A, B, hdata, hpair⟩ :=
    hK.exists_trivalent_piercings_with_nested_common_neighborhoods K L hLK hcard w
      hwinj hvw hneighbors isOpen_univ (fun _ => subset_univ _)
  refine ⟨K, L, v, w, J, C, f, A, B, hKfin, hLfin, hK, hLK, hcard, hwinj, hvw,
    hneighbors, ?_, hpair⟩
  intro i
  rcases hdata i with ⟨hJ, -, -, hf, hCsub, hfix, hC, hinter, -, hAB⟩
  exact ⟨hJ, hf, hCsub, hfix, hC, hinter, hAB⟩

end DifferentialGeometry.Topology.PiecewiseLinear
