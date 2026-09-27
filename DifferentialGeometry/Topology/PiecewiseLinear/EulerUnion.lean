/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ComplexUnion

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPolyhedron.eulerChar_union_add_inter {P Q : Set E}
    (hP : IsPolyhedron P) (hQ : IsPolyhedron Q) (k : Type) [Field k] :
    Homology.eulerChar k (TopCat.of ↥(P ∪ Q)) + Homology.eulerChar k (TopCat.of ↥(P ∩ Q)) =
      Homology.eulerChar k (TopCat.of P) + Homology.eulerChar k (TopCat.of Q) := by
  obtain ⟨K, hKfin, hKspace⟩ := hP.exists_simplicialComplex
  obtain ⟨L, hLfin, hLspace⟩ := hQ.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  obtain ⟨T, hTfin, -, hA, hB⟩ := exists_simplicialComplex_space_union K L
  let _ : Finite T.faces := hTfin.to_subtype
  let A := restrict T K.space
  let B := restrict T L.space
  let _ : Finite A.faces := (restrict_faces_finite T K.space).to_subtype
  let _ : Finite B.faces := (restrict_faces_finite T L.space).to_subtype
  have hcompat : ∀ s ∈ A.faces, ∀ t ∈ B.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E)) := by
    intro s hs t ht
    exact T.inter_subset_convexHull hs.1 ht.1
  have h := DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_union_add_inter A B hcompat
  rwa [eulerChar_eq_singular (unionComplex A B hcompat) k,
    eulerChar_eq_singular (intersectionComplex A B) k,
    eulerChar_eq_singular A k, eulerChar_eq_singular B k,
    unionComplex_space, intersectionComplex_space A B hcompat,
    hA.space_eq, hB.space_eq, hKspace, hLspace] at h

theorem eulerChar_eq_add_sub_of_space_union (R A B I : Geometry.SimplicialComplex ℝ E)
    [Finite R.faces] [Finite A.faces] [Finite B.faces] [Finite I.faces]
    (hR : R.space = A.space ∪ B.space) (hI : I.space = A.space ∩ B.space) :
    eulerChar R = eulerChar A + eulerChar B - eulerChar I := by
  have h := (isPolyhedron_space A).eulerChar_union_add_inter (isPolyhedron_space B) ℚ
  rw [← hR, ← hI, ← eulerChar_eq_singular R ℚ, ← eulerChar_eq_singular I ℚ,
    ← eulerChar_eq_singular A ℚ, ← eulerChar_eq_singular B ℚ] at h
  omega

theorem IsPolyhedron.eulerChar_union_of_disjoint {P Q : Set E}
    (hP : IsPolyhedron P) (hQ : IsPolyhedron Q) (hdis : Disjoint P Q)
    (k : Type) [Field k] :
    Homology.eulerChar k (TopCat.of ↥(P ∪ Q)) =
      Homology.eulerChar k (TopCat.of P) + Homology.eulerChar k (TopCat.of Q) := by
  let _ : IsEmpty ↥(P ∩ Q) := ⟨fun x => disjoint_left.mp hdis x.property.1 x.property.2⟩
  have h := hP.eulerChar_union_add_inter hQ k
  simpa only [Homology.eulerChar_of_isEmpty, add_zero] using h

theorem eulerChar_eq_add_of_space_disjoint_union
    (R A B : Geometry.SimplicialComplex ℝ E) [Finite R.faces] [Finite A.faces] [Finite B.faces]
    (hR : R.space = A.space ∪ B.space) (hdis : Disjoint A.space B.space) :
    eulerChar R = eulerChar A + eulerChar B := by
  rw [eulerChar_eq_singular R ℚ, eulerChar_eq_singular A ℚ, eulerChar_eq_singular B ℚ, hR]
  exact (isPolyhedron_space A).eulerChar_union_of_disjoint (isPolyhedron_space B) hdis ℚ

theorem eulerChar_eq_add_of_space_union_of_isPLSphere_one
    (R A B : Geometry.SimplicialComplex ℝ E) [Finite R.faces] [Finite A.faces] [Finite B.faces]
    (hR : R.space = A.space ∪ B.space) (hI : IsPLSphere 1 (A.space ∩ B.space)) :
    eulerChar R = eulerChar A + eulerChar B := by
  obtain ⟨I, hIfin, hIspace⟩ := hI.isPolyhedron.exists_simplicialComplex
  let _ : Finite I.faces := hIfin.to_subtype
  have h := eulerChar_eq_add_sub_of_space_union R A B I hR hIspace
  rwa [eulerChar_of_isPLSphere_one I (hIspace.symm ▸ hI), sub_zero] at h

end DifferentialGeometry.Topology.PiecewiseLinear
