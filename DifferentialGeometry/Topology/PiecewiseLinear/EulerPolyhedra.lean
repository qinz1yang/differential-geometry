/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLBallSphere
import DifferentialGeometry.Topology.PiecewiseLinear.StellarSphere
import DifferentialGeometry.Topology.PiecewiseLinear.Subdivision

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.Topology.SimplicialComplex

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def eulerChar (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] : ℤ :=
  faceEulerChar K.toPreAbstractSimplicialComplex

theorem eulerChar_eq_singular (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (k : Type) [Field k] :
    eulerChar K = Homology.eulerChar k (TopCat.of K.space) :=
  (eulerChar_geometricSpace_eq_faceEulerChar K k).symm

theorem eulerChar_eq_of_isPLHomeomorphOn [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (L : Geometry.SimplicialComplex ℝ F) [Finite L.faces] {f : E → F}
    (hf : IsPLHomeomorphOn f K.space L.space) : eulerChar K = eulerChar L := by
  calc
    eulerChar K = Homology.eulerChar ℚ (TopCat.of K.space) := eulerChar_eq_singular K ℚ
    _ = Homology.eulerChar ℚ (TopCat.of L.space) :=
      Homology.eulerChar_eq_of_homeomorph ℚ hf.homeomorph
    _ = eulerChar L := (eulerChar_eq_singular L ℚ).symm

theorem eulerChar_eq_of_isSubdivision {K K' : Geometry.SimplicialComplex ℝ E}
    [Finite K.faces] [Finite K'.faces] (hK' : IsSubdivision K' K) :
    eulerChar K' = eulerChar K := by
  rw [eulerChar_eq_singular K' ℚ, eulerChar_eq_singular K ℚ, hK'.space_eq]

theorem eulerChar_of_isPLBall [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {n : ℕ}
    (hK : IsPLBall n K.space) : eulerChar K = 1 := by
  obtain ⟨f, hf⟩ := hK
  calc
    eulerChar K = Homology.eulerChar ℚ (TopCat.of K.space) := eulerChar_eq_singular K ℚ
    _ = Homology.eulerChar ℚ (TopCat.of (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 1)))) :=
      (Homology.eulerChar_eq_of_homeomorph ℚ hf.homeomorph).symm
    _ = 1 := eulerChar_stdSimplex n

theorem eulerChar_of_isPLSphere [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {n : ℕ}
    (hK : IsPLSphere n K.space) : eulerChar K = 1 + (-1 : ℤ) ^ n := by
  obtain ⟨f, hf⟩ := hK
  calc
    eulerChar K = Homology.eulerChar ℚ (TopCat.of K.space) := eulerChar_eq_singular K ℚ
    _ = Homology.eulerChar ℚ (TopCat.of (stdSimplexBoundary (n + 1))) :=
      (Homology.eulerChar_eq_of_homeomorph ℚ hf.homeomorph).symm
    _ = 1 + (-1 : ℤ) ^ n := eulerChar_stdSimplexBoundary n

theorem eulerChar_of_isPLSphere_one [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLSphere 1 K.space) : eulerChar K = 0 := by
  simpa using eulerChar_of_isPLSphere K hK

def intersectionComplex (K L : Geometry.SimplicialComplex ℝ E) :
    Geometry.SimplicialComplex ℝ E where
  faces := K.faces ∩ L.faces
  isRelLowerSet_faces := by
    rintro s ⟨hsK, hsL⟩
    exact ⟨K.nonempty_of_mem_faces hsK, fun t hts ht =>
      ⟨K.down_closed hsK hts ht, L.down_closed hsL hts ht⟩⟩
  indep hs := K.indep hs.1
  inter_subset_convexHull hs ht := K.inter_subset_convexHull hs.1 ht.1

theorem mem_intersectionComplex_faces_iff {K L : Geometry.SimplicialComplex ℝ E}
    {s : Finset E} : s ∈ (intersectionComplex K L).faces ↔ s ∈ K.faces ∧ s ∈ L.faces :=
  Iff.rfl

theorem intersectionComplex_faces_finite (K L : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) : (intersectionComplex K L).faces.Finite :=
  hK.subset fun _ hs => hs.1

instance finite_intersectionComplex_faces (K L : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] : Finite (intersectionComplex K L).faces :=
  (intersectionComplex_faces_finite K L (Set.toFinite K.faces)).to_subtype

instance finite_unionComplex_faces (K L : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] [Finite L.faces]
    (h : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E))) :
    Finite (unionComplex K L h).faces :=
  (unionComplex_faces_finite K L h (Set.toFinite K.faces) (Set.toFinite L.faces)).to_subtype

theorem eulerChar_union_add_inter (K L : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] [Finite L.faces]
    (h : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E))) :
    eulerChar (unionComplex K L h) + eulerChar (intersectionComplex K L) =
      eulerChar K + eulerChar L := by
  have hu : (unionComplex K L h).toPreAbstractSimplicialComplex =
      K.toPreAbstractSimplicialComplex ⊔ L.toPreAbstractSimplicialComplex := by
    ext s
    rfl
  have hi : (intersectionComplex K L).toPreAbstractSimplicialComplex =
      K.toPreAbstractSimplicialComplex ⊓ L.toPreAbstractSimplicialComplex := by
    ext s
    rfl
  unfold eulerChar
  rw [faceEulerChar_congr hu, faceEulerChar_congr hi]
  exact faceEulerChar_sup_add_faceEulerChar_inf K.toPreAbstractSimplicialComplex
    L.toPreAbstractSimplicialComplex

end DifferentialGeometry.Topology.PiecewiseLinear
