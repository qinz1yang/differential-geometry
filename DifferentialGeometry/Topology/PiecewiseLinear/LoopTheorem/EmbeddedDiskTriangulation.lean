/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.EmbeddedDisk
import DifferentialGeometry.Topology.PiecewiseLinear.CellMapTriangulation

/-!
# Simplicial realization of a proper PL embedded disk

A proper PL embedded disk in a normal system is realized simplicially by a finite
subdivision of the manifold complex, without moving the disk: the vertex map may be
taken to be the disk's own map, and the interpolated simplicial map agrees with it on
the whole domain.

The auxiliary subdivision cannot be avoided. Asking instead for the images of the
source faces to be faces of `S.manifoldComplex` itself forces the boundary of the disk
into the one-skeleton of that complex, which a properly embedded disk need not satisfy:
for the single tetrahedron with all its faces, the affine disk cut out by
`x + y + z = 1 / 2` is properly embedded and meets the relative interior of a
two-dimensional face, and that complex contains no properly embedded subcomplex disk at
all. The subdivision produced here is adapted to the given disk rather than obtained by
iterated barycentric subdivision, which would keep the vertices rational and so could
not realize such a disk exactly.
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
/-- A proper PL embedded disk is a subcomplex of a finite subdivision of the manifold
complex, with the disk itself left in place: `P` triangulates the disk's domain, `M`
subdivides `S.manifoldComplex`, every face of `P` is carried by `D.map` to a face of
`M`, and the simplicial interpolation of `D.map` over `P` is `D.map` on the domain. -/
theorem EmbeddedDisk.exists_isSubdivision_simplicialMap {S : NormalSystem E}
    (D : EmbeddedDisk S) :
    ∃ (P : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
      (M : Geometry.SimplicialComplex ℝ E),
      P.faces.Finite ∧ M.faces.Finite ∧ P.space = D.domain ∧
      IsSubdivision M S.manifoldComplex ∧
      (∀ s ∈ P.faces, s.image D.map ∈ M.faces) ∧
      EqOn (simplicialMap P D.map) D.map D.domain := by
  obtain ⟨P₀, hP₀fin, hP₀space⟩ := D.isPLBall_domain.isPolyhedron.exists_simplicialComplex
  let _ : Finite P₀.faces := hP₀fin.to_subtype
  let _ : Finite S.manifoldComplex.faces := S.manifoldComplex_faces_finite.to_subtype
  have hpa : IsPiecewiseAffineOn D.map P₀.space := by
    rw [hP₀space]; exact D.isPLHomeomorphOn.isPiecewiseAffineOn
  have hmap : MapsTo D.map P₀.space S.manifoldComplex.space := by
    rw [hP₀space]; exact D.mapsTo
  obtain ⟨P, M, hPfin, hMfin, hPsub, hMsub, hfaces, heq⟩ :=
    hpa.exists_isSubdivision_simplicialMap P₀ S.manifoldComplex hmap
  exact ⟨P, M, hPfin, hMfin, hPsub.space_eq.trans hP₀space, hMsub, hfaces,
    hP₀space ▸ heq⟩

end DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem
