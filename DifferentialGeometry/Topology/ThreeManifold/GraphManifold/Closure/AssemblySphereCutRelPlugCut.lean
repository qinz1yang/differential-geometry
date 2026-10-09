import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelFold
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugCapShell
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapCapping
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyPieces

/-!
# Chapter-14 assembly, relative COMPARE G4 (first part): the concrete cut of a bounded sphere

Lane ASM-L2e, group G4. The fibre plug carries its OWN sphere cut and capping (the bounded cut
`boundedPlugCutCarrier`, its mixed boundary `boundedPlugCutBoundary` and the canonical capping
`sphereCapRelativeCapping`), on which all the plug side data of the tree (cap ball charts, solid
models, cut factors) are stated. Here this concrete cut is packaged as a `SphereCutCapped`
(`boundedSphereCutCapped`; the fields are those of `exists_sphereCutCarrier`, which produces the
same objects), so that the fold off the caps of G1 applies to the plug.

* `boundedSphereCutCapped`: the concrete `SphereCutCapped` of a bounded interior sphere collar.
* `exists_pieceFold_of_carrier`: a connected carrier with boundary and a smooth map into `W` with
  bijective differentials is a `PieceFold` of `W` (up to the identity diffeomorphism).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

section Bounded

variable {W : CompactCarrier.{u}}
  (d : PartialDiffeomorph sphereSignedCollarModel W.model (ClosureSphere.{u} × ℝ) W.Carrier ∞)
  (hs : d.source = sphereSignedCollarSource) (hI : d.target ⊆ W.interior)
  {n : ℕ} (A : BoundaryTori W n) (hA : W.model.boundary W.Carrier = A.image)
  (hav : ∀ i, Disjoint (A.collar i).target d.target)

/-- The sphere seam of a bounded interior sphere collar. -/
def boundedSphereSeam : SphereSeam W := ⟨d, hs, hI⟩

/-- **The concrete cut and capping of a bounded interior sphere collar**, as a `SphereCutCapped`. -/
def boundedSphereCutCapped : SphereCutCapped W (boundedSphereSeam d hs hI) A where
  C := boundedPlugCutCarrier d hs
  B := boundedPlugCutBoundary d hs hI A hA hav
  hn := rfl
  h2 := rfl
  fold := sphereCutFold (boundedPlugCutCollars d)
  kind := rfl
  smooth := sphereCutFold_smooth (boundedPlugCutCollars d) (boundedPlugCutCollars_source d hs)
    (boundedPlugCutCollars_disjoint d)
  surjective := sphereCut_projection_surjective (boundedPlugCutCollars d)
  oriented x := by
    let := sphereCutChartedSpace (boundedPlugCutCollars d) (boundedPlugCutCollars_source d hs)
      (boundedPlugCutCollars_disjoint d)
    let L := Manifold.differentialEquivOfBijective (𝓡∂ 3) W.model
      (sphereCutFold (boundedPlugCutCollars d))
      (sphereCutFold_mfderiv_bijective (boundedPlugCutCollars d)
        (boundedPlugCutCollars_source d hs) (boundedPlugCutCollars_disjoint d)) x
    exact ⟨L.toLinearEquiv, fun v => rfl, sphereCutFold_orientation_map (boundedPlugCutCollars d)
      (boundedPlugCutCollars_source d hs) (boundedPlugCutCollars_disjoint d) x⟩
  tori i p hp := sphereCutRetainedCollar_fold (boundedPlugCutCollars d)
    (boundedPlugCutCollars_source d hs) (boundedPlugCutCollars_disjoint d) A
    (fun r _ => hav r) i p hp
  spheres i z s hs0 hs1 := by
    have hp : (z, halfPoint s hs0) ∈ sphereHalfCollarSource := hs1
    have hf := sphereCutFullCollar_fold (boundedPlugCutCollars d)
      (boundedPlugCutCollars_source d hs) (boundedPlugCutCollars_disjoint d) 0
      (sphereCutBoundarySide i) _ hp
    change sphereCutFold (boundedPlugCutCollars d) (sphereCutFullCollar (boundedPlugCutCollars d)
      (boundedPlugCutCollars_source d hs) (boundedPlugCutCollars_disjoint d) 0
      (sphereCutBoundarySide i) (z, halfPoint s hs0)) = d (z, if i.val = 0 then s else -s)
    rw [hf]
    fin_cases i <;> rfl
  fold_eq {x y} hxy := by
    have hz : ∀ (b : Bool) (z : ClosureSphere.{u}),
        sphereCutZero (boundedPlugCutCollars d) 0 b z =
          sphereCutFullCollar (boundedPlugCutCollars d) (boundedPlugCutCollars_source d hs)
            (boundedPlugCutCollars_disjoint d) 0 b (z, halfZero) := fun b z =>
      (sphereCutFullCollar_zero (boundedPlugCutCollars d) (boundedPlugCutCollars_source d hs)
        (boundedPlugCutCollars_disjoint d) 0 b z).symm
    rcases (sphereCutFold_fibre_relation (boundedPlugCutCollars d)
      (boundedPlugCutCollars_source d hs) (boundedPlugCutCollars_disjoint d) x y).mp hxy with
      h | ⟨z, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨z, Or.inl ⟨h1.trans (hz false z), h2.trans (hz true z)⟩⟩
    · exact Or.inr ⟨z, Or.inr ⟨h1.trans (hz true z), h2.trans (hz false z)⟩⟩
  Q := (boundedPlugCutBoundary d hs hI A hA hav).sphereCapCarrier
  capping := (boundedPlugCutBoundary d hs hI A hA hav).sphereCapRelativeCapping

theorem boundedSphereCutCapped_fold (x : (boundedSphereCutCapped d hs hI A hA hav).C.Carrier) :
    (boundedSphereCutCapped d hs hI A hA hav).fold x =
      sphereCutFold (boundedPlugCutCollars d) x := rfl

end Bounded

/-- **A carrier as a piece.** A connected carrier with boundary and a smooth map into `W` with
bijective differentials is a `PieceFold` of `W`, through a diffeomorphism. -/
theorem exists_pieceFold_of_carrier {W : CompactCarrier.{u}} (C : CompactCarrier.{u})
    (hk : C.kind = .withBoundary) [ConnectedSpace C.Carrier] (f : C.Carrier → W.Carrier)
    (hf : ContMDiff C.model W.model ∞ f) (hb : ∀ x, Bijective (mfderiv C.model W.model f x)) :
    ∃ (P : PieceFold W) (e : C.Carrier ≃ₘ⟮C.model, 𝓡∂ 3⟯ P.Piece), ∀ x, P.map (e x) = f x := by
  cases C with
  | mk kind Car =>
    change kind = .withBoundary at hk
    subst hk
    exact ⟨{ Piece := Car, map := f, smooth := hf, mfderiv_bijective := hb },
      Diffeomorph.refl (𝓡∂ 3) Car ∞, fun x => rfl⟩

end GC.GraphManifold.Assembly
