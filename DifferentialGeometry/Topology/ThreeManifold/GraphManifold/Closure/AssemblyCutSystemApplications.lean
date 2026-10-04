import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCutSystem
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SphereProduct

/-!
# Applications of the B3 producer

Concrete consumers of `Closure/AssemblyCutSystem.lean`.

* `exists_torusPresentation_of_selfSeam_cutData`: the shape L3-T² uses (design §3 L3; draft §(c)): a
  closed carrier cut along one fibre torus into ONE piece with ONE self-seam gives a torus
  presentation with one component, one pairing torus whose two sides lie on that component, no
  external torus, and the given seam collar.
* `RegularCutData.toTorusPresentation_torusMap`: the external tori of the B3 presentation are the
  ports `E` (the BCF04 labels read them off), and every seam of `D` is a seam of the presentation.
* `RegularCutData.cutMap_selfSeam`: for a self-seam the two boundary copies over one torus point
  are different points of the cut space with the same image, as the kernel clause says.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **One piece, one self-seam** (the L3-T² shape): the B3 presentation of a closed cut with one
piece and one self-seam has one component, one pairing torus with both sides on that component, no
external torus, and keeps the seam collar. -/
theorem exists_torusPresentation_of_selfSeam_cutData {W : CompactCarrier.{u}}
    (D : RegularCutData W (BoundaryTori.empty W)) (h1 : D.count = 1) (hs : D.seamCount = 1)
    (hself : ∀ c, D.side c true = D.side c false) :
    ∃ T : TorusPresentation W, T.components.count = 1 ∧ T.pairing.count = 1 ∧
      T.externalCount = 0 ∧ (∀ c, T.leftPiece c = T.rightPiece c) ∧
      ∀ c, ∃ c', T.seam c' = (D.seam c).collar :=
  ⟨D.toTorusPresentation, h1, hs, rfl, hself, fun c => ⟨c, rfl⟩⟩

namespace RegularCutData

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : RegularCutData W E)

/-- The boundary tori of the B3 presentation are the ports `E`. -/
theorem toTorusPresentation_torusMap (i : Fin n) (t : Torus) :
    D.toTorusPresentation.external.torusMap i t = E.torusMap i t :=
  D.toTorusPresentation_external_collar i (zero_mem_halfCollarSource t)

/-- The two boundary copies of a self-seam over one torus point: different points of the cut space
with the same image in `W`. -/
theorem cutMap_selfSeam (c : Fin D.seamCount) (t : Torus) :
    D.portPoint (.inl (c, true)) (t, halfZero) ≠ D.portPoint (.inl (c, false)) (t, halfZero) ∧
      D.cutMap (D.portPoint (.inl (c, true)) (t, halfZero)) =
        D.cutMap (D.portPoint (.inl (c, false)) (t, halfZero)) := by
  refine ⟨fun h => ?_, (cutMap_eq_cutMap_iff (D := D)).mpr (Or.inr ⟨c, t, Or.inl ⟨rfl, rfl⟩⟩)⟩
  have hd := D.portTarget_disjoint (x := .inl (c, true)) (x' := .inl (c, false))
    (fun h' => Bool.noConfusion (congrArg (fun x : D.Port => Sum.elim (fun p => p.2) (fun _ => true) x) h'))
  exact hd.le_bot ⟨⟨_, zero_mem_halfCollarSource t, rfl⟩, ⟨_, zero_mem_halfCollarSource t, h.symm⟩⟩

end RegularCutData

end GC.GraphManifold.Assembly
