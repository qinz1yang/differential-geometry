import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageGeometryH74
import DifferentialGeometry.Topology.Connected.LocalFacesFiniteComponentsFCP

/-!
# FC39: the finite list of components of `C₁` is a consequence of `JunctionRimFacts74.local_faces`

Lane S-FINCOMP, group G2 (suffix `_FCP`). FDC04's "compact manifold bases have finitely many
components, so all the lists are finite" needs, for the circle base, no separate row: the labelled
local face model `JunctionRimFacts74.local_faces` (gate item (h): at every frontier point of the
compact `C₁` an open `U`, a finite label set `L`, smooth face functions `φ f` with surjective joint
derivative and `C₁ ∩ U = {c' ∈ U | ∀ f ∈ L, φ f c' ≤ 0}`) already forces a finite list.

* `JunctionRimFacts74.circle_cbase_finite_components_FCP`: for every
  `G : JunctionRimFacts74 A D R` the compact circle base `R.circle.cbase = C₁` is the disjoint
  union of finitely many compact connected relatively clopen components (its list).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} {A : SmoothStageGeometry74 W E}
  {D : StageCutChoice74 A} {R : StageCutRows74 A D}

/-- **The finite list of components of `C₁` from the labelled local face model** (see the module
docstring). -/
theorem JunctionRimFacts74.circle_cbase_finite_components_FCP (G : JunctionRimFacts74 A D R) :
    ∃ (m : ℕ) (Bc : Fin m → Set R.circle.Base), (∀ i, IsCompact (Bc i)) ∧
      (∀ i, IsConnected (Bc i)) ∧ (∀ i, Bc i ⊆ R.circle.cbase) ∧
      (∀ i, IsClopen (Subtype.val ⁻¹' Bc i : Set R.circle.cbase)) ∧
      (∀ i, ∀ x ∈ Bc i, connectedComponentIn R.circle.cbase x = Bc i) ∧
      Pairwise (Disjoint on Bc) ∧ R.circle.cbase = ⋃ i, Bc i :=
  finite_components_of_local_faces_FCP R.circle.cbase_compact
    fun c hc => by
      obtain ⟨U, hcU, L, φ, -, -, hφ, hsurj, hcb⟩ := G.local_faces c hc
      exact ⟨U, hcU, L, φ, fun f hf => (hφ f hf).1, hsurj, hcb⟩

end GC.GraphManifold.Assembly.FC39P0
