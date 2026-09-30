/- Ported for the team Lake library; proof bodies and declaration names retained.
Module imports, diagnostic #print commands, and original autoImplicit setting adapted. See docs/geometrization/BASELINE_PROVENANCE.json. -/
/- GC revision197 compatibility port: restore legacy definitional transparency for Lean4.33.1. Original commit c918a72c5170503c98fd66a0f3116b7bfcd1250c; Apache-2.0. -/
import DifferentialGeometry.External.GraphCoveringTheory.KuroshActive

-- Preserve the original standalone port elaboration setting.
set_option autoImplicit true
/-!
# The Kurosh subgroup theorem in Bass--Serre form

The subgroup acts on the Bass--Serre tree of the free product.  The quotient
tree supplies one vertex group for each quotient vertex and a free group for
the quotient graph.  The universal graph-of-groups cover constructed in the
supporting development identifies the resulting free product with the
subgroup itself.
-/

open Set Function
open CategoryTheory
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u v

namespace GraphCoveringTheory.Kurosh

/-- The Bass--Serre graph-of-groups form of Kurosh's theorem. -/
noncomputable def kuroshBassSerreEquiv {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    @TreeKuroshProduct.{u, v, 0} ι G _ H ≃* H :=
  test_treeKuroshProductMulEquivH G H

/-- Every subgroup of a free product is the free product of its Bass--Serre
vertex stabilizers and the free group of the quotient graph. -/
theorem kurosh_bass_serre_decomposition {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    Nonempty (@TreeKuroshProduct.{u, v, 0} ι G _ H ≃* H) :=
  ⟨kuroshBassSerreEquiv G H⟩

/-- Every subgroup of a free product is a free product of the nontrivial
vertex stabilizers in the quotient Bass--Serre graph and the quotient graph's
free group. -/
theorem kurosh_decomposition {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    Nonempty (@KuroshActiveProduct.{u, v, 0} ι G _ H ≃* H) :=
  ⟨kuroshActiveEquivH G H⟩

/-- The vertex groups in the Bass--Serre decomposition are either trivial
central-vertex stabilizers or intersections with conjugates of the original
free factors. -/
theorem kurosh_vertex_stabilizer_classification {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H) :
    (∃ g : FreeProduct G,
      rawTreeRepresentative G H a = RawBassSerreVertex.central g ∧
      treeVertexStabilizer G H a = ⊥) ∨
    (∃ (i : ι) (g : FreeProduct G),
      rawTreeRepresentative G H a =
        RawBassSerreVertex.factor i (factorCosetMk G i g) ∧
      treeVertexStabilizer G H a = intersectionFactorInH H i g) :=
  test_treeVertexStabilizer_central_or_factor G H a

/-- Each nontrivial factor in the factor-only form is an intersection with a
conjugate of one of the original free factors. -/
theorem kurosh_factor_is_conjugate_intersection {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (j : KuroshActiveVertexIndex G H) :
    ∃ (i : ι) (g : FreeProduct G),
      treeVertexStabilizer G H j.1 = intersectionFactorInH H i g :=
  kurosh_active_vertex_intersection G H j

end GraphCoveringTheory.Kurosh
