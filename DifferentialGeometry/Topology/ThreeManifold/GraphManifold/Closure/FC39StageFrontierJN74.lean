import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageCornerPatchJN74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0CornersV2

/-!
# Draft 74, `local_faces`, step 0: the frontier of `C₁` meets the frontier of `M₃` in a fibre point

Lane S-JUNCTIONS (by S-JUNCTIONS4), G23 part 1 (suffix `_JN74`). On any rows
`R : StageCutRows74 A D` (no chain input):

* `StageCutRows74.fibre_nonempty_JN74`: every circle fibre is non-empty (the trivialization);
* `StageCutRows74.mem_cbase_iff_fibre_subset_JN74`: `c ∈ C₁ ↔ fibre c ⊆ M₃` (the saturation
  `M₃ = proj⁻¹ C₁` of the circle facts);
* `StageCutRows74.exists_frontier_fibre_point_JN74`: for `c ∈ ∂C₁` some point of the circle fibre
  over `c` is not in the interior of `M₃` (closed projection);
* `StageCutRows74.relInt_edgeSet_eq_JN74`: from `edgeSet ∩ M₃ = vertical` and `edgeSet ⊆ M₂`, the
  relative interior of `M^edge` in `M₂` is `M^edge ∖ vertical`.
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
  {D : StageCutChoice74 A}

namespace StageCutRows74

variable (R : StageCutRows74 A D)

/-- Every circle fibre is non-empty. -/
theorem fibre_nonempty_JN74 (c : R.circle.Base) : (R.circle.fibre c).Nonempty := by
  obtain ⟨x, hx⟩ := R.circle.proj_surjective_GGFF c
  exact ⟨x, x, hx, rfl⟩

variable {R} {c : R.circle.Base} in
/-- **`c ∈ C₁` iff the whole fibre lies in `M₃`** (saturation of `M₃`). -/
theorem mem_cbase_iff_fibre_subset_JN74 :
    c ∈ R.circle.cbase ↔ R.circle.fibre c ⊆ D.M₃ := by
  have hreg := D.region_circleBundle74_eq_M₃ R.circleFacts
  constructor
  · rintro hc _ ⟨x, hx, rfl⟩
    rw [← hreg]
    have hx' : R.circle.proj x = c := hx
    exact ⟨x, by change R.circle.proj x ∈ R.circle.cbase; rw [hx']; exact hc, rfl⟩
  · intro h
    obtain ⟨_, x, hx, rfl⟩ := R.fibre_nonempty_JN74 c
    have hm : (x : W.Carrier) ∈ R.circle.region := by
      rw [hreg]
      exact h ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hm
    have : y = x := Subtype.ext hyx
    subst this
    rw [← hx]
    exact hy

/-- **A frontier point of `C₁` has a fibre point outside the interior of `M₃`.** -/
theorem exists_frontier_fibre_point_JN74 {c : R.circle.Base} (hc : c ∈ frontier R.circle.cbase) :
    ∃ x ∈ R.circle.fibre c, x ∉ interior D.M₃ := by
  by_contra hcon0
  have hcon : ∀ x ∈ R.circle.fibre c, x ∈ interior D.M₃ := fun x hx => by
    by_contra h
    exact hcon0 ⟨x, hx, h⟩
  have hcl : IsClosedMap R.circle.proj := isClosedMap_circleBundle74 R.circleFacts
  let Z : Set R.circle.domain := Subtype.val ⁻¹' (interior D.M₃)ᶜ
  have hZ : IsClosed Z := isOpen_interior.isClosed_compl.preimage continuous_subtype_val
  have hU : IsOpen (R.circle.proj '' Z)ᶜ := (hcl _ hZ).isOpen_compl
  have hcU : c ∈ (R.circle.proj '' Z)ᶜ := by
    rintro ⟨x, hx, hxc⟩
    exact hx (hcon x ⟨x, hxc, rfl⟩)
  have hsub : (R.circle.proj '' Z)ᶜ ⊆ R.circle.cbase := by
    intro b hb
    rw [StageCutRows74.mem_cbase_iff_fibre_subset_JN74 (R := R)]
    rintro _ ⟨x, hx, rfl⟩
    by_contra hxM
    apply hb
    refine ⟨x, ?_, hx⟩
    intro hxi
    exact hxM (interior_subset hxi)
  exact hc.2 (mem_interior.2 ⟨_, hsub, hU, hcU⟩)

/-- **The relative interior of `M^edge` in `M₂` is `M^edge ∖ vertical`.** -/
theorem relInt_edgeSet_eq_JN74 (hreg : D.edgeSet ∩ D.M₃ = R.edge.vertical)
    (hsub : D.edgeSet ⊆ D.M₂) :
    relInt D.M₂ D.edgeSet = D.edgeSet \ R.edge.vertical := by
  ext x
  constructor
  · intro hx
    have hxE : x ∈ D.edgeSet := by
      obtain ⟨y, hy, rfl⟩ := hx
      exact interior_subset (s := Subtype.val ⁻¹' D.edgeSet) hy
    refine ⟨hxE, fun hv => ?_⟩
    rw [← hreg] at hv
    exact hv.2.2 hx
  · rintro ⟨hxE, hxv⟩
    by_contra hx
    apply hxv
    rw [← hreg]
    exact ⟨hxE, hsub hxE, hx⟩

end StageCutRows74

end GC.GraphManifold.Assembly.FC39P0
