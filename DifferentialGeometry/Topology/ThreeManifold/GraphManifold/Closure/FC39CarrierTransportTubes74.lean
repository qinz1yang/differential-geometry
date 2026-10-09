import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransportJunctions74

/-!
# Draft 74, D74-6: transport of the labelled corner tubes along ONE carrier diffeomorphism

Lane C14-REG-CHAIN (by S-REG-CHAIN), G23 (tube package of `FC39RowsV2.transport74`). For the
junctions `J.mapCarrier74 e hk` of the transported rows:

* **`LabelledCornerTubes.mapCarrier74 e hk T`**: the same base neighbourhoods `V_e`, the same
  charts `κ_e` of the circle base (the base is unchanged), the same descended equations `b_e`;
  the tubes are the `e`-images (`CircleBundle.mapCarrier74_tube`), the equations
  `κ_e¹ ∘ proj = T − 4Δ` and `κ_e² ∘ proj = h_{horizontal e}` hold on the WHOLE transported tube
  (the projection and the height are read through `e⁻¹`, the defining function of the face is
  `h ∘ e⁻¹`), the three labelled side equalities are the `e`-images of the original ones.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

attribute [local instance] diskChartsBase_FC39P0

variable {W₀ W₁ : CompactCarrier.{u}} {n : ℕ}

/-- **The labelled corner tubes transported along `e`** (carriers of the same kind; D74-6,
tube package). -/
def LabelledCornerTubes.mapCarrier74 (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    (hk : W₀.kind = W₁.kind) {E : BoundaryTori W₀ n} {Z : ZeroDomains W₀} {C : CuspCores W₀ E}
    {S : SlimPiecesV2 W₀ Z C} {P : EdgeBundle W₀} {R : CircleBundle W₀}
    {J : JunctionsV2 W₀ E Z C S P R} (T : LabelledCornerTubes J) :
    LabelledCornerTubes (J.mapCarrier74 e hk) where
  base x := T.base x
  rimBase_mem x := T.rimBase_mem x
  chart x := T.chart x
  chart_source x := T.chart_source x
  chart_center x := T.chart_center x
  tube_source x :=
    (subset_of_eq (CircleBundle.mapCarrier74_tube e R _)).trans (image_mono (T.tube_source x))
  tube_near x :=
    (subset_of_eq (CircleBundle.mapCarrier74_tube e R _)).trans
      ((image_mono (T.tube_near x)).trans
        (subset_of_eq (residualNear_mapCarrier74 e S (J.horizontal x)).symm))
  height_eq x z hz := by
    obtain ⟨hx, h⟩ := T.height_eq x (e.restrictOpens74 R.domain z) hz
    exact ⟨⟨e.symm z.1, hx, e.apply_symm_apply _⟩, h⟩
  face_eq x z hz :=
    (T.face_eq x (e.restrictOpens74 R.domain z) hz).trans
      (congrFun (residualFn_mapCarrier74 e S (J.horizontal x)).symm z.1)
  descended x := T.descended x
  descended_smooth x := T.descended_smooth x
  descended_regular x := T.descended_regular x
  descended_eq x z hz := by
    obtain ⟨hx, h⟩ := T.descended_eq x (e.restrictOpens74 R.domain z) hz
    exact ⟨⟨e.symm z.1, hx, e.apply_symm_apply _⟩,
      (congrFun (residualFn_mapCarrier74 e S (J.horizontal x)) z.1).trans h⟩
  vertex_side {x} {z} hz := by
    refine Iff.trans ?_ (T.vertex_side (e := x) (x := e.restrictOpens74 R.domain z) hz)
    change (z : W₁.Carrier) ∈ (S.mapCarrier74 e).rowSet ((S.mapCarrier74 e).residualOwner
      (S.resToMap74 e (J.horizontal x))) ↔ _
    rw [residualOwner_mapCarrier74, rowSet_mapCarrier74, mem_image_iff_symm_R74]
    exact Iff.rfl
  edge_side {x} {z} hz := by
    refine Iff.trans ?_ (T.edge_side (e := x) (x := e.restrictOpens74 R.domain z) hz)
    exact (Iff.of_eq (congrArg (fun s => (z : W₁.Carrier) ∈ s)
      (EdgeBundle.mapCarrier74_wholeComponent e hk P (show P.EdgeEnd from x).component))).trans
      mem_image_iff_symm_R74
  region_side {x} {z} hz := by
    refine Iff.trans ?_ (T.region_side (e := x) (x := e.restrictOpens74 R.domain z) hz)
    rw [CircleBundle.mapCarrier74_region, mem_image_iff_symm_R74]
    exact Iff.rfl

end GC.GraphManifold.Assembly.FC39P0
