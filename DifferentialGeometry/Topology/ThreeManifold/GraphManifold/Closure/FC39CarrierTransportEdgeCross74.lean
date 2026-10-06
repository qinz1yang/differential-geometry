import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransportFaces74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierCrossKind74

/-!
# Draft 74, D74-6: the edge disk bundle transported between carriers of ANY kinds

Lane O-CROSS, G3 (REG-CHAIN G25: remove `hk : W₀.kind = W₁.kind`). Same construction as
`EdgeBundle.mapCarrier74` (lane C14-REG-CHAIN, G19) and the edge part of the face bridge
(`FC39CarrierTransportFaces74`, G23), with the whole-disk fibres carried by the cross-kind lemma
`isSmoothEmbedding_comp_carrier_cross_disk_R74` (O-CROSS G1):

* **`EdgeBundle.mapCarrierCross74 e P`**, `EdgeBundle.mapCarrierCross74_edgePiece`, `…_height`;
* `regionM3_mapCarrierCross74`, `EdgeBundle.mapCarrierCross74_{disk, rim, vertical,
  wholeComponent, wholeVertical, horizontalDisks}`, `labelEquivCross74`,
  `circleFaceSet_mapCarrierCross74`, `allPieces_mapCarrierCross74`.
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

/-- **The edge disk bundle transported along `e`** (carriers of ANY kinds; D74-6, bundle
package): source `e(P.source)`, projection `P.proj ∘ e⁻¹`, height `P.height ∘ e⁻¹`, the same base,
level and compact base. -/
def EdgeBundle.mapCarrierCross74 (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    (P : EdgeBundle W₀) : EdgeBundle W₁ where
  Base := P.Base
  source := e.imageOpens74 P.source
  source_interior := by
    rw [← image_interior_carrier_R74 e]
    exact image_mono P.source_interior
  proj := P.proj.comp ⟨e.restrictOpens74 P.source, (e.restrictOpens74 P.source).continuous⟩
  proj_smooth := P.proj_smooth.comp (e.restrictOpens74 P.source).contMDiff
  proj_submersion x := by
    have hp : MDifferentiableAt W₀.model (𝓡 1) P.proj (e.restrictOpens74 P.source x) :=
      (P.proj_smooth _).mdifferentiableAt (by simp)
    have hr : MDifferentiableAt W₁.model W₀.model (e.restrictOpens74 P.source) x :=
      (e.restrictOpens74 P.source).mdifferentiable (by simp) x
    change Surjective (mfderiv W₁.model (𝓡 1) (P.proj ∘ e.restrictOpens74 P.source) x)
    rw [mfderiv_comp x hp hr]
    exact (P.proj_submersion _).comp (mfderiv_diffeo_bijective_R74 _ x).2
  height := P.height ∘ e.restrictOpens74 P.source
  height_smooth := P.height_smooth.comp (e.restrictOpens74 P.source).contMDiff
  level := P.level
  rank_two x hx := by
    have hp : MDifferentiableAt W₀.model (𝓡 1) P.proj (e.restrictOpens74 P.source x) :=
      (P.proj_smooth _).mdifferentiableAt (by simp)
    have hh : MDifferentiableAt W₀.model 𝓘(ℝ, ℝ) P.height (e.restrictOpens74 P.source x) :=
      (P.height_smooth _).mdifferentiableAt (by simp)
    have hr : MDifferentiableAt W₁.model W₀.model (e.restrictOpens74 P.source) x :=
      (e.restrictOpens74 P.source).mdifferentiable (by simp) x
    have e1 := mfderiv_comp x hp hr
    have e2 := mfderiv_comp x hh hr
    intro ab
    obtain ⟨w, hw⟩ := P.rank_two (e.restrictOpens74 P.source x) hx ab
    obtain ⟨v, rfl⟩ := (mfderiv_diffeo_bijective_R74 (e.restrictOpens74 P.source) x).2 w
    refine ⟨v, ?_⟩
    change (mfderiv W₁.model (𝓡 1) (P.proj ∘ e.restrictOpens74 P.source) x v,
      mfderiv W₁.model 𝓘(ℝ, ℝ) (P.height ∘ e.restrictOpens74 P.source) x v) = ab
    rw [e1, e2]
    exact hw
  proper K hK := by
    have h := e.image_restrictOpens74 P.source (fun y => P.proj y ∈ K ∧ P.height y ≤ P.level)
    change IsCompact (Subtype.val '' {x : e.imageOpens74 P.source |
      P.proj (e.restrictOpens74 P.source x) ∈ K ∧
        P.height (e.restrictOpens74 P.source x) ≤ P.level})
    rw [h]
    exact (P.proper K hK).image e.continuous
  fibre_disk c := by
    obtain ⟨φ, hφ, hr⟩ := P.fibre_disk c
    refine ⟨e ∘ φ, isSmoothEmbedding_comp_carrier_cross_disk_R74 e hφ, ?_⟩
    have h := e.image_restrictOpens74 P.source (fun y => P.proj y = c ∧ P.height y ≤ P.level)
    change range (e ∘ φ) = Subtype.val '' {x : e.imageOpens74 P.source |
      P.proj (e.restrictOpens74 P.source x) = c ∧
        P.height (e.restrictOpens74 P.source x) ≤ P.level}
    rw [h, range_comp, hr]
  cbase := P.cbase
  cbase_compact := P.cbase_compact
  cbase_domain := P.cbase_domain

/-- The transported actual edge piece `M^edge` is the image of the edge piece. -/
theorem EdgeBundle.mapCarrierCross74_edgePiece (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    (P : EdgeBundle W₀) :
    (P.mapCarrierCross74 e).edgePiece = e '' P.edgePiece :=
  e.image_restrictOpens74 P.source (fun y => P.proj y ∈ P.cbase ∧ P.height y ≤ P.level)

/-- The transported height and projection are the pulled-back ones. -/
theorem EdgeBundle.mapCarrierCross74_height (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    (P : EdgeBundle W₀) (x : (P.mapCarrierCross74 e).source) :
    (P.mapCarrierCross74 e).height x = P.height (e.restrictOpens74 P.source x) ∧
      (P.mapCarrierCross74 e).proj x = P.proj (e.restrictOpens74 P.source x) :=
  ⟨rfl, rfl⟩

section Faces

variable (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)

section Regions

variable {E : BoundaryTori W₀ n} {Z : ZeroDomains W₀} {C : CuspCores W₀ E}

/-- `M₃` of the transported rows is the image of `M₃`. -/
theorem regionM3_mapCarrierCross74 (S : SlimPiecesV2 W₀ Z C)
    (P : EdgeBundle W₀) :
    regionM3 (S.mapCarrier74 e) (P.mapCarrierCross74 e) = e '' regionM3 S P := by
  unfold regionM3
  rw [regionM2_mapCarrier74, EdgeBundle.mapCarrierCross74_edgePiece, relInt_image_R74,
    image_sdiff (carrier_injective_R74 e)]

end Regions

/-- The whole disk over `c` is transported. -/
theorem EdgeBundle.mapCarrierCross74_disk (P : EdgeBundle W₀) (c : P.Base) :
    (P.mapCarrierCross74 e).disk c = e '' P.disk c :=
  e.image_restrictOpens74 P.source (fun y => P.proj y = c ∧ P.height y ≤ P.level)

/-- The boundary circle of the disk over `c` is transported. -/
theorem EdgeBundle.mapCarrierCross74_rim (P : EdgeBundle W₀) (c : P.Base) :
    (P.mapCarrierCross74 e).rim c = e '' P.rim c :=
  e.image_restrictOpens74 P.source (fun y => P.proj y = c ∧ P.height y = P.level)

/-- The vertical face is transported. -/
theorem EdgeBundle.mapCarrierCross74_vertical (P : EdgeBundle W₀) :
    (P.mapCarrierCross74 e).vertical = e '' P.vertical :=
  e.image_restrictOpens74 P.source (fun y => P.proj y ∈ P.cbase ∧ P.height y = P.level)

/-- The whole inverse image of a base component below the level is transported. -/
theorem EdgeBundle.mapCarrierCross74_wholeComponent (P : EdgeBundle W₀)
    (C : P.EdgeBaseComponent) :
    (P.mapCarrierCross74 e).wholeComponent C = e '' P.wholeComponent C :=
  e.image_restrictOpens74 P.source (fun y => P.proj y ∈ C.1 ∧ P.height y ≤ P.level)

/-- The vertical face of a base component is transported. -/
theorem EdgeBundle.mapCarrierCross74_wholeVertical (P : EdgeBundle W₀)
    (C : P.EdgeBaseComponent) :
    (P.mapCarrierCross74 e).wholeVertical C = e '' P.wholeVertical C :=
  e.image_restrictOpens74 P.source (fun y => P.proj y ∈ C.1 ∧ P.height y = P.level)

/-- The union of the horizontal disks is transported. -/
theorem EdgeBundle.mapCarrierCross74_horizontalDisks (P : EdgeBundle W₀) :
    (P.mapCarrierCross74 e).horizontalDisks = e '' P.horizontalDisks := by
  rw [EdgeBundle.horizontalDisks, EdgeBundle.horizontalDisks, image_iUnion]
  exact iUnion_congr fun x => EdgeBundle.mapCarrierCross74_disk e P x.1

/-- **The labels of the circle-base faces are unchanged by the transport** (an equivalence). -/
def labelEquivCross74 {E : BoundaryTori W₀ n} {Z : ZeroDomains W₀}
    {C : CuspCores W₀ E} (S : SlimPiecesV2 W₀ Z C) (P : EdgeBundle W₀) :
    CircleFaceLabel S.ResidualFace P.EdgeBaseComponent ≃
      CircleFaceLabel (S.mapCarrier74 e).ResidualFace
        (P.mapCarrierCross74 e).EdgeBaseComponent where
  toFun := fun
    | .horizontal F => .horizontal (S.resToMap74 e F)
    | .vertical c => .vertical c
  invFun := fun
    | .horizontal F => .horizontal (S.resOfMap74 e F)
    | .vertical c => .vertical c
  left_inv f := by
    cases f with
    | horizontal F => exact congrArg CircleFaceLabel.horizontal ((S.residualEquiv74 e).left_inv F)
    | vertical c => rfl
  right_inv f := by
    cases f with
    | horizontal F => exact congrArg CircleFaceLabel.horizontal ((S.residualEquiv74 e).right_inv F)
    | vertical c => rfl

/-- The ambient set of a transported circle-base face is the image. -/
theorem circleFaceSet_mapCarrierCross74 {E : BoundaryTori W₀ n}
    {Z : ZeroDomains W₀} {C : CuspCores W₀ E} (S : SlimPiecesV2 W₀ Z C) (P : EdgeBundle W₀)
    (f : CircleFaceLabel S.ResidualFace P.EdgeBaseComponent) :
    circleFaceSet (S.mapCarrier74 e) (P.mapCarrierCross74 e) (labelEquivCross74 e S P f) =
      e '' circleFaceSet S P f := by
  cases f with
  | horizontal F => exact residualSet_mapCarrier74 e S F
  | vertical c => exact EdgeBundle.mapCarrierCross74_wholeVertical e P c

/-- **All pieces of the transported decomposition are the images of the original pieces.** -/
theorem allPieces_mapCarrierCross74 {E : BoundaryTori W₀ n}
    {Z : ZeroDomains W₀} {C : CuspCores W₀ E} (S : SlimPiecesV2 W₀ Z C) (P : EdgeBundle W₀)
    (R : CircleBundle W₀) (a : S.RowIndex ⊕ Bool) :
    allPieces (S.mapCarrier74 e) (P.mapCarrierCross74 e) (R.mapCarrier74 e) a =
      e '' allPieces S P R a := by
  rcases a with i | b
  · exact rowSet_mapCarrier74 e S i
  · cases b
    · exact R.mapCarrier74_region e
    · exact EdgeBundle.mapCarrierCross74_edgePiece e P

end Faces

end GC.GraphManifold.Assembly.FC39P0
