import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialTorusCores
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Adapters

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.GraphManifold.Assembly.FC39P0
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

local instance sphereSecondCountable_EdgeX135 : SecondCountableTopology SphereCarrier.{0} :=
  secondCountableTopology_sphereCarrier

local instance carrierCharts_EdgeX135 :
    ChartedSpace (EuclideanHalfSpace 3) carrier.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_EdgeX135 : IsManifold (𝓡∂ 3) ∞ carrier.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

def edgeCoreDefiner (p : SphereCarrier.{0}) : ℝ := cliffordHeight p - (-(3 / 4 : ℝ))

theorem edgeCoreDefiner_smooth : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ edgeCoreDefiner :=
  contMDiff_cliffordHeight.sub contMDiff_const

theorem edgeCoreDefiner_regular (p : SphereCarrier.{0}) (hp : edgeCoreDefiner p = 0) :
    mfderiv (𝓡 3) 𝓘(ℝ, ℝ) edgeCoreDefiner p ≠ 0 := by
  have he : cliffordHeight p = -(3 / 4 : ℝ) := sub_eq_zero.mp hp
  have hreg := radial_mvfderiv_regular p ⟨by rw [he]; norm_num, by rw [he]; norm_num⟩
  intro hzero
  have hz : mvfderiv (𝓡 3) edgeCoreDefiner p = 0 := by
    simp only [mvfderiv, hzero, ContinuousLinearMap.comp_zero]
  change mvfderiv (𝓡 3) (fun p => cliffordHeight p - (-(3 / 4 : ℝ))) p = 0 at hz
  rw [mvfderiv_fun_sub (g := cliffordHeight) (g' := fun _ => -(3 / 4 : ℝ))
    (contMDiff_cliffordHeight.mdifferentiableAt (by simp)) mdifferentiableAt_const,
    mvfderiv_const, sub_zero] at hz
  exact hreg hz

def radialEdgeSet : Set SphereCarrier.{0} := {p | edgeCoreDefiner p ≤ 0}

def radialEdgeAtlas : SmoothBoundaryAtlas (𝓡 3) 3 radialEdgeSet :=
  SmoothBoundaryAtlas.regularSublevel (𝓡 3) (n := 2) finrank_euclideanSpace_fin
    edgeCoreDefiner_smooth 0 edgeCoreDefiner_regular

instance radialEdgeCharts : ChartedSpace (EuclideanHalfSpace 3) radialEdgeSet :=
  radialEdgeAtlas.toChartedSpace

instance radialEdgeSmooth : IsManifold (𝓡∂ 3) ∞ radialEdgeSet := radialEdgeAtlas.isManifold

instance radialEdgeCompact : CompactSpace radialEdgeSet :=
  isCompact_iff_compactSpace.mp
    (isClosed_le edgeCoreDefiner_smooth.continuous continuous_const).isCompact

instance radialEdgeSecondCountable : SecondCountableTopology radialEdgeSet := inferInstance

def edgeToCarrier (p : radialEdgeSet) : carrier.Carrier :=
  ⟨p.val, by
    have hh : cliffordHeight p.val ≤ -(3 / 4 : ℝ) := sub_nonpos.mp p.property
    exact hh.trans (by norm_num)⟩

theorem edgeToCarrier_smooth : ContMDiff (𝓡∂ 3) carrier.model ∞ edgeToCarrier :=
  (solidTorusAtlas.contMDiff_iff_subtype_val edgeToCarrier).mpr
    radialEdgeAtlas.contMDiff_subtype_val

theorem edgeToCarrier_injective : Injective edgeToCarrier := by
  intro p q h
  exact Subtype.ext (congrArg (Subtype.val : carrier.Carrier → SphereCarrier.{0}) h)

theorem edgeToCarrier_range : range edgeToCarrier = {p | height p ≤ -(3 / 4 : ℝ)} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact sub_nonpos.mp
      (show cliffordHeight q.val - (-(3 / 4 : ℝ)) ≤ 0 from q.property)
  · intro hp
    refine ⟨⟨p.val, ?_⟩, Subtype.ext rfl⟩
    change cliffordHeight p.val - (-(3 / 4 : ℝ)) ≤ 0
    exact sub_nonpos.mpr hp

theorem edgeToCarrier_mfderiv (p : radialEdgeSet) :
    Bijective (mfderiv (𝓡∂ 3) (𝓡∂ 3) edgeToCarrier p) := by
  have hw : Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
      (Subtype.val : carrier.Carrier → SphereCarrier.{0}) (edgeToCarrier p)) :=
    solidTorusAtlas.mfderiv_subtypeVal_bijective (edgeToCarrier p)
  have hc : Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
      ((Subtype.val : carrier.Carrier → SphereCarrier.{0}) ∘ edgeToCarrier) p) :=
    radialEdgeAtlas.mfderiv_subtypeVal_bijective p
  have hchain := mfderiv_comp p (contMDiff_solidTorus_val.mdifferentiableAt (by simp))
    (edgeToCarrier_smooth.mdifferentiableAt (by simp))
  have hcomp := hchain ▸ hc
  exact Function.Bijective.of_comp_left
    (f := mfderiv (𝓡∂ 3) (𝓡 3)
      (Subtype.val : carrier.Carrier → SphereCarrier.{0}) (edgeToCarrier p))
    (g := mfderiv (𝓡∂ 3) (𝓡∂ 3) edgeToCarrier p) hcomp hw.1

def edgeDiscHalf (w : UnitDisc.{0}) : UnitDisc.{0} :=
  ULift.up ⟨(1 / 2 : ℝ) • w.down.val, by
    change ‖(1 / 2 : ℝ) • w.down.val‖ ^ 2 ≤ 1
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hw : ‖w.down.val‖ ^ 2 ≤ 1 := w.down.property
    nlinarith [hw]⟩

theorem edgeDiscHalf_smooth : ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ edgeDiscHalf := by
  have hd : ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞
      (fun w : UnitDisc.{0} => (edgeDiscHalf w).down) :=
    (unitDiscAtlas.contMDiff_iff_subtype_val _).mpr
      ((contDiff_const_smul (1 / 2 : ℝ)).contMDiff.comp contMDiff_disc_val)
  exact (uliftDiffeomorph (𝓡∂ 2) unitDiscSet).contMDiff.comp hd

def edgeHalfCarrier (q : UnitDisc.{0} × Circle) : carrier.Carrier :=
  solidTorusOfDiscCircle (edgeDiscHalf q.1, q.2)

theorem edgeHalfCarrier_height (q : UnitDisc.{0} × Circle) :
    height (edgeHalfCarrier q) = ‖q.1.down.val‖ ^ 2 / 4 - 1 := by
  have hn := norm_sphereFirst_sq_eq (edgeHalfCarrier q).val
  change ‖((√2 : ℝ)⁻¹) • ((1 / 2 : ℝ) • q.1.down.val)‖ ^ 2 =
    (1 + height (edgeHalfCarrier q)) / 2 at hn
  rw [norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs,
    Real.norm_eq_abs, sq_abs, sq_abs, inv_pow, sqrt_two_sq] at hn
  nlinarith [hn]

def edgeProductMap (q : UnitDisc.{0} × Circle) : radialEdgeSet :=
  ⟨(edgeHalfCarrier q).val, by
    change height (edgeHalfCarrier q) - (-(3 / 4 : ℝ)) ≤ 0
    rw [edgeHalfCarrier_height]
    have hw : ‖q.1.down.val‖ ^ 2 ≤ 1 := q.1.down.property
    nlinarith [hw]⟩

def edgeAsSolidTorus (p : radialEdgeSet) : solidTorusSet.{0} :=
  ⟨p.val, by
    have hh : cliffordHeight p.val ≤ -(3 / 4 : ℝ) :=
      sub_nonpos.mp (show cliffordHeight p.val - (-(3 / 4 : ℝ)) ≤ 0 from p.property)
    exact hh.trans (by norm_num)⟩

def edgeDiscDouble (p : radialEdgeSet) : UnitDisc.{0} :=
  ULift.up ⟨(2 : ℝ) • (discOfSolidTorus (edgeAsSolidTorus p)).down.val, by
    change ‖(2 : ℝ) • (discOfSolidTorus (edgeAsSolidTorus p)).down.val‖ ^ 2 ≤ 1
    change ‖(2 : ℝ) • ((√2 : ℝ) • sphereFirst p.val)‖ ^ 2 ≤ 1
    rw [norm_smul, norm_smul, mul_pow, mul_pow,
      Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, sqrt_two_sq]
    have hn := norm_sphereFirst_sq_eq p.val
    have hh : cliffordHeight p.val ≤ -(3 / 4 : ℝ) :=
      sub_nonpos.mp (show cliffordHeight p.val - (-(3 / 4 : ℝ)) ≤ 0 from p.property)
    change 2 ^ 2 * (2 * ‖sphereFirst p.val‖ ^ 2) ≤ 1
    nlinarith [hn, hh]⟩

def edgeProductInverse (p : radialEdgeSet) : UnitDisc.{0} × Circle :=
  (edgeDiscDouble p, (solidTorusDiscCircle (edgeAsSolidTorus p)).2)

theorem edgeProduct_left (q : UnitDisc.{0} × Circle) :
    edgeProductInverse (edgeProductMap q) = q := by
  have hd := solidTorusDiscCircle.right_inv (edgeDiscHalf q.1, q.2)
  have hphase := congrArg (fun z : UnitDisc.{0} × Circle => z.2) hd
  apply Prod.ext
  · have hdisc : discOfSolidTorus (edgeAsSolidTorus (edgeProductMap q)) =
        edgeDiscHalf q.1 := congrArg Prod.fst hd
    apply ULift.ext
    apply Subtype.ext
    change (2 : ℝ) • (discOfSolidTorus (edgeAsSolidTorus (edgeProductMap q))).down.val =
      q.1.down.val
    rw [hdisc]
    change (2 : ℝ) • ((1 / 2 : ℝ) • q.1.down.val) = q.1.down.val
    rw [smul_smul]
    norm_num
  · change (solidTorusDiscCircle
      (solidTorusOfDiscCircle (edgeDiscHalf q.1, q.2))).2 = q.2
    exact hphase

theorem edgeProduct_right (p : radialEdgeSet) :
    edgeProductMap (edgeProductInverse p) = p := by
  have hdisc : edgeDiscHalf (edgeDiscDouble p) = discOfSolidTorus (edgeAsSolidTorus p) := by
    apply ULift.ext
    apply Subtype.ext
    change (1 / 2 : ℝ) • ((2 : ℝ) • (discOfSolidTorus (edgeAsSolidTorus p)).down.val) = _
    rw [smul_smul]
    norm_num
  apply Subtype.ext
  change (solidTorusOfDiscCircle
    (edgeDiscHalf (edgeDiscDouble p), (solidTorusDiscCircle (edgeAsSolidTorus p)).2)).val = p.val
  rw [hdisc]
  exact congrArg (Subtype.val : solidTorusSet.{0} → SphereCarrier.{0})
    (solidTorusDiscCircle.left_inv (edgeAsSolidTorus p))

theorem edgeProductMap_smooth :
    ContMDiff ((𝓡∂ 2).prod (𝓡 1)) (𝓡∂ 3) ∞ edgeProductMap := by
  apply (radialEdgeAtlas.contMDiff_iff_subtype_val edgeProductMap).mpr
  have hg : ContMDiff ((𝓡∂ 2).prod (𝓡 1)) (𝓡∂ 3) ∞
      (fun q : UnitDisc.{0} × Circle => solidTorusOfDiscCircle (edgeDiscHalf q.1, q.2)) :=
    contMDiff_solidTorusOfDiscCircle.comp
      ((edgeDiscHalf_smooth.comp contMDiff_fst).prodMk contMDiff_snd)
  exact contMDiff_solidTorus_val.comp hg

theorem edgeAsSolidTorus_smooth :
    ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ edgeAsSolidTorus :=
  (solidTorusAtlas.contMDiff_iff_subtype_val edgeAsSolidTorus).mpr
    radialEdgeAtlas.contMDiff_subtype_val

theorem edgeProductInverse_smooth :
    ContMDiff (𝓡∂ 3) ((𝓡∂ 2).prod (𝓡 1)) ∞ edgeProductInverse := by
  have hd : ContMDiff (𝓡∂ 3) (𝓡∂ 2) ∞
      (fun p : radialEdgeSet => (edgeDiscDouble p).down) :=
    (unitDiscAtlas.contMDiff_iff_subtype_val _).mpr
      ((contDiff_const_smul (2 : ℝ)).contMDiff.comp
        (contMDiff_disc_val.comp (contMDiff_discOfSolidTorus.comp edgeAsSolidTorus_smooth)))
  have hdouble : ContMDiff (𝓡∂ 3) (𝓡∂ 2) ∞ edgeDiscDouble :=
    (uliftDiffeomorph (𝓡∂ 2) unitDiscSet).contMDiff.comp hd
  exact hdouble.prodMk ((solidTorusDiscCircle.contMDiff.comp edgeAsSolidTorus_smooth).snd)

def edgeProduct :
    (UnitDisc.{0} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), 𝓡∂ 3⟯ radialEdgeSet where
  toFun := edgeProductMap
  invFun := edgeProductInverse
  left_inv := edgeProduct_left
  right_inv := edgeProduct_right
  contMDiff_toFun := edgeProductMap_smooth
  contMDiff_invFun := edgeProductInverse_smooth

local instance edgeDiscConnected_X135 : ConnectedSpace UnitDisc.{0} :=
  unitDiscSurface.connected

instance radialEdgeConnected : ConnectedSpace radialEdgeSet :=
  edgeProduct.toHomeomorph.connectedSpace_iff.mp inferInstance

def radialEdgePiece : Assembly.PieceEmbedding carrier where
  Piece := radialEdgeSet
  map := edgeToCarrier
  smooth := edgeToCarrier_smooth
  mfderiv_bijective := edgeToCarrier_mfderiv
  injective := edgeToCarrier_injective

local instance edgeCellCharts_X135 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  Handle.closedCellChartedSpaceSucc 1

local instance edgeCellSmooth_X135 : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  Handle.closedCellIsManifold 1

def edgeClosedCellProduct :
    (ClosedCell 2 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), 𝓡∂ 3⟯ radialEdgeSet :=
  ((GC.Seifert.unitDiscClosedCell.{0}.symm).prodCongr
    (Diffeomorph.refl (𝓡 1) Circle ∞)).trans edgeProduct

end GC.GraphManifold.Assembly.FC39P0.X135Radial
