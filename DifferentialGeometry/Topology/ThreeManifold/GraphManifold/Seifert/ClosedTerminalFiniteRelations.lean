import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TerminalUnionPrimeVertex

/-!
# Actual filling relations and the fibre of a closed triangle block

A solid meridian is killed by the actual filling into the carrier. Its image on the product
boundary has precisely the filling slope coordinates, up to the primitive-slope sign convention.
The native product fibre maps to the original fibre class of the block. These are actual
boundary and filling statements; they do not assert finiteness of the carrier fundamental group.
-/

set_option autoImplicit false
noncomputable section
open Multiplicative
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Topology ContinuousMap unitInterval
universe u
namespace GC.Seifert

set_option backward.isDefEq.respectTransparency false in
theorem circleTurnLoop_degree_one :
    fundamentalGroupCircleEquivInt
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (circleTurnLoop 1))) =
        ofAdd (1 : ℤ) := by
  let e := AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)
  have he : e (0 : UnitAddCircle) = 1 := by
    change AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0) 0 = 1
    rw [AddCircle.homeomorphCircle_apply]
    exact AddCircle.toCircle_zero
  let E := fundamentalGroupMulEquivOfHomotopyEquiv e.toHomotopyEquiv 0 1 he
  let a : FundamentalGroup UnitAddCircle 0 :=
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk circleGeneratorPath)
  have hmap : E a =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (circleTurnLoop 1)) := by
    change FundamentalGroup.mapOfEq e.toHomotopyEquiv.toFun he a = _
    rw [FundamentalGroup.mapOfEq_apply]
    apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    funext θ
    change e (circleGeneratorPath θ) = circleTurn θ * 1
    rw [mul_one]
    exact AddCircle.homeomorphCircle_apply _ _
  change fundamentalGroupUnitAddCircleEquivInt (E.symm _) = _
  rw [← hmap, E.symm_apply_apply]
  exact fundamentalGroupUnitAddCircleEquivInt_generator

set_option backward.isDefEq.respectTransparency false in
theorem torusTurnLoop_coordinates :
    toAdd (torusCoordinates
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (torusTurnLoop torusBase)))) =
        ![0, 1] := by
  let g : FundamentalGroup Torus torusBase :=
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (torusTurnLoop torusBase))
  have hfst : FundamentalGroup.map ContinuousMap.fst torusBase g = 1 := by
    exact fundamentalGroup_map_const (1 : Circle) (1 : Circle)
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (circleTurnLoop 1)))
  have hsnd : FundamentalGroup.map ContinuousMap.snd torusBase g =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (circleTurnLoop 1)) := rfl
  change toAdd (torusCoordinates g) = _
  rw [toAdd_torusCoordinates, hfst, hsnd, map_one, circleTurnLoop_degree_one]
  rfl

namespace ProductFibredPiece

variable {W : CompactCarrier.{u}} {T : TorusPresentation W} {i : Fin T.components.count}

theorem solidMeridian_map_eq_one (P : SolidTorusPiece T i)
    (a : FundamentalGroup Circle 1) :
    FundamentalGroup.map (P.portMap 0) torusBase
      (FundamentalGroup.map circleInc 1 a) = 1 := by
  have := P.base.simplyConnectedSpace_one
  apply (P.fundamentalGroupEquiv (P.base.boundaryCircle 0 1) 1).injective
  calc
    P.fundamentalGroupEquiv (P.base.boundaryCircle 0 1) 1
        (FundamentalGroup.map (P.portMap 0) torusBase
          (FundamentalGroup.map circleInc 1 a)) =
        Prod.map (FundamentalGroup.map (P.base.boundaryCircle 0) 1) id
          (fundamentalGroupProdEquiv 1 1 (FundamentalGroup.map circleInc 1 a)) :=
      P.fundamentalGroupEquiv_map_portMap 0 torusBase _
    _ = 1 := by
      apply Prod.ext (Subsingleton.elim _ _)
      change FundamentalGroup.map ContinuousMap.snd torusBase
        (FundamentalGroup.map circleInc 1 a) = 1
      refine Eq.trans ?_ (fundamentalGroup_map_const (1 : Circle) (1 : Circle) a)
      induction a using Path.Homotopic.Quotient.ind
      rfl
    _ = P.fundamentalGroupEquiv (P.base.boundaryCircle 0 1) 1 1 := (map_one _).symm

end ProductFibredPiece

namespace SeifertBlock

variable {W : CompactCarrier.{u}} {d : SeifertData}

abbrev filledBoundaryMap (B : SeifertBlock W d) (m : Fin d.fillingCount) : C(Torus, W.Carrier) :=
  B.productToCarrier.comp (B.product.portMap (B.port (.inr m)))

theorem filledBoundaryMap_matching (B : SeifertBlock W d) (m : Fin d.fillingCount) :
    (B.filledBoundaryMap m).comp (B.presentation.matchingMap (B.seam m)) =
      (B.presentation.pieceToCarrier (B.piece (some m))).comp ((B.solid m).portMap 0) := by
  ext t
  change B.presentation.cutMap (B.product.portMap (B.port (.inr m))
    (B.presentation.pairing.matching (B.seam m) t)) =
      B.presentation.cutMap ((B.solid m).portMap 0 t)
  rw [B.portMap_filled_val, B.portMap_solid_val,
    ← B.presentation.seamTorus_eq_cutMap_right, ← B.presentation.seamTorus_eq_cutMap]

theorem filledMeridian_map_eq_one (B : SeifertBlock W d) (m : Fin d.fillingCount)
    (a : FundamentalGroup Circle 1) :
    FundamentalGroup.map ((B.filledBoundaryMap m).comp
      (B.presentation.matchingMap (B.seam m))) torusBase
        (FundamentalGroup.map circleInc 1 a) = 1 := by
  rw [B.filledBoundaryMap_matching, GC.Topology.fundamentalGroup_map_comp]
  change FundamentalGroup.map (B.presentation.pieceToCarrier (B.piece (some m)))
    ((B.solid m).portMap 0 torusBase)
      (FundamentalGroup.map ((B.solid m).portMap 0) torusBase
        (FundamentalGroup.map circleInc 1 a)) = 1
  rw [(B.solid m).solidMeridian_map_eq_one, map_one]

theorem filledMeridian_torusAut_map_eq_one (B : SeifertBlock W d) (m : Fin d.fillingCount)
    (a : FundamentalGroup Circle 1) :
    FundamentalGroup.map (B.filledBoundaryMap m) torusBase
      (torusAut (B.presentation.matchingMap (B.seam m))
        (FundamentalGroup.map circleInc 1 a)) = 1 := by
  let M := B.presentation.matchingMap (B.seam m)
  let β := PathConnectedSpace.somePath torusBase (M torusBase)
  rw [torusAut_eq M β]
  change FundamentalGroup.map (B.filledBoundaryMap m) torusBase
    (fundamentalGroupChangeBasepoint β
      (FundamentalGroup.map M torusBase (FundamentalGroup.map circleInc 1 a))) = 1
  rw [changeBasepoint_map]
  have h := B.filledMeridian_map_eq_one m a
  rw [GC.Topology.fundamentalGroup_map_comp] at h
  change FundamentalGroup.map (B.filledBoundaryMap m) (M torusBase)
    (FundamentalGroup.map M torusBase (FundamentalGroup.map circleInc 1 a)) = 1 at h
  rw [h, map_one]

theorem filledMeridian_coordinates (B : SeifertBlock W d) (m : Fin d.fillingCount)
    (a : FundamentalGroup Circle 1) :
    let v := toAdd (torusCoordinates
      (torusAut (B.presentation.matchingMap (B.seam m))
        (FundamentalGroup.map circleInc 1 a)))
    let n := toAdd (fundamentalGroupCircleEquivInt a)
    (v 0, v 1) = n • d.fillingSlope m ∨ (v 0, v 1) = -(n • d.fillingSlope m) := by
  let M := B.presentation.matchingMap (B.seam m)
  let n := toAdd (fundamentalGroupCircleEquivInt a)
  have h := torusMapMatrix_mulVec M (FundamentalGroup.map circleInc 1 a)
  rw [toAdd_torusCoordinates_circleInc] at h
  have hmat : torusMapMatrix M =
      torusMatrix (B.presentation.pairing.matching (B.seam m)) := by
    apply congrArg torusMapMatrix
    exact ContinuousMap.ext fun t => rfl
  have hv : ∀ i : Fin 2, toAdd (torusCoordinates
      (torusAut M (FundamentalGroup.map circleInc 1 a))) i =
        torusMatrix (B.presentation.pairing.matching (B.seam m)) i 0 * n := by
    intro i
    rw [← h]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero, add_zero]
    rw [hmat]
  change _ ∨ _
  rw [hv 0, hv 1]
  rcases B.torusMatrix_meridian m with hs | hs
  · left
    have h0 : torusMatrix (B.presentation.pairing.matching (B.seam m)) 0 0 =
        (d.fillingSlope m).1 := congrArg Prod.fst hs
    have h1 : torusMatrix (B.presentation.pairing.matching (B.seam m)) 1 0 =
        (d.fillingSlope m).2 := congrArg Prod.snd hs
    change (_, _) = (n * (d.fillingSlope m).1, n * (d.fillingSlope m).2)
    rw [h0, h1]
    exact Prod.ext (mul_comm _ _) (mul_comm _ _)
  · right
    have h0 := congrArg Prod.fst hs
    have h1 := congrArg Prod.snd hs
    simp only [Prod.fst_neg, Prod.snd_neg] at h0 h1
    change (_, _) = (-(n * (d.fillingSlope m).1), -(n * (d.fillingSlope m).2))
    rw [h0, h1]
    exact Prod.ext (by ring) (by ring)

theorem filledSlope_map_eq_one (B : SeifertBlock W d) (m : Fin d.fillingCount) :
    FundamentalGroup.map (B.filledBoundaryMap m) torusBase
      (torusCoordinates.symm (ofAdd ![(d.fillingSlope m).1, (d.fillingSlope m).2])) = 1 := by
  let a := fundamentalGroupCircleEquivInt.symm (ofAdd (1 : ℤ))
  let g := torusAut (B.presentation.matchingMap (B.seam m))
    (FundamentalGroup.map circleInc 1 a)
  let v : Fin 2 → ℤ := ![(d.fillingSlope m).1, (d.fillingSlope m).2]
  have hk : FundamentalGroup.map (B.filledBoundaryMap m) torusBase g = 1 :=
    B.filledMeridian_torusAut_map_eq_one m a
  have hc := B.filledMeridian_coordinates m a
  have ha : toAdd (fundamentalGroupCircleEquivInt a) = 1 := by simp [a]
  dsimp only at hc
  rw [ha, one_smul] at hc
  have hv : toAdd (torusCoordinates g) = v ∨ toAdd (torusCoordinates g) = -v := by
    rcases hc with hc | hc
    · left
      ext i
      fin_cases i
      · exact congrArg Prod.fst hc
      · exact congrArg Prod.snd hc
    · right
      ext i
      fin_cases i
      · exact congrArg Prod.fst hc
      · exact congrArg Prod.snd hc
  rcases hv with hv | hv
  · have hg : g = torusCoordinates.symm (ofAdd v) := by
      apply torusCoordinates.injective
      apply toAdd.injective
      simpa only [MulEquiv.apply_symm_apply, toAdd_ofAdd] using hv
    exact hg ▸ hk
  · have hg : g = (torusCoordinates.symm (ofAdd v))⁻¹ := by
      apply torusCoordinates.injective
      apply toAdd.injective
      simpa only [map_inv, MulEquiv.apply_symm_apply, toAdd_inv, toAdd_ofAdd] using hv
    rw [hg, map_inv, inv_eq_one] at hk
    exact hk

theorem filledBoundaryMap_fibre (B : SeifertBlock W d) (m : Fin d.fillingCount) (t : Torus) :
    FundamentalGroup.map (B.filledBoundaryMap m) t
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (torusTurnLoop t))) =
        B.fibreClass (B.product.portMap (B.port (.inr m)) t) := by
  change FundamentalGroup.map
    (B.productToCarrier.comp (B.product.portMap (B.port (.inr m)))) t _ = _
  rw [GC.Topology.fundamentalGroup_map_comp]
  change FundamentalGroup.map B.productToCarrier (B.product.portMap (B.port (.inr m)) t)
    (FundamentalGroup.map (B.product.portMap (B.port (.inr m))) t
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (torusTurnLoop t)))) = _
  rw [← ProductFibredPiece.turnLoop_portMap]
  rfl

def filledSectionClass (B : SeifertBlock W d) (m : Fin d.fillingCount) :
    FundamentalGroup W.Carrier
      (B.productToCarrier (B.product.portMap (B.port (.inr m)) torusBase)) :=
  FundamentalGroup.map (B.filledBoundaryMap m) torusBase
    (torusCoordinates.symm (ofAdd ![1, 0]))

theorem filledCoordinateFibre_eq (B : SeifertBlock W d) (m : Fin d.fillingCount) :
    FundamentalGroup.map (B.filledBoundaryMap m) torusBase
      (torusCoordinates.symm (ofAdd ![0, 1])) =
        B.fibreClass (B.product.portMap (B.port (.inr m)) torusBase) := by
  have hg : torusCoordinates.symm (ofAdd ![0, 1]) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (torusTurnLoop torusBase)) := by
    apply torusCoordinates.injective
    apply toAdd.injective
    simpa only [MulEquiv.apply_symm_apply, toAdd_ofAdd] using torusTurnLoop_coordinates.symm
  rw [hg]
  exact B.filledBoundaryMap_fibre m torusBase

set_option backward.isDefEq.respectTransparency false in
theorem filledSection_fibre_relation (B : SeifertBlock W d) (m : Fin d.fillingCount) :
    B.filledSectionClass m ^ (d.fillingSlope m).1 *
      B.fibreClass (B.product.portMap (B.port (.inr m)) torusBase) ^ (d.fillingSlope m).2 =
        1 := by
  rw [← B.filledCoordinateFibre_eq]
  change FundamentalGroup.map (B.filledBoundaryMap m) torusBase
      (torusCoordinates.symm (ofAdd ![1, 0])) ^ (d.fillingSlope m).1 * _ = 1
  rw [← map_zpow (FundamentalGroup.map (B.filledBoundaryMap m) torusBase),
    ← map_zpow (FundamentalGroup.map (B.filledBoundaryMap m) torusBase),
    ← map_mul (FundamentalGroup.map (B.filledBoundaryMap m) torusBase)]
  have hvec : torusCoordinates.symm (ofAdd ![1, 0]) ^ (d.fillingSlope m).1 *
      torusCoordinates.symm (ofAdd ![0, 1]) ^ (d.fillingSlope m).2 =
        torusCoordinates.symm (ofAdd ![(d.fillingSlope m).1, (d.fillingSlope m).2]) := by
    apply torusCoordinates.injective
    apply toAdd.injective
    simp only [map_mul, map_zpow, MulEquiv.apply_symm_apply, toAdd_mul, toAdd_zpow,
      toAdd_ofAdd]
    ext i
    fin_cases i <;> simp
  rw [hvec]
  exact B.filledSlope_map_eq_one m

set_option backward.isDefEq.respectTransparency false in
theorem fibreClass_changeBasepoint (B : SeifertBlock W d)
    {p q : B.presentation.components.piece (B.piece none)} (β : Path p q) :
    fundamentalGroupChangeBasepoint (β.map B.productToCarrier.continuous) (B.fibreClass q) =
      B.fibreClass p := by
  have h := turnLoop_naturality B.product.turn B.productToCarrier β
  change Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk
    (β.map B.productToCarrier.continuous)) (B.fibreClass q) =
      Path.Homotopic.Quotient.trans (B.fibreClass p) (Path.Homotopic.Quotient.mk
        (β.map B.productToCarrier.continuous)) at h
  rw [fundamentalGroupChangeBasepoint_apply]
  change Path.Homotopic.Quotient.trans
    (Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk
      (β.map B.productToCarrier.continuous)) (B.fibreClass q))
    (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk
      (β.map B.productToCarrier.continuous))) = B.fibreClass p
  rw [h, Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.trans_refl]

def filledMarkedSectionClass (B : SeifertBlock W d)
    (p : B.presentation.components.piece (B.piece none)) (m : Fin d.fillingCount)
    (β : Path p (B.product.portMap (B.port (.inr m)) torusBase)) :
    FundamentalGroup W.Carrier (B.productToCarrier p) :=
  fundamentalGroupChangeBasepoint (β.map B.productToCarrier.continuous) (B.filledSectionClass m)

set_option backward.isDefEq.respectTransparency false in
theorem filledMarkedSection_fibre_relation (B : SeifertBlock W d)
    (p : B.presentation.components.piece (B.piece none)) (m : Fin d.fillingCount)
    (β : Path p (B.product.portMap (B.port (.inr m)) torusBase)) :
    B.filledMarkedSectionClass p m β ^ (d.fillingSlope m).1 *
      B.fibreClass p ^ (d.fillingSlope m).2 = 1 := by
  have h := congrArg (fundamentalGroupChangeBasepoint
    (β.map B.productToCarrier.continuous)) (B.filledSection_fibre_relation m)
  rw [map_mul, map_zpow, map_zpow, map_one, B.fibreClass_changeBasepoint] at h
  exact h

end SeifertBlock
end GC.Seifert
