import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsDegrees
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClassicalInputs
import DifferentialGeometry.Topology.FundamentalGroup.TorusHomeomorphMatrixCoherence
import DifferentialGeometry.Topology.Algebra.Group.TorusIntersection
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.SolidTorusBoundaryTori
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.SolidTorusMeridian
import DifferentialGeometry.Topology.Manifold.ClosedBall

/-!
# Adapters between the Seifert slope vocabulary and the torus-matrix modules

Chapter 6. Dictionary between `GC.Seifert` (`Slope`, `PantsDegrees`, `ClassicalInputs`) and the
torus modules `Circle.slopeMap`, `Circle.matrixDiffeomorph`, `GC.Topology.torusHomeomorphMatrix`,
`Int.PrimitiveSlope` and `circlePowerMap`.

Both sides use `torusFundamentalGroup` at `(1, 1)` and column vectors: the slope `(p, q)` is
`p` times the first-factor loop plus `q` times the second-factor loop, carried by
`z ↦ (z ^ p, z ^ q)` (`toAdd_torusCoordinates_slope`), and a matrix acts by `mulVec`. Hence no
transpose or inverse appears: `torusMatrix φ` is the value of `torusHomeomorphMatrix` at the
underlying homeomorphism (`torusMatrix_eq_torusHomeomorphMatrix`), `torusUnit φ` equals it
(`torusUnit_eq_torusHomeomorphMatrix`), and `linearTorusDiffeomorph A` is `matrixDiffeomorph A`.
This proves the named input `TorusMatrixLinear` (`torusMatrixLinear`), so `torusUnit` is onto
(`surjective_torusUnit`); `torusMapMatrix (matrixContinuousMap A) = A` for every integer matrix.

`circleDegree (circlePowerMap k) = k`, `circleDegree (u ^ k) = k * circleDegree u`, and for a
based map `u` the degree is the factor by which `u` multiplies `π₁(S¹, 1) ≅ ℤ`
(`fundamentalGroupCircleEquivInt_mapOfEq`, the form of `fundamentalGroupCircleEquivInt_map_power`).

`primitiveSlopeEquiv : PrimitiveSlope ≃ Int.PrimitiveSlope` sends `(p, q)` to `![p, q]`
(`gcd = 1` against `IsCoprime`). Both determinants are `v₀ w₁ - v₁ w₀`, with the same sign; our
`delta` is its `natAbs` in `ℕ`, theirs its `abs` in `ℤ` (`natCast_delta`, `delta_eq_toNat`). The
equivalence intertwines `A • s` with `Int.PrimitiveSlope.map A` (`primitiveSlopeEquiv_smul`), and
two distinct slope circles of the torus meet in exactly `delta` points (`card_slopeSet_inter`).

Solid tori. `unitDiscClosedCell : UnitDisc ≃ₘ ClosedCell 2` is `Complex.orthonormalBasisOneI.repr`
(`1 ↦ e₀`, `I ↦ e₁`, the identification used by `closedDiskBoundary`), and
`solidTorusClosedSolidTorus` is the diffeomorphism from the Clifford solid torus
`solidTorusCarrier` to `closedSolidTorusCarrier` through `solidTorusDiscCircle`. It carries the
boundary torus of `solidTorusBoundary` onto that of `closedSolidTorusBoundaryTori` on the nose
(`solidTorusClosedSolidTorus_torusMap`): on both sides the first torus coordinate is the meridian
`meridianSlope = (1, 0)` and the second the core direction `fiberSlope = (0, 1)`, and the meridian
disks `closedSolidTorusMeridianDisk w` bound the curves `z ↦ (z, w)` of our boundary torus.
-/

set_option autoImplicit false

noncomputable section
open Multiplicative
open DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Matrix

namespace GC.Seifert

section CircleDegree

theorem circlePowerMap_eq_zpow (k : ℤ) : circlePowerMap k = ContinuousMap.id Circle ^ k := by
  ext z
  simp [circlePowerMap]

def circleDegreeHom : C(Circle, Circle) →* Multiplicative ℤ :=
  MonoidHom.mk' (fun u => ofAdd (circleDegree u)) fun u v => by rw [circleDegree_mul, ofAdd_add]

theorem circleDegree_zpow (u : C(Circle, Circle)) (k : ℤ) :
    circleDegree (u ^ k) = k * circleDegree u := by
  have h := congrArg toAdd (map_zpow circleDegreeHom u k)
  simpa [circleDegreeHom, toAdd_zpow, smul_eq_mul] using h

theorem circleDegree_circlePowerMap (k : ℤ) : circleDegree (circlePowerMap k) = k := by
  rw [circlePowerMap_eq_zpow, circleDegree_zpow, circleDegree_id, mul_one]

end CircleDegree

section TorusMatrix

theorem toAdd_torusCoordinates_eq (g : FundamentalGroup Torus torusBase) :
    toAdd (torusCoordinates g) =
      ![toAdd (GC.Topology.torusFundamentalGroup g).1,
        toAdd (GC.Topology.torusFundamentalGroup g).2] :=
  rfl

theorem torusMapMatrix_eq_torusHomeomorphMatrix (e : Torus ≃ₜ Torus) :
    torusMapMatrix (e : C(Torus, Torus)) = (GC.Topology.torusHomeomorphMatrix e).val := by
  refine Matrix.ext_iff_mulVec.2 fun v => ?_
  obtain ⟨g, rfl⟩ := exists_toAdd_torusCoordinates v
  rw [torusMapMatrix_mulVec, torusAut_eq _ (PathConnectedSpace.somePath torusBase (e torusBase)),
    toAdd_torusCoordinates_eq, toAdd_torusCoordinates_eq,
    GC.Topology.torusHomeomorphMatrix_mulVec]

theorem torusMatrix_eq_torusHomeomorphMatrix (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    torusMatrix φ = (GC.Topology.torusHomeomorphMatrix φ.toHomeomorph).val :=
  torusMapMatrix_eq_torusHomeomorphMatrix φ.toHomeomorph

theorem torusUnit_eq_torusHomeomorphMatrix (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    torusUnit φ = GC.Topology.torusHomeomorphMatrix φ.toHomeomorph :=
  Units.ext (torusMatrix_eq_torusHomeomorphMatrix φ)

theorem linearTorusDiffeomorph_eq_matrixDiffeomorph (A : GL (Fin 2) ℤ) :
    linearTorusDiffeomorph A = Circle.matrixDiffeomorph A :=
  Diffeomorph.ext fun _ => rfl

theorem torusMatrix_linearTorusDiffeomorph (A : GL (Fin 2) ℤ) :
    torusMatrix (linearTorusDiffeomorph A) = A := by
  rw [torusMatrix_eq_torusHomeomorphMatrix, linearTorusDiffeomorph_eq_matrixDiffeomorph,
    GC.Topology.torusHomeomorphMatrix_matrixDiffeomorph]

theorem torusUnit_linearTorusDiffeomorph (A : GL (Fin 2) ℤ) :
    torusUnit (linearTorusDiffeomorph A) = A :=
  Units.ext (torusMatrix_linearTorusDiffeomorph A)

theorem torusMatrixLinear : TorusMatrixLinear :=
  torusMatrix_linearTorusDiffeomorph

theorem surjective_torusUnit : Function.Surjective torusUnit :=
  torusUnit_surjective torusMatrixLinear

end TorusMatrix

section MarkedMaps

private theorem markedMap_cast_refl {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) {y : Y} (h : f x = y) :
    GC.Topology.markedMap f x ((Path.refl y).cast rfl h) = FundamentalGroup.mapOfEq f h := by
  subst h
  ext a
  change fundamentalGroupChangeBasepoint (Path.refl (f x)) (FundamentalGroup.map f x a) =
    FundamentalGroup.mapOfEq f rfl a
  rw [changeBasepoint_refl, FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl]
  rfl

theorem torusAut_eq_mapOfEq (f : C(Torus, Torus)) (h : f torusBase = torusBase) :
    torusAut f = FundamentalGroup.mapOfEq f h := by
  rw [torusAut_eq f ((Path.refl torusBase).cast rfl h), markedMap_cast_refl]

theorem torusMapMatrix_matrixContinuousMap (A : Matrix (Fin 2) (Fin 2) ℤ) :
    torusMapMatrix (Circle.matrixContinuousMap A) = A := by
  refine Matrix.ext_iff_mulVec.2 fun v => ?_
  obtain ⟨g, rfl⟩ := exists_toAdd_torusCoordinates v
  rw [torusMapMatrix_mulVec, torusAut_eq_mapOfEq _ (Circle.matrixContinuousMap_one A),
    toAdd_torusCoordinates_eq, toAdd_torusCoordinates_eq,
    GC.Topology.torusFundamentalGroup_map_matrix]
  ext i
  fin_cases i <;> rfl

private def circleSlice : C(Circle, Torus) := ⟨fun z => (z, 1), by fun_prop⟩

private theorem map_fst_mapOfEq_circleMapTorus (u : C(Circle, Circle)) (hu : u 1 = 1)
    (hf : circleMapTorus u torusBase = torusBase) (g : FundamentalGroup Torus torusBase) :
    FundamentalGroup.map ContinuousMap.fst torusBase
        (FundamentalGroup.mapOfEq (circleMapTorus u) hf g) =
      FundamentalGroup.mapOfEq u hu (FundamentalGroup.map ContinuousMap.fst torusBase g) := by
  induction g using Path.Homotopic.Quotient.ind with
  | mk p =>
    rw [FundamentalGroup.mapOfEq_apply]
    refine Eq.trans ?_ (FundamentalGroup.mapOfEq_apply u hu
      (FundamentalGroup.map ContinuousMap.fst torusBase (Path.Homotopic.Quotient.mk p))).symm
    rfl

theorem fundamentalGroupCircleEquivInt_mapOfEq (u : C(Circle, Circle)) (hu : u 1 = 1)
    (a : FundamentalGroup Circle 1) :
    fundamentalGroupCircleEquivInt (FundamentalGroup.mapOfEq u hu a) =
      ofAdd (circleDegree u * toAdd (fundamentalGroupCircleEquivInt a)) := by
  have hf : circleMapTorus u torusBase = torusBase := by simp [circleMapTorus, hu]
  let g : FundamentalGroup Torus torusBase := FundamentalGroup.map circleSlice 1 a
  have h1 : FundamentalGroup.map ContinuousMap.fst torusBase g = a := by
    induction a using Path.Homotopic.Quotient.ind
    rfl
  have h := congrFun (torusMapMatrix_mulVec (circleMapTorus u) g) 0
  rw [torusMapMatrix_circleMapTorus, torusAut_eq_mapOfEq _ hf, toAdd_torusCoordinates,
    toAdd_torusCoordinates, map_fst_mapOfEq_circleMapTorus u hu, h1] at h
  have h' : circleDegree u * toAdd (fundamentalGroupCircleEquivInt a) =
      toAdd (fundamentalGroupCircleEquivInt (FundamentalGroup.mapOfEq u hu a)) := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
  rw [h', ofAdd_toAdd]

end MarkedMaps

section Slopes

private theorem vec_neg (v : ℤ × ℤ) : ![(-v).1, (-v).2] = -![v.1, v.2] := by
  ext i
  fin_cases i <;> simp

def primitivePairEquiv : {v : ℤ × ℤ // IsPrimitive v} ≃ Int.PrimitivePair :=
  (finTwoArrowEquiv ℤ).symm.subtypeEquiv fun v => by
    simp [IsPrimitive, Int.isCoprime_iff_gcd_eq_one]

def primitiveSlopeEquiv : PrimitiveSlope ≃ Int.PrimitiveSlope :=
  Quotient.congr primitivePairEquiv fun v w => by
    have hinj : ∀ a b : ℤ × ℤ, ![a.1, a.2] = ![b.1, b.2] ↔ a = b := fun a b =>
      (finTwoArrowEquiv ℤ).symm.injective.eq_iff
    change (w.1 = v.1 ∨ w.1 = -v.1) ↔
      (![v.1.1, v.1.2] = ![w.1.1, w.1.2] ∨ ![v.1.1, v.1.2] = -![w.1.1, w.1.2])
    rw [← vec_neg, hinj, hinj, eq_comm]
    exact or_congr_right ⟨fun h => by rw [h, neg_neg], fun h => by rw [h, neg_neg]⟩

theorem primitiveSlopeEquiv_mk {v : ℤ × ℤ} (hv : IsPrimitive v) :
    primitiveSlopeEquiv (PrimitiveSlope.mk v hv) =
      Int.PrimitiveSlope.mk ![v.1, v.2] (Int.isCoprime_iff_gcd_eq_one.mpr hv) :=
  rfl

theorem primitiveSlopeEquiv_symm_mk (v : Fin 2 → ℤ) (hv : IsCoprime (v 0) (v 1)) :
    primitiveSlopeEquiv.symm (Int.PrimitiveSlope.mk v hv) =
      PrimitiveSlope.mk (v 0, v 1) (Int.isCoprime_iff_gcd_eq_one.mp hv) :=
  rfl

theorem primitiveSlopeEquiv_meridianSlope :
    primitiveSlopeEquiv meridianSlope = Int.PrimitiveSlope.mk ![1, 0] isCoprime_one_left :=
  rfl

theorem primitiveSlopeEquiv_fiberSlope :
    primitiveSlopeEquiv fiberSlope = Int.PrimitiveSlope.mk ![0, 1] isCoprime_one_right :=
  rfl

theorem natCast_delta (a b : PrimitiveSlope) :
    (PrimitiveSlope.delta a b : ℤ) =
      Int.PrimitiveSlope.delta (primitiveSlopeEquiv a) (primitiveSlopeEquiv b) := by
  induction a using PrimitiveSlope.ind with | h v hv => ?_
  induction b using PrimitiveSlope.ind with | h w hw => ?_
  rw [PrimitiveSlope.delta_mk, primitiveSlopeEquiv_mk, primitiveSlopeEquiv_mk,
    Int.PrimitiveSlope.delta_mk, Int.natCast_natAbs]
  rfl

theorem delta_eq_toNat (a b : PrimitiveSlope) :
    PrimitiveSlope.delta a b =
      (Int.PrimitiveSlope.delta (primitiveSlopeEquiv a) (primitiveSlopeEquiv b)).toNat := by
  rw [← natCast_delta, Int.toNat_natCast]

theorem primitiveSlopeEquiv_smul (A : GL (Fin 2) ℤ) (s : PrimitiveSlope) :
    primitiveSlopeEquiv (A • s) = Int.PrimitiveSlope.map A (primitiveSlopeEquiv s) := by
  induction s using PrimitiveSlope.ind with | h v hv => ?_
  rw [PrimitiveSlope.smul_mk, primitiveSlopeEquiv_mk, primitiveSlopeEquiv_mk,
    Int.PrimitiveSlope.map_mk, Int.PrimitiveSlope.mk_eq_mk_iff]
  left
  ext i
  fin_cases i <;> simp [smulVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem primitiveSlopeEquiv_torusUnit_smul (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (s : PrimitiveSlope) :
    primitiveSlopeEquiv (torusUnit φ • s) =
      Int.PrimitiveSlope.map (GC.Topology.torusHomeomorphMatrix φ.toHomeomorph)
        (primitiveSlopeEquiv s) := by
  rw [primitiveSlopeEquiv_smul, torusUnit_eq_torusHomeomorphMatrix]

theorem slopeSet_primitiveSlopeEquiv_mk {p q : ℤ} (h : IsPrimitive (p, q)) :
    Circle.slopeSet (primitiveSlopeEquiv (PrimitiveSlope.mk (p, q) h)) =
      Set.range fun z : Circle => ((z ^ p, z ^ q) : Torus) :=
  rfl

theorem card_slopeSet_inter {a b : PrimitiveSlope} (h : a ≠ b) :
    Nat.card ↥(Circle.slopeSet (primitiveSlopeEquiv a) ∩
      Circle.slopeSet (primitiveSlopeEquiv b)) = PrimitiveSlope.delta a b := by
  rw [Circle.card_slopeSet_intersection (primitiveSlopeEquiv.injective.ne h), delta_eq_toNat]

theorem linearTorusDiffeomorph_image_slopeSet (A : GL (Fin 2) ℤ) (s : PrimitiveSlope) :
    linearTorusDiffeomorph A '' Circle.slopeSet (primitiveSlopeEquiv s) =
      Circle.slopeSet (primitiveSlopeEquiv (A • s)) := by
  rw [linearTorusDiffeomorph_eq_matrixDiffeomorph, Circle.matrixDiffeomorph_image_slopeSet,
    primitiveSlopeEquiv_smul]

theorem toAdd_torusCoordinates_slope (v : Fin 2 → ℤ) (a : FundamentalGroup Circle 1) :
    toAdd (torusCoordinates (FundamentalGroup.mapOfEq (Circle.slopeContinuousMap v)
      (Circle.slopeContinuousMap_one v) a)) = toAdd (fundamentalGroupCircleEquivInt a) • v := by
  rw [toAdd_torusCoordinates_eq, GC.Topology.torusFundamentalGroup_map_slope]
  ext i
  fin_cases i <;> simp [mul_comm]

end Slopes

section SolidTorus

universe u

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

open GC.GraphManifold DifferentialGeometry.Topology.Manifold

def unitDiscClosedCell : UnitDisc.{u} ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2 where
  toFun w := ⟨Complex.orthonormalBasisOneI.repr w.down.val, by
    rw [LinearIsometryEquiv.norm_map]
    exact (sq_le_one_iff₀ (norm_nonneg _)).mp w.down.2⟩
  invFun x := ULift.up ⟨Complex.orthonormalBasisOneI.repr.symm x.val, by
    change ‖_‖ ^ 2 ≤ 1
    rw [LinearIsometryEquiv.norm_map]
    exact (sq_le_one_iff₀ (norm_nonneg _)).mpr x.2⟩
  left_inv w := ULift.ext (Subtype.ext (Complex.orthonormalBasisOneI.repr.symm_apply_apply _))
  right_inv x := Subtype.ext (Complex.orthonormalBasisOneI.repr.apply_symm_apply x.val)
  contMDiff_toFun := by
    have h : ContMDiff (𝓡∂ 2) (𝓡 2) ∞
        (fun w : UnitDisc.{u} => Complex.orthonormalBasisOneI.repr w.down.val) :=
      Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv.contDiff.contMDiff.comp
        contMDiff_disc_val
    apply (ContMDiff.iff_comp_isImmersion
      (isSmoothEmbedding_closedCell_inclusion 1).isImmersion).mpr
    exact ⟨h.continuous.subtype_mk _, h⟩
  contMDiff_invFun := by
    have h : ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ (fun x : ClosedCell 2 =>
        (⟨Complex.orthonormalBasisOneI.repr.symm x.val, by
          change ‖_‖ ^ 2 ≤ 1
          rw [LinearIsometryEquiv.norm_map]
          exact (sq_le_one_iff₀ (norm_nonneg _)).mpr x.2⟩ : unitDiscSet)) :=
      (unitDiscAtlas.contMDiff_iff_subtype_val _).mpr
        (Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv.contDiff.contMDiff.comp
          (isSmoothEmbedding_closedCell_inclusion 1).contMDiff)
    exact (uliftDiffeomorph (𝓡∂ 2) unitDiscSet).contMDiff.comp h

theorem unitDiscClosedCell_apply (w : UnitDisc.{u}) :
    (unitDiscClosedCell w).val = Complex.orthonormalBasisOneI.repr w.down.val :=
  rfl

theorem unitDiscClosedCell_symm_apply (x : ClosedCell 2) :
    (unitDiscClosedCell.{u}.symm x).down.val = Complex.orthonormalBasisOneI.repr.symm x.val :=
  rfl

def solidTorusClosedSolidTorus :
    solidTorusCarrier.{u}.Carrier ≃ₘ⟮solidTorusCarrier.{u}.model, closedSolidTorusCarrier.model⟯
      closedSolidTorusCarrier.Carrier :=
  (solidTorusDiscCircle.trans
    (unitDiscClosedCell.prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞))).trans
    closedSolidTorusCarrierDiffeomorph

theorem solidTorusClosedSolidTorus_apply (p : solidTorusCarrier.{u}.Carrier) :
    solidTorusClosedSolidTorus p =
      (unitDiscClosedCell (solidTorusDiscCircle p).1, (solidTorusDiscCircle p).2) :=
  rfl

theorem solidTorusClosedSolidTorus_torusMap (z : Torus) :
    solidTorusClosedSolidTorus (solidTorusBoundary.{u}.torusMap 0 z) =
      closedSolidTorusBoundaryTori.torusMap 0 z := by
  rw [closedSolidTorusBoundaryTori_torusMap]
  have h0 : -halfZero.val 0 = 0 := by
    rw [show halfZero.val 0 = 0 from rfl, neg_zero]
  have hfirst : (√2 : ℝ) * seamFirst (-halfZero.val 0) = 1 := by
    rw [h0, seamFirst, seamClamp_of_mem (by norm_num) (by norm_num),
      ← Real.sqrt_mul (by norm_num)]
    norm_num
  refine Prod.ext (Subtype.ext ?_) ?_
  · change Complex.orthonormalBasisOneI.repr
        ((√2 : ℝ) • sphereFirst (cliffordSeamMap.{u} (z, -halfZero.val 0))) =
      Complex.orthonormalBasisOneI.repr (z.1 : ℂ)
    rw [sphereFirst_cliffordSeamMap, smul_smul, hfirst, one_smul]
  · change unitOf (sphereSecond (cliffordSeamMap.{u} (z, -halfZero.val 0))) = z.2
    rw [sphereSecond_cliffordSeamMap]
    exact unitOf_smul (seamSecond_pos (by rw [h0]; norm_num)) z.2

theorem solidTorusClosedSolidTorus_symm_meridianDisk (w z : Circle) :
    solidTorusClosedSolidTorus.{u}.symm (closedSolidTorusMeridianDisk w (closedDiskBoundary z)) =
      solidTorusBoundary.{u}.torusMap 0 (z, w) := by
  rw [closedSolidTorusMeridianDisk_boundary, ← closedSolidTorusBoundaryTori_torusMap 0,
    ← solidTorusClosedSolidTorus_torusMap, Diffeomorph.symm_apply_apply]

end SolidTorus

end GC.Seifert
