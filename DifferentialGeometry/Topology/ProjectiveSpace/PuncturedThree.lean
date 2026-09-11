import DifferentialGeometry.Topology.ProjectiveSpace.Real
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.GroupTheory.GroupAction.SubMulAction

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry

private noncomputable def realProjectiveThreeSplit :
    EuclideanSpace Real (Fin 4) ≃L[Real]
      EuclideanSpace Real (Fin 3) × EuclideanSpace Real (Fin 1) := by
  simpa only [Nat.reduceAdd] using
    (EuclideanSpace.finAddEquivProd (𝕜 := Real) (n := 3) (m := 1))

private def realProjectiveThreeScalarLine
    (t : Real) : EuclideanSpace Real (Fin 1) :=
  WithLp.toLp 2 (fun _ => t)

private theorem realProjectiveThreeScalarLine_apply (t : Real) :
    realProjectiveThreeScalarLine t 0 = t :=
  rfl

private theorem realProjectiveThreeScalarLine_ext
    (w : EuclideanSpace Real (Fin 1)) :
    realProjectiveThreeScalarLine (w 0) = w := by
  ext i
  fin_cases i
  rfl

private theorem realProjectiveThreeScalarLine_smul (a t : Real) :
    realProjectiveThreeScalarLine (a * t) =
      a • realProjectiveThreeScalarLine t := by
  ext i
  fin_cases i
  simp [realProjectiveThreeScalarLine_apply]

private theorem realProjectiveThreeScalarLine_continuous :
    Continuous realProjectiveThreeScalarLine :=
  (PiLp.continuous_toLp (p := 2)
    (β := fun _ : Fin 1 => Real)).comp
      (continuous_pi fun _ => continuous_id)

private def twoSphereProdRealVector
    (x : Metric.sphere
      (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    EuclideanSpace Real (Fin 4) :=
  realProjectiveThreeSplit.symm
    (x.1.1, realProjectiveThreeScalarLine x.2)

private theorem twoSphereProdRealVector_ne_zero
    (x : Metric.sphere
      (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    twoSphereProdRealVector x ≠ 0 := by
  intro h
  have hp := congrArg realProjectiveThreeSplit h
  change realProjectiveThreeSplit
      (realProjectiveThreeSplit.symm
        (x.1.1, realProjectiveThreeScalarLine x.2)) =
    realProjectiveThreeSplit 0 at hp
  rw [realProjectiveThreeSplit.apply_symm_apply, map_zero] at hp
  have hfirst : (x.1.1 : EuclideanSpace Real (Fin 3)) = 0 :=
    congrArg Prod.fst hp
  exact ne_zero_of_mem_unit_sphere x.1 hfirst

private theorem twoSphereProdRealVector_neg
    (x : Metric.sphere
      (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    twoSphereProdRealVector (-x.1, -x.2) =
      -twoSphereProdRealVector x := by
  apply realProjectiveThreeSplit.injective
  rw [twoSphereProdRealVector,
    realProjectiveThreeSplit.apply_symm_apply, map_neg,
    twoSphereProdRealVector,
    realProjectiveThreeSplit.apply_symm_apply]
  apply Prod.ext
  · rfl
  · ext i
    fin_cases i
    simp [realProjectiveThreeScalarLine_apply]

private def twoSphereProdRealNonzeroVector
    (x : Metric.sphere
      (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    ({0}ᶜ : Set (EuclideanSpace Real (Fin 4))) :=
  ⟨twoSphereProdRealVector x, twoSphereProdRealVector_ne_zero x⟩

private noncomputable def twoSphereProdRealToThreeSphere
    (x : Metric.sphere
      (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1 :=
  (homeomorphUnitSphereProd (EuclideanSpace Real (Fin 4))
    (twoSphereProdRealNonzeroVector x)).1

private theorem twoSphereProdRealToThreeSphere_coe
    (x : Metric.sphere
      (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    (twoSphereProdRealToThreeSphere x :
        EuclideanSpace Real (Fin 4)) =
      ‖twoSphereProdRealVector x‖⁻¹ • twoSphereProdRealVector x := by
  simp [twoSphereProdRealToThreeSphere, twoSphereProdRealNonzeroVector,
    homeomorphUnitSphereProd, homeomorphSphereProd]

private theorem twoSphereProdRealNonzeroVector_continuous :
    Continuous twoSphereProdRealNonzeroVector := by
  apply Continuous.subtype_mk
  unfold twoSphereProdRealVector
  exact realProjectiveThreeSplit.symm.continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (realProjectiveThreeScalarLine_continuous.comp continuous_snd))

private theorem twoSphereProdRealToThreeSphere_continuous :
    Continuous twoSphereProdRealToThreeSphere :=
  continuous_fst.comp
    ((homeomorphUnitSphereProd
      (EuclideanSpace Real (Fin 4))).continuous.comp
        twoSphereProdRealNonzeroVector_continuous)

private theorem realProjectiveThreeSplit_twoSphereProdRealToThreeSphere
    (x : Metric.sphere
      (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    realProjectiveThreeSplit
        (twoSphereProdRealToThreeSphere x :
          EuclideanSpace Real (Fin 4)) =
      (‖twoSphereProdRealVector x‖⁻¹ • x.1.1,
        ‖twoSphereProdRealVector x‖⁻¹ •
          realProjectiveThreeScalarLine x.2) := by
  rw [twoSphereProdRealToThreeSphere_coe, map_smul,
    twoSphereProdRealVector,
    realProjectiveThreeSplit.apply_symm_apply, Prod.smul_mk]

private theorem twoSphereProdRealToThreeSphere_neg
    (x : Metric.sphere
      (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    twoSphereProdRealToThreeSphere (-x.1, -x.2) =
      -twoSphereProdRealToThreeSphere x := by
  apply Subtype.ext
  change (twoSphereProdRealToThreeSphere (-x.1, -x.2) :
      EuclideanSpace Real (Fin 4)) =
    -(twoSphereProdRealToThreeSphere x :
      EuclideanSpace Real (Fin 4))
  rw [twoSphereProdRealToThreeSphere_coe,
    twoSphereProdRealVector_neg, norm_neg,
    twoSphereProdRealToThreeSphere_coe]
  simp

private abbrev ThreeSphereWithNonzeroFirst :=
  {z : Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1 //
    (realProjectiveThreeSplit z.1).1 ≠ 0}

private def twoSphereProdRealToThreeSphereWithNonzeroFirst
    (x : Metric.sphere
      (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    ThreeSphereWithNonzeroFirst :=
  ⟨twoSphereProdRealToThreeSphere x, by
    rw [realProjectiveThreeSplit_twoSphereProdRealToThreeSphere]
    exact smul_ne_zero
      (inv_ne_zero
        (norm_ne_zero_iff.mpr (twoSphereProdRealVector_ne_zero x)))
      (ne_zero_of_mem_unit_sphere x.1)⟩

private theorem twoSphereProdRealToThreeSphereWithNonzeroFirst_continuous :
    Continuous twoSphereProdRealToThreeSphereWithNonzeroFirst :=
  twoSphereProdRealToThreeSphere_continuous.subtype_mk _

private def threeSphereFirstNonzeroVector
    (z : ThreeSphereWithNonzeroFirst) :
    ({0}ᶜ : Set (EuclideanSpace Real (Fin 3))) :=
  ⟨(realProjectiveThreeSplit z.1.1).1, z.2⟩

private noncomputable def threeSphereWithNonzeroFirstToTwoSphereProdReal
    (z : ThreeSphereWithNonzeroFirst) :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real :=
  ((homeomorphUnitSphereProd (EuclideanSpace Real (Fin 3))
      (threeSphereFirstNonzeroVector z)).1,
    (realProjectiveThreeSplit z.1.1).2 0 /
      ‖(realProjectiveThreeSplit z.1.1).1‖)

private theorem threeSphereWithNonzeroFirstToTwoSphereProdReal_fst_coe
    (z : ThreeSphereWithNonzeroFirst) :
    (threeSphereWithNonzeroFirstToTwoSphereProdReal z).1.1 =
      ‖(realProjectiveThreeSplit z.1.1).1‖⁻¹ •
        (realProjectiveThreeSplit z.1.1).1 := by
  simp [threeSphereWithNonzeroFirstToTwoSphereProdReal,
    threeSphereFirstNonzeroVector, homeomorphUnitSphereProd,
    homeomorphSphereProd]

private theorem threeSphereFirstNonzeroVector_continuous :
    Continuous threeSphereFirstNonzeroVector := by
  apply Continuous.subtype_mk
  exact continuous_fst.comp
    (realProjectiveThreeSplit.continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val))

private theorem threeSphereWithNonzeroFirstToTwoSphereProdReal_continuous :
    Continuous threeSphereWithNonzeroFirstToTwoSphereProdReal := by
  apply Continuous.prodMk
  · exact continuous_fst.comp
      ((homeomorphUnitSphereProd
        (EuclideanSpace Real (Fin 3))).continuous.comp
          threeSphereFirstNonzeroVector_continuous)
  · have hsplit : Continuous fun z : ThreeSphereWithNonzeroFirst =>
        realProjectiveThreeSplit z.1.1 :=
      realProjectiveThreeSplit.continuous.comp
        (continuous_subtype_val.comp continuous_subtype_val)
    have hfirst : Continuous fun z : ThreeSphereWithNonzeroFirst =>
        (realProjectiveThreeSplit z.1.1).1 :=
      continuous_fst.comp hsplit
    have hsecond : Continuous fun z : ThreeSphereWithNonzeroFirst =>
        (realProjectiveThreeSplit z.1.1).2 0 :=
      (PiLp.continuous_apply (p := 2)
        (β := fun _ : Fin 1 => Real) 0).comp
          (continuous_snd.comp hsplit)
    exact hsecond.div₀ hfirst.norm fun z =>
      norm_ne_zero_iff.mpr z.2

private theorem threeSphereWithNonzeroFirstToTwoSphereProdReal_left_inv
    (x : Metric.sphere
      (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    threeSphereWithNonzeroFirstToTwoSphereProdReal
      (twoSphereProdRealToThreeSphereWithNonzeroFirst x) = x := by
  have hvpos : 0 < ‖twoSphereProdRealVector x‖ :=
    norm_pos_iff.mpr (twoSphereProdRealVector_ne_zero x)
  let a : Real := ‖twoSphereProdRealVector x‖⁻¹
  have ha : 0 < a := inv_pos.mpr hvpos
  have hsplit :
      realProjectiveThreeSplit
          ((twoSphereProdRealToThreeSphereWithNonzeroFirst x).1.1) =
        (a • x.1.1, a • realProjectiveThreeScalarLine x.2) :=
    realProjectiveThreeSplit_twoSphereProdRealToThreeSphere x
  apply Prod.ext
  · apply Subtype.ext
    rw [threeSphereWithNonzeroFirstToTwoSphereProdReal_fst_coe,
      hsplit]
    change ‖a • (x.1.1 : EuclideanSpace Real (Fin 3))‖⁻¹ •
        a • (x.1.1 : EuclideanSpace Real (Fin 3)) = x.1.1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha,
      norm_eq_of_mem_sphere]
    simp [ha.ne']
  · change (realProjectiveThreeSplit
          ((twoSphereProdRealToThreeSphereWithNonzeroFirst x).1.1)).2 0 /
        ‖(realProjectiveThreeSplit
          ((twoSphereProdRealToThreeSphereWithNonzeroFirst x).1.1)).1‖ = x.2
    rw [hsplit]
    simp only [PiLp.smul_apply, smul_eq_mul,
      realProjectiveThreeScalarLine_apply, norm_smul,
      Real.norm_eq_abs, abs_of_pos ha, norm_eq_of_mem_sphere,
      mul_one]
    exact mul_div_cancel_left₀ x.2 ha.ne'

private theorem twoSphereProdRealToThreeSphereWithNonzeroFirst_right_inv
    (z : ThreeSphereWithNonzeroFirst) :
    twoSphereProdRealToThreeSphereWithNonzeroFirst
      (threeSphereWithNonzeroFirstToTwoSphereProdReal z) = z := by
  let u : EuclideanSpace Real (Fin 3) :=
    (realProjectiveThreeSplit z.1.1).1
  let w : EuclideanSpace Real (Fin 1) :=
    (realProjectiveThreeSplit z.1.1).2
  let b : Real := ‖u‖
  have hb : 0 < b := norm_pos_iff.mpr z.2
  have hvector : twoSphereProdRealVector
      (threeSphereWithNonzeroFirstToTwoSphereProdReal z) =
      b⁻¹ • z.1.1 := by
    apply realProjectiveThreeSplit.injective
    rw [twoSphereProdRealVector,
      realProjectiveThreeSplit.apply_symm_apply, map_smul]
    apply Prod.ext
    · rw [threeSphereWithNonzeroFirstToTwoSphereProdReal_fst_coe]
      rfl
    · change realProjectiveThreeScalarLine (w 0 / b) = b⁻¹ • w
      rw [div_eq_inv_mul, realProjectiveThreeScalarLine_smul,
        realProjectiveThreeScalarLine_ext]
  apply Subtype.ext
  apply Subtype.ext
  change (twoSphereProdRealToThreeSphere
    (threeSphereWithNonzeroFirstToTwoSphereProdReal z) :
      EuclideanSpace Real (Fin 4)) = z.1.1
  rw [twoSphereProdRealToThreeSphere_coe, hvector]
  change NormedSpace.normalize (b⁻¹ • z.1.1) = z.1.1
  rw [NormedSpace.normalize_smul_of_pos (inv_pos.mpr hb),
    NormedSpace.normalize_eq_self_of_norm_eq_one]
  exact norm_eq_of_mem_sphere z.1

private noncomputable def twoSphereProdRealHomeomorphCoordinateComplement :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real ≃ₜ
      ThreeSphereWithNonzeroFirst where
  toFun := twoSphereProdRealToThreeSphereWithNonzeroFirst
  invFun := threeSphereWithNonzeroFirstToTwoSphereProdReal
  left_inv := threeSphereWithNonzeroFirstToTwoSphereProdReal_left_inv
  right_inv := twoSphereProdRealToThreeSphereWithNonzeroFirst_right_inv
  continuous_toFun :=
    twoSphereProdRealToThreeSphereWithNonzeroFirst_continuous
  continuous_invFun :=
    threeSphereWithNonzeroFirstToTwoSphereProdReal_continuous

private noncomputable def realProjectiveThreeNorthVector :
    EuclideanSpace Real (Fin 4) :=
  realProjectiveThreeSplit.symm
    (0, realProjectiveThreeScalarLine 1)

private theorem realProjectiveThreeNorthVector_ne_zero :
    realProjectiveThreeNorthVector ≠ 0 := by
  intro h
  have hp := congrArg realProjectiveThreeSplit h
  change realProjectiveThreeSplit
      (realProjectiveThreeSplit.symm
        (0, realProjectiveThreeScalarLine 1)) =
    realProjectiveThreeSplit 0 at hp
  rw [realProjectiveThreeSplit.apply_symm_apply, map_zero] at hp
  have hsecond := congrArg Prod.snd hp
  have hone := congrArg
    (fun w : EuclideanSpace Real (Fin 1) => w 0) hsecond
  norm_num [realProjectiveThreeScalarLine_apply] at hone

private noncomputable def realProjectiveThreeNorthPole :
    Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1 :=
  ⟨NormedSpace.normalize realProjectiveThreeNorthVector, by
    rw [mem_sphere_zero_iff_norm]
    exact NormedSpace.norm_normalize
      realProjectiveThreeNorthVector_ne_zero⟩

private theorem realProjectiveThreeNorthPole_coe :
    (realProjectiveThreeNorthPole : EuclideanSpace Real (Fin 4)) =
      ‖realProjectiveThreeNorthVector‖⁻¹ •
        realProjectiveThreeNorthVector :=
  rfl

private theorem realProjectiveThreeSplit_northPole_fst :
    (realProjectiveThreeSplit
      (realProjectiveThreeNorthPole :
        EuclideanSpace Real (Fin 4))).1 = 0 := by
  rw [realProjectiveThreeNorthPole_coe, map_smul,
    realProjectiveThreeNorthVector,
    realProjectiveThreeSplit.apply_symm_apply, Prod.smul_mk]
  simp

private theorem eq_smul_realProjectiveThreeNorthVector_of_split_fst_eq_zero
    (z : Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1)
    (hz : (realProjectiveThreeSplit z.1).1 = 0) :
    z.1 = (realProjectiveThreeSplit z.1).2 0 •
      realProjectiveThreeNorthVector := by
  apply realProjectiveThreeSplit.injective
  rw [map_smul, realProjectiveThreeNorthVector,
    realProjectiveThreeSplit.apply_symm_apply, Prod.smul_mk]
  apply Prod.ext
  · simpa using hz
  · rw [← realProjectiveThreeScalarLine_smul, mul_one,
      realProjectiveThreeScalarLine_ext]

private theorem realProjectiveThreeSplit_fst_eq_zero_iff_eq_northPole_or_neg
    (z : Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1) :
    (realProjectiveThreeSplit z.1).1 = 0 ↔
      z = realProjectiveThreeNorthPole ∨
        z = -realProjectiveThreeNorthPole := by
  constructor
  · intro hz
    let a : Real := (realProjectiveThreeSplit z.1).2 0
    have hline : z.1 = a • realProjectiveThreeNorthVector :=
      eq_smul_realProjectiveThreeNorthVector_of_split_fst_eq_zero z hz
    have ha : a ≠ 0 := by
      intro ha
      rw [ha, zero_smul] at hline
      exact ne_zero_of_mem_unit_sphere z hline
    rcases lt_trichotomy a 0 with hneg | hzero | hpos
    · right
      apply Subtype.ext
      change z.1 = -(realProjectiveThreeNorthPole :
        EuclideanSpace Real (Fin 4))
      calc
        z.1 = NormedSpace.normalize z.1 :=
          (NormedSpace.normalize_eq_self_of_norm_eq_one
            (norm_eq_of_mem_sphere z)).symm
        _ = NormedSpace.normalize
            (a • realProjectiveThreeNorthVector) :=
          congrArg NormedSpace.normalize hline
        _ = -NormedSpace.normalize realProjectiveThreeNorthVector :=
          NormedSpace.normalize_smul_of_neg hneg _
        _ = -(realProjectiveThreeNorthPole :
            EuclideanSpace Real (Fin 4)) := rfl
    · exact (ha hzero).elim
    · left
      apply Subtype.ext
      calc
        z.1 = NormedSpace.normalize z.1 :=
          (NormedSpace.normalize_eq_self_of_norm_eq_one
            (norm_eq_of_mem_sphere z)).symm
        _ = NormedSpace.normalize
            (a • realProjectiveThreeNorthVector) :=
          congrArg NormedSpace.normalize hline
        _ = NormedSpace.normalize realProjectiveThreeNorthVector :=
          NormedSpace.normalize_smul_of_pos hpos _
        _ = (realProjectiveThreeNorthPole :
            EuclideanSpace Real (Fin 4)) := rfl
  · rintro (rfl | rfl)
    · exact realProjectiveThreeSplit_northPole_fst
    · change (realProjectiveThreeSplit
        (-(realProjectiveThreeNorthPole :
          EuclideanSpace Real (Fin 4)))).1 = 0
      rw [map_neg]
      simp [realProjectiveThreeSplit_northPole_fst]

def realProjectiveThreeSpacePuncture : RealProjectiveThreeSpace :=
  realProjectiveSpaceQuotientMap realProjectiveThreeNorthPole

abbrev PuncturedRealProjectiveThreeSpace :=
  {q : RealProjectiveThreeSpace // q ≠ realProjectiveThreeSpacePuncture}

noncomputable def threeSphereAwayFromRealProjectivePuncture :
    SubMulAction
      (realProjectiveSpaceAntipodalGroup
        (EuclideanSpace Real (Fin 4)))
      (Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1) where
  carrier := {z | realProjectiveSpaceQuotientMap z ≠
    realProjectiveThreeSpacePuncture}
  smul_mem' psi z hz := by
    intro hbad
    apply hz
    have hquot : realProjectiveSpaceQuotientMap (psi • z) =
        realProjectiveSpaceQuotientMap z := by
      apply Quotient.sound
      exact ⟨psi, rfl⟩
    exact hquot.symm.trans hbad

instance threeSphereAwayFromRealProjectivePunctureContinuousConstSMul :
    ContinuousConstSMul
      (realProjectiveSpaceAntipodalGroup
        (EuclideanSpace Real (Fin 4)))
      threeSphereAwayFromRealProjectivePuncture where
  continuous_const_smul psi :=
    ((continuous_const_smul psi).comp continuous_subtype_val).subtype_mk _

theorem isOpen_threeSphereAwayFromRealProjectivePuncture :
    IsOpen (threeSphereAwayFromRealProjectivePuncture :
      Set (Metric.sphere
        (0 : EuclideanSpace Real (Fin 4)) 1)) := by
  exact isOpen_compl_singleton.preimage
    realProjectiveSpaceQuotientMap_isOpenQuotientMap.continuous

private theorem mem_threeSphereAwayFromRealProjectivePuncture_iff_split_fst_ne_zero
    (z : Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1) :
    z ∈ threeSphereAwayFromRealProjectivePuncture ↔
      (realProjectiveThreeSplit z.1).1 ≠ 0 := by
  constructor
  · intro hz hzero
    apply hz
    rw [realProjectiveThreeSpacePuncture,
      realProjectiveSpaceQuotientMap_eq_iff]
    rw [realProjectiveThreeSplit_fst_eq_zero_iff_eq_northPole_or_neg]
      at hzero
    rcases hzero with hzero | hzero
    · exact Or.inl hzero
    · exact Or.inr (congrArg Subtype.val hzero)
  · intro hfirst hquot
    apply hfirst
    rw [realProjectiveThreeSplit_fst_eq_zero_iff_eq_northPole_or_neg]
    rw [realProjectiveThreeSpacePuncture,
      realProjectiveSpaceQuotientMap_eq_iff] at hquot
    rcases hquot with hquot | hquot
    · exact Or.inl hquot
    · exact Or.inr (Subtype.ext hquot)

private def realProjectivePuncturePreimageToCoordinateComplement
    (z : threeSphereAwayFromRealProjectivePuncture) :
    ThreeSphereWithNonzeroFirst :=
  ⟨z.1,
    (mem_threeSphereAwayFromRealProjectivePuncture_iff_split_fst_ne_zero
      z.1).mp z.2⟩

private theorem realProjectivePuncturePreimageToCoordinateComplement_continuous :
    Continuous realProjectivePuncturePreimageToCoordinateComplement :=
  continuous_subtype_val.subtype_mk _

noncomputable def twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real ≃ₜ
      threeSphereAwayFromRealProjectivePuncture where
  toFun x :=
    ⟨(twoSphereProdRealHomeomorphCoordinateComplement x).1,
      (mem_threeSphereAwayFromRealProjectivePuncture_iff_split_fst_ne_zero
        _).mpr (twoSphereProdRealHomeomorphCoordinateComplement x).2⟩
  invFun z := twoSphereProdRealHomeomorphCoordinateComplement.symm
    (realProjectivePuncturePreimageToCoordinateComplement z)
  left_inv x := twoSphereProdRealHomeomorphCoordinateComplement.left_inv x
  right_inv z := by
    apply Subtype.ext
    change (twoSphereProdRealHomeomorphCoordinateComplement
      (twoSphereProdRealHomeomorphCoordinateComplement.symm
        (realProjectivePuncturePreimageToCoordinateComplement z))).1 = z.1
    exact congrArg Subtype.val
      (twoSphereProdRealHomeomorphCoordinateComplement.right_inv
        (realProjectivePuncturePreimageToCoordinateComplement z))
  continuous_toFun :=
    (continuous_subtype_val.comp
      twoSphereProdRealHomeomorphCoordinateComplement.continuous).subtype_mk _
  continuous_invFun :=
    twoSphereProdRealHomeomorphCoordinateComplement.symm.continuous.comp
      realProjectivePuncturePreimageToCoordinateComplement_continuous

theorem twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture_diagonal
    (x : Metric.sphere
      (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    ((twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture
      (-x.1, -x.2) : threeSphereAwayFromRealProjectivePuncture) :
        Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1) =
      -((twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture
        x : threeSphereAwayFromRealProjectivePuncture) :
          Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1) :=
  twoSphereProdRealToThreeSphere_neg x

abbrev ThreeSphereAwayFromRealProjectivePunctureQuotient :=
  MulAction.orbitRel.Quotient
    (realProjectiveSpaceAntipodalGroup
      (EuclideanSpace Real (Fin 4)))
    threeSphereAwayFromRealProjectivePuncture

def threeSphereAwayFromRealProjectivePunctureQuotientMap
    (z : threeSphereAwayFromRealProjectivePuncture) :
    ThreeSphereAwayFromRealProjectivePunctureQuotient :=
  Quotient.mk'' z

private def threeSphereAwayFromRealProjectivePunctureToPuncturedSpace
    (z : threeSphereAwayFromRealProjectivePuncture) :
    PuncturedRealProjectiveThreeSpace :=
  ⟨realProjectiveSpaceQuotientMap z.1, z.2⟩

private theorem threeSphereAwayFromRealProjectivePunctureToPuncturedSpace_respects
    {x y : threeSphereAwayFromRealProjectivePuncture}
    (hxy : MulAction.orbitRel
      (realProjectiveSpaceAntipodalGroup
        (EuclideanSpace Real (Fin 4)))
      threeSphereAwayFromRealProjectivePuncture x y) :
    threeSphereAwayFromRealProjectivePunctureToPuncturedSpace x =
      threeSphereAwayFromRealProjectivePunctureToPuncturedSpace y := by
  apply Subtype.ext
  apply Quotient.sound
  rw [SubMulAction.orbitRel_of_subMul] at hxy
  exact hxy

private def threeSphereAwayFromRealProjectivePunctureQuotientToPuncturedSpace :
    ThreeSphereAwayFromRealProjectivePunctureQuotient →
      PuncturedRealProjectiveThreeSpace :=
  Quotient.lift
    threeSphereAwayFromRealProjectivePunctureToPuncturedSpace
    (fun _ _ hxy =>
      threeSphereAwayFromRealProjectivePunctureToPuncturedSpace_respects hxy)

private theorem threeSphereAwayFromRealProjectivePunctureQuotientToPuncturedSpace_continuous :
    Continuous
      threeSphereAwayFromRealProjectivePunctureQuotientToPuncturedSpace := by
  apply Continuous.quotient_lift
  exact (realProjectiveSpaceQuotientMap_isOpenQuotientMap.continuous.comp
    continuous_subtype_val).subtype_mk _

private theorem threeSphereAwayFromRealProjectivePunctureQuotientToPuncturedSpace_bijective :
    Function.Bijective
      threeSphereAwayFromRealProjectivePunctureQuotientToPuncturedSpace := by
  constructor
  · intro q r hqr
    induction q using Quotient.inductionOn with
    | _ x =>
      induction r using Quotient.inductionOn with
      | _ y =>
        apply Quotient.sound
        change threeSphereAwayFromRealProjectivePunctureToPuncturedSpace x =
          threeSphereAwayFromRealProjectivePunctureToPuncturedSpace y at hqr
        have hquot := congrArg Subtype.val hqr
        change realProjectiveSpaceQuotientMap x.1 =
          realProjectiveSpaceQuotientMap y.1 at hquot
        have hfull : MulAction.orbitRel
            (realProjectiveSpaceAntipodalGroup
              (EuclideanSpace Real (Fin 4)))
            (Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1)
            x.1 y.1 :=
          Quotient.exact hquot
        rw [SubMulAction.orbitRel_of_subMul]
        exact hfull
  · rintro ⟨q, hq⟩
    refine Quotient.inductionOn q ?_ hq
    intro z hz
    let z' : threeSphereAwayFromRealProjectivePuncture := ⟨z, hz⟩
    refine ⟨threeSphereAwayFromRealProjectivePunctureQuotientMap z', ?_⟩
    apply Subtype.ext
    rfl

private theorem threeSphereAwayFromRealProjectivePunctureToPuncturedSpace_isOpenMap :
    IsOpenMap
      threeSphereAwayFromRealProjectivePunctureToPuncturedSpace := by
  have hopen : IsOpenMap
      (fun z : threeSphereAwayFromRealProjectivePuncture =>
        realProjectiveSpaceQuotientMap z.1) :=
    realProjectiveSpaceQuotientMap_isOpenQuotientMap.isOpenMap.comp
      isOpen_threeSphereAwayFromRealProjectivePuncture.isOpenMap_subtype_val
  exact hopen.codRestrict _

private theorem threeSphereAwayFromRealProjectivePunctureQuotientToPuncturedSpace_isOpenMap :
    IsOpenMap
      threeSphereAwayFromRealProjectivePunctureQuotientToPuncturedSpace := by
  apply IsOpenMap.of_comp
    (MulAction.isOpenQuotientMap_quotientMk
      (Γ := realProjectiveSpaceAntipodalGroup
        (EuclideanSpace Real (Fin 4)))
      (T := threeSphereAwayFromRealProjectivePuncture)).continuous
    (MulAction.isOpenQuotientMap_quotientMk
      (Γ := realProjectiveSpaceAntipodalGroup
        (EuclideanSpace Real (Fin 4)))
      (T := threeSphereAwayFromRealProjectivePuncture)).surjective
  simpa [Function.comp_def,
    threeSphereAwayFromRealProjectivePunctureQuotientToPuncturedSpace] using
      threeSphereAwayFromRealProjectivePunctureToPuncturedSpace_isOpenMap

noncomputable def threeSphereAwayFromRealProjectivePunctureQuotientHomeomorph :
    ThreeSphereAwayFromRealProjectivePunctureQuotient ≃ₜ
      PuncturedRealProjectiveThreeSpace :=
  (Equiv.ofBijective
    threeSphereAwayFromRealProjectivePunctureQuotientToPuncturedSpace
    threeSphereAwayFromRealProjectivePunctureQuotientToPuncturedSpace_bijective).toHomeomorphOfContinuousOpen
      threeSphereAwayFromRealProjectivePunctureQuotientToPuncturedSpace_continuous
      threeSphereAwayFromRealProjectivePunctureQuotientToPuncturedSpace_isOpenMap

theorem threeSphereAwayFromRealProjectivePunctureQuotientHomeomorph_apply
    (z : threeSphereAwayFromRealProjectivePuncture) :
    threeSphereAwayFromRealProjectivePunctureQuotientHomeomorph
        (threeSphereAwayFromRealProjectivePunctureQuotientMap z) =
      ⟨realProjectiveSpaceQuotientMap z.1, z.2⟩ :=
  rfl

end DifferentialGeometry
