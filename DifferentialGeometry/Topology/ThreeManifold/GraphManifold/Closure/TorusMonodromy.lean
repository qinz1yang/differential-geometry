import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PlanarModels
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FibreCoordinate
import DifferentialGeometry.Topology.Manifold.Interval.Tangent
import Mathlib.Topology.UnitInterval

/-!
# Actual interval and annulus gluing for torus monodromy
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

def monodromyIntervalEnd (a : unitInterval) : Set (Torus × unitInterval) :=
  {p | p.2 = a}

def monodromyIntervalEndParam (a : unitInterval) :
    Torus ≃ₜ monodromyIntervalEnd a where
  toFun t := ⟨(t, a), rfl⟩
  invFun p := p.val.1
  left_inv := fun t => show t = t from rfl
  right_inv p := Subtype.ext (Prod.ext rfl p.property.symm)
  continuous_toFun := (continuous_id.prodMk continuous_const).subtype_mk
    fun t => show (t, a).2 = a from rfl
  continuous_invFun := continuous_fst.comp continuous_subtype_val

def monodromyIntervalGluing
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    BoundaryGluing (Torus × unitInterval) (Fin 1) where
  left i := monodromyIntervalEnd 1
  right i := monodromyIntervalEnd 0
  attaching i := ((monodromyIntervalEndParam 1).symm.trans f.toHomeomorph).trans
    (monodromyIntervalEndParam 0)
  isClosed_left i := isClosed_eq continuous_snd continuous_const
  isClosed_right i := isClosed_eq continuous_snd continuous_const
  disjoint_left_right i := by
    rw [Set.disjoint_left]
    intro p hp hq
    have h := congrArg Subtype.val (hp.symm.trans hq)
    norm_num at h
  disjoint_blocks i j hij := False.elim (hij (Subsingleton.elim i j))

theorem monodromyIntervalGluing_attaching
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) (i : Fin 1) (t : Torus) :
    (monodromyIntervalGluing f).attaching i (monodromyIntervalEndParam 1 t) =
      monodromyIntervalEndParam 0 (f t) := rfl

theorem torusMonodromyNormBounds (x : (productSet.{u} 2)) :
    (1 / 2 : ℝ) ≤ ‖x.val.1.down‖ ∧ ‖x.val.1.down‖ ≤ 3 := by
  exact ((mem_planarModel_two x.val.1.down).mp
    ((mem_planarSet_iff (Or.inl rfl) x.val.1).mp x.property)).symm

def torusMonodromyPolarForward (x : (productSet.{u} 2)) :
    Torus × unitInterval :=
  ((unitOf x.val.1.down, x.val.2), ⟨(3 - ‖x.val.1.down‖) / (5 / 2), by
    have hx := torusMonodromyNormBounds x
    constructor <;> linarith⟩)

def torusMonodromyPolarInverse (p : Torus × unitInterval) :
    (productSet.{u} 2) :=
  ⟨(ULift.up ((3 - (5 / 2) * p.2.val) • (p.1.1 : ℂ)), p.1.2), by
    apply (mem_planarSet_iff (Or.inl rfl) _).mpr
    apply (mem_planarModel_two _).mpr
    have hpos : 0 ≤ 3 - (5 / 2) * p.2.val := by linarith [p.2.property.2]
    rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg hpos]
    constructor <;> linarith [p.2.property.1, p.2.property.2]⟩

theorem torusMonodromyPolarInverse_forward (x : (productSet.{u} 2)) :
    torusMonodromyPolarInverse (torusMonodromyPolarForward x) = x := by
  apply Subtype.ext
  apply Prod.ext
  · apply ULift.ext
    change (3 - (5 / 2) * ((3 - ‖x.val.1.down‖) / (5 / 2))) •
      (unitOf x.val.1.down : ℂ) = x.val.1.down
    rw [show 3 - (5 / 2) * ((3 - ‖x.val.1.down‖) / (5 / 2)) =
      ‖x.val.1.down‖ by ring, norm_smul_unitOf]
  · rfl

theorem torusMonodromyPolarForward_inverse (p : Torus × unitInterval) :
    torusMonodromyPolarForward (torusMonodromyPolarInverse p) = p := by
  have hp : 0 < 3 - (5 / 2) * p.2.val := by linarith [p.2.property.2]
  apply Prod.ext
  · apply Prod.ext
    · exact unitOf_smul hp p.1.1
    · rfl
  · apply Subtype.ext
    change (3 - ‖(3 - (5 / 2) * p.2.val) • (p.1.1 : ℂ)‖) / (5 / 2) = p.2.val
    rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg hp.le]
    ring

theorem torusMonodromyPolarForward_continuous :
    Continuous torusMonodromyPolarForward.{u} := by
  have hz : Continuous (fun x : (productSet.{u} 2) => x.val.1.down) :=
    contMDiff_planeLift_down.continuous.comp (continuous_fst.comp continuous_subtype_val)
  have hu : Continuous (fun x : (productSet.{u} 2) =>
      unitOf x.val.1.down) := by
    apply contMDiffOn_unitOf.continuousOn.comp_continuous hz
    intro x
    change x.val.1.down ≠ 0
    have hx := torusMonodromyNormBounds x
    exact norm_pos_iff.mp (by linarith)
  have ht : Continuous (fun x : (productSet.{u} 2) => x.val.2) :=
    continuous_snd.comp continuous_subtype_val
  exact (hu.prodMk ht).prodMk
    (((continuous_const.sub hz.norm).div_const (5 / 2)).subtype_mk fun x =>
      (torusMonodromyPolarForward x).2.property)

theorem torusMonodromyPolarInverse_continuous :
    Continuous torusMonodromyPolarInverse.{u} := by
  have ht : Continuous (fun p : Torus × unitInterval => (p.1.1 : ℂ)) :=
    contMDiff_circle_coe.continuous.comp (continuous_fst.comp continuous_fst)
  have hs : Continuous (fun p : Torus × unitInterval => p.2.val) :=
    continuous_subtype_val.comp continuous_snd
  exact ((contMDiff_planeLift_up.continuous.comp ((continuous_const.sub
    (continuous_const.mul hs)).smul ht)).prodMk
      (continuous_snd.comp continuous_fst)).subtype_mk fun p =>
        (torusMonodromyPolarInverse p).property

def torusMonodromyPolar : (productSet.{u} 2) ≃ₜ Torus × unitInterval where
  toFun := torusMonodromyPolarForward
  invFun := torusMonodromyPolarInverse
  left_inv := torusMonodromyPolarInverse_forward
  right_inv := torusMonodromyPolarForward_inverse
  continuous_toFun := torusMonodromyPolarForward_continuous
  continuous_invFun := torusMonodromyPolarInverse_continuous

def torusMonodromyEnd (a : unitInterval) : Set (productSet.{u} 2) :=
  torusMonodromyPolar ⁻¹' monodromyIntervalEnd a

def torusMonodromyEndHomeomorph (a : unitInterval) :
    torusMonodromyEnd.{u} a ≃ₜ monodromyIntervalEnd a where
  toFun x := ⟨torusMonodromyPolar x.val, x.property⟩
  invFun y := ⟨torusMonodromyPolar.symm y.val, by
    change torusMonodromyPolar (torusMonodromyPolar.symm y.val) ∈ monodromyIntervalEnd a
    rw [Homeomorph.apply_symm_apply]
    exact y.property⟩
  left_inv x := Subtype.ext (Homeomorph.symm_apply_apply torusMonodromyPolar x.val)
  right_inv y := Subtype.ext (Homeomorph.apply_symm_apply torusMonodromyPolar y.val)
  continuous_toFun := (torusMonodromyPolar.continuous.comp continuous_subtype_val).subtype_mk
    fun x => x.property
  continuous_invFun :=
    (torusMonodromyPolar.symm.continuous.comp continuous_subtype_val).subtype_mk
      fun y => (by
        change torusMonodromyPolar (torusMonodromyPolar.symm y.val) ∈ monodromyIntervalEnd a
        rw [Homeomorph.apply_symm_apply]
        exact y.property)

def torusMonodromyEndParam (a : unitInterval) : Torus ≃ₜ torusMonodromyEnd.{u} a :=
  (monodromyIntervalEndParam a).trans (torusMonodromyEndHomeomorph a).symm

def torusMonodromyGluing
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    BoundaryGluing (productSet.{u} 2) (Fin 1) where
  left := Function.const (Fin 1) (torusMonodromyEnd 1)
  right := Function.const (Fin 1) (torusMonodromyEnd 0)
  attaching i := ((torusMonodromyEndHomeomorph 1).trans
    ((monodromyIntervalGluing f).attaching i)).trans (torusMonodromyEndHomeomorph 0).symm
  isClosed_left i :=
    ((monodromyIntervalGluing f).isClosed_left i).preimage torusMonodromyPolar.continuous
  isClosed_right i :=
    ((monodromyIntervalGluing f).isClosed_right i).preimage torusMonodromyPolar.continuous
  disjoint_left_right i := ((monodromyIntervalGluing f).disjoint_left_right i).preimage
    torusMonodromyPolar
  disjoint_blocks i j hij := False.elim (hij (Subsingleton.elim i j))

theorem torusMonodromyGluing_attaching
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) (i : Fin 1) (t : Torus) :
    (torusMonodromyGluing f).attaching i (torusMonodromyEndParam 1 t) =
      torusMonodromyEndParam 0 (f t) := by
  apply Subtype.ext
  change torusMonodromyPolar.symm
    (((monodromyIntervalGluing f).attaching i
      ((torusMonodromyEndHomeomorph 1) ((torusMonodromyEndHomeomorph 1).symm
        (monodromyIntervalEndParam 1 t)))).val) = _
  rw [Homeomorph.apply_symm_apply]
  rfl

theorem torusMonodromyGluing_flip
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) (i : Fin 1)
    (x : (productSet.{u} 2)) :
    torusMonodromyPolar ((torusMonodromyGluing f).flip i x) =
      (monodromyIntervalGluing f).flip i (torusMonodromyPolar x) := by
  by_cases hL : x ∈ (torusMonodromyGluing f).left i
  · rw [(torusMonodromyGluing f).flip_of_mem_left hL,
      (monodromyIntervalGluing f).flip_of_mem_left (show torusMonodromyPolar x ∈
        (monodromyIntervalGluing f).left i from hL)]
    exact Homeomorph.apply_symm_apply torusMonodromyPolar _
  · by_cases hR : x ∈ (torusMonodromyGluing f).right i
    · rw [(torusMonodromyGluing f).flip_of_mem_right hR,
        (monodromyIntervalGluing f).flip_of_mem_right (show torusMonodromyPolar x ∈
          (monodromyIntervalGluing f).right i from hR)]
      exact Homeomorph.apply_symm_apply torusMonodromyPolar _
    · rw [(torusMonodromyGluing f).flip_of_notMem (not_or.mpr ⟨hL, hR⟩),
        (monodromyIntervalGluing f).flip_of_notMem (not_or.mpr ⟨hL, hR⟩)]

theorem torusMonodromyGluing_rel_iff
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (x y : (productSet.{u} 2)) :
    (torusMonodromyGluing f).rel x y ↔
      (monodromyIntervalGluing f).rel (torusMonodromyPolar x) (torusMonodromyPolar y) := by
  constructor
  · rintro (rfl | ⟨i, hx, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨i, hx, torusMonodromyGluing_flip f i x⟩
  · rintro (he | ⟨i, hx, he⟩)
    · exact Or.inl (torusMonodromyPolar.injective he)
    · exact Or.inr ⟨i, hx, torusMonodromyPolar.injective
        (he.trans (torusMonodromyGluing_flip f i x).symm)⟩

def torusMonodromyQuotientHomeomorph
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    Quotient (torusMonodromyGluing.{u} f).setoid ≃ₜ
      Quotient (monodromyIntervalGluing f).setoid :=
  (torusMonodromyGluing f).congrHomeomorph (monodromyIntervalGluing f)
    torusMonodromyPolar (torusMonodromyGluing_rel_iff f)

theorem torusMonodromyQuotientHomeomorph_apply
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (x : (productSet.{u} 2)) :
    torusMonodromyQuotientHomeomorph f (Quotient.mk'' x) =
      Quotient.mk'' (torusMonodromyPolar x) := rfl

def torusMonodromyTwist : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus where
  toFun t := (t.1⁻¹, t.2)
  invFun t := (t.1⁻¹, t.2)
  left_inv t := by simp
  right_inv t := by simp
  contMDiff_toFun := ((contMDiff_inv (𝓡 1) ∞).comp contMDiff_fst).prodMk contMDiff_snd
  contMDiff_invFun := ((contMDiff_inv (𝓡 1) ∞).comp contMDiff_fst).prodMk contMDiff_snd

def torusMonodromyOuterCollar :
    PartialDiffeomorph halfCollarModel (𝓡∂ 3)
      (Torus × EuclideanHalfSpace 1) (productSet.{u} 2) ∞ :=
  productCollar 2 (Or.inl rfl) 0

def torusMonodromyInnerCollar :
    PartialDiffeomorph halfCollarModel (𝓡∂ 3)
      (Torus × EuclideanHalfSpace 1) (productSet.{u} 2) ∞ :=
  (torusMonodromyTwist.prodCongr
    (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)).toPartialDiffeomorph.trans
      (productCollar 2 (Or.inl rfl) 1)

theorem torusMonodromyOuterCollar_source :
    torusMonodromyOuterCollar.{u}.source = halfCollarSource := rfl

theorem torusMonodromyInnerCollar_source :
    torusMonodromyInnerCollar.{u}.source = halfCollarSource := by
  ext p
  change (p ∈ univ ∧
    (torusMonodromyTwist p.1, p.2) ∈ (productCollar.{u} 2 (Or.inl rfl) 1).source) ↔ _
  simp only [mem_univ, true_and]
  rfl

theorem torusMonodromyOuterCollar_down {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) :
    (torusMonodromyOuterCollar.{u} p).val.1.down =
      (3 - p.2.val 0 / 4) • (p.1.1 : ℂ) := by
  change (planarCollar.{u} 2 (Or.inl rfl) 0 (p.1.1, p.2)).val.down = _
  rw [planarCollar_apply_val (Or.inl rfl) 0 hp]
  simp [planarCollarFormula, planarCenter, planarRadius, planarSign, planarTwist]
  ring

theorem torusMonodromyInnerCollar_down {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) :
    (torusMonodromyInnerCollar.{u} p).val.1.down =
      (1 / 2 + p.2.val 0 / 4) • (p.1.1 : ℂ) := by
  change (planarCollar.{u} 2 (Or.inl rfl) 1 (p.1.1⁻¹, p.2)).val.down = _
  rw [planarCollar_apply_val (Or.inl rfl) 1 hp]
  simp only [planarCollarFormula, planarCenter, planarRadius, planarSign, planarTwist,
    Fin.val_one, one_ne_zero, ↓reduceIte, Complex.ofReal_zero, zero_add,
    one_mul, Circle.coe_inv_eq_conj, Complex.conj_conj]

theorem torusMonodromyOuterCollar_zero (t : Torus) :
    torusMonodromyOuterCollar.{u} (t, halfZero) =
      (torusMonodromyEndParam 0 t).val := by
  apply Subtype.ext
  apply Prod.ext
  · apply ULift.ext
    rw [torusMonodromyOuterCollar_down (p := (t, halfZero))
      (by change (0 : ℝ) < 1; norm_num)]
    change (3 - (0 : ℝ) / 4) • (t.1 : ℂ) =
      (3 - (5 / 2) * (0 : ℝ)) • (t.1 : ℂ)
    norm_num
  · rfl

theorem torusMonodromyInnerCollar_zero (t : Torus) :
    torusMonodromyInnerCollar.{u} (t, halfZero) =
      (torusMonodromyEndParam 1 t).val := by
  apply Subtype.ext
  apply Prod.ext
  · apply ULift.ext
    rw [torusMonodromyInnerCollar_down (p := (t, halfZero))
      (by change (0 : ℝ) < 1; norm_num)]
    change (1 / 2 + (0 : ℝ) / 4) • (t.1 : ℂ) =
      (3 - (5 / 2) * (1 : ℝ)) • (t.1 : ℂ)
    norm_num
  · rfl

theorem torusMonodromyGluing_boundary
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    (𝓡∂ 3).boundary (productSet.{u} 2) =
      ⋃ i, (torusMonodromyGluing.{u} f).block i := by
  change (𝓡∂ 3).boundary (productSet.{u} 2) =
    ⋃ i : Fin 1, (torusMonodromyEnd.{u} 1 ∪ torusMonodromyEnd.{u} 0)
  ext x
  change (𝓡∂ 3).IsBoundaryPoint x ↔ _
  simp only [Set.mem_iUnion, Fin.exists_fin_one]
  change (𝓡∂ 3).IsBoundaryPoint (x : productSet.{u} 2) ↔
    (torusMonodromyPolar x).2 = 1 ∨ (torusMonodromyPolar x).2 = 0
  rw [productSet_isBoundaryPoint_iff, planarFunction_eq_zero_iff (Or.inl rfl),
    Fin.exists_fin_two]
  simp only [planarCenter, planarRadius, Fin.val_zero, Fin.val_one, ↓reduceIte,
    one_ne_zero, Complex.ofReal_zero, sub_zero]
  constructor
  · rintro (h | h)
    · exact Or.inr (Subtype.ext (by change (3 - ‖x.val.1.down‖) / (5 / 2) = 0; rw [h]; ring))
    · exact Or.inl (Subtype.ext (by change (3 - ‖x.val.1.down‖) / (5 / 2) = 1; rw [h]; ring))
  · rintro (h | h)
    · have hh := congrArg Subtype.val h
      change (3 - ‖x.val.1.down‖) / (5 / 2) = 1 at hh
      exact Or.inr (by linarith)
    · have hh := congrArg Subtype.val h
      change (3 - ‖x.val.1.down‖) / (5 / 2) = 0 at hh
      exact Or.inl (by linarith)

abbrev torusMonodromyCylinderModel := torusModel.prod (𝓡∂ 1)

theorem torusMonodromyPolarForward_smooth :
    ContMDiff (𝓡∂ 3) torusMonodromyCylinderModel ∞ torusMonodromyPolarForward.{u} := by
  have hz : ContMDiff (𝓡∂ 3) 𝓘(ℝ, ℂ) ∞
      (fun x : productSet.{u} 2 => x.val.1.down) :=
    contMDiff_planeLift_down.comp
      (contMDiff_fst.comp (productAtlas 2).contMDiff_subtype_val)
  have hn : ContMDiff (𝓡∂ 3) 𝓘(ℝ, ℝ) ∞
      (fun x : productSet.{u} 2 => ‖x.val.1.down‖) := by
    intro x
    have hne : x.val.1.down ≠ 0 := norm_pos_iff.mp
      (by linarith [(torusMonodromyNormBounds x).1])
    exact (contDiffAt_norm ℝ hne).contMDiffAt.comp x hz.contMDiffAt
  have hu := contMDiffOn_unitOf.comp_contMDiff hz fun x =>
    norm_pos_iff.mp (by linarith [(torusMonodromyNormBounds x).1])
  refine (hu.prodMk (contMDiff_snd.comp (productAtlas 2).contMDiff_subtype_val)).prodMk ?_
  apply contMDiff_iff_comp_subtypeVal_Icc.mpr
  exact ⟨continuous_snd.comp torusMonodromyPolarForward_continuous,
    (contMDiff_const.sub hn).div_const (5 / 2)⟩

theorem torusMonodromyPolarInverse_smooth :
    ContMDiff torusMonodromyCylinderModel (𝓡∂ 3) ∞ torusMonodromyPolarInverse.{u} := by
  apply ((productAtlas 2).contMDiff_iff_subtype_val _).mpr
  have hs : ContMDiff torusMonodromyCylinderModel 𝓘(ℝ, ℝ) ∞
      (fun p : Torus × unitInterval => 3 - (5 / 2) * p.2.val) :=
    contMDiff_const.sub (contMDiff_const.mul (contMDiff_subtypeVal_Icc.comp contMDiff_snd))
  exact (contMDiff_planeLift_up.comp
    (hs.smul (contMDiff_circle_coe.comp (contMDiff_fst.comp contMDiff_fst)))).prodMk
      (contMDiff_snd.comp contMDiff_fst)

def torusMonodromyPolarDiffeomorph :
    (productSet.{u} 2) ≃ₘ⟮𝓡∂ 3, torusMonodromyCylinderModel⟯ (Torus × unitInterval) where
  toEquiv := torusMonodromyPolar.toEquiv
  contMDiff_toFun := torusMonodromyPolarForward_smooth
  contMDiff_invFun := torusMonodromyPolarInverse_smooth

def torusMonodromyIntervalReflection : unitInterval ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ unitInterval where
  toFun s := ⟨1 - s.val, by constructor <;> linarith [s.property.1, s.property.2]⟩
  invFun s := ⟨1 - s.val, by constructor <;> linarith [s.property.1, s.property.2]⟩
  left_inv s := Subtype.ext (by dsimp; ring)
  right_inv s := Subtype.ext (by dsimp; ring)
  contMDiff_toFun := contMDiff_iff_comp_subtypeVal_Icc.mpr
    ⟨(continuous_const.sub continuous_subtype_val).subtype_mk fun s =>
      by
        dsimp
        constructor <;> linarith [s.property.1, s.property.2],
      contMDiff_const.sub contMDiff_subtypeVal_Icc⟩
  contMDiff_invFun := contMDiff_iff_comp_subtypeVal_Icc.mpr
    ⟨(continuous_const.sub continuous_subtype_val).subtype_mk fun s =>
      by
        dsimp
        constructor <;> linarith [s.property.1, s.property.2],
      contMDiff_const.sub contMDiff_subtypeVal_Icc⟩

theorem exists_torusMonodromyIntervalOrientation :
    ∃ O : ManifoldOrientation (𝓡∂ 1) unitInterval 1,
      ∀ s, Orientation.map (Fin 1)
        (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc s).toLinearEquiv
        (O.orientation s) = realLineOrientation.orientation s.val := by
  have hb : ∀ s : unitInterval,
      Bijective (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : unitInterval → ℝ) s) := by
    intro s
    exact (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc s).bijective
  obtain ⟨O, hO⟩ := Manifold.exists_manifoldOrientation_pullback (𝓡∂ 1) 𝓘(ℝ, ℝ)
    (by simp) (Subtype.val : unitInterval → ℝ) contMDiff_subtypeVal_Icc hb realLineOrientation
  refine ⟨O, fun s => ?_⟩
  have he : (Manifold.differentialEquivOfBijective (𝓡∂ 1) 𝓘(ℝ, ℝ)
      (Subtype.val : unitInterval → ℝ) hb s).toLinearEquiv =
      (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc s).toLinearEquiv := by
    ext v
    rfl
  rw [← he]
  exact hO s

theorem torusMonodromyCylinderPositive
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (hf : f.preservesOrientation productTorusOrientation productTorusOrientation)
    (O : ManifoldOrientation torusMonodromyCylinderModel (Torus × unitInterval) 3) :
    (f.prodCongr (Diffeomorph.refl (𝓡∂ 1) unitInterval ∞)).preservesOrientation O O := by
  obtain ⟨OI, hOI⟩ := exists_torusMonodromyIntervalOrientation
  let R := productOrientation torusModel (𝓡∂ 1) (by norm_num) le_rfl
    productTorusOrientation OI
  have hR : (f.prodCongr (Diffeomorph.refl (𝓡∂ 1) unitInterval ∞)).preservesOrientation
      R R := Diffeomorph.prodCongr_preservesOrientation (by norm_num) le_rfl f
        (Diffeomorph.refl (𝓡∂ 1) unitInterval ∞) hf (Diffeomorph.preservesOrientation_refl OI)
  let p : Torus × unitInterval := ((1, 1), 0)
  have hc : Fintype.card (Fin 3) =
      Module.finrank ℝ (TangentSpace torusMonodromyCylinderModel p) := by
    change Fintype.card (Fin 3) = Module.finrank ℝ
      ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1))
    simp
  rcases Orientation.eq_or_eq_neg (O.orientation p) (R.orientation p) hc with hp | hp
  · have he : O = R := ManifoldOrientation.eq_of_eq_at O R p hp
    rw [he]
    exact hR
  · have he : O = R.opposite := ManifoldOrientation.eq_of_eq_at O R.opposite p hp
    rw [he]
    exact Diffeomorph.preservesOrientation_opposite hR

theorem torusMonodromyIntervalReflection_tangent (s : unitInterval)
    (v : TangentSpace (𝓡∂ 1) s) :
    DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc
        (torusMonodromyIntervalReflection s)
        (mfderiv (𝓡∂ 1) (𝓡∂ 1) torusMonodromyIntervalReflection s v) =
      -DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc s v := by
  change mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : unitInterval → ℝ)
      (torusMonodromyIntervalReflection s)
      (mfderiv (𝓡∂ 1) (𝓡∂ 1) torusMonodromyIntervalReflection s v) =
    -(mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : unitInterval → ℝ) s v)
  rw [← mfderiv_comp_apply s
    ((contMDiff_subtypeVal_Icc (n := ∞)).mdifferentiableAt (by simp))
    (torusMonodromyIntervalReflection.contMDiff.mdifferentiableAt (by simp))]
  change mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ)
    (fun y : unitInterval => 1 - y.val) s v = _
  erw [mfderiv_sub mdifferentiableAt_const
    ((contMDiff_subtypeVal_Icc (n := ∞)).mdifferentiableAt (by simp)), mfderiv_const]
  erw [zero_sub]
  rfl

def torusMonodromyMidpoint : unitInterval := ⟨1 / 2, by norm_num⟩

theorem torusMonodromyIntervalReflection_midpoint :
    torusMonodromyIntervalReflection torusMonodromyMidpoint = torusMonodromyMidpoint := by
  apply Subtype.ext
  change 1 - (1 / 2 : ℝ) = 1 / 2
  norm_num

theorem torusMonodromyIntervalReflection_midpoint_derivative :
    mfderiv (𝓡∂ 1) (𝓡∂ 1) torusMonodromyIntervalReflection torusMonodromyMidpoint =
      -ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)) := by
  ext v
  apply (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc
    torusMonodromyMidpoint).injective
  have h := torusMonodromyIntervalReflection_tangent torusMonodromyMidpoint v
  rw [torusMonodromyIntervalReflection_midpoint] at h
  change DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc
      torusMonodromyMidpoint
      (mfderiv (𝓡∂ 1) (𝓡∂ 1) torusMonodromyIntervalReflection
        torusMonodromyMidpoint v) =
    DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc torusMonodromyMidpoint (-v)
  rw [map_neg]
  exact h

def torusMonodromyCylinderReflection :
    (Torus × unitInterval) ≃ₘ⟮torusMonodromyCylinderModel,
      torusMonodromyCylinderModel⟯ (Torus × unitInterval) :=
  (Diffeomorph.refl torusModel Torus ∞).prodCongr torusMonodromyIntervalReflection

def torusMonodromyNormalReflection :
    ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
      EuclideanSpace ℝ (Fin 1)) ≃ₗ[ℝ]
    ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
      EuclideanSpace ℝ (Fin 1)) :=
  (LinearEquiv.refl ℝ _).prodCongr (LinearEquiv.neg ℝ)

theorem torusMonodromyNormalReflection_map
    (o : Orientation ℝ
      ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
        EuclideanSpace ℝ (Fin 1)) (Fin 3)) :
    Orientation.map (Fin 3) torusMonodromyNormalReflection o = -o := by
  apply (Orientation.map_eq_neg_iff_det_neg o torusMonodromyNormalReflection (by simp)).mpr
  have he : torusMonodromyNormalReflection.toLinearMap =
      (LinearMap.id : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) →ₗ[ℝ] _).prodMap
        (-LinearMap.id : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1)) := by
    apply LinearMap.ext
    intro v
    rfl
  rw [he, LinearMap.det_prodMap, LinearMap.det_id]
  rw [show (-LinearMap.id : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] _) =
    (-1 : ℝ) • LinearMap.id by simp]
  rw [LinearMap.det_smul, LinearMap.det_id]
  norm_num

theorem torusMonodromyCylinderReflection_reversing
    (O : ManifoldOrientation torusMonodromyCylinderModel (Torus × unitInterval) 3) :
    torusMonodromyCylinderReflection.preservesOrientation O.opposite O := by
  rcases preservesOrientation_or_opposite torusMonodromyCylinderReflection O O with h | h
  · let p : Torus × unitInterval := ((1, 1), torusMonodromyMidpoint)
    have hfix : torusMonodromyCylinderReflection p = p :=
      Prod.ext rfl torusMonodromyIntervalReflection_midpoint
    have he : (torusMonodromyCylinderReflection.mfderivToContinuousLinearEquiv
        (by simp) p).toLinearEquiv = torusMonodromyNormalReflection := by
      ext v
      change mfderiv torusMonodromyCylinderModel torusMonodromyCylinderModel
        (Prod.map id torusMonodromyIntervalReflection) p v = _
      rw [mfderiv_prodMap mdifferentiableAt_id
        (torusMonodromyIntervalReflection.contMDiff.mdifferentiableAt (by simp)), mfderiv_id]
      rw [torusMonodromyIntervalReflection_midpoint_derivative]
      rfl
    have hh := h p
    erw [he, hfix, torusMonodromyNormalReflection_map] at hh
    exact False.elim (Module.Ray.ne_neg_self (O.orientation p) hh.symm)
  · exact h

def torusMonodromyCylinderExchange (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    (Torus × unitInterval) ≃ₘ⟮torusMonodromyCylinderModel,
      torusMonodromyCylinderModel⟯ (Torus × unitInterval) :=
  (f.prodCongr (Diffeomorph.refl (𝓡∂ 1) unitInterval ∞)).trans
    torusMonodromyCylinderReflection

def torusMonodromyExchange (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    (productSet.{u} 2) ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ (productSet.{u} 2) :=
  (torusMonodromyPolarDiffeomorph.trans (torusMonodromyCylinderExchange f)).trans
    torusMonodromyPolarDiffeomorph.symm

theorem exists_torusMonodromyPolarOrientation
    (O : ManifoldOrientation (𝓡∂ 3) (productSet.{u} 2) 3) :
    ∃ OP : ManifoldOrientation torusMonodromyCylinderModel (Torus × unitInterval) 3,
      torusMonodromyPolarDiffeomorph.preservesOrientation O OP := by
  let A := torusMonodromyPolarDiffeomorph.{u}.symm
  have hb : ∀ x, Bijective (mfderiv torusMonodromyCylinderModel (𝓡∂ 3) A x) :=
    fun x => (A.mfderivToContinuousLinearEquiv (by simp) x).bijective
  obtain ⟨OP, hOP⟩ := Manifold.exists_manifoldOrientation_pullback
    torusMonodromyCylinderModel (𝓡∂ 3) (by
      change Module.finrank ℝ
        ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
          EuclideanSpace ℝ (Fin 1)) = 3
      simp)
    A A.contMDiff hb O
  have hA : A.preservesOrientation OP O := by
    intro x
    have he : (Manifold.differentialEquivOfBijective torusMonodromyCylinderModel
        (𝓡∂ 3) A hb x).toLinearEquiv =
        (A.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv := by
      ext v
      rfl
    rw [← he]
    exact hOP x
  refine ⟨OP, ?_⟩
  have h := Diffeomorph.preservesOrientation_symm hA
  have hAA : A.symm = torusMonodromyPolarDiffeomorph.{u} := by
    apply Diffeomorph.ext
    intro x
    rfl
  rw [hAA] at h
  exact h

theorem torusMonodromyExchange_reversing
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (hf : f.preservesOrientation productTorusOrientation productTorusOrientation)
    (O : ManifoldOrientation (𝓡∂ 3) (productSet.{u} 2) 3) :
    (torusMonodromyExchange f).preservesOrientation O.opposite O := by
  obtain ⟨OP, hA⟩ := exists_torusMonodromyPolarOrientation O
  have hcy : (torusMonodromyCylinderExchange f).preservesOrientation OP.opposite OP :=
    Diffeomorph.preservesOrientation_trans
      (Diffeomorph.preservesOrientation_opposite (torusMonodromyCylinderPositive f hf OP))
      (torusMonodromyCylinderReflection_reversing OP)
  exact Diffeomorph.preservesOrientation_trans
    (Diffeomorph.preservesOrientation_trans
      (Diffeomorph.preservesOrientation_opposite hA) hcy)
      (Diffeomorph.preservesOrientation_symm hA)

theorem torusMonodromyExchange_collar
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) :
    torusMonodromyExchange.{u} f (torusMonodromyInnerCollar p) =
      torusMonodromyOuterCollar (f p.1, p.2) := by
  have hs : 0 ≤ p.2.val 0 := p.2.property
  have hr : 0 < (1 / 2 : ℝ) + p.2.val 0 / 4 := by linarith
  have hdown := torusMonodromyInnerCollar_down.{u} hp
  have hnorm : ‖(torusMonodromyInnerCollar.{u} p).val.1.down‖ =
      1 / 2 + p.2.val 0 / 4 := by
    rw [hdown, norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg hr.le]
  have hunit : unitOf (torusMonodromyInnerCollar.{u} p).val.1.down = p.1.1 := by
    rw [hdown]
    exact unitOf_smul hr p.1.1
  have hfibre : (torusMonodromyInnerCollar.{u} p).val.2 = p.1.2 := rfl
  apply Subtype.ext
  apply Prod.ext
  · apply ULift.ext
    rw [torusMonodromyOuterCollar_down (p := (f p.1, p.2)) hp]
    change (3 - (5 / 2) *
      (1 - (3 - ‖(torusMonodromyInnerCollar.{u} p).val.1.down‖) / (5 / 2))) •
      ((f (unitOf (torusMonodromyInnerCollar.{u} p).val.1.down,
        (torusMonodromyInnerCollar.{u} p).val.2)).1 : ℂ) = _
    rw [hnorm, hunit, hfibre]
    congr 1
    ring
  · change (f (unitOf (torusMonodromyInnerCollar.{u} p).val.1.down,
      (torusMonodromyInnerCollar.{u} p).val.2)).2 = (f p.1).2
    rw [hunit, hfibre]

theorem torusMonodromyReversal_of_exchange (C : CompactCarrier.{u})
    (F : C.Carrier ≃ₘ⟮C.model, C.model⟯ C.Carrier)
    (hF : F.preservesOrientation C.orientation.opposite C.orientation)
    (l r0 : PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (hlSource : l.source = halfCollarSource) (hrSource : r0.source = halfCollarSource)
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (hex : ∀ p ∈ halfCollarSource, F (l p) = r0 (f p.1, p.2)) :
    ReversesBoundaryOrientation C l (fun p => r0 (f p.1, p.2)) := by
  intro t
  let q : Torus × EuclideanHalfSpace 1 := (t, halfZero)
  let r : PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞ :=
    (f.prodCongr (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)).toPartialDiffeomorph.trans
      r0
  have hq : q ∈ halfCollarSource := by change (0 : ℝ) < 1; norm_num
  have hl : q ∈ l.source := by
    rw [hlSource]
    exact hq
  have hr : q ∈ r.source := by
    refine ⟨mem_univ _, ?_⟩
    change (f q.1, q.2) ∈ r0.source
    rw [hrSource]
    exact hq
  let L := ((l.isLocalDiffeomorphAt
    halfCollarModel C.model ∞ hl).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  have hRloc := r.isLocalDiffeomorphAt halfCollarModel C.model ∞ hr
  let R := (hRloc.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  let D := ((F).mfderivToContinuousLinearEquiv
    (by simp) (l q)).toLinearEquiv
  refine ⟨L, R, fun v => rfl, fun v => rfl, ?_⟩
  have hevent : (F) ∘ l =ᶠ[𝓝 q] r := by
    filter_upwards [l.open_source.mem_nhds hl] with p hp
    exact hex p (by rwa [hlSource] at hp)
  have hLR : R = L.trans D := by
    apply LinearEquiv.ext
    intro v
    change mfderiv halfCollarModel C.model r q v =
      mfderiv C.model C.model (F)
        (l q)
        (mfderiv halfCollarModel C.model l q v)
    rw [← mfderiv_comp_apply q
      (F.contMDiff.mdifferentiableAt (by simp))
      (l.mdifferentiableAt (by simp) hl)]
    exact DFunLike.congr_fun (Filter.EventuallyEq.mfderiv_eq hevent).symm v
  let O : ManifoldOrientation C.model C.Carrier 3 :=
    C.orientation
  have hpoint : F (l q) = r q :=
    hex q hq
  have hneg : Orientation.map (Fin 3) D (O.orientation (l q)) =
      -O.orientation (r q) := by
    have h := hF (l q)
    change Orientation.map (Fin 3) D (-O.orientation (l q)) =
      O.orientation (F (l q)) at h
    rw [Orientation.map_neg, hpoint] at h
    let a : Orientation ℝ (TangentSpace C.model (r q)) (Fin 3) :=
      Orientation.map (Fin 3) D (O.orientation (l q))
    let b : Orientation ℝ (TangentSpace C.model (r q)) (Fin 3) := O.orientation (r q)
    have hh : -a = b := h
    change a = -b
    calc
      a = -(-a) := (neg_neg a).symm
      _ = -b := congrArg Neg.neg hh
  change Orientation.map (Fin 3) L.symm (O.orientation (l q)) =
    -Orientation.map (Fin 3) R.symm (O.orientation (r q))
  apply (Orientation.map (Fin 3) R).injective
  erw [Orientation.map_neg, ← Orientation.map_symm (Fin 3) R, Equiv.apply_symm_apply]
  erw [hLR, DifferentialGeometry.orientation_map_trans,
    ← Orientation.map_symm (Fin 3) L, Equiv.apply_symm_apply]
  exact hneg

theorem torusMonodromyCollars_reversing
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (hf : f.preservesOrientation productTorusOrientation productTorusOrientation) :
    ReversesBoundaryOrientation annulusCircleCarrier.{u} torusMonodromyInnerCollar.{u}
      (fun p => torusMonodromyOuterCollar.{u} (f p.1, p.2)) := by
  exact torusMonodromyReversal_of_exchange annulusCircleCarrier.{u}
    (torusMonodromyExchange.{u} f)
    (torusMonodromyExchange_reversing.{u} f hf annulusCircleCarrier.{u}.orientation)
    torusMonodromyInnerCollar.{u} torusMonodromyOuterCollar.{u} torusMonodromyInnerCollar_source.{u}
    torusMonodromyOuterCollar_source.{u} f (fun p hp => torusMonodromyExchange_collar.{u} f hp)

def torusMonodromyPairing
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (hf : f.preservesOrientation productTorusOrientation productTorusOrientation) :
    TorusPairing annulusCircleCarrier.{u} where
  count := 1
  gluing := torusMonodromyGluing.{u} f
  leftParam := Function.const (Fin 1) (torusMonodromyEndParam.{u} 1)
  rightParam := Function.const (Fin 1) (torusMonodromyEndParam.{u} 0)
  matching := Function.const (Fin 1) f
  matching_eq := torusMonodromyGluing_attaching f
  leftCollar := Function.const (Fin 1) torusMonodromyInnerCollar.{u}
  rightCollar := Function.const (Fin 1) torusMonodromyOuterCollar.{u}
  left_source := Function.const (Fin 1) torusMonodromyInnerCollar_source.{u}
  right_source := Function.const (Fin 1) torusMonodromyOuterCollar_source.{u}
  left_zero := Function.const (Fin 1) torusMonodromyInnerCollar_zero.{u}
  right_zero := Function.const (Fin 1) torusMonodromyOuterCollar_zero.{u}
  reversing := Function.const (Fin 1) (torusMonodromyCollars_reversing.{u} f hf)

theorem exists_torusMonodromyPairing
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (hf : f.preservesOrientation productTorusOrientation productTorusOrientation) :
    ∃ P : TorusPairing annulusCircleCarrier.{u}, ∃ e : Fin 1 ≃ Fin P.count,
      (∀ i, P.matching (e i) = f) ∧
      annulusCircleCarrier.model.boundary annulusCircleCarrier.Carrier =
        ⋃ i, P.gluing.block i := by
  refine ⟨torusMonodromyPairing f hf, Equiv.refl (Fin 1), fun i => rfl, ?_⟩
  exact torusMonodromyGluing_boundary f

theorem torusMonodromyPairing_count
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (hf : f.preservesOrientation productTorusOrientation productTorusOrientation) :
    (torusMonodromyPairing.{u} f hf).count = 1 := rfl

theorem torusMonodromyPairing_matching
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (hf : f.preservesOrientation productTorusOrientation productTorusOrientation)
    (i : Fin (torusMonodromyPairing.{u} f hf).count) :
    (torusMonodromyPairing f hf).matching i = f := rfl

def torusMonodromyPairingQuotientHomeomorph
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (hf : f.preservesOrientation productTorusOrientation productTorusOrientation) :
    (torusMonodromyPairing.{u} f hf).QuotientSpace ≃ₜ
      Quotient (monodromyIntervalGluing f).setoid :=
  torusMonodromyQuotientHomeomorph f

theorem torusMonodromyPairingQuotientHomeomorph_apply
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (hf : f.preservesOrientation productTorusOrientation productTorusOrientation)
    (x : annulusCircleCarrier.{u}.Carrier) :
    torusMonodromyPairingQuotientHomeomorph f hf
        ((torusMonodromyPairing f hf).quotientMap x) =
      Quotient.mk'' (torusMonodromyPolar x) := rfl

theorem torusMonodromyPairing_connected
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (hf : f.preservesOrientation productTorusOrientation productTorusOrientation) :
    ConnectedSpace (torusMonodromyPairing.{u} f hf).QuotientSpace := by
  let : ConnectedSpace (productSet.{u} 2) := connectedSpace_productSet (Or.inl rfl)
  change ConnectedSpace (Quotient (torusMonodromyGluing.{u} f).setoid)
  infer_instance

end GC.GraphManifold
