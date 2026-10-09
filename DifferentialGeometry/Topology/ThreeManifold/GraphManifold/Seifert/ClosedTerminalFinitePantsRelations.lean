import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTerminalFinitePants
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PlanarModels

/-!
# Native boundary generators of the compact planar pants

The actual outer semicircles and a vertical strip path split the outer loop into two half
loops. Native hole-circle equivalences and their winding numbers identify those loops.
Van Kampen supplies generation, yielding the same-sign relation for all three boundaries.
-/

set_option autoImplicit false

noncomputable section

open Multiplicative Set DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold
open DifferentialGeometry.Topology.VanKampen
open scoped Topology ContinuousMap unitInterval ComplexConjugate

namespace GC.Seifert

def closedPantsToPlane : C(ClosedPants, PantsPlane) :=
  ⟨fun z => ⟨z.1, planarModel_subset_pantsPlane z.2⟩,
    continuous_subtype_val.subtype_mk _⟩

theorem closedPantsToPlane_circle (j : Fin 3) :
    closedPantsToPlane.comp (closedPantsCircle j) = pantsCircle j := rfl

theorem closedPants_mem_of_norm (z : ℂ) (hz : ‖z‖ = 3) : z ∈ planarModel 3 := by
  refine ⟨hz.le, fun j hj => ?_⟩
  have h := (norm_sub_real_bounds z (planarCenter 3 j)).1
  have hc := abs_planarCenter_le 3 j
  linarith

def closedPantsOuter : C(Circle, ClosedPants) :=
  (closedPantsCircle 0).comp (circleRotate pantsQuarter)

theorem coe_closedPantsOuter (t : Circle) :
    ((closedPantsOuter t : ClosedPants) : ℂ) = 3 * Complex.I * t := by
  change planarCircleMap 3 0 (pantsQuarter * t) = _
  simp [planarCircleMap, planarCenter, planarRadius, coe_pantsQuarter]
  ring

theorem re_closedPantsOuter_one : ((closedPantsOuter 1 : ClosedPants) : ℂ).re = 0 := by
  rw [coe_closedPantsOuter]
  simp

abbrev closedPantsBase : ↥(closedPantsLeft ∩ closedPantsRight) :=
  ⟨closedPantsOuter 1,
    show ((closedPantsOuter 1 : ClosedPants) : ℂ).re < 1 / 2 by
      rw [re_closedPantsOuter_one]; norm_num,
    show -(1 / 2) < ((closedPantsOuter 1 : ClosedPants) : ℂ).re by
      rw [re_closedPantsOuter_one]; norm_num⟩

def closedPantsBot : ClosedPants :=
  ⟨-(3 * Complex.I), closedPantsStrip_subset ⟨by simp, by simp, by simp⟩⟩

def closedPantsStripBot : ↥(closedPantsLeft ∩ closedPantsRight) :=
  ⟨closedPantsBot, show (-(3 * Complex.I)).re < 1 / 2 by simp,
    show -(1 / 2) < (-(3 * Complex.I)).re by simp⟩

theorem coe_closedPantsBase : ((closedPantsBase.1 : ClosedPants) : ℂ) = 3 * Complex.I := by
  change ((closedPantsOuter 1 : ClosedPants) : ℂ) = _
  rw [coe_closedPantsOuter, Circle.coe_one, mul_one]

def closedPantsLeftArc : Path (interToLeft closedPantsLeft closedPantsRight closedPantsBase)
    (interToLeft closedPantsLeft closedPantsRight closedPantsStripBot) where
  toFun s := ⟨⟨pantsArcValue (3 * Complex.I) s, closedPants_mem_of_norm _ (by
    rw [norm_pantsArcValue]; simp)⟩, re_pantsArcValue_top s⟩
  continuous_toFun := ((continuous_pantsArcValue _).subtype_mk _).subtype_mk _
  source' := by
    apply Subtype.ext
    apply Subtype.ext
    change pantsArcValue (3 * Complex.I) 0 = ((closedPantsBase.1 : ClosedPants) : ℂ)
    rw [pantsArcValue_zero, coe_closedPantsBase]
  target' := by
    apply Subtype.ext
    apply Subtype.ext
    change pantsArcValue (3 * Complex.I) 1 = -(3 * Complex.I)
    rw [pantsArcValue_one]

def closedPantsRightArc : Path (interToRight closedPantsLeft closedPantsRight closedPantsStripBot)
    (interToRight closedPantsLeft closedPantsRight closedPantsBase) where
  toFun s := ⟨⟨pantsArcValue (-(3 * Complex.I)) s, closedPants_mem_of_norm _ (by
    rw [norm_pantsArcValue]; simp)⟩, re_pantsArcValue_bot s⟩
  continuous_toFun := ((continuous_pantsArcValue _).subtype_mk _).subtype_mk _
  source' := by
    apply Subtype.ext
    apply Subtype.ext
    change pantsArcValue (-(3 * Complex.I)) 0 = -(3 * Complex.I)
    rw [pantsArcValue_zero]
  target' := by
    apply Subtype.ext
    apply Subtype.ext
    change pantsArcValue (-(3 * Complex.I)) 1 = ((closedPantsBase.1 : ClosedPants) : ℂ)
    rw [pantsArcValue_one, coe_closedPantsBase, neg_neg]

def closedPantsStripPath : Path closedPantsStripBot closedPantsBase where
  toFun s := ⟨⟨pantsStripValue s, closedPantsStrip_subset ⟨by
      rw [pantsStripValue, norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [s.2.1, s.2.2], by
      rw [re_pantsStripValue]; norm_num, by rw [re_pantsStripValue]; norm_num⟩⟩,
    show (pantsStripValue s).re < 1 / 2 by rw [re_pantsStripValue]; norm_num,
    show -(1 / 2) < (pantsStripValue s).re by rw [re_pantsStripValue]; norm_num⟩
  continuous_toFun := (((by unfold pantsStripValue; fun_prop :
    Continuous pantsStripValue).subtype_mk _).subtype_mk _)
  source' := by
    apply Subtype.ext
    apply Subtype.ext
    change pantsStripValue 0 = -(3 * Complex.I)
    simp [pantsStripValue]
  target' := by
    apply Subtype.ext
    apply Subtype.ext
    change pantsStripValue 1 = ((closedPantsBase.1 : ClosedPants) : ℂ)
    rw [coe_closedPantsBase]
    simp [pantsStripValue]
    norm_num

def closedPantsLoopLeft : Path (interToLeft closedPantsLeft closedPantsRight closedPantsBase)
    (interToLeft closedPantsLeft closedPantsRight closedPantsBase) :=
  closedPantsLeftArc.trans
    (closedPantsStripPath.map (interToLeft closedPantsLeft closedPantsRight).continuous)

def closedPantsLoopRight : Path (interToRight closedPantsLeft closedPantsRight closedPantsBase)
    (interToRight closedPantsLeft closedPantsRight closedPantsBase) :=
  (closedPantsStripPath.map
    (interToRight closedPantsLeft closedPantsRight).continuous).symm.trans closedPantsRightArc

def closedPantsLeftPath : Path closedPantsBase.1 closedPantsBot :=
  closedPantsLeftArc.map (subsetToAmbient closedPantsLeft).continuous

def closedPantsRightPath : Path closedPantsBot closedPantsBase.1 :=
  closedPantsRightArc.map (subsetToAmbient closedPantsRight).continuous

def closedPantsMidPath : Path closedPantsBot closedPantsBase.1 :=
  closedPantsStripPath.map (subsetToAmbient (closedPantsLeft ∩ closedPantsRight)).continuous

theorem closedPantsOuter_circleLoop :
    circleLoop.map closedPantsOuter.continuous =
      closedPantsLeftPath.trans closedPantsRightPath := by
  ext t
  rw [Path.trans_apply]
  split_ifs with h
  · change ((closedPantsOuter (Circle.exp (2 * Real.pi * t)) : ClosedPants) : ℂ) =
      pantsArcValue (3 * Complex.I) _
    rw [coe_closedPantsOuter, Circle.coe_exp, pantsArcValue]
    push_cast
    ring_nf
  · change ((closedPantsOuter (Circle.exp (2 * Real.pi * t)) : ClosedPants) : ℂ) =
      pantsArcValue (-(3 * Complex.I)) _
    rw [coe_closedPantsOuter, Circle.coe_exp, pantsArcValue]
    have he : (((Real.pi * (2 * (t : ℝ) - 1) : ℝ) : ℂ) * Complex.I) =
        (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) - (Real.pi : ℂ) * Complex.I := by
      push_cast
      ring
    rw [he, Complex.exp_sub, Complex.exp_pi_mul_I]
    field_simp

theorem closedPantsOuter_map_circleLoop :
    FundamentalGroup.map closedPantsOuter 1 (FundamentalGroup.fromPath ⟦circleLoop⟧) =
      FundamentalGroup.fromPath ⟦closedPantsMidPath.symm.trans closedPantsRightPath⟧ *
        FundamentalGroup.fromPath ⟦closedPantsLeftPath.trans closedPantsMidPath⟧ := by
  rw [FundamentalGroup.mul_def]
  change (⟦circleLoop.map closedPantsOuter.continuous⟧ : Path.Homotopic.Quotient _ _) = _
  rw [closedPantsOuter_circleLoop]
  have hq : ∀ {x y : ClosedPants} (q : Path x y),
      (⟦q⟧ : Path.Homotopic.Quotient x y) = Path.Homotopic.Quotient.mk q := fun q => rfl
  simp only [hq, Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc]
  rw [← Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.mk closedPantsMidPath)
    (Path.Homotopic.Quotient.mk closedPantsMidPath).symm, Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.refl_trans]

theorem map_closedPantsLoopLeft :
    @id (FundamentalGroup ClosedPants closedPantsBase.1) (FundamentalGroup.map
        (subsetToAmbient closedPantsLeft) _ (FundamentalGroup.fromPath ⟦closedPantsLoopLeft⟧)) =
      FundamentalGroup.fromPath ⟦closedPantsLeftPath.trans closedPantsMidPath⟧ := by
  change (⟦closedPantsLoopLeft.map (subsetToAmbient closedPantsLeft).continuous⟧ :
    Path.Homotopic.Quotient _ _) = _
  rw [closedPantsLoopLeft, Path.map_trans]
  rfl

theorem map_closedPantsLoopRight :
    @id (FundamentalGroup ClosedPants closedPantsBase.1) (FundamentalGroup.map
        (subsetToAmbient closedPantsRight) _ (FundamentalGroup.fromPath ⟦closedPantsLoopRight⟧)) =
      FundamentalGroup.fromPath ⟦closedPantsMidPath.symm.trans closedPantsRightPath⟧ := by
  change (⟦closedPantsLoopRight.map (subsetToAmbient closedPantsRight).continuous⟧ :
    Path.Homotopic.Quotient _ _) = _
  rw [closedPantsLoopRight, Path.map_trans, Path.map_symm]
  rfl


def closedPantsToLeft : C(↥closedPantsLeft, ↥pantsLeft) :=
  ⟨fun z => ⟨closedPantsToPlane z.1, z.2⟩,
    (closedPantsToPlane.continuous.comp continuous_subtype_val).subtype_mk _⟩

def closedPantsToRight : C(↥closedPantsRight, ↥pantsRight) :=
  ⟨fun z => ⟨closedPantsToPlane z.1, z.2⟩,
    (closedPantsToPlane.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem closedPantsToLeft_loop :
    closedPantsLoopLeft.map closedPantsToLeft.continuous = pantsLoopLeft := by
  rw [closedPantsLoopLeft, Path.map_trans, pantsLoopLeft]
  congr 1

theorem closedPantsToRight_loop :
    closedPantsLoopRight.map closedPantsToRight.continuous = pantsLoopRight := by
  rw [closedPantsLoopRight, Path.map_trans, Path.map_symm, pantsLoopRight]
  congr 1

def closedPantsRetractionLeft : C(ClosedPants, Circle) :=
  pantsRetractionLeft.comp closedPantsToPlane

def closedPantsRetractionRight : C(ClosedPants, Circle) :=
  pantsRetractionRight.comp closedPantsToPlane

theorem closedPantsRetractionLeft_circle :
    (closedPantsRetractionLeft.comp (subsetToAmbient closedPantsLeft)).comp
      closedPantsLeftCircle = ContinuousMap.id Circle := by
  rw [ContinuousMap.comp_assoc, closedPantsLeftCircle_toAmbient]
  change (pantsRetractionLeft.comp closedPantsToPlane).comp (closedPantsCircle 2) = _
  rw [ContinuousMap.comp_assoc, closedPantsToPlane_circle]
  exact pantsRetraction_comp_pantsCircle 2 (by decide)

theorem closedPantsRetractionRight_circle :
    (closedPantsRetractionRight.comp (subsetToAmbient closedPantsRight)).comp
      closedPantsRightCircle = ContinuousMap.id Circle := by
  rw [ContinuousMap.comp_assoc, closedPantsRightCircle_toAmbient]
  change (pantsRetractionRight.comp closedPantsToPlane).comp (closedPantsCircle 1) = _
  rw [ContinuousMap.comp_assoc, closedPantsToPlane_circle]
  exact pantsRetraction_comp_pantsCircle 1 (by decide)

theorem closedPantsLoopLeft_winding :
    toAdd (circleHom (closedPantsRetractionLeft.comp (subsetToAmbient closedPantsLeft))
      (interToLeft closedPantsLeft closedPantsRight closedPantsBase)
      (FundamentalGroup.fromPath ⟦closedPantsLoopLeft⟧)) = -1 := by
  have h := toAdd_circleHom_pantsOuter pantsRetractionLeft
  have hd : circleDegree (pantsRetractionLeft.comp pantsOuter) = -1 :=
    circleDegree_pantsRetraction_pantsOuter pantsPlanarBase.{0} 2 (by decide)
      (by norm_num [planarCenter])
  rw [circleHom_pantsOuter, circleHom_pantsRetractionLeft_right, one_mul, hd] at h
  change toAdd (circleHom ((pantsRetractionLeft.comp (subsetToAmbient pantsLeft)).comp
    closedPantsToLeft) _ _) = -1
  rw [← circleHom_map]
  change toAdd (circleHom (pantsRetractionLeft.comp (subsetToAmbient pantsLeft)) _
    (FundamentalGroup.fromPath ⟦closedPantsLoopLeft.map closedPantsToLeft.continuous⟧)) = -1
  rw [closedPantsToLeft_loop]
  exact h

theorem closedPantsLoopRight_winding :
    toAdd (circleHom (closedPantsRetractionRight.comp (subsetToAmbient closedPantsRight))
      (interToRight closedPantsLeft closedPantsRight closedPantsBase)
      (FundamentalGroup.fromPath ⟦closedPantsLoopRight⟧)) = -1 := by
  have h := toAdd_circleHom_pantsOuter pantsRetractionRight
  have hd : circleDegree (pantsRetractionRight.comp pantsOuter) = -1 :=
    circleDegree_pantsRetraction_pantsOuter pantsPlanarBase.{0} 1 (by decide)
      (by norm_num [planarCenter])
  rw [circleHom_pantsOuter, circleHom_pantsRetractionRight_left, mul_one, hd] at h
  change toAdd (circleHom ((pantsRetractionRight.comp (subsetToAmbient pantsRight)).comp
    closedPantsToRight) _ _) = -1
  rw [← circleHom_map]
  change toAdd (circleHom (pantsRetractionRight.comp (subsetToAmbient pantsRight)) _
    (FundamentalGroup.fromPath ⟦closedPantsLoopRight.map closedPantsToRight.continuous⟧)) = -1
  rw [closedPantsToRight_loop]
  exact h

theorem eq_marked_circleLoop_zpow_of_bijective {Y : Type*} [TopologicalSpace Y]
    (f : C(Circle, Y)) (ρ : C(Y, Circle)) {y : Y} (γ : Path y (f 1))
    (hf : Function.Bijective (FundamentalGroup.map f 1))
    (hρ : ρ.comp f = ContinuousMap.id Circle) (a : FundamentalGroup Y y) :
    a = GC.Topology.markedMap f 1 γ (FundamentalGroup.fromPath ⟦circleLoop⟧) ^
      toAdd (circleHom ρ y a) := by
  have hb : Function.Bijective (GC.Topology.markedMap f 1 γ) :=
    (fundamentalGroupChangeBasepoint γ).bijective.comp hf
  obtain ⟨b, rfl⟩ := hb.surjective a
  rw [circleHom_markedMap, hρ, circleDegree_id, one_mul]
  conv_lhs => rw [eq_circleLoop_zpow b]
  rw [map_zpow]

private theorem subgroup_eq_top_of_openCover {X : Type*} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x : ↥(U ∩ V)) [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace ↥(U ∩ V)] (S : Subgroup (FundamentalGroup X x.1))
    (hL : ∀ a, FundamentalGroup.map (subsetToAmbient U) (interToLeft U V x) a ∈ S)
    (hR : ∀ a, FundamentalGroup.map (subsetToAmbient V) (interToRight U V x) a ∈ S) :
    S = ⊤ := by
  let e := fundamentalGroupEquivAmalgamatedProduct U V hU hV hcover x.1 x.2
  let φ := fundamentalGroupAmalgamation U V x.1 x.2
  have hof : ∀ i a, e (Monoid.PushoutI.of (φ := φ) i a) ∈ S := by
    intro i a
    cases i
    · have he := fundamentalGroupEquivAmalgamatedProduct_of_false U V hU hV hcover x a
      exact he.symm ▸ hL a
    · have he := fundamentalGroupEquivAmalgamatedProduct_of_true U V hU hV hcover x a
      exact he.symm ▸ hR a
  apply top_unique
  intro g hg
  clear hg
  obtain ⟨w, rfl⟩ := e.surjective g
  induction w using Monoid.PushoutI.induction_on with
  | of i a => exact hof i a
  | base a =>
    rw [← Monoid.PushoutI.of_apply_eq_base φ false a]
    exact hof false (φ false a)
  | mul a b ha hb =>
    rw [map_mul]
    exact S.mul_mem ha hb

theorem exists_closedPants_outerBoundaryPath :
    ∃ β : Path closedPantsBase.1 (closedPantsCircle 0 1),
      GC.Topology.markedMap (closedPantsCircle 0) 1 β
        (FundamentalGroup.fromPath ⟦circleLoop⟧) =
          FundamentalGroup.map closedPantsOuter 1 (FundamentalGroup.fromPath ⟦circleLoop⟧) := by
  have hc : closedPantsOuter.comp (circleRotate pantsQuarter⁻¹) = closedPantsCircle 0 := by
    apply ContinuousMap.ext
    intro t
    change closedPantsCircle 0 (pantsQuarter * (pantsQuarter⁻¹ * t)) = _
    rw [mul_inv_cancel_left]
  rw [← hc]
  let γ := PathConnectedSpace.somePath (1 : Circle) (circleRotate pantsQuarter⁻¹ 1)
  refine ⟨(Path.refl _).trans (γ.map closedPantsOuter.continuous), ?_⟩
  rw [← markedMap_comp_markedMap, MonoidHom.comp_apply, markedMap_refl]
  apply congrArg (FundamentalGroup.map closedPantsOuter 1)
  apply fundamentalGroupCircleEquivInt.injective
  apply toAdd.injective
  rw [circleInt_markedMap, circleDegree_circleRotate, one_mul]

theorem exists_closedPants_boundary_generators :
    ∃ p : ClosedPants, ∃ β : (j : Fin 3) → Path p (closedPantsCircle j 1),
      let x := fun j => GC.Topology.markedMap (closedPantsCircle j) 1 (β j)
        (FundamentalGroup.fromPath ⟦circleLoop⟧)
      Subgroup.closure (Set.range x) = ⊤ ∧ x 0 * x 2 * x 1 = 1 := by
  let γL := PathConnectedSpace.somePath
    (interToLeft closedPantsLeft closedPantsRight closedPantsBase) (closedPantsLeftCircle 1)
  let γR := PathConnectedSpace.somePath
    (interToRight closedPantsLeft closedPantsRight closedPantsBase) (closedPantsRightCircle 1)
  let gL := GC.Topology.markedMap closedPantsLeftCircle 1 γL
    (FundamentalGroup.fromPath ⟦circleLoop⟧)
  let gR := GC.Topology.markedMap closedPantsRightCircle 1 γR
    (FundamentalGroup.fromPath ⟦circleLoop⟧)
  let l : FundamentalGroup ClosedPants closedPantsBase.1 :=
    FundamentalGroup.map (subsetToAmbient closedPantsLeft)
      (interToLeft closedPantsLeft closedPantsRight closedPantsBase) gL
  let r : FundamentalGroup ClosedPants closedPantsBase.1 :=
    FundamentalGroup.map (subsetToAmbient closedPantsRight)
      (interToRight closedPantsLeft closedPantsRight closedPantsBase) gR
  have hL : FundamentalGroup.fromPath ⟦closedPantsLoopLeft⟧ = gL⁻¹ := by
    have h := eq_marked_circleLoop_zpow_of_bijective closedPantsLeftCircle
      (closedPantsRetractionLeft.comp (subsetToAmbient closedPantsLeft)) γL
      (bijective_map_closedPantsLeftCircle 1) closedPantsRetractionLeft_circle
      (FundamentalGroup.fromPath ⟦closedPantsLoopLeft⟧)
    rwa [closedPantsLoopLeft_winding, zpow_neg_one] at h
  have hR : FundamentalGroup.fromPath ⟦closedPantsLoopRight⟧ = gR⁻¹ := by
    have h := eq_marked_circleLoop_zpow_of_bijective closedPantsRightCircle
      (closedPantsRetractionRight.comp (subsetToAmbient closedPantsRight)) γR
      (bijective_map_closedPantsRightCircle 1) closedPantsRetractionRight_circle
      (FundamentalGroup.fromPath ⟦closedPantsLoopRight⟧)
    rwa [closedPantsLoopRight_winding, zpow_neg_one] at h
  have ho : FundamentalGroup.map closedPantsOuter 1
      (FundamentalGroup.fromPath ⟦circleLoop⟧) = r⁻¹ * l⁻¹ := by
    rw [closedPantsOuter_map_circleLoop, ← map_closedPantsLoopLeft,
      ← map_closedPantsLoopRight, hL, hR, map_inv, map_inv]
    rfl
  obtain ⟨β0, h0⟩ := exists_closedPants_outerBoundaryPath
  have hleft : ∃ β2 : Path closedPantsBase.1 (closedPantsCircle 2 1),
      GC.Topology.markedMap (closedPantsCircle 2) 1 β2
        (FundamentalGroup.fromPath ⟦circleLoop⟧) = l := by
    rw [← closedPantsLeftCircle_toAmbient]
    refine ⟨γL.map (subsetToAmbient closedPantsLeft).continuous, ?_⟩
    exact (DFunLike.congr_fun (map_comp_markedMap closedPantsLeftCircle
      (subsetToAmbient closedPantsLeft) 1 γL) (FundamentalGroup.fromPath ⟦circleLoop⟧)).symm
  have hright : ∃ β1 : Path closedPantsBase.1 (closedPantsCircle 1 1),
      GC.Topology.markedMap (closedPantsCircle 1) 1 β1
        (FundamentalGroup.fromPath ⟦circleLoop⟧) = r := by
    rw [← closedPantsRightCircle_toAmbient]
    refine ⟨γR.map (subsetToAmbient closedPantsRight).continuous, ?_⟩
    exact (DFunLike.congr_fun (map_comp_markedMap closedPantsRightCircle
      (subsetToAmbient closedPantsRight) 1 γR) (FundamentalGroup.fromPath ⟦circleLoop⟧)).symm
  obtain ⟨β1, h1⟩ := hright
  obtain ⟨β2, h2⟩ := hleft
  let β : (j : Fin 3) → Path closedPantsBase.1 (closedPantsCircle j 1) := by
    exact Fin.cases β0 (Fin.cases β1 (Fin.cases β2 (fun i => Fin.elim0 i)))
  let x := fun j => GC.Topology.markedMap (closedPantsCircle j) 1 (β j)
    (FundamentalGroup.fromPath ⟦circleLoop⟧)
  have hx0 : x 0 = r⁻¹ * l⁻¹ := h0.trans ho
  have hx1 : x 1 = r := h1
  have hx2 : x 2 = l := h2
  refine ⟨closedPantsBase.1, β, ?_, ?_⟩
  · let S := Subgroup.closure (Set.range x)
    have hl : l ∈ S := hx2 ▸ Subgroup.subset_closure ⟨2, rfl⟩
    have hr : r ∈ S := hx1 ▸ Subgroup.subset_closure ⟨1, rfl⟩
    apply subgroup_eq_top_of_openCover closedPantsLeft closedPantsRight
      isOpen_closedPantsLeft isOpen_closedPantsRight
      closedPantsLeft_union_closedPantsRight closedPantsBase S
    · intro a
      have h := eq_marked_circleLoop_zpow_of_bijective closedPantsLeftCircle
        (closedPantsRetractionLeft.comp (subsetToAmbient closedPantsLeft)) γL
        (bijective_map_closedPantsLeftCircle 1) closedPantsRetractionLeft_circle a
      rw [h, map_zpow]
      exact S.zpow_mem hl _
    · intro a
      have h := eq_marked_circleLoop_zpow_of_bijective closedPantsRightCircle
        (closedPantsRetractionRight.comp (subsetToAmbient closedPantsRight)) γR
        (bijective_map_closedPantsRightCircle 1) closedPantsRetractionRight_circle a
      rw [h, map_zpow]
      exact S.zpow_mem hr _
  · change x 0 * x 2 * x 1 = 1
    simp only [hx0, hx2, hx1, mul_assoc, inv_mul_cancel, one_mul]

end GC.Seifert
