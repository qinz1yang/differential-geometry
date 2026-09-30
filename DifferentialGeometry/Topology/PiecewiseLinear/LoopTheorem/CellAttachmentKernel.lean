/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.FundamentalGroup.Circle
import DifferentialGeometry.Topology.Homotopy.ClosedCell
import DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.BasedCircle
import DifferentialGeometry.Topology.VanKampen.Based
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Topology.Piecewise

open CategoryTheory Set
open scoped ContinuousMap

namespace DifferentialGeometry.Topology

universe u

theorem ker_eq_normalClosure_range_of_isPushout_of_subsingleton
    {A G T P : Type u} [Group A] [Group G] [Group T] [Group P]
    (f : A →* G) (g : A →* T) (i : G →* P) (j : T →* P)
    (h : IsPushout (GrpCat.ofHom f) (GrpCat.ofHom g)
      (GrpCat.ofHom i) (GrpCat.ofHom j)) [Subsingleton T] :
    MonoidHom.ker i = Subgroup.normalClosure (Set.range f) := by
  let N : Subgroup G := Subgroup.normalClosure (Set.range f)
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let k : T →* G ⧸ N := 1
  have hcompat : (GrpCat.ofHom f) ≫ (GrpCat.ofHom q) =
      (GrpCat.ofHom g) ≫ (GrpCat.ofHom k) := by
    apply GrpCat.ext
    intro x
    change q (f x) = k (g x)
    rw [show k (g x) = 1 by rfl]
    exact (QuotientGroup.eq_one_iff (f x)).2
      (Subgroup.subset_normalClosure ⟨x, rfl⟩)
  let d : GrpCat.of P ⟶ GrpCat.of (G ⧸ N) :=
    h.desc (GrpCat.ofHom q) (GrpCat.ofHom k) hcompat
  apply le_antisymm
  · intro x hx
    have hix : i x = 1 := MonoidHom.mem_ker.mp hx
    have hdi := congrArg (fun m : G →* G ⧸ N => m x)
      (congrArg GrpCat.Hom.hom
        (h.inl_desc (GrpCat.ofHom q) (GrpCat.ofHom k) hcompat))
    change d.hom (i x) = q x at hdi
    rw [hix, map_one] at hdi
    exact (QuotientGroup.eq_one_iff x).1 hdi.symm
  · apply Subgroup.normalClosure_le_normal
    rintro x ⟨a, rfl⟩
    apply MonoidHom.mem_ker.mpr
    have hw := congrArg (fun m : A →* P => m a)
      (congrArg GrpCat.Hom.hom h.w)
    change i (f a) = j (g a) at hw
    rw [hw, Subsingleton.elim (g a) 1, map_one]

theorem surjective_of_isPushout_of_subsingleton
    {A G T P : Type u} [Group A] [Group G] [Group T] [Group P]
    (f : A →* G) (g : A →* T) (i : G →* P) (j : T →* P)
    (h : IsPushout (GrpCat.ofHom f) (GrpCat.ofHom g)
      (GrpCat.ofHom i) (GrpCat.ofHom j)) [Subsingleton T] :
    Function.Surjective i := by
  let N : Subgroup G := Subgroup.normalClosure (Set.range f)
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let k : T →* G ⧸ N := 1
  have hNker : N ≤ MonoidHom.ker i := by
    apply Subgroup.normalClosure_le_normal
    rintro x ⟨a, rfl⟩
    apply MonoidHom.mem_ker.mpr
    have hw := congrArg (fun m : A →* P => m a)
      (congrArg GrpCat.Hom.hom h.w)
    change i (f a) = j (g a) at hw
    rw [hw, Subsingleton.elim (g a) 1, map_one]
  let e : G ⧸ N →* P := QuotientGroup.lift N i hNker
  have hcompat : (GrpCat.ofHom f) ≫ (GrpCat.ofHom q) =
      (GrpCat.ofHom g) ≫ (GrpCat.ofHom k) := by
    apply GrpCat.ext
    intro x
    change q (f x) = k (g x)
    rw [show k (g x) = 1 by rfl]
    exact (QuotientGroup.eq_one_iff (f x)).2
      (Subgroup.subset_normalClosure ⟨x, rfl⟩)
  let d : GrpCat.of P ⟶ GrpCat.of (G ⧸ N) :=
    h.desc (GrpCat.ofHom q) (GrpCat.ofHom k) hcompat
  have hed : d ≫ GrpCat.ofHom e = 𝟙 (GrpCat.of P) := by
    apply h.hom_ext
    · apply GrpCat.ext
      intro x
      have hinl := congrArg (fun m : G →* G ⧸ N => m x)
        (congrArg GrpCat.Hom.hom
          (h.inl_desc (GrpCat.ofHom q) (GrpCat.ofHom k) hcompat))
      change d.hom (i x) = q x at hinl
      change e (d.hom (i x)) = i x
      rw [hinl]
      rfl
    · apply GrpCat.ext
      intro x
      have hinr := congrArg (fun m : T →* G ⧸ N => m x)
        (congrArg GrpCat.Hom.hom
          (h.inr_desc (GrpCat.ofHom q) (GrpCat.ofHom k) hcompat))
      change d.hom (j x) = k x at hinr
      change e (d.hom (j x)) = j x
      rw [hinr, Subsingleton.elim x 1, map_one, map_one]
      exact (map_one j).symm
  intro p
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N (d.hom p)
  refine ⟨x, ?_⟩
  have hp := congrArg (fun m : P →* P => m p)
    (congrArg GrpCat.Hom.hom hed)
  change e (d.hom p) = p at hp
  rw [← hx] at hp
  exact hp

theorem normalClosure_range_eq_normalClosure_singleton_of_zpowers
    {A G : Type*} [Group A] [Group G] (f : A →* G) (z : A)
    (hz : ∀ a : A, a ∈ Subgroup.zpowers z) :
    Subgroup.normalClosure (Set.range f) =
      Subgroup.normalClosure ({f z} : Set G) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨a, rfl⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hz a)
    rw [map_zpow]
    exact Subgroup.zpow_mem _
      (Subgroup.subset_normalClosure (Set.mem_singleton (f z))) m
  · apply Subgroup.normalClosure_mono
    rintro _ rfl
    exact ⟨z, rfl⟩

namespace VanKampen

theorem ker_fundamentalGroupLeftToAmbient_eq_normalClosure_range
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [SimplyConnectedSpace V]
    [PathConnectedSpace (↑(U ∩ V))] :
    MonoidHom.ker (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom =
      Subgroup.normalClosure
        (Set.range (fundamentalGroupInterToLeft U V x₀ hx₀).hom) := by
  exact ker_eq_normalClosure_range_of_isPushout_of_subsingleton
    (fundamentalGroupInterToLeft U V x₀ hx₀).hom
    (fundamentalGroupInterToRight U V x₀ hx₀).hom
    (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom
    (fundamentalGroupRightToAmbient V x₀ hx₀.2).hom
    (fundamentalGroup_isPushout U V hU hV hcover x₀ hx₀)

theorem surjective_fundamentalGroupLeftToAmbient
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [SimplyConnectedSpace V]
    [PathConnectedSpace (↑(U ∩ V))] :
    Function.Surjective (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom := by
  exact surjective_of_isPushout_of_subsingleton
    (fundamentalGroupInterToLeft U V x₀ hx₀).hom
    (fundamentalGroupInterToRight U V x₀ hx₀).hom
    (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom
    (fundamentalGroupRightToAmbient V x₀ hx₀.2).hom
    (fundamentalGroup_isPushout U V hU hV hcover x₀ hx₀)

theorem ker_fundamentalGroupLeftToAmbient_eq_normalClosure_singleton
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [SimplyConnectedSpace V]
    [PathConnectedSpace (↑(U ∩ V))]
    (z : FundamentalGroup (↑(U ∩ V)) (overlapBasepoint U V x₀ hx₀))
    (hz : ∀ a, a ∈ Subgroup.zpowers z) :
    MonoidHom.ker (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom =
      Subgroup.normalClosure
        ({(fundamentalGroupInterToLeft U V x₀ hx₀).hom z} :
          Set (FundamentalGroup U (leftBasepoint U x₀ hx₀.1))) := by
  rw [ker_fundamentalGroupLeftToAmbient_eq_normalClosure_range
    U V hU hV hcover x₀ hx₀]
  exact normalClosure_range_eq_normalClosure_singleton_of_zpowers
    (fundamentalGroupInterToLeft U V x₀ hx₀).hom z hz

end VanKampen

abbrev PuncturedClosedCell (n : ℕ) :=
  {x : ClosedCell n // x ≠ closedCellCenter n}

def puncturedClosedCellBoundary (n : ℕ) : Set (PuncturedClosedCell n) :=
  {x | ‖(x.1 : EuclideanSpace ℝ (Fin n))‖ = 1}

noncomputable def puncturedClosedCellRadialScale (t : unitInterval) (r : ℝ) : ℝ :=
  (1 - (t : ℝ)) + (t : ℝ) * r⁻¹

theorem puncturedClosedCellRadialScale_nonneg (t : unitInterval) {r : ℝ}
    (hr : 0 < r) : 0 ≤ puncturedClosedCellRadialScale t r := by
  exact add_nonneg (sub_nonneg.mpr t.2.2) (mul_nonneg t.2.1 (inv_nonneg.mpr hr.le))

theorem puncturedClosedCellRadialScale_mul (t : unitInterval) {r : ℝ}
    (hr : 0 < r) : puncturedClosedCellRadialScale t r * r =
      (1 - (t : ℝ)) * r + (t : ℝ) := by
  unfold puncturedClosedCellRadialScale
  rw [add_mul, mul_assoc, inv_mul_cancel₀ hr.ne', mul_one]

noncomputable def puncturedClosedCellRadialExpansion (n : ℕ)
    (t : unitInterval) (x : PuncturedClosedCell n) : PuncturedClosedCell n := by
  let r := ‖(x.1 : EuclideanSpace ℝ (Fin n))‖
  have hr : 0 < r := norm_pos_iff.mpr fun hx => x.2 (Subtype.ext hx)
  have hnorm : ‖puncturedClosedCellRadialScale t r •
      (x.1 : EuclideanSpace ℝ (Fin n))‖ =
      (1 - (t : ℝ)) * r + (t : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (puncturedClosedCellRadialScale_nonneg t hr),
      puncturedClosedCellRadialScale_mul t hr]
  have hle : (1 - (t : ℝ)) * r + (t : ℝ) ≤ 1 := by
    have hrle : r ≤ 1 := x.1.2
    nlinarith [t.2.1, t.2.2]
  have hpos : 0 < (1 - (t : ℝ)) * r + (t : ℝ) := by
    by_cases ht : (t : ℝ) = 1
    · simp [ht]
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (sub_pos.mpr (lt_of_le_of_ne t.2.2 ht)) hr) t.2.1
  have hne : (⟨puncturedClosedCellRadialScale t r •
      (x.1 : EuclideanSpace ℝ (Fin n)), hnorm.trans_le hle⟩ : ClosedCell n) ≠
      closedCellCenter n := by
    intro hx
    have hzero : ‖puncturedClosedCellRadialScale t r •
        (x.1 : EuclideanSpace ℝ (Fin n))‖ = 0 := by
      simpa [closedCellCenter] using congrArg norm (congrArg Subtype.val hx)
    exact (ne_of_gt hpos) (hnorm.symm.trans hzero)
  exact ⟨⟨puncturedClosedCellRadialScale t r •
    (x.1 : EuclideanSpace ℝ (Fin n)), hnorm.trans_le hle⟩,
      hne⟩

@[simp]
theorem puncturedClosedCellRadialExpansion_zero (n : ℕ)
    (x : PuncturedClosedCell n) :
    puncturedClosedCellRadialExpansion n 0 x = x := by
  apply Subtype.ext
  apply Subtype.ext
  simp [puncturedClosedCellRadialExpansion, puncturedClosedCellRadialScale]

theorem puncturedClosedCellRadialExpansion_boundary (n : ℕ)
    (t : unitInterval) {x : PuncturedClosedCell n}
    (hx : x ∈ puncturedClosedCellBoundary n) :
    puncturedClosedCellRadialExpansion n t x = x := by
  apply Subtype.ext
  apply Subtype.ext
  change puncturedClosedCellRadialScale t
      ‖(x.1 : EuclideanSpace ℝ (Fin n))‖ •
        (x.1 : EuclideanSpace ℝ (Fin n)) = x.1
  rw [hx]
  simp [puncturedClosedCellRadialScale]

theorem puncturedClosedCellRadialExpansion_one_mem_boundary (n : ℕ)
    (x : PuncturedClosedCell n) :
    puncturedClosedCellRadialExpansion n 1 x ∈
      puncturedClosedCellBoundary n := by
  let r := ‖(x.1 : EuclideanSpace ℝ (Fin n))‖
  have hr : 0 < r := norm_pos_iff.mpr fun hx => x.2 (Subtype.ext hx)
  change ‖puncturedClosedCellRadialScale 1 r •
      (x.1 : EuclideanSpace ℝ (Fin n))‖ = 1
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (puncturedClosedCellRadialScale_nonneg 1 hr),
    puncturedClosedCellRadialScale_mul 1 hr]
  norm_num

theorem continuous_puncturedClosedCellRadialExpansion (n : ℕ) :
    Continuous (fun p : unitInterval × PuncturedClosedCell n =>
      puncturedClosedCellRadialExpansion n p.1 p.2) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  have hval : Continuous (fun p : unitInterval × PuncturedClosedCell n =>
      (p.2.1 : EuclideanSpace ℝ (Fin n))) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  have hnorm : Continuous (fun p : unitInterval × PuncturedClosedCell n =>
      ‖(p.2.1 : EuclideanSpace ℝ (Fin n))‖) := continuous_norm.comp hval
  have hnorm_ne : ∀ p : unitInterval × PuncturedClosedCell n,
      ‖(p.2.1 : EuclideanSpace ℝ (Fin n))‖ ≠ 0 := fun p =>
    norm_ne_zero_iff.mpr fun hx => p.2.2 (Subtype.ext hx)
  have hscale : Continuous (fun p : unitInterval × PuncturedClosedCell n =>
      puncturedClosedCellRadialScale p.1
        ‖(p.2.1 : EuclideanSpace ℝ (Fin n))‖) :=
    (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
      ((continuous_subtype_val.comp continuous_fst).mul (hnorm.inv₀ hnorm_ne))
  exact hscale.smul hval

noncomputable def puncturedClosedCellStrongDeformationRetract (n : ℕ) :
    Homotopy.StrongDeformationRetract (puncturedClosedCellBoundary n) where
  retraction := ⟨fun x => ⟨puncturedClosedCellRadialExpansion n 1 x,
    puncturedClosedCellRadialExpansion_one_mem_boundary n x⟩,
      Continuous.subtype_mk
        ((continuous_puncturedClosedCellRadialExpansion n).comp
          (continuous_const.prodMk continuous_id)) _⟩
  homotopy := {
    toHomotopy := {
      toContinuousMap := ⟨fun p => puncturedClosedCellRadialExpansion n p.1 p.2,
        continuous_puncturedClosedCellRadialExpansion n⟩
      map_zero_left := puncturedClosedCellRadialExpansion_zero n
      map_one_left := by
        intro x
        rfl
    }
    prop' := by
      intro t x hx
      exact puncturedClosedCellRadialExpansion_boundary n t hx
  }

noncomputable def puncturedClosedCellBoundaryHomeomorph (n : ℕ) :
    puncturedClosedCellBoundary n ≃ₜ CellBoundary n where
  toFun x := ⟨(x.1.1 : EuclideanSpace ℝ (Fin n)), x.2⟩
  invFun x := ⟨⟨⟨x, x.2.le⟩, by
    intro h
    have hzero : ‖(x : EuclideanSpace ℝ (Fin n))‖ = 0 := by
      simpa [closedCellCenter] using congrArg norm (congrArg Subtype.val h)
    exact one_ne_zero (x.2.symm.trans hzero)⟩, x.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl
  continuous_toFun := Continuous.subtype_mk
    (continuous_subtype_val.comp
      (continuous_subtype_val.comp continuous_subtype_val)) _
  continuous_invFun := Continuous.subtype_mk
    (Continuous.subtype_mk
      (Continuous.subtype_mk continuous_subtype_val _) _) _

noncomputable def cellBoundaryTwoHomeomorphCircle : CellBoundary 2 ≃ₜ Circle := by
  let e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ :=
    Complex.orthonormalBasisOneI.repr.symm
  exact {
    toFun := fun x => ⟨e x, by
      change dist (e x) 0 = 1
      rw [dist_zero_right, e.norm_map, x.2]⟩
    invFun := fun x => ⟨e.symm x, by
      exact (e.symm.norm_map x).trans (Circle.norm_coe x)⟩
    left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
    right_inv := fun x => Subtype.ext (e.apply_symm_apply x)
    continuous_toFun := Continuous.subtype_mk
      (e.continuous.comp continuous_subtype_val) (fun x => by
        change dist (e x) 0 = 1
        rw [dist_zero_right, e.norm_map, x.2])
    continuous_invFun := Continuous.subtype_mk
      (e.symm.continuous.comp continuous_subtype_val) (fun x => by
        exact (e.symm.norm_map x).trans (Circle.norm_coe x))
  }

noncomputable def puncturedClosedCellTwoHomotopyEquivCircle :
    PuncturedClosedCell 2 ≃ₕ Circle :=
  (puncturedClosedCellStrongDeformationRetract 2).toHomotopyEquiv |>.trans
    (puncturedClosedCellBoundaryHomeomorph 2).toHomotopyEquiv |>.trans
      cellBoundaryTwoHomeomorphCircle.toHomotopyEquiv

noncomputable def puncturedClosedCellTwoFundamentalGroupEquivInt
    (x : PuncturedClosedCell 2) :
    FundamentalGroup (PuncturedClosedCell 2) x ≃* Multiplicative ℤ :=
  (fundamentalGroupMulEquivOfHomotopyEquiv
      puncturedClosedCellTwoHomotopyEquivCircle x
      (puncturedClosedCellTwoHomotopyEquivCircle x) rfl).trans
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
      (puncturedClosedCellTwoHomotopyEquivCircle x) (1 : Circle)) |>.trans
      fundamentalGroupCircleEquivInt

noncomputable def puncturedClosedCellTwoFundamentalGroupGenerator
    (x : PuncturedClosedCell 2) : FundamentalGroup (PuncturedClosedCell 2) x :=
  (puncturedClosedCellTwoFundamentalGroupEquivInt x).symm
    (Multiplicative.ofAdd (1 : ℤ))

theorem fundamentalGroup_puncturedClosedCell_two_mem_zpowers
    (x : PuncturedClosedCell 2)
    (a : FundamentalGroup (PuncturedClosedCell 2) x) :
    a ∈ Subgroup.zpowers
      (puncturedClosedCellTwoFundamentalGroupGenerator x) := by
  let e := puncturedClosedCellTwoFundamentalGroupEquivInt x
  refine Subgroup.mem_zpowers_iff.mpr
    ⟨Multiplicative.toAdd (e a), ?_⟩
  apply e.injective
  rw [map_zpow]
  have hgenerator : e (puncturedClosedCellTwoFundamentalGroupGenerator x) =
      Multiplicative.ofAdd (1 : ℤ) := by
    exact e.apply_symm_apply _
  rw [hgenerator]
  exact Multiplicative.toAdd.injective (by simp)

abbrev PuncturedCellInterior (n : ℕ) :=
  {x : CellInterior n // (x.1 : EuclideanSpace ℝ (Fin n)) ≠ 0}

abbrev cellRadiusInterval := Set.Ioo (0 : ℝ) 1

noncomputable def puncturedCellInteriorToBoundaryRadius (n : ℕ) :
    PuncturedCellInterior n → CellBoundary n × cellRadiusInterval :=
  fun x => (Homotopy.boundaryNormalize
    (x.1 : EuclideanSpace ℝ (Fin n)) x.2,
      ⟨‖(x.1 : EuclideanSpace ℝ (Fin n))‖,
        norm_pos_iff.mpr x.2, x.1.2⟩)

theorem continuous_puncturedCellInteriorToBoundaryRadius (n : ℕ) :
    Continuous (puncturedCellInteriorToBoundaryRadius n) := by
  have hval : Continuous (fun x : PuncturedCellInterior n =>
      (x.1 : EuclideanSpace ℝ (Fin n))) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hnorm : Continuous (fun x : PuncturedCellInterior n =>
      ‖(x.1 : EuclideanSpace ℝ (Fin n))‖) := continuous_norm.comp hval
  have hnormalize : Continuous (fun x : PuncturedCellInterior n =>
      Homotopy.boundaryNormalize
        (x.1 : EuclideanSpace ℝ (Fin n)) x.2) := by
    apply Continuous.subtype_mk
    exact (Continuous.inv₀ hnorm (fun x => norm_ne_zero_iff.mpr x.2)).smul hval
  exact hnormalize.prodMk (Continuous.subtype_mk hnorm _)

noncomputable def boundaryRadiusToPuncturedCellInterior (n : ℕ) :
    CellBoundary n × cellRadiusInterval → PuncturedCellInterior n :=
  fun p => ⟨⟨(p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin n)), by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos p.2.2.1, p.1.2, mul_one]
    exact p.2.2.2⟩, by
      rw [smul_ne_zero_iff]
      exact ⟨p.2.2.1.ne', fun h => one_ne_zero (p.1.2.symm.trans (by
        simpa using congrArg norm h))⟩⟩

theorem continuous_boundaryRadiusToPuncturedCellInterior (n : ℕ) :
    Continuous (boundaryRadiusToPuncturedCellInterior n) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_snd).smul
    (continuous_subtype_val.comp continuous_fst)

theorem boundaryRadiusToPuncturedCellInterior_leftInverse (n : ℕ) :
    Function.LeftInverse (boundaryRadiusToPuncturedCellInterior n)
      (puncturedCellInteriorToBoundaryRadius n) := by
  intro x
  apply Subtype.ext
  apply Subtype.ext
  exact Homotopy.smul_boundaryNormalize _ x.2

theorem boundaryRadiusToPuncturedCellInterior_rightInverse (n : ℕ) :
    Function.RightInverse (boundaryRadiusToPuncturedCellInterior n)
      (puncturedCellInteriorToBoundaryRadius n) := by
  intro p
  apply Prod.ext
  · apply Subtype.ext
    change ‖(p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin n))‖⁻¹ •
        ((p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin n))) = p.1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos p.2.2.1, p.1.2,
      mul_one, smul_smul, inv_mul_cancel₀ p.2.2.1.ne', one_smul]
  · apply Subtype.ext
    change ‖(p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin n))‖ = p.2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos p.2.2.1, p.1.2, mul_one]

noncomputable def puncturedCellInteriorHomeomorphBoundaryRadius (n : ℕ) :
    PuncturedCellInterior n ≃ₜ CellBoundary n × cellRadiusInterval where
  toFun := puncturedCellInteriorToBoundaryRadius n
  invFun := boundaryRadiusToPuncturedCellInterior n
  left_inv := boundaryRadiusToPuncturedCellInterior_leftInverse n
  right_inv := boundaryRadiusToPuncturedCellInterior_rightInverse n
  continuous_toFun := continuous_puncturedCellInteriorToBoundaryRadius n
  continuous_invFun := continuous_boundaryRadiusToPuncturedCellInterior n

noncomputable def prodHomotopyEquivLeftOfContractible
    (A B : Type*) [TopologicalSpace A] [TopologicalSpace B] [ContractibleSpace B] :
    A × B ≃ₕ A :=
  ((ContinuousMap.HomotopyEquiv.refl A).prodCongr
      (ContractibleSpace.hequiv_unit B).some).trans
    (Homeomorph.prodUnique A Unit).toHomotopyEquiv

noncomputable def puncturedCellInteriorTwoHomotopyEquivCircle :
    PuncturedCellInterior 2 ≃ₕ Circle := by
  let _ : ContractibleSpace cellRadiusInterval :=
    (convex_Ioo (0 : ℝ) 1).contractibleSpace
      ⟨(1 / 2 : ℝ), by norm_num⟩
  exact (puncturedCellInteriorHomeomorphBoundaryRadius 2).toHomotopyEquiv |>.trans
    (prodHomotopyEquivLeftOfContractible (CellBoundary 2) cellRadiusInterval) |>.trans
      cellBoundaryTwoHomeomorphCircle.toHomotopyEquiv

noncomputable def puncturedCellInteriorTwoFundamentalGroupEquivInt
    (x : PuncturedCellInterior 2) :
    FundamentalGroup (PuncturedCellInterior 2) x ≃* Multiplicative ℤ :=
  (fundamentalGroupMulEquivOfHomotopyEquiv
      puncturedCellInteriorTwoHomotopyEquivCircle x
      (puncturedCellInteriorTwoHomotopyEquivCircle x) rfl).trans
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
      (puncturedCellInteriorTwoHomotopyEquivCircle x) (1 : Circle)) |>.trans
      fundamentalGroupCircleEquivInt

noncomputable def puncturedCellInteriorTwoFundamentalGroupGenerator
    (x : PuncturedCellInterior 2) : FundamentalGroup (PuncturedCellInterior 2) x :=
  (puncturedCellInteriorTwoFundamentalGroupEquivInt x).symm
    (Multiplicative.ofAdd (1 : ℤ))

theorem fundamentalGroup_puncturedCellInterior_two_mem_zpowers
    (x : PuncturedCellInterior 2)
    (a : FundamentalGroup (PuncturedCellInterior 2) x) :
    a ∈ Subgroup.zpowers
      (puncturedCellInteriorTwoFundamentalGroupGenerator x) := by
  let e := puncturedCellInteriorTwoFundamentalGroupEquivInt x
  refine Subgroup.mem_zpowers_iff.mpr
    ⟨Multiplicative.toAdd (e a), ?_⟩
  apply e.injective
  rw [map_zpow]
  have hgenerator : e (puncturedCellInteriorTwoFundamentalGroupGenerator x) =
      Multiplicative.ofAdd (1 : ℤ) := by
    exact e.apply_symm_apply _
  rw [hgenerator]
  exact Multiplicative.toAdd.injective (by simp)

abbrev AttachedCellUnion {Y : Type*} (X D : Set Y) := ↑(X ∪ D)

def attachedCellCenter {Y : Type*} [TopologicalSpace Y] {X D : Set Y} {n : ℕ}
    (e : ClosedCell n ≃ₜ D) : AttachedCellUnion X D :=
  ⟨e (closedCellCenter n), Or.inr (e (closedCellCenter n)).2⟩

def attachedCellOuter {Y : Type*} [TopologicalSpace Y] {X D : Set Y} {n : ℕ}
    (e : ClosedCell n ≃ₜ D) : Set (AttachedCellUnion X D) :=
  {y | y ≠ attachedCellCenter e}

def attachedCellInner {Y : Type*} (X D : Set Y) :
    Set (AttachedCellUnion X D) :=
  {y | (y : Y) ∉ X}

theorem isOpen_attachedCellOuter {Y : Type*} [TopologicalSpace Y] [T1Space Y]
    {X D : Set Y} {n : ℕ} (e : ClosedCell n ≃ₜ D) :
    IsOpen (attachedCellOuter (X := X) e) := by
  change IsOpen ({attachedCellCenter (X := X) e}ᶜ : Set (AttachedCellUnion X D))
  exact isOpen_compl_singleton

theorem isOpen_attachedCellInner {Y : Type*} [TopologicalSpace Y]
    {X D : Set Y} (hX : IsClosed X) : IsOpen (attachedCellInner X D) := by
  change IsOpen (Subtype.val ⁻¹' Xᶜ)
  exact hX.isOpen_compl.preimage continuous_subtype_val

noncomputable def attachedCellInnerHomeomorphCellInterior
    {Y : Type*} [TopologicalSpace Y] {X D : Set Y} {n : ℕ}
    (e : ClosedCell n ≃ₜ D)
    (hboundary : ∀ d : ClosedCell n, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin n))‖ = 1) :
    attachedCellInner X D ≃ₜ CellInterior n where
  toFun y := by
    have hyD : (y.1 : Y) ∈ D := y.1.2.resolve_left y.2
    let d : ClosedCell n := e.symm ⟨y.1, hyD⟩
    have hdne : ‖(d : EuclideanSpace ℝ (Fin n))‖ ≠ 1 := by
      intro hd
      have hdX : (e d : Y) ∈ X := (hboundary d).2 hd
      have heq : (e d : Y) = y.1 :=
        congrArg Subtype.val (e.apply_symm_apply ⟨y.1, hyD⟩)
      exact y.2 (heq ▸ hdX)
    exact ⟨d, lt_of_le_of_ne d.2 hdne⟩
  invFun d := by
    let c : ClosedCell n := ⟨d, d.2.le⟩
    have hcX : (e c : Y) ∉ X := by
      intro h
      have hnorm := (hboundary c).1 h
      exact (ne_of_lt d.2) hnorm
    exact ⟨⟨e c, Or.inr (e c).2⟩, hcX⟩
  left_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp
    exact congrArg Subtype.val (e.apply_symm_apply
      ⟨y.1, y.1.2.resolve_left y.2⟩)
  right_inv d := by
    apply Subtype.ext
    dsimp
    let c : ClosedCell n := ⟨d, d.2.le⟩
    have harg : (⟨(e c : Y), (e c).2⟩ : D) = e c := Subtype.ext rfl
    rw [harg, e.symm_apply_apply]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (e.symm.continuous.comp
      (Continuous.subtype_mk
        (continuous_subtype_val.comp continuous_subtype_val) _))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (e.continuous.comp
      (Continuous.subtype_mk continuous_subtype_val _))

theorem contractibleSpace_attachedCellInner
    {Y : Type*} [TopologicalSpace Y] {X D : Set Y} {n : ℕ}
    (e : ClosedCell n ≃ₜ D)
    (hboundary : ∀ d : ClosedCell n, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin n))‖ = 1) :
    ContractibleSpace (attachedCellInner X D) := by
  let hball : ContractibleSpace (Metric.ball
      (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    Metric.contractibleSpace_ball (by norm_num)
  let _ := hball
  let hcell : CellInterior n ≃ₜ Metric.ball
      (0 : EuclideanSpace ℝ (Fin n)) 1 := Homeomorph.setCongr (by
    ext x
    change ‖x‖ < 1 ↔ dist x 0 < 1
    rw [dist_zero_right])
  let _ : ContractibleSpace (CellInterior n) := hcell.contractibleSpace
  exact (attachedCellInnerHomeomorphCellInterior e hboundary).contractibleSpace

noncomputable def attachedCellOverlapHomeomorphPuncturedCellInterior
    {Y : Type*} [TopologicalSpace Y] {X D : Set Y} {n : ℕ}
    (e : ClosedCell n ≃ₜ D)
    (hboundary : ∀ d : ClosedCell n, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin n))‖ = 1) :
    ↑(attachedCellOuter (X := X) e ∩ attachedCellInner X D) ≃ₜ
      PuncturedCellInterior n where
  toFun y := by
    let h := attachedCellInnerHomeomorphCellInterior e hboundary
    let y' : attachedCellInner X D := ⟨y.1, y.2.2⟩
    refine ⟨h y', ?_⟩
    have hyD : (y.1 : Y) ∈ D := y.1.2.resolve_left y.2.2
    let d : ClosedCell n := e.symm ⟨y.1, hyD⟩
    change (d : EuclideanSpace ℝ (Fin n)) ≠ 0
    intro hd
    have hdcenter : d = closedCellCenter n := Subtype.ext hd
    apply y.2.1
    apply Subtype.ext
    calc
      (y.1 : Y) = e d :=
        (congrArg Subtype.val (e.apply_symm_apply ⟨y.1, hyD⟩)).symm
      _ = e (closedCellCenter n) := congrArg (fun z => (e z : Y)) hdcenter
  invFun z := by
    let h := attachedCellInnerHomeomorphCellInterior e hboundary
    let y : attachedCellInner X D := h.symm z.1
    have hyouter : y.1 ∈ attachedCellOuter (X := X) e := by
      intro hy
      have heq : (e (⟨z.1, z.1.2.le⟩ : ClosedCell n) : Y) =
          e (closedCellCenter n) := by
        simpa [h, y, attachedCellInnerHomeomorphCellInterior,
          attachedCellCenter] using congrArg Subtype.val hy
      have hc : (⟨z.1, z.1.2.le⟩ : ClosedCell n) = closedCellCenter n := by
        apply e.injective
        exact Subtype.ext heq
      exact z.2 (congrArg Subtype.val hc)
    exact ⟨y.1, ⟨hyouter, y.2⟩⟩
  left_inv y := by
    apply Subtype.ext
    let h := attachedCellInnerHomeomorphCellInterior e hboundary
    have hh := h.symm_apply_apply (⟨y.1, y.2.2⟩ : attachedCellInner X D)
    exact congrArg (fun z : attachedCellInner X D => z.1) hh
  right_inv z := by
    apply Subtype.ext
    let h := attachedCellInnerHomeomorphCellInterior e hboundary
    dsimp
    have harg : (⟨(h.symm z.1).1, (h.symm z.1).2⟩ : attachedCellInner X D) =
        h.symm z.1 := Subtype.ext rfl
    rw [harg, h.apply_symm_apply]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (attachedCellInnerHomeomorphCellInterior e hboundary).continuous.comp
      (Continuous.subtype_mk continuous_subtype_val _)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp
      ((attachedCellInnerHomeomorphCellInterior e hboundary).symm.continuous.comp
        continuous_subtype_val)

theorem pathConnectedSpace_of_homotopyEquiv
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [PathConnectedSpace A] (e : A ≃ₕ B) : PathConnectedSpace B := by
  constructor
  · exact ⟨e (Classical.choice (inferInstance : Nonempty A))⟩
  · intro y₀ y₁
    obtain ⟨H⟩ := e.right_inv
    have h₀ : Joined y₀ (e (e.symm y₀)) := ⟨(H.evalAt y₀).symm⟩
    have hmid : Joined (e (e.symm y₀)) (e (e.symm y₁)) :=
      (PathConnectedSpace.joined (e.symm y₀) (e.symm y₁)).map e.continuous
    have h₁ : Joined (e (e.symm y₁)) y₁ := ⟨H.evalAt y₁⟩
    exact h₀.trans (hmid.trans h₁)

noncomputable def attachedCellOverlapTwoHomotopyEquivCircle
    {Y : Type*} [TopologicalSpace Y] {X D : Set Y}
    (e : ClosedCell 2 ≃ₜ D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1) :
    ↑(attachedCellOuter (X := X) e ∩ attachedCellInner X D) ≃ₕ Circle :=
  (attachedCellOverlapHomeomorphPuncturedCellInterior e hboundary).toHomotopyEquiv |>.trans
    puncturedCellInteriorTwoHomotopyEquivCircle

theorem pathConnectedSpace_attachedCellOverlap_two
    {Y : Type*} [TopologicalSpace Y] {X D : Set Y}
    (e : ClosedCell 2 ≃ₜ D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1) :
    PathConnectedSpace
      ↑(attachedCellOuter (X := X) e ∩ attachedCellInner X D) :=
  pathConnectedSpace_of_homotopyEquiv
    (attachedCellOverlapTwoHomotopyEquivCircle e hboundary).symm

noncomputable def attachedCellOverlapTwoFundamentalGroupEquivInt
    {Y : Type*} [TopologicalSpace Y] {X D : Set Y}
    (e : ClosedCell 2 ≃ₜ D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1)
    (x : ↑(attachedCellOuter (X := X) e ∩ attachedCellInner X D)) :
    FundamentalGroup
      ↑(attachedCellOuter (X := X) e ∩ attachedCellInner X D) x ≃*
        Multiplicative ℤ := by
  let _ : PathConnectedSpace Circle := inferInstance
  exact (fundamentalGroupMulEquivOfHomotopyEquiv
      (attachedCellOverlapTwoHomotopyEquivCircle e hboundary) x
      (attachedCellOverlapTwoHomotopyEquivCircle e hboundary x) rfl).trans
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
      (attachedCellOverlapTwoHomotopyEquivCircle e hboundary x) (1 : Circle)) |>.trans
      fundamentalGroupCircleEquivInt

noncomputable def attachedCellOverlapTwoFundamentalGroupGenerator
    {Y : Type*} [TopologicalSpace Y] {X D : Set Y}
    (e : ClosedCell 2 ≃ₜ D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1)
    (x : ↑(attachedCellOuter (X := X) e ∩ attachedCellInner X D)) :
    FundamentalGroup
      ↑(attachedCellOuter (X := X) e ∩ attachedCellInner X D) x :=
  (attachedCellOverlapTwoFundamentalGroupEquivInt e hboundary x).symm
    (Multiplicative.ofAdd (1 : ℤ))

theorem fundamentalGroup_attachedCellOverlap_two_mem_zpowers
    {Y : Type*} [TopologicalSpace Y] {X D : Set Y}
    (e : ClosedCell 2 ≃ₜ D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1)
    (x : ↑(attachedCellOuter (X := X) e ∩ attachedCellInner X D))
    (a : FundamentalGroup
      ↑(attachedCellOuter (X := X) e ∩ attachedCellInner X D) x) :
    a ∈ Subgroup.zpowers
      (attachedCellOverlapTwoFundamentalGroupGenerator e hboundary x) := by
  let q := attachedCellOverlapTwoFundamentalGroupEquivInt e hboundary x
  refine Subgroup.mem_zpowers_iff.mpr
    ⟨Multiplicative.toAdd (q a), ?_⟩
  apply q.injective
  rw [map_zpow]
  have hgenerator : q (attachedCellOverlapTwoFundamentalGroupGenerator e hboundary x) =
      Multiplicative.ofAdd (1 : ℤ) := by
    exact q.apply_symm_apply _
  rw [hgenerator]
  exact Multiplicative.toAdd.injective (by simp)

abbrev AttachedCellOuterDisk {Y : Type*} [TopologicalSpace Y]
    {X D : Set Y} {n : ℕ} (e : ClosedCell n ≃ₜ D) :=
  {y : attachedCellOuter (X := X) e // (y.1 : Y) ∈ D}

noncomputable def attachedCellOuterDiskHomeomorphPuncturedClosedCell
    {Y : Type*} [TopologicalSpace Y] {X D : Set Y} {n : ℕ}
    (e : ClosedCell n ≃ₜ D) :
    AttachedCellOuterDisk (X := X) e ≃ₜ PuncturedClosedCell n where
  toFun y := by
    let d : ClosedCell n := e.symm ⟨y.1.1, y.2⟩
    refine ⟨d, ?_⟩
    intro hd
    apply y.1.2
    apply Subtype.ext
    calc
      (y.1.1 : Y) = e d :=
        (congrArg Subtype.val (e.apply_symm_apply ⟨y.1.1, y.2⟩)).symm
      _ = e (closedCellCenter n) := congrArg (fun z => (e z : Y)) hd
  invFun d := by
    have houter : (⟨e d.1, Or.inr (e d.1).2⟩ : AttachedCellUnion X D) ∈
        attachedCellOuter (X := X) e := by
      intro h
      have heq : (e d.1 : Y) = e (closedCellCenter n) :=
        congrArg (fun z : AttachedCellUnion X D => (z : Y)) h
      exact d.2 (e.injective (Subtype.ext heq))
    exact ⟨⟨⟨e d.1, Or.inr (e d.1).2⟩, houter⟩, (e d.1).2⟩
  left_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    dsimp
    exact congrArg Subtype.val (e.apply_symm_apply ⟨y.1.1, y.2⟩)
  right_inv d := by
    apply Subtype.ext
    dsimp
    have harg : (⟨(e d.1 : Y), (e d.1).2⟩ : D) = e d.1 := Subtype.ext rfl
    rw [harg, e.symm_apply_apply]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact e.symm.continuous.comp (Continuous.subtype_mk
      (continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_subtype_val)) _)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp
      (e.continuous.comp continuous_subtype_val)

noncomputable def attachedCellOuterDiskRadialExpansion
    {Y : Type*} [TopologicalSpace Y] {X D : Set Y} {n : ℕ}
    (e : ClosedCell n ≃ₜ D) :
    unitInterval × AttachedCellOuterDisk (X := X) e →
      AttachedCellOuterDisk (X := X) e :=
  fun p => (attachedCellOuterDiskHomeomorphPuncturedClosedCell e).symm
    (puncturedClosedCellRadialExpansion n p.1
      (attachedCellOuterDiskHomeomorphPuncturedClosedCell e p.2))

theorem continuous_attachedCellOuterDiskRadialExpansion
    {Y : Type*} [TopologicalSpace Y] {X D : Set Y} {n : ℕ}
    (e : ClosedCell n ≃ₜ D) :
    Continuous (attachedCellOuterDiskRadialExpansion (X := X) e) := by
  exact (attachedCellOuterDiskHomeomorphPuncturedClosedCell e).symm.continuous.comp
    ((continuous_puncturedClosedCellRadialExpansion n).comp
      (continuous_fst.prodMk
        ((attachedCellOuterDiskHomeomorphPuncturedClosedCell e).continuous.comp
          continuous_snd)))

theorem attachedCellOuterDisk_parametrization
    {Y : Type*} [TopologicalSpace Y] {X D : Set Y} {n : ℕ}
    (e : ClosedCell n ≃ₜ D) (y : AttachedCellOuterDisk (X := X) e) :
    (y.1.1 : Y) = e
      (attachedCellOuterDiskHomeomorphPuncturedClosedCell e y).1 := by
  exact (congrArg Subtype.val (e.apply_symm_apply ⟨y.1.1, y.2⟩)).symm

theorem attachedCellOuterDiskRadialExpansion_eq_of_mem_base
    {Y : Type*} [TopologicalSpace Y] {X D : Set Y} {n : ℕ}
    (e : ClosedCell n ≃ₜ D)
    (hboundary : ∀ d : ClosedCell n, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin n))‖ = 1)
    (t : unitInterval) (y : AttachedCellOuterDisk (X := X) e)
    (hy : (y.1.1 : Y) ∈ X) :
    attachedCellOuterDiskRadialExpansion (X := X) e (t, y) = y := by
  let h := attachedCellOuterDiskHomeomorphPuncturedClosedCell (X := X) e
  apply h.injective
  dsimp [attachedCellOuterDiskRadialExpansion]
  rw [h.apply_symm_apply]
  apply puncturedClosedCellRadialExpansion_boundary
  change ‖((h y).1 : EuclideanSpace ℝ (Fin n))‖ = 1
  apply (hboundary (h y).1).1
  rw [← attachedCellOuterDisk_parametrization e y]
  exact hy

theorem attachedCellOuterDiskRadialExpansion_one_mem_base
    {Y : Type*} [TopologicalSpace Y] {X D : Set Y} {n : ℕ}
    (e : ClosedCell n ≃ₜ D)
    (hboundary : ∀ d : ClosedCell n, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin n))‖ = 1)
    (y : AttachedCellOuterDisk (X := X) e) :
    ((attachedCellOuterDiskRadialExpansion (X := X) e (1, y)).1.1 : Y) ∈ X := by
  let h := attachedCellOuterDiskHomeomorphPuncturedClosedCell (X := X) e
  let d := puncturedClosedCellRadialExpansion n 1 (h y)
  have hd : ‖(d.1 : EuclideanSpace ℝ (Fin n))‖ = 1 :=
    puncturedClosedCellRadialExpansion_one_mem_boundary n (h y)
  have hdX : (e d.1 : Y) ∈ X := (hboundary d.1).2 hd
  have hparam := attachedCellOuterDisk_parametrization e
    (attachedCellOuterDiskRadialExpansion (X := X) e (1, y))
  change ((attachedCellOuterDiskRadialExpansion (X := X) e (1, y)).1.1 : Y) ∈ X
  rw [hparam]
  have hcoord : h (attachedCellOuterDiskRadialExpansion (X := X) e (1, y)) = d := by
    exact h.apply_symm_apply d
  rw [hcoord]
  exact hdX

open Classical in
noncomputable def attachedCellOuterRadialExpansion
    {Y : Type*} [TopologicalSpace Y] {X D : Set Y} {n : ℕ}
    (e : ClosedCell n ≃ₜ D) :
    unitInterval × ↑(attachedCellOuter (X := X) e) →
      ↑(attachedCellOuter (X := X) e) :=
  fun p => if hp : (p.2.1 : Y) ∈ X then p.2 else
    (attachedCellOuterDiskRadialExpansion (X := X) e
      (p.1, ⟨p.2, p.2.1.2.resolve_left hp⟩)).1

theorem attachedCellOuterRadialExpansion_of_mem_base
    {Y : Type*} [TopologicalSpace Y] {X D : Set Y} {n : ℕ}
    (e : ClosedCell n ≃ₜ D) (t : unitInterval)
    (y : ↑(attachedCellOuter (X := X) e)) (hy : (y.1 : Y) ∈ X) :
    attachedCellOuterRadialExpansion (X := X) e (t, y) = y := by
  rw [attachedCellOuterRadialExpansion, dite_eq_left hy]

theorem attachedCellOuterRadialExpansion_of_mem_disk
    {Y : Type*} [TopologicalSpace Y] {X D : Set Y} {n : ℕ}
    (e : ClosedCell n ≃ₜ D)
    (hboundary : ∀ d : ClosedCell n, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin n))‖ = 1)
    (t : unitInterval) (y : ↑(attachedCellOuter (X := X) e))
    (hyD : (y.1 : Y) ∈ D) :
    attachedCellOuterRadialExpansion (X := X) e (t, y) =
      (attachedCellOuterDiskRadialExpansion (X := X) e (t, ⟨y, hyD⟩)).1 := by
  by_cases hyX : (y.1 : Y) ∈ X
  · rw [attachedCellOuterRadialExpansion_of_mem_base e t y hyX,
      attachedCellOuterDiskRadialExpansion_eq_of_mem_base e hboundary t ⟨y, hyD⟩ hyX]
  · rw [attachedCellOuterRadialExpansion, dite_eq_right hyX]

theorem continuous_attachedCellOuterRadialExpansion
    {Y : Type*} [TopologicalSpace Y] {X D : Set Y} {n : ℕ}
    (e : ClosedCell n ≃ₜ D) (hX : IsClosed X) (hD : IsClosed D)
    (hboundary : ∀ d : ClosedCell n, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin n))‖ = 1) :
    Continuous (attachedCellOuterRadialExpansion (X := X) e) := by
  let A : Set (unitInterval × ↑(attachedCellOuter (X := X) e)) :=
    {p | (p.2.1 : Y) ∈ X}
  let B : Set (unitInterval × ↑(attachedCellOuter (X := X) e)) :=
    {p | (p.2.1 : Y) ∈ D}
  have hA : IsClosed A := hX.preimage
    (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
  have hB : IsClosed B := hD.preimage
    (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
  have hAB : A ∪ B = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    exact p.2.1.2
  have hleft : ContinuousOn (attachedCellOuterRadialExpansion (X := X) e) A :=
    continuous_snd.continuousOn.congr fun p hp =>
      attachedCellOuterRadialExpansion_of_mem_base e p.1 p.2 hp
  have hright : ContinuousOn (attachedCellOuterRadialExpansion (X := X) e) B := by
    rw [continuousOn_iff_continuous_domRestrict]
    let j : B → unitInterval × AttachedCellOuterDisk (X := X) e :=
      fun p => (p.1.1, ⟨p.1.2, p.2⟩)
    have hj : Continuous j := continuous_fst.comp continuous_subtype_val |>.prodMk
      (Continuous.subtype_mk (continuous_snd.comp continuous_subtype_val) _)
    let g : B → ↑(attachedCellOuter (X := X) e) := fun p =>
      (attachedCellOuterDiskRadialExpansion (X := X) e (j p)).1
    have hg : Continuous g := continuous_subtype_val.comp
      ((continuous_attachedCellOuterDiskRadialExpansion (X := X) e).comp hj)
    apply hg.congr
    intro p
    exact (attachedCellOuterRadialExpansion_of_mem_disk e hboundary
      p.1.1 p.1.2 p.2).symm
  rw [← continuousOn_univ, ← hAB]
  exact hleft.union_of_isClosed hright hA hB

theorem attachedCellOuterDiskRadialExpansion_zero
    {Y : Type*} [TopologicalSpace Y] {X D : Set Y} {n : ℕ}
    (e : ClosedCell n ≃ₜ D) (y : AttachedCellOuterDisk (X := X) e) :
    attachedCellOuterDiskRadialExpansion (X := X) e (0, y) = y := by
  let h := attachedCellOuterDiskHomeomorphPuncturedClosedCell (X := X) e
  apply h.injective
  dsimp [attachedCellOuterDiskRadialExpansion]
  rw [h.apply_symm_apply, puncturedClosedCellRadialExpansion_zero]

@[simp]
theorem attachedCellOuterRadialExpansion_zero
    {Y : Type*} [TopologicalSpace Y] {X D : Set Y} {n : ℕ}
    (e : ClosedCell n ≃ₜ D) (y : ↑(attachedCellOuter (X := X) e)) :
    attachedCellOuterRadialExpansion (X := X) e (0, y) = y := by
  by_cases hy : (y.1 : Y) ∈ X
  · exact attachedCellOuterRadialExpansion_of_mem_base e 0 y hy
  · rw [attachedCellOuterRadialExpansion, dite_eq_right hy]
    exact congrArg Subtype.val
      (attachedCellOuterDiskRadialExpansion_zero e
        (⟨y, y.1.2.resolve_left hy⟩ : AttachedCellOuterDisk (X := X) e))

def attachedCellOuterBase {Y : Type*} [TopologicalSpace Y]
    {X D : Set Y} {n : ℕ} (e : ClosedCell n ≃ₜ D) :
    Set ↑(attachedCellOuter (X := X) e) :=
  {y | (y.1 : Y) ∈ X}

theorem attachedCellOuterRadialExpansion_one_mem_base
    {Y : Type*} [TopologicalSpace Y] {X D : Set Y} {n : ℕ}
    (e : ClosedCell n ≃ₜ D)
    (hboundary : ∀ d : ClosedCell n, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin n))‖ = 1)
    (y : ↑(attachedCellOuter (X := X) e)) :
    attachedCellOuterRadialExpansion (X := X) e (1, y) ∈
      attachedCellOuterBase e := by
  by_cases hy : (y.1 : Y) ∈ X
  · rw [attachedCellOuterRadialExpansion_of_mem_base e 1 y hy]
    exact hy
  · rw [attachedCellOuterRadialExpansion_of_mem_disk e hboundary 1 y
      (y.1.2.resolve_left hy)]
    exact attachedCellOuterDiskRadialExpansion_one_mem_base e hboundary
      ⟨y, y.1.2.resolve_left hy⟩

noncomputable def attachedCellOuterStrongDeformationRetract
    {Y : Type*} [TopologicalSpace Y] {X D : Set Y} {n : ℕ}
    (e : ClosedCell n ≃ₜ D) (hX : IsClosed X) (hD : IsClosed D)
    (hboundary : ∀ d : ClosedCell n, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin n))‖ = 1) :
    Homotopy.StrongDeformationRetract (attachedCellOuterBase (X := X) e) where
  retraction := ⟨fun y => ⟨attachedCellOuterRadialExpansion (X := X) e (1, y),
    attachedCellOuterRadialExpansion_one_mem_base e hboundary y⟩,
      Continuous.subtype_mk
        ((continuous_attachedCellOuterRadialExpansion e hX hD hboundary).comp
          (continuous_const.prodMk continuous_id)) _⟩
  homotopy := {
    toHomotopy := {
      toContinuousMap := ⟨attachedCellOuterRadialExpansion (X := X) e,
        continuous_attachedCellOuterRadialExpansion e hX hD hboundary⟩
      map_zero_left := attachedCellOuterRadialExpansion_zero e
      map_one_left := by
        intro y
        rfl
    }
    prop' := by
      intro t y hy
      exact attachedCellOuterRadialExpansion_of_mem_base e t y hy
  }

noncomputable def attachedCellOuterBaseHomeomorph
    {Y : Type*} [TopologicalSpace Y] {X D : Set Y} {n : ℕ}
    (e : ClosedCell n ≃ₜ D)
    (hboundary : ∀ d : ClosedCell n, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin n))‖ = 1) :
    attachedCellOuterBase (X := X) e ≃ₜ X where
  toFun y := ⟨y.1.1, y.2⟩
  invFun x := by
    have hxcenter : (⟨x, Or.inl x.2⟩ : AttachedCellUnion X D) ≠
        attachedCellCenter e := by
      intro h
      have hcenterX : (e (closedCellCenter n) : Y) ∈ X := by
        have heq : (x : Y) = e (closedCellCenter n) :=
          congrArg (fun z : AttachedCellUnion X D => (z : Y)) h
        simpa [heq] using x.2
      have hnorm := (hboundary (closedCellCenter n)).1 hcenterX
      norm_num [closedCellCenter] at hnorm
    exact ⟨⟨⟨x, Or.inl x.2⟩, hxcenter⟩, x.2⟩
  left_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl
  continuous_toFun := Continuous.subtype_mk
    (continuous_subtype_val.comp
      (continuous_subtype_val.comp continuous_subtype_val)) _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val

noncomputable def attachedCellOuterHomotopyEquivBase
    {Y : Type*} [TopologicalSpace Y] {X D : Set Y} {n : ℕ}
    (e : ClosedCell n ≃ₜ D) (hX : IsClosed X) (hD : IsClosed D)
    (hboundary : ∀ d : ClosedCell n, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin n))‖ = 1) :
    ↑(attachedCellOuter (X := X) e) ≃ₕ X :=
  (attachedCellOuterStrongDeformationRetract e hX hD hboundary).toHomotopyEquiv |>.trans
    (attachedCellOuterBaseHomeomorph e hboundary).toHomotopyEquiv

theorem pathConnectedSpace_attachedCellOuter
    {Y : Type*} [TopologicalSpace Y] {X D : Set Y} {n : ℕ}
    [PathConnectedSpace X]
    (e : ClosedCell n ≃ₜ D) (hX : IsClosed X) (hD : IsClosed D)
    (hboundary : ∀ d : ClosedCell n, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin n))‖ = 1) :
    PathConnectedSpace ↑(attachedCellOuter (X := X) e) :=
  pathConnectedSpace_of_homotopyEquiv
    (attachedCellOuterHomotopyEquivBase e hX hD hboundary).symm

open Classical in
noncomputable def fundamentalGroupPathRepresentative
    {Z : Type*} [TopologicalSpace Z] {z : Z} (g : FundamentalGroup Z z) : Path z z :=
  Classical.choose (Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath g))

theorem fundamentalGroupPathRepresentative_mk
    {Z : Type*} [TopologicalSpace Z] {z : Z} (g : FundamentalGroup Z z) :
    Path.Homotopic.Quotient.mk (fundamentalGroupPathRepresentative g) =
      FundamentalGroup.toPath g :=
  Classical.choose_spec
    (Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath g))

open Classical in
noncomputable def fundamentalGroupBasedCircleRepresentative
    {Z : Type*} [TopologicalSpace Z] {z : Z} (g : FundamentalGroup Z z) :
    basedCircleLoop z :=
  basedPathCircleHomeomorph z (fundamentalGroupPathRepresentative g)

theorem fundamentalGroupBasedCircleRepresentative_mk
    {Z : Type*} [TopologicalSpace Z] {z : Z} (g : FundamentalGroup Z z) :
    Path.Homotopic.Quotient.mk
        (circleToPath (fundamentalGroupBasedCircleRepresentative g)) =
      FundamentalGroup.toPath g := by
  rw [show circleToPath (fundamentalGroupBasedCircleRepresentative g) =
      fundamentalGroupPathRepresentative g from
    (basedPathCircleHomeomorph z).left_inv _]
  exact fundamentalGroupPathRepresentative_mk g

open Classical in
noncomputable def attachedTwoCellKernelGeneratorLoop
    {Y : Type u} [TopologicalSpace Y] {X D : Set Y}
    (e : ClosedCell 2 ≃ₜ D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1)
    (x₀ : AttachedCellUnion X D)
    (hx₀ : x₀ ∈ attachedCellOuter (X := X) e ∩ attachedCellInner X D) :
    basedCircleLoop
      (VanKampen.leftBasepoint (attachedCellOuter (X := X) e) x₀ hx₀.1) :=
  fundamentalGroupBasedCircleRepresentative
    ((VanKampen.fundamentalGroupInterToLeft
      (attachedCellOuter (X := X) e) (attachedCellInner X D) x₀ hx₀).hom
      (attachedCellOverlapTwoFundamentalGroupGenerator e hboundary
        (VanKampen.overlapBasepoint
          (attachedCellOuter (X := X) e) (attachedCellInner X D) x₀ hx₀)))

theorem attachedTwoCellKernelGeneratorLoop_mk
    {Y : Type u} [TopologicalSpace Y] {X D : Set Y}
    (e : ClosedCell 2 ≃ₜ D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1)
    (x₀ : AttachedCellUnion X D)
    (hx₀ : x₀ ∈ attachedCellOuter (X := X) e ∩ attachedCellInner X D) :
    Path.Homotopic.Quotient.mk
        (circleToPath (attachedTwoCellKernelGeneratorLoop e hboundary x₀ hx₀)) =
      (VanKampen.fundamentalGroupInterToLeft
        (attachedCellOuter (X := X) e) (attachedCellInner X D) x₀ hx₀).hom
        (attachedCellOverlapTwoFundamentalGroupGenerator e hboundary
          (VanKampen.overlapBasepoint
            (attachedCellOuter (X := X) e) (attachedCellInner X D) x₀ hx₀)) := by
  exact fundamentalGroupBasedCircleRepresentative_mk _

open Classical in
noncomputable def attachedTwoCellGeometricGeneratorLoop
    {Y : Type u} [TopologicalSpace Y] {X D : Set Y}
    (e : ClosedCell 2 ≃ₜ D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1)
    (x₀ : AttachedCellUnion X D)
    (hx₀ : x₀ ∈ attachedCellOuter (X := X) e ∩ attachedCellInner X D) :
    basedCircleLoop
      ((VanKampen.interToLeft
        (attachedCellOuter (X := X) e) (attachedCellInner X D))
        (VanKampen.overlapBasepoint
          (attachedCellOuter (X := X) e) (attachedCellInner X D) x₀ hx₀)) where
  val := (VanKampen.interToLeft
    (attachedCellOuter (X := X) e) (attachedCellInner X D)).comp
      (fundamentalGroupBasedCircleRepresentative
        (attachedCellOverlapTwoFundamentalGroupGenerator e hboundary
          (VanKampen.overlapBasepoint
            (attachedCellOuter (X := X) e) (attachedCellInner X D) x₀ hx₀))).1
  property := by
    change (VanKampen.interToLeft
      (attachedCellOuter (X := X) e) (attachedCellInner X D))
        ((fundamentalGroupBasedCircleRepresentative
          (attachedCellOverlapTwoFundamentalGroupGenerator e hboundary
            (VanKampen.overlapBasepoint
              (attachedCellOuter (X := X) e) (attachedCellInner X D) x₀ hx₀))).1 0) = _
    rw [(fundamentalGroupBasedCircleRepresentative
      (attachedCellOverlapTwoFundamentalGroupGenerator e hboundary
        (VanKampen.overlapBasepoint
          (attachedCellOuter (X := X) e) (attachedCellInner X D) x₀ hx₀))).2]

theorem attachedTwoCellGeometricGeneratorLoop_mk_heq
    {Y : Type u} [TopologicalSpace Y] {X D : Set Y}
    (e : ClosedCell 2 ≃ₜ D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1)
    (x₀ : AttachedCellUnion X D)
    (hx₀ : x₀ ∈ attachedCellOuter (X := X) e ∩ attachedCellInner X D) :
    Path.Homotopic.Quotient.mk
        (circleToPath (attachedTwoCellGeometricGeneratorLoop e hboundary x₀ hx₀)) ≍
      (VanKampen.fundamentalGroupInterToLeft
        (attachedCellOuter (X := X) e) (attachedCellInner X D) x₀ hx₀).hom
        (attachedCellOverlapTwoFundamentalGroupGenerator e hboundary
          (VanKampen.overlapBasepoint
            (attachedCellOuter (X := X) e) (attachedCellInner X D) x₀ hx₀)) := by
  let z := attachedCellOverlapTwoFundamentalGroupGenerator e hboundary
    (VanKampen.overlapBasepoint
      (attachedCellOuter (X := X) e) (attachedCellInner X D) x₀ hx₀)
  let f := VanKampen.interToLeft
    (attachedCellOuter (X := X) e) (attachedCellInner X D)
  have hcircle :
      circleToPath (attachedTwoCellGeometricGeneratorLoop e hboundary x₀ hx₀) =
        (fundamentalGroupPathRepresentative z).map f.continuous := by
    apply Path.ext
    funext t
    change f (pathToCircle (fundamentalGroupPathRepresentative z)
      ((t : unitInterval).val : loopCircle)) = f (fundamentalGroupPathRepresentative z t)
    exact congrArg f (pathToCircle_coe (fundamentalGroupPathRepresentative z) t)
  have hmap : Path.Homotopic.Quotient.mk
        (circleToPath (attachedTwoCellGeometricGeneratorLoop e hboundary x₀ hx₀)) =
      FundamentalGroup.map f
        (VanKampen.overlapBasepoint
          (attachedCellOuter (X := X) e) (attachedCellInner X D) x₀ hx₀) z := by
    rw [hcircle, Path.Homotopic.Quotient.mk_map,
      fundamentalGroupPathRepresentative_mk]
    rfl
  exact (heq_of_eq hmap).trans
    (VanKampen.fundamentalGroup_mapOfEq_heq_map f
      (VanKampen.overlapBasepoint
        (attachedCellOuter (X := X) e) (attachedCellInner X D) x₀ hx₀)
      (VanKampen.leftBasepoint (attachedCellOuter (X := X) e) x₀ hx₀.1)
      (VanKampen.interToLeft_overlapBasepoint
        (attachedCellOuter (X := X) e) (attachedCellInner X D) x₀ hx₀) z).symm

open Classical in
noncomputable def attachedTwoCellRadialBoundaryLoop
    {Y : Type u} [TopologicalSpace Y] {X D : Set Y}
    (e : ClosedCell 2 ≃ₜ D) (hX : IsClosed X) (hD : IsClosed D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1)
    (x₀ : AttachedCellUnion X D)
    (hx₀ : x₀ ∈ attachedCellOuter (X := X) e ∩ attachedCellInner X D) :
    freeLoop ↑(attachedCellOuter (X := X) e) where
  toFun θ := attachedCellOuterRadialExpansion (X := X) e
    (1, (attachedTwoCellGeometricGeneratorLoop e hboundary x₀ hx₀).1 θ)
  continuous_toFun :=
    (continuous_attachedCellOuterRadialExpansion e hX hD hboundary).comp
      (continuous_const.prodMk
        (attachedTwoCellGeometricGeneratorLoop e hboundary x₀ hx₀).1.continuous)

theorem attachedTwoCellGeometricGeneratorLoop_homotopic_radialBoundary
    {Y : Type u} [TopologicalSpace Y] {X D : Set Y}
    (e : ClosedCell 2 ≃ₜ D) (hX : IsClosed X) (hD : IsClosed D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1)
    (x₀ : AttachedCellUnion X D)
    (hx₀ : x₀ ∈ attachedCellOuter (X := X) e ∩ attachedCellInner X D) :
    (attachedTwoCellGeometricGeneratorLoop e hboundary x₀ hx₀).1.Homotopic
      (attachedTwoCellRadialBoundaryLoop e hX hD hboundary x₀ hx₀) := by
  refine ⟨⟨⟨fun z : unitInterval × loopCircle =>
    attachedCellOuterRadialExpansion (X := X) e
      (z.1, (attachedTwoCellGeometricGeneratorLoop e hboundary x₀ hx₀).1 z.2),
    (continuous_attachedCellOuterRadialExpansion e hX hD hboundary).comp
      (continuous_fst.prodMk
        ((attachedTwoCellGeometricGeneratorLoop e hboundary x₀ hx₀).1.continuous.comp
          continuous_snd))⟩, ?_, ?_⟩⟩
  · intro θ
    exact attachedCellOuterRadialExpansion_zero e _
  · intro θ
    rfl

open Classical in
noncomputable def attachedTwoCellRadialBoundaryLoopInBase
    {Y : Type u} [TopologicalSpace Y] {X D : Set Y}
    (e : ClosedCell 2 ≃ₜ D) (hX : IsClosed X) (hD : IsClosed D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1)
    (x₀ : AttachedCellUnion X D)
    (hx₀ : x₀ ∈ attachedCellOuter (X := X) e ∩ attachedCellInner X D) :
    freeLoop (attachedCellOuterBase (X := X) e) where
  toFun θ := ⟨attachedTwoCellRadialBoundaryLoop e hX hD hboundary x₀ hx₀ θ,
    attachedCellOuterRadialExpansion_one_mem_base e hboundary _⟩
  continuous_toFun := Continuous.subtype_mk
    (attachedTwoCellRadialBoundaryLoop e hX hD hboundary x₀ hx₀).continuous _

open Classical in
noncomputable def attachedTwoCellBoundaryLoop
    {Y : Type u} [TopologicalSpace Y] {X D : Set Y}
    (e : ClosedCell 2 ≃ₜ D) (hX : IsClosed X) (hD : IsClosed D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1)
    (x₀ : AttachedCellUnion X D)
    (hx₀ : x₀ ∈ attachedCellOuter (X := X) e ∩ attachedCellInner X D) :
    freeLoop X :=
  FreeLoop.postcompose
    ⟨attachedCellOuterBaseHomeomorph e hboundary,
      (attachedCellOuterBaseHomeomorph e hboundary).continuous⟩
    (attachedTwoCellRadialBoundaryLoopInBase e hX hD hboundary x₀ hx₀)

open Classical in
noncomputable def attachedCellBaseToOuter
    {Y : Type u} [TopologicalSpace Y] {X D : Set Y} {n : ℕ}
    (e : ClosedCell n ≃ₜ D)
    (hboundary : ∀ d : ClosedCell n, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin n))‖ = 1) :
    C(X, ↑(attachedCellOuter (X := X) e)) :=
  ⟨fun x => ((attachedCellOuterBaseHomeomorph e hboundary).symm x).1,
    continuous_subtype_val.comp
      (attachedCellOuterBaseHomeomorph e hboundary).symm.continuous⟩

theorem attachedTwoCellBoundaryLoop_postcompose_baseToOuter
    {Y : Type u} [TopologicalSpace Y] {X D : Set Y}
    (e : ClosedCell 2 ≃ₜ D) (hX : IsClosed X) (hD : IsClosed D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1)
    (x₀ : AttachedCellUnion X D)
    (hx₀ : x₀ ∈ attachedCellOuter (X := X) e ∩ attachedCellInner X D) :
    FreeLoop.postcompose (attachedCellBaseToOuter e hboundary)
        (attachedTwoCellBoundaryLoop e hX hD hboundary x₀ hx₀) =
      attachedTwoCellRadialBoundaryLoop e hX hD hboundary x₀ hx₀ := by
  ext θ
  exact congrArg
    (fun y : attachedCellOuterBase (X := X) e => ((y.1.1 : AttachedCellUnion X D) : Y))
    ((attachedCellOuterBaseHomeomorph e hboundary).symm_apply_apply
      ((attachedTwoCellRadialBoundaryLoopInBase e hX hD hboundary x₀ hx₀) θ))

theorem attachedTwoCellGeometricGeneratorLoop_homotopic_boundaryLoop
    {Y : Type u} [TopologicalSpace Y] {X D : Set Y}
    (e : ClosedCell 2 ≃ₜ D) (hX : IsClosed X) (hD : IsClosed D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1)
    (x₀ : AttachedCellUnion X D)
    (hx₀ : x₀ ∈ attachedCellOuter (X := X) e ∩ attachedCellInner X D) :
    (attachedTwoCellGeometricGeneratorLoop e hboundary x₀ hx₀).1.Homotopic
      (FreeLoop.postcompose (attachedCellBaseToOuter e hboundary)
        (attachedTwoCellBoundaryLoop e hX hD hboundary x₀ hx₀)) := by
  rw [attachedTwoCellBoundaryLoop_postcompose_baseToOuter]
  exact attachedTwoCellGeometricGeneratorLoop_homotopic_radialBoundary
    e hX hD hboundary x₀ hx₀

theorem attachedTwoCellBoundaryLoop_mem_attached_cell
    {Y : Type u} [TopologicalSpace Y] {X D : Set Y}
    (e : ClosedCell 2 ≃ₜ D) (hX : IsClosed X) (hD : IsClosed D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1)
    (x₀ : AttachedCellUnion X D)
    (hx₀ : x₀ ∈ attachedCellOuter (X := X) e ∩ attachedCellInner X D)
    (θ : loopCircle) :
    ((attachedTwoCellBoundaryLoop e hX hD hboundary x₀ hx₀ θ : X) : Y) ∈ D := by
  change ((attachedCellOuterRadialExpansion (X := X) e
    (1, (attachedTwoCellGeometricGeneratorLoop e hboundary x₀ hx₀).1 θ)).1 :
      AttachedCellUnion X D).1 ∈ D
  have hyD :
      (((attachedTwoCellGeometricGeneratorLoop e hboundary x₀ hx₀).1 θ).1 :
        AttachedCellUnion X D).1 ∈ D := by
    let y := (fundamentalGroupBasedCircleRepresentative
      (attachedCellOverlapTwoFundamentalGroupGenerator e hboundary
        (VanKampen.overlapBasepoint
          (attachedCellOuter (X := X) e) (attachedCellInner X D) x₀ hx₀))).1 θ
    exact y.1.2.resolve_left y.2.2
  by_cases hy :
      (((attachedTwoCellGeometricGeneratorLoop e hboundary x₀ hx₀).1 θ).1 :
        AttachedCellUnion X D).1 ∈ X
  · rw [attachedCellOuterRadialExpansion_of_mem_base e 1 _ hy]
    exact hyD
  · rw [attachedCellOuterRadialExpansion_of_mem_disk e hboundary 1 _ hyD]
    exact (e _).2

theorem attachedCellOuter_union_inner
    {Y : Type*} [TopologicalSpace Y] {X D : Set Y} {n : ℕ}
    (e : ClosedCell n ≃ₜ D)
    (hboundary : ∀ d : ClosedCell n, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin n))‖ = 1) :
    attachedCellOuter (X := X) e ∪ attachedCellInner X D = Set.univ := by
  ext y
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  by_cases hy : y = attachedCellCenter e
  · right
    change (y : Y) ∉ X
    rw [hy]
    intro hcenter
    have hnorm := (hboundary (closedCellCenter n)).1 hcenter
    norm_num [closedCellCenter] at hnorm
  · left
    change y ≠ attachedCellCenter e
    exact hy

open Classical in
theorem ker_fundamentalGroup_attachedCellOuterToUnion_eq_normalClosure
    {Y : Type u} [TopologicalSpace Y] [T1Space Y]
    {X D : Set Y} [PathConnectedSpace X]
    (e : ClosedCell 2 ≃ₜ D) (hX : IsClosed X) (hD : IsClosed D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1)
    (x₀ : AttachedCellUnion X D)
    (hx₀ : x₀ ∈ attachedCellOuter (X := X) e ∩ attachedCellInner X D) :
    MonoidHom.ker
        (VanKampen.fundamentalGroupLeftToAmbient
          (attachedCellOuter (X := X) e) x₀ hx₀.1).hom =
      Subgroup.normalClosure
        ({(VanKampen.fundamentalGroupInterToLeft
            (attachedCellOuter (X := X) e) (attachedCellInner X D) x₀ hx₀).hom
            (attachedCellOverlapTwoFundamentalGroupGenerator e hboundary
              (VanKampen.overlapBasepoint
                (attachedCellOuter (X := X) e) (attachedCellInner X D) x₀ hx₀))} :
          Set (FundamentalGroup (attachedCellOuter (X := X) e)
            (VanKampen.leftBasepoint (attachedCellOuter (X := X) e) x₀ hx₀.1))) := by
  let _ : PathConnectedSpace ↑(attachedCellOuter (X := X) e) :=
    pathConnectedSpace_attachedCellOuter e hX hD hboundary
  let _ : ContractibleSpace (attachedCellInner X D) :=
    contractibleSpace_attachedCellInner e hboundary
  let _ : SimplyConnectedSpace (attachedCellInner X D) := inferInstance
  let _ : PathConnectedSpace
      ↑(attachedCellOuter (X := X) e ∩ attachedCellInner X D) :=
    pathConnectedSpace_attachedCellOverlap_two e hboundary
  exact VanKampen.ker_fundamentalGroupLeftToAmbient_eq_normalClosure_singleton
    (attachedCellOuter (X := X) e) (attachedCellInner X D)
    (isOpen_attachedCellOuter e) (isOpen_attachedCellInner hX)
    (attachedCellOuter_union_inner e hboundary) x₀ hx₀
    (attachedCellOverlapTwoFundamentalGroupGenerator e hboundary
      (VanKampen.overlapBasepoint
        (attachedCellOuter (X := X) e) (attachedCellInner X D) x₀ hx₀))
    (fundamentalGroup_attachedCellOverlap_two_mem_zpowers e hboundary _)

open Classical in
theorem surjective_fundamentalGroup_attachedCellOuterToUnion
    {Y : Type u} [TopologicalSpace Y] [T1Space Y]
    {X D : Set Y} [PathConnectedSpace X]
    (e : ClosedCell 2 ≃ₜ D) (hX : IsClosed X) (hD : IsClosed D)
    (hboundary : ∀ d : ClosedCell 2, (e d : Y) ∈ X ↔
      ‖(d : EuclideanSpace ℝ (Fin 2))‖ = 1)
    (x₀ : AttachedCellUnion X D)
    (hx₀ : x₀ ∈ attachedCellOuter (X := X) e ∩ attachedCellInner X D) :
    Function.Surjective
      (VanKampen.fundamentalGroupLeftToAmbient
        (attachedCellOuter (X := X) e) x₀ hx₀.1).hom := by
  let _ : PathConnectedSpace ↑(attachedCellOuter (X := X) e) :=
    pathConnectedSpace_attachedCellOuter e hX hD hboundary
  let _ : ContractibleSpace (attachedCellInner X D) :=
    contractibleSpace_attachedCellInner e hboundary
  let _ : SimplyConnectedSpace (attachedCellInner X D) := inferInstance
  let _ : PathConnectedSpace
      ↑(attachedCellOuter (X := X) e ∩ attachedCellInner X D) :=
    pathConnectedSpace_attachedCellOverlap_two e hboundary
  exact VanKampen.surjective_fundamentalGroupLeftToAmbient
    (attachedCellOuter (X := X) e) (attachedCellInner X D)
    (isOpen_attachedCellOuter e) (isOpen_attachedCellInner hX)
    (attachedCellOuter_union_inner e hboundary) x₀ hx₀

end DifferentialGeometry.Topology
