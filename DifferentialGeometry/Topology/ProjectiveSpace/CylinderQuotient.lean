import DifferentialGeometry.Topology.Manifold.SphereOrthogonalAction
import DifferentialGeometry.Topology.Manifold.Quotient
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.ApplyFun
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

def cylinderAntipodal :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real →
      Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real :=
  fun x => (-x.1, x.2)

def cylinderDiagonal :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real →
      Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real :=
  fun x => (-x.1, -x.2)

private noncomputable def roundTwoSphereAntipodalDiffeomorph :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 ≃ₘ⟮𝓡 2, 𝓡 2⟯
      Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 := by
  let : Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) :=
    ⟨by simp⟩
  exact sphereDiffeo (n := 2) (LinearIsometryEquiv.neg Real)

noncomputable def cylinderAntipodalDiffeomorph :
    (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
      ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), (𝓡 2).prod 𝓘(Real, Real)⟯
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real :=
  roundTwoSphereAntipodalDiffeomorph.prodCongr
    (Diffeomorph.refl 𝓘(Real, Real) Real ∞)

noncomputable def cylinderDiagonalDiffeomorph :
    (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
      ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), (𝓡 2).prod 𝓘(Real, Real)⟯
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real :=
  roundTwoSphereAntipodalDiffeomorph.prodCongr
    (ContinuousLinearEquiv.neg Real).toDiffeomorph

theorem cylinderAntipodal_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderAntipodal x = (-x.1, x.2) := rfl

theorem cylinderDiagonal_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderDiagonal x = (-x.1, -x.2) := rfl

private theorem roundTwoSphereAntipodalDiffeomorph_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    roundTwoSphereAntipodalDiffeomorph x = -x := by
  apply Subtype.ext
  simp [roundTwoSphereAntipodalDiffeomorph]

theorem cylinderAntipodalDiffeomorph_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderAntipodalDiffeomorph x = cylinderAntipodal x := by
  apply Prod.ext
  · exact roundTwoSphereAntipodalDiffeomorph_apply x.1
  · rfl

theorem cylinderDiagonalDiffeomorph_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderDiagonalDiffeomorph x = cylinderDiagonal x := by
  apply Prod.ext
  · exact roundTwoSphereAntipodalDiffeomorph_apply x.1
  · rfl

theorem cylinderAntipodal_involutive (x :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderAntipodal (cylinderAntipodal x) = x := by
  apply Prod.ext
  · simp [cylinderAntipodal]
  · simp [cylinderAntipodal]

theorem cylinderDiagonal_involutive (x :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderDiagonal (cylinderDiagonal x) = x := by
  apply Prod.ext
  · simp [cylinderDiagonal]
  · simp [cylinderDiagonal]

theorem cylinderAntipodal_fixed_point_free (x :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderAntipodal x ≠ x := by
  intro h
  have hsphere : -x.1 = x.1 := congrArg Prod.fst h
  have hzero : (x.1 : EuclideanSpace Real (Fin 3)) = 0 := by
    apply_fun (fun z : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
      (z : EuclideanSpace Real (Fin 3))) at hsphere
    have hamb : -(x.1 : EuclideanSpace Real (Fin 3)) = x.1 := by
      simpa using hsphere
    ext i
    have hi := congrArg (fun z : EuclideanSpace Real (Fin 3) => z i) hamb
    simp only [PiLp.neg_apply, PiLp.zero_apply] at hi ⊢
    linarith
  have hnorm := x.1.2
  rw [hzero] at hnorm
  norm_num at hnorm

theorem cylinderDiagonal_fixed_point_free (x :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderDiagonal x ≠ x := by
  intro h
  have hsphere : -x.1 = x.1 := congrArg Prod.fst h
  have hzero : (x.1 : EuclideanSpace Real (Fin 3)) = 0 := by
    apply_fun (fun z : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
      (z : EuclideanSpace Real (Fin 3))) at hsphere
    have hamb : -(x.1 : EuclideanSpace Real (Fin 3)) = x.1 := by
      simpa using hsphere
    ext i
    have hi := congrArg (fun z : EuclideanSpace Real (Fin 3) => z i) hamb
    simp only [PiLp.neg_apply, PiLp.zero_apply] at hi ⊢
    linarith
  have hnorm := x.1.2
  rw [hzero] at hnorm
  norm_num at hnorm

theorem cylinderAntipodalDiffeomorph_fixed_point_free
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderAntipodalDiffeomorph x ≠ x := by
  rw [cylinderAntipodalDiffeomorph_apply]
  exact cylinderAntipodal_fixed_point_free x

theorem cylinderDiagonalDiffeomorph_fixed_point_free
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderDiagonalDiffeomorph x ≠ x := by
  rw [cylinderDiagonalDiffeomorph_apply]
  exact cylinderDiagonal_fixed_point_free x

private theorem perm_orderOf_eq_two {X : Type*} [Nonempty X]
    (phi : Equiv.Perm X) (hinvolutive : Function.Involutive phi)
    (hfree : ∀ x, phi x ≠ x) :
    orderOf phi = 2 := by
  apply orderOf_eq_prime
  · ext x
    exact hinvolutive x
  · intro h
    obtain ⟨x⟩ := ‹Nonempty X›
    exact hfree x (by rw [h]; rfl)

private theorem mem_zpowers_perm_order_two_iff {X : Type*}
    (phi : Equiv.Perm X) (horder : orderOf phi = 2) (psi : Equiv.Perm X) :
    psi ∈ Subgroup.zpowers phi ↔ psi = 1 ∨ psi = phi := by
  classical
  have hfinite : IsOfFinOrder phi :=
    orderOf_pos_iff.mp (by rw [horder]; exact Nat.zero_lt_two)
  constructor
  · intro hpsi
    have hrange := hfinite.mem_zpowers_iff_mem_range_orderOf.mp hpsi
    rw [horder] at hrange
    rcases Finset.mem_image.mp hrange with ⟨n, hn, rfl⟩
    simp only [Finset.mem_range] at hn
    interval_cases n <;> simp
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

noncomputable def cylinderAntipodalGroup : Subgroup (Equiv.Perm
    (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)) :=
  Subgroup.zpowers cylinderAntipodalDiffeomorph.toEquiv

noncomputable def cylinderDiagonalGroup : Subgroup (Equiv.Perm
    (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)) :=
  Subgroup.zpowers cylinderDiagonalDiffeomorph.toEquiv

instance cylinderAntipodalGroupSMul :
    SMul cylinderAntipodalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) where
  smul gamma x := gamma.1 x

instance cylinderDiagonalGroupSMul :
    SMul cylinderDiagonalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) where
  smul gamma x := gamma.1 x

instance cylinderAntipodalGroupMulAction :
    MulAction cylinderAntipodalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :=
  inferInstance

instance cylinderDiagonalGroupMulAction :
    MulAction cylinderDiagonalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :=
  inferInstance

theorem cylinderAntipodalGroup_orderOf :
    orderOf cylinderAntipodalDiffeomorph.toEquiv = 2 := by
  let : Nonempty (Metric.sphere
      (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :=
    ⟨⟨Classical.choice
      (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype, 0⟩⟩
  apply perm_orderOf_eq_two
  · intro x
    change cylinderAntipodalDiffeomorph
        (cylinderAntipodalDiffeomorph x) = x
    rw [cylinderAntipodalDiffeomorph_apply,
      cylinderAntipodalDiffeomorph_apply]
    exact cylinderAntipodal_involutive x
  · exact cylinderAntipodalDiffeomorph_fixed_point_free

theorem cylinderDiagonalGroup_orderOf :
    orderOf cylinderDiagonalDiffeomorph.toEquiv = 2 := by
  let : Nonempty (Metric.sphere
      (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :=
    ⟨⟨Classical.choice
      (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype, 0⟩⟩
  apply perm_orderOf_eq_two
  · intro x
    change cylinderDiagonalDiffeomorph
        (cylinderDiagonalDiffeomorph x) = x
    rw [cylinderDiagonalDiffeomorph_apply,
      cylinderDiagonalDiffeomorph_apply]
    exact cylinderDiagonal_involutive x
  · exact cylinderDiagonalDiffeomorph_fixed_point_free

theorem cylinderAntipodalGroup_eq_one_or_generator
    (psi : cylinderAntipodalGroup) :
    psi.1 = 1 ∨ psi.1 = cylinderAntipodalDiffeomorph.toEquiv := by
  exact (mem_zpowers_perm_order_two_iff _
    cylinderAntipodalGroup_orderOf psi.1).mp psi.2

theorem cylinderDiagonalGroup_eq_one_or_generator
    (psi : cylinderDiagonalGroup) :
    psi.1 = 1 ∨ psi.1 = cylinderDiagonalDiffeomorph.toEquiv := by
  exact (mem_zpowers_perm_order_two_iff _
    cylinderDiagonalGroup_orderOf psi.1).mp psi.2

noncomputable instance cylinderAntipodalGroupFinite :
    Finite cylinderAntipodalGroup := by
  have hfinite : IsOfFinOrder cylinderAntipodalDiffeomorph.toEquiv :=
    orderOf_pos_iff.mp (by
      rw [cylinderAntipodalGroup_orderOf]
      exact Nat.zero_lt_two)
  exact Finite.of_equiv
    (Fin (orderOf cylinderAntipodalDiffeomorph.toEquiv))
    (finEquivZPowers hfinite)

noncomputable instance cylinderDiagonalGroupFinite :
    Finite cylinderDiagonalGroup := by
  have hfinite : IsOfFinOrder cylinderDiagonalDiffeomorph.toEquiv :=
    orderOf_pos_iff.mp (by
      rw [cylinderDiagonalGroup_orderOf]
      exact Nat.zero_lt_two)
  exact Finite.of_equiv
    (Fin (orderOf cylinderDiagonalDiffeomorph.toEquiv))
    (finEquivZPowers hfinite)

noncomputable def cylinderAntipodalGroupGenerator : cylinderAntipodalGroup :=
  ⟨cylinderAntipodalDiffeomorph.toEquiv, Subgroup.mem_zpowers _⟩

noncomputable def cylinderDiagonalGroupGenerator : cylinderDiagonalGroup :=
  ⟨cylinderDiagonalDiffeomorph.toEquiv, Subgroup.mem_zpowers _⟩

theorem cylinderAntipodalGroupGenerator_smul
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    @SMul.smul cylinderAntipodalGroup
        (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
        cylinderAntipodalGroupMulAction.toSMul
        cylinderAntipodalGroupGenerator x =
      cylinderAntipodalDiffeomorph x :=
  rfl

theorem cylinderDiagonalGroupGenerator_smul
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    @SMul.smul cylinderDiagonalGroup
        (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
        cylinderDiagonalGroupMulAction.toSMul
        cylinderDiagonalGroupGenerator x =
      cylinderDiagonalDiffeomorph x :=
  rfl

instance cylinderAntipodalGroupContinuousConstSMul :
    ContinuousConstSMul cylinderAntipodalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) where
  continuous_const_smul psi := by
    rcases cylinderAntipodalGroup_eq_one_or_generator psi with hpsi | hpsi
    · change Continuous (psi.1 :
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → _)
      rw [hpsi]
      exact continuous_id
    · change Continuous (psi.1 :
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → _)
      rw [hpsi]
      exact cylinderAntipodalDiffeomorph.continuous

instance cylinderDiagonalGroupContinuousConstSMul :
    ContinuousConstSMul cylinderDiagonalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) where
  continuous_const_smul psi := by
    rcases cylinderDiagonalGroup_eq_one_or_generator psi with hpsi | hpsi
    · change Continuous (psi.1 :
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → _)
      rw [hpsi]
      exact continuous_id
    · change Continuous (psi.1 :
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → _)
      rw [hpsi]
      exact cylinderDiagonalDiffeomorph.continuous

instance cylinderAntipodalGroupIsCancelSMul :
    IsCancelSMul cylinderAntipodalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro psi x hpsi
  rcases cylinderAntipodalGroup_eq_one_or_generator psi with h | h
  · exact Subtype.ext h
  · exfalso
    change psi.1 x = x at hpsi
    rw [h] at hpsi
    exact cylinderAntipodalDiffeomorph_fixed_point_free x hpsi

instance cylinderDiagonalGroupIsCancelSMul :
    IsCancelSMul cylinderDiagonalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro psi x hpsi
  rcases cylinderDiagonalGroup_eq_one_or_generator psi with h | h
  · exact Subtype.ext h
  · exfalso
    change psi.1 x = x at hpsi
    rw [h] at hpsi
    exact cylinderDiagonalDiffeomorph_fixed_point_free x hpsi

private theorem cylinderAntipodalDiffeomorph_toEquiv_ne_one :
    cylinderAntipodalDiffeomorph.toEquiv ≠ 1 := by
  intro h
  have horder := cylinderAntipodalGroup_orderOf
  rw [h, orderOf_one] at horder
  omega

private theorem cylinderDiagonalDiffeomorph_toEquiv_ne_one :
    cylinderDiagonalDiffeomorph.toEquiv ≠ 1 := by
  intro h
  have horder := cylinderDiagonalGroup_orderOf
  rw [h, orderOf_one] at horder
  omega

theorem cylinderAntipodalGroup_ne_bot :
    cylinderAntipodalGroup ≠ (⊥ : Subgroup (Equiv.Perm
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real))) := by
  intro h
  have hmem : cylinderAntipodalDiffeomorph.toEquiv ∈
      (⊥ : Subgroup (Equiv.Perm
        (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real))) := by
    rw [← h]
    exact Subgroup.mem_zpowers _
  have hone : cylinderAntipodalDiffeomorph.toEquiv = 1 := by
    simpa using hmem
  exact cylinderAntipodalDiffeomorph_toEquiv_ne_one hone

theorem cylinderDiagonalGroup_ne_bot :
    cylinderDiagonalGroup ≠ (⊥ : Subgroup (Equiv.Perm
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real))) := by
  intro h
  have hmem : cylinderDiagonalDiffeomorph.toEquiv ∈
      (⊥ : Subgroup (Equiv.Perm
        (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real))) := by
    rw [← h]
    exact Subgroup.mem_zpowers _
  have hone : cylinderDiagonalDiffeomorph.toEquiv = 1 := by
    simpa using hmem
  exact cylinderDiagonalDiffeomorph_toEquiv_ne_one hone

theorem cylinderAntipodalGroup_ne_cylinderDiagonalGroup :
    cylinderAntipodalGroup ≠ cylinderDiagonalGroup := by
  intro h
  have hmem : cylinderAntipodalDiffeomorph.toEquiv ∈ cylinderDiagonalGroup := by
    rw [← h]
    exact Subgroup.mem_zpowers _
  let psi : cylinderDiagonalGroup :=
    ⟨cylinderAntipodalDiffeomorph.toEquiv, hmem⟩
  rcases cylinderDiagonalGroup_eq_one_or_generator psi with hone | heq
  · change cylinderAntipodalDiffeomorph.toEquiv = 1 at hone
    exact cylinderAntipodalDiffeomorph_toEquiv_ne_one hone
  · let y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 :=
      ⟨EuclideanSpace.single 0 1, by simp [PiLp.norm_single]⟩
    have hact := congrArg
      (fun e : Equiv.Perm
        (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) => e (y, 1)) heq
    change cylinderAntipodalDiffeomorph (y, 1) =
      cylinderDiagonalDiffeomorph (y, 1) at hact
    rw [cylinderAntipodalDiffeomorph_apply,
      cylinderDiagonalDiffeomorph_apply] at hact
    have hsnd := congrArg Prod.snd hact
    simp [cylinderAntipodal, cylinderDiagonal] at hsnd
    norm_num at hsnd

noncomputable def cylinderAntipodalGroupDiffeomorph
    (psi : cylinderAntipodalGroup) :
    (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
      ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), (𝓡 2).prod 𝓘(Real, Real)⟯
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real := by
  classical
  exact if psi.1 = 1 then
      Diffeomorph.refl ((𝓡 2).prod 𝓘(Real, Real))
        (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) ∞
    else cylinderAntipodalDiffeomorph

noncomputable def cylinderDiagonalGroupDiffeomorph
    (psi : cylinderDiagonalGroup) :
    (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
      ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), (𝓡 2).prod 𝓘(Real, Real)⟯
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real := by
  classical
  exact if psi.1 = 1 then
      Diffeomorph.refl ((𝓡 2).prod 𝓘(Real, Real))
        (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) ∞
    else cylinderDiagonalDiffeomorph

theorem cylinderAntipodalGroupDiffeomorph_apply
    (psi : cylinderAntipodalGroup)
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderAntipodalGroupDiffeomorph psi x = psi.1 x := by
  rcases cylinderAntipodalGroup_eq_one_or_generator psi with h | h
  · simp [cylinderAntipodalGroupDiffeomorph, h]
  · simp [cylinderAntipodalGroupDiffeomorph, h,
      cylinderAntipodalDiffeomorph_toEquiv_ne_one]

theorem cylinderDiagonalGroupDiffeomorph_apply
    (psi : cylinderDiagonalGroup)
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderDiagonalGroupDiffeomorph psi x = psi.1 x := by
  rcases cylinderDiagonalGroup_eq_one_or_generator psi with h | h
  · simp [cylinderDiagonalGroupDiffeomorph, h]
  · simp [cylinderDiagonalGroupDiffeomorph, h,
      cylinderDiagonalDiffeomorph_toEquiv_ne_one]

instance cylinderAntipodalGroupContMDiffConstSMul :
    ContMDiffConstSMul
      ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))).prod
        (modelWithCornersSelf Real Real)) ∞
      cylinderAntipodalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) where
  contMDiff_const_smul psi := by
    change ContMDiff ((𝓡 2).prod 𝓘(Real, Real))
      ((𝓡 2).prod 𝓘(Real, Real)) ∞
      (psi.1 : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → _)
    refine (cylinderAntipodalGroupDiffeomorph psi).contMDiff.congr ?_
    exact fun x => (cylinderAntipodalGroupDiffeomorph_apply psi x).symm

instance cylinderDiagonalGroupContMDiffConstSMul :
    ContMDiffConstSMul
      ((modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))).prod
        (modelWithCornersSelf Real Real)) ∞
      cylinderDiagonalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) where
  contMDiff_const_smul psi := by
    change ContMDiff ((𝓡 2).prod 𝓘(Real, Real))
      ((𝓡 2).prod 𝓘(Real, Real)) ∞
      (psi.1 : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → _)
    refine (cylinderDiagonalGroupDiffeomorph psi).contMDiff.congr ?_
    exact fun x => (cylinderDiagonalGroupDiffeomorph_apply psi x).symm

abbrev CylinderAntipodalQuotient := MulAction.orbitRel.Quotient
  cylinderAntipodalGroup
    (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)

abbrev CylinderDiagonalQuotient := MulAction.orbitRel.Quotient
  cylinderDiagonalGroup
    (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)

def cylinderAntipodalQuotientMap
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    CylinderAntipodalQuotient := Quotient.mk'' x

def cylinderDiagonalQuotientMap
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    CylinderDiagonalQuotient := Quotient.mk'' x

theorem cylinderAntipodalQuotientMap_isQuotientCoveringMap :
    IsQuotientCoveringMap cylinderAntipodalQuotientMap
      cylinderAntipodalGroup := by
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

theorem cylinderDiagonalQuotientMap_isQuotientCoveringMap :
    IsQuotientCoveringMap cylinderDiagonalQuotientMap
      cylinderDiagonalGroup := by
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

theorem cylinderAntipodalQuotientMap_isCoveringMap :
    IsCoveringMap cylinderAntipodalQuotientMap :=
  cylinderAntipodalQuotientMap_isQuotientCoveringMap.isCoveringMap

theorem cylinderDiagonalQuotientMap_isCoveringMap :
    IsCoveringMap cylinderDiagonalQuotientMap :=
  cylinderDiagonalQuotientMap_isQuotientCoveringMap.isCoveringMap

theorem cylinderAntipodalQuotientMap_isLocalDiffeomorph :
    IsLocalDiffeomorph ((𝓡 2).prod 𝓘(Real, Real))
      ((𝓡 2).prod 𝓘(Real, Real)) ∞ cylinderAntipodalQuotientMap := by
  exact MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
    ((𝓡 2).prod 𝓘(Real, Real))

theorem cylinderDiagonalQuotientMap_isLocalDiffeomorph :
    IsLocalDiffeomorph ((𝓡 2).prod 𝓘(Real, Real))
      ((𝓡 2).prod 𝓘(Real, Real)) ∞ cylinderDiagonalQuotientMap := by
  exact MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
    ((𝓡 2).prod 𝓘(Real, Real))

theorem cylinderAntipodalQuotientMap_surjective :
    Function.Surjective cylinderAntipodalQuotientMap :=
  cylinderAntipodalQuotientMap_isQuotientCoveringMap.surjective

theorem cylinderDiagonalQuotientMap_surjective :
    Function.Surjective cylinderDiagonalQuotientMap :=
  cylinderDiagonalQuotientMap_isQuotientCoveringMap.surjective

theorem cylinderAntipodalQuotientMap_eq_iff_mem_orbit
    {x y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real} :
    cylinderAntipodalQuotientMap x = cylinderAntipodalQuotientMap y ↔
      x ∈ MulAction.orbit cylinderAntipodalGroup y :=
  cylinderAntipodalQuotientMap_isQuotientCoveringMap.apply_eq_iff_mem_orbit

theorem cylinderDiagonalQuotientMap_eq_iff_mem_orbit
    {x y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real} :
    cylinderDiagonalQuotientMap x = cylinderDiagonalQuotientMap y ↔
      x ∈ MulAction.orbit cylinderDiagonalGroup y :=
  cylinderDiagonalQuotientMap_isQuotientCoveringMap.apply_eq_iff_mem_orbit

theorem cylinderAntipodalQuotientMap_eq_iff
    {x y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real} :
    cylinderAntipodalQuotientMap x = cylinderAntipodalQuotientMap y ↔
      x = y ∨ x = cylinderAntipodalDiffeomorph y := by
  rw [cylinderAntipodalQuotientMap_eq_iff_mem_orbit]
  constructor
  · rintro ⟨psi, rfl⟩
    rcases cylinderAntipodalGroup_eq_one_or_generator psi with h | h
    · left
      change psi.1 y = y
      rw [h]
      rfl
    · right
      change psi.1 y = cylinderAntipodalDiffeomorph y
      rw [h]
      rfl
  · rintro (rfl | h)
    · exact MulAction.mem_orbit_self _
    · rw [h]
      refine ⟨cylinderAntipodalGroupGenerator, ?_⟩
      exact cylinderAntipodalGroupGenerator_smul y

theorem cylinderDiagonalQuotientMap_eq_iff
    {x y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real} :
    cylinderDiagonalQuotientMap x = cylinderDiagonalQuotientMap y ↔
      x = y ∨ x = cylinderDiagonalDiffeomorph y := by
  rw [cylinderDiagonalQuotientMap_eq_iff_mem_orbit]
  constructor
  · rintro ⟨psi, rfl⟩
    rcases cylinderDiagonalGroup_eq_one_or_generator psi with h | h
    · left
      change psi.1 y = y
      rw [h]
      rfl
    · right
      change psi.1 y = cylinderDiagonalDiffeomorph y
      rw [h]
      rfl
  · rintro (rfl | h)
    · exact MulAction.mem_orbit_self _
    · rw [h]
      refine ⟨cylinderDiagonalGroupGenerator, ?_⟩
      exact cylinderDiagonalGroupGenerator_smul y

theorem cylinderAntipodalQuotientMap_lift_unique {Y : Type*}
    (F : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → Y)
    (hinvariant : ∀ psi : cylinderAntipodalGroup, ∀ x, F (psi.1 x) = F x) :
    ∃! Fbar : CylinderAntipodalQuotient → Y,
      Fbar ∘ cylinderAntipodalQuotientMap = F := by
  let Fbar : CylinderAntipodalQuotient → Y :=
    Quotient.lift F (by
      intro x y hxy
      rcases hxy with ⟨psi, rfl⟩
      exact hinvariant psi y)
  refine ⟨Fbar, ?_, ?_⟩
  · funext x
    rfl
  · intro G hG
    funext q
    induction q using Quotient.inductionOn with
    | _ x => exact congrFun hG x

theorem cylinderDiagonalQuotientMap_lift_unique {Y : Type*}
    (F : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → Y)
    (hinvariant : ∀ psi : cylinderDiagonalGroup, ∀ x, F (psi.1 x) = F x) :
    ∃! Fbar : CylinderDiagonalQuotient → Y,
      Fbar ∘ cylinderDiagonalQuotientMap = F := by
  let Fbar : CylinderDiagonalQuotient → Y :=
    Quotient.lift F (by
      intro x y hxy
      rcases hxy with ⟨psi, rfl⟩
      exact hinvariant psi y)
  refine ⟨Fbar, ?_, ?_⟩
  · funext x
    rfl
  · intro G hG
    funext q
    induction q using Quotient.inductionOn with
    | _ x => exact congrFun hG x

end DifferentialGeometry.Geometry

end
