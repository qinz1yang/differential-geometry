import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Ball.Action
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry

noncomputable def realProjectiveSpaceAntipodalHomeomorph
    (E : Type*) [NormedAddCommGroup E] :
    Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : E) 1 :=
  (Homeomorph.neg E).subtype (by
    intro x
    simp)

theorem realProjectiveSpaceAntipodalHomeomorph_coe
    {E : Type*} [NormedAddCommGroup E]
    (x : Metric.sphere (0 : E) 1) :
    (realProjectiveSpaceAntipodalHomeomorph E x : E) = -(x : E) :=
  rfl

theorem realProjectiveSpaceAntipodalHomeomorph_fixed_point_free
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (x : Metric.sphere (0 : E) 1) :
    realProjectiveSpaceAntipodalHomeomorph E x ≠ x := by
  intro h
  apply ne_neg_of_mem_unit_sphere Real x
  exact h.symm

private theorem realProjectiveSpaceAntipodalHomeomorph_sq
    (E : Type*) [NormedAddCommGroup E] :
    (realProjectiveSpaceAntipodalHomeomorph E).toEquiv ^ 2 = 1 := by
  apply Equiv.ext
  intro x
  change realProjectiveSpaceAntipodalHomeomorph E
      (realProjectiveSpaceAntipodalHomeomorph E x) = x
  apply Subtype.ext
  rw [realProjectiveSpaceAntipodalHomeomorph_coe,
    realProjectiveSpaceAntipodalHomeomorph_coe]
  simp

theorem realProjectiveSpaceAntipodalHomeomorph_orderOf
    (E : Type*) [NormedAddCommGroup E] [NormedSpace Real E] [Nontrivial E] :
    orderOf (realProjectiveSpaceAntipodalHomeomorph E).toEquiv = 2 := by
  apply orderOf_eq_prime
  · exact realProjectiveSpaceAntipodalHomeomorph_sq E
  · intro h
    obtain ⟨x, hx⟩ := NormedSpace.sphere_nonempty (E := E).2 zero_le_one
    let y : Metric.sphere (0 : E) 1 := ⟨x, hx⟩
    exact realProjectiveSpaceAntipodalHomeomorph_fixed_point_free y (by
      change (realProjectiveSpaceAntipodalHomeomorph E).toEquiv y = y
      rw [h]
      rfl)

private theorem mem_zpowers_realProjectiveSpaceAntipodalHomeomorph_iff
    {E : Type*} [NormedAddCommGroup E]
    (psi : Equiv.Perm (Metric.sphere (0 : E) 1)) :
    psi ∈ Subgroup.zpowers
        (realProjectiveSpaceAntipodalHomeomorph E).toEquiv ↔
      psi = 1 ∨
        psi = (realProjectiveSpaceAntipodalHomeomorph E).toEquiv := by
  classical
  have hfinite : IsOfFinOrder
      (realProjectiveSpaceAntipodalHomeomorph E).toEquiv :=
    isOfFinOrder_iff_pow_eq_one.mpr
      ⟨2, Nat.zero_lt_two,
        realProjectiveSpaceAntipodalHomeomorph_sq E⟩
  have hle : orderOf
      (realProjectiveSpaceAntipodalHomeomorph E).toEquiv ≤ 2 :=
    Nat.le_of_dvd Nat.zero_lt_two
      (orderOf_dvd_of_pow_eq_one
        (realProjectiveSpaceAntipodalHomeomorph_sq E))
  constructor
  · intro hpsi
    have hrange := hfinite.mem_zpowers_iff_mem_range_orderOf.mp hpsi
    rcases Finset.mem_image.mp hrange with ⟨n, hn, rfl⟩
    simp only [Finset.mem_range] at hn
    have hn2 : n < 2 := lt_of_lt_of_le hn hle
    interval_cases n <;> simp
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

noncomputable def realProjectiveSpaceAntipodalGroup
    (E : Type*) [NormedAddCommGroup E] :
    Subgroup (Equiv.Perm (Metric.sphere (0 : E) 1)) :=
  Subgroup.zpowers (realProjectiveSpaceAntipodalHomeomorph E).toEquiv

instance realProjectiveSpaceAntipodalGroupMulAction
    (E : Type*) [NormedAddCommGroup E] :
    MulAction (realProjectiveSpaceAntipodalGroup E)
      (Metric.sphere (0 : E) 1) :=
  MulAction.instMulAction (realProjectiveSpaceAntipodalGroup E)

noncomputable instance realProjectiveSpaceAntipodalGroupFinite
    (E : Type*) [NormedAddCommGroup E] :
    Finite (realProjectiveSpaceAntipodalGroup E) := by
  have hfinite : IsOfFinOrder
      (realProjectiveSpaceAntipodalHomeomorph E).toEquiv :=
    isOfFinOrder_iff_pow_eq_one.mpr
      ⟨2, Nat.zero_lt_two,
        realProjectiveSpaceAntipodalHomeomorph_sq E⟩
  exact Finite.of_equiv
    (Fin (orderOf (realProjectiveSpaceAntipodalHomeomorph E).toEquiv))
    (finEquivZPowers hfinite)

theorem realProjectiveSpaceAntipodalGroup_eq_one_or_generator
    {E : Type*} [NormedAddCommGroup E]
    (psi : realProjectiveSpaceAntipodalGroup E) :
    psi.1 = 1 ∨
      psi.1 = (realProjectiveSpaceAntipodalHomeomorph E).toEquiv :=
  (mem_zpowers_realProjectiveSpaceAntipodalHomeomorph_iff psi.1).mp psi.2

instance realProjectiveSpaceAntipodalGroupContinuousConstSMul
    (E : Type*) [NormedAddCommGroup E] :
    ContinuousConstSMul (realProjectiveSpaceAntipodalGroup E)
      (Metric.sphere (0 : E) 1) where
  continuous_const_smul psi := by
    rcases realProjectiveSpaceAntipodalGroup_eq_one_or_generator psi with
      hpsi | hpsi
    · change Continuous (psi.1 : Metric.sphere (0 : E) 1 → _)
      rw [hpsi]
      exact continuous_id
    · change Continuous (psi.1 : Metric.sphere (0 : E) 1 → _)
      rw [hpsi]
      exact (realProjectiveSpaceAntipodalHomeomorph E).continuous

instance realProjectiveSpaceAntipodalGroupIsCancelSMul
    (E : Type*) [NormedAddCommGroup E] [inst : NormedSpace Real E] :
    IsCancelSMul (realProjectiveSpaceAntipodalGroup E)
      (Metric.sphere (0 : E) 1) := by
  let _ := inst
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro psi x hpsi
  rcases realProjectiveSpaceAntipodalGroup_eq_one_or_generator psi with
    hone | hanti
  · exact Subtype.ext hone
  · exfalso
    change psi.1 x = x at hpsi
    rw [hanti] at hpsi
    exact realProjectiveSpaceAntipodalHomeomorph_fixed_point_free x hpsi

theorem realProjectiveSpaceAntipodalGroup_smul_eq_self_or_neg
    {E : Type*} [NormedAddCommGroup E]
    (psi : realProjectiveSpaceAntipodalGroup E)
    (x : Metric.sphere (0 : E) 1) :
    psi • x = x ∨ psi • x = -x := by
  rcases realProjectiveSpaceAntipodalGroup_eq_one_or_generator psi with
    hone | hanti
  · left
    change psi.1 x = x
    rw [hone]
    rfl
  · right
    change psi.1 x = -x
    rw [hanti]
    rfl

abbrev RealProjectiveSpace
    (E : Type*) [NormedAddCommGroup E] :=
  MulAction.orbitRel.Quotient (realProjectiveSpaceAntipodalGroup E)
    (Metric.sphere (0 : E) 1)

def realProjectiveSpaceQuotientMap
    {E : Type*} [NormedAddCommGroup E]
    (x : Metric.sphere (0 : E) 1) :
    RealProjectiveSpace E :=
  Quotient.mk'' x

theorem realProjectiveSpaceQuotientMap_isOpenQuotientMap
    {E : Type*} [NormedAddCommGroup E] :
    IsOpenQuotientMap (realProjectiveSpaceQuotientMap (E := E)) :=
  MulAction.isOpenQuotientMap_quotientMk

theorem realProjectiveSpaceQuotientMap_eq_iff
    {E : Type*} [NormedAddCommGroup E]
    {x y : Metric.sphere (0 : E) 1} :
    realProjectiveSpaceQuotientMap x = realProjectiveSpaceQuotientMap y ↔
      x = y ∨ (x : E) = -(y : E) := by
  constructor
  · intro hxy
    rcases Quotient.exact hxy with ⟨psi, hpsi⟩
    rcases realProjectiveSpaceAntipodalGroup_eq_one_or_generator psi with
      hone | hanti
    · left
      rw [← hpsi]
      change psi.1 y = y
      rw [hone]
      rfl
    · right
      rw [← hpsi]
      change (psi.1 y : E) = _
      rw [hanti]
      exact realProjectiveSpaceAntipodalHomeomorph_coe y
  · rintro (rfl | hxy)
    · rfl
    · apply Quotient.sound
      let psi : realProjectiveSpaceAntipodalGroup E :=
        ⟨(realProjectiveSpaceAntipodalHomeomorph E).toEquiv, by
          exact Subgroup.mem_zpowers _⟩
      refine ⟨psi, ?_⟩
      change (realProjectiveSpaceAntipodalHomeomorph E).toEquiv y = x
      apply Subtype.ext
      change (realProjectiveSpaceAntipodalHomeomorph E y : E) = (x : E)
      rw [realProjectiveSpaceAntipodalHomeomorph_coe]
      exact hxy.symm

theorem realProjectiveSpaceQuotientMap_isQuotientCoveringMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] :
    IsQuotientCoveringMap (realProjectiveSpaceQuotientMap (E := E))
      (realProjectiveSpaceAntipodalGroup E) :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

theorem realProjectiveSpaceQuotientMap_isCoveringMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] :
    IsCoveringMap (realProjectiveSpaceQuotientMap (E := E)) :=
  realProjectiveSpaceQuotientMap_isQuotientCoveringMap.isCoveringMap

theorem realProjectiveSpaceQuotientMap_surjective
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] :
    Function.Surjective (realProjectiveSpaceQuotientMap (E := E)) :=
  realProjectiveSpaceQuotientMap_isQuotientCoveringMap.surjective

noncomputable def realProjectivePlaneAntipodalHomeomorph :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 ≃ₜ
      Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 :=
  realProjectiveSpaceAntipodalHomeomorph _

theorem realProjectivePlaneAntipodalHomeomorph_coe
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    (realProjectivePlaneAntipodalHomeomorph x :
        EuclideanSpace Real (Fin 3)) =
      -(x : EuclideanSpace Real (Fin 3)) :=
  realProjectiveSpaceAntipodalHomeomorph_coe x

theorem realProjectivePlaneAntipodalHomeomorph_fixed_point_free
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    realProjectivePlaneAntipodalHomeomorph x ≠ x :=
  realProjectiveSpaceAntipodalHomeomorph_fixed_point_free x

theorem realProjectivePlaneAntipodalHomeomorph_orderOf :
    orderOf realProjectivePlaneAntipodalHomeomorph.toEquiv = 2 :=
  realProjectiveSpaceAntipodalHomeomorph_orderOf _

abbrev realProjectivePlaneAntipodalGroup :=
  realProjectiveSpaceAntipodalGroup (EuclideanSpace Real (Fin 3))

instance realProjectivePlaneAntipodalGroupMulAction :
    MulAction realProjectivePlaneAntipodalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :=
  realProjectiveSpaceAntipodalGroupMulAction _

noncomputable instance realProjectivePlaneAntipodalGroupFinite :
    Finite realProjectivePlaneAntipodalGroup :=
  realProjectiveSpaceAntipodalGroupFinite _

instance realProjectivePlaneAntipodalGroupContinuousConstSMul :
    ContinuousConstSMul realProjectivePlaneAntipodalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :=
  realProjectiveSpaceAntipodalGroupContinuousConstSMul _

instance realProjectivePlaneAntipodalGroupIsCancelSMul :
    IsCancelSMul realProjectivePlaneAntipodalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :=
  realProjectiveSpaceAntipodalGroupIsCancelSMul _

abbrev RealProjectivePlane :=
  RealProjectiveSpace (EuclideanSpace Real (Fin 3))

abbrev RealProjectiveThreeSpace :=
  RealProjectiveSpace (EuclideanSpace Real (Fin 4))

def realProjectivePlaneQuotientMap
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    RealProjectivePlane :=
  realProjectiveSpaceQuotientMap x

theorem realProjectivePlaneQuotientMap_isOpenQuotientMap :
    IsOpenQuotientMap realProjectivePlaneQuotientMap :=
  realProjectiveSpaceQuotientMap_isOpenQuotientMap

theorem realProjectivePlaneQuotientMap_isQuotientCoveringMap :
    IsQuotientCoveringMap realProjectivePlaneQuotientMap
      realProjectivePlaneAntipodalGroup :=
  realProjectiveSpaceQuotientMap_isQuotientCoveringMap

theorem realProjectivePlaneQuotientMap_isCoveringMap :
    IsCoveringMap realProjectivePlaneQuotientMap :=
  realProjectiveSpaceQuotientMap_isCoveringMap

theorem realProjectivePlaneQuotientMap_surjective :
    Function.Surjective realProjectivePlaneQuotientMap :=
  realProjectiveSpaceQuotientMap_surjective

theorem realProjectivePlaneQuotientMap_eq_iff
    {x y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1} :
    realProjectivePlaneQuotientMap x = realProjectivePlaneQuotientMap y ↔
      x = y ∨
        (x : EuclideanSpace Real (Fin 3)) =
          -(y : EuclideanSpace Real (Fin 3)) :=
  realProjectiveSpaceQuotientMap_eq_iff

end DifferentialGeometry
