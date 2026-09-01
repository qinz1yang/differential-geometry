import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry

noncomputable def realProjectivePlaneAntipodalHomeomorph :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 ≃ₜ
      Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 :=
  (Homeomorph.neg (EuclideanSpace Real (Fin 3))).subtype (by
    intro x
    simp)

theorem realProjectivePlaneAntipodalHomeomorph_coe
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    (realProjectivePlaneAntipodalHomeomorph x :
        EuclideanSpace Real (Fin 3)) =
      -(x : EuclideanSpace Real (Fin 3)) :=
  rfl

theorem realProjectivePlaneAntipodalHomeomorph_fixed_point_free
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    realProjectivePlaneAntipodalHomeomorph x ≠ x := by
  intro h
  have hamb : -(x : EuclideanSpace Real (Fin 3)) = x := by
    rw [← realProjectivePlaneAntipodalHomeomorph_coe x]
    exact congrArg Subtype.val h
  have hzero : (x : EuclideanSpace Real (Fin 3)) = 0 := by
    ext i
    have hi := congrArg (fun z : EuclideanSpace Real (Fin 3) => z i) hamb
    simp only [PiLp.neg_apply, PiLp.zero_apply] at hi ⊢
    linarith
  have hnorm := x.2
  rw [hzero] at hnorm
  norm_num at hnorm

theorem realProjectivePlaneAntipodalHomeomorph_orderOf :
    orderOf realProjectivePlaneAntipodalHomeomorph.toEquiv = 2 := by
  apply orderOf_eq_prime
  · apply Equiv.ext
    intro x
    change realProjectivePlaneAntipodalHomeomorph
        (realProjectivePlaneAntipodalHomeomorph x) = x
    apply Subtype.ext
    rw [realProjectivePlaneAntipodalHomeomorph_coe,
      realProjectivePlaneAntipodalHomeomorph_coe]
    simp
  · intro h
    let x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 :=
      ⟨EuclideanSpace.single 0 1, by simp [PiLp.norm_single]⟩
    apply realProjectivePlaneAntipodalHomeomorph_fixed_point_free x
    change realProjectivePlaneAntipodalHomeomorph.toEquiv x = x
    rw [h]
    rfl

private theorem mem_zpowers_realProjectivePlaneAntipodalHomeomorph_iff
    (psi : Equiv.Perm
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1)) :
    psi ∈ Subgroup.zpowers realProjectivePlaneAntipodalHomeomorph.toEquiv ↔
      psi = 1 ∨ psi = realProjectivePlaneAntipodalHomeomorph.toEquiv := by
  classical
  have hfinite : IsOfFinOrder realProjectivePlaneAntipodalHomeomorph.toEquiv :=
    orderOf_pos_iff.mp (by
      rw [realProjectivePlaneAntipodalHomeomorph_orderOf]
      exact Nat.zero_lt_two)
  constructor
  · intro hpsi
    have hrange := hfinite.mem_zpowers_iff_mem_range_orderOf.mp hpsi
    rw [realProjectivePlaneAntipodalHomeomorph_orderOf] at hrange
    rcases Finset.mem_image.mp hrange with ⟨n, hn, rfl⟩
    simp only [Finset.mem_range] at hn
    interval_cases n <;> simp
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

noncomputable def realProjectivePlaneAntipodalGroup : Subgroup (Equiv.Perm
    (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1)) :=
  Subgroup.zpowers realProjectivePlaneAntipodalHomeomorph.toEquiv

instance realProjectivePlaneAntipodalGroupMulAction :
    MulAction realProjectivePlaneAntipodalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :=
  MulAction.instMulAction realProjectivePlaneAntipodalGroup

private theorem realProjectivePlaneAntipodalGroup_eq_one_or_generator
    (psi : realProjectivePlaneAntipodalGroup) :
    psi.1 = 1 ∨
      psi.1 = realProjectivePlaneAntipodalHomeomorph.toEquiv :=
  (mem_zpowers_realProjectivePlaneAntipodalHomeomorph_iff psi.1).mp psi.2

instance realProjectivePlaneAntipodalGroupContinuousConstSMul :
    ContinuousConstSMul realProjectivePlaneAntipodalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) where
  continuous_const_smul psi := by
    rcases realProjectivePlaneAntipodalGroup_eq_one_or_generator psi with hpsi | hpsi
    · change Continuous (psi.1 :
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 → _)
      rw [hpsi]
      exact continuous_id
    · change Continuous (psi.1 :
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 → _)
      rw [hpsi]
      exact realProjectivePlaneAntipodalHomeomorph.continuous

abbrev RealProjectivePlane := MulAction.orbitRel.Quotient
  realProjectivePlaneAntipodalGroup
    (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1)

def realProjectivePlaneQuotientMap
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    RealProjectivePlane :=
  Quotient.mk'' x

theorem realProjectivePlaneQuotientMap_isOpenQuotientMap :
    IsOpenQuotientMap realProjectivePlaneQuotientMap :=
  MulAction.isOpenQuotientMap_quotientMk

theorem realProjectivePlaneQuotientMap_eq_iff
    {x y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1} :
    realProjectivePlaneQuotientMap x =
        realProjectivePlaneQuotientMap y ↔
      x = y ∨
        (x : EuclideanSpace Real (Fin 3)) =
          -(y : EuclideanSpace Real (Fin 3)) := by
  constructor
  · intro hxy
    rcases Quotient.exact hxy with ⟨psi, hpsi⟩
    rcases realProjectivePlaneAntipodalGroup_eq_one_or_generator psi with hone | hanti
    · left
      rw [← hpsi]
      change psi.1 y = y
      rw [hone]
      rfl
    · right
      rw [← hpsi]
      change (psi.1 y : EuclideanSpace Real (Fin 3)) = _
      rw [hanti]
      exact realProjectivePlaneAntipodalHomeomorph_coe y
  · rintro (rfl | hxy)
    · rfl
    · apply Quotient.sound
      let psi : realProjectivePlaneAntipodalGroup :=
        ⟨realProjectivePlaneAntipodalHomeomorph.toEquiv, by
          change realProjectivePlaneAntipodalHomeomorph.toEquiv ∈
            Subgroup.zpowers realProjectivePlaneAntipodalHomeomorph.toEquiv
          exact Subgroup.mem_zpowers _⟩
      refine ⟨psi, ?_⟩
      change realProjectivePlaneAntipodalHomeomorph.toEquiv y = x
      apply Subtype.ext
      change (realProjectivePlaneAntipodalHomeomorph y :
        EuclideanSpace Real (Fin 3)) = (x : EuclideanSpace Real (Fin 3))
      rw [realProjectivePlaneAntipodalHomeomorph_coe]
      exact hxy.symm

end DifferentialGeometry
