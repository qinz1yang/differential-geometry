/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.LieGroup.ProjectiveOrthogonal.BoundedTorsion
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Matrix.Normed
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Topology.Algebra.Star.Unitary
import DifferentialGeometry.Topology.Algebra.Group.CommutatorContraction
import DifferentialGeometry.Analysis.NormedRing.CommutatorContraction

noncomputable section

open Set Filter
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology commutatorElement

namespace DifferentialGeometry.Zassenhaus

section Lorentz

open HyperbolicAction
open scoped Matrix.Norms.Operator

variable {n : ℕ}

def lorentzUnits : LorGrp n →*
    (Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)ˣ :=
  (Units.map MatrixSum.ofMatrix.symm.toMonoidHom).comp Unitary.toUnits

@[simp] theorem lorentzUnits_val (A : LorGrp n) : (lorentzUnits A).val = matOf A := rfl

theorem isEmbedding_matOf : Topology.IsEmbedding (matOf : LorGrp n →
    Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) :=
  ⟨⟨rfl⟩, fun _ _ h => Subtype.ext h⟩

theorem continuous_size : Continuous (size (lorentzUnits (n := n))) := by
  change Continuous (fun A : LorGrp n =>
    max ‖matOf A - 1‖ ‖matOf A⁻¹ - 1‖)
  exact (BoundedTorsion.continuous_matOf.sub continuous_const).norm.max
    ((BoundedTorsion.continuous_matOf.comp continuous_inv).sub continuous_const).norm

def lorentzNeighborhood (n : ℕ) : Set (LorGrp n) :=
  {A | size lorentzUnits A < 1 / 16}

theorem isOpen_lorentzNeighborhood : IsOpen (lorentzNeighborhood n) :=
  isOpen_lt continuous_size continuous_const

theorem one_mem_lorentzNeighborhood : (1 : LorGrp n) ∈ lorentzNeighborhood n := by
  change size lorentzUnits 1 < 1 / 16
  rw [size_one]
  norm_num

theorem exists_size_gap (H : Subgroup (LorGrp n)) (hH : IsDiscrete (SetLike.coe H)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ A : H, size (lorentzUnits.comp H.subtype) A < ε → A = 1 := by
  let : DiscreteTopology H := SetLike.isDiscrete_iff_discreteTopology.mp hH
  have hind : Topology.IsInducing (fun A : H => matOf (A : LorGrp n)) :=
    isEmbedding_matOf.isInducing.comp Topology.IsEmbedding.subtypeVal.isInducing
  have hs : ({1} : Set H) ∈ 𝓝 1 := (isOpen_discrete _).mem_nhds rfl
  rw [hind.nhds_eq_comap] at hs
  obtain ⟨V, hV, hsub⟩ := Filter.mem_comap.mp hs
  change V ∈ 𝓝 (matOf (1 : LorGrp n)) at hV
  rw [matOf_one] at hV
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨ε, hε, fun A hA => ?_⟩
  have hn : ‖matOf (A : LorGrp n) - 1‖ < ε :=
    (norm_sub_one_le_size (lorentzUnits.comp H.subtype) A).trans_lt hA
  exact hsub (hball (by simpa only [Metric.mem_ball, dist_eq_norm] using hn))

theorem isNilpotent_lorentz_closure {S : Set (LorGrp n)}
    (hS : S ⊆ lorentzNeighborhood n)
    (hdisc : IsDiscrete (SetLike.coe (Subgroup.closure S))) :
    Group.IsNilpotent (Subgroup.closure S) := by
  let H := Subgroup.closure S
  let ρ := lorentzUnits.comp H.subtype
  apply isNilpotent_of_contraction (size ρ) (H.subtype ⁻¹' S)
    (Subgroup.closure_preimage_eq_top S) (r := 1 / 16) (by norm_num)
  · intro s hs
    change size lorentzUnits (s : LorGrp n) ≤ 1 / 16
    exact (hS hs).le
  · exact fun a b ha hb => size_commutator_contract ρ ha hb
  · exact exists_size_gap H hdisc

end Lorentz

section Projective

open HyperbolicAction

variable {n : ℕ}

theorem isDiscrete_comap_quotient (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) :
    IsDiscrete (SetLike.coe (Γ.comap (QuotientGroup.mk' (Subgroup.center (LorGrp n))))) := by
  classical
  let q : LorGrp n →* PO n 1 := QuotientGroup.mk' _
  let H := Γ.comap q
  let p : H →* Γ :=
    { toFun A := ⟨q (A : LorGrp n), A.property⟩
      map_one' := Subtype.ext (map_one q)
      map_mul' A B := Subtype.ext (map_mul q (A : LorGrp n) (B : LorGrp n)) }
  let : DiscreteTopology Γ := SetLike.isDiscrete_iff_discreteTopology.mp hΓ
  have hq : Continuous q := QuotientGroup.continuous_mk
  have hp : Continuous p := (hq.comp continuous_subtype_val).subtype_mk _
  let K : Set H := p ⁻¹' {1}
  have hKopen : IsOpen K := (isOpen_discrete _).preimage hp
  have hcfin : (((↑) : H → LorGrp n) ⁻¹' (Subgroup.center (LorGrp n) : Set (LorGrp n))).Finite :=
    (DifferentialGeometry.ProjectiveOrthogonalGroup.Center.center_finite hn).preimage Subtype.coe_injective.injOn
  have hKfin : K.Finite := hcfin.subset (by
    intro A hA
    have hqA : q (A : LorGrp n) = 1 :=
      congrArg Subtype.val (show p A = 1 from hA)
    exact (QuotientGroup.eq_one_iff (A : LorGrp n)).mp hqA)
  have hsingle : ({1} : Set H) = K \ (K \ {1}) := by
    ext A
    simp only [mem_singleton_iff, Set.mem_sdiff]
    constructor
    · rintro rfl
      exact ⟨map_one p, fun h => h.2 rfl⟩
    · rintro ⟨hA, hnot⟩
      by_contra hne
      exact hnot ⟨hA, hne⟩
  apply SetLike.isDiscrete_iff_discreteTopology.mpr
  apply discreteTopology_of_isOpen_singleton_one
  rw [hsingle]
  exact hKopen.sdiff hKfin.sdiff.isClosed

def poNeighborhood (n : ℕ) : Set (PO n 1) :=
  (QuotientGroup.mk' (Subgroup.center (LorGrp n))) '' lorentzNeighborhood n

theorem isOpen_poNeighborhood : IsOpen (poNeighborhood n) :=
  QuotientGroup.isOpenMap_coe _ isOpen_lorentzNeighborhood

theorem one_mem_poNeighborhood : (1 : PO n 1) ∈ poNeighborhood n :=
  ⟨1, one_mem_lorentzNeighborhood, map_one (QuotientGroup.mk' _)⟩

theorem isNilpotent_po_small (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) :
    Group.IsNilpotent (Subgroup.closure ((Γ : Set (PO n 1)) ∩ poNeighborhood n)) := by
  let q : LorGrp n →* PO n 1 := QuotientGroup.mk' _
  let S : Set (LorGrp n) := (Γ.comap q : Set (LorGrp n)) ∩ lorentzNeighborhood n
  have hle : Subgroup.closure S ≤ Γ.comap q := (Subgroup.closure_le _).mpr inter_subset_left
  have hdisc : IsDiscrete (SetLike.coe (Subgroup.closure S)) :=
    (isDiscrete_comap_quotient hn Γ hΓ).mono hle
  let : Group.IsNilpotent (Subgroup.closure S) :=
    isNilpotent_lorentz_closure inter_subset_right hdisc
  have hnil : Group.IsNilpotent ((Subgroup.closure S).map q) :=
    Group.nilpotent_of_surjective (q.subgroupMap (Subgroup.closure S))
      (q.subgroupMap_surjective (Subgroup.closure S))
  have hmap : (Subgroup.closure S).map q =
      Subgroup.closure ((Γ : Set (PO n 1)) ∩ poNeighborhood n) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext g
    constructor
    · rintro ⟨A, ⟨hAΓ, hAU⟩, rfl⟩
      exact ⟨hAΓ, A, hAU, rfl⟩
    · rintro ⟨hgΓ, A, hAU, hAg⟩
      refine ⟨A, ⟨?_, hAU⟩, hAg⟩
      change q A ∈ Γ
      rwa [hAg]
  rwa [hmap] at hnil

theorem exists_po_zassenhaus_nhds (hn : 1 ≤ n) :
    ∃ U : Set (PO n 1), IsOpen U ∧ (1 : PO n 1) ∈ U ∧
      ∀ Γ : Subgroup (PO n 1), IsDiscrete (SetLike.coe Γ) →
        Group.IsNilpotent (Subgroup.closure ((Γ : Set (PO n 1)) ∩ U)) :=
  ⟨poNeighborhood n, isOpen_poNeighborhood, one_mem_poNeighborhood, isNilpotent_po_small hn⟩

end Projective

end DifferentialGeometry.Zassenhaus
