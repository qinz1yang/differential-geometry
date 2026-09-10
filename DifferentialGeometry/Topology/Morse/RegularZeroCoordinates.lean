import DifferentialGeometry.Topology.Manifold.RegularZero.Coordinates

set_option autoImplicit false
noncomputable section
open Set Filter Function
open scoped Manifold ContDiff Topology
namespace Poincare.Morse
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
  {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]


theorem exists_regular_coordinates [FiniteDimensional ℝ B]
    {g : A → B} {a : A} (hg : ContDiffAt ℝ 1 g a)
    (hreg : Surjective (fderiv ℝ g a)) {s : Set A} (hs : IsOpen s) (ha : a ∈ s) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, B × (fderiv ℝ g a).ker)
        A (B × (fderiv ℝ g a).ker) 1,
      a ∈ Φ.source ∧ Φ.source ⊆ s ∧
      (∀ y, (Φ y).1 = g y) ∧ (Φ a).2 = 0 := by
  obtain ⟨U,hUsub,hU,haU⟩ := mem_nhds_iff.mp
    (Filter.inter_mem (hg.eventually (by norm_num)) (hs.mem_nhds ha))
  have hgU : ContDiffOn ℝ 1 g U := by
    intro y hy
    have hh : ContDiffAt ℝ 1 g y := (hUsub hy).1
    exact hh.contDiffWithinAt
  obtain ⟨Φ,haΦ,hΦU,hΦ,ha0⟩ :=
    Poincare.Manifold.RegularZero.exists_coordinates one_ne_zero hU hgU haU hreg
  exact ⟨Φ,haΦ,fun y hy => (hUsub (hΦU hy)).2,hΦ,ha0⟩

omit [CompleteSpace A] in
theorem exists_regular_coordinates_finrank [FiniteDimensional ℝ A] [FiniteDimensional ℝ B]
    {g : A → B} {a : A} (hg : ContDiffAt ℝ 1 g a)
    (hreg : Surjective (fderiv ℝ g a)) {s : Set A} (hs : IsOpen s) (ha : a ∈ s) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, A)
        𝓘(ℝ, B × (Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ))
        A (B × (Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ)) 1,
      a ∈ Φ.source ∧ Φ.source ⊆ s ∧
      (∀ y, (Φ y).1 = g y) ∧ (Φ a).2 = 0 := by
  obtain ⟨U,hUsub,hU,haU⟩ := mem_nhds_iff.mp
    (Filter.inter_mem (hg.eventually (by norm_num)) (hs.mem_nhds ha))
  have hgU : ContDiffOn ℝ 1 g U := by
    intro y hy
    have hh : ContDiffAt ℝ 1 g y := (hUsub hy).1
    exact hh.contDiffWithinAt
  obtain ⟨Φ,haΦ,hΦU,hΦ,ha0⟩ :=
    Poincare.Manifold.RegularZero.exists_coordinates_finrank one_ne_zero hU hgU haU hreg
  exact ⟨Φ,haΦ,fun y hy => (hUsub (hΦU hy)).2,hΦ,ha0⟩

section FiberChart
variable {S : Set A} {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]


def zeroFiberChart (g : A → B)
    (Φ : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, B × C) A (B × C) 1)
    (hΦ : ∀ y, (Φ y).1 = g y) (hΦS : Φ.source ⊆ S) (a : {y : A // y ∈ S ∧ g y = 0}) :
    OpenPartialHomeomorph {y : A // y ∈ S ∧ g y = 0} C :=
  Poincare.Manifold.RegularZero.fiberChart g Φ hΦ hΦS a

omit [CompleteSpace A] in
theorem zeroFiberChart_source (g : A → B)
    (Φ : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, B × C) A (B × C) 1)
    (hΦ : ∀ y, (Φ y).1 = g y) (hΦS : Φ.source ⊆ S) (a : {y : A // y ∈ S ∧ g y = 0}) :
    (zeroFiberChart g Φ hΦ hΦS a).source = Subtype.val ⁻¹' Φ.source :=
  Poincare.Manifold.RegularZero.fiberChart_source g Φ hΦ hΦS a

omit [CompleteSpace A] in
theorem zeroFiberChart_target (g : A → B)
    (Φ : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, B × C) A (B × C) 1)
    (hΦ : ∀ y, (Φ y).1 = g y) (hΦS : Φ.source ⊆ S) (a : {y : A // y ∈ S ∧ g y = 0}) :
    (zeroFiberChart g Φ hΦ hΦS a).target = (fun z => (0, z)) ⁻¹' Φ.target :=
  Poincare.Manifold.RegularZero.fiberChart_target g Φ hΦ hΦS a

omit [CompleteSpace A] in
theorem zeroFiberChart_symm_apply (g : A → B)
    (Φ : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, B × C) A (B × C) 1)
    (hΦ : ∀ y, (Φ y).1 = g y) (hΦS : Φ.source ⊆ S) (a : {y : A // y ∈ S ∧ g y = 0})
    {z : C} (hz : z ∈ (zeroFiberChart g Φ hΦ hΦS a).target) :
    ((zeroFiberChart g Φ hΦ hΦS a).symm z).val = Φ.symm (0, z) :=
  Poincare.Manifold.RegularZero.fiberChart_symm_apply g Φ hΦ hΦS a hz

omit [CompleteSpace A] in
theorem contDiffOn_zeroFiberChart_symm (g : A → B)
    (Φ : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, B × C) A (B × C) 1)
    (hΦ : ∀ y, (Φ y).1 = g y) (hΦS : Φ.source ⊆ S) (a : {y : A // y ∈ S ∧ g y = 0}) :
    ContDiffOn ℝ 1 (fun z => ((zeroFiberChart g Φ hΦ hΦS a).symm z).val)
      (zeroFiberChart g Φ hΦ hΦS a).target :=
  Poincare.Manifold.RegularZero.contDiffOn_fiberChart_symm g Φ hΦ hΦS a

omit [CompleteSpace A] in
theorem contDiffOn_zeroFiberChart_transition
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (g : A → B)
    (Φ : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, B × C) A (B × C) 1)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, B × D) A (B × D) 1)
    (hΦ : ∀ y, (Φ y).1 = g y) (hΨ : ∀ y, (Ψ y).1 = g y)
    (hΦS : Φ.source ⊆ S) (hΨS : Ψ.source ⊆ S) (a b : {y : A // y ∈ S ∧ g y = 0}) :
    ContDiffOn ℝ 1 ((zeroFiberChart g Ψ hΨ hΨS b) ∘ (zeroFiberChart g Φ hΦ hΦS a).symm)
      ((zeroFiberChart g Φ hΦ hΦS a).target ∩
        (zeroFiberChart g Φ hΦ hΦS a).symm ⁻¹' (zeroFiberChart g Ψ hΨ hΨS b).source) :=
  Poincare.Manifold.RegularZero.contDiffOn_fiberChart_transition g Φ Ψ hΦ hΨ hΦS hΨS a b

end FiberChart
end Poincare.Morse
