import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff

namespace Poincare.Topology.Manifold

open scoped Classical in
def collarStep {M : Type*} (U L : Set M) (q : M → ℝ) (β : ℝ → ℝ) : M → ℝ :=
  fun x ↦ if x ∈ U then β (q x) else if x ∈ L then 0 else 1

open scoped Classical in
private theorem collarStep_eq_side_off_band
    {M : Type*} (U L : Set M) (q : M → ℝ) (β : ℝ → ℝ)
    (a c b : ℝ) (hac : a ≤ c) (hcb : c ≤ b)
    (hside : ∀ x ∈ U, x ∈ L ↔ q x ≤ c)
    (hzero : ∀ t, t ≤ a → β t = 0) (hone : ∀ t, b ≤ t → β t = 1)
    {x : M} (hx : x ∉ U ∩ q ⁻¹' Icc a b) :
    collarStep U L q β x = if x ∈ L then 0 else 1 := by
  classical
  by_cases hu : x ∈ U
  · have hq : ¬ (a ≤ q x ∧ q x ≤ b) := fun h ↦ hx ⟨hu, h⟩
    rcases not_and_or.mp hq with hlo | hhi
    · have hqa : q x ≤ a := (lt_of_not_ge hlo).le
      rw [collarStep, if_pos hu, hzero _ hqa,
        if_pos ((hside x hu).mpr (hqa.trans hac))]
    · have hbq : b < q x := lt_of_not_ge hhi
      have hnotL : x ∉ L := fun h ↦ (not_le_of_gt (hcb.trans_lt hbq)) ((hside x hu).mp h)
      rw [collarStep, if_pos hu, hone _ hbq.le, if_neg hnotL]
  · rw [collarStep, if_neg hu]

open scoped Classical in
private theorem collarStep_eventuallyEq_side_off_band
    {M : Type*} [TopologicalSpace M] (U L : Set M) (hL : IsClosed L)
    (q : M → ℝ) (β : ℝ → ℝ) (a c b : ℝ) (hac : a ≤ c) (hcb : c ≤ b)
    (hside : ∀ x ∈ U, x ∈ L ↔ q x ≤ c)
    (hzero : ∀ t, t ≤ a → β t = 0) (hone : ∀ t, b ≤ t → β t = 1)
    (hK : IsClosed (U ∩ q ⁻¹' Icc a b))
    (hfrontier : frontier L ⊆ U ∩ q ⁻¹' Icc a b)
    {x : M} (hx : x ∉ U ∩ q ⁻¹' Icc a b) :
    collarStep U L q β =ᶠ[𝓝 x] fun _ ↦ if x ∈ L then 0 else 1 := by
  classical
  have hf : x ∉ frontier L := fun h ↦ hx (hfrontier h)
  by_cases hl : x ∈ L
  · have hi : x ∈ interior L := by
      by_contra hnot
      exact hf ⟨subset_closure hl, hnot⟩
    filter_upwards [hK.isOpen_compl.mem_nhds hx, isOpen_interior.mem_nhds hi] with y hy hyL
    rw [collarStep_eq_side_off_band U L q β a c b hac hcb hside hzero hone hy,
      if_pos (interior_subset hyL), if_pos hl]
  · filter_upwards [hK.isOpen_compl.mem_nhds hx, hL.isOpen_compl.mem_nhds hl] with y hy hyL
    rw [collarStep_eq_side_off_band U L q β a c b hac hcb hside hzero hone hy,
      if_neg hyL, if_neg hl]

theorem contMDiff_collarStep
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    {U L : Set M} (hU : IsOpen U) (hL : IsClosed L)
    (q : M → ℝ) (hq : ContMDiffOn I 𝓘(ℝ) ∞ q U)
    (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β)
    (a c b : ℝ) (hac : a ≤ c) (hcb : c ≤ b)
    (hside : ∀ x ∈ U, x ∈ L ↔ q x ≤ c)
    (hzero : ∀ t, t ≤ a → β t = 0) (hone : ∀ t, b ≤ t → β t = 1)
    (hK : IsClosed (U ∩ q ⁻¹' Icc a b))
    (hfrontier : frontier L ⊆ U ∩ q ⁻¹' Icc a b) :
    ContMDiff I 𝓘(ℝ) ∞ (collarStep U L q β) := by
  classical
  intro x
  by_cases hu : x ∈ U
  · apply (hβ.comp_contMDiffAt ((hq x hu).contMDiffAt (hU.mem_nhds hu))).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hu] with y hy
    exact if_pos hy
  · have hk : x ∉ U ∩ q ⁻¹' Icc a b := fun h ↦ hu h.1
    exact contMDiffAt_const.congr_of_eventuallyEq
      (collarStep_eventuallyEq_side_off_band U L hL q β a c b hac hcb hside hzero hone hK hfrontier hk)

theorem collarStep_mem_Icc {M : Type*} (U L : Set M) (q : M → ℝ) (β : ℝ → ℝ)
    (hβ : ∀ t, β t ∈ Icc (0 : ℝ) 1) (x : M) : collarStep U L q β x ∈ Icc (0 : ℝ) 1 := by
  classical
  unfold collarStep
  split_ifs
  · exact hβ _
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨zero_le_one, le_rfl⟩

theorem mvfderiv_collarStep_eq_zero_off_band
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    (U L : Set M) (hL : IsClosed L) (q : M → ℝ) (β : ℝ → ℝ)
    (a c b : ℝ) (hac : a ≤ c) (hcb : c ≤ b)
    (hside : ∀ x ∈ U, x ∈ L ↔ q x ≤ c)
    (hzero : ∀ t, t ≤ a → β t = 0) (hone : ∀ t, b ≤ t → β t = 1)
    (hK : IsClosed (U ∩ q ⁻¹' Icc a b))
    (hfrontier : frontier L ⊆ U ∩ q ⁻¹' Icc a b)
    {x : M} (hx : x ∉ U ∩ q ⁻¹' Icc a b) :
    mvfderiv I (collarStep U L q β) x = 0 := by
  have heq := collarStep_eventuallyEq_side_off_band U L hL q β a c b hac hcb
    hside hzero hone hK hfrontier hx
  ext v
  change (show ℝ from mfderiv I 𝓘(ℝ) (collarStep U L q β) x v) = 0
  rw [heq.mfderiv_eq, mfderiv_const]
  rfl

theorem mvfderiv_collarStep_of_mem
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    {U : Set M} (hU : IsOpen U) (L : Set M) (q : M → ℝ) (β : ℝ → ℝ)
    {x : M} (hx : x ∈ U) (hq : MDifferentiableAt I 𝓘(ℝ) q x)
    (hβ : DifferentiableAt ℝ β (q x)) (v : TangentSpace I x) :
    mvfderiv I (collarStep U L q β) x v = deriv β (q x) * mvfderiv I q x v := by
  have heq : collarStep U L q β =ᶠ[𝓝 x] β ∘ q := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact if_pos hy
  change (show ℝ from mfderiv I 𝓘(ℝ) (collarStep U L q β) x v) = _
  rw [heq.mfderiv_eq, mfderiv_comp x hβ.mdifferentiableAt hq]
  change (show ℝ from mfderiv 𝓘(ℝ) 𝓘(ℝ) β (q x) (mfderiv I 𝓘(ℝ) q x v)) = _
  rw [mfderiv_eq_fderiv, hβ.hasDerivAt.hasFDerivAt.fderiv]
  exact mul_comm _ _

end Poincare.Topology.Manifold
