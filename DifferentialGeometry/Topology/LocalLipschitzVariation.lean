import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.UnitInterval

set_option autoImplicit false
open Set
open scoped Topology NNReal ENNReal

namespace DifferentialGeometry.Topology

variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

theorem eVariationOn_comp_le_of_locally_lipschitzOn
    {f : X → Y} {γ : ℝ → X} {a b : ℝ} {C : ℝ≥0}
    (hγ : ContinuousOn γ (Icc a b))
    (hf : ∀ x ∈ γ '' Icc a b, ∃ s ∈ 𝓝 x, LipschitzOnWith C f s) :
    eVariationOn (f ∘ γ) (Icc a b) ≤ C * eVariationOn γ (Icc a b) := by
  by_cases hab : a ≤ b
  · have hloc : ∀ t : Icc a b, ∃ V : Set X,
        IsOpen V ∧ γ t ∈ V ∧ LipschitzOnWith C f V := by
      intro t
      obtain ⟨s, hs, hfs⟩ := hf (γ t) ⟨t, t.property, rfl⟩
      obtain ⟨V, hVs, hVo, htV⟩ := mem_nhds_iff.mp hs
      exact ⟨V, hVo, htV, hfs.mono hVs⟩
    choose V hVo htV hfV using hloc
    let curve : Icc a b → X := fun t => γ t
    have hc : Continuous curve := hγ.domRestrict
    obtain ⟨t, ht0, htm, ⟨n, htn⟩, htV'⟩ :=
      exists_monotone_Icc_subset_open_cover_Icc hab
        (c := fun i => curve ⁻¹' V i)
        (fun i => hc.isOpen_preimage _ (hVo i)) (by
          intro i _
          exact mem_iUnion.mpr ⟨i, htV i⟩)
    let u : ℕ → ℝ := fun i => t i
    have hu : Monotone u := fun i j hij => htm hij
    have hu0 : u 0 = a := ht0
    have hun : u n = b := htn n le_rfl
    have hpiece (i : ℕ) :
        eVariationOn (f ∘ γ) (Icc (u i) (u (i + 1))) ≤
          C * eVariationOn γ (Icc (u i) (u (i + 1))) := by
      obtain ⟨j, hj⟩ := htV' i
      apply (hfV j).comp_eVariationOn_le
      intro z hz
      have hzab : z ∈ Icc a b :=
        ⟨(t i).property.1.trans hz.1, hz.2.trans (t (i + 1)).property.2⟩
      exact hj (show (⟨z, hzab⟩ : Icc a b) ∈ Icc (t i) (t (i + 1)) from hz)
    calc
      eVariationOn (f ∘ γ) (Icc a b) =
          ∑ i ∈ Finset.range n, eVariationOn (f ∘ γ) (Icc (u i) (u (i + 1))) := by
        rw [eVariationOn.sum' (f ∘ γ) hu, hu0, hun]
      _ ≤ ∑ i ∈ Finset.range n, C * eVariationOn γ (Icc (u i) (u (i + 1))) :=
        Finset.sum_le_sum fun i _ => hpiece i
      _ = C * eVariationOn γ (Icc a b) := by
        rw [← Finset.mul_sum, eVariationOn.sum' γ hu, hu0, hun]
  · simp [Icc_eq_empty_of_lt (lt_of_not_ge hab)]

theorem boundedVariationOn_comp_of_locally_lipschitzOn
    {f : X → Y} {γ : ℝ → X} {a b : ℝ} {C : ℝ≥0}
    (hγ : ContinuousOn γ (Icc a b))
    (hf : ∀ x ∈ γ '' Icc a b, ∃ s ∈ 𝓝 x, LipschitzOnWith C f s)
    (hvar : BoundedVariationOn γ (Icc a b)) :
    BoundedVariationOn (f ∘ γ) (Icc a b) :=
  ne_top_of_le_ne_top (by finiteness)
    (eVariationOn_comp_le_of_locally_lipschitzOn hγ hf)

end DifferentialGeometry.Topology
