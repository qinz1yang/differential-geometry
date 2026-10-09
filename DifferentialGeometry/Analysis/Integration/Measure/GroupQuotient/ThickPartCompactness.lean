/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Group
import Mathlib.Tactic.Push

noncomputable section

open Set Filter Function MeasureTheory MeasureTheory.Measure
open scoped Pointwise Topology ENNReal

namespace DifferentialGeometry.LatticeCompactness

section Group

variable {G : Type*} [Group G]

def thickSet (Γ : Subgroup G) (U : Set G) : Set G :=
  {g | ∀ γ : Γ, g⁻¹ * (γ : G) * g ∈ U → γ = 1}

theorem mul_mem_thickSet {Γ : Subgroup G} {U : Set G} {g : G}
    (hg : g ∈ thickSet Γ U) (δ : Γ) :
    (δ : G) * g ∈ thickSet Γ U := by
  intro γ hγ
  have heq : δ⁻¹ * γ * δ = 1 := hg (δ⁻¹ * γ * δ) (by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, mul_assoc] using hγ)
  have h := congrArg (fun a : Γ => δ * a * δ⁻¹) heq
  simpa only [mul_assoc, mul_inv_cancel, inv_mul_cancel_left, mul_one,
    mul_inv_cancel_left] using h

theorem mul_mem_thickSet_iff {Γ : Subgroup G} {U : Set G} (g : G) (δ : Γ) :
    (δ : G) * g ∈ thickSet Γ U ↔ g ∈ thickSet Γ U := by
  constructor
  · intro h
    simpa only [Subgroup.coe_inv, inv_mul_cancel_left] using mul_mem_thickSet h δ⁻¹
  · exact fun h => mul_mem_thickSet h δ

theorem pairwise_disjoint_translates {Γ : Subgroup G} {U V : Set G}
    (hVU : V * V⁻¹ ⊆ U) {g : G} (hg : g ∈ thickSet Γ U) :
    Pairwise (Disjoint on fun γ : Γ => γ • (g • V)) := by
  intro γ δ hne
  change Disjoint (γ • (g • V)) (δ • (g • V))
  rw [Set.disjoint_left]
  rintro z ⟨x, ⟨v, hv, rfl⟩, rfl⟩ ⟨y, ⟨w, hw, rfl⟩, heq⟩
  change (δ : G) * (g * w) = (γ : G) * (g * v) at heq
  have hconj : g⁻¹ * ((δ⁻¹ * γ : Γ) : G) * g = w * v⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc
      g⁻¹ * ((δ : G)⁻¹ * (γ : G)) * g
          = g⁻¹ * (δ : G)⁻¹ * ((γ : G) * (g * v)) * v⁻¹ := by group
      _ = g⁻¹ * (δ : G)⁻¹ * ((δ : G) * (g * w)) * v⁻¹ := by rw [← heq]
      _ = w * v⁻¹ := by group
  have hmem : g⁻¹ * ((δ⁻¹ * γ : Γ) : G) * g ∈ U := by
    rw [hconj]
    exact hVU (Set.mul_mem_mul hw (Set.inv_mem_inv.mpr hv))
  exact hne (inv_mul_eq_one.mp (hg (δ⁻¹ * γ) hmem)).symm

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem isClosed_thickSet (Γ : Subgroup G) {U : Set G} (hU : IsOpen U) :
    IsClosed (thickSet Γ U) := by
  have hset : thickSet Γ U =
      ⋂ γ : Γ, {g : G | g⁻¹ * (γ : G) * g ∈ U → γ = 1} := by
    ext g
    simp only [thickSet, mem_ofPred_eq, mem_iInter]
  rw [hset]
  apply isClosed_iInter
  intro γ
  by_cases hγ : γ = 1
  · simp only [hγ, implies_true, ofPred_true, isClosed_univ]
  · have hpre : {g : G | g⁻¹ * (γ : G) * g ∈ U → γ = 1}
        = (fun g : G => g⁻¹ * (γ : G) * g) ⁻¹' Uᶜ := by
      ext g
      simp only [hγ, imp_false, mem_ofPred_eq, mem_preimage, mem_compl_iff]
    rw [hpre]
    exact hU.isClosed_compl.preimage (by fun_prop)

variable [LocallyCompactSpace G] [T2Space G]

omit [T2Space G] in
theorem exists_compact_patch {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ V : Set G, IsCompact V ∧ V ∈ 𝓝 (1 : G) ∧ V * V⁻¹ ⊆ U := by
  obtain ⟨W, hW, hWcl, hWinv, hWW⟩ := exists_closed_nhds_one_inv_eq_mul_subset hU
  obtain ⟨L, hLc, hL⟩ := exists_compact_mem_nhds (1 : G)
  refine ⟨L ∩ W, hLc.inter_right hWcl, inter_mem hL hW, ?_⟩
  apply Subset.trans _ hWW
  apply Set.mul_subset_mul inter_subset_right
  calc
    (L ∩ W)⁻¹ ⊆ W⁻¹ := Set.inv_subset_inv.mpr inter_subset_right
    _ = W := hWinv

variable [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
variable [IsHaarMeasure μ] [InnerRegularCompactLTTop μ]

omit [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G] [IsHaarMeasure μ] in
theorem exists_compact_small_tail {F : Set G} (hF : μ F ≠ ⊤)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : Set G, IsCompact K ∧ μ (F \ K) < ε := by
  obtain ⟨K, _, hK, htail⟩ :=
    (measurableSet_toMeasurable μ F).exists_isCompact_sdiff_lt
      (by rwa [measure_toMeasurable]) hε
  exact ⟨K, hK, (measure_mono (sdiff_subset_sdiff_left (subset_toMeasurable μ F))).trans_lt
    htail⟩

variable {Γ : Subgroup G} [Countable Γ]

omit [LocallyCompactSpace G] [T2Space G] [InnerRegularCompactLTTop μ] in
theorem measure_saturated_inter {F A : Set G} (hF : IsFundamentalDomain Γ F μ)
    (hA : NullMeasurableSet A μ)
    (hdisj : Pairwise (Disjoint on fun γ : Γ => γ • A)) :
    μ (⋃ γ : Γ, γ • A ∩ F) = μ A := by
  rw [measure_iUnion₀]
  · exact (hF.measure_eq_tsum A).symm
  · intro γ δ hne
    exact ((hdisj hne).mono inter_subset_left inter_subset_left).aedisjoint
  · intro γ
    exact (hA.smul γ).inter hF.nullMeasurableSet

omit [LocallyCompactSpace G] [T2Space G] [InnerRegularCompactLTTop μ] in
theorem exists_translate_inter_compact {F A K : Set G}
    (hF : IsFundamentalDomain Γ F μ) (hA : NullMeasurableSet A μ)
    (hdisj : Pairwise (Disjoint on fun γ : Γ => γ • A))
    (htail : μ (F \ K) < μ A) :
    ∃ γ : Γ, (γ • A ∩ K).Nonempty := by
  by_contra h
  push Not at h
  have hsub : (⋃ γ : Γ, γ • A ∩ F) ⊆ F \ K := by
    intro z hz
    obtain ⟨γ, hzA, hzF⟩ := mem_iUnion.mp hz
    refine ⟨hzF, fun hzK => ?_⟩
    exact (show z ∈ (∅ : Set G) from h γ ▸ ⟨hzA, hzK⟩)
  have hle := measure_mono (μ := μ) hsub
  rw [measure_saturated_inter hF hA hdisj] at hle
  exact (not_le_of_gt htail) hle

theorem exists_compact_cover_thickSet {F : Set G} (hF : IsFundamentalDomain Γ F μ)
    (hvol : μ F ≠ ⊤) {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ C : Set G, IsCompact C ∧
      ∀ g ∈ thickSet Γ U, ∃ γ : Γ, (γ : G) * g ∈ C := by
  obtain ⟨V, hVc, hV, hVU⟩ := exists_compact_patch hU
  have hVpos : μ V ≠ 0 := (measure_pos_of_mem_nhds μ hV).ne'
  obtain ⟨K, hKc, htail⟩ := exists_compact_small_tail hvol hVpos
  refine ⟨K * V⁻¹, hKc.mul hVc.inv, fun g hg => ?_⟩
  obtain ⟨γ, z, hzA, hzK⟩ :=
    exists_translate_inter_compact hF (hVc.measurableSet.nullMeasurableSet.smul g)
      (pairwise_disjoint_translates hVU hg)
      (by simpa only [measure_smul] using htail)
  obtain ⟨x, ⟨v, hv, rfl⟩, hz⟩ := hzA
  change (γ : G) * (g * v) = z at hz
  refine ⟨γ, Set.mem_mul.mpr ⟨z, hzK, v⁻¹, Set.inv_mem_inv.mpr hv, ?_⟩⟩
  rw [← hz]
  group

theorem isCompact_quotient_thickSet {F : Set G} (hF : IsFundamentalDomain Γ F μ)
    (hvol : μ F ≠ ⊤) {U : Set G} (hU : IsOpen U) (hU1 : (1 : G) ∈ U) :
    IsCompact ((Quotient.mk (MulAction.orbitRel Γ G)) '' thickSet Γ U) := by
  obtain ⟨C, hC, hcover⟩ := exists_compact_cover_thickSet hF hvol (hU.mem_nhds hU1)
  have himage : (Quotient.mk (MulAction.orbitRel Γ G)) '' (C ∩ thickSet Γ U)
      = (Quotient.mk (MulAction.orbitRel Γ G)) '' thickSet Γ U := by
    apply Subset.antisymm (image_mono inter_subset_right)
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨γ, hγ⟩ := hcover g hg
    refine ⟨(γ : G) * g, ⟨hγ, mul_mem_thickSet hg γ⟩, ?_⟩
    exact Quotient.sound ⟨γ, rfl⟩
  rw [← himage]
  exact (hC.inter_right (isClosed_thickSet Γ hU)).image continuous_quotient_mk'

end Group

end DifferentialGeometry.LatticeCompactness
