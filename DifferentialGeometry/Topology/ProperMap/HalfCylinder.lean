import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.DenselyOrdered

set_option autoImplicit false
open Set Filter
open scoped Topology NNReal

namespace DifferentialGeometry.Topology

variable {N M : Type*} [TopologicalSpace N] [TopologicalSpace M]

theorem uniform_scalar_divergence_of_isProperMap
    (R : M → ℝ) (hcompact : ∀ B : ℝ, IsCompact {x : M | R x ≤ B})
    (f : N × ℝ≥0 → M) (hf : IsProperMap f) (B : ℝ) :
    ∃ T : ℝ≥0, ∀ (x : N) (t : ℝ≥0), T ≤ t → B < R (f (x, t)) := by
  have hK : IsCompact (f ⁻¹' {x : M | R x ≤ B}) := hf.isCompact_preimage (hcompact B)
  obtain ⟨T, hT⟩ := hK.bddAbove_image
    (continuous_subtype_val.comp continuous_snd).continuousOn
  let U : ℝ≥0 := ⟨max T 0 + 1, by positivity⟩
  refine ⟨U, ?_⟩
  intro x t ht
  by_contra h
  have hx : (x, t) ∈ f ⁻¹' {x : M | R x ≤ B} := not_lt.mp h
  have hu : t.val ≤ T := hT ⟨(x, t), hx, rfl⟩
  have htu : max T 0 + 1 ≤ t.val := ht
  linarith [le_max_left T 0]

theorem isProperMap_of_uniform_scalar_divergence
    [CompactSpace N] [T2Space M] [CompactlyCoherentSpace M]
    (R : M → ℝ) (hR : UpperSemicontinuous R) (f : N × ℝ≥0 → M) (hf : Continuous f)
    (hdiv : ∀ B : ℝ, ∃ T : ℝ≥0, ∀ (x : N) (t : ℝ≥0), T ≤ t → B < R (f (x, t))) :
    IsProperMap f := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨hf, ?_⟩
  intro K hK
  obtain ⟨B, hB⟩ := (hR.upperSemicontinuousOn K).bddAbove_of_isCompact hK
  obtain ⟨T, hT⟩ := hdiv B
  apply (isCompact_univ.prod (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) T))).of_isClosed_subset
    (hK.isClosed.preimage hf)
  intro z hz
  refine ⟨mem_univ _, zero_le, ?_⟩
  by_contra h
  have hbound := hB ⟨f z, hz, rfl⟩
  exact (not_lt_of_ge hbound) (hT z.1 z.2 (not_le.mp h).le)

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

variable {N M : Type*} [TopologicalSpace N] [TopologicalSpace M]

theorem closure_image_positive_half_cylinder_of_isProperMap
    (f : N × ℝ≥0 → M) (hf : IsProperMap f) :
    closure (f '' (univ ×ˢ Ioi (0 : ℝ≥0))) = range f := by
  rw [hf.isClosedMap.closure_image_eq_of_continuous hf.continuous,
    closure_prod_eq, closure_univ, closure_Ioi]
  have hnonneg : Ici (0 : ℝ≥0) = univ := by
    apply eq_univ_of_forall
    intro t
    exact t.property
  rw [hnonneg, univ_prod_univ, image_univ]

omit [TopologicalSpace N] [TopologicalSpace M] in
theorem range_sdiff_image_positive_half_cylinder
    (f : N × ℝ≥0 → M) (hf : Function.Injective f) :
    range f \ f '' (univ ×ˢ Ioi (0 : ℝ≥0)) = range (fun x => f (x, 0)) := by
  ext y
  constructor
  · rintro ⟨⟨⟨x, t⟩, rfl⟩, hy⟩
    have ht : t = 0 := by
      by_contra h
      exact hy ⟨(x, t), ⟨mem_univ _, lt_of_le_of_ne zero_le (Ne.symm h)⟩, rfl⟩
    exact ⟨x, by rw [ht]⟩
  · rintro ⟨x, rfl⟩
    refine ⟨mem_range_self (x, 0), ?_⟩
    rintro ⟨⟨z, t⟩, ht, heq⟩
    have hz := congrArg Prod.snd (hf heq)
    exact ht.2.ne' hz

end DifferentialGeometry.Topology


set_option autoImplicit false

open Set
open scoped NNReal

namespace DifferentialGeometry.Topology

def halfCylinderHomeomorphProdNNReal (N : Type*) [TopologicalSpace N] :
    {p : N × ℝ // 0 ≤ p.2} ≃ₜ N × ℝ≥0 where
  toFun p := (p.1.1, ⟨p.1.2, p.2⟩)
  invFun p := ⟨(p.1, p.2), p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.fst.prodMk
    (continuous_subtype_val.snd.subtype_mk _)
  continuous_invFun := (continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

variable {N M : Type*}

theorem range_half_cylinder_eq_image (f : N × ℝ → M) :
    range (fun p : {p : N × ℝ // 0 ≤ p.2} => f p.1) =
      f '' (univ ×ˢ Ici (0 : ℝ)) := by
  ext y
  constructor
  · rintro ⟨⟨p, hp⟩, rfl⟩
    exact ⟨p, ⟨mem_univ _, hp⟩, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp.2⟩, rfl⟩

theorem uniform_scalar_divergence_nnreal_iff (R : M → ℝ) (f : N × ℝ → M) (B : ℝ) :
    (∃ T : ℝ≥0, ∀ (x : N) (t : ℝ≥0), T ≤ t → B < R (f (x, t))) ↔
      ∃ T : ℝ, ∀ (x : N) (t : ℝ), T ≤ t → B < R (f (x, t)) := by
  constructor
  · rintro ⟨T, hT⟩
    refine ⟨T, ?_⟩
    intro x t ht
    exact hT x ⟨t, T.property.trans ht⟩ ht
  · rintro ⟨T, hT⟩
    refine ⟨⟨max T 0, le_max_right T 0⟩, ?_⟩
    intro x t ht
    exact hT x t ((le_max_left T 0).trans ht)

variable [TopologicalSpace N] [TopologicalSpace M]

theorem isProperMap_half_cylinder_iff (f : N × ℝ → M) :
    IsProperMap (fun p : {p : N × ℝ // 0 ≤ p.2} => f p.1) ↔
      IsProperMap (fun p : N × ℝ≥0 => f (p.1, p.2)) := by
  constructor
  · intro hf
    exact hf.comp (halfCylinderHomeomorphProdNNReal N).symm.isProperMap
  · intro hf
    exact hf.comp (halfCylinderHomeomorphProdNNReal N).isProperMap

theorem uniform_scalar_divergence_of_isProperMap_half_cylinder
    (R : M → ℝ) (hcompact : ∀ B : ℝ, IsCompact {x : M | R x ≤ B})
    (f : N × ℝ → M) (hf : IsProperMap (fun p : {p : N × ℝ // 0 ≤ p.2} => f p.1))
    (B : ℝ) :
    ∃ T : ℝ, ∀ (x : N) (t : ℝ), T ≤ t → B < R (f (x, t)) := by
  exact (uniform_scalar_divergence_nnreal_iff R f B).mp
    (uniform_scalar_divergence_of_isProperMap R hcompact
      (fun p : N × ℝ≥0 => f (p.1, p.2)) ((isProperMap_half_cylinder_iff f).mp hf) B)

end DifferentialGeometry.Topology
