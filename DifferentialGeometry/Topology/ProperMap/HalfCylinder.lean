import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

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
