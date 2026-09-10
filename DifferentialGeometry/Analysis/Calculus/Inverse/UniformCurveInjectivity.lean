import DifferentialGeometry.Topology.Compactness.UniformBounds
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open Set Filter Topology

namespace Poincare.Analysis

theorem exists_uniform_injOn_of_continuous_deriv
    {P E : Type*} [TopologicalSpace P] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : Set P} (hK : IsCompact K) {γ dγ : P → ℝ → E}
    (hdγ : Continuous (fun q : P × ℝ ↦ dγ q.1 q.2))
    (hderiv : ∀ p ∈ K, ∀ t, HasDerivAt (γ p) (dγ p t) t)
    (hzero : ∀ p ∈ K, dγ p 0 ≠ 0) :
    ∃ ε > 0, ∀ p ∈ K, InjOn (γ p) (Icc (-ε) ε) := by
  let D : P × ℝ → ℝ := fun q ↦ inner ℝ (dγ q.1 0) (dγ q.1 q.2)
  have hD : Continuous D :=
    (hdγ.comp (continuous_fst.prodMk continuous_const)).inner hdγ
  have hpos (p : P) (hp : p ∈ K) : 0 < D (p, 0) :=
    real_inner_self_pos.mpr (hzero p hp)
  obtain ⟨m, hm, V, hV, hbound⟩ :=
    Poincare.Topology.Compactness.exists_pos_uniform_lower_bound hK
      (fun _ _ ↦ hD.continuousAt) hpos
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨r / 2, half_pos hr, fun p hp ↦ ?_⟩
  let f : ℝ → ℝ := fun t ↦ inner ℝ (dγ p 0) (γ p t)
  have hf (t : ℝ) : HasDerivAt f (D (p, t)) t := by
    simpa only [D, inner_zero_left, add_zero] using
      (hasDerivAt_const t (dγ p 0)).inner ℝ (hderiv p hp t)
  have hmono : StrictMonoOn f (Icc (-(r / 2)) (r / 2)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun t _ ↦ (hf t).continuousAt.continuousWithinAt)
    intro t ht
    rw [(hf t).deriv]
    apply hm.trans_le (hbound p hp t (hrV ?_))
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    have ht' : t ∈ Icc (-(r / 2)) (r / 2) := interior_subset ht
    exact (abs_le.mpr ht').trans_lt (half_lt_self hr)
  intro s hs t ht he
  exact hmono.injOn hs ht (congrArg (fun z ↦ inner ℝ (dγ p 0) z) he)

theorem exists_uniform_injOn_of_continuous_deriv_on_Icc
    {P E : Type*} [TopologicalSpace P] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : Set P} (hK : IsCompact K) {γ dγ : P → ℝ → E} {ρ : ℝ} (hρ : 0 < ρ)
    (hdγ : ContinuousOn (fun q : P × ℝ ↦ dγ q.1 q.2) (K ×ˢ Icc 0 ρ))
    (hderiv : ∀ p ∈ K, ∀ t ∈ Icc 0 ρ, HasDerivWithinAt (γ p) (dγ p t) (Icc 0 ρ) t)
    (hzero : ∀ p ∈ K, dγ p 0 ≠ 0) :
    ∃ ε > 0, ε ≤ ρ ∧ ∀ p ∈ K, InjOn (γ p) (Icc 0 ε) := by
  let D : P × ℝ → ℝ := fun q ↦ inner ℝ (dγ q.1 0) (dγ q.1 q.2)
  have hd₀ : ContinuousOn (fun q : P × ℝ ↦ dγ q.1 0) (K ×ˢ Icc 0 ρ) :=
    hdγ.comp (continuous_fst.prodMk continuous_const).continuousOn
      (fun _ hq ↦ ⟨hq.1, le_rfl, hρ.le⟩)
  have hD : ContinuousOn D (K ×ˢ Icc 0 ρ) := hd₀.inner hdγ
  obtain ⟨ε, hε, hερ, m, hm, hbound⟩ :=
    Poincare.Topology.Compactness.exists_pos_uniform_lower_bound_on_Icc hK hρ hD
      (fun p hp ↦ real_inner_self_pos.mpr (hzero p hp))
  refine ⟨ε, hε, hερ, fun p hp ↦ ?_⟩
  let f : ℝ → ℝ := fun t ↦ inner ℝ (dγ p 0) (γ p t)
  have hsub : Icc (0 : ℝ) ε ⊆ Icc 0 ρ := Icc_subset_Icc_right hερ
  have hf (t : ℝ) (ht : t ∈ Icc 0 ε) : HasDerivWithinAt f (D (p, t)) (Icc 0 ε) t := by
    have he := (hasDerivAt_const t (dγ p 0)).hasDerivWithinAt.inner ℝ
      (hderiv p hp t (hsub ht))
    simpa only [D, inner_zero_left, add_zero] using he.mono hsub
  have hmono : StrictMonoOn f (Icc 0 ε) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
      (fun t ht ↦ (hf t ht).continuousWithinAt)
      (fun t ht ↦ (hf t (interior_subset ht)).mono interior_subset)
      (fun t ht ↦ hm.trans_le (hbound p hp t (interior_subset ht)))
  intro s hs t ht he
  exact hmono.injOn hs ht (congrArg (fun z ↦ inner ℝ (dγ p 0) z) he)

end Poincare.Analysis
