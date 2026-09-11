import DifferentialGeometry.Geometry.Metric.CompactSourceDerivative







noncomputable section

open Set Bundle Manifold DifferentialGeometry
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

set_option backward.isDefEq.respectTransparency false in


theorem exists_compact_source_mfderiv_lower_bound
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {f : V → M} {U K : Set V}
    (hU : IsOpen U) (hf : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) 1 f U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f x)) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ v : V,
      c * ‖v‖ ≤ Real.sqrt (g.inner (f x) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f x v)
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f x v)) := by
  let A : V × V → ℝ := fun p => Real.sqrt (g.inner (f p.1)
    (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f p.1 p.2) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f p.1 p.2))
  let S := K ×ˢ Metric.sphere (0 : V) 1
  have hS : IsCompact S := hK.prod (isCompact_sphere (0 : V) 1)
  have hc : ContinuousOn A S :=
    (continuousOn_metric_mfderiv_norm g hU hf).mono (fun p hp => ⟨hKU hp.1, mem_univ _⟩)
  have hpos : ∀ p ∈ S, 0 < A p := by
    intro p hp
    apply Real.sqrt_pos.mpr
    apply g.pos
    have hv : p.2 ≠ 0 := by
      intro hv
      simpa [hv] using hp.2
    exact fun h => hv ((hinj p.1 hp.1) (h.trans (map_zero _).symm))
  have hl : ∃ c : ℝ, 0 < c ∧ ∀ p ∈ S, c ≤ A p := by
    by_cases hne : S.Nonempty
    · obtain ⟨p, hp, hmin⟩ := hS.exists_isMinOn hne hc
      exact ⟨A p, hpos p hp, fun q hq => hmin hq⟩
    · exact ⟨1, zero_lt_one, fun p hp => (hne ⟨p, hp⟩).elim⟩
  obtain ⟨c, hcp, hcl⟩ := hl
  refine ⟨c, hcp, fun x hx v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w : V := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := by
    simp [w, norm_smul, hvn.ne']
  have hvec : v = ‖v‖ • w := by simp [w, smul_smul, hvn.ne']
  have hcw : c ≤ A (x, w) := hcl (x, w) ⟨hx, by simpa using hw⟩
  calc
    c * ‖v‖ ≤ ‖v‖ * A (x, w) := by nlinarith
    _ = Real.sqrt (g.inner (f x) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f x v)
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f x v)) := by
      conv_rhs => rw [hvec]
      rw [show mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f x (‖v‖ • w) =
        ‖v‖ • mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f x w from map_smul _ _ _,
        sqrt_metric_smul, abs_of_pos hvn]



theorem exists_compact_source_metric_ellipticity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {f : V → M} {U K : Set V}
    (hU : IsOpen U) (hf : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) 1 f U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f x)) :
    ∃ m A : ℝ, 0 < m ∧ m ≤ A ∧ ∀ x ∈ K, ∀ v : V,
      m * ‖v‖ ^ 2 ≤ g.inner (f x) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f x v)
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f x v) ∧
      g.inner (f x) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f x v)
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f x v) ≤ A * ‖v‖ ^ 2 := by
  obtain ⟨c, hcp, hc⟩ := exists_compact_source_mfderiv_lower_bound g hU hf hK hKU hinj
  obtain ⟨C, hC⟩ := exists_compact_source_mfderiv_bound g hU hf hK hKU
  refine ⟨c ^ 2, max (c ^ 2) ((C : ℝ) ^ 2), sq_pos_of_pos hcp, ?_, fun x hx v => ?_⟩
  · exact le_max_left _ _
  · have hn : 0 ≤ g.inner (f x) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f x v)
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f x v) := by
      by_cases hz : mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f x v = 0
      · simp [hz]
      · exact (g.pos _ _ hz).le
    have hs := Real.sq_sqrt hn
    constructor
    · have h := mul_self_le_mul_self (by positivity : 0 ≤ c * ‖v‖) (hc x hx v)
      nlinarith
    · have h := mul_self_le_mul_self (Real.sqrt_nonneg _) (hC x hx v)
      have hmax : (C : ℝ) ^ 2 ≤ max (c ^ 2) ((C : ℝ) ^ 2) := le_max_right _ _
      nlinarith [mul_le_mul_of_nonneg_right hmax (sq_nonneg ‖v‖)]

end DifferentialGeometry.Geometry
