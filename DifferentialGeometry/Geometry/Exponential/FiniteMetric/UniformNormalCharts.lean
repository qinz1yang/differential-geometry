import DifferentialGeometry.Geometry.Exponential.FiniteMetric.UniformInverse
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.NormalBall

/-!
# Uniform normal charts of a finite-regularity metric (CM1.d)

On a compact set `K` there is a uniform radius `ρ > 0` such that for every `x ∈ K`, `exp_x` is a
`C^r` chart from the `g_x`-ball of radius `ρ` onto the metric ball `ball x ρ`, with
`dist x (exp_x v) = |v|_{g_x}` (`exists_uniform_normal_charts`). Assembly of the uniform local
inverses (`exists_nhds_expMap_partialHomeomorph`) and the normal-ball theorem
(`expChart_target_eq_ball_and_dist_eq`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric
open scoped Manifold ContDiff Topology

namespace Bundle.ContMDiffRiemannianMetric

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  {r : ℕ∞} (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))

/-- **CM1.d** Uniform normal charts on a compact set, with the Gauss-lemma distance identity. -/
theorem exists_uniform_normal_charts (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {K : Set M} (hK : IsCompact K) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ K, ∃ e : OpenPartialHomeomorph E M,
      e.source = {v : E | g.inner x v v < ρ ^ 2} ∧ e.target = ball x ρ ∧
      (∀ v ∈ e.source, (⟨x, v⟩ : TangentBundle I M) ∈ g.expDomain ∧
        e v = g.expMap (⟨x, v⟩ : TangentBundle I M)) ∧
      ContMDiffOn 𝓘(ℝ, E) I r e e.source ∧ ContMDiffOn I 𝓘(ℝ, E) r e.symm e.target ∧
      ∀ v ∈ e.source, dist x (e v) = Real.sqrt (g.inner x v v) := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  choose W hW δ hδ hprop using fun x₀ : M => g.exists_nhds_expMap_partialHomeomorph hr1 x₀
  -- the conclusion for a given radius, at a point of some `W x₀`
  have hgood : ∀ x₀ x : M, x ∈ W x₀ → ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ x₀ →
      ∃ e : OpenPartialHomeomorph E M,
        e.source = {v : E | g.inner x v v < ρ ^ 2} ∧ e.target = ball x ρ ∧
        (∀ v ∈ e.source, (⟨x, v⟩ : TangentBundle I M) ∈ g.expDomain ∧
          e v = g.expMap (⟨x, v⟩ : TangentBundle I M)) ∧
        ContMDiffOn 𝓘(ℝ, E) I r e e.source ∧ ContMDiffOn I 𝓘(ℝ, E) r e.symm e.target ∧
        ∀ v ∈ e.source, dist x (e v) = Real.sqrt (g.inner x v v) := by
    intro x₀ x hx ρ hρ hρδ
    obtain ⟨e, hsrc, hexp, hsm, hsymm⟩ := hprop x₀ x hx ρ hρ.le hρδ
    obtain ⟨htgt, hdist⟩ :=
      g.expChart_target_eq_ball_and_dist_eq hr hnorm hρ e hsrc hexp hsymm
    exact ⟨e, hsrc, htgt, hexp, hsm, hsymm, hdist⟩
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨1, one_pos, fun x hx => absurd hx (notMem_empty x)⟩
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover W (fun x _ => hW x)
  have htne : t.Nonempty := by
    obtain ⟨x, hx⟩ := hKne
    have h := hcover hx
    simp only [mem_iUnion] at h
    obtain ⟨x₀, hx₀, -⟩ := h
    exact ⟨x₀, hx₀⟩
  refine ⟨t.inf' htne δ, (Finset.lt_inf'_iff htne).mpr (fun x₀ _ => hδ x₀), fun x hx => ?_⟩
  have h := hcover hx
  simp only [mem_iUnion] at h
  obtain ⟨x₀, hx₀, hxW⟩ := h
  exact hgood x₀ x hxW _ ((Finset.lt_inf'_iff htne).mpr (fun x₀ _ => hδ x₀))
    (Finset.inf'_le δ hx₀)

end Bundle.ContMDiffRiemannianMetric
