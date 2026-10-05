import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimFibreGraph

/-!
# Consumer: (LFR20.1) along the vertical field gives monotone coordinate lines

`strictMonoOn_comp_splitting_line`: if `f` is differentiable along the coordinate line
`s ↦ Φ⁻¹(s, w)` and `df(V) > 0` there for `s ∈ [-b, b]`, then `s ↦ f(Φ⁻¹(s, w))` is strictly
increasing on `[-b, b]` — the input `hmono` of `nonempty_homeomorph_zeroLevel_of_graph`, from the
derivative bound (LFR20.1) of `eventually_three_quarters_lt_mvfderiv_vertical`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Metric Bundle WithLp
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]
  [CompleteSpace N] {r : ℕ∞} {W : Type*} [MetricSpace W]

/-- **Monotone coordinate lines.** A positive derivative along `V` on the line makes the
restriction of `f` to the line strictly increasing. -/
theorem strictMonoOn_comp_splitting_line
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) {ℓ : ℝ} (hℓ : 0 < ℓ) (V : ∀ x : N, TangentSpace I x)
    (hVdir : ∀ x, G.finiteMinimizingDirectionsTo
      {Φ.symm (toLp 2 ((Φ x).fst + ℓ, (Φ x).snd))} x = {V x})
    {f : N → ℝ} (w₀ : W) {b : ℝ}
    (hf : ∀ s ∈ Icc (-b) b, MDifferentiableAt I 𝓘(ℝ, ℝ) f (Φ.symm (toLp 2 (s, w₀))))
    (hpos : ∀ s ∈ Icc (-b) b,
      0 < mvfderiv I f (Φ.symm (toLp 2 (s, w₀))) (V (Φ.symm (toLp 2 (s, w₀))))) :
    StrictMonoOn (fun s => f (Φ.symm (toLp 2 (s, w₀)))) (Icc (-b) b) := by
  have hder : ∀ s ∈ Icc (-b) b, HasDerivAt (fun s => f (Φ.symm (toLp 2 (s, w₀))))
      (mvfderiv I f (Φ.symm (toLp 2 (s, w₀))) (V (Φ.symm (toLp 2 (s, w₀))))) s :=
    fun s hs => hasDerivAt_comp_splitting_line G hr hnorm Φ hℓ V hVdir w₀ s (hf s hs)
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · exact fun s hs => (hder s hs).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    rw [(hder s (Ioo_subset_Icc_self hs)).deriv]
    exact hpos s (Ioo_subset_Icc_self hs)

end DifferentialGeometry.Geometry.Collapse
