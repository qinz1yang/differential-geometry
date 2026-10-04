import DifferentialGeometry.Geometry.Collapse.SublevelCore.OpenBallModelTypeAtScale

/-!
# Consumer of LC61 at a fixed scale: open balls of comparable radii are diffeomorphic

From `exists_scale_eventually_open_ball_model_type`: at every fixed scale `R ≥ R₀`, one tail has,
for all `ρ₁, ρ₂ ∈ [1/5, 2]`, a diffeomorphism of the open ball `B(p_i, ρ₁ R)` onto `B(p_i, ρ₂ R)`
(both are diffeomorphic to the model).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open GC.MetricGeometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type} [m : MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [SigmaCompactSpace N]
  [ConnectedSpace N] [RiemannianBundle (fun x : N => TangentSpace I x)]
  [IsRiemannianManifold I N] [hNc : CompleteSpace N]
  [IsContinuousRiemannianBundle E (fun x : N => TangentSpace I x)]
  [T2Space (TangentBundle I N)]
  {M : ℕ → Type} [mM : ∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)] [∀ i, SigmaCompactSpace (M i)]
  [∀ i, RiemannianBundle (fun x : M i => TangentSpace I x)]
  [∀ i, IsRiemannianManifold I (M i)] [hMc : ∀ i, CompleteSpace (M i)]
  [∀ i, IsContinuousRiemannianBundle E (fun x : M i => TangentSpace I x)]

/-- **Consumer of `exists_scale_eventually_open_ball_model_type`.** At every fixed scale
`R ≥ R₀`, one tail has the open balls `B(p_i, ρ₁ R)` and `B(p_i, ρ₂ R)`, `ρ₁, ρ₂ ∈ [1/5, 2]`,
diffeomorphic. -/
theorem exists_scale_eventually_open_balls_diffeomorphic [NoncompactSpace N] {mdim : ℕ}
    (hdim : Module.finrank ℝ E = mdim + 1) (g : SmoothRiemannianMetric I N)
    (hNorm : IsMetricNorm (I := I) (M := N) g) (hsec : ∀ x, SectionalBoundedBelowAt g x 0)
    (n : N) {C : Type} [MetricSpace C] {o : C} (Hc : RadialConeData o)
    (hcone : ∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
      Nonempty (@KleinerLottApprox N C (m.rescale R⁻¹ (inv_pos.mpr hR)) _ n o τ))
    (gSeq : ∀ i, SmoothRiemannianMetric I (M i)) (hSeqNorm : ∀ i, IsMetricNorm (gSeq i))
    (j : ∀ i, PartialDiffeomorph I I N (M i) ∞)
    (hGH : PointedGHConverges (fun i => j i n) n)
    (hC1 : ∀ r : ℝ, 0 < r → ∃ i₀ : ℕ, ∃ hsub : ∀ k,
      ((⟨Metric.ball n r, Metric.isOpen_ball⟩ : TopologicalSpace.Opens N) : Set N) ⊆
        (j (k + i₀)).source,
      ∀ C : Set (⟨Metric.ball n r, Metric.isOpen_ball⟩ : TopologicalSpace.Opens N),
        IsCompact C → MetricCPConvergenceOn C 1
          (fun k => PartialDiffeomorph.pullbackMetricOn (j (k + i₀)) _ (hsub k) (gSeq (k + i₀)))
          (g.restrictOpen _) (g.restrictOpen _))
    (Hb : ℕ → ℝ) (hHb : Tendsto Hb atTop atTop)
    (hsecM : ∀ i, ∀ y ∈ Metric.ball (j i n) (Hb i),
      SectionalBoundedBelowAt (gSeq i) y (-((Hb i)⁻¹ ^ 2))) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ᶠ i in atTop, ∀ ρ₁ ∈ Icc (1 / 5 : ℝ) 2,
      ∀ ρ₂ ∈ Icc (1 / 5 : ℝ) 2, ∃ Ψ : PartialDiffeomorph I I (M i) (M i) ∞,
        Ψ.source = Metric.ball (j i n) (ρ₁ * R) ∧ Ψ.target = Metric.ball (j i n) (ρ₂ * R) := by
  obtain ⟨R₀, hR₀, hall⟩ := exists_scale_eventually_open_ball_model_type hdim g hNorm hsec n Hc
    hcone gSeq hSeqNorm j hGH hC1 Hb hHb hsecM
  refine ⟨R₀, hR₀, fun R hR => ?_⟩
  filter_upwards [hall R hR] with i hi ρ₁ hρ₁ ρ₂ hρ₂
  obtain ⟨Ψ₁, h1s, h1t⟩ := hi ρ₁ hρ₁
  obtain ⟨Ψ₂, h2s, h2t⟩ := hi ρ₂ hρ₂
  refine ⟨Ψ₁.trans Ψ₂.symm, ?_, ?_⟩
  · rw [PartialDiffeomorph.trans_source, h1s, PartialDiffeomorph.symm_source, h2t, preimage_univ,
      inter_univ]
  · ext y
    constructor
    · intro hy
      have hy' : y ∈ Ψ₂.symm.target := hy.1
      rwa [PartialDiffeomorph.symm_target, h2s] at hy'
    · intro hy
      have hy' : y ∈ Ψ₂.source := by rw [h2s]; exact hy
      refine ⟨hy', ?_⟩
      change Ψ₂ y ∈ Ψ₁.target
      rw [h1t]
      exact mem_univ _

end DifferentialGeometry.Geometry.Collapse
