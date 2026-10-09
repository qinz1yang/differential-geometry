import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulCarrier

/-!
# Consumers of LFR47 (lane CMS3-CARRIER2, group G4b)

* the frozen interface `finiteSoul_transportedCarrier` VERBATIM, in the frozen ambient context
  (complete Riemannian `M`), as an `example`. Its proof does not use `[CompactSpace B]`,
  `[T2Space B]` or `hdimE`; the unused explicit binder is renamed `_hdimE`, and the statement text
  is otherwise unchanged;
* `finiteSoul_transportedCarrier_lift_eq_zero_of_norm_le`: the lift vanishes on the `δ`-disc bundle
  around the zero section, where `X` vanishes too.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.Topology (TransportedCarrier)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- The frozen interface LFR47, verbatim (`FiniteSoulThreeInterfaces.lean` :615–641). -/
example
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
    {B : Type*} [TopologicalSpace B] [ChartedSpace EB B] [IsManifold 𝓘(ℝ, EB) ∞ B] [CompactSpace B]
    [T2Space B]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ s, NormedAddCommGroup (V s)]
    [∀ s, InnerProductSpace ℝ (V s)] [FiberBundle F V] [VectorBundle ℝ F V]
    [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, EB)] [IsContMDiffRiemannianBundle 𝓘(ℝ, EB) ∞ F V]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 5 ≤ r)
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (_hdimE : Module.finrank ℝ EB + Module.finrank ℝ F = Module.finrank ℝ E)
    (e : TotalSpace F V ≃ₘ^((r - 2 : ℕ∞) : ℕ∞ω)⟮𝓘(ℝ, EB).prod 𝓘(ℝ, F), I⟯ M)
    (X : (x : M) → TangentSpace I x) {δ : ℝ} (hδ : 0 < δ) (prof : ℝ → ℝ)
    (hprof : ContDiff ℝ ∞ prof) (hprof0 : ∀ τ ≤ δ, prof τ = 0) (hXS : ∀ s : B, X (e ⟨s, 0⟩) = 0)
    (hXray : ∀ (s : B) (w : V s), ‖w‖ = 1 → ∀ τ : ℝ, 0 < τ → ∃ Y : TangentSpace I (e ⟨s, τ • w⟩),
      HasMFDerivAt 𝓘(ℝ, ℝ) I (fun t : ℝ => e ⟨s, t • w⟩) τ ((1 : ℝ →L[ℝ] ℝ).smulRight Y) ∧
        X (e ⟨s, τ • w⟩) = prof τ • Y) :
    (∃ Xhat : (z : TotalSpace F V) → TangentSpace (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) z,
      ContMDiff (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (𝓘(ℝ, EB).prod 𝓘(ℝ, F)).tangent ∞
        (fun z => (⟨z, Xhat z⟩ : TangentBundle (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (TotalSpace F V))) ∧
      ∀ z, mfderiv (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) I e z (Xhat z) = X (e z)) ∧
    ∀ (m' : ℕ∞ω) (hmn : m' ≤ (r : ℕ∞ω) + 1) (hmr : m' + 1 ≤ ((r - 2 : ℕ∞) : ℕ∞ω)), 2 ≤ m' →
      ∀ (y : TransportedCarrier e.toHomeomorph)
        (v w : TangentSpace (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) y),
        0 ≤ (TransportedCarrier.metric e g hmn hmr).sectionalCurvature y v w :=
  finiteSoul_transportedCarrier g hr hsec e X hδ prof hprof hprof0 hXS hXray

/-- **The lift vanishes on the `δ`-disc bundle** (`prof = 0` on `(-∞, δ]`): the soul-flow field is
zero near the soul in the new carrier as well. -/
theorem finiteSoul_transportedCarrier_lift_eq_zero_of_norm_le
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
    {B : Type*} [TopologicalSpace B] [ChartedSpace EB B]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ s, NormedAddCommGroup (V s)]
    [∀ s, InnerProductSpace ℝ (V s)] [FiberBundle F V] {δ : ℝ} {prof : ℝ → ℝ} (hprof0 : ∀ τ ≤ δ, prof τ = 0)
    (z : TotalSpace F V) (hz : ‖z.snd‖ ≤ δ) :
    carrierRadialField 𝓘(ℝ, EB) prof z = 0 := by
  have hq : Real.sqrt (inner ℝ z.snd z.snd) = ‖z.snd‖ := by
    rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  change carrierRadialCoeff prof (inner ℝ z.snd z.snd) • _ = _
  rw [carrierRadialCoeff, hq, hprof0 _ hz, zero_div, zero_smul]

end DifferentialGeometry.Geometry.FiniteSoul
