import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulCarrierFlow

/-!
# Consumer of the smooth carrier flow (lane CMS3-CARRIER2, group G4c)

`exists_smooth_carrierFlow_inner_le`: LFR47's "its complete flow, norm bound ... are the same ones
as before" for the norm bound. The generator `W` of the SAME flow `φ`, which is smooth in the
carrier transported along `e`, has the same `g`-length as LFR46's field `X`. It is measured in the
UNCHANGED metric `g` read in the new carrier (`TransportedCarrier.metric`, any admissible order).
So LFR46's `g (X, X) ≤ 4` gives `|W| ≤ 2` there.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.Topology (TransportedCarrier)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- **The smooth carrier flow keeps LFR46's norm bound** in the unchanged metric. -/
theorem exists_smooth_carrierFlow_inner_le {r : ℕ∞}
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
    {B : Type*} [TopologicalSpace B] [ChartedSpace EB B] [IsManifold 𝓘(ℝ, EB) ∞ B]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ s, NormedAddCommGroup (V s)]
    [∀ s, InnerProductSpace ℝ (V s)] [FiberBundle F V] [VectorBundle ℝ F V]
    [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, EB)] [IsContMDiffRiemannianBundle 𝓘(ℝ, EB) ∞ F V]
    {n m' : ℕ∞ω} (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (e : TotalSpace F V ≃ₘ^((r - 2 : ℕ∞) : ℕ∞ω)⟮𝓘(ℝ, EB).prod 𝓘(ℝ, F), I⟯ M)
    (hmn : m' ≤ n) (hmr : m' + 1 ≤ ((r - 2 : ℕ∞) : ℕ∞ω))
    (X : (x : M) → TangentSpace I x) {A : ℝ} (hXb : ∀ x, g.inner x (X x) (X x) ≤ A)
    {δ : ℝ} (hδ : 0 < δ) (prof : ℝ → ℝ)
    (hprof : ContDiff ℝ ∞ prof) (hprof0 : ∀ τ ≤ δ, prof τ = 0) (hXS : ∀ s : B, X (e ⟨s, 0⟩) = 0)
    (hXray : ∀ (s : B) (w : V s), ‖w‖ = 1 → ∀ τ : ℝ, 0 < τ → ∃ Y : TangentSpace I (e ⟨s, τ • w⟩),
      HasMFDerivAt 𝓘(ℝ, ℝ) I (fun t : ℝ => e ⟨s, t • w⟩) τ ((1 : ℝ →L[ℝ] ℝ).smulRight Y) ∧
        X (e ⟨s, τ • w⟩) = prof τ • Y)
    (φ : ℝ → M → M) (hφ0 : ∀ x, φ 0 x = x) (hφadd : ∀ s t x, φ (s + t) x = φ s (φ t x))
    (hφX : ∀ t x, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => φ s x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X (φ t x))))
    {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hray : ∀ (s : B) (w : V s), ‖w‖ = 1 → ∀ t : ℝ, ℓ < t →
      e ⟨s, t • w⟩ = φ (t - ℓ) (e ⟨s, ℓ • w⟩)) :
    ∃ (ϕ : Flow ℝ (TransportedCarrier e.toHomeomorph))
      (W : (y : TransportedCarrier e.toHomeomorph) → TangentSpace (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) y),
      (∀ t y, (ϕ t y).point = φ t y.point) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, EB).prod 𝓘(ℝ, F))) (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) ∞
        (fun q : ℝ × TransportedCarrier e.toHomeomorph => ϕ q.1 q.2) ∧
      (∀ t y, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (fun s => ϕ s y) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (W (ϕ t y)))) ∧
      ∀ y, (TransportedCarrier.metric e g hmn hmr).inner y (W y) (W y) ≤ A := by
  obtain ⟨ϕ, W, hpt, hsm, -, hWX, hgen, -, -⟩ :=
    exists_smooth_carrierFlow hr e X hδ prof hprof hprof0 hXS hXray φ hφ0 hφadd hφX hℓ hray
  refine ⟨ϕ, W, hpt, hsm, hgen, fun y => ?_⟩
  rw [TransportedCarrier.metric_inner, hWX y]
  exact hXb y.point

end DifferentialGeometry.Geometry.FiniteSoul
