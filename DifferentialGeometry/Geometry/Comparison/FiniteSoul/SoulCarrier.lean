import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulCarrierEuler
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulCarrierCurvatureApplications

/-!
# LFR47: the smooth soul-flow carrier (lane CMS3-CARRIER2, group G4b)

Frozen interface `finiteSoul_transportedCarrier` (`build-logs/scratch/D-CMS3/FiniteSoulThreeInterfaces.lean`
:615–641; review §13, dispositions D6/D9). For the soul's smooth Riemannian normal bundle
`V → B` (model `EB × F`), a `C^{r−2}` diffeomorphism `e : TotalSpace F V → M` (`5 ≤ r`) and a field
`X` with LFR46's ray identification:

1. `X` lifts to a SMOOTH field `Xhat = prof(|w|) ∂_{|w|}` on the total space with `de ∘ Xhat = X ∘ e`
   (`exists_smooth_carrierLift`, SoulCarrierEuler.lean);
2. in the carrier transported along `e`, the UNCHANGED metric `g` read at any order
   `2 ≤ m' ≤ r − 3` has `sec ≥ 0` (`finiteSoul_transportedCarrier_sectional_nonneg`, cross-model
   curvature transfer, SoulCarrierCurvature.lean).

Proved form: the frozen statement minus the hypotheses its proof does not use
(`[CompactSpace B]`, `[T2Space B]`, `hdimE`; the ambient metric-space/Riemannian instances of `M`
are not needed either). The verbatim frozen statement is an `example` in
SoulCarrierApplications.lean.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.Topology (TransportedCarrier)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- `5 ≤ r` makes the `C^{r−2}` order nonzero. -/
theorem sub_two_ne_zero_of_five_le {r : ℕ∞} (hr : 5 ≤ r) : ((r - 2 : ℕ∞) : ℕ∞ω) ≠ 0 := by
  have h3 := three_le_sub_two_of_five_le hr
  intro h0
  rw [WithTop.coe_eq_zero] at h0
  rw [h0] at h3
  exact absurd h3 (by decide)

/-- **LFR47** (`5 ≤ r`): the smooth lift `Xhat` of the soul-flow field and `sec ≥ 0` of the
unchanged metric in the carrier transported along `e`. -/
theorem finiteSoul_transportedCarrier {r : ℕ∞}
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
    {B : Type*} [TopologicalSpace B] [ChartedSpace EB B] [IsManifold 𝓘(ℝ, EB) ∞ B]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ s, NormedAddCommGroup (V s)]
    [∀ s, InnerProductSpace ℝ (V s)] [FiberBundle F V] [VectorBundle ℝ F V]
    [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, EB)] [IsContMDiffRiemannianBundle 𝓘(ℝ, EB) ∞ F V]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 5 ≤ r)
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
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
  ⟨exists_smooth_carrierLift (e.mdifferentiable (sub_two_ne_zero_of_five_le hr)) X hδ prof hprof
      hprof0 hXS hXray,
    fun m' hmn hmr hm y v w =>
      finiteSoul_transportedCarrier_sectional_nonneg g hr hsec e m' hmn hmr hm y v w⟩

end DifferentialGeometry.Geometry.FiniteSoul
