import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulCarrierCurvature

/-!
# Consumer of the cross-model curvature transfer (lane CMS3-CARRIER2, group G4a)

`finiteSoul_transportedCarrier_sectional_nonneg`: the curvature half of LFR47 in its frozen setting.
The carrier is the total space of a smooth vector bundle `V → B` (model `EB × F`, not the model `E`
of `M`), transported to `M` along the `C^{r−2}` diffeomorphism `e` (`5 ≤ r`); the UNCHANGED metric
`g` (order `r + 1`, `sec ≥ 0`) read in that carrier at any order `2 ≤ m' ≤ r − 3` still has
`sec ≥ 0`.
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

/-- `5 ≤ r` gives `3 ≤ r − 2` in `ℕ∞`. -/
theorem three_le_sub_two_of_five_le {r : ℕ∞} (hr : 5 ≤ r) : (3 : ℕ∞) ≤ r - 2 :=
  le_of_eq_of_le rfl (tsub_le_tsub_right hr 2)

/-- **LFR47, curvature half, in the soul-bundle carrier.** -/
theorem finiteSoul_transportedCarrier_sectional_nonneg {r : ℕ∞}
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
    {B : Type*} [TopologicalSpace B] [ChartedSpace EB B] [IsManifold 𝓘(ℝ, EB) ∞ B]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ s, NormedAddCommGroup (V s)]
    [∀ s, NormedSpace ℝ (V s)] [FiberBundle F V] [VectorBundle ℝ F V]
    [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, EB)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 5 ≤ r)
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (e : TotalSpace F V ≃ₘ^((r - 2 : ℕ∞) : ℕ∞ω)⟮𝓘(ℝ, EB).prod 𝓘(ℝ, F), I⟯ M)
    (m' : ℕ∞ω) (hmn : m' ≤ (r : ℕ∞ω) + 1) (hmr : m' + 1 ≤ ((r - 2 : ℕ∞) : ℕ∞ω)) (hm : 2 ≤ m')
    (y : TransportedCarrier e.toHomeomorph) (v w : TangentSpace (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) y) :
    0 ≤ (TransportedCarrier.metric e g hmn hmr).sectionalCurvature y v w :=
  TransportedCarrier.metric_sectionalCurvature_nonneg_cross e g hmn hmr
    (three_le_sub_two_of_five_le hr) hm (hm.trans hmn) hsec y v w

end DifferentialGeometry.Geometry.FiniteSoul
