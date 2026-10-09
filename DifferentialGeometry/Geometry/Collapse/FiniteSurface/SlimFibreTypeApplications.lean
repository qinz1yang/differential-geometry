import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimFibreType

/-!
# Consumer: the zero fibre inherits compactness and connectedness from the factor

`compactSpace_connectedSpace_zeroLevel_of_splitting`: under the hypotheses of
`nonempty_homeomorph_zeroLevel_of_splitting`, the ENTIRE zero level `{y ∈ S | η y = 0}` is compact,
and connected whenever the zero factor of `N` is connected (LFR20 step 4: "this gives connectedness").
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

/-- **Consumer.** The zero level is compact, and connected if the zero factor is. -/
theorem compactSpace_connectedSpace_zeroLevel_of_splitting [CompactSpace W]
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) {ℓ : ℝ} (hℓ : 0 < ℓ) (V : ∀ x : N, TangentSpace I x)
    (hVdir : ∀ x, G.finiteMinimizingDirectionsTo
      {Φ.symm (toLp 2 ((Φ x).fst + ℓ, (Φ x).snd))} x = {V x})
    {X : Type*} [TopologicalSpace X] [T2Space X] (J : N → X) {b c : ℝ} (hc : 0 < c)
    (hcb : c ≤ b) (hJ : ContinuousOn J {x | |(Φ x).fst| ≤ b})
    (hJinj : InjOn J {x | |(Φ x).fst| ≤ b}) {η : X → ℝ} (hη : Continuous η)
    (hfd : ∀ x, |(Φ x).fst| ≤ b → MDifferentiableAt I 𝓘(ℝ, ℝ) (η ∘ J) x)
    (hpos : ∀ x, |(Φ x).fst| ≤ b → 0 < mvfderiv I (η ∘ J) x (V x))
    (hval : ∀ x, |(Φ x).fst| ≤ b → |η (J x) - (Φ x).fst| < c)
    {S : Set X} (hS : ∀ x, |(Φ x).fst| < b → η (J x) = 0 → J x ∈ S)
    (hencl : ∀ y ∈ S, η y = 0 → ∃ x, |(Φ x).fst| ≤ b ∧ J x = y) :
    CompactSpace {y // y ∈ S ∧ η y = 0} ∧
      (ConnectedSpace {x : N // (Φ x).fst = 0} → ConnectedSpace {y // y ∈ S ∧ η y = 0}) := by
  obtain ⟨h⟩ := nonempty_homeomorph_zeroLevel_of_splitting G hr hnorm Φ hℓ V hVdir J hc hcb hJ
    hJinj hη hfd hpos hval hS hencl
  have : CompactSpace {x : N // (Φ x).fst = 0} :=
    isCompact_iff_compactSpace.mp (isCompact_splitting_zeroFactor Φ)
  exact ⟨h.symm.compactSpace, fun hZ => h.connectedSpace_iff.mpr hZ⟩

end DifferentialGeometry.Geometry.Collapse
