import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalFlowMarginTransport
import DifferentialGeometry.Geometry.Metric.Pullback.TransportedCarrier

/-!
# LFR46.2 in the transported carrier of LFR47 (lane CMS3-FLOW2, G4; LFR49 item (b))

The carrier `N' = TransportedCarrier e` of LFR47 (the points of `M` with the smooth structure of
the total space, transported along LFR46's `C^(r−2)` diffeomorphism `e`) carries the UNCHANGED metric
`G = TransportedCarrier.metric e g` and LFR47's smooth field `W` reading as `X` through the identity
transition (`exists_smooth_carrierFlow`). The identity transition is a `C¹` isometry with
`G = id^* g`, so `G`'s finite minimizing directions go to `g`'s
(`mfderiv_mem_finiteMinimizingDirectionsTo_of_isometry`), and LFR46.2's margin of `X` becomes the
margin of `W` against `G`'s FINITE minimizing directions, as LFR49's kernel T4 (`hVdir`) consumes.

The Riemannian-bundle structure of `N'` whose norm is `G` (and `IsRiemannianManifold`) is an
instance argument here: installing it is part of LFR49's item (a) (the carrier rechart).

* `inner_le_carrierMargin`: the margin of `W` against `G`'s finite minimizing directions to the
  carrier point of `p`, beyond `A₂`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.Topology (TransportedCarrier)

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

section Carrier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  {B : Type*} [TopologicalSpace B] [ChartedSpace EB B] [IsManifold 𝓘(ℝ, EB) ∞ B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ s, AddCommMonoid (V s)]
  [∀ s, Module ℝ (V s)] [∀ s, TopologicalSpace (V s)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, EB)]

variable {r : ℕ∞}

/-- **LFR46.2 in the carrier (LFR49 item (b)).** Let `e` be LFR46's `C^(r−2)` diffeomorphism
(`3 ≤ r`), `G = TransportedCarrier.metric e g` the unchanged metric read in the carrier (order
`r' + 1`, `2 ≤ r'`), Riemannian on the carrier (`hGnorm`), and `W` a field on the carrier reading
as `X` through the identity transition. If `X` has LFR46.2's margin `−1/4` against `g`'s minimizing
directions to `p` beyond `A₂`, then `W` has it against `G`'s FINITE minimizing directions to the
carrier point of `p`. -/
theorem inner_le_carrierMargin
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : TotalSpace F V ≃ₘ^((r - 2 : ℕ∞) : ℕ∞ω)⟮𝓘(ℝ, EB).prod 𝓘(ℝ, F), I⟯ M)
    [RiemannianBundle (fun y : TransportedCarrier e.toHomeomorph =>
      TangentSpace (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) y)]
    [IsRiemannianManifold (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (TransportedCarrier e.toHomeomorph)]
    {r' : ℕ∞} (hr' : 2 ≤ r') (hmn : ((r' : ℕ∞ω) + 1) ≤ (r : ℕ∞ω) + 1)
    (hmr : ((r' : ℕ∞ω) + 1) + 1 ≤ ((r - 2 : ℕ∞) : ℕ∞ω))
    (hGnorm : ∀ (y : TransportedCarrier e.toHomeomorph)
      (w : TangentSpace (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt ((TransportedCarrier.metric e g hmn hmr).inner y w w)))
    (X : (x : M) → TangentSpace I x)
    (W : (y : TransportedCarrier e.toHomeomorph) → TangentSpace (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) y)
    (hWX : ∀ y, mfderiv (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) I (TransportedCarrier.identity e) y (W y) =
      X y.point)
    (p : M) {A₂ : ℝ}
    (hXp : ∀ q, A₂ ≤ dist p q → ∀ u ∈ g.finiteMinimizingDirectionsTo {p} q,
      g.inner q (X q) u ≤ -(1 / 4)) :
    ∀ y : TransportedCarrier e.toHomeomorph, A₂ ≤ dist (⟨p⟩ : TransportedCarrier e.toHomeomorph) y →
      ∀ v ∈ (TransportedCarrier.metric e g hmn hmr).finiteMinimizingDirectionsTo
        {(⟨p⟩ : TransportedCarrier e.toHomeomorph)} y,
        (TransportedCarrier.metric e g hmn hmr).inner y (W y) v ≤ -(1 / 4) := by
  have hk : ((r - 2 : ℕ∞) : ℕ∞ω) ≠ 0 := by
    intro h0
    have h1 : (r - 2 : ℕ∞) = 0 := by exact_mod_cast h0
    have h2 : r ≤ 2 := tsub_eq_zero_iff_le.mp h1
    exact absurd (hr.trans h2) (by decide)
  have hFi : Isometry (TransportedCarrier.identity e) :=
    Isometry.of_dist_eq fun _ _ => rfl
  exact inner_le_of_finiteMinimizingDirectionsTo_of_isometry g (le_trans (by norm_num) hr) hnorm
    (TransportedCarrier.metric e g hmn hmr) hr' hGnorm
    (fun y => (TransportedCarrier.identity e).mdifferentiable hk y) hFi
    (fun y v w => TransportedCarrier.metric_inner e g hmn hmr y v w) X W hWX ⟨p⟩ hXp

end Carrier

section Interface

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **LFR49 item (b), the binding interface** (`build-logs/scratch/LFR49/Assembly.lean`, verbatim
statement): a `C¹` distance-preserving `κ` with `G' = κ^* g` carries the finite minimizing
directions of `G'` to a set `T` into those of `g` to `κ '' T`. One line from the cross-model kernel
`mfderiv_mem_finiteMinimizingDirectionsTo_of_isometry`. -/
theorem cms3flow2_finiteMinimizingDirectionsTo_map
    {N' M : Type*} [MetricSpace N'] [ChartedSpace H N'] [IsManifold I ∞ N']
    [RiemannianBundle (fun x : N' => TangentSpace I x)] [IsRiemannianManifold I N']
    [CompleteSpace N']
    [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]
    {r' r : ℕ∞} (hr' : 2 ≤ r') (hr : 2 ≤ r)
    (G' : ContMDiffRiemannianMetric I ((r' : ℕ∞ω) + 1) E (TangentSpace I : N' → Type _))
    (hG'norm : ∀ (x : N') (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G'.inner x w w)))
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hgnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (κ : N' → M) (hκ : ContMDiff I I 1 κ) (hκd : ∀ x y, dist (κ x) (κ y) = dist x y)
    (hκG : ∀ (y : N') (v w : TangentSpace I y),
      G'.inner y v w = g.inner (κ y) (mfderiv I I κ y v) (mfderiv I I κ y w))
    (T : Set N') (y : N') (v : TangentSpace I y) (hv : v ∈ G'.finiteMinimizingDirectionsTo T y) :
    mfderiv I I κ y v ∈ g.finiteMinimizingDirectionsTo (κ '' T) (κ y) :=
  mfderiv_mem_finiteMinimizingDirectionsTo_of_isometry g hr hgnorm G' hr' hG'norm
    (fun z => (hκ z).mdifferentiableAt one_ne_zero) (Isometry.of_dist_eq hκd) hκG hv

end Interface

end DifferentialGeometry.Geometry.FiniteSoul
