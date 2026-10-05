import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeDiskPacket

/-!
# LC84 item 4: the LC81 comparison of an edge chart with `ℝ × Z`

Blueprint LC84 (`def:collapse-edge-packet`, master207A:30874), item 4: "a buffered comparison with
`ℝ × Z` from LC81, where `Z` is a complete orientable nonnegative surface"; LFR28
(`thm:collapse-finite-source-edge-packet`, A:27223): "There is one complete nonnegative `C^{K-1}`
product model `ℝ × Z` and an actual `C^K` embedding of the whole buffered model domain from LFR24,
containing the ENTIRE source closed slab `|f| ≤ 4Δ`, `η ≤ 4Δ`. ... Any prescribed positive
finite-buffer metric/distance comparison tolerance may be imposed by further reducing `β`."

`EdgeProductModel c K` records, for an edge chart `c` (coordinate `η_p = c.coord`, height
`H = edgeRowHeight Δ F ρ`):
* the finite model `N` (proper, connected, Riemannian for a `C^{K-1}` metric `G`, `sec ≥ 0`);
* the surface `Z = S` (smooth surface, Riemannian for a `C^{K-1}` metric `κ`, `sec ≥ 0`, oriented)
  and the product structure `Θ : ℝ × S ≃ₘ N` of class `C^K`: an isometry from `ℓ²(ℝ × S)`
  (`dist_Θ`) with `Θ^* G = dt² + κ` (`product_metric`);
* the actual `C^K` embedding `j : N ⇀ M`, pointed at `Θ (0, s₀) ↦ center`;
* `slab`: the ENTIRE source closed slab `{y ∈ B(center, 100Δ) : |η_p| ≤ 4Δ, H ≤ 4Δ}` is the
  `j`-image of model points `Θ (t, s)` with `|t| < 5Δ`, `d(s, s₀) < 5Δ`.
Completeness and connectedness of `S` are consequences (`EdgeProductModelApplications.lean`).
The prescribed-tolerance comparisons on a buffer (distance, first coordinate of the SAME
splitting, `C^{K-1}` metric on a finite atlas, orientation) are the conjuncts of the producer
`exists_edgeDiskPacket_comparison_threshold` (`EdgeDiskPacketComparison.lean`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Metric WithLp Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry.Collapse

open GC.MetricGeometry DifferentialGeometry.Geometry.Riemannian

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

local instance nezero_finrank_euclidean_three_productModel_LFR28ROW2 :
    NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

variable {M : Type*} [mM : MetricSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
  [SigmaCompactSpace M] [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
  [IsRiemannianManifold 𝓘(ℝ, E3) M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]

/-- **LC84 item 4: the LC81 comparison of an edge chart with `ℝ × Z`.** See the module
docstring. -/
structure EdgeProductModel {g : SmoothRiemannianMetric 𝓘(ℝ, E3) M} {hEnorm : IsMetricNorm g}
    {Δ σ μ b γ β : ℝ} {A : Set M} {ρ F : M → ℝ}
    (c : EdgeChart g hEnorm Δ σ μ b γ β A ρ F) (K : ℕ) where
  /-- The finite model. -/
  N : Type
  [instMetricN : MetricSpace N]
  [instChartedN : ChartedSpace E3 N]
  [instManifoldN : IsManifold 𝓘(ℝ, E3) ∞ N]
  [instProperN : ProperSpace N]
  [instConnectedN : ConnectedSpace N]
  [instBundleN : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x)]
  [instRiemannianN : IsRiemannianManifold 𝓘(ℝ, E3) N]
  /-- Its finite-order metric, nonnegatively curved. -/
  G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) ((K - 1 : ℕ) : ℕ∞ω) E3
    (TangentSpace 𝓘(ℝ, E3) : N → Type _)
  enorm : ∀ (x : N) (v : TangentSpace 𝓘(ℝ, E3) x),
    ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x v v))
  sectional_nonneg : ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, E3) x), 0 ≤ G.sectionalCurvature x v w
  /-- The surface factor `Z`. -/
  S : Type
  [instMetricS : MetricSpace S]
  [instChartedS : ChartedSpace E2 S]
  [instManifoldS : IsManifold (𝓡 2) ∞ S]
  [instBundleS : RiemannianBundle (fun x : S => TangentSpace (𝓡 2) x)]
  [instRiemannianS : IsRiemannianManifold (𝓡 2) S]
  /-- Its finite-order metric, nonnegatively curved, and an orientation. -/
  κ : ContMDiffRiemannianMetric (𝓡 2) ((K - 1 : ℕ) : ℕ∞ω) E2 (TangentSpace (𝓡 2) : S → Type _)
  enormS : ∀ (x : S) (w : TangentSpace (𝓡 2) x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (κ.inner x w w))
  sectional_nonnegS : ∀ (x : S) (v w : TangentSpace (𝓡 2) x), 0 ≤ κ.sectionalCurvature x v w
  orientationS : ManifoldOrientation (𝓡 2) S 2
  /-- `N = ℝ × S`: a `C^K` diffeomorphism, an isometry from `ℓ²(ℝ × S)`, with `Θ^* G = dt² + κ`. -/
  Θ : Diffeomorph (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) (ℝ × S) N K
  dist_Θ : ∀ a b : ℝ × S, dist (Θ a) (Θ b) = dist (toLp 2 a) (toLp 2 b)
  product_metric : ∀ (p : ℝ × S) (v w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) p),
    G.inner (Θ p) (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p v)
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p w) = v.1 * w.1 + κ.inner p.2 v.2 w.2
  /-- The actual `C^K` embedding, pointed. -/
  j : PartialDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) N M K
  s₀ : S
  base_mem : Θ (0, s₀) ∈ j.source
  j_base : j (Θ (0, s₀)) = c.center
  /-- The ENTIRE source closed slab lies in the image of `[-5Δ, 5Δ] × B(s₀, 5Δ)`. -/
  slab : ∀ y ∈ ball c.center (100 * Δ), |c.coord y| ≤ 4 * Δ → edgeRowHeight Δ F ρ y ≤ 4 * Δ →
    ∃ s : ℝ × S, |s.1| < 5 * Δ ∧ dist s.2 s₀ < 5 * Δ ∧ Θ s ∈ j.source ∧ j (Θ s) = y

end DifferentialGeometry.Geometry.Collapse
