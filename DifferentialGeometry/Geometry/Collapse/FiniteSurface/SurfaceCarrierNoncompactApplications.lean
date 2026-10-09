import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SurfaceCarrierNoncompact
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.EdgeCoreBinding

/-!
# Consumers of the noncompact surface carrier (LFR28 blocker B2)

* `surfaceFactor_smoothCarrier_of_finite_limit_noncompact`: a finite Cheeger–Gromov limit in the
  L-CONS shape (metric of natural order `K - 1`, `K ≥ 4`, carried by `⟨G.toRiemannianMetric⟩`,
  proper, connected) with `sec ≥ 0` and an exact line splitting with ANY residual factor `W`: the
  surface factor has a complete connected smooth carrier isometric to `W`, carrying a
  nonnegatively curved metric for which it is a Riemannian manifold.
* `surfaceFactor_edge_model_disks_of_finite_limit_noncompact`: the same limit, oriented, with
  `K ≥ 5`: LFR24 (`finiteSurface_edge_model_core`) runs on the oriented carrier, i.e. every LFR23
  endpoint model on the carrier of small error yields the smooth edge-core disks `D_s`,
  `s ∈ [3, 6]` — the use LFR28 makes of B2.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter WithLp Manifold Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.ExactSplitting DifferentialGeometry.Topology

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

universe u

/-- **B2 in the L-CONS shape.** The noncompact surface factor of a finite limit has a complete
connected smooth carrier, isometric to the residual factor `W`, with a nonnegatively curved
`C^{K-1}` metric for which it is a Riemannian manifold. -/
theorem surfaceFactor_smoothCarrier_of_finite_limit_noncompact {N W : Type u} [MetricSpace N]
    [ChartedSpace E3 N] [IsManifold 𝓘(ℝ, E3) ∞ N] [ProperSpace N] [ConnectedSpace N]
    [MetricSpace W] (K : ℕ) (hK : 4 ≤ K)
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) ((K - 1 : ℕ) : ℕ∞ω) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (hRiem : letI : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x) :=
        ⟨G.toRiemannianMetric⟩
      IsRiemannianManifold 𝓘(ℝ, E3) N)
    (hsec : ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, E3) x), 0 ≤ G.sectionalCurvature x v w)
    (e : N ≃ᵢ WithLp 2 (ℝ × W)) :
    ∃ (S : Type u) (_ : MetricSpace S) (_ : ChartedSpace E2 S) (_ : IsManifold (𝓡 2) ∞ S),
      CompleteSpace S ∧ ConnectedSpace S ∧ Nonempty (S ≃ᵢ W) ∧
      ∃ κ : ContMDiffRiemannianMetric (𝓡 2) ((K - 2 + 1 : ℕ) : ℕ∞ω) E2
          (TangentSpace (𝓡 2) : S → Type _),
        (∀ (x : S) (v w : TangentSpace (𝓡 2) x), 0 ≤ κ.sectionalCurvature x v w) ∧
        (letI : RiemannianBundle (fun x : S => TangentSpace (𝓡 2) x) := ⟨κ.toRiemannianMetric⟩
         IsRiemannianManifold (𝓡 2) S) := by
  let _ : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x) := ⟨G.toRiemannianMetric⟩
  let _ : IsRiemannianManifold 𝓘(ℝ, E3) N := hRiem
  have hsec' : ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, E3) x),
      0 ≤ (finiteMetricReindex K hK G).sectionalCurvature x v w := fun x v w => hsec x v w
  obtain ⟨S, mS, cS, iS, hc, hconn, φ, -, -, -, ⟨ψ, -⟩, κ, -, hsecS, hR, -⟩ :=
    surfaceFactor_smoothCarrier_noncompact (finiteMetricReindex K hK G) (two_le_reindex K hK)
      (finiteMetricReindex_enorm K hK G) hsec' e
  exact ⟨S, mS, cS, iS, hc, hconn, ⟨ψ⟩, κ, hsecS, hR⟩

/-- **LFR24 on the oriented noncompact carrier (the LFR28 use of B2).** For an oriented finite
limit (`K ≥ 5`) with `sec ≥ 0` and an exact line splitting with any residual factor `W`, the
oriented carrier `S ≃ᵢ W` of the surface factor carries LFR24: there is `δ₀ > 0` such that every
endpoint model `q` around `z₀` of error `δ ≤ δ₀` and every `0 < μ < 1/100` give a function `h`
whose sublevels `D_s` (`s ∈ [3, 6]`, inside `r < 9`) are smooth closed disks with boundary the
level, between `B̄(z₀, s - μ)` and `B(z₀, s + μ)`. -/
theorem surfaceFactor_edge_model_disks_of_finite_limit_noncompact {N W : Type u} [MetricSpace N]
    [ChartedSpace E3 N] [IsManifold 𝓘(ℝ, E3) ∞ N] [ProperSpace N] [ConnectedSpace N]
    [MetricSpace W] (K : ℕ) (hK : 5 ≤ K)
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) ((K - 1 : ℕ) : ℕ∞ω) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (hRiem : letI : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x) :=
        ⟨G.toRiemannianMetric⟩
      IsRiemannianManifold 𝓘(ℝ, E3) N)
    (hsec : ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, E3) x), 0 ≤ G.sectionalCurvature x v w)
    (oN : ManifoldOrientation (𝓡 3) N 3) (e : N ≃ᵢ WithLp 2 (ℝ × W)) :
    ∃ (S : Type u) (_ : MetricSpace S) (_ : ChartedSpace E2 S) (_ : IsManifold (𝓡 2) ∞ S),
      CompleteSpace S ∧ ConnectedSpace S ∧ Nonempty (S ≃ᵢ W) ∧
      ∃ δ₀ > 0, ∀ (z₀ : S) (q : S → ℝ) (δ : ℝ), 0 < δ → δ ≤ δ₀ → q z₀ = 0 →
        (∀ y ∈ closedBall z₀ 10, 0 ≤ q y) →
        (∀ y ∈ closedBall z₀ 10, ∀ y' ∈ closedBall z₀ 10, |dist (q y) (q y') - dist y y'| ≤ δ) →
        (∀ t ∈ Icc (0 : ℝ) 10, ∃ y ∈ closedBall z₀ 10, |q y - t| ≤ δ) →
        ∀ μ : ℝ, 0 < μ → μ < 1 / 100 →
        ∃ h : S → ℝ, ∀ s ∈ Icc (3 : ℝ) 6,
          IsCompact {x | dist x z₀ < 9 ∧ h x ≤ s} ∧
          closedBall z₀ (s - μ) ⊆ {x | dist x z₀ < 9 ∧ h x ≤ s} ∧
          {x | dist x z₀ < 9 ∧ h x ≤ s} ⊆ ball z₀ (s + μ) ∧
          ∃ b : ClosedCell 2 → S, Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ b ∧
            range b = {x | dist x z₀ < 9 ∧ h x ≤ s} ∧
            range (b ∘ cellBoundaryInclusion 2) = {x | dist x z₀ < 9 ∧ h x = s} := by
  let _ : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x) := ⟨G.toRiemannianMetric⟩
  let _ : IsRiemannianManifold 𝓘(ℝ, E3) N := hRiem
  have hK4 : 4 ≤ K := by omega
  have hsec' : ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, E3) x),
      0 ≤ (finiteMetricReindex K hK4 G).sectionalCurvature x v w := fun x v w => hsec x v w
  obtain ⟨S, mS, cS, iS, hc, hconn, ⟨o⟩, φ, -, -, -, ⟨ψ, -⟩, κ, -, hsecS, hR, hnormS⟩ :=
    surfaceFactor_smoothCarrier_oriented_noncompact (finiteMetricReindex K hK4 G)
      (two_le_reindex K hK4) (finiteMetricReindex_enorm K hK4 G) hsec' oN e
  let _ : RiemannianBundle (fun x : S => TangentSpace (𝓡 2) x) := ⟨κ.toRiemannianMetric⟩
  have _ : IsRiemannianManifold (𝓡 2) S := hR
  let κ' : ContMDiffRiemannianMetric (𝓡 2) ((((K - 2 : ℕ) : ℕ∞) : ℕ∞ω) + 1) E2
      (TangentSpace (𝓡 2) : S → Type _) :=
    { κ with contMDiff := by rw [withTop_natCast_add_one]; exact κ.contMDiff }
  have hr : (3 : ℕ∞) ≤ ((K - 2 : ℕ) : ℕ∞) := by exact_mod_cast (show 3 ≤ K - 2 by omega)
  obtain ⟨δ₀, hδ₀, hcore⟩ := finiteSurface_edge_model_core o κ' hr (fun x w => hnormS x w)
    (fun x v w => hsecS x v w) (ε := 1 / 200) (by norm_num) (by norm_num)
  refine ⟨S, mS, cS, iS, hc, hconn, ⟨ψ⟩, δ₀, hδ₀,
    fun z₀ q δ hδ hδδ hq0 hqnn hdist hdense μ hμ hμ1 => ?_⟩
  obtain ⟨h, -, -, -, -, hdisk, -⟩ := hcore z₀ q δ hδ hδδ hq0 hqnn hdist hdense μ hμ hμ1
  exact ⟨h, hdisk⟩

end DifferentialGeometry.Geometry.Collapse
