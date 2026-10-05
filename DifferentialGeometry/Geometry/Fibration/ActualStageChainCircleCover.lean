import DifferentialGeometry.Geometry.Fibration.ActualStageChainEGaf07Circle
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRemainder
import DifferentialGeometry.Geometry.Fibration.ActualEdgeCollarCircle

/-!
# FDC03's coverage with the circle base: every point is zero, slim, in `X₁`, or in `int X₂°`

Blueprint `master207B.tex`, FDC03 (B:7322–7335): "Consequently every point of `M₃` is two-stratum.
LPA06's ORIGINAL circle cover has `|η_a| < 2` at such a point, and GAF07 puts it in `X₁`." On the
chain with GAF01's (JA) (`Gaf02ChainEJA`, lane C14-GAF-C), with BASES' `W₁ = C.finalBase_BAS 0` and
GAF07's ratio set `R₁ = gaf07CircleRatio_G47` (`X₁ = (π₁E)⁻¹(W₁ ∩ R₁)`).

* `LocalChartPackets.circle_coord_lt_of_ball_FDC`: on a circle covering ball `B(a, 2ρ_a)` the
  circle coordinate has `‖η_a‖ < 2(1 + γ)` (the circle adapted packet is `(1 + γ)`-Lipschitz; the
  argument of `LocalChartPackets.circle_chart_of_two_EDP6`, here from ball membership).
* `Gaf02ChainEJA.circle_ball_mem_X₁_FDC` (`0 ≤ γ ≤ 3/4`): a point of `B(a, 2ρ_a)` has
  `π₁E(x) ∈ W₁ ∩ R₁` (`final_mem_circleBase_GAFC` + `gaf07_circle_first_inclusion_G47`).
* `Gaf02ChainEJA.fdc03_cover_FDC` (`σc ≤ 1/2`, `0 ≤ γ ≤ 3/4`): every point is zero-stratum, in a
  slim ball `B(j, 2Δρ_j)`, in `X₁`, or in the interior of the edge candidate `X₂°`.

NOT here: `int Z` (ZSP02) and `int_{M₁}M^slim` (GAF07 + (SK)) — the exclusion of the zero and
slim alternatives for points of `M₂`; the circle-bundle structure of `M₃` (GAF07, EDP06).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- **The circle coordinate on a covering ball**: `x ∈ B(a, 2ρ_a)` gives `‖η_a(x)‖ < 2(1 + γ)`. -/
theorem LocalChartPackets.circle_coord_lt_of_ball_FDC
    (L : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hγ : 0 ≤ γ) (a : L.toLocalChartFamily.circle.finite_centres.toFinset) {x : X}
    (hx : x ∈ ball a.1 (2 * ρ a.1)) :
    ‖cgpCoord L.toLocalChartFamily L.zero (.inl a) x‖ < 2 * (1 + γ) := by
  have ha := (Set.Finite.mem_toFinset _).mp a.2
  have hxa : dist x a.1 < 2 * ρ a.1 := mem_ball.mp hx
  have hxa' : (ρ a.1)⁻¹ * dist x a.1 < 2 := by
    rw [inv_mul_lt_iff₀ (hρ a.1)]
    linarith
  have hcc0 := L.circle.chart_center a.1 ha
  have hlip := (L.circleAdapted a.1 ha).lipschitz
  let c := L.circle.chart a.1 ha
  let _ := mX.rescale (ρ a.1)⁻¹ (inv_pos.mpr (hρ a.1))
  have hcc : c.center = a.1 := hcc0
  have h0 : c.coord a.1 = 0 := by
    have h := c.coord_center
    rwa [hcc] at h
  have hxa'' : dist x a.1 < 2 := hxa'
  have hxB : x ∈ ball a.1 200 := by
    rw [mem_ball]
    linarith
  have haB : a.1 ∈ ball a.1 200 := mem_ball_self (by norm_num)
  have hl : LipschitzOnWith (Real.toNNReal (1 + γ)) c.coord (ball a.1 200) := hlip
  have hd := hl.dist_le_mul x hxB a.1 haB
  rw [h0, dist_zero_right, Real.coe_toNNReal _ (by linarith)] at hd
  have hpos : 0 < 1 + γ := by linarith
  change ‖c.coord x‖ < 2 * (1 + γ)
  calc ‖c.coord x‖ ≤ (1 + γ) * dist x a.1 := hd
    _ < (1 + γ) * 2 := mul_lt_mul_of_pos_left hxa'' hpos
    _ = 2 * (1 + γ) := by ring

namespace Gaf02ChainEJA

variable {vs ζ Λz : ℝ}
  {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}

/-- **A circle covering ball lies in `X₁`** (FDC03, B:7334–7335): `x ∈ B(a, 2ρ_a)` gives
`π₁E(x) ∈ W₁ ∩ R₁` (`0 ≤ γ ≤ 3/4`, so `‖η_a(x)‖ < 3.5`). -/
theorem circle_ball_mem_X₁_FDC (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) (hγ : 0 ≤ γ)
    (hγ1 : γ ≤ 3 / 4) (a : P.toLocalChartFamily.circle.finite_centres.toFinset) {x : X}
    (hx : x ∈ ball a.1 (2 * ρ a.1)) :
    (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E x) ∈
      C.toChain.finalBase_BAS 0 ∩ gaf07CircleRatio_G47 P.toLocalChartPackets := by
  have hη := P.toLocalChartPackets.circle_coord_lt_of_ball_FDC hγ a hx
  have hra := hρ a.1
  have hx200 : x ∈ ball a.1 (200 * ρ a.1) := by
    rw [mem_ball] at hx ⊢
    linarith
  have hY : x ∈ gaf07CircleY_GAFC P.toLocalChartPackets a := ⟨hx200, by linarith⟩
  exact ⟨(C.toGaf02ChainE.final_mem_circleBase_GAFC a hY).1,
    C.toChain.gaf07_circle_first_inclusion_G47 C.c_two_lt a hx200 (by linarith)⟩

/-- **FDC03's coverage** (B:7322–7335): every point is zero-stratum, in a slim ball
`B(j, 2Δρ_j)`, in `X₁ = (π₁E)⁻¹(W₁ ∩ R₁)`, or in the interior of the edge candidate `X₂°`. -/
theorem fdc03_cover_FDC (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) (hσc : σc ≤ 1 / 2)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 3 / 4) (x : X) :
    x ∈ scaledSplittingStratum.{0, 0} ρ hρ β 0 ∨
      (∃ j ∈ P.slim.centres, x ∈ ball j (2 * (Δ * ρ j))) ∨
      (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E x) ∈
        C.toChain.finalBase_BAS 0 ∩ gaf07CircleRatio_G47 P.toLocalChartPackets ∨
      x ∈ interior ({x | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily
        P.zero (C.toChain.E x)) / C.toChain.scale x < 4 * Δ} ∩
      {x | ∃ k : P.toLocalChartFamily.edge.finite_centres.toFinset,
        blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) (C.toChain.E x) = ρ k.1 ∧
        ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) (C.toChain.E x)‖ < 4 * Δ * ρ k.1}) := by
  rcases C.toGaf02ChainE.fdc03_coverage_FDC hσc x with h | ⟨j, hj, hx⟩ | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl
      (C.circle_ball_mem_X₁_FDC hγ hγ1 ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩ hx)))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr h))

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
