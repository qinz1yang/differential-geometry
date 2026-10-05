import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamilyEdge
import DifferentialGeometry.Geometry.Collapse.LocalExport.ZeroModelBall

/-!
# LC87: the final combined local chart family (review-42 packets (i)–(iv) and the zero kind)

* `CircleAdaptedCentre X g hmetric ρ hρ β γ C j hj` (packet (i)): for the SAME chosen chart
  `C.chart j hj` of a circle family, the original normalized `(2, β₂)`-splitting, the adaptation error
  `< γ`, the `(1 + γ)`-Lipschitz bound on `B(j, 200)` and the original long derivative tests against
  the same splitting (`x ∈ B(j, 200)`, `z ∈ B(j, 201·10⁴)`, `201 < d(x, z)`, unit initial velocity
  of a geodesic of the normalized metric reaching `z`), at normalized scale `(ρ(j)⁻¹ d, ρ(j)⁻² g)`.
* `LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V`
  (`X : Type`): `LocalChartFamilyE` (cutoff formulas, curvature buffer, edge coarse-border
  composite) with a circle adapted-coordinate packet at every circle centre, and, on the SAME data,
  the models `N, C, o` and the LC80 zero-model family `zero : ZeroModelFamily` (the projections
  `toLocalChartFamily` and `zero` are the inputs of chapter 14's global map).

Producer: `eventually_nonempty_localChartPackets` (`LocalChartPacketsProducer.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Data

variable (X : Type u) [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X]

/-- **(i) The circle adapted-coordinate packet of the SAME chosen chart** at a circle centre `j`:
the original normalized `(2, β₂)`-splitting, the adaptation error `γ` and the `(1 + γ)`-Lipschitz
bound on `B(j, 200)`, and the original long derivative tests (`x ∈ B(j, 200)`,
`z ∈ B(j, 201·10⁴)`, `201 < d(x, z)`, unit initial velocity of a geodesic reaching `z`), all at
normalized scale `(ρ(j)⁻¹ d, ρ(j)⁻² g)` and for `η_j = (C.chart j hj).coord`. -/
structure CircleAdaptedCentre (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (β : ℕ → ℝ) (γ : ℝ)
    (C : CircleFamily 𝓘(ℝ, E3) X ρ hρ β) (j : X) (hj : j ∈ C.centres) where
  Y : Type
  [instY : MetricSpace Y]
  a : Y
  split : @KleinerLottApprox X (WithLp 2 (ℝ² × Y)) (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ j
    (WithLp.toLp 2 ((0 : ℝ²), a)) (β 2)
  adapted :
    let c := C.chart j hj
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    ∀ x ∈ ball j 200, ‖c.coord x - (split.toFun x).fst‖ < γ
  lipschitz :
    let c := C.chart j hj
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    LipschitzOnWith (Real.toNNReal (1 + γ)) c.coord (ball j 200)
  test :
    let c := C.chart j hj
    let hMc : CompleteSpace X := complete_of_compact
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : CompleteSpace X :=
      (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
    let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
      scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) g
    have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
    ∀ x ∈ ball j 200, ∀ z ∈ ball j (201 * 10000), 201 < dist x z →
      ∀ w : TangentSpace 𝓘(ℝ, E3) x, gR.inner x w w = 1 →
      intrinsicGeodesic gR hnR x w (dist x z) = z →
      ‖mvfderiv (I := 𝓘(ℝ, E3)) c.coord x w -
        (dist x z)⁻¹ • ((split.toFun z).fst - (split.toFun x).fst)‖ < γ

end Data

/-- **The final combined LC87 family** (frozen target, review 42 + CGP01): the edge-packet family
`LocalChartFamilyE` (cutoff formulas, curvature buffer, edge coarse-border composite) together with
(i) a circle adapted-coordinate packet for EVERY selected circle chart and the LC80 zero-model family
on the SAME data (projections `toLocalChartFamily` and `zero : ZeroModelFamily`, as in
`LocalChartFamilyWithZero`). `X : Type` (the zero family is universe 0). -/
structure LocalChartPackets (X : Type) [mX : MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
    (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ)
    extends LocalChartFamilyE X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ where
  circleAdapted : ∀ j (hj : j ∈ circle.centres),
    CircleAdaptedCentre X g hmetric ρ hρ β γ circle j hj
  N : X → Type
  C : X → Type
  [instMetricN : ∀ a, MetricSpace (N a)]
  [instChartedN : ∀ a, ChartedSpace E3 (N a)]
  [instMetricC : ∀ a, MetricSpace (C a)]
  o : ∀ a, C a
  zero : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V

end DifferentialGeometry.Geometry.Collapse
