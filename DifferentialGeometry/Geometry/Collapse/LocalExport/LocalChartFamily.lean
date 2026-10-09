import DifferentialGeometry.Geometry.Collapse.LocalExport.CircleFamily
import DifferentialGeometry.Geometry.Collapse.LocalExport.SlimPacket
import DifferentialGeometry.Geometry.Collapse.LocalExport.SlimProductModel
import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeChart

/-!
# LC87 items 2–3: the local chart family (circle, slim and edge kinds) as data

Blueprint row LC87 (`def:collapse-local-export-certificate`, master207A:31053): a local-collapse
export is a fixed manifold and metric, a positive modified scale, ONE parameter assignment and
finite families of local charts with their actual maps; item 2 lists the LC83 circle charts, the
LC84 edge packets and the LC85 slim packets, item 3 the LC86 covers, the overlap bound, the cutoffs
and the stratum exhaustion. LPA06 (A:30586) produces them on LPA04's tail. This module records the
three nonzero kinds as data on a closed three-manifold (model `𝓘(ℝ, ℝ³)`); every chart lives at
normalized scale `(ρ(j)⁻¹ d, ρ(j)⁻² g)`, the convention of `CircleChart`, `SlimChart`, `EdgeChart`.

* `SlimCentre X g hmetric ρ hρ β₁ Δ σs K j`: the actual normalized `(1, β₁)`-splitting at `j` with a
  factor of diameter `≤ 10³Δ`, the LC85 `SlimPacket` over it (fibre `S²` or `T²`) and its LC81
  `SlimProductModel`.
* `SlimFamily`: finitely many slim centres (`Δρ/3`-disjoint, covering the slim one-stratum by
  `B(j, 2Δρ(j))`, support multiplicity bounded by a numerical constant) with a `SlimCentre` each.
* `EdgeFamily`: finitely many strong edge centres (`Δρ/3`-disjoint, covering the strong edge points
  and the nonslim one-stratum, multiplicity bounded), ONE shared smoothing `F` of the distance to the
  closed weak edge set, and an LC84 `EdgeChart` (items 1–3) at every centre. The disk bundle of LC84
  item 4 (`EdgeDiskPacket`, lane LFR28-ROW2) is not part of it.
* `LocalChartFamily`: one smooth `Λ`-Lipschitz scale `ρ`, a `CircleFamily`, a `SlimFamily`, an
  `EdgeFamily` and the stratum exhaustion: every point lies in the zero stratum or in a covering ball.

The producer on the reordered LPA04 tail is `eventually_nonempty_localChartFamily`
(`LocalChartFamilyProducer.lean`). The LC80 zero family (item 1), the chart-overlap comparisons
(item 4) and the boundary collars (item 5) are not part of this structure.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- `finrank ℝ ℝ³ ≠ 0`, for the `NeZero` argument of the slim and edge charts. -/
local instance nezero_finrank_euclideanThree_LC87 : NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

section Data

variable (X : Type u) [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X]

/-- **One LC85 slim centre** (LC87 item 2, slim kind) at `j`: the actual normalized
`(1, β₁)`-splitting with a factor of diameter `≤ 10³Δ`, the LC85 slim packet over it in the
normalization `(ρ(j)⁻¹ d, ρ(j)⁻² g)` and its LC81 product model. -/
structure SlimCentre (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (β₁ Δ σs : ℝ) (K : ℕ) (j : X) where
  /-- The compact factor of the splitting. -/
  Z : Type
  [instZ : MetricSpace Z]
  z : Z
  factor_dist : ∀ y y' : Z, dist y y' ≤ 10 ^ 3 * Δ
  /-- The actual normalized `(1, β₁)`-splitting at `j`. -/
  split : @KleinerLottApprox X (WithLp 2 (ℝ × Z)) (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ j
    (WithLp.toLp 2 ((0 : ℝ), z)) β₁
  /-- The LC85 slim packet at normalized scale. -/
  packet :
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
    SlimPacket gR hnR Δ σs split
  /-- The LC81 comparison with `ℝ × Z` (LFR20 item 3). -/
  model :
    let hMc : CompleteSpace X := complete_of_compact
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : CompleteSpace X :=
      (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
    SlimProductModel packet.toSlimChart K

/-- **The LC85 slim family** (LC87 items 2–3, slim kind). -/
structure SlimFamily (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ) where
  centres : Set X
  finite_centres : centres.Finite
  centres_subset : centres ⊆ {p | p ∈ scaledSplittingStratum.{u, 0} ρ hρ β 1 ∧
    (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
      Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
      Nonempty (@KleinerLottApprox X (WithLp 2 (ℝ × Z))
        (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ p (WithLp.toLp 2 ((0 : ℝ), z)) (β 1)))}
  disjoint_centres : centres.PairwiseDisjoint (fun j => ball j (Δ * ρ j / 3))
  covers : ∀ p ∈ scaledSplittingStratum.{u, 0} ρ hρ β 1,
    (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
      Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
      Nonempty (@KleinerLottApprox X (WithLp 2 (ℝ × Z))
        (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ p (WithLp.toLp 2 ((0 : ℝ), z)) (β 1))) →
    ∃ j ∈ centres, ball p (Δ * ρ p) ⊆ ball j (2 * (Δ * ρ j))
  /-- The slim packet at every centre. -/
  centre : (j : X) → j ∈ centres → SlimCentre X g hmetric ρ hρ (β 1) Δ σs K j
  multiplicity : ∀ x : X, ((centres ∩ {j | x ∈ ball j (2000000 * (Δ * ρ j))}).ncard : ℝ) ≤
    modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (3 * 2000000 + 2 / 3) /
      modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3)

/-- **The LC84 strong-edge family at the `EdgeChart` level** (LC87 items 2–3, edge kind, without
the disk bundle of LC84 item 4). -/
structure EdgeFamily (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (β : ℕ → ℝ) (Δ σc μ b s b' s' ε γc βc : ℝ) where
  centres : Set X
  finite_centres : centres.Finite
  strong : ∀ j ∈ centres,
    @isEdgePoint.{u, 0} X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) j Δ b s
  disjoint_centres : centres.PairwiseDisjoint (fun j => ball j (Δ * ρ j / 3))
  covers_strong : ∀ a : X,
    @isEdgePoint.{u, 0} X (mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρ a))) a Δ b s →
    ∃ j ∈ centres, dist a j < Δ * ρ j
  covers_nonslim : ∀ p ∈ scaledSplittingStratum.{u, 0} ρ hρ β 1,
    ¬ (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
      Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
      Nonempty (@KleinerLottApprox X (WithLp 2 (ℝ × Z))
        (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ p (WithLp.toLp 2 ((0 : ℝ), z)) (β 1))) →
    ∃ j ∈ centres, dist p j < 2 * Δ * ρ j
  multiplicity : ∀ x : X, ((centres ∩ {j | x ∈ ball j (2000000 * (Δ * ρ j))}).ncard : ℝ) ≤
    modelVolume (-((1 / (4 * (1 + 2 * 2000000 + 1 / 3)) : ℝ) ^ 2)) 3
        (4 * (1 + 2 * 2000000 + 1 / 3)) /
      modelVolume (-((1 / (4 * (1 + 2 * 2000000 + 1 / 3)) : ℝ) ^ 2)) 3 (1 / 3)
  /-- The ONE shared smoothing of the distance to the closed weak edge set. -/
  smoothing : X → ℝ
  smoothing_nonneg : ∀ x, 0 ≤ smoothing x
  lipschitz_smoothing : LipschitzWith (Real.toNNReal (1 + ε)) smoothing
  smoothing_value : ∀ p ∈ centres, ∀ x, |smoothing x - infDist x (closure
    {y | @isEdgePoint.{u, 0} X (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y))) y Δ b' s'})| <
      μ * (Δ * ρ p)
  /-- The LC84 edge chart at every centre, at normalized scale. -/
  chart : (j : X) → j ∈ centres →
    let A : Set X := closure
      {y | @isEdgePoint.{u, 0} X (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y))) y Δ b' s'}
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
    EdgeChart gR hnR Δ σc μ b γc βc A (fun x => ρ x / ρ j) (fun x => smoothing x / ρ j)
  chart_center : ∀ j (hj : j ∈ centres),
    let hMc : CompleteSpace X := complete_of_compact
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : CompleteSpace X :=
      (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
    (chart j hj).center = j

/-- **The LC87 local chart family** (items 2–3 for the circle, slim and edge kinds, with the
stratum exhaustion of item 3): ONE scale `ρ` (smooth, `Λ`-Lipschitz), one parameter assignment,
the three nonzero families and the exhaustion of `X` by the zero stratum and the covering balls. -/
structure LocalChartFamily (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
    (σc μ b s b' s' ε γc βc : ℝ) where
  contMDiff_scale : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ ρ
  lipschitz_scale : LipschitzWith (Real.toNNReal Λ) ρ
  circle : CircleFamily 𝓘(ℝ, E3) X ρ hρ β
  slim : SlimFamily X g hmetric ρ hρ β Δ σs K
  edge : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc
  exhaustion : ∀ x : X, x ∈ scaledSplittingStratum.{u, 0} ρ hρ β 0 ∨
    (∃ j ∈ circle.centres, x ∈ ball j (2 * ρ j)) ∨
    (∃ j ∈ slim.centres, x ∈ ball j (2 * (Δ * ρ j))) ∨
    ∃ j ∈ edge.centres, dist x j < 2 * Δ * ρ j

end Data

end DifferentialGeometry.Geometry.Collapse
