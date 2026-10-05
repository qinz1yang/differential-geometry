import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsFinal

/-!
# LC88 / BCP04, packet P0: the shared regionalised LC87 packets `LocalPacketsOn` (lane BDRY-2, G10)

Review 45 §3.3 (binding): ONE shared regionalised kernel. The per-centre payloads are those of the
closed LC87 structures (`LocalChartPackets`), now on a COMPLETE σ-compact carrier (no
`CompactSpace`; the normalized-scale instance blocks take the carrier's own `CompleteSpace`); the
admissible centres lie in a region `U₁`, and the cover obligations are stated on regions:
* circle, slim, strong-edge centres and zero centres lie in `U₁`; the circle, slim and strong-edge
  covers are the ELIGIBLE covers of `U₁` (the maximal-selection conclusions are kept);
* the nonslim edge cover and the stratum exhaustion are asserted on `U₂`;
* the curvature buffer is asserted at `p ∈ U₁`;
* the zero family covers `U₁ ∩ Z₀` by tenth-radius balls; each selected ball MEETS `Z₀` (its centre
  need not be a zero point).
For LC88 (`T2`, `T3` of BDRY-1's frozen targets v2): `U₁ = {D > 10}`, `U₂ = {D ≥ 20}` on the
completed interior `(W°, d_ĝ)`; the rank region `U₀ = {D > 5}` appears only in the transport
clauses of `T2`.

* the structures `CircleFamilyOn`, `SlimCentreOn`, `SlimFamilyOn`, `EdgeFamilyOn`, `ChartFamilyOn`,
  `ChartFamilyQOn`, `ChartFamilyEOn`, `CircleAdaptedCentreOn`, `ZeroModelFamilyOn`,
  `LocalPacketsOn` (verbatim the P0 draft of BDRY-1's `Targets.lean` v2);
* the closed specialization `LocalPacketsOn.ofClosed` (`LocalChartPackets X … → LocalPacketsOn X …
  univ univ`, `CompactSpace ⇒ CompleteSpace, SigmaCompactSpace`) and its per-family pieces;
* consumer / producer: `eventually_nonempty_localPacketsOn_closed_BDRY2`, the closed producer
  `eventually_nonempty_localChartPackets` composed with the specialization — on one tail of every
  closed standing sequence the regionalised packets with `U₁ = U₂ = univ` exist.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

universe uE uH u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-! ## The regionalised structures -/

section RegionCircle

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  (X : Type u) [mX : MetricSpace X] [ChartedSpace H X] [IsManifold I ∞ X]

/-- `CircleFamily` with centres in `U₁` and the eligible cover of `U₁`. -/
structure CircleFamilyOn (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (β : ℕ → ℝ) (U₁ U₂ : Set X) where
  centres : Set X
  finite_centres : centres.Finite
  centres_subset : centres ⊆ U₁ ∩ scaledSplittingStratum.{u, 0} ρ hρ β 2
  disjoint_centres : centres.PairwiseDisjoint (fun p => ball p (ρ p / 3))
  covers : ∀ p ∈ U₁ ∩ scaledSplittingStratum.{u, 0} ρ hρ β 2, ∃ j ∈ centres,
    ball p (ρ p) ⊆ ball j (2 * ρ j)
  chart : (j : X) → j ∈ centres →
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    CircleChart I X
  chart_center : ∀ j (hj : j ∈ centres),
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    (chart j hj).center = j
  cutoff : X → X → ℝ
  contMDiff_cutoff : ∀ j ∈ centres, ContMDiff I 𝓘(ℝ, ℝ) ∞ (cutoff j)
  cutoff_mem_Icc : ∀ j ∈ centres, ∀ x, cutoff j x ∈ Icc (0 : ℝ) 1
  cutoff_eq_one : ∀ j (hj : j ∈ centres),
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    ∀ x ∈ ball j 200, ‖(chart j hj).coord x‖ ≤ 8 → cutoff j x = 1
  coord_lt_of_cutoff_ne_zero : ∀ j (hj : j ∈ centres),
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    ∀ x, cutoff j x ≠ 0 → x ∈ ball j 200 ∧ ‖(chart j hj).coord x‖ < 9
  tsupport_subset_domain : ∀ j (hj : j ∈ centres),
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    tsupport (cutoff j) ⊆ (diskPreimageOpens (ball (chart j hj).center 200) isOpen_ball
      (chart j hj).coord (chart j hj).contMDiffOn_coord.continuousOn 100 : Set X)
  plateau : ∀ j ∈ centres, ∀ x ∈ ball j (2 * ρ j), cutoff j x = 1
  tsupport_subset_ball : ∀ j ∈ centres, tsupport (cutoff j) ⊆ ball j (200 * ρ j)
  multiplicity : ∀ x : X, ((centres ∩ {j | x ∈ tsupport (cutoff j)}).ncard : ℝ) ≤
    modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (3 * 2000000 + 2 / 3) /
      modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3)

end RegionCircle

section RegionData

variable (X : Type u) [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X]

/-- `SlimCentre` on a complete (not necessarily compact) carrier. -/
structure SlimCentreOn (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (β₁ Δ σs : ℝ) (K : ℕ) (j : X) where
  Z : Type
  [instZ : MetricSpace Z]
  z : Z
  factor_dist : ∀ y y' : Z, dist y y' ≤ 10 ^ 3 * Δ
  split : @KleinerLottApprox X (WithLp 2 (ℝ × Z)) (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ j
    (WithLp.toLp 2 ((0 : ℝ), z)) β₁
  packet :
    let hMc : CompleteSpace X := ‹CompleteSpace X›
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
  model :
    let hMc : CompleteSpace X := ‹CompleteSpace X›
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : CompleteSpace X :=
      (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
    SlimProductModel packet.toSlimChart K

/-- `SlimFamily` with centres in `U₁` and the eligible cover of `U₁`. -/
structure SlimFamilyOn (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ) (U₁ U₂ : Set X) where
  centres : Set X
  finite_centres : centres.Finite
  centres_subset : centres ⊆ {p | p ∈ U₁ ∧ p ∈ scaledSplittingStratum.{u, 0} ρ hρ β 1 ∧
    (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
      Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
      Nonempty (@KleinerLottApprox X (WithLp 2 (ℝ × Z))
        (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ p (WithLp.toLp 2 ((0 : ℝ), z)) (β 1)))}
  disjoint_centres : centres.PairwiseDisjoint (fun j => ball j (Δ * ρ j / 3))
  covers : ∀ p ∈ U₁ ∩ scaledSplittingStratum.{u, 0} ρ hρ β 1,
    (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
      Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
      Nonempty (@KleinerLottApprox X (WithLp 2 (ℝ × Z))
        (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ p (WithLp.toLp 2 ((0 : ℝ), z)) (β 1))) →
    ∃ j ∈ centres, ball p (Δ * ρ p) ⊆ ball j (2 * (Δ * ρ j))
  centre : (j : X) → j ∈ centres → SlimCentreOn X g hmetric ρ hρ (β 1) Δ σs K j
  multiplicity : ∀ x : X, ((centres ∩ {j | x ∈ ball j (2000000 * (Δ * ρ j))}).ncard : ℝ) ≤
    modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (3 * 2000000 + 2 / 3) /
      modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3)

/-- `EdgeFamily` with centres in `U₁`, the strong cover of `U₁`, the nonslim cover of `U₂`. -/
structure EdgeFamilyOn (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (β : ℕ → ℝ) (Δ σc μ b s b' s' ε γc βc : ℝ)
    (U₁ U₂ : Set X) where
  centres : Set X
  finite_centres : centres.Finite
  centres_subset : centres ⊆ U₁
  strong : ∀ j ∈ centres,
    @isEdgePoint.{u, 0} X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) j Δ b s
  disjoint_centres : centres.PairwiseDisjoint (fun j => ball j (Δ * ρ j / 3))
  covers_strong : ∀ a ∈ U₁,
    @isEdgePoint.{u, 0} X (mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρ a))) a Δ b s →
    ∃ j ∈ centres, dist a j < Δ * ρ j
  covers_nonslim : ∀ p ∈ U₂ ∩ scaledSplittingStratum.{u, 0} ρ hρ β 1,
    ¬ (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
      Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
      Nonempty (@KleinerLottApprox X (WithLp 2 (ℝ × Z))
        (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ p (WithLp.toLp 2 ((0 : ℝ), z)) (β 1))) →
    ∃ j ∈ centres, dist p j < 2 * Δ * ρ j
  multiplicity : ∀ x : X, ((centres ∩ {j | x ∈ ball j (2000000 * (Δ * ρ j))}).ncard : ℝ) ≤
    modelVolume (-((1 / (4 * (1 + 2 * 2000000 + 1 / 3)) : ℝ) ^ 2)) 3
        (4 * (1 + 2 * 2000000 + 1 / 3)) /
      modelVolume (-((1 / (4 * (1 + 2 * 2000000 + 1 / 3)) : ℝ) ^ 2)) 3 (1 / 3)
  smoothing : X → ℝ
  smoothing_nonneg : ∀ x, 0 ≤ smoothing x
  lipschitz_smoothing : LipschitzWith (Real.toNNReal (1 + ε)) smoothing
  smoothing_value : ∀ p ∈ centres, ∀ x, |smoothing x - infDist x (closure
    {y | @isEdgePoint.{u, 0} X (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y))) y Δ b' s'})| <
      μ * (Δ * ρ p)
  chart : (j : X) → j ∈ centres →
    let A : Set X := closure
      {y | @isEdgePoint.{u, 0} X (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y))) y Δ b' s'}
    let hMc : CompleteSpace X := ‹CompleteSpace X›
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
    let hMc : CompleteSpace X := ‹CompleteSpace X›
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : CompleteSpace X :=
      (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
    (chart j hj).center = j

/-- `LocalChartFamily` with the exhaustion asserted on `U₂`. -/
structure ChartFamilyOn (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
    (σc μ b s b' s' ε γc βc : ℝ) (U₁ U₂ : Set X) where
  contMDiff_scale : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ ρ
  lipschitz_scale : LipschitzWith (Real.toNNReal Λ) ρ
  circle : CircleFamilyOn 𝓘(ℝ, E3) X ρ hρ β U₁ U₂
  slim : SlimFamilyOn X g hmetric ρ hρ β Δ σs K U₁ U₂
  edge : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂
  exhaustion : ∀ x ∈ U₂, x ∈ scaledSplittingStratum.{u, 0} ρ hρ β 0 ∨
    (∃ j ∈ circle.centres, x ∈ ball j (2 * ρ j)) ∨
    (∃ j ∈ slim.centres, x ∈ ball j (2 * (Δ * ρ j))) ∨
    ∃ j ∈ edge.centres, dist x j < 2 * Δ * ρ j

/-- `LocalChartFamilyQ` with the curvature buffer asserted at `p ∈ U₁`. -/
structure ChartFamilyQOn (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
    (σc μ b s b' s' ε γc βc Lmax : ℝ) (U₁ U₂ : Set X)
    extends ChartFamilyOn X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc U₁ U₂ where
  circle_cutoff_eq : ∀ j (hj : j ∈ circle.centres),
    let c := circle.chart j hj
    let ζ := circle.cutoff j
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    ζ = c.formulaCutoff
  slim_cutoff_eq : ∀ j (hj : j ∈ slim.centres),
    let S := slim.centre j hj
    let P := S.packet
    letI := S.instZ
    let hMc : CompleteSpace X := ‹CompleteSpace X›
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : CompleteSpace X :=
      (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
    P.cutoff = P.toSlimChart.formulaCutoff
  sectional_buffer : ∀ L, 0 < L → L ≤ Lmax → ∀ p ∈ U₁, ∀ y ∈ ball p (L * ρ p),
    SectionalBoundedBelowAt g y (-((L * ρ p) ^ 2)⁻¹)

/-- `LocalChartFamilyE` (edge coarse-border composite), region form. -/
structure ChartFamilyEOn (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
    (σc μ b s b' s' ε γc βc Lmax τ : ℝ) (U₁ U₂ : Set X)
    extends ChartFamilyQOn X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax U₁ U₂ where
  edge_coarse : ∀ j (hj : j ∈ edge.centres),
    let c := edge.chart j hj
    let A : Set X := closure
      {y | @isEdgePoint.{u, 0} X (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y))) y Δ b' s'}
    let hMc : CompleteSpace X := ‹CompleteSpace X›
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : CompleteSpace X :=
      (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
    (c.Qn j = 0 ∧
      (∀ x ∈ ball j (200 * Δ), ∀ y ∈ ball j (200 * Δ),
        (|dist (c.Qn x) (c.Qn y) - dist x y| ≤ τ * Δ)) ∧
      (∀ x ∈ ball j (200 * Δ), 0 ≤ (c.Qn x).snd) ∧
      (∀ z : WithLp 2 (ℝ × ℝ), (|z.fst| ≤ 100 * Δ) → z.snd ∈ Icc 0 (100 * Δ) →
        ∃ x ∈ ball j (200 * Δ), dist (c.Qn x) z ≤ τ * Δ) ∧
      (∀ a ∈ A ∩ ball j (190 * Δ), (c.Qn a).snd ≤ τ * Δ) ∧
      (∀ t : ℝ, (|t| ≤ 100 * Δ) → ∃ a ∈ A ∩ ball j (190 * Δ),
        dist (c.Qn a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ))

/-- `CircleAdaptedCentre` on a complete carrier. -/
structure CircleAdaptedCentreOn (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (β : ℕ → ℝ) (γ : ℝ) (U₁ U₂ : Set X)
    (C : CircleFamilyOn 𝓘(ℝ, E3) X ρ hρ β U₁ U₂) (j : X) (hj : j ∈ C.centres) where
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
    let hMc : CompleteSpace X := ‹CompleteSpace X›
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

end RegionData

section RegionZero

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type) [mM : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- `ZeroModelFamily` with centres in `U₁` and the tenth-ball cover of `U₁ ∩ Z₀` (balls MEET the
zero stratum). -/
structure ZeroModelFamilyOn (g : SmoothRiemannianMetric I M) (ρ : M → ℝ)
    (hρ : ∀ p, 0 < ρ p) (β : ℕ → ℝ) {ι : Type} (N C : ι → Type) [∀ b, MetricSpace (N b)]
    [∀ b, ChartedSpace H (N b)] [∀ b, MetricSpace (C b)] (o : ∀ b, C b) (δ ε e T V : ℝ)
    (U₁ U₂ : Set M) where
  centres : Set M
  finite_centres : centres.Finite
  centres_subset : centres ⊆ U₁
  zero : (i : M) → i ∈ centres → ZeroModelBall I M g N C o δ ε e
  zero_center : ∀ i (hi : i ∈ centres), (zero i hi).center = i
  radius_mem : ∀ i (hi : i ∈ centres),
    T * ρ i ≤ (zero i hi).radius ∧ (zero i hi).radius ≤ V * ρ i
  disjoint : ∀ i (hi : i ∈ centres) j (hj : j ∈ centres), i ≠ j →
    Disjoint (ball i (zero i hi).radius) (ball j (zero j hj).radius)
  meets_stratum : ∀ i (hi : i ∈ centres),
    (ball i (zero i hi).radius ∩ scaledSplittingStratum.{0, 0} ρ hρ β 0).Nonempty
  covers_stratum : U₁ ∩ scaledSplittingStratum.{0, 0} ρ hρ β 0 ⊆
    ⋃ i, ⋃ (hi : i ∈ centres), ball i ((zero i hi).radius / 10)
  one_end : ∀ i (hi : i ∈ centres), ∀ K : Set (N (zero i hi).model), IsCompact K →
    ∀ a₁ a₂ : N (zero i hi).model,
      ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a₁) →
      ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a₂) →
      connectedComponentIn Kᶜ a₁ = connectedComponentIn Kᶜ a₂

end RegionZero

/-- **`LocalPacketsOn`** (P0): the shared regionalised LC87 packets — the family with circle
adapted-coordinate packets and the zero family on the SAME data, centres in `U₁`, covers on
`U₁`/`U₂`. The closed case is `U₁ = U₂ = univ` (`LocalPacketsOn.ofClosed`). -/
structure LocalPacketsOn (X : Type) [mX : MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompleteSpace X] [SigmaCompactSpace X]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
    (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ) (U₁ U₂ : Set X)
    extends ChartFamilyEOn X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ U₁ U₂ where
  circleAdapted : ∀ j (hj : j ∈ circle.centres),
    CircleAdaptedCentreOn X g hmetric ρ hρ β γ U₁ U₂ circle j hj
  N : X → Type
  C : X → Type
  [instMetricN : ∀ a, MetricSpace (N a)]
  [instChartedN : ∀ a, ChartedSpace E3 (N a)]
  [instMetricC : ∀ a, MetricSpace (C a)]
  o : ∀ a, C a
  zero : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂

/-! ## The closed specialization `U₁ = U₂ = univ` -/

section Closed

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The closed circle family as a regionalised one over `univ`. -/
def CircleFamilyOn.ofClosed (C : CircleFamily 𝓘(ℝ, E3) X ρ hρ β) :
    CircleFamilyOn 𝓘(ℝ, E3) X ρ hρ β univ univ :=
  { C with
    centres_subset := fun _ hj => ⟨mem_univ _, C.centres_subset hj⟩
    covers := fun p hp => C.covers p hp.2 }

/-- A closed slim centre as a slim centre on the (complete) carrier. -/
def SlimCentreOn.ofClosed {j : X} (S : SlimCentre X g hmetric ρ hρ (β 1) Δ σs K j) :
    SlimCentreOn X g hmetric ρ hρ (β 1) Δ σs K j :=
  { S with }

/-- The closed slim family as a regionalised one over `univ`. -/
def SlimFamilyOn.ofClosed (S : SlimFamily X g hmetric ρ hρ β Δ σs K) :
    SlimFamilyOn X g hmetric ρ hρ β Δ σs K univ univ :=
  { S with
    centres_subset := fun _ hj => ⟨mem_univ _, (S.centres_subset hj).1, (S.centres_subset hj).2⟩
    covers := fun p hp => S.covers p hp.2
    centre := fun j hj => SlimCentreOn.ofClosed (S.centre j hj) }

/-- The closed edge family as a regionalised one over `univ`. -/
def EdgeFamilyOn.ofClosed (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) :
    EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc univ univ :=
  { F with
    centres_subset := subset_univ _
    covers_strong := fun a _ ha => F.covers_strong a ha
    covers_nonslim := fun p hp => F.covers_nonslim p hp.2 }

/-- The closed zero-model family as a regionalised one over `univ`. -/
def ZeroModelFamilyOn.ofClosed {ι : Type} {N C : ι → Type} [∀ a, MetricSpace (N a)]
    [∀ a, ChartedSpace E3 (N a)] [∀ a, MetricSpace (C a)] {o : ∀ a, C a}
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) :
    ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V univ univ :=
  { Z with
    centres_subset := subset_univ _
    covers_stratum := fun _ hx => Z.covers_stratum hx.2 }

/-- **The closed specialization** (review 45 §3.3): every closed `LocalChartPackets` is a
`LocalPacketsOn` with `U₁ = U₂ = univ` (same centres, same per-centre payloads). -/
def LocalPacketsOn.ofClosed
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V) :
    LocalPacketsOn X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      univ univ where
  contMDiff_scale := P.contMDiff_scale
  lipschitz_scale := P.lipschitz_scale
  circle := CircleFamilyOn.ofClosed P.circle
  slim := SlimFamilyOn.ofClosed P.slim
  edge := EdgeFamilyOn.ofClosed P.edge
  exhaustion := fun x _ => P.exhaustion x
  circle_cutoff_eq := P.circle_cutoff_eq
  slim_cutoff_eq := P.slim_cutoff_eq
  sectional_buffer := fun L hL hLm p _ => P.sectional_buffer L hL hLm p
  edge_coarse := P.edge_coarse
  circleAdapted := fun j hj => { P.circleAdapted j hj with }
  N := P.N
  C := P.C
  instMetricN := P.instMetricN
  instChartedN := P.instChartedN
  instMetricC := P.instMetricC
  o := P.o
  zero :=
    letI := P.instMetricN
    letI := P.instChartedN
    letI := P.instMetricC
    ZeroModelFamilyOn.ofClosed P.zero

end Closed

/-- **Consumer / closed producer.** The closed producer `eventually_nonempty_localChartPackets`
composed with the closed specialization: on one tail of every closed standing sequence the
regionalised packets `LocalPacketsOn … univ univ` exist, on the same scale `ρ` with LC02's
bounds. -/
theorem eventually_nonempty_localPacketsOn_closed_BDRY2
    {σs : ℝ} (hσs : 0 < σs) (hσs1 : σs ≤ 1 / 100) (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ → ℝ)
    (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ βc γc : ℝ, 0 < βc → βc < γc / 1000 → 0 < γc → γc < 1 / 100 →
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ → Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ bc₀ : ℝ, 0 < bc₀ ∧
      ∀ σc ε μ τ : ℝ, 0 < σc → σc ≤ σ₀ → σc < 1 → 0 < ε → ε < 1 / 100 → 0 < μ → μ ≤ 1 / 1000000 →
        0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 →
      ∀ s b' s' : ℝ, 0 < s → s < 1 / 100 → s < b' / 100000 → s < s' / 100000 →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 → ∃ a₀ b₁ : ℝ, 0 < a₀ ∧ 0 < b₁ ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{0, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < s' / (100000000 * Δ ^ 2) →
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → b < b₁ → 100 * Δ < b⁻¹ → ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{0, 0} →
      ∀ ζ : ℝ, β 1 < ζ → ζ < 1 →
      ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < 1 / 4 ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ T : ℝ, 0 < T → 20 * Λ' ≤ T → ∀ e : ℝ, 0 < e → e < 1 / 40 →
      ∀ Lmax : ℝ, 0 < Lmax →
      ∀ (X : ℕ → Type) [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
        [∀ i, IsManifold 𝓘(ℝ, E3) ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E3) (X i))
        (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
        (α : ℕ → ℝ), Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
        (∀ i (p : X i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
          ∀ C, 0 < C → C < α i → ∀ k ≤ K,
          ∀ y ∈ riemannianBallOf (g i) p (C * firstVolumeScale (g i) p v),
            curvatureDerivativeNorm (g i) k y ≤
              A C v * (firstVolumeScale (g i) p v ^ (k + 2))⁻¹) →
        (∀ i, ManifoldOrientation (𝓡 3) (X i) 3) →
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ i in atTop,
        ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        (∀ p, firstVolumeScale (g i) p w / 2 < ρ p ∧
          ρ p < 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
        Nonempty (LocalPacketsOn (X i) (g i) (hmetric i) ρ hρpos Λ β Δ σs K
          σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V univ univ) := by
  obtain ⟨a₂, ha₂, h⟩ := eventually_nonempty_localChartPackets hσs hσs1 K hK A hA
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, h⟩ := h γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, h⟩ := h βc γc hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, h⟩ := h β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, fun σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ s b' s' hs
    hssmall hsb' hss' hb'd hs'd hb'e hs'e => ?_⟩
  obtain ⟨a₀, b₁, ha₀, hb₁, h⟩ := h σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ s b' s' hs
    hssmall hsb' hss' hb'd hs'd hb'e hs'e
  refine ⟨a₀, b₁, ha₀, hb₁, fun σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend => ?_⟩
  obtain ⟨w₀, hw₀, h⟩ := h σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend
  refine ⟨w₀, hw₀, fun w hw hww hwc b hb hbs hbc hbb₁ hsource => ?_⟩
  obtain ⟨b₀, hb₀, h⟩ := h w hw hww hwc b hb hbs hbc hbb₁ hsource
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβone hβ3 ζ hβζ hζone => ?_⟩
  obtain ⟨εr, δ', Λ5, hεr, hεr4, hδ', hΛ5, h⟩ := h β hβ2 hβ1 hβ1b hβone hβ3 ζ hβζ hζone
  refine ⟨εr, δ', Λ5, hεr, hεr4, hδ', hΛ5,
    fun T hT hTΛ e he he1 Lmax hLmax X _ _ _ _ g hmetric α hα hstand hder hor => ?_⟩
  obtain ⟨V, hTV, δ, hδ0, hδδ', h⟩ :=
    h T hT hTΛ e he he1 Lmax hLmax X g hmetric α hα hstand hder hor
  refine ⟨V, hTV, δ, hδ0, hδδ', ?_⟩
  filter_upwards [h] with i hi
  obtain ⟨ρ, hρpos, hρb, ⟨P⟩⟩ := hi
  exact ⟨ρ, hρpos, hρb, ⟨LocalPacketsOn.ofClosed P⟩⟩

end DifferentialGeometry.Geometry.Collapse
