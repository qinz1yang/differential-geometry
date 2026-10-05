import DifferentialGeometry.Geometry.Collapse.StrongEdgeFullCollarCover

/-!
# The LC84 edge chart (the edge packet without its disk bundle)

Blueprint LC84 (`def:collapse-edge-packet`, master207A:30874), items 1–3, at NORMALIZED scale
(the ambient metric is `ρ(p)⁻¹ d`, `ρ(center) = 1`; the convention of `CircleChart` inside
`CircleFamily` and of LFR44's per-centre clauses). `EdgeChart g hEnorm Δ σ μ b γ β A ρ F` records,
for the closed weak edge set `A`, the normalized scale `ρ` and the normalized shared smoothing `F`
of `d_A` (parameters, shared by the edge family):

1. the ACTUAL rank-one map `split : (M, center) → ℝ × Y` (a `b`-approximation) and the plane map
   `Qn` with `(Qn z).1 = (split z).1` (LFR32's coarse-border comparison, LFR44's `Qn`);
2. (with `A`, `F` as parameters) the coarse-border data enter through `Qn`;
3. the tangential coordinate `coord = η_p` on `B(center, 100Δ)` with LFR19's clauses (smooth on a
   neighbourhood of `B̄(center, 100Δ)`, `η_p(center) = 0`, `(1 + σ)`-Lipschitz, value error `< μΔ`,
   (LFR19.1) on `B(100Δ) × B(1000Δ)`), the edge disk domain `{|η_p| < 4Δ, F/ρ ≤ 4Δ}` containing
   `B(center, 3Δ)` with the edge cutoff `= 1` there, and LFR38's rank-two collar of
   `J = (η_p, F/ρ)` at every collar point (LFR44's clause with `ρ(p) = 1`).

NOT recorded here: the comparison with `ℝ × Z` (LC81) and the proper `D²`-bundle with boundary
`F/ρ = 4Δ` (LFR28; `EdgeDiskPacket` once the LFR28 row is frozen).
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open GC.MetricGeometry DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [mM : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **LC84 edge chart** at normalized scale (fields = LFR44's per-centre clauses with
`ρ(center) = 1`, plus LFR19's clauses for the chosen tangential coordinate). -/
structure EdgeChart (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (Δ σ μ b γ β : ℝ) (A : Set M) (ρ F : M → ℝ) where
  /-- The strong edge centre `p`. -/
  center : M
  rho_center : ρ center = 1
  center_mem : center ∈ A
  /-- The rank-one target `ℝ × Y` and the actual splitting map. -/
  Y : Type
  [instY : MetricSpace Y]
  q : Y
  split : KleinerLottApprox center (WithLp.toLp 2 ((0 : ℝ), q)) b
  /-- The plane comparison map of the coarse border (LFR32/LFR44). -/
  Qn : M → WithLp 2 (ℝ × ℝ)
  Qn_fst : ∀ z, (Qn z).fst = (split.toFun z).fst
  /-- The tangential coordinate `η_p`. -/
  coord : M → ℝ
  domain : Set M
  isOpen_domain : IsOpen domain
  closedBall_subset_domain : closedBall center (100 * Δ) ⊆ domain
  contMDiffOn_coord : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ coord domain
  coord_center : coord center = 0
  lipschitz : LipschitzWith (Real.toNNReal (1 + σ)) coord
  value : ∀ x ∈ ball center (100 * Δ), |coord x - (split.toFun x).fst| < μ * Δ
  test : ∀ x ∈ ball center (100 * Δ), ∀ x' ∈ ball center (1000 * Δ), 100 * Δ < dist x x' →
    ∀ w : TangentSpace I x, g.inner x w w = 1 →
    intrinsicGeodesic g hEnorm x w (dist x x') = x' →
    |mvfderiv (I := I) coord x w - ((split.toFun x').fst - (split.toFun x).fst) / dist x x'| < σ
  /-- The edge disk domain contains `B(center, 3Δ)` ... -/
  disk_subset : ball center (3 * Δ) ⊆ edgeDiskDomain center Δ (fun x => coord x.val) F ρ
  /-- ... and the edge cutoff is one there. -/
  cutoff_eq_one : EqOn ((Subtype.val : ball center (100 * Δ) → M).extend
    (fun x => edgeCoordinateProfile (coord x.val / Δ) *
      edgeHeightProfile (F x.val / (Δ * ρ x.val))) 0) 1 (ball center (3 * Δ))
  /-- LFR38's full collar at every collar point of the disk band. -/
  collar : ∀ x ∈ ball center (100 * Δ), |coord x| ≤ 10 * Δ →
    Δ / 10 ≤ F x / ρ x → F x / ρ x ≤ 10 * Δ →
    ∃ hq : 99 / 100 ≤ ρ x ∧ ρ x ≤ 101 / 100,
      (letI := mM.rescale (ρ x)⁻¹ (inv_pos.mpr (lt_of_lt_of_le (by norm_num) hq.1));
        ∃ Φ : KleinerLottApprox x (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) β,
          ∀ y, Φ.toFun y = @planeComparisonMap M mM Qn center x Δ (ρ x) y) ∧
      let J := edgeReferenceCoordinates ![coord, fun z => F z / ρ z]
      ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ J (ball x (300 * ρ x)) ∧
      (∀ y ∈ ball x (100 * ρ x), Function.Surjective (mvfderiv (I := I) J y)) ∧
      (∀ y ∈ ball x (100 * ρ x), ∀ z ∈ ball x (100 * ρ x),
        ‖J y - J z‖ ≤ (1 + γ) * (dist y z / ρ x)) ∧
      (∀ y ∈ ball x (100 * ρ x), infDist (J y) (ball (J x) 100) < 100 * γ) ∧
      (∀ v ∈ ball (J x) 100, ∃ y ∈ ball x (100 * ρ x), ‖J y - v‖ < 100 * γ) ∧
      ∀ y ∈ ball x (100 * ρ x), ∀ z ∈ ball x (100 * ρ x / γ), ρ x < dist y z →
        ∀ W : TangentSpace I y, g.inner y W W = 1 →
        intrinsicGeodesic g hEnorm y W (dist y z) = z →
        ‖ρ x • mvfderiv (I := I) J y W - (dist y z / ρ x)⁻¹ •
          (planeReferenceIsometry (planeComparisonMap Qn center x Δ (ρ x) z) -
            planeReferenceIsometry (planeComparisonMap Qn center x Δ (ρ x) y))‖ < γ

end DifferentialGeometry.Geometry.Collapse
