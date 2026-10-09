import DifferentialGeometry.Geometry.Collapse.FixtureC1.LatticeTorusRank
import DifferentialGeometry.Geometry.Collapse.FixtureC1.LatticeTorusFlat
import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusGeodesic

/-!
# Explicit consumer of the lattice-torus kernel (S-FIXTURE-C1, K1, consumer)

The torus `T³ = ℝ³ / (400ℤ ⊕ 400ℤ ⊕ (1/50)ℤ)` at the scale `R = 1` with the kernel tolerances
`β₂ = 1/50`, `β₃ = 3/20` (review 75 section C: independent model-kernel tests may choose their own
constants; the register values are used in the fixture of group G2):

* every point has splitting rank exactly two, the two-stratum is the whole torus;
* no point is a strong edge point (`Δ = 1200`, `b = s = 1/300`);
* distances: `5 ≤ d(π 0, π (3, 4, 0)) ≤ 5 + 1/100`;
* `sec ≥ -1` everywhere (`sec = 0`);
* the projected line `t ↦ π(x + t v)` is a geodesic (scale constant `c = 1`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] torMS_FXC1

/-- The periods `(400, 400, 1/50)`. -/
def torPeriodsEx_FXC1 : TorusPeriods_FXC1 where
  L := fun i => if i = 2 then 1 / 50 else 400
  pos := fun i => by
    by_cases h : i = 2 <;> simp [h]

/-- The kernel tolerances `β₂ = 1/50`, `β₃ = 3/20` (and `1/50` elsewhere). -/
def torBetaEx_FXC1 : ℕ → ℝ := fun k => if k = 3 then 3 / 20 else 1 / 50

theorem torEx_planePeriod_FXC1 : planePeriod_FXC1 torPeriodsEx_FXC1 = 400 := by
  simp [planePeriod_FXC1, torPeriodsEx_FXC1]

theorem torEx_L2_FXC1 : torPeriodsEx_FXC1.L 2 = 1 / 50 := by simp [torPeriodsEx_FXC1]

/-- Every point of the example torus has splitting rank exactly two at the scale `1`. -/
theorem torEx_rank_two_FXC1 (p : Tor_FXC1 torPeriodsEx_FXC1) :
    scaledSplittingRank.{0, 0} (fun _ : Tor_FXC1 torPeriodsEx_FXC1 => (1 : ℝ))
      (fun _ => one_pos) torBetaEx_FXC1 p = 2 :=
  torRank_eq_two_FXC1 torPeriodsEx_FXC1 (R := 1) (β := torBetaEx_FXC1) one_pos
    (by simp [torBetaEx_FXC1])
    (by simp [torBetaEx_FXC1]) (by simp [torBetaEx_FXC1]) (by
      rw [torEx_L2_FXC1]; simp [torBetaEx_FXC1])
    (by rw [torEx_planePeriod_FXC1]; simp [torBetaEx_FXC1]; norm_num) p

theorem torEx_stratum_FXC1 :
    scaledSplittingStratum.{0, 0} (fun _ : Tor_FXC1 torPeriodsEx_FXC1 => (1 : ℝ))
      (fun _ => one_pos) torBetaEx_FXC1 2 = univ :=
  eq_univ_of_forall torEx_rank_two_FXC1

/-- No point of the example torus is a strong edge point. -/
theorem torEx_not_edge_FXC1 (p : Tor_FXC1 torPeriodsEx_FXC1) :
    ¬ @isEdgePoint.{0, 0} (Tor_FXC1 torPeriodsEx_FXC1)
      ((torMS_FXC1 torPeriodsEx_FXC1).rescale (1 : ℝ)⁻¹ (inv_pos.mpr one_pos)) p 1200 (1 / 300)
      (1 / 300) :=
  torNotEdge_FXC1 torPeriodsEx_FXC1 (R := 1) (β := torBetaEx_FXC1) one_pos
    (by simp [torBetaEx_FXC1]) (by simp [torBetaEx_FXC1])
    (by simp [torBetaEx_FXC1]) (by rw [torEx_L2_FXC1]; simp [torBetaEx_FXC1])
    (by rw [torEx_planePeriod_FXC1]; simp [torBetaEx_FXC1]; norm_num) (by norm_num)
    (by norm_num) (by norm_num) p

/-- The distance of `π 0` and `π (3, 4, 0)` is between `5` and `5 + 1/100`. -/
theorem torEx_dist_FXC1 :
    5 ≤ dist (torPi_FXC1 torPeriodsEx_FXC1 0)
        (torPi_FXC1 torPeriodsEx_FXC1 (WithLp.toLp 2 ![3, 4, 0])) ∧
      dist (torPi_FXC1 torPeriodsEx_FXC1 0)
        (torPi_FXC1 torPeriodsEx_FXC1 (WithLp.toLp 2 ![3, 4, 0])) ≤ 5 + 1 / 100 := by
  have hn : ‖planeL_FXC1 ((0 : E3) - WithLp.toLp 2 ![3, 4, 0])‖ = 5 := by
    have h : planeL_FXC1 ((0 : E3) - WithLp.toLp 2 ![3, 4, 0]) = !₂[-3, -4] := by
      ext i
      fin_cases i <;> simp
    rw [h]
    have h2 := norm_sq_mk_SMR (-3) (-4)
    refine (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp ?_
    rw [h2]; norm_num
  constructor
  · have := norm_planeL_le_dist_torPi_FXC1 torPeriodsEx_FXC1 0 (WithLp.toLp 2 ![3, 4, 0])
      (by rw [hn, torEx_planePeriod_FXC1]; norm_num)
    rwa [hn] at this
  · have := dist_torPi_le_FXC1 torPeriodsEx_FXC1 0 (WithLp.toLp 2 ![3, 4, 0])
    rw [hn, torEx_L2_FXC1] at this
    linarith

/-- The example torus is flat: `sec ≥ -1` everywhere. -/
theorem torEx_sectional_FXC1 (y : Tor_FXC1 torPeriodsEx_FXC1) :
    SectionalBoundedBelowAt (torMetric_FXC1 torPeriodsEx_FXC1) y (-1) :=
  torMetric_sectional_FXC1 torPeriodsEx_FXC1 y (by norm_num)

/-- Projected lines are geodesics of the example torus (and of its rescalings). -/
theorem torEx_geodesic_FXC1 (x v : E3) :
    Geodesic.IsGeodesic (I := 𝓘(ℝ, E3)) (scaleMetric (1 : ℝ) one_pos
      (torMetric_FXC1 torPeriodsEx_FXC1))
      (fun t : ℝ => torPi_FXC1 torPeriodsEx_FXC1 (x + t • v)) :=
  isGeodesic_torPi_line_FXC1 torPeriodsEx_FXC1 one_pos x v

end DifferentialGeometry.Geometry.Collapse
