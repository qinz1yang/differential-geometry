import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusAdaptedTest
import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusCircleFamily
import DifferentialGeometry.Geometry.Collapse.FixtureC1.LatticeTorusRank
import DifferentialGeometry.Geometry.Collapse.FixtureC1.ThinPlaneKL

/-!
# The circle adapted centre of the flat torus (S-FIXTURE-C1b, F1, G4 file 3)

`torCircleAdapted_FXC1 : CircleAdaptedCentre (Tor Λ) … (torCircleFamily_FXC1 …) j hj` at every
centre of the circle family of the flat torus:

* `split` is the Kleiner-Lott `β₂`-approximation `x ↦ (η_j x, ⋆)` into `ℝ² ×₂ PUnit` based at `j`
  (`torPlaneKLAt_FXC1`: the plane chart is an almost isometry on the `Lp/4` ball and covers the
  `Lp/2` ball of the plane);
* `adapted` holds with error `0 < γ` (the chart coordinate IS the plane component of `split`);
* `lipschitz`: `η_j` is `1`-Lipschitz at the normalized scale, hence `(1 + γ)`-Lipschitz;
* `test`: the geodesic test (`torTest_FXC1`): the projected lines are the geodesics and `η_j` is
  affine along them.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] torMS_FXC1

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Adapted

/-- **The plane chart of the torus is a Kleiner-Lott `δ`-approximation based at any `j`** (the
version of `torPlaneKL_FXC1` at the base point `j` itself, not at `π (lift j)`). Its map is
`x ↦ (η_j x, ⋆)`. -/
def torPlaneKLAt_FXC1 (Λ : TorusPeriods_FXC1) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hL2 : Λ.L 2 ≤ 2 * (R * δ)) (hLp : 4 * (R * δ⁻¹) ≤ planePeriod_FXC1 Λ) (j : Tor_FXC1 Λ) :
    @KleinerLottApprox (Tor_FXC1 Λ) (WithLp 2 (ℝ² × PUnit.{1}))
      ((torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)) _ j
      (WithLp.toLp 2 ((0 : ℝ²), PUnit.unit)) δ := by
  have hbase : ell_FXC1 Λ (torLift_FXC1 Λ j) j = 0 := by
    have h := ell_base_FXC1 Λ (torLift_FXC1 Λ j)
    rwa [torPi_torLift_FXC1] at h
  refine kleinerLott_of_thin_chart_FXC1 (D := Λ.L 2 / 2) hR hδ hδ1 (ell_FXC1 Λ (torLift_FXC1 Λ j))
    hbase (fun q hq q' hq' => ?_) (by linarith) (fun u hu => ?_)
  · refine ell_dist_bounds_FXC1 Λ (torLift_FXC1 Λ j) q q' (r := R * δ⁻¹) (by linarith) ?_ ?_
    · rw [torPi_torLift_FXC1, dist_comm]; exact hq
    · rw [torPi_torLift_FXC1, dist_comm]; exact hq'
  · have hLp0 := planePeriod_pos_FXC1 Λ
    obtain ⟨q, hq, hd⟩ := exists_ell_eq_FXC1 Λ (torLift_FXC1 Λ j) u (by linarith)
    rw [torPi_torLift_FXC1] at hd
    exact ⟨q, by rw [mem_ball, dist_comm]; exact lt_of_le_of_lt hd hu, hq⟩

variable (Λ : TorusPeriods_FXC1) {R : ℝ} (hR : 0 < R) {β : ℕ → ℝ} (hβ2 : 0 < β 2)
  (hβ2s : β 2 ≤ 1 / 10 ^ 7) (hL2 : Λ.L 2 ≤ R * β 2) (hLp : 8 * R / β 2 ≤ planePeriod_FXC1 Λ)
  (N : ℕ) (hL0 : Λ.L 0 = N * R) (hL1 : Λ.L 1 = N * R) (hβ3 : β 3 ≤ 3 / 20)

include hR hβ2 hβ2s hL2 hLp in
/-- The Kleiner-Lott split of the torus at `j` with error `β₂`. -/
def torSplit_FXC1 (j : Tor_FXC1 Λ) :
    @KleinerLottApprox (Tor_FXC1 Λ) (WithLp 2 (ℝ² × PUnit.{1}))
      ((torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)) _ j
      (WithLp.toLp 2 ((0 : ℝ²), PUnit.unit)) (β 2) :=
  torPlaneKLAt_FXC1 Λ hR hβ2 (by linarith [hβ2s]) (by
    have : 0 ≤ R * β 2 := mul_nonneg hR.le hβ2.le
    linarith) (by
    have h : 4 * (R * (β 2)⁻¹) ≤ 8 * R / β 2 := by
      rw [div_eq_mul_inv]
      have : 0 ≤ R * (β 2)⁻¹ := mul_nonneg hR.le (inv_nonneg.mpr hβ2.le)
      nlinarith
    exact h.trans hLp) j

variable {γ : ℝ} (hγ : 0 < γ)

include hR hβ2 hβ2s hL2 hLp hL0 hL1 hβ3 hγ in
/-- **The circle adapted centre of the flat torus** at every centre `j` of the circle family. -/
def torCircleAdapted_FXC1 (j : Tor_FXC1 Λ)
    (hj : j ∈ (torCircleFamily_FXC1 Λ hR hβ2 hβ2s hL2 hLp N hL0 hL1 hβ3).centres) :
    CircleAdaptedCentre (Tor_FXC1 Λ) (torMetric_FXC1 Λ) (torMS_hmetric_FXC1 Λ) (fun _ => R)
      (fun _ => hR) β γ (torCircleFamily_FXC1 Λ hR hβ2 hβ2s hL2 hLp N hL0 hL1 hβ3) j hj where
  Y := PUnit.{1}
  a := PUnit.unit
  split := torSplit_FXC1 Λ hR hβ2 hβ2s hL2 hLp j
  adapted := fun x _ => by
    change ‖torEta_FXC1 Λ R j x - torEta_FXC1 Λ R j x‖ < γ
    rw [sub_self, norm_zero]
    exact hγ
  lipschitz := by
    intro c
    let _ := (torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    have hxp := torRescaledBall_FXC1 Λ hR (mem_ball.mp hx)
    have hyp := torRescaledBall_FXC1 Λ hR (mem_ball.mp hy)
    have h := (torEta_dist_bounds_FXC1 Λ hR hβ2 hβ2s hLp j x y (by linarith) (by linarith)).1
    rw [Real.coe_toNNReal _ (by linarith)]
    change dist (torEta_FXC1 Λ R j x) (torEta_FXC1 Λ R j y) ≤
      (1 + γ) * (R⁻¹ * @dist _ (torMS_FXC1 Λ).toDist x y)
    rw [dist_eq_norm]
    have : 0 ≤ R⁻¹ * @dist _ (torMS_FXC1 Λ).toDist x y :=
      mul_nonneg (inv_pos.mpr hR).le (@dist_nonneg _ (torMS_FXC1 Λ).toPseudoMetricSpace x y)
    nlinarith
  test := torTest_FXC1 Λ hR hβ2 hβ2s hLp j hγ

end Adapted

section Residual

variable (Λ : TorusPeriods_FXC1) {R : ℝ} (hR : 0 < R) {β : ℕ → ℝ} (hβ2 : 0 < β 2)
  (hβ2s : β 2 ≤ 1 / 10 ^ 7) (hL2 : Λ.L 2 ≤ R * β 2) (hLp : 8 * R / β 2 ≤ planePeriod_FXC1 Λ)

include hR hβ2 hβ2s hL2 hLp in
/-- **LFR07's residual enclosure** of the circle chart of the torus: `‖η_j‖ ≤ 8` on `B(j, 200)`
(normalized at `j`) implies membership in `B(j, 10)`. -/
theorem torCircle_residual_FXC1 (j : Tor_FXC1 Λ) :
    letI := (torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)
    ∀ x ∈ ball j 200, ‖torEta_FXC1 Λ R j x‖ ≤ 8 → x ∈ ball j 10 := by
  intro x hx h8
  let _ := (torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)
  have h := torEta_enclosure_FXC1 Λ hR hβ2 hβ2s hL2 hLp j x (a := 9) (mem_ball.mp hx)
    (by linarith)
  exact mem_ball.mpr (lt_trans h (by norm_num))

end Residual

end DifferentialGeometry.Geometry.Collapse
