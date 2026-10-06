import DifferentialGeometry.Geometry.Collapse.FixtureC1.LatticeTorusRank
import DifferentialGeometry.Geometry.Collapse.FixtureC1.LatticeTorusFlat
import DifferentialGeometry.Geometry.Collapse.LocalExport.CircleChart
import DifferentialGeometry.Geometry.Collapse.AnnularAdaptedCoordinates

/-!
# The circle chart of the flat torus at a centre (S-FIXTURE-C1, F1, file 1)

At the constant scale `ρ ≡ R` with `R > 0` and the thin torus of the K1 kernel
(`L₂ ≤ R β₂`, `Lp ≥ 8R/β₂`, `β₂ ≤ 10⁻⁷`), the LC83 circle chart at a point `j = π pt` is
`η_j = R⁻¹ · ell(pt)` (the plane chart of K1 at normalized scale), produced by the LC83 producer
`CircleChart.ofLocalModel` on the rescaled complete Riemannian manifold `(T³, R⁻¹ d, R⁻² g)`.

* `torEta_FXC1`: the normalized coordinate; `torEta_*`: smoothness, rank, Lipschitz bound,
  enclosure on `B(j, 200)`;
* `torChart_FXC1`: the `CircleChart` at normalized scale with `center = j`, `coord = torEta`.
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

/-- A chosen lift of a point of the torus. -/
def torLift_FXC1 (Λ : TorusPeriods_FXC1) (j : Tor_FXC1 Λ) : E3 :=
  (torPi_surjective_FXC1 Λ j).choose

theorem torPi_torLift_FXC1 (Λ : TorusPeriods_FXC1) (j : Tor_FXC1 Λ) :
    torPi_FXC1 Λ (torLift_FXC1 Λ j) = j :=
  (torPi_surjective_FXC1 Λ j).choose_spec

/-- The normalized plane coordinate `η_j = R⁻¹ · ell(j̃)`. -/
def torEta_FXC1 (Λ : TorusPeriods_FXC1) (R : ℝ) (j : Tor_FXC1 Λ) (q : Tor_FXC1 Λ) : ℝ² :=
  R⁻¹ • ell_FXC1 Λ (torLift_FXC1 Λ j) q

theorem torEta_center_FXC1 (Λ : TorusPeriods_FXC1) (R : ℝ) (j : Tor_FXC1 Λ) :
    torEta_FXC1 Λ R j j = 0 := by
  have h := ell_base_FXC1 Λ (torLift_FXC1 Λ j)
  rw [torPi_torLift_FXC1] at h
  rw [torEta_FXC1, h, smul_zero]

section Chart

variable (Λ : TorusPeriods_FXC1) {R : ℝ} (hR : 0 < R) {β : ℕ → ℝ} (hβ2 : 0 < β 2)
  (hβ2s : β 2 ≤ 1 / 10 ^ 7) (hL2 : Λ.L 2 ≤ R * β 2) (hLp : 8 * R / β 2 ≤ planePeriod_FXC1 Λ)

include hR hβ2 hβ2s hLp in
theorem torLp_ge_FXC1 : 8 * 10 ^ 7 * R ≤ planePeriod_FXC1 Λ := by
  refine le_trans ?_ hLp
  rw [le_div_iff₀ hβ2]
  have : 8 * 10 ^ 7 * R * β 2 ≤ 8 * 10 ^ 7 * R * (1 / 10 ^ 7) :=
    mul_le_mul_of_nonneg_left hβ2s (by positivity)
  linarith

/-- Points of the torus within `r ≤ Lp/2` of `j = π pt` lie in the image of the slab. -/
theorem mem_image_ellDom_of_dist_lt_FXC1 (pt : E3) (q : Tor_FXC1 Λ) {r : ℝ}
    (hr : r ≤ planePeriod_FXC1 Λ / 2) (h : dist (torPi_FXC1 Λ pt) q < r) :
    q ∈ torPi_FXC1 Λ '' ellDom_FXC1 Λ pt := by
  obtain ⟨y, rfl, hy⟩ := exists_lift_of_dist_lt_FXC1 Λ pt q h
  refine ⟨y, ?_, rfl⟩
  change ‖planeL_FXC1 (y - pt)‖ < _
  rw [norm_sub_rev] at hy
  linarith [norm_planeL_le_FXC1 (y - pt)]

include hR hβ2 hβ2s hLp in
/-- The normalized coordinate is smooth on `B(j, 200)`. -/
theorem contMDiffOn_torEta_FXC1 (j : Tor_FXC1 Λ) :
    ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) ∞ (torEta_FXC1 Λ R j)
      (@ball _ ((torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)).toPseudoMetricSpace j 200) := by
  have hLp' := torLp_ge_FXC1 Λ hR hβ2 hβ2s hLp
  have hsm : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) ∞ (torEta_FXC1 Λ R j)
      (torPi_FXC1 Λ '' ellDom_FXC1 Λ (torLift_FXC1 Λ j)) := by
    have h := (contMDiffOn_ell_FXC1 Λ (torLift_FXC1 Λ j))
    exact ((contDiff_const_smul R⁻¹).contMDiff :
      ContMDiff 𝓘(ℝ, ℝ²) 𝓘(ℝ, ℝ²) ∞ fun v : ℝ² => R⁻¹ • v).comp_contMDiffOn h
  refine hsm.mono fun q hq => ?_
  refine mem_image_ellDom_of_dist_lt_FXC1 Λ (torLift_FXC1 Λ j) q (r := 200 * R) (by nlinarith) ?_
  have h2 : R⁻¹ * dist q j < 200 := hq
  rw [dist_comm, torPi_torLift_FXC1]
  rw [inv_mul_lt_iff₀ hR] at h2
  linarith

include hR hβ2 hβ2s hLp in
/-- Two-sided distance bound for the normalized coordinate on the physical ball `B(j, 200 R)`. -/
theorem torEta_dist_bounds_FXC1 (j q q' : Tor_FXC1 Λ) (hq : dist q j < 200 * R)
    (hq' : dist q' j < 200 * R) :
    ‖torEta_FXC1 Λ R j q - torEta_FXC1 Λ R j q'‖ ≤ R⁻¹ * dist q q' ∧
      R⁻¹ * dist q q' ≤ ‖torEta_FXC1 Λ R j q - torEta_FXC1 Λ R j q'‖ + R⁻¹ * (Λ.L 2 / 2) := by
  have hLp' := torLp_ge_FXC1 Λ hR hβ2 hβ2s hLp
  obtain ⟨h1, h2⟩ := ell_dist_bounds_FXC1 Λ (torLift_FXC1 Λ j) q q' (r := 200 * R) (by nlinarith)
    (by rw [torPi_torLift_FXC1, dist_comm]; exact hq)
    (by rw [torPi_torLift_FXC1, dist_comm]; exact hq')
  have hRi := inv_pos.mpr hR
  have hn : ‖torEta_FXC1 Λ R j q - torEta_FXC1 Λ R j q'‖ =
      R⁻¹ * ‖ell_FXC1 Λ (torLift_FXC1 Λ j) q - ell_FXC1 Λ (torLift_FXC1 Λ j) q'‖ := by
    rw [torEta_FXC1, torEta_FXC1, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hRi]
  rw [hn]
  exact ⟨mul_le_mul_of_nonneg_left h1 hRi.le, by nlinarith⟩

include hR hβ2 hβ2s hLp in
/-- The normalized coordinate is a submersion on `B(j, 200 R)`. -/
theorem surjective_mfderiv_torEta_FXC1 (j q : Tor_FXC1 Λ) (hq : dist q j < 200 * R) :
    Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (torEta_FXC1 Λ R j) q) := by
  have hLp' := torLp_ge_FXC1 Λ hR hβ2 hβ2s hLp
  obtain ⟨y, rfl, hy⟩ := exists_lift_of_dist_lt_FXC1 Λ (torLift_FXC1 Λ j) q (r := 200 * R)
    (by rw [torPi_torLift_FXC1, dist_comm]; exact hq)
  have hmem : y ∈ ellDom_FXC1 Λ (torLift_FXC1 Λ j) := by
    change ‖planeL_FXC1 (y - torLift_FXC1 Λ j)‖ < _
    rw [norm_sub_rev] at hy
    nlinarith [norm_planeL_le_FXC1 (y - torLift_FXC1 Λ j)]
  have hell := surjective_mfderiv_ell_FXC1 Λ (torLift_FXC1 Λ j) hmem
  have hdiff : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (ell_FXC1 Λ (torLift_FXC1 Λ j))
      (torPi_FXC1 Λ y) :=
    ((contMDiffOn_ell_FXC1 Λ (torLift_FXC1 Λ j)).contMDiffAt
      ((isOpen_image_ellDom_FXC1 Λ (torLift_FXC1 Λ j)).mem_nhds ⟨y, hmem, rfl⟩)).mdifferentiableAt
      (by decide)
  have hL : MDifferentiableAt 𝓘(ℝ, ℝ²) 𝓘(ℝ, ℝ²) (fun v : ℝ² => R⁻¹ • v)
      (ell_FXC1 Λ (torLift_FXC1 Λ j) (torPi_FXC1 Λ y)) :=
    ((contDiff_const_smul R⁻¹ : ContDiff ℝ ∞ fun v : ℝ² => R⁻¹ • v).contMDiff.mdifferentiableAt
      (by simp))
  have hcomp := mfderiv_comp (torPi_FXC1 Λ y) hL hdiff
  have hLd : mfderiv 𝓘(ℝ, ℝ²) 𝓘(ℝ, ℝ²) (fun v : ℝ² => R⁻¹ • v)
      (ell_FXC1 Λ (torLift_FXC1 Λ j) (torPi_FXC1 Λ y)) =
      (R⁻¹ • ContinuousLinearMap.id ℝ ℝ² : ℝ² →L[ℝ] ℝ²) := by
    rw [mfderiv_eq_fderiv]
    exact ((hasFDerivAt_id (ell_FXC1 Λ (torLift_FXC1 Λ j) (torPi_FXC1 Λ y))).const_smul R⁻¹).fderiv
  have hη : torEta_FXC1 Λ R j =
      (fun v : ℝ² => R⁻¹ • v) ∘ ell_FXC1 Λ (torLift_FXC1 Λ j) := rfl
  rw [hη, hcomp, hLd]
  intro w
  let w' : ℝ² := w
  obtain ⟨u, hu⟩ := hell (R • w')
  refine ⟨u, ?_⟩
  have h3 : R⁻¹ • (R • w') = w' := by rw [smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
  change R⁻¹ • mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (ell_FXC1 Λ (torLift_FXC1 Λ j)) (torPi_FXC1 Λ y) u = w'
  rw [hu]
  exact h3

include hR hβ2s hL2 in
/-- `R⁻¹ (L₂/2) ≤ 10⁻⁷`: the thin circle direction is negligible at the normalized scale. -/
theorem torEps_le_FXC1 : R⁻¹ * (Λ.L 2 / 2) ≤ 1 / 10 ^ 7 := by
  have hRi := inv_pos.mpr hR
  have h1 : R⁻¹ * (Λ.L 2 / 2) ≤ R⁻¹ * (R * β 2 / 2) := by
    apply mul_le_mul_of_nonneg_left _ hRi.le
    linarith
  have h2 : R⁻¹ * (R * β 2 / 2) = β 2 / 2 := by field_simp
  linarith

include hR hβ2 hβ2s hLp in
/-- The normalized coordinate is `1`-Lipschitz (hence `2`-Lipschitz) on `B(j, 200)`. -/
theorem torEta_dist_le_FXC1 (j q q' : Tor_FXC1 Λ) (hq : dist q j < 200 * R)
    (hq' : dist q' j < 200 * R) :
    dist (torEta_FXC1 Λ R j q) (torEta_FXC1 Λ R j q') ≤ 2 * (R⁻¹ * dist q q') := by
  have h := (torEta_dist_bounds_FXC1 Λ hR hβ2 hβ2s hLp j q q' hq hq').1
  rw [dist_eq_norm]
  have : 0 ≤ R⁻¹ * dist q q' := mul_nonneg (inv_pos.mpr hR).le dist_nonneg
  linarith

include hR in
/-- The rescaled ball `B(j, r)` is the physical ball `B(j, r R)`. -/
theorem torRescaledBall_FXC1 {x j : Tor_FXC1 Λ} {r : ℝ}
    (h : @dist _ ((torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)).toDist x j < r) :
    dist x j < r * R := by
  have h2 : R⁻¹ * dist x j < r := h
  rw [inv_mul_lt_iff₀ hR] at h2
  linarith

include hR hβ2 hβ2s hLp in
theorem torEta_lipschitz_FXC1 (j x y : Tor_FXC1 Λ)
    (hx : @dist _ ((torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)).toDist x j < 200)
    (hy : @dist _ ((torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)).toDist y j < 200) :
    dist (torEta_FXC1 Λ R j x) (torEta_FXC1 Λ R j y) ≤
      2 * @dist _ ((torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)).toDist x y := by
  have h := torEta_dist_le_FXC1 Λ hR hβ2 hβ2s hLp j x y
    (by simpa using torRescaledBall_FXC1 Λ hR hx)
    (by simpa using torRescaledBall_FXC1 Λ hR hy)
  exact h

include hR hβ2 hβ2s hL2 hLp in
theorem torEta_enclosure_FXC1 (j x : Tor_FXC1 Λ) {a : ℝ}
    (hx : @dist _ ((torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)).toDist x j < 200)
    (h : ‖torEta_FXC1 Λ R j x‖ < a) :
    @dist _ ((torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)).toDist x j < a + 1 / 10 ^ 7 := by
  have hb := (torEta_dist_bounds_FXC1 Λ hR hβ2 hβ2s hLp j x j
    (by simpa using torRescaledBall_FXC1 Λ hR hx)
    (by
      rw [@dist_self _ (torMS_FXC1 Λ).toPseudoMetricSpace j]
      positivity)).2
  rw [torEta_center_FXC1, sub_zero] at hb
  have hε := torEps_le_FXC1 Λ hR hβ2s hL2
  change R⁻¹ * dist x j < a + 1 / 10 ^ 7
  linarith

include hR hβ2 hβ2s hL2 hLp in
/-- **The LC83 circle chart of the flat torus at `j`** (normalized scale `R⁻¹ d`): the LC83
producer applied to the plane chart `η_j = R⁻¹ ell(j̃)`. -/
def torChart_FXC1 (j : Tor_FXC1 Λ) :
    letI := (torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)
    CircleChart 𝓘(ℝ, E3) (Tor_FXC1 Λ) := by
  have hRi := inv_pos.mpr hR
  have hMc : CompleteSpace (Tor_FXC1 Λ) := complete_of_compact
  have hrank : ∀ x : Tor_FXC1 Λ,
      @dist _ ((torMS_FXC1 Λ).rescale R⁻¹ hRi).toDist x j < 200 →
      Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (torEta_FXC1 Λ R j) x) := fun x hx =>
    surjective_mfderiv_torEta_FXC1 Λ hR hβ2 hβ2s hLp j x
      (by simpa using torRescaledBall_FXC1 Λ hR hx)
  letI := (torMS_FXC1 Λ).rescale R⁻¹ hRi
  letI := radialScaledBundle (torMetric_FXC1 Λ) R⁻¹ hRi
  letI : IsContinuousRiemannianBundle E3 (fun x : Tor_FXC1 Λ => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous (torMetric_FXC1 Λ) R⁻¹ hRi
  letI : IsRiemannianManifold 𝓘(ℝ, E3) (Tor_FXC1 Λ) :=
    radialScaledManifold (m := torMS_FXC1 Λ) (torMetric_FXC1 Λ) (torMS_hmetric_FXC1 Λ) R⁻¹ hRi
  letI : CompleteSpace (Tor_FXC1 Λ) :=
    ((torMS_FXC1 Λ).rescale_completeSpace_iff R⁻¹ hRi).mpr hMc
  let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) (Tor_FXC1 Λ) :=
    scaleMetric (R⁻¹ ^ 2) (pow_pos hRi 2) (torMetric_FXC1 Λ)
  have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := Tor_FXC1 Λ) gR :=
    isMetricNorm_of_riemannianBundle gR
  exact CircleChart.ofLocalModel gR hnR (η := torEta_FXC1 Λ R j) (p := j)
    (contMDiffOn_torEta_FXC1 Λ hR hβ2 hβ2s hLp j) (fun x hx => hrank x hx)
    (LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
      have h := torEta_lipschitz_FXC1 Λ hR hβ2 hβ2s hLp j x y hx hy
      exact_mod_cast h)
    (torEta_center_FXC1 Λ R j)
    (fun x hx hlt => by
      have h := torEta_enclosure_FXC1 Λ hR hβ2 hβ2s hL2 hLp j x hx (a := 100) hlt
      exact lt_trans h (by norm_num))
    (fun x hx h0 => by
      have h := torEta_enclosure_FXC1 Λ hR hβ2 hβ2s hL2 hLp j x hx (a := 1)
        (by rw [h0, norm_zero]; norm_num)
      exact lt_trans h (by norm_num))

end Chart

end DifferentialGeometry.Geometry.Collapse
