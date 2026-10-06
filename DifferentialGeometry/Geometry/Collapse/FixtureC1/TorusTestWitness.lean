import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusAdaptedTest

/-!
# The geodesic test of the flat torus is NOT vacuous (O-FIXTURE-C1, G10 file 1)

S-FIXTURE-C1b's `torTest_FXC1` (the `test` field of the circle adapted centre) quantifies over
`x ∈ B(j, 200)`, `z ∈ B(j, 201·10⁴)` with `201 < d(x, z)` and a unit `gR`-vector `w` at `x` whose
intrinsic geodesic reaches `z` at time `d(x, z)` (all at the normalized scale `R⁻¹ d`). Here these
premises are met by an explicit triple (`torTest_witness_OFC`, for every centre `j` once the plane
period is at least `404 R`): `x = π(x̃)` with `x̃` a lift of `j`, `w = dπ(R e₁)`,
`z = π(x̃ + 202 R e₁)`;

* `torPi_line_dist_OFC`: `d(π x̃, π(x̃ + D R e₁)) = D R` for `D R ≤ L_p / 2` (the covering map is
  `1`-Lipschitz; no planar shortcut);
* `torIntrinsic_line_OFC`: the projected line `t ↦ π(x̃ + t v)` IS the intrinsic `gR`-geodesic of
  `dπ(v)` (geodesic by local isometry, same initial data);
* so `d_R(x, z) = 202`, `gR(w, w) = 1` and the intrinsic geodesic of `w` reaches `z` at time `202`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] torMS_FXC1

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The first planar unit vector `e₁` of `ℝ³`. -/
def torE0_OFC : E3 := EuclideanSpace.single 0 1

theorem norm_torE0_OFC : ‖torE0_OFC‖ = 1 := by
  simp [torE0_OFC]

theorem norm_planeL_torE0_OFC : ‖planeL_FXC1 torE0_OFC‖ = 1 := by
  have h : planeL_FXC1 torE0_OFC = EuclideanSpace.single 0 1 := by
    ext i
    fin_cases i <;> simp [torE0_OFC]
  rw [h]
  simp

section Witness

variable (Λ : TorusPeriods_FXC1) {R : ℝ} (hR : 0 < R)

include hR in
/-- **Exact distance along a planar line**: `d(π x̃, π(x̃ + D R e₁)) = D R` when `D R ≤ L_p / 2`. -/
theorem torPi_line_dist_OFC (xt : E3) {D : ℝ} (hD : 0 ≤ D)
    (hDL : D * R ≤ planePeriod_FXC1 Λ / 2) :
    dist (torPi_FXC1 Λ xt) (torPi_FXC1 Λ (xt + D • (R • torE0_OFC))) = D * R := by
  have hDR : 0 ≤ D * R := mul_nonneg hD hR.le
  have hn : ‖xt - (xt + D • (R • torE0_OFC))‖ = D * R := by
    rw [sub_add_cancel_left, norm_neg, norm_smul, norm_smul, norm_torE0_OFC, Real.norm_of_nonneg hD,
      Real.norm_of_nonneg hR.le, mul_one]
  have hp : ‖planeL_FXC1 (xt - (xt + D • (R • torE0_OFC)))‖ = D * R := by
    rw [sub_add_cancel_left, map_neg, norm_neg, map_smul, map_smul, norm_smul, norm_smul,
      norm_planeL_torE0_OFC, Real.norm_of_nonneg hD, Real.norm_of_nonneg hR.le, mul_one]
  refine le_antisymm ?_ ?_
  · refine dist_le_of_edist_le_FXC1 Λ _ _ _ hDR ?_
    rw [← hn]
    exact edist_torPi_le_FXC1 Λ _ _
  · rw [← hp]
    exact norm_planeL_le_dist_torPi_FXC1 Λ _ _ (by rw [hp]; exact hDL)

include hR in
/-- **The projected line is the intrinsic geodesic** of `dπ(v)` for the normalized metric `gR`. -/
theorem torIntrinsic_line_OFC (xt v : E3) :
    let hMc : CompleteSpace (Tor_FXC1 Λ) := complete_of_compact
    letI := (torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)
    letI := radialScaledBundle (torMetric_FXC1 Λ) R⁻¹ (inv_pos.mpr hR)
    letI : IsContinuousRiemannianBundle E3 (fun x : Tor_FXC1 Λ => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous (torMetric_FXC1 Λ) R⁻¹ (inv_pos.mpr hR)
    letI : IsRiemannianManifold 𝓘(ℝ, E3) (Tor_FXC1 Λ) :=
      radialScaledManifold (m := torMS_FXC1 Λ) (torMetric_FXC1 Λ) (torMS_hmetric_FXC1 Λ) R⁻¹
        (inv_pos.mpr hR)
    letI : CompleteSpace (Tor_FXC1 Λ) :=
      ((torMS_FXC1 Λ).rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
    let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) (Tor_FXC1 Λ) :=
      scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) (torMetric_FXC1 Λ)
    have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := Tor_FXC1 Λ) gR :=
      isMetricNorm_of_riemannianBundle gR
    (fun t : ℝ => torPi_FXC1 Λ (xt + t • v)) =
      intrinsicGeodesic gR hnR (torPi_FXC1 Λ xt)
        (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) xt v) := by
  intro hMc gR hnR
  let _ := (torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)
  let _ := radialScaledBundle (torMetric_FXC1 Λ) R⁻¹ (inv_pos.mpr hR)
  let _ : IsContinuousRiemannianBundle E3 (fun x : Tor_FXC1 Λ => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous (torMetric_FXC1 Λ) R⁻¹ (inv_pos.mpr hR)
  let _ : IsRiemannianManifold 𝓘(ℝ, E3) (Tor_FXC1 Λ) :=
    radialScaledManifold (m := torMS_FXC1 Λ) (torMetric_FXC1 Λ) (torMS_hmetric_FXC1 Λ) R⁻¹
      (inv_pos.mpr hR)
  let _ : CompleteSpace (Tor_FXC1 Λ) :=
    ((torMS_FXC1 Λ).rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
  have hΓ : IsGeodesic (I := 𝓘(ℝ, E3)) (scaleMetric 1 one_pos gR)
      (fun t : ℝ => torPi_FXC1 Λ (xt + t • v)) :=
    (isGeodesic_scaleMetric_iff 1 one_pos).mpr
      (isGeodesic_torPi_line_FXC1 Λ (c := R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) xt v)
  have hcont : Continuous (fun t : ℝ => torPi_FXC1 Λ (xt + t • v)) :=
    (contMDiff_torPi_FXC1 Λ).continuous.comp (by fun_prop)
  have h0 : torPi_FXC1 Λ (xt + (0 : ℝ) • v) = torPi_FXC1 Λ xt := by simp
  have hder : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E3) (fun t : ℝ => torPi_FXC1 Λ (xt + t • v)) 0 (1 : ℝ) :
      E3) = (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) xt v : E3) := by
    let γ' : ℝ → E3 := fun t => xt + t • v
    have hγd : HasDerivAt γ' v 0 := by
      have h := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add xt
      rwa [one_smul] at h
    have hγm : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E3) γ' 0 :=
      hγd.differentiableAt.mdifferentiableAt
    have hγ0 : γ' 0 = xt := by simp [γ']
    have hpm : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) xt :=
      ((contMDiff_torPi_FXC1 Λ) xt).mdifferentiableAt (by simp)
    have hcomp := mfderiv_comp_of_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E3)) (I'' := 𝓘(ℝ, E3))
      hpm hγm hγ0
    have hγder : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E3) γ' 0 (1 : ℝ) : E3) = v := by
      rw [mfderiv_eq_fderiv]
      change (fderiv ℝ γ' 0) 1 = v
      rw [hγd.hasFDerivAt.fderiv]
      simp
    have hpt : ∀ p q : E3, p = q → ∀ u : E3,
        (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) p u : E3) =
          (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) q u : E3) := by
      intro p q h u
      subst h
      rfl
    have h2 := DFunLike.congr_fun hcomp (1 : ℝ)
    have h3 : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E3) (torPi_FXC1 Λ ∘ γ') 0 (1 : ℝ) : E3) =
        (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) (γ' 0)
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E3) γ' 0 (1 : ℝ)) : E3) :=
      congrArg (fun a : TangentSpace 𝓘(ℝ, E3) (torPi_FXC1 Λ (γ' 0)) => (a : E3)) h2
    have h4 := hpt (γ' 0) xt hγ0 (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E3) γ' 0 (1 : ℝ))
    change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E3) (torPi_FXC1 Λ ∘ γ') 0 (1 : ℝ) : E3) = _
    rw [h3, h4, hγder]
  exact eq_intrinsicGeodesic_of_isGeodesic_scaleMetric gR hnR one_pos hΓ hcont h0 hder

include hR in
/-- **A witness of the premises of the geodesic test** at every centre `j` (plane period
`≥ 404 R`): `x = π(x̃)`, `w = dπ(R e₁)`, `z = π(x̃ + 202 R e₁)` with `d_R(x, z) = 202`. -/
theorem torTest_witness_OFC (j : Tor_FXC1 Λ) (hLp : 404 * R ≤ planePeriod_FXC1 Λ) :
    let hMc : CompleteSpace (Tor_FXC1 Λ) := complete_of_compact
    letI := (torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)
    letI := radialScaledBundle (torMetric_FXC1 Λ) R⁻¹ (inv_pos.mpr hR)
    letI : IsContinuousRiemannianBundle E3 (fun x : Tor_FXC1 Λ => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous (torMetric_FXC1 Λ) R⁻¹ (inv_pos.mpr hR)
    letI : IsRiemannianManifold 𝓘(ℝ, E3) (Tor_FXC1 Λ) :=
      radialScaledManifold (m := torMS_FXC1 Λ) (torMetric_FXC1 Λ) (torMS_hmetric_FXC1 Λ) R⁻¹
        (inv_pos.mpr hR)
    letI : CompleteSpace (Tor_FXC1 Λ) :=
      ((torMS_FXC1 Λ).rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
    let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) (Tor_FXC1 Λ) :=
      scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) (torMetric_FXC1 Λ)
    have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := Tor_FXC1 Λ) gR :=
      isMetricNorm_of_riemannianBundle gR
    ∃ x ∈ ball j 200, ∃ z ∈ ball j (201 * 10000), 201 < dist x z ∧
      ∃ w : TangentSpace 𝓘(ℝ, E3) x, gR.inner x w w = 1 ∧
        intrinsicGeodesic gR hnR x w (dist x z) = z := by
  intro hMc gR hnR
  obtain ⟨xt, hxj⟩ := torPi_surjective_FXC1 Λ j
  have hgeo := torIntrinsic_line_OFC Λ hR xt (R • torE0_OFC)
  have hd := torPi_line_dist_OFC Λ hR xt (D := 202) (by norm_num) (by linarith)
  have hv : ‖R • torE0_OFC‖ = R := by
    rw [norm_smul, norm_torE0_OFC, Real.norm_of_nonneg hR.le, mul_one]
  have hinner : gR.inner (torPi_FXC1 Λ xt)
      (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) xt (R • torE0_OFC))
      (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) xt (R • torE0_OFC)) = 1 := by
    have h1 := localPullMetric_inner (torMetric_FXC1 Λ) (torPi_FXC1 Λ)
      (torPi_isLocalDiffeomorph_FXC1 Λ) xt (R • torE0_OFC) (R • torE0_OFC)
    rw [torMetric_localPull_FXC1] at h1
    have h2 : gR.inner (torPi_FXC1 Λ xt)
        (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) xt (R • torE0_OFC))
        (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) xt (R • torE0_OFC)) =
        (R⁻¹ ^ 2) * (torMetric_FXC1 Λ).inner (torPi_FXC1 Λ xt)
          (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) xt (R • torE0_OFC))
          (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) xt (R • torE0_OFC)) :=
      scaleMetric_inner _ _ _ _ _ _
    have h1' : inner ℝ (R • torE0_OFC) (R • torE0_OFC) =
        (torMetric_FXC1 Λ).inner (torPi_FXC1 Λ xt)
          (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) xt (R • torE0_OFC))
          (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) xt (R • torE0_OFC)) := h1
    rw [h2, ← h1', real_inner_self_eq_norm_sq, hv]
    field_simp
  let _ := (torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)
  let _ := radialScaledBundle (torMetric_FXC1 Λ) R⁻¹ (inv_pos.mpr hR)
  let _ : IsContinuousRiemannianBundle E3 (fun x : Tor_FXC1 Λ => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous (torMetric_FXC1 Λ) R⁻¹ (inv_pos.mpr hR)
  let _ : IsRiemannianManifold 𝓘(ℝ, E3) (Tor_FXC1 Λ) :=
    radialScaledManifold (m := torMS_FXC1 Λ) (torMetric_FXC1 Λ) (torMS_hmetric_FXC1 Λ) R⁻¹
      (inv_pos.mpr hR)
  let _ : CompleteSpace (Tor_FXC1 Λ) :=
    ((torMS_FXC1 Λ).rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
  have hdR : @dist _ ((torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)).toDist
      (torPi_FXC1 Λ xt) (torPi_FXC1 Λ (xt + (202 : ℝ) • (R • torE0_OFC))) = 202 := by
    change R⁻¹ * @dist _ (torMS_FXC1 Λ).toDist _ _ = 202
    rw [hd]
    field_simp
  have hgeo2 : (fun t : ℝ => torPi_FXC1 Λ (xt + t • (R • torE0_OFC))) =
      intrinsicGeodesic gR hnR (torPi_FXC1 Λ xt)
        (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) xt (R • torE0_OFC)) := hgeo
  refine ⟨torPi_FXC1 Λ xt, ?_, torPi_FXC1 Λ (xt + (202 : ℝ) • (R • torE0_OFC)), ?_, ?_,
    mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) xt (R • torE0_OFC), hinner, ?_⟩
  · change R⁻¹ * @dist _ (torMS_FXC1 Λ).toDist (torPi_FXC1 Λ xt) j < 200
    rw [hxj, @dist_self _ (torMS_FXC1 Λ).toPseudoMetricSpace, mul_zero]
    norm_num
  · change R⁻¹ * @dist _ (torMS_FXC1 Λ).toDist
      (torPi_FXC1 Λ (xt + (202 : ℝ) • (R • torE0_OFC))) j < 201 * 10000
    rw [← hxj, @dist_comm _ (torMS_FXC1 Λ).toPseudoMetricSpace, hd]
    field_simp
    norm_num
  · rw [hdR]
    norm_num
  · rw [hdR, ← hgeo2]

end Witness

end DifferentialGeometry.Geometry.Collapse
