import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusAdaptedLines
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPackets
import DifferentialGeometry.Geometry.Collapse.SublevelCore.ScaledMinimizingDirections

/-!
# The geodesic test of the circle adapted centre of the flat torus (S-FIXTURE-C1b, F1, G4 file 2)

The test field of `CircleAdaptedCentre` at normalized scale `(ρ(j)⁻¹ d, ρ(j)⁻² g)` for the flat
torus at the constant scale `R`: for `x ∈ B(j, 200)`, a unit `gR`-vector `w` at `x` whose intrinsic
geodesic reaches `z ∈ B(j, 201·10⁴)` at time `d(x, z)`, the derivative of the plane coordinate
`η_j` at `x` in the direction `w` equals the chord quotient of `η_j` exactly.

Proof (D75-8, three transport exits): lift `x = π x̃` in the slab of the lift of `j`, put
`v = (dπ)⁻¹ w` (`‖v‖ = R` because `w` is `gR`-unit); the projected line `t ↦ π(x̃ + t v)` is a
geodesic of `gR` with the initial data of `w` (`isGeodesic_torPi_line_FXC1`), hence it IS the
intrinsic geodesic (`eq_intrinsicGeodesic_of_isGeodesic_scaleMetric` at `c = 1`); it stays in the
slab for the whole test time (`D < 2010200 ≪ Lp / (2R)`), where `η_j` is affine
(`torEta_line_FXC1`), so `dη(w) = R⁻¹ planeL v` and the chord equals `D · R⁻¹ planeL v`.
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

section Test

variable (Λ : TorusPeriods_FXC1) {R : ℝ} (hR : 0 < R)

include hR in
/-- A point of the rescaled ball `B(j, 200)` has a lift in the `200 R` ball of the lift of `j`. -/
theorem torWrap_lift_FXC1 {x j : Tor_FXC1 Λ}
    (h : @dist _ ((torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)).toDist x j < 200) :
    ∃ xt : E3, torPi_FXC1 Λ xt = x ∧ ‖xt - torLift_FXC1 Λ j‖ < 200 * R := by
  have h1 := torRescaledBall_FXC1 Λ hR h
  obtain ⟨xt, hxt, hxt'⟩ := exists_lift_of_dist_lt_FXC1 Λ (torLift_FXC1 Λ j) x (r := 200 * R)
    (by rw [torPi_torLift_FXC1, dist_comm]; exact h1)
  exact ⟨xt, hxt, by rwa [norm_sub_rev] at hxt'⟩

variable {β : ℕ → ℝ} (hβ2 : 0 < β 2) (hβ2s : β 2 ≤ 1 / 10 ^ 7)
  (hLp : 8 * R / β 2 ≤ planePeriod_FXC1 Λ)

include hR hβ2 hβ2s hLp in
/-- **The geodesic test at the flat torus** (the field `CircleAdaptedCentre.test`, with the plane
coordinate `η_j = torEta` and the Kleiner-Lott map `x ↦ (η_j x, ⋆)`). -/
theorem torTest_FXC1 (j : Tor_FXC1 Λ) {γ : ℝ} (hγ : 0 < γ) :
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
    ∀ x ∈ ball j 200, ∀ z ∈ ball j (201 * 10000), 201 < dist x z →
      ∀ w : TangentSpace 𝓘(ℝ, E3) x, gR.inner x w w = 1 →
      intrinsicGeodesic gR hnR x w (dist x z) = z →
      ‖mvfderiv (I := 𝓘(ℝ, E3)) (torEta_FXC1 Λ R j) x w -
        (dist x z)⁻¹ • (torEta_FXC1 Λ R j z - torEta_FXC1 Λ R j x)‖ < γ := by
  intro hMc gR hnR x hx z hz hxz w hw hgeo
  let _ := (torMS_FXC1 Λ).rescale R⁻¹ (inv_pos.mpr hR)
  let _ := radialScaledBundle (torMetric_FXC1 Λ) R⁻¹ (inv_pos.mpr hR)
  let _ : IsContinuousRiemannianBundle E3 (fun x : Tor_FXC1 Λ => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous (torMetric_FXC1 Λ) R⁻¹ (inv_pos.mpr hR)
  let _ : IsRiemannianManifold 𝓘(ℝ, E3) (Tor_FXC1 Λ) :=
    radialScaledManifold (m := torMS_FXC1 Λ) (torMetric_FXC1 Λ) (torMS_hmetric_FXC1 Λ) R⁻¹
      (inv_pos.mpr hR)
  let _ : CompleteSpace (Tor_FXC1 Λ) :=
    ((torMS_FXC1 Λ).rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
  obtain ⟨xt, rfl, hxt⟩ := torWrap_lift_FXC1 Λ hR (mem_ball.mp hx)
  have hloc := torPi_isLocalDiffeomorph_FXC1 Λ
  let hD := hloc.mfderivToContinuousLinearEquiv (n := ∞) (by decide : (∞ : WithTop ℕ∞) ≠ 0) xt
  have hcoe : (hD : TangentSpace 𝓘(ℝ, E3) xt →L[ℝ] TangentSpace 𝓘(ℝ, E3) (torPi_FXC1 Λ xt)) =
      mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) xt :=
    hloc.mfderivToContinuousLinearEquiv_coe (n := ∞) (by decide : (∞ : WithTop ℕ∞) ≠ 0) xt
  let v : E3 := hD.symm w
  have hwv : mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) xt v = w := by
    rw [← hcoe]
    exact hD.apply_symm_apply w
  -- the velocity has Euclidean norm `R`
  have hnorm : ‖v‖ = R := by
    have h1 := localPullMetric_inner (torMetric_FXC1 Λ) (torPi_FXC1 Λ) hloc xt v v
    rw [torMetric_localPull_FXC1, hwv, euclideanMetric_inner] at h1
    have h2 : gR.inner (torPi_FXC1 Λ xt) w w = (R⁻¹ ^ 2) *
        (torMetric_FXC1 Λ).inner (torPi_FXC1 Λ xt) w w := scaleMetric_inner _ _ _ _ _ _
    have h1' : inner ℝ v v = (torMetric_FXC1 Λ).inner (torPi_FXC1 Λ xt) w w := h1
    rw [h2, ← h1', real_inner_self_eq_norm_sq] at hw
    have hw' : R⁻¹ ^ 2 * ‖v‖ ^ 2 = 1 := hw
    have h3 : ‖v‖ ^ 2 = R ^ 2 := by
      have : R ^ 2 * (R⁻¹ ^ 2 * ‖v‖ ^ 2) = R ^ 2 * 1 := by rw [hw']
      field_simp at this
      linarith
    exact (sq_eq_sq₀ (norm_nonneg _) hR.le).mp h3
  -- the projected line is the intrinsic geodesic
  have hΓ : IsGeodesic (I := 𝓘(ℝ, E3)) (scaleMetric 1 one_pos gR)
      (fun t : ℝ => torPi_FXC1 Λ (xt + t • v)) :=
    (isGeodesic_scaleMetric_iff 1 one_pos).mpr
      (isGeodesic_torPi_line_FXC1 Λ (c := R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) xt v)
  have hcont : Continuous (fun t : ℝ => torPi_FXC1 Λ (xt + t • v)) :=
    (contMDiff_torPi_FXC1 Λ).continuous.comp (by fun_prop)
  have h0 : torPi_FXC1 Λ (xt + (0 : ℝ) • v) = torPi_FXC1 Λ xt := by simp
  have hder : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E3) (fun t : ℝ => torPi_FXC1 Λ (xt + t • v)) 0 (1 : ℝ) :
      E3) = (w : E3) := by
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
    have h5 : (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) xt v : E3) = (w : E3) :=
      congrArg (fun a : TangentSpace 𝓘(ℝ, E3) (torPi_FXC1 Λ xt) => (a : E3)) hwv
    change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E3) (torPi_FXC1 Λ ∘ γ') 0 (1 : ℝ) : E3) = _
    rw [h3, h4, hγder, h5]
  have hGeo := eq_intrinsicGeodesic_of_isGeodesic_scaleMetric gR hnR one_pos hΓ hcont h0 hder
  have hgeo' : torPi_FXC1 Λ (xt + (dist (torPi_FXC1 Λ xt) z) • v) = z :=
    (congr_fun hGeo (dist (torPi_FXC1 Λ xt) z)).trans hgeo
  have hDnn : 0 ≤ dist (torPi_FXC1 Λ xt) z := dist_nonneg
  have hDlt : dist (torPi_FXC1 Λ xt) z < 2010200 := by
    have h1 : dist (torPi_FXC1 Λ xt) j < 200 := mem_ball.mp hx
    have h2 : dist z j < 201 * 10000 := mem_ball.mp hz
    have h3 := dist_triangle_right (torPi_FXC1 Λ xt) z j
    linarith
  obtain ⟨D, hdD⟩ : ∃ D, D = dist (torPi_FXC1 Λ xt) z := ⟨_, rfl⟩
  rw [← hdD] at hDnn hDlt hxz hgeo' ⊢
  have key := torEta_line_FXC1 Λ hR hβ2 hβ2s hLp j xt v hDnn hxt hnorm hDlt
  have hmf := mfderiv_torEta_FXC1 Λ hR hβ2 hβ2s hLp j xt hxt v
  rw [hwv] at hmf
  rw [← hgeo', key]
  have hmv : mvfderiv (I := 𝓘(ℝ, E3)) (torEta_FXC1 Λ R j) (torPi_FXC1 Λ xt) w =
      R⁻¹ • planeL_FXC1 v := hmf
  rw [hmv, smul_smul, inv_mul_cancel₀ (by linarith), one_smul, sub_self, norm_zero]
  exact hγ

end Test

end DifferentialGeometry.Geometry.Collapse
