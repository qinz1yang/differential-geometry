import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsZeroApplications
import DifferentialGeometry.Geometry.Collapse.SublevelCore.ScaledMinimizingDirections
import DifferentialGeometry.Geometry.Fibration.RiemannianDerivativeTools
import DifferentialGeometry.Topology.Ehresmann.SideBoundaryInterval

/-!
# LC73's adapted zero coordinate in physical form (the double-rescale context of `zero_adapted`)

Blueprint `master207B.tex`, TCP03's zero block (B:5430: "LC73 at EVERY `x ∈ D_i` has the same raw
distance difference, and the stated radial quality puts this endpoint in its original
all-direction test ball"), and SGP03 / EGP04's zero blocks. The field `zero_adapted` of
`LocalChartPacketsZ` is stated in the DOUBLE rescale context `((X, R⁻¹ d), λ ·)`,
`radialScaledBundle (R⁻² g) λ`, `h = λ² R⁻² g`; this module transports it to physical form.

* `intrinsicGeodesic_radialScaled_eq_c_KA5`: the intrinsic geodesics of `c² g` (instances
  `m.rescale c`, `radialScaledBundle g c`, …) are those of `g` — the `c`-form of
  `intrinsicGeodesic_radialScaled_eq` (which is stated with `R⁻¹`), by transport along
  `(c⁻¹)⁻¹ = c`.
* `intrinsicGeodesic_radialScaled_hit_c_KA5`: a geodesic of `g` reaching `q` at time `d(p, q)`
  gives the geodesic of `c² g` with velocity `c⁻¹ v` reaching `q` at the rescaled time.
* `zero_radial_mdifferentiableAt_KA5`: the original radial function is differentiable at every
  point of the closed shell (LC30, `radial_spec`).
* `zero_adapted_test_phys_KA5`: LC73's test at a shell point `x`, ratio `λ = R/r`
  (`Λz ≤ R/r`), along a physical minimizing direction `w₀` toward `y` with
  `r < d(x, y)`, `ζ d(x, y) < r`: `|R dη₀(w₀) − (d(k, y) − d(k, x))/d(x, y)| < ζ`.
* `zero_adapted_deriv_bound_KA5`: LC73's Lipschitz clause gives `|R dη₀(v)| ≤ (1 + ζ)√(g(v, v))`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section CForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [hM : CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **The intrinsic geodesics of `c² g` are those of `g`** (`c`-form of
`intrinsicGeodesic_radialScaled_eq`): with the instances `m.rescale c`, `radialScaledBundle g c`,
`radialScaledContinuous g c`, `radialScaledManifold g c`, the intrinsic geodesic of
`scaleMetric (c²) g` with initial velocity `v` is the intrinsic geodesic of `g`. -/
theorem intrinsicGeodesic_radialScaled_eq_c_KA5 (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {c : ℝ} (hc : 0 < c) (p : M)
    (v : TangentSpace I p) :
    (have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
    letI := m.rescale c hc
    letI := radialScaledBundle g c hc
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      radialScaledContinuous g c hc
    letI : IsRiemannianManifold I M := radialScaledManifold (m := m) g hmetric c hc
    letI : CompleteSpace M := (m.rescale_completeSpace_iff c hc).mpr hM
    let gc : SmoothRiemannianMetric I M := scaleMetric (c ^ 2) (pow_pos hc 2) g
    have hnc : IsMetricNorm (I := I) (M := M) gc := isMetricNorm_of_riemannianBundle gc
    intrinsicGeodesic (I := I) gc hnc p v) =
      intrinsicGeodesic (I := I) g hEnorm p v := by
  have key : ∀ (a : ℝ) (ha : 0 < a), a = c →
      (have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
      letI := m.rescale a ha
      letI := radialScaledBundle g a ha
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        radialScaledContinuous g a ha
      letI : IsRiemannianManifold I M := radialScaledManifold (m := m) g hmetric a ha
      letI : CompleteSpace M := (m.rescale_completeSpace_iff a ha).mpr hM
      let ga : SmoothRiemannianMetric I M := scaleMetric (a ^ 2) (pow_pos ha 2) g
      have hna : IsMetricNorm (I := I) (M := M) ga := isMetricNorm_of_riemannianBundle ga
      intrinsicGeodesic (I := I) ga hna p v) =
        intrinsicGeodesic (I := I) g hEnorm p v →
      (have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
      letI := m.rescale c hc
      letI := radialScaledBundle g c hc
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        radialScaledContinuous g c hc
      letI : IsRiemannianManifold I M := radialScaledManifold (m := m) g hmetric c hc
      letI : CompleteSpace M := (m.rescale_completeSpace_iff c hc).mpr hM
      let gc : SmoothRiemannianMetric I M := scaleMetric (c ^ 2) (pow_pos hc 2) g
      have hnc : IsMetricNorm (I := I) (M := M) gc := isMetricNorm_of_riemannianBundle gc
      intrinsicGeodesic (I := I) gc hnc p v) =
        intrinsicGeodesic (I := I) g hEnorm p v := by
    rintro a ha rfl h
    exact h
  exact key _ (inv_pos.mpr (inv_pos.mpr hc)) (inv_inv c)
    (intrinsicGeodesic_radialScaled_eq g hEnorm (inv_pos.mpr hc) p v)

/-- A geodesic of `g` with velocity `v` reaching `q` at time `d(p, q)` gives the geodesic of `c² g`
(instances `m.rescale c`, …) with velocity `c⁻¹ v` reaching `q` at the rescaled time
`c d(p, q)`. -/
theorem intrinsicGeodesic_radialScaled_hit_c_KA5 (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {c : ℝ} (hc : 0 < c) {p q : M}
    (v : TangentSpace I p) (hpq : intrinsicGeodesic (I := I) g hEnorm p v (dist p q) = q) :
    (have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
    letI := m.rescale c hc
    letI := radialScaledBundle g c hc
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      radialScaledContinuous g c hc
    letI : IsRiemannianManifold I M := radialScaledManifold (m := m) g hmetric c hc
    letI : CompleteSpace M := (m.rescale_completeSpace_iff c hc).mpr hM
    let gc : SmoothRiemannianMetric I M := scaleMetric (c ^ 2) (pow_pos hc 2) g
    have hnc : IsMetricNorm (I := I) (M := M) gc := isMetricNorm_of_riemannianBundle gc
    intrinsicGeodesic (I := I) gc hnc p (c⁻¹ • v) (dist p q)) = q := by
  have h := intrinsicGeodesic_radialScaled_eq_c_KA5 g hEnorm hc p (c⁻¹ • v)
  simp only at h ⊢
  rw [h, intrinsicGeo_smul_apply (I := I) g hEnorm p v c⁻¹, MetricSpace.rescale_dist,
    ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  exact hpq

end CForm

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Zero

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}

/-- The model metrics of `LocalChartPacketsZ`, as a named local instance. -/
local instance instMetricNZ_ZAP_KA5
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsZ`, as a named local instance. -/
local instance instChartedNZ_ZAP_KA5
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsZ`, as a named local instance. -/
local instance instMetricCZ_ZAP_KA5
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- The original radial function of a selected zero ball is differentiable at every point of the
closed shell `R/10 ≤ d(k, x) ≤ 10R` (LC30, `radial_spec`: smooth on an open neighbourhood of
`3/40 ≤ R⁻¹ d(k, ·) ≤ 11`). -/
theorem zero_radial_mdifferentiableAt_KA5
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) {k : X} (hk : k ∈ P.zero.centres) {x : X}
    (h1 : (P.zero.zero k hk).radius / 10 ≤ dist k x)
    (h2 : dist k x ≤ 10 * (P.zero.zero k hk).radius) :
    MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (P.zero.zero k hk).radial x := by
  have hR := (P.zero.zero k hk).radius_pos
  have hc := P.zero.zero_center k hk
  obtain ⟨-, ⟨O, hO, hsub, hsm⟩, -⟩ := (P.zero.zero k hk).radial_spec
  have hxO : x ∈ O := by
    apply hsub
    change 3 / 40 ≤ (P.zero.zero k hk).radius⁻¹ * dist x (P.zero.zero k hk).center ∧
      (P.zero.zero k hk).radius⁻¹ * dist x (P.zero.zero k hk).center ≤ 11
    rw [hc, dist_comm]
    constructor
    · rw [le_inv_mul_iff₀ hR]; linarith
    · rw [inv_mul_le_iff₀ hR]; linarith
  exact (hsm.contMDiffAt (hO.mem_nhds hxO)).mdifferentiableAt (by simp)

/-- **The double-rescale geodesic of LC73 is a physical one.** A geodesic of `R⁻² g` (instances
`mX.rescale R⁻¹`, `radialScaledBundle g R⁻¹`, …) with velocity `v` reaching `y` at the time
`R⁻¹ d(x, y)` gives, in the context of the field `zero_adapted` (`(mX.rescale R⁻¹).rescale λ`,
`radialScaledBundle (R⁻² g) λ`, `h = λ² R⁻² g`), the geodesic of `h` with velocity `λ⁻¹ v` reaching
`y` at the time `λ R⁻¹ d(x, y)`, for every `IsMetricNorm h`. -/
theorem zero_double_geodesic_KA5 (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) {R : ℝ}
    (hR : 0 < R) {lam : ℝ} (hlam : 0 < lam) {x y : X} (v : TangentSpace 𝓘(ℝ, E3) x)
    (h0 : let hMc : CompleteSpace X := complete_of_compact
        letI := mX.rescale R⁻¹ (inv_pos.mpr hR)
        letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
        letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
          radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
        letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
          radialScaledManifold (m := mX) g hmetric R⁻¹ (inv_pos.mpr hR)
        letI : CompleteSpace X := (mX.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
        let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
          scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
        have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR :=
          isMetricNorm_of_riemannianBundle gR
        intrinsicGeodesic gR hnR x v (dist x y) = y) :
    let mr := mX.rescale R⁻¹ (inv_pos.mpr hR)
    let gr := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
    let hmr := riemannianEDistOf_scaleMetric_inv_sq_eq_rescale (m := mX) g hmetric hR
    let := mr.rescale lam hlam
    letI := (mr.rescale_completeSpace_iff lam hlam).mpr
      ((mX.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr
        (@complete_of_compact X mX.toUniformSpace _))
    letI := radialScaledBundle gr lam hlam
    letI := radialScaledContinuous gr lam hlam
    letI := radialScaledManifold (m := mr) gr hmr lam hlam
    let h := scaleMetric (lam ^ 2) (pow_pos hlam 2) gr
    ∀ hEnorm : IsMetricNorm h, intrinsicGeodesic h hEnorm x (lam⁻¹ • v) (dist x y) = y := by
  have h1 := @intrinsicGeodesic_radialScaled_hit_c_KA5 E3 _ _ _ _ _ _ 𝓘(ℝ, E3) _ X
    (mX.rescale R⁻¹ (inv_pos.mpr hR)) _ _ _
    (radialScaledBundle (m := mX.rescale R⁻¹ (inv_pos.mpr hR)) g R⁻¹ (inv_pos.mpr hR))
    (radialScaledManifold (m := mX) g hmetric R⁻¹ (inv_pos.mpr hR))
    ((mX.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr
      (@complete_of_compact X mX.toUniformSpace _))
    (radialScaledContinuous (m := mX.rescale R⁻¹ (inv_pos.mpr hR)) g R⁻¹ (inv_pos.mpr hR))
    (scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g)
    (isMetricNorm_of_riemannianBundle _) lam hlam x y v h0
  intro mr gr hmr _ h hEnorm
  exact h1

/-- **LC73's test in physical form.** At a point `x` of the closed shell of the zero ball at `k`
(radius `R`), with the ratio `λ = R/r` (`0 < r`, `Λz ≤ R/r`, `0 < ζ`), along a physical unit
direction `w₀` whose normalized geodesics reach `y` (`r < d(x, y)`, `ζ d(x, y) < r`):
`|R dη₀(w₀) − (d(k, y) − d(k, x))/d(x, y)| < ζ`. -/
theorem zero_adapted_test_phys_KA5
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) {k : X} (hk : k ∈ P.zero.centres) {x : X}
    (h1 : (P.zero.zero k hk).radius / 10 ≤ dist k x)
    (h2 : dist k x ≤ 10 * (P.zero.zero k hk).radius) {r : ℝ} (hr : 0 < r)
    (hΛz : Λz ≤ (P.zero.zero k hk).radius / r) (hζ : 0 < ζ) {y : X} (hy1 : r < dist x y)
    (hy2 : ζ * dist x y < r) (w₀ : TangentSpace 𝓘(ℝ, E3) x) (hw₀ : g.inner x w₀ w₀ = 1)
    (hgeo : ∀ (R : ℝ) (hR : 0 < R),
        let hMc : CompleteSpace X := complete_of_compact
        letI := mX.rescale R⁻¹ (inv_pos.mpr hR)
        letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
        letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
          radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
        letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
          radialScaledManifold (m := mX) g hmetric R⁻¹ (inv_pos.mpr hR)
        letI : CompleteSpace X := (mX.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
        let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
          scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
        have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR :=
          isMetricNorm_of_riemannianBundle gR
        intrinsicGeodesic gR hnR x (R • w₀) (dist x y) = y) :
    |(P.zero.zero k hk).radius * mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x w₀ -
      (dist k y - dist k x) / dist x y| < ζ := by
  have hR : 0 < (P.zero.zero k hk).radius := (P.zero.zero k hk).radius_pos
  have hlam : 0 < (P.zero.zero k hk).radius / r := div_pos hR hr
  have hdiff := zero_radial_mdifferentiableAt_KA5 P hk h1 h2
  have hd : 0 < dist x y := hr.trans hy1
  obtain ⟨hEnorm, Zf, mZ, z, κ, hκ, -, -, -, -, -, htest⟩ :=
    P.zero_adapted k hk x h1 h2 _ hlam hΛz
  have hx1 : (P.zero.zero k hk).radius / r * ((P.zero.zero k hk).radius⁻¹ * dist x x) < 1 := by
    rw [dist_self]; norm_num
  have hy : (P.zero.zero k hk).radius / r * ((P.zero.zero k hk).radius⁻¹ * dist y x) < ζ⁻¹ := by
    rw [dist_comm]
    have he : (P.zero.zero k hk).radius / r * ((P.zero.zero k hk).radius⁻¹ * dist x y) =
        dist x y / r := by field_simp
    rw [he, div_lt_iff₀ hr, inv_mul_eq_div, lt_div_iff₀ hζ]
    linarith
  have hsep : 1 < (P.zero.zero k hk).radius / r * ((P.zero.zero k hk).radius⁻¹ * dist x y) := by
    have he : (P.zero.zero k hk).radius / r * ((P.zero.zero k hk).radius⁻¹ * dist x y) =
        dist x y / r := by field_simp
    rw [he, one_lt_div hr]
    exact hy1
  have hu : (scaleMetric (((P.zero.zero k hk).radius / r) ^ 2) (pow_pos hlam 2)
      (scaleMetric ((P.zero.zero k hk).radius⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g)).inner x
      (((P.zero.zero k hk).radius / r)⁻¹ • ((P.zero.zero k hk).radius • w₀))
      (((P.zero.zero k hk).radius / r)⁻¹ • ((P.zero.zero k hk).radius • w₀)) = 1 := by
    rw [scaleMetric_inner, scaleMetric_inner, gInner_smul_self, gInner_smul_self, hw₀]
    field_simp
  have hT := htest x hx1 y hy hsep _ hu
    (zero_double_geodesic_KA5 g hmetric hR hlam ((P.zero.zero k hk).radius • w₀)
      (hgeo _ hR) hEnorm)
  rw [hκ y, hκ x] at hT
  have hψ : mvfderiv 𝓘(ℝ, E3) (fun x' => (P.zero.zero k hk).radius / r *
      ((P.zero.zero k hk).radial x' - (P.zero.zero k hk).radial x)) x
      (((P.zero.zero k hk).radius / r)⁻¹ • ((P.zero.zero k hk).radius • w₀)) =
      (P.zero.zero k hk).radius * mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x w₀ := by
    have hc := DifferentialGeometry.Topology.Ehresmann.mvfderiv_comp_real hdiff
      (g := fun t => (P.zero.zero k hk).radius / r * (t - (P.zero.zero k hk).radial x))
      (by fun_prop) (((P.zero.zero k hk).radius / r)⁻¹ • ((P.zero.zero k hk).radius • w₀))
    rw [hc, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    simp only [deriv_const_mul_field', deriv_sub_const, deriv_id'', mul_one]
    field_simp
  have hT' : |mvfderiv 𝓘(ℝ, E3) (fun x' => (P.zero.zero k hk).radius / r *
      ((P.zero.zero k hk).radial x' - (P.zero.zero k hk).radial x)) x
      (((P.zero.zero k hk).radius / r)⁻¹ • ((P.zero.zero k hk).radius • w₀)) -
      ((P.zero.zero k hk).radius / r * ((P.zero.zero k hk).radius⁻¹ * dist k y -
          (P.zero.zero k hk).radius⁻¹ * dist k x) -
        (P.zero.zero k hk).radius / r * ((P.zero.zero k hk).radius⁻¹ * dist k x -
          (P.zero.zero k hk).radius⁻¹ * dist k x)) /
        ((P.zero.zero k hk).radius / r * ((P.zero.zero k hk).radius⁻¹ * dist x y))| < ζ := hT
  rw [hψ] at hT'
  have he : ((P.zero.zero k hk).radius / r * ((P.zero.zero k hk).radius⁻¹ * dist k y -
          (P.zero.zero k hk).radius⁻¹ * dist k x) -
        (P.zero.zero k hk).radius / r * ((P.zero.zero k hk).radius⁻¹ * dist k x -
          (P.zero.zero k hk).radius⁻¹ * dist k x)) /
        ((P.zero.zero k hk).radius / r * ((P.zero.zero k hk).radius⁻¹ * dist x y)) =
      (dist k y - dist k x) / dist x y := by
    rw [sub_self, mul_zero, sub_zero]
    field_simp
  rw [he] at hT'
  exact hT'

/-- **LC73's Lipschitz clause in physical form**: at a point `x` of the closed shell (ratio
`λ = R/r`, `Λz ≤ R/r`), `|R dη₀(v)| ≤ (1 + ζ)√(g(v, v))` for every tangent vector `v`. -/
theorem zero_adapted_deriv_bound_KA5
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) {k : X} (hk : k ∈ P.zero.centres) {x : X}
    (h1 : (P.zero.zero k hk).radius / 10 ≤ dist k x)
    (h2 : dist k x ≤ 10 * (P.zero.zero k hk).radius) {r : ℝ} (hr : 0 < r)
    (hΛz : Λz ≤ (P.zero.zero k hk).radius / r) (v : TangentSpace 𝓘(ℝ, E3) x) :
    |(P.zero.zero k hk).radius * mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x v| ≤
      (1 + ζ) * Real.sqrt (g.inner x v v) := by
  have hR : 0 < (P.zero.zero k hk).radius := (P.zero.zero k hk).radius_pos
  have hlam : 0 < (P.zero.zero k hk).radius / r := div_pos hR hr
  have hdiff := zero_radial_mdifferentiableAt_KA5 P hk h1 h2
  obtain ⟨-, Zf, mZ, z, κ, -, -, -, hlip, -⟩ := P.zero_adapted k hk x h1 h2 _ hlam hΛz
  have hmem : ∀ a ∈ ball x r,
      (P.zero.zero k hk).radius / r * ((P.zero.zero k hk).radius⁻¹ * dist a x) < 1 := by
    intro a ha
    have he : (P.zero.zero k hk).radius / r * ((P.zero.zero k hk).radius⁻¹ * dist a x) =
        dist a x / r := by field_simp
    rw [he, div_lt_one hr]
    exact mem_ball.mp ha
  have hlip' : ∀ a ∈ ball x r, ∀ c ∈ ball x r,
      |(P.zero.zero k hk).radial a - (P.zero.zero k hk).radial c| ≤
        (1 + ζ) * (P.zero.zero k hk).radius⁻¹ * dist a c := by
    intro a ha c hc
    have h := hlip a (hmem a ha) c (hmem c hc)
    change |(P.zero.zero k hk).radius / r *
        ((P.zero.zero k hk).radial a - (P.zero.zero k hk).radial x) -
      (P.zero.zero k hk).radius / r *
        ((P.zero.zero k hk).radial c - (P.zero.zero k hk).radial x)| ≤
      (1 + ζ) * ((P.zero.zero k hk).radius / r * ((P.zero.zero k hk).radius⁻¹ * dist a c)) at h
    have he1 : (P.zero.zero k hk).radius / r *
        ((P.zero.zero k hk).radial a - (P.zero.zero k hk).radial x) -
      (P.zero.zero k hk).radius / r *
        ((P.zero.zero k hk).radial c - (P.zero.zero k hk).radial x) =
        (P.zero.zero k hk).radius / r *
          ((P.zero.zero k hk).radial a - (P.zero.zero k hk).radial c) := by ring
    have he2 : (1 + ζ) * ((P.zero.zero k hk).radius / r *
        ((P.zero.zero k hk).radius⁻¹ * dist a c)) =
        (P.zero.zero k hk).radius / r * ((1 + ζ) * (P.zero.zero k hk).radius⁻¹ * dist a c) := by
      ring
    rw [he1, he2, abs_mul, abs_of_pos hlam] at h
    exact le_of_mul_le_mul_left h hlam
  have hb := abs_mvfderiv_le_of_lipschitzOn_riem g hmetric isOpen_ball (mem_ball_self hr) hdiff
    hlip' v
  rw [abs_mul, abs_of_pos hR]
  calc (P.zero.zero k hk).radius * |mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x v|
      ≤ (P.zero.zero k hk).radius *
          ((1 + ζ) * (P.zero.zero k hk).radius⁻¹ * Real.sqrt (g.inner x v v)) :=
        mul_le_mul_of_nonneg_left hb hR.le
    _ = (1 + ζ) * Real.sqrt (g.inner x v v) := by field_simp

end Zero

end DifferentialGeometry.Geometry.Collapse
