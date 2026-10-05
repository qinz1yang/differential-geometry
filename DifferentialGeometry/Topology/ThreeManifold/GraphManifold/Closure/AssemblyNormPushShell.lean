import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyNormSplitVertex
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecCapProjectiveShell
import DifferentialGeometry.Topology.Manifold.SpherePolarCoordinates
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Product

/-!
# FC42 normalization, packet N2a (tools): the radial push, the thin shell, the chart radius

Lane ASM-NRM4 (design of lane ASM-NRM3, `build-logs/resume/state-ASM-NRM3.md` §2, approved by
main). Euclidean and chart-level tools for splitting a punctured `ℝP³` vertex along the sphere of
chart radius `1 + η`:

* the derivative of `Real.smoothTransition` is bounded (`exists_deriv_smoothTransition_bound`);
* the radial push profile `radialPushProfile η r = r + η (1 - τ (2 (r - 1)))` (`r + η` on
  `r ≤ 1`, the identity on `r ≥ 3/2`, strictly monotone with derivative `≥ 1/2` for small `η`), the
  radial push `radialPush η` of `ℝ³` (a local diffeomorphism off `0`, injective on `{0}ᶜ`) and its
  reading `chartPush c η` in a chart `c` defined on the closed ball of radius `2` (a local
  diffeomorphism and injective off `c (B̄^{1/2})`, mapping the complement of `c (B¹)` ONTO the
  complement of `c (B^{1+η})`);
* the thin shell `pushShellRadial η : S² × [0, 1] → ℝ³`, `(z, t) ↦ (1 + η t) z` (smooth, injective,
  bijective differential), and the collar radial map `pushCollarRadial η`, `(z, s) ↦
  (1 + η + η s / 4) z` (a local diffeomorphism where the radius is positive);
* the chart radius `chartRadius c y = min ‖c⁻¹ y‖ (3/2)` (`3/2` off the chart ball of radius `2`),
  continuous.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

local instance sphereDim_ASMNRM4 : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by simp⟩

/-- The derivative of the smooth transition is bounded. -/
theorem exists_deriv_smoothTransition_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ x, |deriv Real.smoothTransition x| ≤ B := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x => ?_⟩
  rcases lt_or_ge x 0 with hx | hx
  · have h0 : deriv Real.smoothTransition x = 0 := by
      have hev : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds hx] with y hy
        exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
      rw [hev.deriv_eq, deriv_const]
    rw [h0, abs_zero]
    exact le_trans zero_le_one (le_max_right _ _)
  rcases le_or_gt x 1 with hx1 | hx1
  · exact le_trans (hC x ⟨hx, hx1⟩) (le_max_left _ _)
  · have h0 : deriv Real.smoothTransition x = 0 := by
      have hev : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 1 := by
        filter_upwards [Ioi_mem_nhds hx1] with y hy
        exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
      rw [hev.deriv_eq, deriv_const]
    rw [h0, abs_zero]
    exact le_trans zero_le_one (le_max_right _ _)

/-! ## The radial push profile -/

/-- The radial push profile `r ↦ r + η (1 - τ (2 (r - 1)))`: `r + η` for `r ≤ 1`, `r` for
`r ≥ 3/2`. -/
def radialPushProfile (η r : ℝ) : ℝ :=
  r + η * (1 - Real.smoothTransition (2 * (r - 1)))

theorem contDiff_radialPushProfile (η : ℝ) : ContDiff ℝ ∞ (radialPushProfile η) := by
  unfold radialPushProfile
  have := (Real.smoothTransition.contDiff (n := ⊤)).comp
    ((contDiff_const.mul (contDiff_id.sub contDiff_const)) : ContDiff ℝ ∞ fun r : ℝ => 2 * (r - 1))
  exact contDiff_id.add (contDiff_const.mul (contDiff_const.sub this))

theorem radialPushProfile_of_le_one (η : ℝ) {r : ℝ} (hr : r ≤ 1) :
    radialPushProfile η r = r + η := by
  unfold radialPushProfile
  rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
  ring

theorem radialPushProfile_of_ge (η : ℝ) {r : ℝ} (hr : 3 / 2 ≤ r) : radialPushProfile η r = r := by
  unfold radialPushProfile
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  ring

theorem hasDerivAt_radialPushProfile (η r : ℝ) :
    HasDerivAt (radialPushProfile η)
      (1 - η * (deriv Real.smoothTransition (2 * (r - 1)) * 2)) r := by
  have hτ : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (2 * (r - 1)))
      (2 * (r - 1)) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable (by simp) _).hasDerivAt
  have hin : HasDerivAt (fun r : ℝ => 2 * (r - 1)) 2 r := by
    simpa using ((hasDerivAt_id r).sub_const 1).const_mul (2 : ℝ)
  have hcomp := hτ.comp r hin
  have h := (hasDerivAt_id r).add ((hcomp.const_sub 1).const_mul η)
  have hfun : radialPushProfile η =
      fun x => id x + η * (1 - (Real.smoothTransition ∘ fun r : ℝ => 2 * (r - 1)) x) := rfl
  rw [hfun]
  convert h using 1
  ring

/-- With `η ≤ 1/(4B)` the profile has derivative at least `1/2`. -/
theorem half_le_deriv_radialPushProfile {B η : ℝ} (hB : ∀ x, |deriv Real.smoothTransition x| ≤ B)
    (hη : 0 ≤ η) (hηB : η * B ≤ 1 / 4) (r : ℝ) :
    1 / 2 ≤ 1 - η * (deriv Real.smoothTransition (2 * (r - 1)) * 2) := by
  have h1 := hB (2 * (r - 1))
  have h2 : η * deriv Real.smoothTransition (2 * (r - 1)) ≤ η * B :=
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans h1) hη
  nlinarith

theorem strictMono_radialPushProfile {B η : ℝ}
    (hB : ∀ x, |deriv Real.smoothTransition x| ≤ B) (hη : 0 ≤ η) (hηB : η * B ≤ 1 / 4) :
    StrictMono (radialPushProfile η) := by
  apply strictMono_of_deriv_pos
  intro r
  rw [(hasDerivAt_radialPushProfile η r).deriv]
  linarith [half_le_deriv_radialPushProfile hB hη hηB r]

theorem isLocalDiffeomorphAt_radialPushProfile {B η : ℝ}
    (hB : ∀ x, |deriv Real.smoothTransition x| ≤ B) (hη : 0 ≤ η) (hηB : η * B ≤ 1 / 4) (r : ℝ) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (radialPushProfile η) r := by
  set d := 1 - η * (deriv Real.smoothTransition (2 * (r - 1)) * 2) with hd
  have hd0 : d ≠ 0 := by
    have := half_le_deriv_radialPushProfile hB hη hηB r
    rw [← hd] at this
    linarith
  let A : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 d hd0)
  have hA : (A : ℝ →L[ℝ] ℝ) = ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) d := by
    ext
    simp [A]
  have hder : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (radialPushProfile η) r (A : ℝ →L[ℝ] ℝ) := by
    rw [hA]
    exact (hasDerivAt_radialPushProfile η r).hasFDerivAt.hasMFDerivAt
  exact Topology.Manifold.isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv
    _ (contDiff_radialPushProfile η).contMDiff.contMDiffOn isOpen_univ r (mem_univ r) A hder

/-! ## The radial push of Euclidean space -/

/-- The radial push `v ↦ g (‖v‖) • v / ‖v‖`. -/
def radialPush (η : ℝ) (v : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  (radialPushProfile η ‖v‖ / ‖v‖) • v

theorem radialPush_of_ge (η : ℝ) {v : EuclideanSpace ℝ (Fin 3)} (hv : 3 / 2 ≤ ‖v‖) :
    radialPush η v = v := by
  have hv0 : ‖v‖ ≠ 0 := by linarith
  rw [radialPush, radialPushProfile_of_ge η hv, div_self hv0, one_smul]

theorem radialPush_eq_polar (η : ℝ) (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {v : EuclideanSpace ℝ (Fin 3)} (hv : v ≠ 0) :
    radialPush η v =
      radialPushProfile η ‖v‖ • (DifferentialGeometry.Topology.Manifold.sphereDirection z v :
        EuclideanSpace ℝ (Fin 3)) := by
  have h := DifferentialGeometry.Topology.Manifold.norm_smul_sphereDirection z hv
  calc radialPush η v = (radialPushProfile η ‖v‖ / ‖v‖) •
        (‖v‖ • (DifferentialGeometry.Topology.Manifold.sphereDirection z v :
          EuclideanSpace ℝ (Fin 3))) := by rw [h]; rfl
    _ = _ := by rw [smul_smul, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hv)]

theorem le_radialPushProfile {η : ℝ} (hη : 0 ≤ η) (r : ℝ) : r ≤ radialPushProfile η r := by
  unfold radialPushProfile
  have := Real.smoothTransition.le_one (2 * (r - 1))
  nlinarith

theorem norm_radialPush {η : ℝ} (hη : 0 ≤ η) {v : EuclideanSpace ℝ (Fin 3)} (hv : v ≠ 0) :
    ‖radialPush η v‖ = radialPushProfile η ‖v‖ := by
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hg : 0 < radialPushProfile η ‖v‖ := lt_of_lt_of_le hn (le_radialPushProfile hη _)
  rw [radialPush, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hg hn),
    div_mul_cancel₀ _ hn.ne']

theorem injOn_radialPush {B η : ℝ} (hB : ∀ x, |deriv Real.smoothTransition x| ≤ B)
    (hη : 0 ≤ η) (hηB : η * B ≤ 1 / 4) : InjOn (radialPush η) {0}ᶜ := by
  intro v hv w hw h
  have hv' : v ≠ 0 := hv
  have hw' : w ≠ 0 := hw
  have hn : ‖v‖ = ‖w‖ := (strictMono_radialPushProfile hB hη hηB).injective
    ((norm_radialPush hη hv').symm.trans ((congrArg norm h).trans (norm_radialPush hη hw')))
  have hc : radialPushProfile η ‖v‖ / ‖v‖ ≠ 0 :=
    div_ne_zero (lt_of_lt_of_le (norm_pos_iff.mpr hv') (le_radialPushProfile hη _)).ne'
      (norm_ne_zero_iff.mpr hv')
  have h' : (radialPushProfile η ‖v‖ / ‖v‖) • v = (radialPushProfile η ‖v‖ / ‖v‖) • w := by
    have := h
    rw [radialPush, radialPush, ← hn] at this
    exact this
  exact smul_right_injective _ hc h'

theorem isLocalDiffeomorphAt_radialPush {B η : ℝ} (hB : ∀ x, |deriv Real.smoothTransition x| ≤ B)
    (hη : 0 ≤ η) (hηB : η * B ≤ 1 / 4) {v : EuclideanSpace ℝ (Fin 3)} (hv : v ≠ 0) :
    IsLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (radialPush η) v := by
  let z₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    ⟨EuclideanSpace.single 0 1, by simp⟩
  let pol := DifferentialGeometry.Topology.Manifold.spherePolarChart (n := 2) z₀
  have h1 : IsLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      pol.symm v := pol.symm.isLocalDiffeomorphAt _ _ _ (show v ∈ ({0}ᶜ : Set _) from hv)
  have h2 : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (Prod.map (Diffeomorph.refl (𝓡 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)
        (radialPushProfile η)) (pol.symm v) :=
    ((Diffeomorph.refl (𝓡 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞).isLocalDiffeomorph
      _).prodMap (isLocalDiffeomorphAt_radialPushProfile hB hη hηB _)
  have hpos : 0 < (Prod.map (Diffeomorph.refl (𝓡 2)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞) (radialPushProfile η)
        (pol.symm v)).2 := by
    change 0 < radialPushProfile η ‖v‖
    exact lt_of_lt_of_le (norm_pos_iff.mpr hv) (le_radialPushProfile hη _)
  have h3 := DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_sphere_smul (n := 2) _ hpos
  have htot := (h1.comp _ _ h2).comp _ _ h3
  refine DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq ?_ htot
  filter_upwards [isOpen_compl_singleton.mem_nhds hv] with w hw
  rw [radialPush_eq_polar η z₀ hw]
  rfl

theorem radialPushProfile_three_halves (η : ℝ) : radialPushProfile η (3 / 2) = 3 / 2 :=
  radialPushProfile_of_ge η le_rfl

theorem norm_radialPush_lt_two {B η : ℝ} (hB : ∀ x, |deriv Real.smoothTransition x| ≤ B)
    (hη : 0 ≤ η) (hηB : η * B ≤ 1 / 4) {v : EuclideanSpace ℝ (Fin 3)} (hv0 : v ≠ 0)
    (hv : ‖v‖ < 2) : ‖radialPush η v‖ < 2 := by
  rcases le_or_gt (3 / 2) ‖v‖ with h | h
  · rw [radialPush_of_ge η h]
    exact hv
  · rw [norm_radialPush hη hv0]
    have := (strictMono_radialPushProfile hB hη hηB).monotone h.le
    rw [radialPushProfile_three_halves] at this
    linarith

/-- On the unit sphere the push is the dilation by `1 + η`. -/
theorem radialPush_of_norm_eq_one (η : ℝ) {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ = 1) :
    radialPush η v = (1 + η) • v := by
  rw [radialPush, hv, radialPushProfile_of_le_one η le_rfl, div_one]

/-! ## The push in a chart -/

section ChartPush

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y]
  (c : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡 3) (EuclideanSpace ℝ (Fin 3)) Y ∞)

open Classical in
/-- The radial push read in the chart `c`, the identity off the chart ball of radius `2`. -/
def chartPush (η : ℝ) (y : Y) : Y :=
  if y ∈ c.target ∧ ‖c.symm y‖ < 2 then c (radialPush η (c.symm y)) else y

variable {c}

theorem chartPush_chart (hc : Metric.closedBall 0 2 ⊆ c.source) (η : ℝ)
    {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ < 2) : chartPush c η (c v) = c (radialPush η v) := by
  have hvs : v ∈ c.source := hc (mem_closedBall_zero_iff.mpr hv.le)
  have hl : c.symm (c v) = v := c.toPartialEquiv.left_inv hvs
  unfold chartPush
  rw [ite_eq_left ⟨c.map_source hvs, by rw [hl]; exact hv⟩, hl]

theorem chartPush_of_not_mem (η : ℝ) {y : Y} (hy : y ∉ c '' Metric.ball 0 2) :
    chartPush c η y = y := by
  unfold chartPush
  rw [ite_eq_right]
  rintro ⟨hyt, hy2⟩
  exact hy ⟨c.symm y, mem_ball_zero_iff.mpr hy2, c.toPartialEquiv.right_inv hyt⟩

theorem chartPush_eq_self (η : ℝ) {y : Y} (hy : y ∉ c '' Metric.closedBall 0 (3 / 2)) :
    chartPush c η y = y := by
  unfold chartPush
  split_ifs with h
  · obtain ⟨hyt, hy2⟩ := h
    have hr : c (c.symm y) = y := c.toPartialEquiv.right_inv hyt
    have h32 : 3 / 2 < ‖c.symm y‖ := by
      by_contra hle
      exact hy ⟨c.symm y, mem_closedBall_zero_iff.mpr (not_lt.mp hle), hr⟩
    rw [radialPush_of_ge η h32.le]
    exact hr
  · rfl

theorem isOpen_chart_image_ball (hc : Metric.closedBall 0 2 ⊆ c.source) :
    IsOpen (c '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 2) :=
  c.toOpenPartialHomeomorph.isOpen_image_of_subset_source Metric.isOpen_ball
    (Metric.ball_subset_closedBall.trans hc)

theorem isClosed_chart_image_closedBall [T2Space Y] (hc : Metric.closedBall 0 2 ⊆ c.source)
    {r : ℝ} (hr : r ≤ 2) : IsClosed (c '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) r) :=
  ((isCompact_closedBall 0 r).image_of_continuousOn
    (c.contMDiffOn.continuousOn.mono ((Metric.closedBall_subset_closedBall hr).trans hc))).isClosed

theorem isLocalDiffeomorphAt_chartPush [T2Space Y]
    (hc : Metric.closedBall 0 2 ⊆ c.source) {B η : ℝ}
    (hB : ∀ x, |deriv Real.smoothTransition x| ≤ B) (hη : 0 ≤ η) (hηB : η * B ≤ 1 / 4) {y : Y}
    (hy : y ∉ c '' Metric.closedBall 0 (1 / 2)) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (chartPush c η) y := by
  by_cases hin : y ∈ c '' Metric.ball 0 2
  · obtain ⟨v, hv, rfl⟩ := hin
    have hv2 : ‖v‖ < 2 := mem_ball_zero_iff.mp hv
    have hvs : v ∈ c.source := hc (Metric.ball_subset_closedBall hv)
    have hl : c.symm (c v) = v := c.toPartialEquiv.left_inv hvs
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact hy ⟨0, Metric.mem_closedBall_self (by norm_num), rfl⟩
    have h1 : IsLocalDiffeomorphAt (𝓡 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ c.symm (c v) :=
      c.symm.isLocalDiffeomorphAt _ _ _ (c.map_source hvs)
    have h2 : IsLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
        (radialPush η) (c.symm (c v)) := by
      rw [hl]
      exact isLocalDiffeomorphAt_radialPush hB hη hηB hv0
    have hρs : radialPush η (c.symm (c v)) ∈ c.source := by
      rw [hl]
      exact hc (mem_closedBall_zero_iff.mpr (norm_radialPush_lt_two hB hη hηB hv0 hv2).le)
    have h3 : IsLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡 3) ∞ c
        (radialPush η (c.symm (c v))) := c.isLocalDiffeomorphAt _ _ _ hρs
    have htot := (h1.comp _ _ h2).comp _ _ h3
    refine DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq ?_ htot
    filter_upwards [(isOpen_chart_image_ball hc).mem_nhds ⟨v, hv, rfl⟩] with z hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [chartPush_chart hc η (mem_ball_zero_iff.mp hw)]
    have hlw : c.symm (c w) = w :=
      c.toPartialEquiv.left_inv (hc (Metric.ball_subset_closedBall hw))
    change c (radialPush η w) = c (radialPush η (c.symm (c w)))
    rw [hlw]
  · have hy32 : y ∉ c '' Metric.closedBall 0 (3 / 2) := fun h =>
      hin (image_mono (Metric.closedBall_subset_ball (by norm_num)) h)
    have hid : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (id : Y → Y) y :=
      (Diffeomorph.refl (𝓡 3) Y ∞).isLocalDiffeomorph y
    refine DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq ?_ hid
    filter_upwards [(isClosed_chart_image_closedBall hc (by norm_num)).isOpen_compl.mem_nhds hy32]
      with z hz
    exact chartPush_eq_self η hz

theorem mem_chart_image_ball_chartPush (hc : Metric.closedBall 0 2 ⊆ c.source) {B η : ℝ}
    (hB : ∀ x, |deriv Real.smoothTransition x| ≤ B) (hη : 0 ≤ η) (hηB : η * B ≤ 1 / 4)
    {v : EuclideanSpace ℝ (Fin 3)} (hv0 : v ≠ 0) (hv : ‖v‖ < 2) :
    chartPush c η (c v) ∈ c '' Metric.ball 0 2 := by
  rw [chartPush_chart hc η hv]
  exact ⟨_, mem_ball_zero_iff.mpr (norm_radialPush_lt_two hB hη hηB hv0 hv), rfl⟩

theorem injOn_chartPush (hc : Metric.closedBall 0 2 ⊆ c.source) {B η : ℝ}
    (hB : ∀ x, |deriv Real.smoothTransition x| ≤ B) (hη : 0 ≤ η) (hηB : η * B ≤ 1 / 4) :
    InjOn (chartPush c η) (c '' Metric.closedBall 0 (1 / 2))ᶜ := by
  have hnz : ∀ {v : EuclideanSpace ℝ (Fin 3)}, c v ∉ c '' Metric.closedBall 0 (1 / 2) → v ≠ 0 := by
    intro v hv h
    rw [h] at hv
    exact hv ⟨0, Metric.mem_closedBall_self (by norm_num), rfl⟩
  intro y hy y' hy' h
  by_cases hin : y ∈ c '' Metric.ball 0 2 <;> by_cases hin' : y' ∈ c '' Metric.ball 0 2
  · obtain ⟨v, hv, rfl⟩ := hin
    obtain ⟨w, hw, rfl⟩ := hin'
    have hv2 := mem_ball_zero_iff.mp hv
    have hw2 := mem_ball_zero_iff.mp hw
    rw [chartPush_chart hc η hv2, chartPush_chart hc η hw2] at h
    have h' := c.toOpenPartialHomeomorph.injOn
      (hc (mem_closedBall_zero_iff.mpr (norm_radialPush_lt_two hB hη hηB (hnz hy) hv2).le))
      (hc (mem_closedBall_zero_iff.mpr (norm_radialPush_lt_two hB hη hηB (hnz hy') hw2).le)) h
    rw [injOn_radialPush hB hη hηB (hnz hy) (hnz hy') h']
  · obtain ⟨v, hv, rfl⟩ := hin
    have hm := mem_chart_image_ball_chartPush hc hB hη hηB (hnz hy) (mem_ball_zero_iff.mp hv)
    rw [h, chartPush_of_not_mem η hin'] at hm
    exact (hin' hm).elim
  · obtain ⟨w, hw, rfl⟩ := hin'
    have hm := mem_chart_image_ball_chartPush hc hB hη hηB (hnz hy') (mem_ball_zero_iff.mp hw)
    rw [← h, chartPush_of_not_mem η hin] at hm
    exact (hin hm).elim
  · rwa [chartPush_of_not_mem η hin, chartPush_of_not_mem η hin'] at h

/-- The push maps the complement of the unit chart ball into the complement of the chart ball of
radius `1 + η`. -/
theorem chartPush_not_mem (hc : Metric.closedBall 0 2 ⊆ c.source) {B η : ℝ}
    (hB : ∀ x, |deriv Real.smoothTransition x| ≤ B) (hη : 0 ≤ η) (hηB : η * B ≤ 1 / 4)
    (hη2 : η < 1 / 2) {y : Y} (hy : y ∉ c '' Metric.ball 0 1) :
    chartPush c η y ∉ c '' Metric.ball 0 (1 + η) := by
  by_cases hin : y ∈ c '' Metric.ball 0 2
  · obtain ⟨v, hv, rfl⟩ := hin
    have hv2 := mem_ball_zero_iff.mp hv
    have hv1 : 1 ≤ ‖v‖ := not_lt.mp fun h => hy ⟨v, mem_ball_zero_iff.mpr h, rfl⟩
    have hv0 : v ≠ 0 := norm_pos_iff.mp (by linarith)
    have hnorm : 1 + η ≤ ‖radialPush η v‖ := by
      rcases le_or_gt (3 / 2) ‖v‖ with h | h
      · rw [radialPush_of_ge η h]
        linarith
      · rw [norm_radialPush hη hv0]
        have := (strictMono_radialPushProfile hB hη hηB).monotone hv1
        rw [radialPushProfile_of_le_one η le_rfl] at this
        exact this
    rw [chartPush_chart hc η hv2]
    rintro ⟨w, hw, hcw⟩
    have hρs : radialPush η v ∈ c.source :=
      hc (mem_closedBall_zero_iff.mpr (norm_radialPush_lt_two hB hη hηB hv0 hv2).le)
    have hws : w ∈ c.source := hc (mem_closedBall_zero_iff.mpr
      (le_of_lt (lt_trans (mem_ball_zero_iff.mp hw) (by linarith))))
    have := c.toOpenPartialHomeomorph.injOn hws hρs hcw
    rw [← this] at hnorm
    linarith [mem_ball_zero_iff.mp hw]
  · rw [chartPush_of_not_mem η hin]
    exact fun h => hin (image_mono (Metric.ball_subset_ball (by linarith)) h)

/-- The push maps the complement of the unit chart ball ONTO the complement of the chart ball of
radius `1 + η`. -/
theorem exists_chartPush_eq (hc : Metric.closedBall 0 2 ⊆ c.source) {η : ℝ} (hη : 0 ≤ η)
    {y : Y} (hy : y ∉ c '' Metric.ball 0 (1 + η)) :
    ∃ y', y' ∉ c '' Metric.ball 0 1 ∧ chartPush c η y' = y := by
  by_cases hin : y ∈ c '' Metric.ball 0 2
  · obtain ⟨w, hw, rfl⟩ := hin
    have hw2 := mem_ball_zero_iff.mp hw
    have hw1 : 1 + η ≤ ‖w‖ := not_lt.mp fun h => hy ⟨w, mem_ball_zero_iff.mpr h, rfl⟩
    have hwpos : 0 < ‖w‖ := by linarith
    have hnot1 : ∀ v : EuclideanSpace ℝ (Fin 3), 1 ≤ ‖v‖ → ‖v‖ < 2 →
        c v ∉ c '' Metric.ball 0 1 := by
      rintro v hv1 hv2 ⟨u, hu, hcu⟩
      have hus : u ∈ c.source := hc (mem_closedBall_zero_iff.mpr
        (le_of_lt (lt_trans (mem_ball_zero_iff.mp hu) (by norm_num))))
      have hvs : v ∈ c.source := hc (mem_closedBall_zero_iff.mpr hv2.le)
      have := c.toOpenPartialHomeomorph.injOn hus hvs hcu
      rw [this] at hu
      linarith [mem_ball_zero_iff.mp hu]
    rcases le_or_gt (3 / 2) ‖w‖ with h | h
    · refine ⟨c w, hnot1 w (by linarith) hw2, ?_⟩
      rw [chartPush_chart hc η hw2, radialPush_of_ge η h]
    · have hcont : ContinuousOn (radialPushProfile η) (Icc 1 (3 / 2)) :=
        (contDiff_radialPushProfile η).continuous.continuousOn
      have hmem : ‖w‖ ∈ Icc (radialPushProfile η 1) (radialPushProfile η (3 / 2)) := by
        rw [radialPushProfile_of_le_one η le_rfl, radialPushProfile_three_halves]
        exact ⟨hw1, h.le⟩
      obtain ⟨r, ⟨hr1, hr2⟩, hgr⟩ := intermediate_value_Icc (by norm_num) hcont hmem
      have hrpos : 0 < r := by linarith
      set v : EuclideanSpace ℝ (Fin 3) := (r / ‖w‖) • w with hvdef
      have hvn : ‖v‖ = r := by
        rw [hvdef, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hrpos hwpos),
          div_mul_cancel₀ _ hwpos.ne']
      have hv2 : ‖v‖ < 2 := by rw [hvn]; linarith
      refine ⟨c v, hnot1 v (by rw [hvn]; exact hr1) hv2, ?_⟩
      rw [chartPush_chart hc η hv2]
      congr 1
      rw [radialPush, hvn, hgr, hvdef, smul_smul, div_mul_div_cancel₀ hrpos.ne', div_self hwpos.ne',
        one_smul]
  · refine ⟨y, fun h => hin (image_mono (Metric.ball_subset_ball (by norm_num)) h), ?_⟩
    exact chartPush_of_not_mem η hin

end ChartPush

/-! ## The thin shell and the collar radial map -/

/-- The affine diffeomorphism `t ↦ a + b t` of the line (`b ≠ 0`). -/
def pushAffine (a b : ℝ) (hb : b ≠ 0) : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ where
  toFun t := a + b * t
  invFun t := (t - a) / b
  left_inv t := by
    change (a + b * t - a) / b = t
    field_simp
    ring
  right_inv t := by
    change a + b * ((t - a) / b) = t
    field_simp
    ring
  contMDiff_toFun := (contDiff_const.add (contDiff_const.mul contDiff_id)).contMDiff
  contMDiff_invFun := ((contDiff_id.sub contDiff_const).div_const b).contMDiff

/-- The thin shell `(z, t) ↦ (1 + η t) z` between the spheres of radius `1` and `1 + η`. -/
def pushShellRadial (η : ℝ) (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1) :
    EuclideanSpace ℝ (Fin 3) :=
  (1 + η * (p.2 : ℝ)) • (p.1 : EuclideanSpace ℝ (Fin 3))

theorem norm_pushShellRadial {η : ℝ} (hη : 0 ≤ η)
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1) :
    ‖pushShellRadial η p‖ = 1 + η * (p.2 : ℝ) := by
  have h0 : 0 ≤ η * (p.2 : ℝ) := mul_nonneg hη p.2.2.1
  rw [pushShellRadial, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith),
    norm_eq_of_mem_sphere, mul_one]

theorem pushShellRadial_injective {η : ℝ} (hη : 0 < η) : Injective (pushShellRadial η) := by
  intro p q h
  have hn := congrArg norm h
  rw [norm_pushShellRadial hη.le, norm_pushShellRadial hη.le] at hn
  have ht : (p.2 : ℝ) = q.2 := by
    have : η * (p.2 : ℝ) = η * q.2 := by linarith
    exact mul_left_cancel₀ hη.ne' this
  have hpos : (1 + η * (p.2 : ℝ)) ≠ 0 := by nlinarith [p.2.2.1]
  have hz : (p.1 : EuclideanSpace ℝ (Fin 3)) = q.1 := by
    have h' : (1 + η * (p.2 : ℝ)) • (p.1 : EuclideanSpace ℝ (Fin 3)) =
        (1 + η * (p.2 : ℝ)) • (q.1 : EuclideanSpace ℝ (Fin 3)) := by
      have h1 : pushShellRadial η p = pushShellRadial η q := h
      unfold pushShellRadial at h1
      rw [h1, ht]
    exact smul_right_injective _ hpos h'
  exact Prod.ext (Subtype.ext hz) (Subtype.ext ht)

theorem contMDiff_pushShellRadial (η : ℝ) :
    ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ (pushShellRadial η) := by
  have ht : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
      (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1 =>
        1 + η * (p.2 : ℝ)) := by
    have hs : ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ (fun z : Icc (0 : ℝ) 1 => (z : ℝ)) :=
      contMDiff_subtypeVal_Icc
    have ha : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => 1 + η * t) :=
      (contDiff_const.add (contDiff_const.mul contDiff_id)).contMDiff
    exact ha.comp (hs.comp contMDiff_snd)
  exact ht.smul (contMDiff_coe_sphere.comp contMDiff_fst)

theorem mfderiv_pushShellRadial_bijective {η : ℝ} (hη : 0 < η)
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1) :
    Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) (pushShellRadial η) p) := by
  let e : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1 →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ := Prod.map id Subtype.val
  have hs : IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ (fun z : Icc (0 : ℝ) 1 => (z : ℝ)) :=
    isSmoothEmbedding_subtypeVal_Icc
  have he : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e :=
    contMDiff_id.prodMap hs.contMDiff
  have hBe : Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e p) := by
    have hBs : Bijective (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (fun z : Icc (0 : ℝ) 1 => (z : ℝ)) p.2) :=
      bijective_mfderiv_of_isImmersionAt (𝓡∂ 1) 𝓘(ℝ, ℝ) _ p.2
        (hs.isImmersion.isImmersionAt p.2) (by simp)
    rw [mfderiv_prodMap mdifferentiableAt_id (hs.contMDiff.mdifferentiable (by simp) _), mfderiv_id]
    exact Function.bijective_id.prodMap hBs
  let R : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) ∞ :=
    (Diffeomorph.refl (𝓡 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞).prodCongr
      (pushAffine 1 η hη.ne')
  let g : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ → EuclideanSpace ℝ (Fin 3) :=
    fun q => (R q).2 • ((R q).1 : EuclideanSpace ℝ (Fin 3))
  have hpos : 0 < (R (e p)).2 := by
    change 0 < 1 + η * (p.2 : ℝ)
    nlinarith [p.2.2.1]
  have hg : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ g (e p) :=
    (R.isLocalDiffeomorph (e p)).comp (𝓡 3) (EuclideanSpace ℝ (Fin 3))
      (DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_sphere_smul (R (e p)) hpos)
  have hBg : Bijective (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) g (e p)) :=
    (hg.mfderivToContinuousLinearEquiv (by simp)).bijective
  have hcomp : pushShellRadial η = g ∘ e := rfl
  rw [hcomp, mfderiv_comp p (hg.mdifferentiableAt (by simp)) (he.mdifferentiableAt (by simp))]
  exact hBg.comp hBe

/-- The collar radial map `(z, s) ↦ (1 + η + η s / 4) z`. -/
def pushCollarRadial (η : ℝ) (q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) :
    EuclideanSpace ℝ (Fin 3) :=
  (1 + η + η / 4 * q.2) • (q.1 : EuclideanSpace ℝ (Fin 3))

theorem norm_pushCollarRadial {η : ℝ}
    (q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) (hq : 0 ≤ 1 + η + η / 4 * q.2) :
    ‖pushCollarRadial η q‖ = 1 + η + η / 4 * q.2 := by
  rw [pushCollarRadial, norm_smul, Real.norm_eq_abs, abs_of_nonneg hq, norm_eq_of_mem_sphere,
    mul_one]

theorem isLocalDiffeomorphAt_pushCollarRadial {η : ℝ} (hη : 0 < η)
    (q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) (hq : 0 < 1 + η + η / 4 * q.2) :
    IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (pushCollarRadial η) q := by
  let R : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) ∞ :=
    (Diffeomorph.refl (𝓡 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞).prodCongr
      (pushAffine (1 + η) (η / 4) (by positivity))
  have hpos : 0 < (R q).2 := hq
  exact (R.isLocalDiffeomorph q).comp (𝓡 3) (EuclideanSpace ℝ (Fin 3))
    (DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_sphere_smul (R q) hpos)

/-! ## The chart radius -/

section ChartRadius

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y]
  (c : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡 3) (EuclideanSpace ℝ (Fin 3)) Y ∞)

open Classical in
/-- The chart radius `min ‖c⁻¹ y‖ (3/2)` on the chart ball of radius `2`, `3/2` off it. -/
def chartRadius (y : Y) : ℝ :=
  if y ∈ c '' Metric.ball 0 2 then min ‖c.symm y‖ (3 / 2) else 3 / 2

variable {c}

theorem chartRadius_chart (hc : Metric.closedBall 0 2 ⊆ c.source)
    {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ < 2) : chartRadius c (c v) = min ‖v‖ (3 / 2) := by
  have hvs : v ∈ c.source := hc (mem_closedBall_zero_iff.mpr hv.le)
  have hl : c.symm (c v) = v := c.toPartialEquiv.left_inv hvs
  unfold chartRadius
  rw [ite_eq_left ⟨v, mem_ball_zero_iff.mpr hv, rfl⟩, hl]

theorem chartRadius_le (y : Y) : chartRadius c y ≤ 3 / 2 := by
  unfold chartRadius
  split_ifs
  · exact min_le_right _ _
  · exact le_rfl

/-- A point of chart radius below `3/2` is a chart point of that norm. -/
theorem exists_chart_of_chartRadius_lt (hc : Metric.closedBall 0 2 ⊆ c.source) {y : Y}
    (hy : chartRadius c y < 3 / 2) :
    ∃ v : EuclideanSpace ℝ (Fin 3), ‖v‖ < 3 / 2 ∧ c v = y ∧ chartRadius c y = ‖v‖ := by
  by_cases hin : y ∈ c '' Metric.ball 0 2
  · obtain ⟨v, hv, rfl⟩ := hin
    have hv2 := mem_ball_zero_iff.mp hv
    rw [chartRadius_chart hc hv2] at hy ⊢
    have hv32 : ‖v‖ < 3 / 2 := by
      by_contra h
      rw [min_eq_right (not_lt.mp h)] at hy
      exact lt_irrefl _ hy
    exact ⟨v, hv32, rfl, min_eq_left hv32.le⟩
  · unfold chartRadius at hy
    rw [ite_eq_right hin] at hy
    exact (lt_irrefl _ hy).elim

theorem continuous_chartRadius [T2Space Y] (hc : Metric.closedBall 0 2 ⊆ c.source) :
    Continuous (chartRadius c) := by
  refine continuous_iff_continuousAt.mpr fun y => ?_
  by_cases hin : y ∈ c '' Metric.ball 0 2
  · have hU := isOpen_chart_image_ball hc
    have hev : chartRadius c =ᶠ[𝓝 y] fun y' => min ‖c.symm y'‖ (3 / 2) := by
      filter_upwards [hU.mem_nhds hin] with y' hy'
      unfold chartRadius
      rw [ite_eq_left hy']
    have hyt : y ∈ c.target := by
      obtain ⟨v, hv, rfl⟩ := hin
      exact c.map_source (hc (Metric.ball_subset_closedBall hv))
    have hcs : ContinuousAt c.symm y :=
      c.symm.contMDiffOn.continuousOn.continuousAt (c.open_target.mem_nhds hyt)
    have hc' : ContinuousAt (fun y' => min ‖c.symm y'‖ (3 / 2 : ℝ)) y :=
      hcs.norm.min continuousAt_const
    exact hc'.congr_of_eventuallyEq hev
  · have hy32 : y ∉ c '' Metric.closedBall 0 (3 / 2) := fun h =>
      hin (image_mono (Metric.closedBall_subset_ball (by norm_num)) h)
    have hev : chartRadius c =ᶠ[𝓝 y] fun _ => 3 / 2 := by
      filter_upwards [(isClosed_chart_image_closedBall hc (by norm_num)).isOpen_compl.mem_nhds hy32]
        with y' hy'
      by_cases hin' : y' ∈ c '' Metric.ball 0 2
      · obtain ⟨v, hv, rfl⟩ := hin'
        rw [chartRadius_chart hc (mem_ball_zero_iff.mp hv)]
        refine min_eq_right (not_lt.mp fun hlt => hy' ⟨v, ?_, rfl⟩)
        exact mem_closedBall_zero_iff.mpr hlt.le
      · unfold chartRadius
        rw [ite_eq_right hin']
    exact continuousAt_const.congr_of_eventuallyEq hev

end ChartRadius

end GC.GraphManifold.Assembly
