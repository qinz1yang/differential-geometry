import DifferentialGeometry.Geometry.Curvature.Closure
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Basic
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FixedRegions

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold TopologicalSpace DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Manifold.Attachment DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology InnerProductSpace
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private theorem radialBilinearField_gram (a : ℝ → ℝ) {x : E3} (hx : x ≠ 0) (u v : E3) :
    let r := ‖x‖
    let uT := u - (⟪x, u⟫_ℝ / r ^ 2) • x
    let vT := v - (⟪x, v⟫_ℝ / r ^ 2) • x
    radialBilinearField a x u u * radialBilinearField a x v v -
      radialBilinearField a x u v ^ 2 =
      a r ^ 2 / r ^ 4 * ‖⟪x, u⟫_ℝ • v - ⟪x, v⟫_ℝ • u‖ ^ 2 +
        a r ^ 4 / r ^ 4 * (‖uT‖ ^ 2 * ‖vT‖ ^ 2 - ⟪uT, vT⟫_ℝ ^ 2) := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  dsimp only
  simp only [radialBilinearField_apply, ← real_inner_self_eq_norm_sq,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_comm]
  rw [real_inner_self_eq_norm_sq x]
  field_simp
  ring

theorem metricRm04_round_region {x : E3} (hx : ‖x‖ < transitionStart) (u v : E3) :
    metricRm04StandardAt metric x u v v u = (1 / 2 : ℝ) *
      (metric.inner x u u * metric.inner x v v - metric.inner x u v ^ 2) := by
  by_cases hx0 : x = 0
  · subst x
    rw [metricRm04_zero, metric_inner_zero, metric_inner_zero, metric_inner_zero]
  · have hr := norm_pos_iff.mpr hx0
    have ha := (warpingFunction_pos hr).ne'
    have hrad := radialSectionalValue_round hx
    rw [radialSectionalValue_of_pos hr] at hrad
    have htang := tangentialSectionalValue_round hx
    rw [tangentialSectionalValue_of_pos hr] at htang
    have hdd : deriv (deriv warpingFunction) ‖x‖ = -(1 / 2 : ℝ) * warpingFunction ‖x‖ := by
      have h := (div_eq_iff ha).mp hrad
      linarith
    have hd : 1 - deriv warpingFunction ‖x‖ ^ 2 = (1 / 2 : ℝ) * warpingFunction ‖x‖ ^ 2 :=
      (div_eq_iff (pow_ne_zero 2 ha)).mp htang
    have hnum := metricRm04StdAt_radialBilinearField_plane metric (metric_eventually_radial hx0)
      contDiff_warpingFunction hx0 ha u v
    have hgram := radialBilinearField_gram warpingFunction hx0 u v
    rw [metric_inner_of_ne_zero hx0, metric_inner_of_ne_zero hx0, metric_inner_of_ne_zero hx0]
    rw [hgram]
    erw [hnum]
    rw [hdd, hd]
    ring

theorem sectionalCurvature_round_region {x : E3} (hx : ‖x‖ < transitionStart) (u v : E3)
    (hplane : metric.inner x u u * metric.inner x v v - metric.inner x u v ^ 2 ≠ 0) :
    sectionalCurvature metric x u v = 1 / 2 := by
  exact (sectionalCurvature_eq_metricRm04StandardAt_div metric x u v).trans
    ((congrArg (fun t : ℝ => t /
      (metric.inner x u u * metric.inner x v v - metric.inner x u v ^ 2))
      (metricRm04_round_region hx u v)).trans (mul_div_cancel_right₀ _ hplane))

theorem fixed_positive_region_uniform_margin (A : ℝ) :
    ∀ x ∈ positiveRegion A, ∀ u v : TangentSpace (𝓡 3) x,
      metric.inner x u u * metric.inner x v v - metric.inner x u v ^ 2 ≠ 0 →
        sectionalCurvature metric x u v = 1 / 2 := by
  have hs : 0 < Real.sqrt 2 := by positivity
  have hs2 : Real.sqrt 2 ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hhalf : (1 / 2 : ℝ) ≤ transitionStart := by
    unfold transitionStart
    have hratio : 1 ≤ Real.pi / Real.sqrt 2 := (le_div_iff₀ hs).mpr (by linarith [Real.two_le_pi])
    linarith
  have hd : deepRadius A < 1 := (fixed_radii_bounds A).2.2.1.trans_le (min_le_left _ _)
  have hp : positiveRadius A < 1 / 2 := by
    unfold positiveRadius
    exact (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr hd
  intro x hx u v hplane
  exact sectionalCurvature_round_region ((hx.trans_lt hp).trans_le hhalf) u v hplane

private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace E3 (InsertionQuotient hB) := radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) := radialCapAttachment_isManifold transitionEnd_pos hB
private local instance quotientT2Space {B : ℝ} {hB : 0 < B} :
    T2Space (InsertionQuotient hB) := radialCapAttachment_t2Space transitionEnd_pos hB

private local instance (O : Opens E3) : SigmaCompactSpace O :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) O.isOpen)

private theorem insertedMetric_Rm_inner {A B η : ℝ} (hA : 0 < A) (hAB : 2 * A < B)
    (hη : 0 < η) (h : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ)) (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (x : insertionBall B) (hx : ‖x.val‖ < conformalRadius (-7 * A / 4))
    (u v w z : TangentSpace (𝓡 3) x) :
    metricRm04StandardAt (insertedMetric hA hAB hη h) x u v w z =
      η * metricRm04StandardAt metric x.val u v w z := by
  let U : Opens (insertionBall B) :=
    ⟨{y | ‖y.val‖ < conformalRadius (-7 * A / 4)},
      isOpen_lt continuous_subtype_val.norm continuous_const⟩
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) U.isOpen)
  have heq : ∀ y : insertionBall B, y ∈ U → ∀ a b : TangentSpace (𝓡 3) y,
      (insertedMetric hA hAB hη h).inner y a b =
        (scaleMetric η hη (metric.restrictOpen (insertionBall B))).inner y a b := by
    intro y hy a b
    rw [scaleMetric_inner, SmoothRiemannianMetric.restrictOpen_inner]
    exact insertedMetric_inner_of_inner hA hAB hη h y hy a b
  have hc := DifferentialGeometry.Geometry.Curvature.metricRm04StdAt_eq_of_eqOn_closure
    (insertedMetric hA hAB hη h) (scaleMetric η hη (metric.restrictOpen (insertionBall B)))
    U heq x (subset_closure hx) u v w z
  rw [metricRmStandard_scale, metricRm04StandardAt_restrictOpen, mfderiv_subtype_val] at hc
  exact hc

theorem normalizedDatum_positiveSideInsertionMetric_fixed_positive_sectional
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
    (d : DifferentialGeometry.Geometry.Neck.normalizedDatum g x₀ δ k) {A : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹)
    (x : {x : E3 // ‖x‖ ≤ transitionEnd}) (hx : x.val ∈ positiveRegion A) :
    let p := adjunctionCell (radialCapBoundary transitionEnd_pos)
      (retainedBoundary (inv_pos.mpr d.precision_pos)) x
    let out := d.positiveSideInsertionMetric hA hAB
    ∀ u v : TangentSpace (𝓡 3) p,
      out.inner p u u * out.inner p v v - out.inner p u v ^ 2 ≠ 0 →
        sectionalCurvature out p u v = metricScalarAt g x₀ / (2 * (1 - Real.sqrt δ)) := by
  let p := adjunctionCell (radialCapBoundary transitionEnd_pos)
    (retainedBoundary (inv_pos.mpr d.precision_pos)) x
  let out := d.positiveSideInsertionMetric hA hAB
  let e := radialCapAttachmentDiffeomorph transitionEnd_pos (inv_pos.mpr d.precision_pos)
  let D := mfderiv (𝓡 3) (𝓡 3) e p
  let η := 1 - Real.sqrt δ
  let Q := metricScalarAt g x₀
  let c := Q⁻¹ * η
  have hη : 0 < η := d.controlledMetric_cylinder_lower.1
  have hQ : 0 < Q := d.scalar_pos
  have hpoint : (e p : E3) = x.val := rfl
  have hinner : ‖(e p : E3)‖ < conformalRadius (-7 * A / 4) := by
    rw [hpoint]
    exact (hx.trans_lt (fixed_radii_bounds A).2.1).trans (fixed_radii_bounds A).2.2.2
  have hm (a b : TangentSpace (𝓡 3) p) :
      out.inner p a b = c * metric.inner x.val (D a) (D b) := by
    change (scaleMetric Q⁻¹ (inv_pos.mpr hQ)
      (insertedQuotientMetric hA hAB hη d.controlledMetric)).inner p a b = _
    rw [scaleMetric_inner, insertedQuotientMetric_inner]
    have h := insertedMetric_inner_of_inner hA hAB hη d.controlledMetric (e p) hinner (D a) (D b)
    change Q⁻¹ * (insertedMetric hA hAB hη d.controlledMetric).inner (e p) (D a) (D b) = _
    rw [h]
    change Q⁻¹ * (η * metric.inner x.val (D a) (D b)) = c * metric.inner x.val (D a) (D b)
    ring
  dsimp only
  intro u v hplane
  let G := metric.inner x.val (D u) (D u) * metric.inner x.val (D v) (D v) -
    metric.inner x.val (D u) (D v) ^ 2
  have hgram : out.inner p u u * out.inner p v v - out.inner p u v ^ 2 = c ^ 2 * G := by
    rw [hm, hm, hm]
    dsimp only [G]
    ring
  have hG : G ≠ 0 := by
    intro h
    apply hplane
    change out.inner p u u * out.inner p v v - out.inner p u v ^ 2 = 0
    rw [hgram, h, mul_zero]
  have hs := fixed_positive_region_uniform_margin A x.val hx (D u) (D v) hG
  have hsrc : metricRm04StandardAt metric x.val (D u) (D v) (D v) (D u) = (1 / 2 : ℝ) * G :=
    (div_eq_iff hG).mp ((sectionalCurvature_eq_metricRm04StandardAt_div metric x.val (D u) (D v)).symm.trans hs)
  have hn : metricRm04StandardAt out p u v v u =
      c * metricRm04StandardAt metric x.val (D u) (D v) (D v) (D u) := by
    have hscale := metricRmStandard_scale Q⁻¹ (inv_pos.mpr hQ)
      (insertedQuotientMetric hA hAB hη d.controlledMetric) p u v v u
    have hp := metricRm04Standard_pullback (insertedMetric hA hAB hη d.controlledMetric) e p u v v u
    have hb := insertedMetric_Rm_inner hA hAB hη d.controlledMetric (e p) hinner (D u) (D v) (D v) (D u)
    have hr : metricRm04StandardAt (insertedQuotientMetric hA hAB hη d.controlledMetric) p u v v u =
        η * metricRm04StandardAt metric x.val (D u) (D v) (D v) (D u) := hp.trans hb
    exact hscale.trans ((congrArg (fun t : ℝ => Q⁻¹ * t) hr).trans (by dsimp only [c]; ring))
  change sectionalCurvature out p u v = Q / (2 * η)
  rw [sectionalCurvature_eq_metricRm04StandardAt_div, hn, hsrc, hgram]
  dsimp only [c]
  field_simp [hG, hQ.ne', hη.ne']

end DifferentialGeometry.PDE.RicciFlow.StandardCap
