import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SingleTimeHLow_O81
import DifferentialGeometry.Geometry.Curvature.Bounds.SectionalPerturbationUpper
import DifferentialGeometry.Geometry.Curvature.Bounds.RiemannTensorOperator

set_option autoImplicit false

/-! # CH12-O81 G3 (part B): universal single-time curvature window and volume upper bound.

* `hLow1_single_O81`: `sec ≥ -1` on `B(φ y, 1)` with the UNIVERSAL radius `c₀ = 1`
  (`cusp_sectional_pinching_of_small_metric_derivatives`: `ε ≤ 1/4000`, `|Rm_h| ≤ 1`, `sec_h = -1/4`
  ⇒ `sec ≥ -1/2`), replacing the model-dependent constant of `hLow_single_O81`.
* `ball_subset_image_single_O81`, `image_volume_upper_single_O81`, `ballVolume_upper_single_O81`:
  single-time copies of `bufferedMap_ball_subset_image / image_volume_le / ballVolume_le_O27`.
* `thick_core_single_O81`: the real curvature radius `r ∈ [1, √8]` at `φ y` with
  `(2/3) vol_H B(y, 1/2) ≤ vol B(φ y, r) ≤ 2 vol_H B(y, 4)`. -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set Filter
open Manifold GC.LongTime DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal Topology
universe u
namespace GC.LongTime.Ch12

section Single

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {Hm : FiniteVolumeHyperbolicModel.{u}} {s δ : ℝ} {U : TopologicalSpace.Opens Hm.Carrier}
  {φ : Hm.Carrier → (postStage F.observation s).Carrier}

/-- Universal single-time `hLow` (`c₀ = 1`). -/
theorem hLow1_single_O81 (hs : 0 < s) (hsm : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ U)
    (hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun x : U => φ x) ∧
      Function.Injective (fun x : U => φ x))
    (hU : riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹) ⊆ U)
    (hck : ∀ k : ℕ, k ≤ 2 → ∀ p ∈ riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹),
      ckErr_S45 Hm (postMetric F.observation s) s⁻¹ φ k p < δ)
    (hδ : 0 < δ) (hacc1 : δ ≤ 1 / 10000)
    (y : Hm.Carrier) (hy : y ∈ riemannianBallOf Hm.metric Hm.basepoint δ⁻¹) :
    ∀ q ∈ riemannianBallOf (scaleMetric s⁻¹ (inv_pos.mpr hs) (postMetric F.observation s)) (φ y) 1,
      SectionalBoundedBelowAt (scaleMetric s⁻¹ (inv_pos.mpr hs) (postMetric F.observation s))
        q (-((1 : ℝ) ^ 2)⁻¹) := by
  intro q hq
  have hnpos : 0 < δ⁻¹ := inv_pos.mpr hδ
  have hn : (10000 : ℝ) ≤ δ⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hδ]
    simpa using hacc1
  have hyd : y ∈ U := hU (riemannianBallOf_mono _ _ (by linarith) hy)
  have hsource : riemannianClosedBallOf Hm.metric y 4 ⊆ (U : Set _) :=
    fun z hz => hU (closedBall_subset_buffer_single_O81 hδ y hy (by linarith) hz)
  have hlow4 : ∀ x ∈ riemannianClosedBallOf Hm.metric y 4, ∀ v : TangentSpace (𝓡 3) x,
      Hm.metric.inner x v v ≤ (2 : ℝ) ^ 2 *
        (scaleMetric s⁻¹ (inv_pos.mpr hs) (postMetric F.observation s)).inner (φ x)
          (mfderiv (𝓡 3) (𝓡 3) φ x v) (mfderiv (𝓡 3) (𝓡 3) φ x v) := by
    intro x hx v
    have hlo := metric_lower_single_O81 hs hck x
      (closedBall_subset_buffer_single_O81 hδ y hy (by linarith) hx) v
    have hnn := metric_inner_self_nonneg Hm.metric x v
    have hacc : δ ≤ 1 / 2 := by linarith
    nlinarith
  have hcap := ambient_ball_subset_image_single_O81 hsm hf
    (scaleMetric s⁻¹ (inv_pos.mpr hs) (postMetric F.observation s))
    y hyd (R := 4) (L := 2) (by norm_num) (by norm_num) hsource hlow4
  obtain ⟨z, hz4, rfl⟩ := hcap (riemannianBallOf_mono _ _ (by norm_num) hq)
  have hz2 : z ∈ riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹) :=
    closedBall_subset_buffer_single_O81 hδ y hy (by linarith) hz4
  obtain ⟨q', hq', hiff⟩ := curvature_bridge_single_O81 hsm hf hU hck
    (scaleMetric s⁻¹ (inv_pos.mpr hs) (postMetric F.observation s))
    (fun w => by
      ext a b
      simp only [localPullInner_apply, scaleMetric_inner, smul_apply, smul_eq_mul])
    z hz2
  have hsec : ∀ a b : TangentSpace (𝓡 3) z,
      metricRm04StandardAt Hm.metric z a b b a =
        -(1 / 4 : ℝ) * (Hm.metric.inner z a a * Hm.metric.inner z b b -
          Hm.metric.inner z a b ^ 2) := fun a b => by
    rw [metricRm_eq_neg_quarter_S26 Hm z a b]; ring
  have hnorm := normSq0S_metricRm04At_eq_of_constant_sectional_numerator
    Hm.metric z (-(1 / 4 : ℝ)) hsec
  have hrank : (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ) = 3 := by simp
  rw [hrank] at hnorm
  have hRm1 : Real.sqrt (normSq0S Hm.metric z 4 (metricRm04At Hm.metric z)) ≤ 1 :=
    Real.sqrt_le_one.mpr (by rw [hnorm]; norm_num)
  have hmodel : ∀ u v w : TangentSpace (𝓡 3) z,
      let r := riemannOp (LeviCivita Hm.metric) z u v w
      Real.sqrt (Hm.metric.inner z r r) ≤
        1 * Real.sqrt (Hm.metric.inner z u u) * Real.sqrt (Hm.metric.inner z v v) *
          Real.sqrt (Hm.metric.inner z w w) := by
    intro u v w
    have h := sqrt_inner_riemannOp_le Hm.metric z u v w
    have hu := Real.sqrt_nonneg (Hm.metric.inner z u u)
    have hv := Real.sqrt_nonneg (Hm.metric.inner z v v)
    have hw := Real.sqrt_nonneg (Hm.metric.inner z w w)
    have huvw : 0 ≤ Real.sqrt (Hm.metric.inner z u u) * Real.sqrt (Hm.metric.inner z v v) *
        Real.sqrt (Hm.metric.inner z w w) := by positivity
    refine h.trans ?_
    have := mul_le_mul_of_nonneg_right hRm1 huvw
    simpa only [mul_assoc] using this
  have hpin := (cusp_sectional_pinching_of_small_metric_derivatives q' Hm.metric z
    (ε := δ) (K := 1) (by linarith) (by norm_num) (fun k hk => (hq' k hk).le) hmodel
    (fun a b => by rw [metricRm_eq_neg_quarter_S26 Hm z a b]; ring)).1
  exact ((hiff _).mp hpin).mono (by norm_num)

theorem ball_subset_image_single_O81 (hs : 0 < s) (hsm : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ U)
    (hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun x : U => φ x) ∧
      Function.Injective (fun x : U => φ x))
    (hU : riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹) ⊆ U)
    (hck : ∀ k : ℕ, k ≤ 2 → ∀ p ∈ riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹),
      ckErr_S45 Hm (postMetric F.observation s) s⁻¹ φ k p < δ)
    (hδ0 : 0 < δ) (y : Hm.Carrier) (hy : y ∈ riemannianBallOf Hm.metric Hm.basepoint δ⁻¹)
    {R : ℝ} (hR : 0 < R) (hRn : R ≤ δ⁻¹) (hδ : δ < 1) :
    riemannianBallOf (scaleMetric s⁻¹ (inv_pos.mpr hs) (postMetric F.observation s))
        (φ y) (R * Real.sqrt (1 - δ)) ⊆ φ '' riemannianClosedBallOf Hm.metric y R := by
  have hsub := closedBall_subset_buffer_single_O81 hδ0 y hy hRn
  have hpos : 0 < 1 - δ := sub_pos.mpr hδ
  have hsq : 0 < Real.sqrt (1 - δ) := Real.sqrt_pos.mpr hpos
  have hnpos : 0 < δ⁻¹ := inv_pos.mpr hδ0
  have hy2 : y ∈ riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹) :=
    riemannianBallOf_mono _ _ (by linarith) hy
  have hcap := ambient_ball_subset_image_single_O81 hsm hf
    (scaleMetric s⁻¹ (inv_pos.mpr hs) (postMetric F.observation s)) y
    (hU hy2) hR (inv_pos.mpr hsq : 0 < (Real.sqrt (1 - δ))⁻¹)
    (fun x hx => hU (hsub hx))
    (fun x hx v => by
      have hlow := metric_lower_single_O81 hs hck x (hsub hx) v
      have hnn := metric_inner_self_nonneg Hm.metric x v
      have hL : ((Real.sqrt (1 - δ))⁻¹) ^ 2 = (1 - δ)⁻¹ := by
        rw [inv_pow, Real.sq_sqrt hpos.le]
      rw [hL, inv_mul_eq_div, le_div_iff₀ hpos]
      linarith)
  have hRL : R / (Real.sqrt (1 - δ))⁻¹ = R * Real.sqrt (1 - δ) := by
    rw [div_inv_eq_mul]
  rwa [hRL] at hcap

theorem image_volume_upper_single_O81 (hs : 0 < s) (hsm : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ U)
    (hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun x : U => φ x) ∧
      Function.Injective (fun x : U => φ x))
    (hU : riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹) ⊆ U)
    (hck : ∀ k : ℕ, k ≤ 2 → ∀ p ∈ riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹),
      ckErr_S45 Hm (postMetric F.observation s) s⁻¹ φ k p < δ)
    (hδ0 : 0 < δ) (y : Hm.Carrier) (hy : y ∈ riemannianBallOf Hm.metric Hm.basepoint δ⁻¹)
    {R : ℝ} (hRn : R ≤ δ⁻¹) (hδ : δ ≤ 1 / 4) :
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (𝓡 3)
        (postStage F.observation s).Carrier
        (scaleMetric s⁻¹ (inv_pos.mpr hs) (postMetric F.observation s))
        (φ '' riemannianClosedBallOf Hm.metric y R) ≤
      ENNReal.ofReal 2 *
        DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (𝓡 3) Hm.Carrier
          Hm.metric (riemannianClosedBallOf Hm.metric y R) := by
  classical
  let : MeasurableSpace Hm.Carrier := borel _
  have : BorelSpace Hm.Carrier := ⟨rfl⟩
  let : MeasurableSpace (postStage F.observation s).Carrier := borel _
  have : BorelSpace (postStage F.observation s).Carrier := ⟨rfl⟩
  let : MeasurableSpace U := borel _
  have : BorelSpace U := ⟨rfl⟩
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) U.isOpen)
  obtain ⟨hf, hinj⟩ := hf
  have hsub := closedBall_subset_buffer_single_O81 hδ0 y hy hRn
  have hAU : riemannianClosedBallOf Hm.metric y R ⊆ (U : Set _) := fun x hx => hU (hsub hx)
  have hAclosed : IsClosed (riemannianClosedBallOf Hm.metric y R) :=
    isClosed_le (Geometry.Riemannian.continuous_riemannianEDist Hm.metric y) continuous_const
  have hSclosed : IsClosed ((Subtype.val : U → _) ⁻¹' riemannianClosedBallOf Hm.metric y R) :=
    hAclosed.preimage continuous_subtype_val
  let f : U → (postStage F.observation s).Carrier := fun x => φ x
  set gb := scaleMetric s⁻¹ (inv_pos.mpr hs) (postMetric F.observation s) with hgb
  let gp := DifferentialGeometry.Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph gb f hf hinj
  have hmetric : ∀ (x : U) (v w : TangentSpace (𝓡 3) x), gp.inner x v w =
      gb.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) :=
    DifferentialGeometry.Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph_inner gb f hf hinj
  have h1 := DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry
    gp gb f hf hinj hmetric hSclosed.measurableSet
  have himg : f '' (Subtype.val ⁻¹' riemannianClosedBallOf Hm.metric y R) =
      φ '' riemannianClosedBallOf Hm.metric y R := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.val, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hAU hx⟩, hx, rfl⟩
  rw [← himg, ← h1]
  have hS2 := Geometry.Measure.riemannianVolumeMeasure_restrictOpen_preimage_of_subset
    Hm.metric U hAclosed.measurableSet hAU
  have hcomp : ∀ x ∈ (Subtype.val ⁻¹' riemannianClosedBallOf Hm.metric y R : Set U),
      ∀ v : TangentSpace (𝓡 3) x,
      gp.inner x v v ≤ (5 / 4 : ℝ) * (Hm.metric.restrictOpen U).inner x v v := by
    intro x hx v
    have hmd : MDifferentiableAt (𝓡 3) (𝓡 3) φ x.val :=
      (hsm.mdifferentiableOn (by simp) x.val x.2).mdifferentiableAt (U.isOpen.mem_nhds x.2)
    have hcomp : mfderiv (𝓡 3) (𝓡 3) f x =
        (mfderiv (𝓡 3) (𝓡 3) φ x.val).comp (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → _) x) :=
      mfderiv_comp x hmd (hasMFDerivAt_subtype_val (I := 𝓡 3) U x).mdifferentiableAt
    rw [hmetric, hcomp]
    simp only [ContinuousLinearMap.comp_apply, mfderiv_subtype_val_apply]
    have hup := metric_upper_single_O81 hs hck x.val (hsub hx) v
    have hnn := metric_inner_self_nonneg Hm.metric x.val v
    have hδ' : (1 + δ) ≤ 5 / 4 := by linarith
    calc _ ≤ (1 + δ) * Hm.metric.inner x.val v v := hup
      _ ≤ _ := mul_le_mul_of_nonneg_right hδ' hnn
  have hle := DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.riemannianVolumeMeasure_le_on
    (Hm.metric.restrictOpen U) gp hSclosed.measurableSet (by norm_num : (0 : ℝ) < 5 / 4) hcomp
  rw [hS2] at hle
  refine hle.trans (mul_le_mul' ?_ le_rfl)
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.sqrt_le_iff]
  refine ⟨by norm_num, ?_⟩
  have : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  rw [this]
  norm_num

theorem ballVolume_upper_single_O81 (hs : 0 < s) (hsm : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ U)
    (hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun x : U => φ x) ∧
      Function.Injective (fun x : U => φ x))
    (hU : riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹) ⊆ U)
    (hck : ∀ k : ℕ, k ≤ 2 → ∀ p ∈ riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹),
      ckErr_S45 Hm (postMetric F.observation s) s⁻¹ φ k p < δ)
    (hδ0 : 0 < δ) (y : Hm.Carrier) (hy : y ∈ riemannianBallOf Hm.metric Hm.basepoint δ⁻¹)
    (hδ : δ ≤ 1 / 4) {r : ℝ} (hr : 0 < r) (hr8 : r ^ 2 ≤ 8) :
    ballVolume (scaleMetric s⁻¹ (inv_pos.mpr hs) (postMetric F.observation s)) (φ y) r ≤
      ENNReal.ofReal 2 * ballVolume Hm.metric y 4 := by
  have hpos : 0 < 1 - δ := by linarith
  have hsq : 0 < Real.sqrt (1 - δ) := Real.sqrt_pos.mpr hpos
  have hn4 : 4 ≤ δ⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hδ0]
    norm_num
    exact hδ
  set R : ℝ := r / Real.sqrt (1 - δ) with hR
  have hRr : R * Real.sqrt (1 - δ) = r := by
    rw [hR]; field_simp
  have hRpos : 0 < R := div_pos hr hsq
  have hR2 : R ^ 2 * (1 - δ) = r ^ 2 := by
    rw [← hRr, mul_pow, Real.sq_sqrt hpos.le]
  have hR4 : R < 4 := by
    have : R ^ 2 < 4 ^ 2 := by nlinarith [sq_nonneg R]
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) this
  have hcap := ball_subset_image_single_O81 hs hsm hf hU hck hδ0 y hy hRpos (hR4.le.trans hn4)
    (by linarith)
  rw [hRr] at hcap
  have hvol := image_volume_upper_single_O81 hs hsm hf hU hck hδ0 y hy (hR4.le.trans hn4) hδ
  have hclosed : riemannianClosedBallOf Hm.metric y R ⊆ riemannianBallOf Hm.metric y 4 := by
    intro x hx
    exact lt_of_le_of_lt hx ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hR4)
  unfold ballVolume
  calc _ ≤ _ := MeasureTheory.measure_mono hcap
    _ ≤ _ := hvol
    _ ≤ _ := mul_le_mul' le_rfl (MeasureTheory.measure_mono hclosed)

/-- Real curvature radius `r ∈ [1, √8]` at `φ y` and the two-sided volume window. -/
theorem thick_core_single_O81 (hs : 0 < s) (hsm : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ U)
    (hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun x : U => φ x) ∧
      Function.Injective (fun x : U => φ x))
    (hU : riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹) ⊆ U)
    (hck : ∀ k : ℕ, k ≤ 2 → ∀ p ∈ riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹),
      ckErr_S45 Hm (postMetric F.observation s) s⁻¹ φ k p < δ)
    (hδ : 0 < δ) (hacc1 : δ ≤ 1 / 10000)
    (y : Hm.Carrier) (hy : y ∈ riemannianBallOf Hm.metric Hm.basepoint δ⁻¹) :
    ∃ r : ℝ, 0 < r ∧
      curvatureRadius (scaleMetric s⁻¹ (inv_pos.mpr hs) (postMetric F.observation s)) (φ y) =
        ENNReal.ofReal r ∧ 1 ≤ r ∧ r ^ 2 ≤ 8 ∧
      ENNReal.ofReal (2 / 3) * ballVolume Hm.metric y (1 / 2) ≤
        ballVolume (scaleMetric s⁻¹ (inv_pos.mpr hs) (postMetric F.observation s)) (φ y) r ∧
      ballVolume (scaleMetric s⁻¹ (inv_pos.mpr hs) (postMetric F.observation s)) (φ y) r ≤
        ENNReal.ofReal 2 * ballVolume Hm.metric y 4 := by
  have hn : (10000 : ℝ) ≤ δ⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hδ]
    simpa using hacc1
  obtain ⟨r, hr, hcr, hr1, hr8⟩ := exists_curvatureRadius_real_S114 _ _ one_pos
    (hLow1_single_O81 hs hsm hf hU hck hδ hacc1 y hy)
    (hUp_single_O81 hs hsm hf hU hck hδ hacc1 y hy)
  have hr3 : r ≤ 3 := by nlinarith
  refine ⟨r, hr, hcr, hr1, hr8, ?_, ballVolume_upper_single_O81 hs hsm hf hU hck hδ y hy
    (by linarith) hr hr8⟩
  have hB := ball_image_volume_lower_single_O81 hs hsm hf hU hck hδ y hy (by linarith) hr
    (by linarith)
  refine le_trans (mul_le_mul' le_rfl (MeasureTheory.measure_mono ?_)) hB
  exact riemannianBallOf_mono _ _ (by linarith)

end Single

end GC.LongTime.Ch12
