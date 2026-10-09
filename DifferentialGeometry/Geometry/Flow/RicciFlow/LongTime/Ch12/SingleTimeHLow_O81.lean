import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HLowAux_S114
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SingleTimeCurv_O81

set_option autoImplicit false

/-! # CH12-O81 G1 (part B): single-time `HLOW` (`hlow_single_O81`, [FROZEN] CH12-O81).

Single-time copies of `image_volume_lower_S100` and `ball_image_volume_lower_S114`, then the
`HLOW_S114` assembly at ONE map `q` at ONE time `s`: (a) `hUp_single_O81` + `hLow_single_O81` +
`exists_curvatureRadius_real_S114` (real radius `r ∈ [c₀, √8]`); (b) `q '' B_H(y, r/2) ⊆ B(q y, r)`;
(c) image volume `≥ (2/3)` model volume; (d) `exists_uniform_ball_volume_S114`; (e) `w := (2/3) v / 27`.
The embedding of `q` on `B(base, 2/δ)` comes from `InjOn` + `ckErr` order 0 (`localDiffeo_single_O81`). -/

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

/-- Single-time copy of `image_volume_lower_S100` (Jacobian factor `2/3`). -/
theorem image_volume_lower_single_O81 (hs : 0 < s) (hsm : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ U)
    (hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun x : U => φ x) ∧
      Function.Injective (fun x : U => φ x))
    (hU : riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹) ⊆ U)
    (hck : ∀ k : ℕ, k ≤ 2 → ∀ p ∈ riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹),
      ckErr_S45 Hm (postMetric F.observation s) s⁻¹ φ k p < δ)
    (hδ0 : 0 < δ) (y : Hm.Carrier) (hy : y ∈ riemannianBallOf Hm.metric Hm.basepoint δ⁻¹)
    {R : ℝ} (hRn : R ≤ δ⁻¹) (hδ : δ ≤ 1 / 8)
    {S : Set Hm.Carrier} (hS : IsOpen S) (hSR : S ⊆ riemannianClosedBallOf Hm.metric y R) :
    ENNReal.ofReal (2 / 3) *
        DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (𝓡 3) Hm.Carrier Hm.metric S ≤
      DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (𝓡 3)
        (postStage F.observation s).Carrier
        (scaleMetric s⁻¹ (inv_pos.mpr hs) (postMetric F.observation s)) (φ '' S) := by
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
  have hAU : S ⊆ (U : Set _) := fun x hx => hU (hsub (hSR hx))
  have hSopen : IsOpen ((Subtype.val : U → _) ⁻¹' S) := hS.preimage continuous_subtype_val
  let f : U → (postStage F.observation s).Carrier := fun x => φ x
  set gb := scaleMetric s⁻¹ (inv_pos.mpr hs) (postMetric F.observation s) with hgb
  let gp := DifferentialGeometry.Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph gb f hf hinj
  have hmetric : ∀ (x : U) (v w : TangentSpace (𝓡 3) x), gp.inner x v w =
      gb.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) :=
    DifferentialGeometry.Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph_inner gb f hf hinj
  have h1 := DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry
    gp gb f hf hinj hmetric hSopen.measurableSet
  have himg : f '' (Subtype.val ⁻¹' S) = φ '' S := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.val, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hAU hx⟩, hx, rfl⟩
  rw [← himg, ← h1]
  have hS2 := Geometry.Measure.riemannianVolumeMeasure_restrictOpen_preimage_of_subset
    Hm.metric U hS.measurableSet hAU
  have hcomp : ∀ x ∈ (Subtype.val ⁻¹' S : Set U), ∀ v : TangentSpace (𝓡 3) x,
      (Hm.metric.restrictOpen U).inner x v v ≤ (8 / 7 : ℝ) * gp.inner x v v := by
    intro x hx v
    have hmd : MDifferentiableAt (𝓡 3) (𝓡 3) φ x.val :=
      (hsm.mdifferentiableOn (by simp) x.val x.2).mdifferentiableAt (U.isOpen.mem_nhds x.2)
    have hcomp : mfderiv (𝓡 3) (𝓡 3) f x =
        (mfderiv (𝓡 3) (𝓡 3) φ x.val).comp (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → _) x) :=
      mfderiv_comp x hmd (hasMFDerivAt_subtype_val (I := 𝓡 3) U x).mdifferentiableAt
    rw [hmetric, hcomp]
    simp only [ContinuousLinearMap.comp_apply, mfderiv_subtype_val_apply]
    have hlo := metric_lower_single_O81 hs hck x.val (hsub (hSR hx)) v
    have hnn := metric_inner_self_nonneg Hm.metric x.val v
    have hδ' : (7 / 8 : ℝ) ≤ 1 - δ := by linarith
    have h78 : (7 / 8 : ℝ) * Hm.metric.inner x.val v v ≤ gb.inner (φ x.val)
        (mfderiv (𝓡 3) (𝓡 3) φ x.val v) (mfderiv (𝓡 3) (𝓡 3) φ x.val v) :=
      (mul_le_mul_of_nonneg_right hδ' hnn).trans hlo
    change Hm.metric.inner x.val v v ≤ _
    nlinarith
  have hle := DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.riemannianVolumeMeasure_le_on gp
    (Hm.metric.restrictOpen U) hSopen.measurableSet (by norm_num : (0 : ℝ) < 8 / 7) hcomp
  rw [hS2] at hle
  have hc : ENNReal.ofReal (2 / 3) * ENNReal.ofReal
      (Real.sqrt ((8 / 7 : ℝ) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) ≤ 1 := by
    rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
    rw [this]
    have hs' : Real.sqrt ((8 / 7 : ℝ) ^ 3) ≤ 3 / 2 := by
      rw [Real.sqrt_le_iff]
      refine ⟨by norm_num, ?_⟩
      norm_num
    nlinarith [Real.sqrt_nonneg ((8 / 7 : ℝ) ^ 3)]
  calc ENNReal.ofReal (2 / 3) * _ ≤ ENNReal.ofReal (2 / 3) * (ENNReal.ofReal
          (Real.sqrt ((8 / 7 : ℝ) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) * _) :=
        mul_le_mul' le_rfl hle
    _ = (ENNReal.ofReal (2 / 3) * ENNReal.ofReal
          (Real.sqrt ((8 / 7 : ℝ) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))))) * _ := by
        rw [mul_assoc]
    _ ≤ 1 * _ := mul_le_mul' hc le_rfl
    _ = _ := one_mul _

/-- Single-time copy of `ball_image_volume_lower_S114`. -/
theorem ball_image_volume_lower_single_O81 (hs : 0 < s) (hsm : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ U)
    (hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun x : U => φ x) ∧
      Function.Injective (fun x : U => φ x))
    (hU : riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹) ⊆ U)
    (hck : ∀ k : ℕ, k ≤ 2 → ∀ p ∈ riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹),
      ckErr_S45 Hm (postMetric F.observation s) s⁻¹ φ k p < δ)
    (hδ0 : 0 < δ) (y : Hm.Carrier) (hy : y ∈ riemannianBallOf Hm.metric Hm.basepoint δ⁻¹)
    (hδ : δ ≤ 1 / 8) {r : ℝ} (hr : 0 < r) (hrn : r ≤ δ⁻¹) :
    ENNReal.ofReal (2 / 3) *
        DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (𝓡 3) Hm.Carrier Hm.metric
          (riemannianBallOf Hm.metric y (r / 2)) ≤
      ballVolume (scaleMetric s⁻¹ (inv_pos.mpr hs) (postMetric F.observation s)) (φ y) r := by
  have hnpos : 0 < δ⁻¹ := inv_pos.mpr hδ0
  have hS : IsOpen (riemannianBallOf Hm.metric y (r / 2)) := isOpen_riemannianBallOf Hm.metric y (r / 2)
  have hSR : riemannianBallOf Hm.metric y (r / 2) ⊆ riemannianClosedBallOf Hm.metric y (r / 2) :=
    fun z hz => (show riemannianEDistOf Hm.metric y z < ENNReal.ofReal (r / 2) from hz).le
  have h1 := image_volume_lower_single_O81 hs hsm hf hU hck hδ0 y hy (R := r / 2) (by linarith)
    hδ hS hSR
  obtain ⟨hf', hinj⟩ := hf
  have hsub := closedBall_subset_buffer_single_O81 hδ0 y hy hrn
  have hy2 : y ∈ (U : Set Hm.Carrier) := hU (riemannianBallOf_mono _ _ (by linarith) hy)
  set gb := scaleMetric s⁻¹ (inv_pos.mpr hs) (postMetric F.observation s) with hgb
  have hupper : ∀ x : U, x.val ∈ riemannianClosedBallOf Hm.metric y r → ∀ v : TangentSpace (𝓡 3) x,
      gb.inner (φ x.val) (mfderiv (𝓡 3) (𝓡 3) (fun x : U => φ x) x v)
        (mfderiv (𝓡 3) (𝓡 3) (fun x : U => φ x) x v) ≤
        (3 / 2 : ℝ) ^ 2 * Hm.metric.inner x.val v v := by
    intro x hx v
    have hmd : MDifferentiableAt (𝓡 3) (𝓡 3) φ x.val :=
      (hsm.mdifferentiableOn (by simp) x.val x.2).mdifferentiableAt (U.isOpen.mem_nhds x.2)
    have hcomp : mfderiv (𝓡 3) (𝓡 3) (fun x : U => φ x) x =
        (mfderiv (𝓡 3) (𝓡 3) φ x.val).comp (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → _) x) :=
      mfderiv_comp x hmd (hasMFDerivAt_subtype_val (I := 𝓡 3) U x).mdifferentiableAt
    rw [hcomp]
    simp only [ContinuousLinearMap.comp_apply, mfderiv_subtype_val_apply]
    have hup := metric_upper_single_O81 hs hck x.val (hsub hx) v
    have hnn := metric_inner_self_nonneg Hm.metric x.val v
    change gb.inner _ _ _ ≤ _ at hup
    nlinarith
  have hcap := DifferentialGeometry.Geometry.Metric.image_closedBall_subset_ball_of_metric_upper_on_opens
    gb Hm.metric U (fun x : U => φ x) hf' hinj ⟨y, hy2⟩ (r := r / 2) (R := r) (L := 3 / 2) (c := 2)
    (by linarith) (by linarith) (by norm_num) (by norm_num)
    (fun x hx => hU (hsub hx)) hupper
  have hcont : φ '' riemannianBallOf Hm.metric y (r / 2) ⊆ riemannianBallOf gb (φ y) r := by
    rintro _ ⟨z, hz, rfl⟩
    have hzd : z ∈ (U : Set Hm.Carrier) :=
      hU (hsub (riemannianClosedBallOf_mono _ _ (by linarith) (hSR hz)))
    have := hcap ⟨⟨z, hzd⟩, hSR hz, rfl⟩
    have e : (2 : ℝ) * (r / 2) = r := by ring
    rwa [e] at this
  exact h1.trans (MeasureTheory.measure_mono hcont)

end Single

/-- **G1 ([FROZEN] CH12-O81).**  Single-time `HLOW`: one map `q` at one time `s`, accuracy `δ`. -/
theorem hlow_single_O81 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u}) (R : ℝ) :
    ∃ w : ℝ, 0 < w ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 10000 → R ≤ δ⁻¹ →
      ∀ (s : ℝ) (hs : 0 < s) (q : H.Carrier → (postStage F.observation s).Carrier),
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ q (riemannianBallOf H.metric H.basepoint (2 * δ⁻¹)) →
        Set.InjOn q (riemannianBallOf H.metric H.basepoint (2 * δ⁻¹)) →
        (∀ k : ℕ, k ≤ 2 → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * δ⁻¹),
          ckErr_S45 H (postMetric F.observation s) s⁻¹ q k p < δ) →
        ∀ y ∈ riemannianBallOf H.metric H.basepoint R, ∃ r : ℝ, 0 < r ∧
          curvatureRadius (scaleMetric s⁻¹ (inv_pos.mpr hs) (postMetric F.observation s)) (q y) =
            ENNReal.ofReal r ∧
          ENNReal.ofReal (w * r ^ 3) ≤
            ballVolume (scaleMetric s⁻¹ (inv_pos.mpr hs) (postMetric F.observation s)) (q y) r := by
  obtain ⟨c₀, hc₀, hLow⟩ := hLow_single_O81 H
  obtain ⟨v, hv, hvol⟩ := exists_uniform_ball_volume_S114 H R (ρ := c₀ / 2) (by positivity)
  refine ⟨2 / 3 * v / 27, by positivity, fun δ hδ hδ1 hRδ s hs q hsm hinj hck y hy => ?_⟩
  let U : TopologicalSpace.Opens H.Carrier :=
    ⟨riemannianBallOf H.metric H.basepoint (2 * δ⁻¹), isOpen_riemannianBallOf _ _ _⟩
  have hU : riemannianBallOf H.metric H.basepoint (2 * δ⁻¹) ⊆ U := subset_rfl
  have hδ1' : δ ≤ 1 := by linarith
  have hf := localDiffeo_single_O81 (U := U) hsm hinj
    (fun p hp => (hck 0 (Nat.zero_le _) p hp).trans_le hδ1')
  have hn : (10000 : ℝ) ≤ δ⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hδ]
    simpa using hδ1
  have hδ8 : δ ≤ 1 / 8 := by linarith
  have hyB : y ∈ riemannianBallOf H.metric H.basepoint δ⁻¹ := riemannianBallOf_mono _ _ hRδ hy
  have hlow := hLow F s hs δ U q hsm hf hU hck hδ hδ1 y hyB
  have hup := hUp_single_O81 hs hsm hf hU hck hδ hδ1 y hyB
  obtain ⟨r, hr, hcr, hcr1, hr8⟩ := exists_curvatureRadius_real_S114 _ _ hc₀ hlow hup
  refine ⟨r, hr, hcr, ?_⟩
  have hr3 : r ≤ 3 := by nlinarith
  have hr27 : r ^ 3 ≤ 27 := by
    calc r ^ 3 ≤ 3 ^ 3 := pow_le_pow_left₀ hr.le hr3 3
      _ = 27 := by norm_num
  have hB := ball_image_volume_lower_single_O81 hs hsm hf hU hck hδ y hyB hδ8 hr (by linarith)
  have hmono : riemannianBallOf H.metric y (c₀ / 2) ⊆ riemannianBallOf H.metric y (r / 2) :=
    riemannianBallOf_mono _ _ (by linarith)
  refine le_trans ?_ hB
  calc ENNReal.ofReal (2 / 3 * v / 27 * r ^ 3)
      ≤ ENNReal.ofReal (2 / 3) * ENNReal.ofReal v := by
        rw [← ENNReal.ofReal_mul (by norm_num)]
        refine ENNReal.ofReal_le_ofReal ?_
        have : 2 / 3 * v / 27 * r ^ 3 ≤ 2 / 3 * v / 27 * 27 :=
          mul_le_mul_of_nonneg_left hr27 (by positivity)
        linarith
    _ ≤ ENNReal.ofReal (2 / 3) * _ :=
        mul_le_mul' le_rfl ((hvol y hy).trans (MeasureTheory.measure_mono hmono))

end GC.LongTime.Ch12
