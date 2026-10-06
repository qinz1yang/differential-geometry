import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OuterTransferC0_S40
import DifferentialGeometry.Geometry.Measure.LocalIsometry
import DifferentialGeometry.Geometry.Measure.OpenSubtypeVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalVolumeOrder

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

theorem bufferedMap_image_volume_le_S40 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} (B : BufferedPersistentCores F K)
    (i : Fin B.count) (t : ℝ) (ht : B.start ≤ t) (y : (B.model i).Carrier)
    (hy : y ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint (B.accuracy t)⁻¹)
    {R : ℝ} (hRn : R ≤ (B.accuracy t)⁻¹) (hδ : B.accuracy t ≤ 1 / 4) :
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (𝓡 3) (postStage F.observation t).Carrier
        (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht)) (postMetric F.observation t))
        (B.map i t ht '' riemannianClosedBallOf (B.model i).metric y R) ≤
      ENNReal.ofReal 2 *
        DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (𝓡 3) (B.model i).Carrier
          (B.model i).metric (riemannianClosedBallOf (B.model i).metric y R) := by
  classical
  let : MeasurableSpace (B.model i).Carrier := borel _
  have : BorelSpace (B.model i).Carrier := ⟨rfl⟩
  let : MeasurableSpace (postStage F.observation t).Carrier := borel _
  have : BorelSpace (postStage F.observation t).Carrier := ⟨rfl⟩
  let : MeasurableSpace (B.domain i t) := borel _
  have : BorelSpace (B.domain i t) := ⟨rfl⟩
  let : SigmaCompactSpace (B.domain i t) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) (B.domain i t).isOpen)
  obtain ⟨hf, hinj⟩ := bufferedMap_localDiffeo_S35 B i t ht
  have hsub := closedBall_subset_buffer_S40 B i t ht y hy hRn
  have hAU : riemannianClosedBallOf (B.model i).metric y R ⊆ (B.domain i t : Set _) :=
    fun x hx => B.buffer_domain i t ht (hsub hx)
  have hAclosed : IsClosed (riemannianClosedBallOf (B.model i).metric y R) :=
    isClosed_le (Geometry.Riemannian.continuous_riemannianEDist (B.model i).metric y) continuous_const
  have hSclosed : IsClosed ((Subtype.val : B.domain i t → _) ⁻¹'
      riemannianClosedBallOf (B.model i).metric y R) :=
    hAclosed.preimage continuous_subtype_val
  let f : B.domain i t → (postStage F.observation t).Carrier := fun x => B.map i t ht x
  set gb := scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht)) (postMetric F.observation t)
    with hgb
  let gp := DifferentialGeometry.Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph gb f hf hinj
  have hmetric : ∀ (x : B.domain i t) (v w : TangentSpace (𝓡 3) x), gp.inner x v w =
      gb.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) :=
    DifferentialGeometry.Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph_inner gb f hf hinj
  have h1 := DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry
    gp gb f hf hinj hmetric hSclosed.measurableSet
  have himg : f '' (Subtype.val ⁻¹' riemannianClosedBallOf (B.model i).metric y R) =
      B.map i t ht '' riemannianClosedBallOf (B.model i).metric y R := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.val, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hAU hx⟩, hx, rfl⟩
  rw [← himg, ← h1]
  have hS2 := Geometry.Measure.riemannianVolumeMeasure_restrictOpen_preimage_of_subset
    (B.model i).metric (B.domain i t) hAclosed.measurableSet hAU
  have hcomp : ∀ x ∈ (Subtype.val ⁻¹' riemannianClosedBallOf (B.model i).metric y R :
      Set (B.domain i t)), ∀ v : TangentSpace (𝓡 3) x,
      gp.inner x v v ≤ (5 / 4 : ℝ) * ((B.model i).metric.restrictOpen (B.domain i t)).inner x v v := by
    intro x hx v
    have hmd : MDifferentiableAt (𝓡 3) (𝓡 3) (B.map i t ht) x.val :=
      ((B.smooth i t ht).mdifferentiableOn (by simp) x.val x.2).mdifferentiableAt
        ((B.domain i t).isOpen.mem_nhds x.2)
    have hcomp : mfderiv (𝓡 3) (𝓡 3) f x =
        (mfderiv (𝓡 3) (𝓡 3) (B.map i t ht) x.val).comp
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : B.domain i t → _) x) :=
      mfderiv_comp x hmd (hasMFDerivAt_subtype_val (I := 𝓡 3) (B.domain i t) x).mdifferentiableAt
    rw [hmetric, hcomp]
    simp only [ContinuousLinearMap.comp_apply, mfderiv_subtype_val_apply]
    have hup := bufferedMap_metric_upper_S40 B i t ht x.val (hsub hx) v
    have hnn := metric_inner_self_nonneg (B.model i).metric x.val v
    have hδ' : (1 + B.accuracy t) ≤ 5 / 4 := by linarith
    calc _ ≤ (1 + B.accuracy t) * (B.model i).metric.inner x.val v v := hup
      _ ≤ _ := mul_le_mul_of_nonneg_right hδ' hnn
  have hle := DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.riemannianVolumeMeasure_le_on ((B.model i).metric.restrictOpen (B.domain i t)) gp
    hSclosed.measurableSet (by norm_num : (0 : ℝ) < 5 / 4) hcomp
  rw [hS2] at hle
  refine hle.trans (mul_le_mul' ?_ le_rfl)
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.sqrt_le_iff]
  refine ⟨by norm_num, ?_⟩
  have : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  rw [this]
  norm_num

/-- **(S4)** Volume comparison: `vol B_ḡ(φ y, r) ≤ 2 · vol B_H(y, 4)` for `r² ≤ 8`, `y ∈ B(x_i, n)`,
`δ ≤ 1/4`. -/
theorem bufferedMap_ballVolume_le_S40 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} (B : BufferedPersistentCores F K)
    (i : Fin B.count) (t : ℝ) (ht : B.start ≤ t) (y : (B.model i).Carrier)
    (hy : y ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint (B.accuracy t)⁻¹)
    (hδ : B.accuracy t ≤ 1 / 4) {r : ℝ} (hr : 0 < r) (hr8 : r ^ 2 ≤ 8) :
    ballVolume (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht)) (postMetric F.observation t))
        (B.map i t ht y) r ≤ ENNReal.ofReal 2 * ballVolume (B.model i).metric y 4 := by
  have hδpos := B.accuracy_pos t ht
  have hpos : 0 < 1 - B.accuracy t := by linarith
  have hsq : 0 < Real.sqrt (1 - B.accuracy t) := Real.sqrt_pos.mpr hpos
  have hn4 : 4 ≤ (B.accuracy t)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hδpos]
    norm_num
    exact hδ
  set R : ℝ := r / Real.sqrt (1 - B.accuracy t) with hR
  have hRr : R * Real.sqrt (1 - B.accuracy t) = r := by
    rw [hR]; field_simp
  have hRpos : 0 < R := div_pos hr hsq
  have hR2 : R ^ 2 * (1 - B.accuracy t) = r ^ 2 := by
    rw [← hRr, mul_pow, Real.sq_sqrt hpos.le]
  have hR4 : R < 4 := by
    have : R ^ 2 < 4 ^ 2 := by nlinarith [sq_nonneg R]
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) this
  have hcap := bufferedMap_ball_subset_image_S40 B i t ht y hy hRpos (hR4.le.trans hn4)
    (by linarith)
  rw [hRr] at hcap
  have hvol := bufferedMap_image_volume_le_S40 B i t ht y hy (hR4.le.trans hn4) hδ
  have hclosed : riemannianClosedBallOf (B.model i).metric y R ⊆
      riemannianBallOf (B.model i).metric y 4 := by
    intro x hx
    exact lt_of_le_of_lt hx ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hR4)
  unfold ballVolume
  calc _ ≤ _ := MeasureTheory.measure_mono hcap
    _ ≤ _ := hvol
    _ ≤ _ := mul_le_mul' le_rfl (MeasureTheory.measure_mono hclosed)

end GC.LongTime.Ch12
