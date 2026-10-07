import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBarrierTransferA_O27

set_option autoImplicit false

/-! # CH12-S100 G1: image-volume LOWER bound for one model datum.

Mirror of `bufferedMap_image_volume_le_O27` (upper bound): for an open set `S` inside the closed
ball `B(y, R)` with `y ∈ B(base, 1/acc t)`, `R ≤ 1/acc t` and `acc t ≤ 1/8`, the normalised volume
of `mp t ht '' S` is at least `(2/3)` times the model volume of `S`.  The constant comes from
`(1 - acc) h ≤ pullback`, hence `h ≤ (8/7) pullback`, and `riemannianVolumeMeasure_le_on`
(`sqrt ((8/7)^3) ≤ 3/2`).  Source of the metric lower bound: `bufferedMap_metric_lower_O27`. -/

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

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {Hm : FiniteVolumeHyperbolicModel.{u}} {st : ℝ} {acc : ℝ → ℝ}
  {dom : ℝ → TopologicalSpace.Opens Hm.Carrier}
  {mp : (t : ℝ) → st ≤ t → Hm.Carrier → (postStage F.observation t).Carrier}

/-- **G1.**  Image-volume lower bound (single model datum, Jacobian factor `2/3`). -/
theorem image_volume_lower_S100 (hst : 0 < st) (hD : ((∀ t (ht : st ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mp t ht) (dom t)) ∧
      (∀ t (ht : st ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : dom t => mp t ht x)) ∧
      (∀ t, st ≤ t → riemannianBallOf Hm.metric Hm.basepoint (2 * (acc t)⁻¹) ⊆ dom t) ∧
      (∀ t (ht : st ≤ t),
        let h := Hm.metric; let error := fun p : Hm.Carrier =>
          ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) p) ℝ).symm.toContinuousLinearMap.comp
            ((t⁻¹ : ℝ) • localPullInner (postMetric F.observation t) (mp t ht) p - h.inner p)).uncurryLeft;
        ∀ k : ℕ, k ≤ max K ⌈(acc t)⁻¹⌉₊ →
          ∀ p ∈ riemannianBallOf h Hm.basepoint (2 * (acc t)⁻¹),
            tensor0SFiberNorm h p (2 + k) (iteratedMetricCovariantDerivative h 2 error k p) < acc t) ∧
      (∀ t, st ≤ t → 0 < acc t) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → acc t < ε)))
    (t : ℝ) (ht : st ≤ t) (y : (Hm).Carrier)
    (hy : y ∈ riemannianBallOf (Hm).metric (Hm).basepoint (acc t)⁻¹)
    {R : ℝ} (hRn : R ≤ (acc t)⁻¹) (hδ : acc t ≤ 1 / 8)
    {S : Set (Hm).Carrier} (hS : IsOpen S) (hSR : S ⊆ riemannianClosedBallOf (Hm).metric y R) :
    ENNReal.ofReal (2 / 3) *
        DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (𝓡 3) (Hm).Carrier
          (Hm).metric S ≤
      DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (𝓡 3)
        (postStage F.observation t).Carrier
        (scaleMetric t⁻¹ (inv_pos.mpr (hst.trans_le ht)) (postMetric F.observation t))
        (mp t ht '' S) := by
  classical
  let : MeasurableSpace (Hm).Carrier := borel _
  have : BorelSpace (Hm).Carrier := ⟨rfl⟩
  let : MeasurableSpace (postStage F.observation t).Carrier := borel _
  have : BorelSpace (postStage F.observation t).Carrier := ⟨rfl⟩
  let : MeasurableSpace (dom t) := borel _
  have : BorelSpace (dom t) := ⟨rfl⟩
  let : SigmaCompactSpace (dom t) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) (dom t).isOpen)
  obtain ⟨hf, hinj⟩ := bufferedMap_localDiffeo_O27 hD t ht
  have hsub := closedBall_subset_buffer_O27 hD t ht y hy hRn
  have hAU : S ⊆ (dom t : Set _) := fun x hx => hD.2.2.1 t ht (hsub (hSR hx))
  have hSopen : IsOpen ((Subtype.val : dom t → _) ⁻¹' S) := hS.preimage continuous_subtype_val
  let f : dom t → (postStage F.observation t).Carrier := fun x => mp t ht x
  set gb := scaleMetric t⁻¹ (inv_pos.mpr (hst.trans_le ht)) (postMetric F.observation t)
    with hgb
  let gp := DifferentialGeometry.Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph gb f hf hinj
  have hmetric : ∀ (x : dom t) (v w : TangentSpace (𝓡 3) x), gp.inner x v w =
      gb.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) :=
    DifferentialGeometry.Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph_inner gb f hf hinj
  have h1 := DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry
    gp gb f hf hinj hmetric hSopen.measurableSet
  have himg : f '' (Subtype.val ⁻¹' S) = mp t ht '' S := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.val, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hAU hx⟩, hx, rfl⟩
  rw [← himg, ← h1]
  have hS2 := Geometry.Measure.riemannianVolumeMeasure_restrictOpen_preimage_of_subset
    (Hm).metric (dom t) hS.measurableSet hAU
  have hcomp : ∀ x ∈ (Subtype.val ⁻¹' S : Set (dom t)), ∀ v : TangentSpace (𝓡 3) x,
      ((Hm).metric.restrictOpen (dom t)).inner x v v ≤ (8 / 7 : ℝ) * gp.inner x v v := by
    intro x hx v
    have hmd : MDifferentiableAt (𝓡 3) (𝓡 3) (mp t ht) x.val :=
      ((hD.1 t ht).mdifferentiableOn (by simp) x.val x.2).mdifferentiableAt
        ((dom t).isOpen.mem_nhds x.2)
    have hcomp : mfderiv (𝓡 3) (𝓡 3) f x =
        (mfderiv (𝓡 3) (𝓡 3) (mp t ht) x.val).comp
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : dom t → _) x) :=
      mfderiv_comp x hmd (hasMFDerivAt_subtype_val (I := 𝓡 3) (dom t) x).mdifferentiableAt
    rw [hmetric, hcomp]
    simp only [ContinuousLinearMap.comp_apply, mfderiv_subtype_val_apply]
    have hlo := bufferedMap_metric_lower_O27 hst hD t ht x.val (hsub (hSR hx)) v
    have hnn := metric_inner_self_nonneg (Hm).metric x.val v
    have hδ' : (7 / 8 : ℝ) ≤ 1 - acc t := by linarith
    have h78 : (7 / 8 : ℝ) * (Hm).metric.inner x.val v v ≤ gb.inner (mp t ht x.val)
        (mfderiv (𝓡 3) (𝓡 3) (mp t ht) x.val v) (mfderiv (𝓡 3) (𝓡 3) (mp t ht) x.val v) :=
      (mul_le_mul_of_nonneg_right hδ' hnn).trans hlo
    change (Hm).metric.inner x.val v v ≤ _
    nlinarith
  have hle := DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.riemannianVolumeMeasure_le_on gp
    ((Hm).metric.restrictOpen (dom t)) hSopen.measurableSet (by norm_num : (0 : ℝ) < 8 / 7) hcomp
  rw [hS2] at hle
  have hc : ENNReal.ofReal (2 / 3) * ENNReal.ofReal (Real.sqrt ((8 / 7 : ℝ) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) ≤ 1 := by
    rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
    rw [this]
    have hs : Real.sqrt ((8 / 7 : ℝ) ^ 3) ≤ 3 / 2 := by
      rw [Real.sqrt_le_iff]
      refine ⟨by norm_num, ?_⟩
      norm_num
    nlinarith [Real.sqrt_nonneg ((8 / 7 : ℝ) ^ 3)]
  calc ENNReal.ofReal (2 / 3) * _ ≤ ENNReal.ofReal (2 / 3) * (ENNReal.ofReal (Real.sqrt ((8 / 7 : ℝ) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))))
          * _) := mul_le_mul' le_rfl hle
    _ = (ENNReal.ofReal (2 / 3) * ENNReal.ofReal (Real.sqrt ((8 / 7 : ℝ) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))))) * _ := by rw [mul_assoc]
    _ ≤ 1 * _ := mul_le_mul' hc le_rfl
    _ = _ := one_mul _

end GC.LongTime.Ch12
