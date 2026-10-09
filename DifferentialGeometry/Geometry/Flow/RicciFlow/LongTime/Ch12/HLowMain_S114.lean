import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HLowAux_S114
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBarrierTransferB_O27

set_option autoImplicit false

/-! # CH12-S114 G1b: the HLOW producer.

`HLOW_S114 F K` is the `HLOW` binder of `hstep_O44` / `hfam_O44` ([FROZEN] CH12-O44), verbatim:
image-thickness lower bound at fixed radius `R` for a hyperbolic-model datum with the hpi07 inputs.
Steps: (a) `hTrans_of_curv_O27` + `exists_curvatureRadius_real_S114` (real radius `r ∈ [c₀, √8]`);
(b) `mapH '' B_H(y, r/2) ⊆ ball(mapH y, r)` (`image_closedBall_subset_ball_of_metric_upper_on_opens`, `L = 3/2 < 2`);
(c) `image_volume_lower_S100`; (d) `exists_uniform_ball_volume_S114`; (e) `w := (2/3) v / 27`. -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set Filter
open Manifold GC.LongTime DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal Topology
universe u
namespace GC.LongTime.Ch12

section Image

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {Hm : FiniteVolumeHyperbolicModel.{u}} {st : ℝ} {acc : ℝ → ℝ}
  {dom : ℝ → TopologicalSpace.Opens Hm.Carrier}
  {mp : (t : ℝ) → st ≤ t → Hm.Carrier → (postStage F.observation t).Carrier}

/-- Image of the model ball `B(y, r/2)` lies in the physical ball `B(mp y, r)`, and the model ball has
volume at most `3/2` times the physical ball volume. -/
theorem ball_image_volume_lower_S114 (hst : 0 < st) (hD : ((∀ t (ht : st ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mp t ht) (dom t)) ∧
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
    (t : ℝ) (ht : st ≤ t) (y : Hm.Carrier)
    (hy : y ∈ riemannianBallOf Hm.metric Hm.basepoint (acc t)⁻¹)
    (hδ : acc t ≤ 1 / 8) {r : ℝ} (hr : 0 < r) (hrn : r ≤ (acc t)⁻¹) :
    ENNReal.ofReal (2 / 3) *
        DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (𝓡 3) Hm.Carrier Hm.metric
          (riemannianBallOf Hm.metric y (r / 2)) ≤
      ballVolume (scaleMetric t⁻¹ (inv_pos.mpr (hst.trans_le ht)) (postMetric F.observation t))
        (mp t ht y) r := by
  have hnpos : 0 < (acc t)⁻¹ := inv_pos.mpr (hD.2.2.2.2.1 t ht)
  have hS : IsOpen (riemannianBallOf Hm.metric y (r / 2)) := isOpen_riemannianBallOf Hm.metric y (r / 2)
  have hSR : riemannianBallOf Hm.metric y (r / 2) ⊆ riemannianClosedBallOf Hm.metric y (r / 2) :=
    fun z hz => (show riemannianEDistOf Hm.metric y z < ENNReal.ofReal (r / 2) from hz).le
  have h1 := image_volume_lower_S100 hst hD t ht y hy (R := r / 2) (by linarith) hδ hS hSR
  obtain ⟨hf, hinj⟩ := bufferedMap_localDiffeo_O27 hD t ht
  have hsub := closedBall_subset_buffer_O27 hD t ht y hy hrn
  have hy2 : y ∈ (dom t : Set Hm.Carrier) :=
    hD.2.2.1 t ht (riemannianBallOf_mono _ _ (by linarith) hy)
  set gb := scaleMetric t⁻¹ (inv_pos.mpr (hst.trans_le ht)) (postMetric F.observation t) with hgb
  have hupper : ∀ x : dom t, x.val ∈ riemannianClosedBallOf Hm.metric y r → ∀ v : TangentSpace (𝓡 3) x,
      gb.inner (mp t ht x.val) (mfderiv (𝓡 3) (𝓡 3) (fun x : dom t => mp t ht x) x v)
        (mfderiv (𝓡 3) (𝓡 3) (fun x : dom t => mp t ht x) x v) ≤
        (3 / 2 : ℝ) ^ 2 * Hm.metric.inner x.val v v := by
    intro x hx v
    have hmd : MDifferentiableAt (𝓡 3) (𝓡 3) (mp t ht) x.val :=
      ((hD.1 t ht).mdifferentiableOn (by simp) x.val x.2).mdifferentiableAt
        ((dom t).isOpen.mem_nhds x.2)
    have hcomp : mfderiv (𝓡 3) (𝓡 3) (fun x : dom t => mp t ht x) x =
        (mfderiv (𝓡 3) (𝓡 3) (mp t ht) x.val).comp
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : dom t → _) x) :=
      mfderiv_comp x hmd (hasMFDerivAt_subtype_val (I := 𝓡 3) (dom t) x).mdifferentiableAt
    rw [hcomp]
    simp only [ContinuousLinearMap.comp_apply, mfderiv_subtype_val_apply]
    have hup := bufferedMap_metric_upper_O27 hst hD t ht x.val (hsub hx) v
    have hnn := metric_inner_self_nonneg Hm.metric x.val v
    have hacc : acc t ≤ 1 / 8 := hδ
    change gb.inner _ _ _ ≤ _ at hup
    nlinarith
  have hcap := DifferentialGeometry.Geometry.Metric.image_closedBall_subset_ball_of_metric_upper_on_opens gb Hm.metric (dom t)
    (fun x : dom t => mp t ht x) hf hinj ⟨y, hy2⟩ (r := r / 2) (R := r) (L := 3 / 2) (c := 2)
    (by linarith) (by linarith) (by norm_num) (by norm_num)
    (fun x hx => hD.2.2.1 t ht (hsub hx)) hupper
  have hcont : mp t ht '' riemannianBallOf Hm.metric y (r / 2) ⊆ riemannianBallOf gb (mp t ht y) r := by
    rintro _ ⟨z, hz, rfl⟩
    have hzd : z ∈ (dom t : Set Hm.Carrier) :=
      hD.2.2.1 t ht (hsub (riemannianClosedBallOf_mono _ _ (by linarith) (hSR hz)))
    have := hcap ⟨⟨z, hzd⟩, hSR hz, rfl⟩
    have e : (2 : ℝ) * (r / 2) = r := by ring
    rwa [e] at this
  exact h1.trans (MeasureTheory.measure_mono hcont)

end Image

/-- **G1.**  The `HLOW` binder of `hstep_O44` / `hfam_O44` ([FROZEN] CH12-O44), proved. -/
theorem HLOW_S114 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) :
    ∀ (H : FiniteVolumeHyperbolicModel.{u}) (sH : ℝ) (hsH : 0 < sH) (αH : ℝ → ℝ)
      (ΩH : TopologicalSpace.Opens (ℝ × H.Carrier))
      (mapH : (t : ℝ) → sH ≤ t → H.Carrier → (postStage F.observation t).Carrier),
      (∀ t, sH ≤ t → 0 < αH t) → (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → αH t < ε) →
      (∀ t (ht : sH ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mapH t ht) (sourceSlice_CX5 ΩH t)) →
      (∀ t (ht : sH ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : sourceSlice_CX5 ΩH t => mapH t ht x)) →
      (∀ t, sH ≤ t → riemannianBallOf H.metric H.basepoint (2 * (αH t)⁻¹) ⊆ sourceSlice_CX5 ΩH t) →
      (∀ t (ht : sH ≤ t), ∀ k : ℕ, k ≤ max K ⌈(αH t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (αH t)⁻¹),
          ckErr_O21 H (postMetric F.observation t) t⁻¹ (mapH t ht) k p < αH t) →
      ∀ R : ℝ, ∃ w : ℝ, 0 < w ∧ ∃ T : ℝ, ∀ t (ht : sH ≤ t), T ≤ t →
        ∀ y ∈ riemannianBallOf H.metric H.basepoint R, ∃ r : ℝ, 0 < r ∧
          curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr (hsH.trans_le ht))
            (postMetric F.observation t)) (mapH t ht y) = ENNReal.ofReal r ∧
          ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (scaleMetric t⁻¹
            (inv_pos.mpr (hsH.trans_le ht)) (postMetric F.observation t)) (mapH t ht y) r := by
  intro H sH hsH αH ΩH mapH hpos hdec hsm hemb hball hck R
  have hD : ((∀ t (ht : sH ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mapH t ht) (sourceSlice_CX5 ΩH t)) ∧
      (∀ t (ht : sH ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : sourceSlice_CX5 ΩH t => mapH t ht x)) ∧
      (∀ t, sH ≤ t → riemannianBallOf H.metric H.basepoint (2 * (αH t)⁻¹) ⊆ sourceSlice_CX5 ΩH t) ∧
      (∀ t (ht : sH ≤ t),
        let h := H.metric; let error := fun p : H.Carrier =>
          ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) p) ℝ).symm.toContinuousLinearMap.comp
            ((t⁻¹ : ℝ) • localPullInner (postMetric F.observation t) (mapH t ht) p - h.inner p)).uncurryLeft;
        ∀ k : ℕ, k ≤ max K ⌈(αH t)⁻¹⌉₊ →
          ∀ p ∈ riemannianBallOf h H.basepoint (2 * (αH t)⁻¹),
            tensor0SFiberNorm h p (2 + k) (iteratedMetricCovariantDerivative h 2 error k p) < αH t) ∧
      (∀ t, sH ≤ t → 0 < αH t) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → αH t < ε)) :=
    ⟨hsm, hemb, hball, fun t ht => by intro h error k hk p hp; exact hck t ht k hk p hp,
      hpos, hdec⟩
  obtain ⟨c₀, hc₀, T₁, hT⟩ := hTrans_of_curv_O27 hsH hD (hUp_O27 hsH hD)
    (hLow_O27 hsH hD (hC0_O27 hsH hD))
  obtain ⟨T₂, -, hT₂⟩ := accuracy_inv_large_O27 hD (max R 8)
  obtain ⟨v, hv, hvol⟩ := exists_uniform_ball_volume_S114 H R (ρ := c₀ / 2) (by positivity)
  refine ⟨2 / 3 * v / 27, by positivity, max T₁ T₂, fun t ht hTt y hy => ?_⟩
  have hn := hT₂ t ((le_max_right _ _).trans hTt)
  have hn8 : (8 : ℝ) ≤ (αH t)⁻¹ := (le_max_right _ _).trans hn
  have hnR : R ≤ (αH t)⁻¹ := (le_max_left _ _).trans hn
  have hδ : αH t ≤ 1 / 8 := by
    rw [le_inv_comm₀ (by norm_num) (hpos t ht)] at hn8
    simpa using hn8
  have hyB : y ∈ riemannianBallOf H.metric H.basepoint (αH t)⁻¹ :=
    riemannianBallOf_mono _ _ hnR hy
  obtain ⟨hlow, hup, -⟩ := hT t ht ((le_max_left _ _).trans hTt) y hyB
  obtain ⟨r, hr, hcr, hcr1, hr8⟩ := exists_curvatureRadius_real_S114 _ _ hc₀ hlow hup
  refine ⟨r, hr, hcr, ?_⟩
  have hr3 : r ≤ 3 := by nlinarith
  have hr27 : r ^ 3 ≤ 27 := by
    calc r ^ 3 ≤ 3 ^ 3 := pow_le_pow_left₀ hr.le hr3 3
      _ = 27 := by norm_num
  have hB := ball_image_volume_lower_S114 hsH hD t ht y hyB hδ hr (by linarith)
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
