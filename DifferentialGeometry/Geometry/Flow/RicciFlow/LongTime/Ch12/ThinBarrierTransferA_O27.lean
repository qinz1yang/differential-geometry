import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OuterTransferVolume_S40

set_option autoImplicit false

/-! CH12-O27 G1 (part A) — count-free copy of the S35/S40 first-exit, C⁰ and volume transfer for ONE
model datum (`hD` = exactly the `BufferedPersistentCores` fields these proofs read). -/

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

theorem bufferedMap_localDiffeo_O27 (hD : ((∀ t (ht : st ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mp t ht) (dom t)) ∧
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
    (t : ℝ) (ht : st ≤ t) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun x : dom t => mp t ht x) ∧
      Function.Injective (fun x : dom t => mp t ht x) := by
  have hemb := hD.2.1 t ht
  refine ⟨?_, hemb.isEmbedding.injective⟩
  exact isLocalDiffeomorph_of_injective_mfderiv _ hemb.contMDiff
    (fun q => injective_mfderiv_of_isImmersionAt _ _ _ q
      (hemb.isImmersion.isImmersionAt q)) rfl

theorem ambient_ball_subset_image_O27 (hD : ((∀ t (ht : st ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mp t ht) (dom t)) ∧
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
    (t : ℝ) (ht : st ≤ t)
    (gb : SmoothRiemannianMetric (𝓡 3) (postStage F.observation t).Carrier)
    (y : (Hm).Carrier) (hy : y ∈ dom t) {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (hsource : riemannianClosedBallOf (Hm).metric y R ⊆ (dom t : Set _))
    (hlower : ∀ x ∈ riemannianClosedBallOf (Hm).metric y R,
      ∀ v : TangentSpace (𝓡 3) x, (Hm).metric.inner x v v ≤
        L ^ 2 * gb.inner (mp t ht x) (mfderiv (𝓡 3) (𝓡 3) (mp t ht) x v)
          (mfderiv (𝓡 3) (𝓡 3) (mp t ht) x v)) :
    riemannianBallOf gb (mp t ht y) (R / L) ⊆
      mp t ht '' riemannianClosedBallOf (Hm).metric y R := by
  obtain ⟨hf, hinj⟩ := bufferedMap_localDiffeo_O27 hD t ht
  have hcap := DifferentialGeometry.Geometry.Metric.ball_subset_image_of_metric_lower_on_opens gb (Hm).metric (dom t)
    (fun x : dom t => mp t ht x) hf hinj ⟨y, hy⟩ hR hL
    ((Hm).complete.closedEBall_isCompact y R) hsource (fun x hx v => by
      have hmd : MDifferentiableAt (𝓡 3) (𝓡 3) (mp t ht) x.val :=
        ((hD.1 t ht).mdifferentiableOn (by simp) x.val x.2).mdifferentiableAt
          ((dom t).isOpen.mem_nhds x.2)
      have hcomp : mfderiv (𝓡 3) (𝓡 3) (fun x : dom t => mp t ht x) x =
          (mfderiv (𝓡 3) (𝓡 3) (mp t ht) x.val).comp
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : dom t → _) x) :=
        mfderiv_comp x hmd (hasMFDerivAt_subtype_val (I := 𝓡 3) (dom t) x).mdifferentiableAt
      rw [hcomp]
      simp only [ContinuousLinearMap.comp_apply, mfderiv_subtype_val_apply]
      exact hlower x.val hx v)
  intro z hz
  obtain ⟨x, hx, rfl⟩ := hcap hz
  exact ⟨x.val, hx, rfl⟩


theorem bufferedMap_metric_abs_le_O27 (hst : 0 < st) (hD : ((∀ t (ht : st ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mp t ht) (dom t)) ∧
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
    (t : ℝ) (ht : st ≤ t) (p : (Hm).Carrier)
    (hp : p ∈ riemannianBallOf (Hm).metric (Hm).basepoint
      (2 * (acc t)⁻¹))
    (v : TangentSpace (𝓡 3) p) :
    |(scaleMetric t⁻¹ (inv_pos.mpr (hst.trans_le ht)) (postMetric F.observation t)).inner
        (mp t ht p) (mfderiv (𝓡 3) (𝓡 3) (mp t ht) p v)
        (mfderiv (𝓡 3) (𝓡 3) (mp t ht) p v) - (Hm).metric.inner p v v| ≤
      acc t * (Hm).metric.inner p v v := by
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (Hm).metric p
  have herr := hD.2.2.2.1 t ht 0 (Nat.zero_le _) p hp
  set E : Tensor0SSpace 2 (𝓡 3) p :=
    ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) p) ℝ).symm.toContinuousLinearMap.comp
          ((t⁻¹ : ℝ) • localPullInner (postMetric F.observation t) (mp t ht) p -
            (Hm).metric.inner p)).uncurryLeft with hE
  change Real.sqrt (normSq0S (Hm).metric p 2 E) < _ at herr
  have hbound := abs_apply_le_sqrt_normSq0S (Hm).metric p 2 basis hON E (fun _ => v)
  have heval : E (fun _ => v) =
      (scaleMetric t⁻¹ (inv_pos.mpr (hst.trans_le ht)) (postMetric F.observation t)).inner
        (mp t ht p) (mfderiv (𝓡 3) (𝓡 3) (mp t ht) p v)
        (mfderiv (𝓡 3) (𝓡 3) (mp t ht) p v) - (Hm).metric.inner p v v := rfl
  have hprod : (∏ _a : Fin 2, Real.sqrt ((Hm).metric.inner p v v)) =
      (Hm).metric.inner p v v := by
    rw [Fin.prod_univ_two, Real.mul_self_sqrt (metric_inner_self_nonneg _ _ _)]
  rw [heval, hprod] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_right herr.le (metric_inner_self_nonneg _ _ _))

theorem bufferedMap_metric_lower_O27 (hst : 0 < st) (hD : ((∀ t (ht : st ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mp t ht) (dom t)) ∧
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
    (t : ℝ) (ht : st ≤ t) (p : (Hm).Carrier)
    (hp : p ∈ riemannianBallOf (Hm).metric (Hm).basepoint
      (2 * (acc t)⁻¹))
    (v : TangentSpace (𝓡 3) p) :
    (1 - acc t) * (Hm).metric.inner p v v ≤
      (scaleMetric t⁻¹ (inv_pos.mpr (hst.trans_le ht)) (postMetric F.observation t)).inner
        (mp t ht p) (mfderiv (𝓡 3) (𝓡 3) (mp t ht) p v)
        (mfderiv (𝓡 3) (𝓡 3) (mp t ht) p v) := by
  have h := (abs_le.mp (bufferedMap_metric_abs_le_O27 hst hD t ht p hp v)).1
  linarith

theorem bufferedMap_metric_upper_O27 (hst : 0 < st) (hD : ((∀ t (ht : st ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mp t ht) (dom t)) ∧
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
    (t : ℝ) (ht : st ≤ t) (p : (Hm).Carrier)
    (hp : p ∈ riemannianBallOf (Hm).metric (Hm).basepoint
      (2 * (acc t)⁻¹))
    (v : TangentSpace (𝓡 3) p) :
    (scaleMetric t⁻¹ (inv_pos.mpr (hst.trans_le ht)) (postMetric F.observation t)).inner
        (mp t ht p) (mfderiv (𝓡 3) (𝓡 3) (mp t ht) p v)
        (mfderiv (𝓡 3) (𝓡 3) (mp t ht) p v) ≤
      (1 + acc t) * (Hm).metric.inner p v v := by
  have h := (abs_le.mp (bufferedMap_metric_abs_le_O27 hst hD t ht p hp v)).2
  linarith

theorem closedBall_subset_buffer_O27 (hD : ((∀ t (ht : st ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mp t ht) (dom t)) ∧
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
    {R : ℝ} (hRn : R ≤ (acc t)⁻¹) :
    riemannianClosedBallOf (Hm).metric y R ⊆
      riemannianBallOf (Hm).metric (Hm).basepoint (2 * (acc t)⁻¹) := by
  intro x hx
  have hnpos : 0 < (acc t)⁻¹ := inv_pos.mpr (hD.2.2.2.2.1 t ht)
  have h1 : riemannianEDistOf (Hm).metric (Hm).basepoint y <
      ENNReal.ofReal (acc t)⁻¹ := hy
  have h2 : riemannianEDistOf (Hm).metric y x ≤ ENNReal.ofReal R := hx
  have h3 := (riemannianEDistOf_triangle (Hm).metric (Hm).basepoint y x).trans_lt
    (ENNReal.add_lt_add_of_lt_of_le (h2.trans_lt ENNReal.ofReal_lt_top).ne h1 (h2.trans (ENNReal.ofReal_le_ofReal hRn)))
  rw [← ENNReal.ofReal_add hnpos.le hnpos.le] at h3
  have : (acc t)⁻¹ + (acc t)⁻¹ = 2 * (acc t)⁻¹ := by ring
  rwa [this] at h3

theorem bufferedMap_ball_subset_image_O27 (hst : 0 < st) (hD : ((∀ t (ht : st ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mp t ht) (dom t)) ∧
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
    {R : ℝ} (hR : 0 < R) (hRn : R ≤ (acc t)⁻¹) (hδ : acc t < 1) :
    riemannianBallOf
        (scaleMetric t⁻¹ (inv_pos.mpr (hst.trans_le ht)) (postMetric F.observation t))
        (mp t ht y) (R * Real.sqrt (1 - acc t)) ⊆
      mp t ht '' riemannianClosedBallOf (Hm).metric y R := by
  have hsub := closedBall_subset_buffer_O27 hD t ht y hy hRn
  have hpos : 0 < 1 - acc t := sub_pos.mpr hδ
  have hsq : 0 < Real.sqrt (1 - acc t) := Real.sqrt_pos.mpr hpos
  have hnpos : 0 < (acc t)⁻¹ := inv_pos.mpr (hD.2.2.2.2.1 t ht)
  have hy2 : y ∈ riemannianBallOf (Hm).metric (Hm).basepoint
      (2 * (acc t)⁻¹) := by
    refine riemannianBallOf_mono _ _ ?_ hy
    linarith
  have hcap := ambient_ball_subset_image_O27 hD t ht
    (scaleMetric t⁻¹ (inv_pos.mpr (hst.trans_le ht)) (postMetric F.observation t)) y
    (hD.2.2.1 t ht hy2) hR (inv_pos.mpr hsq : 0 < (Real.sqrt (1 - acc t))⁻¹)
    (fun x hx => hD.2.2.1 t ht (hsub hx))
    (fun x hx v => by
      have hlow := bufferedMap_metric_lower_O27 hst hD t ht x (hsub hx) v
      have hnn := metric_inner_self_nonneg (Hm).metric x v
      have hL : ((Real.sqrt (1 - acc t))⁻¹) ^ 2 = (1 - acc t)⁻¹ := by
        rw [inv_pow, Real.sq_sqrt hpos.le]
      rw [hL]
      rw [inv_mul_eq_div, le_div_iff₀ hpos]
      linarith)
  have hRL : R / (Real.sqrt (1 - acc t))⁻¹ = R * Real.sqrt (1 - acc t) := by
    rw [div_inv_eq_mul]
  rwa [hRL] at hcap


theorem bufferedMap_image_volume_le_O27 (hst : 0 < st) (hD : ((∀ t (ht : st ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mp t ht) (dom t)) ∧
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
    {R : ℝ} (hRn : R ≤ (acc t)⁻¹) (hδ : acc t ≤ 1 / 4) :
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (𝓡 3) (postStage F.observation t).Carrier
        (scaleMetric t⁻¹ (inv_pos.mpr (hst.trans_le ht)) (postMetric F.observation t))
        (mp t ht '' riemannianClosedBallOf (Hm).metric y R) ≤
      ENNReal.ofReal 2 *
        DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (𝓡 3) (Hm).Carrier
          (Hm).metric (riemannianClosedBallOf (Hm).metric y R) := by
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
  have hAU : riemannianClosedBallOf (Hm).metric y R ⊆ (dom t : Set _) :=
    fun x hx => hD.2.2.1 t ht (hsub hx)
  have hAclosed : IsClosed (riemannianClosedBallOf (Hm).metric y R) :=
    isClosed_le (Geometry.Riemannian.continuous_riemannianEDist (Hm).metric y) continuous_const
  have hSclosed : IsClosed ((Subtype.val : dom t → _) ⁻¹'
      riemannianClosedBallOf (Hm).metric y R) :=
    hAclosed.preimage continuous_subtype_val
  let f : dom t → (postStage F.observation t).Carrier := fun x => mp t ht x
  set gb := scaleMetric t⁻¹ (inv_pos.mpr (hst.trans_le ht)) (postMetric F.observation t)
    with hgb
  let gp := DifferentialGeometry.Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph gb f hf hinj
  have hmetric : ∀ (x : dom t) (v w : TangentSpace (𝓡 3) x), gp.inner x v w =
      gb.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) :=
    DifferentialGeometry.Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph_inner gb f hf hinj
  have h1 := DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry
    gp gb f hf hinj hmetric hSclosed.measurableSet
  have himg : f '' (Subtype.val ⁻¹' riemannianClosedBallOf (Hm).metric y R) =
      mp t ht '' riemannianClosedBallOf (Hm).metric y R := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.val, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hAU hx⟩, hx, rfl⟩
  rw [← himg, ← h1]
  have hS2 := Geometry.Measure.riemannianVolumeMeasure_restrictOpen_preimage_of_subset
    (Hm).metric (dom t) hAclosed.measurableSet hAU
  have hcomp : ∀ x ∈ (Subtype.val ⁻¹' riemannianClosedBallOf (Hm).metric y R :
      Set (dom t)), ∀ v : TangentSpace (𝓡 3) x,
      gp.inner x v v ≤ (5 / 4 : ℝ) * ((Hm).metric.restrictOpen (dom t)).inner x v v := by
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
    have hup := bufferedMap_metric_upper_O27 hst hD t ht x.val (hsub hx) v
    have hnn := metric_inner_self_nonneg (Hm).metric x.val v
    have hδ' : (1 + acc t) ≤ 5 / 4 := by linarith
    calc _ ≤ (1 + acc t) * (Hm).metric.inner x.val v v := hup
      _ ≤ _ := mul_le_mul_of_nonneg_right hδ' hnn
  have hle := DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.riemannianVolumeMeasure_le_on ((Hm).metric.restrictOpen (dom t)) gp
    hSclosed.measurableSet (by norm_num : (0 : ℝ) < 5 / 4) hcomp
  rw [hS2] at hle
  refine hle.trans (mul_le_mul' ?_ le_rfl)
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.sqrt_le_iff]
  refine ⟨by norm_num, ?_⟩
  have : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  rw [this]
  norm_num

theorem bufferedMap_ballVolume_le_O27 (hst : 0 < st) (hD : ((∀ t (ht : st ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mp t ht) (dom t)) ∧
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
    (hδ : acc t ≤ 1 / 4) {r : ℝ} (hr : 0 < r) (hr8 : r ^ 2 ≤ 8) :
    ballVolume (scaleMetric t⁻¹ (inv_pos.mpr (hst.trans_le ht)) (postMetric F.observation t))
        (mp t ht y) r ≤ ENNReal.ofReal 2 * ballVolume (Hm).metric y 4 := by
  have hδpos := hD.2.2.2.2.1 t ht
  have hpos : 0 < 1 - acc t := by linarith
  have hsq : 0 < Real.sqrt (1 - acc t) := Real.sqrt_pos.mpr hpos
  have hn4 : 4 ≤ (acc t)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hδpos]
    norm_num
    exact hδ
  set R : ℝ := r / Real.sqrt (1 - acc t) with hR
  have hRr : R * Real.sqrt (1 - acc t) = r := by
    rw [hR]; field_simp
  have hRpos : 0 < R := div_pos hr hsq
  have hR2 : R ^ 2 * (1 - acc t) = r ^ 2 := by
    rw [← hRr, mul_pow, Real.sq_sqrt hpos.le]
  have hR4 : R < 4 := by
    have : R ^ 2 < 4 ^ 2 := by nlinarith [sq_nonneg R]
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) this
  have hcap := bufferedMap_ball_subset_image_O27 hst hD t ht y hy hRpos (hR4.le.trans hn4)
    (by linarith)
  rw [hRr] at hcap
  have hvol := bufferedMap_image_volume_le_O27 hst hD t ht y hy (hR4.le.trans hn4) hδ
  have hclosed : riemannianClosedBallOf (Hm).metric y R ⊆
      riemannianBallOf (Hm).metric y 4 := by
    intro x hx
    exact lt_of_le_of_lt hx ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hR4)
  unfold ballVolume
  calc _ ≤ _ := MeasureTheory.measure_mono hcap
    _ ≤ _ := hvol
    _ ≤ _ := mul_le_mul' le_rfl (MeasureTheory.measure_mono hclosed)

end GC.LongTime.Ch12
