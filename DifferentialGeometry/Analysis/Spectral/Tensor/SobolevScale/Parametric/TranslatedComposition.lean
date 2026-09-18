import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.TimeComposition
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.SimultaneousComposition
import DifferentialGeometry.Analysis.FunctionalAnalysis.ContinuousLinearMap.ClosedBall
import DifferentialGeometry.Analysis.FunctionalAnalysis.ClosedBall

noncomputable section
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {ι : Type*} [Fintype ι]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold 𝓘(ℝ, ℝ) ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
  [BoundarylessManifold 𝓘(ℝ, ℝ) M]

theorem exists_scalar_vectorH1_time_composition_on_symmetric_translated_closedBall
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M) (n : ℕ)
    (J : X →L[ℝ] PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) (t₀ : ℝ) (f₀ : X)
    (F : (Option ι → ℝ) → ℝ) (G : (Option ι → ℝ) → (Fin n → ℝ))
    {U : Set (Option ι → ℝ)} (hF : ContDiffOn ℝ ∞ F U) (hG : ContDiffOn ℝ ∞ G U)
    (hU : IsOpen U)
    (hf₀ : Set.range (scalarH1PiToContinuous g (scalarH1TimeCoordinate g (t₀, J f₀))) ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ), ‖J‖ * δ ≤ r ∧
      ∃ Ca Cb : ℝ≥0,
      r ≤ ε ∧ (Ca : ℝ) * r ≤ ε ∧ (Cb : ℝ) * r ≤ ε ∧
      ∃ alpha : Metric.closedBall f₀ δ → ℝ →
        Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) r → TensorHs g 0 0 1,
      ∃ reaction : Metric.closedBall f₀ δ → ℝ →
        Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) r →
          PiLp 2 (fun _ : Fin n => TensorHs g 0 0 1),
      (∀ f, LipschitzWith Ca (fun p : ℝ × Metric.closedBall
        (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) r => alpha f p.1 p.2)) ∧
      (∀ f, LipschitzWith Cb (fun p : ℝ × Metric.closedBall
        (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) r => reaction f p.1 p.2)) ∧
      (∀ f t, t ∈ Set.Icc (-r) r → ∀ v,
        ‖alpha f t v - alpha ⟨f₀, Metric.mem_closedBall_self hδ.le⟩ 0
          ⟨0, Metric.mem_closedBall_self hr.le⟩‖ ≤ (Ca : ℝ) * (2 * r)) ∧
      (∀ f t, t ∈ Set.Icc (-r) r → ∀ v,
        ‖reaction f t v - reaction ⟨f₀, Metric.mem_closedBall_self hδ.le⟩ 0
          ⟨0, Metric.mem_closedBall_self hr.le⟩‖ ≤ (Cb : ℝ) * (2 * r)) ∧
      (∀ f k t s v, ‖alpha f t v - alpha k s v‖ ≤
        (Ca : ℝ) * max |t - s| ‖J (f - k)‖) ∧
      (∀ f k t s v, ‖reaction f t v - reaction k s v‖ ≤
        (Cb : ℝ) * max |t - s| ‖J (f - k)‖) ∧
      (∀ (f : Metric.closedBall f₀ δ) t
        (v : Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) r),
        t ∈ Set.Icc (-r) r →
        Set.range (scalarH1PiToContinuous g (scalarH1TimeCoordinate g (t₀ + t, J f + v.val))) ⊆ U) ∧
      (∀ f t, t ∈ Set.Icc (-r) r → ∀ v x,
        scalarH1ToContinuous g (alpha f t v) x = F (fun i => match i with
          | none => t₀ + t
          | some i => scalarH1ToContinuous g ((J f) i + v.val i) x)) ∧
      (∀ f t, t ∈ Set.Icc (-r) r → ∀ v x j,
        scalarH1ToContinuous g (reaction f t v j) x = G (fun i => match i with
          | none => t₀ + t
          | some i => scalarH1ToContinuous g ((J f) i + v.val i) x) j) := by
  obtain ⟨R, hR, Ca, Cb, a, b, ha, hb, hRange, haeval, hbeval⟩ :=
    exists_scalar_vectorH1_time_composition_on_symmetric_time_interval
      g n F G hF hG hU t₀ (J f₀) hf₀
  let r := min (R / 2) (ε / ((Ca : ℝ) + Cb + 1))
  have hr : 0 < r := by dsimp only [r]; positivity
  have hrR : 2 * r ≤ R := by
    have := min_le_left (R / 2) (ε / ((Ca : ℝ) + Cb + 1))
    dsimp only [r]
    linarith
  have hsmall : ((Ca : ℝ) + Cb + 1) * r ≤ ε := by
    have hdenom : 0 < (Ca : ℝ) + Cb + 1 := by positivity
    have h := (le_div_iff₀ hdenom).mp
      (min_le_right (R / 2) (ε / ((Ca : ℝ) + Cb + 1)))
    simpa only [mul_comm] using h
  have hrε : r ≤ ε := by nlinarith [Ca.coe_nonneg, Cb.coe_nonneg]
  have hCaε : (Ca : ℝ) * r ≤ ε := by nlinarith [Cb.coe_nonneg]
  have hCbε : (Cb : ℝ) * r ≤ ε := by nlinarith [Ca.coe_nonneg]
  obtain ⟨δ, hδ, _, hJδ⟩ := J.exists_pos_norm_mul_le hr
  have hJf (f : Metric.closedBall f₀ δ) : ‖J (f - f₀)‖ ≤ r := by
    have hf : ‖f.val - f₀‖ ≤ δ := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using f.property
    exact (J.le_opNorm _).trans
      ((mul_le_mul_of_nonneg_left hf (norm_nonneg J)).trans hJδ)
  let shift : Metric.closedBall f₀ δ →
      Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) r →
      Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) R :=
    fun f => Metric.closedBallTranslate (J (f - f₀))
      ((add_le_add (hJf f) le_rfl).trans (by simpa only [two_mul] using hrR))
  have heq (f : Metric.closedBall f₀ δ) (v : Metric.closedBall
      (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) r) :
      J f₀ + (shift f v).val = J f + v.val := by
    simp only [shift, Metric.closedBallTranslate_coe, map_sub]
    abel
  have hshift0 : shift ⟨f₀, Metric.mem_closedBall_self hδ.le⟩
      ⟨0, Metric.mem_closedBall_self hr.le⟩ =
      ⟨0, Metric.mem_closedBall_self hR.le⟩ := by
    apply Subtype.ext
    simp only [shift, Metric.closedBallTranslate_coe, sub_self, map_zero, add_zero]
  refine ⟨r, δ, hr, hδ, hJδ, Ca, Cb, hrε, hCaε, hCbε,
    fun f t v => a t (shift f v), fun f t v => b t (shift f v),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    apply LipschitzWith.of_dist_le_mul
    intro p q
    simpa only [Prod.dist_eq, Subtype.dist_eq, shift, Metric.closedBallTranslate_coe,
      dist_add_left] using
      ha.dist_le_mul (p.1, shift f p.2) (q.1, shift f q.2)
  · intro f
    apply LipschitzWith.of_dist_le_mul
    intro p q
    simpa only [Prod.dist_eq, Subtype.dist_eq, shift, Metric.closedBallTranslate_coe,
      dist_add_left] using
      hb.dist_le_mul (p.1, shift f p.2) (q.1, shift f q.2)
  · intro f t ht v
    dsimp only
    rw [hshift0]
    have hsp : ‖J (f - f₀) + v.val‖ ≤ 2 * r := by
      have hv : ‖v.val‖ ≤ r := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using v.property
      simpa only [two_mul] using (norm_add_le _ _).trans (add_le_add (hJf f) hv)
    have htime : |t| ≤ 2 * r := (abs_le.mpr ht).trans (by linarith)
    have hdist := ha.dist_le_mul (t, shift f v)
      (0, ⟨0, Metric.mem_closedBall_self hR.le⟩)
    have hn : ‖a t (shift f v) - a 0 ⟨0, Metric.mem_closedBall_self hR.le⟩‖ ≤
        (Ca : ℝ) * max |t| ‖J (f - f₀) + v.val‖ := by
      simpa only [Prod.dist_eq, Subtype.dist_eq, shift, Metric.closedBallTranslate_coe,
        dist_zero_right, dist_eq_norm, sub_zero, Real.norm_eq_abs] using hdist
    exact hn.trans (mul_le_mul_of_nonneg_left (max_le htime hsp) Ca.coe_nonneg)
  · intro f t ht v
    dsimp only
    rw [hshift0]
    have hsp : ‖J (f - f₀) + v.val‖ ≤ 2 * r := by
      have hv : ‖v.val‖ ≤ r := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using v.property
      simpa only [two_mul] using (norm_add_le _ _).trans (add_le_add (hJf f) hv)
    have htime : |t| ≤ 2 * r := (abs_le.mpr ht).trans (by linarith)
    have hdist := hb.dist_le_mul (t, shift f v)
      (0, ⟨0, Metric.mem_closedBall_self hR.le⟩)
    have hn : ‖b t (shift f v) - b 0 ⟨0, Metric.mem_closedBall_self hR.le⟩‖ ≤
        (Cb : ℝ) * max |t| ‖J (f - f₀) + v.val‖ := by
      simpa only [Prod.dist_eq, Subtype.dist_eq, shift, Metric.closedBallTranslate_coe,
        dist_zero_right, dist_eq_norm, sub_zero, Real.norm_eq_abs] using hdist
    exact hn.trans (mul_le_mul_of_nonneg_left (max_le htime hsp) Cb.coe_nonneg)
  · intro f k t s v
    have heqfk : J (f - f₀) - J (k - f₀) = J (f - k) := by
      rw [← map_sub]
      congr 1
      abel
    simpa only [Prod.dist_eq, Subtype.dist_eq, shift, Metric.closedBallTranslate_coe,
      dist_add_right, dist_eq_norm, Real.norm_eq_abs, add_sub_add_right_eq_sub, heqfk] using
      ha.dist_le_mul (t, shift f v) (s, shift k v)
  · intro f k t s v
    have heqfk : J (f - f₀) - J (k - f₀) = J (f - k) := by
      rw [← map_sub]
      congr 1
      abel
    simpa only [Prod.dist_eq, Subtype.dist_eq, shift, Metric.closedBallTranslate_coe,
      dist_add_right, dist_eq_norm, Real.norm_eq_abs, add_sub_add_right_eq_sub, heqfk] using
      hb.dist_le_mul (t, shift f v) (s, shift k v)
  · intro f t v ht
    have hrR' : r ≤ R := by linarith
    have htR : t ∈ Set.Icc (-R) R := ⟨(neg_le_neg hrR').trans ht.1, ht.2.trans hrR'⟩
    simpa only [zero_add, heq] using hRange t htR (shift f v).val (shift f v).property
  · intro f t ht v x
    have hrR' : r ≤ R := by linarith
    have htR : t ∈ Set.Icc (-R) R := ⟨(neg_le_neg hrR').trans ht.1, ht.2.trans hrR'⟩
    have h := haeval t htR (shift f v) x
    have hpoint (i : ι) : J f₀ i + (shift f v).val i = J f i + v.val i := by
      exact congrArg (fun u => u i) (heq f v)
    calc
      _ = _ := h
      _ = _ := by
        congr 1
        funext i
        cases i with
        | none => rfl
        | some i =>
          change scalarH1ToContinuous g (J f₀ i + (shift f v).val i) x =
            scalarH1ToContinuous g (J f i + v.val i) x
          rw [hpoint]
  · intro f t ht v x j
    have hrR' : r ≤ R := by linarith
    have htR : t ∈ Set.Icc (-R) R := ⟨(neg_le_neg hrR').trans ht.1, ht.2.trans hrR'⟩
    have h := hbeval t htR (shift f v) x j
    have hpoint (i : ι) : J f₀ i + (shift f v).val i = J f i + v.val i := by
      exact congrArg (fun u => u i) (heq f v)
    calc
      _ = _ := h
      _ = _ := by
        congr 1
        funext i
        cases i with
        | none => rfl
        | some i =>
          change scalarH1ToContinuous g (J f₀ i + (shift f v).val i) x =
            scalarH1ToContinuous g (J f i + v.val i) x
          rw [hpoint]


theorem exists_scalar_vectorH1_time_composition_on_translated_closedBall
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M) (n : ℕ)
    (J : X →L[ℝ] PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) (f₀ : X)
    (F : (Option ι → ℝ) → ℝ) (G : (Option ι → ℝ) → (Fin n → ℝ))
    {U : Set (Option ι → ℝ)} (hF : ContDiffOn ℝ ∞ F U) (hG : ContDiffOn ℝ ∞ G U)
    (hU : IsOpen U)
    (hf₀ : Set.range (scalarH1PiToContinuous g (scalarH1TimeCoordinate g (0, J f₀))) ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ), ‖J‖ * δ ≤ r ∧
      ∃ Ca Cb : ℝ≥0,
      r ≤ ε ∧ (Ca : ℝ) * r ≤ ε ∧ (Cb : ℝ) * r ≤ ε ∧
      ∃ alpha : Metric.closedBall f₀ δ → ℝ →
        Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) r → TensorHs g 0 0 1,
      ∃ reaction : Metric.closedBall f₀ δ → ℝ →
        Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) r →
          PiLp 2 (fun _ : Fin n => TensorHs g 0 0 1),
      (∀ f, LipschitzWith Ca (fun p : ℝ × Metric.closedBall
        (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) r => alpha f p.1 p.2)) ∧
      (∀ f, LipschitzWith Cb (fun p : ℝ × Metric.closedBall
        (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) r => reaction f p.1 p.2)) ∧
      (∀ f t, t ∈ Set.Icc (0 : ℝ) r → ∀ v,
        ‖alpha f t v - alpha ⟨f₀, Metric.mem_closedBall_self hδ.le⟩ 0
          ⟨0, Metric.mem_closedBall_self hr.le⟩‖ ≤ (Ca : ℝ) * (2 * r)) ∧
      (∀ f t, t ∈ Set.Icc (0 : ℝ) r → ∀ v,
        ‖reaction f t v - reaction ⟨f₀, Metric.mem_closedBall_self hδ.le⟩ 0
          ⟨0, Metric.mem_closedBall_self hr.le⟩‖ ≤ (Cb : ℝ) * (2 * r)) ∧
      (∀ f k t v, ‖alpha f t v - alpha k t v‖ ≤ (Ca : ℝ) * ‖J (f - k)‖) ∧
      (∀ f k t v, ‖reaction f t v - reaction k t v‖ ≤ (Cb : ℝ) * ‖J (f - k)‖) ∧
      (∀ (f : Metric.closedBall f₀ δ) t (v : Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) r),
        t ∈ Set.Icc (0 : ℝ) r →
        Set.range (scalarH1PiToContinuous g (scalarH1TimeCoordinate g (t, J f + v.val))) ⊆ U) ∧
      (∀ f t, t ∈ Set.Icc (0 : ℝ) r → ∀ v x,
        scalarH1ToContinuous g (alpha f t v) x = F (fun i => match i with
          | none => t
          | some i => scalarH1ToContinuous g ((J f) i + v.val i) x)) ∧
      (∀ f t, t ∈ Set.Icc (0 : ℝ) r → ∀ v x j,
        scalarH1ToContinuous g (reaction f t v j) x = G (fun i => match i with
          | none => t
          | some i => scalarH1ToContinuous g ((J f) i + v.val i) x) j) := by
  obtain ⟨R, hR, Ca, Cb, a, b, ha, hb, hRange, haeval, hbeval⟩ :=
    exists_scalar_vectorH1_time_composition_on_closedBall g n F G hF hG hU 0 (J f₀) hf₀
  let r := min (R / 2) (ε / ((Ca : ℝ) + Cb + 1))
  have hr : 0 < r := by dsimp only [r]; positivity
  have hrR : 2 * r ≤ R := by
    have := min_le_left (R / 2) (ε / ((Ca : ℝ) + Cb + 1))
    dsimp only [r]
    linarith
  have hsmall : ((Ca : ℝ) + Cb + 1) * r ≤ ε := by
    have hdenom : 0 < (Ca : ℝ) + Cb + 1 := by positivity
    have h := (le_div_iff₀ hdenom).mp
      (min_le_right (R / 2) (ε / ((Ca : ℝ) + Cb + 1)))
    simpa only [mul_comm] using h
  have hrε : r ≤ ε := by nlinarith [Ca.coe_nonneg, Cb.coe_nonneg]
  have hCaε : (Ca : ℝ) * r ≤ ε := by nlinarith [Cb.coe_nonneg]
  have hCbε : (Cb : ℝ) * r ≤ ε := by nlinarith [Ca.coe_nonneg]
  obtain ⟨δ, hδ, _, hJδ⟩ := J.exists_pos_norm_mul_le hr
  have hJf (f : Metric.closedBall f₀ δ) : ‖J (f - f₀)‖ ≤ r := by
    have hf : ‖f.val - f₀‖ ≤ δ := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using f.property
    exact (J.le_opNorm _).trans
      ((mul_le_mul_of_nonneg_left hf (norm_nonneg J)).trans hJδ)
  let shift : Metric.closedBall f₀ δ →
      Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) r →
      Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) R :=
    fun f => Metric.closedBallTranslate (J (f - f₀))
      ((add_le_add (hJf f) le_rfl).trans (by simpa only [two_mul] using hrR))
  have heq (f : Metric.closedBall f₀ δ) (v : Metric.closedBall
      (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) r) :
      J f₀ + (shift f v).val = J f + v.val := by
    simp only [shift, Metric.closedBallTranslate_coe, map_sub]
    abel
  have hshift0 : shift ⟨f₀, Metric.mem_closedBall_self hδ.le⟩
      ⟨0, Metric.mem_closedBall_self hr.le⟩ =
      ⟨0, Metric.mem_closedBall_self hR.le⟩ := by
    apply Subtype.ext
    simp only [shift, Metric.closedBallTranslate_coe, sub_self, map_zero, add_zero]
  refine ⟨r, δ, hr, hδ, hJδ, Ca, Cb, hrε, hCaε, hCbε,
    fun f t v => a t (shift f v), fun f t v => b t (shift f v),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    apply LipschitzWith.of_dist_le_mul
    intro p q
    simpa only [Prod.dist_eq, Subtype.dist_eq, shift, Metric.closedBallTranslate_coe,
      dist_add_left] using
      ha.dist_le_mul (p.1, shift f p.2) (q.1, shift f q.2)
  · intro f
    apply LipschitzWith.of_dist_le_mul
    intro p q
    simpa only [Prod.dist_eq, Subtype.dist_eq, shift, Metric.closedBallTranslate_coe,
      dist_add_left] using
      hb.dist_le_mul (p.1, shift f p.2) (q.1, shift f q.2)
  · intro f t ht v
    dsimp only
    rw [hshift0]
    exact ha.norm_sub_origin_time_precomp_closedBallTranslate
      (J (f - f₀)) (hJf f) hr.le hrR t ht v
  · intro f t ht v
    dsimp only
    rw [hshift0]
    exact hb.norm_sub_origin_time_precomp_closedBallTranslate
      (J (f - f₀)) (hJf f) hr.le hrR t ht v
  · intro f k t v
    have heqfk : J (f - f₀) - J (k - f₀) = J (f - k) := by
      rw [← map_sub]
      congr 1
      abel
    simpa only [heqfk] using ha.norm_sub_time_closedBallTranslate
      (J (f - f₀)) (J (k - f₀))
      ((add_le_add (hJf f) le_rfl).trans (by simpa only [two_mul] using hrR))
      ((add_le_add (hJf k) le_rfl).trans (by simpa only [two_mul] using hrR)) t v
  · intro f k t v
    have heqfk : J (f - f₀) - J (k - f₀) = J (f - k) := by
      rw [← map_sub]
      congr 1
      abel
    simpa only [heqfk] using hb.norm_sub_time_closedBallTranslate
      (J (f - f₀)) (J (k - f₀))
      ((add_le_add (hJf f) le_rfl).trans (by simpa only [two_mul] using hrR))
      ((add_le_add (hJf k) le_rfl).trans (by simpa only [two_mul] using hrR)) t v
  · intro f t v ht
    have htR : t ∈ Set.Icc (0 : ℝ) R := ⟨ht.1, ht.2.trans (by dsimp only [r]; linarith)⟩
    simpa only [zero_add, heq] using hRange t htR (shift f v).val (shift f v).property
  · intro f t ht v x
    have htR : t ∈ Set.Icc (0 : ℝ) R := ⟨ht.1, ht.2.trans (by dsimp only [r]; linarith)⟩
    have h := haeval t htR (shift f v) x
    have hpoint (i : ι) : J f₀ i + (shift f v).val i = J f i + v.val i := by
      exact congrArg (fun u => u i) (heq f v)
    calc
      _ = _ := h
      _ = _ := by
        congr 1
        funext i
        cases i with
        | none => simp only [zero_add]
        | some i =>
          change scalarH1ToContinuous g (J f₀ i + (shift f v).val i) x =
            scalarH1ToContinuous g (J f i + v.val i) x
          rw [hpoint]
  · intro f t ht v x j
    have htR : t ∈ Set.Icc (0 : ℝ) R := ⟨ht.1, ht.2.trans (by dsimp only [r]; linarith)⟩
    have h := hbeval t htR (shift f v) x j
    have hpoint (i : ι) : J f₀ i + (shift f v).val i = J f i + v.val i := by
      exact congrArg (fun u => u i) (heq f v)
    calc
      _ = _ := h
      _ = _ := by
        congr 1
        funext i
        cases i with
        | none => simp only [zero_add]
        | some i =>
          change scalarH1ToContinuous g (J f₀ i + (shift f v).val i) x =
            scalarH1ToContinuous g (J f i + v.val i) x
          rw [hpoint]

end DifferentialGeometry.Analysis.Spectral

end

noncomputable section

open Set
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {ι : Type*} [Fintype ι]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold 𝓘(ℝ, ℝ) ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M]

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

theorem exists_scalarH1TimeCoordinate_bounds_on_translated_closedBall
    {X Y : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M)
    (P : X →L[ℝ] PiLp 2 (fun _ : ι => TensorHs g 0 0 1))
    (J : Y →L[ℝ] PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) (f₀ : X)
    {S : Set (Option ι → ℝ)} (hS : IsOpen S)
    (hf₀ : range (scalarH1PiToContinuous g (scalarH1TimeCoordinate g (0, P f₀))) ⊆ S) :
    ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧
      ∃ Krange : Set (Option ι → ℝ), IsCompact Krange ∧ Krange ⊆ S ∧
      ∃ R : ℝ, 0 ≤ R ∧ ∀ f : X, dist f f₀ ≤ δ →
        ∀ t ∈ Icc (0 : ℝ) ρ, ∀ w : Y, ‖w‖ ≤ ρ →
          range (scalarH1PiToContinuous g (scalarH1TimeCoordinate g (t, P f + J w))) ⊆ Krange ∧
            (∑ i, ‖scalarH1TimeCoordinate g (t, P f + J w) i‖) ≤ R := by
  let q₀ := scalarH1TimeCoordinate g (0, P f₀)
  obtain ⟨η, hη, Krange, hK, hKS, hrange⟩ :=
    exists_scalarH1Pi_ball_range_subset g q₀ hS hf₀
  let A : X × Y →L[ℝ] PiLp 2 (fun _ : ι => TensorHs g 0 0 1) :=
    P.comp (ContinuousLinearMap.fst ℝ X Y) + J.comp (ContinuousLinearMap.snd ℝ X Y)
  let B : ℝ × (X × Y) →L[ℝ] PiLp 2 (fun _ : Option ι => TensorHs g 0 0 1) :=
    (scalarH1TimeCoordinate g).comp ((ContinuousLinearMap.fst ℝ ℝ (X × Y)).prod
      (A.comp (ContinuousLinearMap.snd ℝ ℝ (X × Y))))
  obtain ⟨r, hr, _, hB⟩ := B.exists_pos_norm_mul_le (half_pos hη)
  let R := (Fintype.card (Option ι) : ℝ) * (‖q₀‖ + η)
  refine ⟨r, r, hr, hr, Krange, hK, hKS, R, by positivity, ?_⟩
  intro f hf t ht w hw
  have hp : ‖(t, (f - f₀, w))‖ ≤ r := by
    rw [Prod.norm_def, Prod.norm_def]
    apply max_le
    · simpa only [Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
    · exact max_le (by simpa only [dist_eq_norm] using hf) hw
  have hpert : ‖B (t, (f - f₀, w))‖ < η := by
    calc
      _ ≤ ‖B‖ * ‖(t, (f - f₀, w))‖ := B.le_opNorm _
      _ ≤ ‖B‖ * r := mul_le_mul_of_nonneg_left hp (norm_nonneg B)
      _ ≤ η / 2 := hB
      _ < η := half_lt_self hη
  have hq : scalarH1TimeCoordinate g (t, P f + J w) = q₀ + B (t, (f - f₀, w)) := by
    change scalarH1TimeCoordinate g (t, P f + J w) =
      scalarH1TimeCoordinate g (0, P f₀) + scalarH1TimeCoordinate g (t, P (f - f₀) + J w)
    rw [← map_add]
    congr 1
    simp only [Prod.mk_add_mk, zero_add, map_sub]
    abel_nf
  have hmem : scalarH1TimeCoordinate g (t, P f + J w) ∈ Metric.ball q₀ η := by
    rw [Metric.mem_ball, dist_eq_norm, hq, add_sub_cancel_left]
    exact hpert
  refine ⟨hrange _ hmem, ?_⟩
  have hnorm : ‖scalarH1TimeCoordinate g (t, P f + J w)‖ ≤ ‖q₀‖ + η := by
    rw [hq]
    exact (norm_add_le _ _).trans (add_le_add le_rfl hpert.le)
  calc
    _ ≤ ∑ _i : Option ι, ‖scalarH1TimeCoordinate g (t, P f + J w)‖ :=
      Finset.sum_le_sum (fun i _ => PiLp.norm_apply_le _ i)
    _ = (Fintype.card (Option ι) : ℝ) * ‖scalarH1TimeCoordinate g (t, P f + J w)‖ := by simp
    _ ≤ R := mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg _)

end DifferentialGeometry.Analysis.Spectral

end
