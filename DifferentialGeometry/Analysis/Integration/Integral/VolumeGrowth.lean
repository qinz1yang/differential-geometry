import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.CompactBall
import DifferentialGeometry.Geometry.Comparison.Volume.Model
import DifferentialGeometry.Geometry.Comparison.Volume.VolumeNaturality
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem volume_ball_le (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete g) (p : M) {r : ℝ} (hr : 0 < r)
    (hRic : BonnetMyers.RicciBoundedBelow (I := I) g 0) :
    riemannianVolumeMeasure (I := I) (M := M) g {x | riemannianEDistOf g p x < ENNReal.ofReal r} ≤
      ENNReal.ofReal (euclideanUnitBallVolume (Module.finrank ℝ E) * r ^ Module.finrank ℝ E) := by
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  have hnorm : IsMetricNorm (I := I) g := fun x v =>
    tensor0SBundle_enorm_eq_riemannianBundle_enorm g x v
  have hcpt := hg.closedEBall_isCompact p r
  simp_rw [riemannianEDistOf_eq_riemannianEDist g hnorm] at hcpt ⊢
  have hcpt' : IsCompact (Metric.closedEBall p (ENNReal.ofReal r)) := by
    change IsCompact {x | riemannianEDist I x p ≤ ENNReal.ofReal r}
    simpa only [riemannianEDist_comm] using hcpt
  have h := riemannianVolumeMeasure_ball_le_hyperbolic_of_isCompact_closedEBall g hnorm p
    (q := 0) (by rfl) hr hcpt' (fun x v _ => by simpa using hRic x v)
  have hn : 1 ≤ Module.finrank ℝ E := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  rw [← ofReal_modelVolume_neg_sq 0 r (Module.finrank ℝ E) hn (by rfl)] at h
  simpa only [zero_pow (by decide : 2 ≠ 0), neg_zero, modelVolume_zero _ _ hn] using h

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem integral_le_of_support_subset_ball_of_ricci_nonnegative
    (g h : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g)
    (hRic : BonnetMyers.RicciBoundedBelow (I := I) g 0)
    (p : M) {r Q B : ℝ} (hr : 0 < r) (hQ : 0 < Q)
    (hcomp : ∀ x, riemannianEDistOf g p x < ENNReal.ofReal r →
      ∀ v : TangentSpace I x, h.inner x v v ≤ Q * g.inner x v v)
    {f : M → ℝ} (hf : ∀ x, f x ∈ Icc 0 B)
    (hsupport : Function.support f ⊆ {x | riemannianEDistOf g p x < ENNReal.ofReal r}) :
    (∫ x, f x ∂riemannianVolumeMeasure (I := I) (M := M) h) ≤
      B * Real.sqrt (Q ^ Module.finrank ℝ E) *
        euclideanUnitBallVolume (Module.finrank ℝ E) * r ^ Module.finrank ℝ E := by
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  let A : Set M := {x | riemannianEDistOf g p x < ENNReal.ofReal r}
  have hd : Continuous (fun x => riemannianEDistOf g p x) := by
    let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
    let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    exact continuous_const.edist continuous_id
  have hA : MeasurableSet A := (isOpen_lt hd continuous_const).measurableSet
  have hV := (riemannianVolumeMeasure_apply_le_of_inner_le_on g h hA hQ
    (fun x hx v => hcomp x hx v)).trans
      (mul_le_mul_right (volume_ball_le g hg p hr hRic) _)
  let V := Real.sqrt (Q ^ Module.finrank ℝ E) *
    (euclideanUnitBallVolume (Module.finrank ℝ E) * r ^ Module.finrank ℝ E)
  have hω := euclideanUnitBallVolume_pos (Module.finrank ℝ E)
  have hV0 : 0 ≤ V := by dsimp [V]; positivity
  have hV' : riemannianVolumeMeasure (I := I) (M := M) h A ≤ ENNReal.ofReal V := by
    simpa only [V, ENNReal.ofReal_mul (Real.sqrt_nonneg _)] using hV
  have hfinite : riemannianVolumeMeasure (I := I) (M := M) h A < ⊤ := hV'.trans_lt ENNReal.ofReal_lt_top
  have hB : 0 ≤ B := (hf p).1.trans (hf p).2
  have hi : Integrable (A.indicator (fun _ : M => B)) (riemannianVolumeMeasure (I := I) (M := M) h) := by
    rw [integrable_indicator_iff hA]
    exact integrableOn_const hfinite.ne
  have hle : (∫ x, f x ∂riemannianVolumeMeasure (I := I) (M := M) h) ≤
      (riemannianVolumeMeasure (I := I) (M := M) h A).toReal * B := by
    calc _ ≤ ∫ x, A.indicator (fun _ : M => B) x ∂riemannianVolumeMeasure (I := I) (M := M) h := by
            apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => (hf x).1) hi
            filter_upwards [] with x
            by_cases hx : x ∈ A
            · simpa only [indicator_of_mem hx] using (hf x).2
            · have hz : f x = 0 := not_not.mp (fun hn => hx (hsupport hn))
              simp only [indicator_of_notMem hx, hz, le_refl]
         _ = _ := by simp only [integral_indicator hA, setIntegral_const, smul_eq_mul, measureReal_def]
  have hvle : (riemannianVolumeMeasure (I := I) (M := M) h A).toReal ≤ V :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hV').trans_eq (ENNReal.toReal_ofReal hV0)
  calc _ ≤ V * B := hle.trans (mul_le_mul_of_nonneg_right hvle hB)
       _ = _ := by dsimp [V]; ring

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
