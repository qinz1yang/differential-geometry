import DifferentialGeometry.Geometry.Metric.Scaling
import Mathlib.Geometry.Manifold.Riemannian.PathELength

set_option autoImplicit false

/-!
# Distance under constant metric scaling

This file exposes Mathlib's path-length distance with the Riemannian metric as
an explicit argument and proves its behavior under positive constant scaling.
The explicit wrapper keeps the norm-instance choice local to this metric layer.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Riemannian extended distance with the metric supplied explicitly. -/
noncomputable def riemannianEDistOf
    (g : SmoothRiemannianMetric I M) (x y : M) : ℝ≥0∞ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  Manifold.riemannianEDist I x y

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
private theorem edistOf_iInf
    (g : SmoothRiemannianMetric I M) (x y : M) :
    riemannianEDistOf (I := I) g x y =
      ⨅ (γ : Path x y) (_ : CMDiff 1 γ),
        ∫⁻ t, ENNReal.ofReal (Real.sqrt
          (g.inner (γ t) (mfderiv% γ t 1) (mfderiv% γ t 1))) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change Manifold.riemannianEDist I x y = _
  rw [Manifold.riemannianEDist]
  refine iInf_congr fun γ => ?_
  refine iInf_congr fun hγ => ?_
  refine lintegral_congr fun t => ?_
  rw [← ofReal_norm_eq_enorm, norm_eq_sqrt_real_inner]
  congr 2

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Pointwise domination of Riemannian metrics implies domination of their
extended distances. -/
theorem edistOf_mono
    (g h : SmoothRiemannianMetric I M)
    (hgh : ∀ x v, g.inner x v v ≤ h.inner x v v)
    (x y : M) :
    riemannianEDistOf (I := I) g x y ≤
      riemannianEDistOf (I := I) h x y := by
  rw [edistOf_iInf, edistOf_iInf]
  refine iInf_mono fun γ => ?_
  refine iInf_mono fun hγ => ?_
  refine lintegral_mono fun t => ?_
  exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (hgh (γ t) _))

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Positive constant metric scaling multiplies Riemannian extended distance
by the square root of the scaling constant. -/
theorem edistOf_scale
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (x y : M) :
    riemannianEDistOf (I := I) (scaleMetric (I := I) c hc g) x y =
      ENNReal.ofReal (Real.sqrt c) * riemannianEDistOf (I := I) g x y := by
  rw [edistOf_iInf, edistOf_iInf]
  let a : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt c)
  have ha0 : a ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.2 hc))
  have hatop : a ≠ (∞ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  change
    (⨅ (γ : Path x y) (_ : CMDiff 1 γ),
      ∫⁻ t, ENNReal.ofReal (Real.sqrt
        ((scaleMetric (I := I) c hc g).inner
          (γ t) (mfderiv% γ t 1) (mfderiv% γ t 1))) =
      a * ⨅ (γ : Path x y) (_ : CMDiff 1 γ),
        ∫⁻ t, ENNReal.ofReal (Real.sqrt
          (g.inner (γ t) (mfderiv% γ t 1) (mfderiv% γ t 1))))
  rw [ENNReal.mul_iInf_of_ne ha0 hatop]
  refine iInf_congr fun γ => ?_
  rw [ENNReal.mul_iInf_of_ne ha0 hatop]
  refine iInf_congr fun hγ => ?_
  rw [← lintegral_const_mul' a _ hatop]
  refine lintegral_congr fun t => ?_
  simp only [scaleMetric_inner]
  rw [Real.sqrt_mul hc.le]
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg c)]

/-- A pointwise quadratic upper bound gives the corresponding square-root
upper bound on Riemannian extended distance. -/
theorem edistOf_le_of_quad
    (g h : SmoothRiemannianMetric I M) {c : Real} (hc : 0 < c)
    (hu : ∀ x v, h.inner x v v ≤ c * g.inner x v v)
    (x y : M) :
    riemannianEDistOf (I := I) h x y ≤
      ENNReal.ofReal (Real.sqrt c) * riemannianEDistOf (I := I) g x y := by
  calc
    riemannianEDistOf (I := I) h x y ≤
        riemannianEDistOf (I := I) (scaleMetric (I := I) c hc g) x y :=
      edistOf_mono h (scaleMetric (I := I) c hc g)
        (by
          intro z v
          simpa only [scaleMetric_inner] using hu z v)
        x y
    _ = ENNReal.ofReal (Real.sqrt c) *
        riemannianEDistOf (I := I) g x y :=
      edistOf_scale c hc g x y

/-- A pointwise quadratic lower bound gives the corresponding square-root
lower bound on Riemannian extended distance. -/
theorem le_edistOf_of_quad
    (g h : SmoothRiemannianMetric I M) {c : Real} (hc : 0 < c)
    (hl : ∀ x v, c * g.inner x v v ≤ h.inner x v v)
    (x y : M) :
    ENNReal.ofReal (Real.sqrt c) * riemannianEDistOf (I := I) g x y ≤
      riemannianEDistOf (I := I) h x y := by
  calc
    ENNReal.ofReal (Real.sqrt c) * riemannianEDistOf (I := I) g x y =
        riemannianEDistOf (I := I) (scaleMetric (I := I) c hc g) x y :=
      (edistOf_scale c hc g x y).symm
    _ ≤ riemannianEDistOf (I := I) h x y :=
      edistOf_mono (scaleMetric (I := I) c hc g) h
        (by
          intro z v
          simpa only [scaleMetric_inner] using hl z v)
        x y

/-- Scaling the metric by `c` and the radius by `√c` preserves the carrier
of an extended-distance ball. -/
theorem edistBall_scale
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (x : M) (r : Real) :
    {y : M | riemannianEDistOf (I := I)
        (scaleMetric (I := I) c hc g) x y <
          ENNReal.ofReal (Real.sqrt c * r)} =
      {y : M | riemannianEDistOf (I := I) g x y < ENNReal.ofReal r} := by
  ext y
  simp only [Set.mem_setOf_eq]
  rw [edistOf_scale]
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg c)]
  let a : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt c)
  have ha0 : a ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.2 hc))
  have hatop : a ≠ (∞ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  exact ENNReal.mul_lt_mul_iff_right ha0 hatop

end DifferentialGeometry

end
