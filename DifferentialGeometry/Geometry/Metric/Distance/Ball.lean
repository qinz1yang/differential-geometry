import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def riemannianClosedBallOf (g : SmoothRiemannianMetric I M) (x : M) (r : ℝ) : Set M :=
  {y | riemannianEDistOf (I := I) g x y ≤ ENNReal.ofReal r}

def riemannianBallOf (g : SmoothRiemannianMetric I M) (x : M) (r : ℝ) : Set M :=
  {y | riemannianEDistOf (I := I) g x y < ENNReal.ofReal r}

theorem riemannianClosedBallOf_mono (g : SmoothRiemannianMetric I M) (x : M) {r r' : ℝ}
    (h : r ≤ r') :
    riemannianClosedBallOf (I := I) g x r ⊆ riemannianClosedBallOf (I := I) g x r' := by
  intro y hy
  exact hy.trans (ENNReal.ofReal_le_ofReal h)

theorem riemannianBallOf_mono (g : SmoothRiemannianMetric I M) (x : M) {r r' : ℝ}
    (h : r ≤ r') :
    riemannianBallOf (I := I) g x r ⊆ riemannianBallOf (I := I) g x r' := by
  intro y hy
  exact hy.trans_le (ENNReal.ofReal_le_ofReal h)

theorem riemannianClosedBallOf_scaleMetric
    (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M) (r : ℝ) :
    riemannianClosedBallOf (I := I) (scaleMetric (I := I) c hc g) x (Real.sqrt c * r) =
      riemannianClosedBallOf (I := I) g x r := by
  ext y
  have ha0 : ENNReal.ofReal (Real.sqrt c) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.2 hc))
  have hatop : ENNReal.ofReal (Real.sqrt c) ≠ (⊤ : ENNReal) := ENNReal.ofReal_ne_top
  change riemannianEDistOf (I := I) (scaleMetric (I := I) c hc g) x y ≤
      ENNReal.ofReal (Real.sqrt c * r) ↔
    riemannianEDistOf (I := I) g x y ≤ ENNReal.ofReal r
  rw [edistOf_scale, ENNReal.ofReal_mul (Real.sqrt_nonneg c)]
  constructor
  · intro h
    by_contra hcon
    exact absurd ((ENNReal.mul_lt_mul_iff_right ha0 hatop).2 (not_le.1 hcon)) (not_lt.2 h)
  · intro h
    by_contra hcon
    exact absurd ((ENNReal.mul_lt_mul_iff_right ha0 hatop).1 (not_le.1 hcon)) (not_lt.2 h)

theorem riemannianBallOf_scaleMetric
    (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M) (r : ℝ) :
    riemannianBallOf (I := I) (scaleMetric (I := I) c hc g) x (Real.sqrt c * r) =
      riemannianBallOf (I := I) g x r := by
  ext y
  have ha0 : ENNReal.ofReal (Real.sqrt c) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.2 hc))
  have hatop : ENNReal.ofReal (Real.sqrt c) ≠ (⊤ : ENNReal) := ENNReal.ofReal_ne_top
  change riemannianEDistOf (I := I) (scaleMetric (I := I) c hc g) x y <
      ENNReal.ofReal (Real.sqrt c * r) ↔
    riemannianEDistOf (I := I) g x y < ENNReal.ofReal r
  rw [edistOf_scale, ENNReal.ofReal_mul (Real.sqrt_nonneg c)]
  exact ENNReal.mul_lt_mul_iff_right ha0 hatop

end DifferentialGeometry
