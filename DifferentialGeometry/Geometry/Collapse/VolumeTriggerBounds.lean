import DifferentialGeometry.Geometry.Collapse.CurvatureScale

set_option autoImplicit false

noncomputable section

open DifferentialGeometry
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem ballVolume_le_of_volumeCollapsedAtCurvatureScale
    (g : SmoothRiemannianMetric I M) {p : M} {η r R : ℝ}
    (hη : 0 ≤ η) (hr : 0 < r)
    (hscale : ENNReal.ofReal r ≤ curvatureRadius g p)
    (hupper : curvatureRadius g p ≤ ENNReal.ofReal R)
    (hcollapse : volumeCollapsedAtCurvatureScale g η p) :
    ballVolume g p r ≤ ENNReal.ofReal (η * R ^ 3) := by
  have hfinite : curvatureRadius g p ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hupper
  have hpos : 0 < curvatureRadius g p :=
    (ENNReal.ofReal_pos.mpr hr).trans_le hscale
  have hR : 0 < R :=
    ENNReal.ofReal_pos.mp (hpos.trans_le hupper)
  let ρ := (curvatureRadius g p).toReal
  have hρ : 0 < ρ := ENNReal.toReal_pos hpos.ne' hfinite
  have heq : ENNReal.ofReal ρ = curvatureRadius g p :=
    ENNReal.ofReal_toReal hfinite
  have hrρ : r ≤ ρ := by
    apply (ENNReal.ofReal_le_ofReal_iff hρ.le).mp
    simpa only [heq] using hscale
  have hρR : ρ ≤ R := by
    apply (ENNReal.ofReal_le_ofReal_iff hR.le).mp
    simpa only [heq] using hupper
  calc
    ballVolume g p r ≤ ballVolume g p ρ :=
      MeasureTheory.measure_mono (riemannianBallOf_mono g p hrρ)
    _ ≤ ENNReal.ofReal (η * ρ ^ 3) := hcollapse ρ hρ heq.symm
    _ ≤ ENNReal.ofReal (η * R ^ 3) :=
      ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ.le hρR 3) hη)

theorem radius_lt_of_volumeCollapsedAtCurvatureScale
    (g : SmoothRiemannianMetric I M) {p : M} {η w b r R : ℝ}
    (hη : 0 ≤ η) (hw : 0 < w) (hr : 0 < r)
    (hscale : ENNReal.ofReal r ≤ curvatureRadius g p)
    (hupper : curvatureRadius g p ≤ ENNReal.ofReal R)
    (hcollapse : volumeCollapsedAtCurvatureScale g η p)
    (hvol : ENNReal.ofReal (w * r ^ 3) ≤ ballVolume g p r)
    (hsmall : η * R ^ 3 < w * b ^ 3) : r < b := by
  have hR : 0 < R := ENNReal.ofReal_pos.mp
    ((ENNReal.ofReal_pos.mpr hr).trans_le (hscale.trans hupper))
  have hnonneg : 0 ≤ η * R ^ 3 :=
    mul_nonneg hη (pow_nonneg hR.le 3)
  have hbound : w * r ^ 3 ≤ η * R ^ 3 :=
    (ENNReal.ofReal_le_ofReal_iff hnonneg).mp
      (hvol.trans
        (ballVolume_le_of_volumeCollapsedAtCurvatureScale g hη hr hscale hupper hcollapse))
  have hb : 0 < b := by
    by_contra! hb
    have hb3 : b ^ 3 ≤ 0 := by
      calc
        b ^ 3 = b ^ 2 * b := by ring
        _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg b) hb
    have hwb : w * b ^ 3 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hw.le hb3
    linarith
  by_contra! hbr
  have hpow : b ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hb.le hbr 3
  exact (not_lt_of_ge
    ((mul_le_mul_of_nonneg_left hpow hw.le).trans hbound)) hsmall

end DifferentialGeometry.Geometry.Collapse
