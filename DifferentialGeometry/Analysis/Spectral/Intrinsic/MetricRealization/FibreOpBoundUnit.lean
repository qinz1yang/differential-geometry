import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.PosDefPerturbation
import DifferentialGeometry.Geometry.Curvature.QuadraticFormBound
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.DeTurckRHSSection
import DifferentialGeometry.Tensor.RSTensor.QuadraticBounds.Unit

set_option autoImplicit false

noncomputable section

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor.RSTensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in
theorem gOpBound_unitQuad
    (q : SmoothRiemannianMetric I M)
    (A : ∀ x : M, TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] ℝ)
    (hsymm : ∀ (x : M) (v w : TangentSpace I x),
      A x v w = A x w v)
    {δ : ℝ}
    (hunit : ∀ (x : M) (u : TangentSpace I x),
      q.inner x u u = 1 → |A x u u| ≤ δ) :
    gFibreOpBound (I := I) (M := M) q A δ := by
  intro x v w
  let Q : Tensor02At (I := I) (M := M) x :=
    Tensor0SSpace.ofModel (I := I) (x := x)
      (bilinFormToModel E (A x))
  have hQeval (z₁ z₂ : TangentSpace I x) :
      Q (vec2 (I := I) z₁ z₂) = A x z₁ z₂ := by
    change Tensor0SSpace.toModel Q (vec2 (I := I) z₁ z₂) = A x z₁ z₂
    rw [Tensor0SSpace.toModel_ofModel, bilinFormToModel_apply]
    rfl
  have hdiag (z : TangentSpace I x) :
      |A x z z| ≤ δ * q.inner x z z := by
    rw [← hQeval z z]
    apply tensor02_quadForm_abs_le_of_unit_bound q Q
    intro u hu
    rw [hQeval u u]
    exact hunit x u hu
  have hpair (u z : TangentSpace I x)
      (hu : q.inner x u u = 1) (hz : q.inner x z z = 1) :
      |A x u z| ≤ δ := by
    have hpolar :
        (4 : ℝ) * A x u z =
          A x (u + z) (u + z) - A x (u - z) (u - z) := by
      simp only [map_add, map_sub, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.sub_apply]
      rw [hsymm x z u]
      ring
    have habs :
        |(4 : ℝ) * A x u z| ≤
          |A x (u + z) (u + z)| + |A x (u - z) (u - z)| := by
      rw [hpolar]
      simpa only [sub_zero, zero_sub, abs_neg] using
        (abs_sub_le (A x (u + z) (u + z)) 0
          (A x (u - z) (u - z)))
    have hsum := add_le_add (hdiag (u + z)) (hdiag (u - z))
    have hmetric :
        q.inner x (u + z) (u + z) + q.inner x (u - z) (u - z) = 4 := by
      simp only [map_add, map_sub, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.sub_apply]
      rw [q.symm x z u, hu, hz]
      ring
    calc
      |A x u z| = (1 / 4 : ℝ) * |(4 : ℝ) * A x u z| := by
        rw [abs_mul]
        norm_num
        ring
      _ ≤ (1 / 4 : ℝ) *
          (|A x (u + z) (u + z)| + |A x (u - z) (u - z)|) :=
        mul_le_mul_of_nonneg_left habs (by norm_num)
      _ ≤ (1 / 4 : ℝ) *
          (δ * q.inner x (u + z) (u + z) +
            δ * q.inner x (u - z) (u - z)) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = δ := by rw [← mul_add, hmetric]; ring
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  have hvpos : 0 < q.inner x v v := q.pos x v hv
  have hwpos : 0 < q.inner x w w := q.pos x w hw
  let rv : ℝ := Real.sqrt (q.inner x v v)
  let sw : ℝ := Real.sqrt (q.inner x w w)
  have hrvpos : 0 < rv := by simpa [rv] using Real.sqrt_pos.mpr hvpos
  have hswpos : 0 < sw := by simpa [sw] using Real.sqrt_pos.mpr hwpos
  have hrv_sq : rv * rv = q.inner x v v := by
    simpa [rv, pow_two] using Real.sq_sqrt hvpos.le
  have hsw_sq : sw * sw = q.inner x w w := by
    simpa [sw, pow_two] using Real.sq_sqrt hwpos.le
  let u : TangentSpace I x := rv⁻¹ • v
  let z : TangentSpace I x := sw⁻¹ • w
  have hu : q.inner x u u = 1 := by
    rw [show u = rv⁻¹ • v from rfl, metric_smul2, ← hrv_sq]
    field_simp [hrvpos.ne']
  have hz : q.inner x z z = 1 := by
    rw [show z = sw⁻¹ • w from rfl, metric_smul2, ← hsw_sq]
    field_simp [hswpos.ne']
  have hvscale : rv • u = v := by simp [u, hrvpos.ne']
  have hwscale : sw • z = w := by simp [z, hswpos.ne']
  have hval : A x v w = rv * sw * A x u z := by
    rw [← hvscale, ← hwscale]
    simp [smul_eq_mul]
    ring
  have habsval : |A x v w| = rv * sw * |A x u z| := by
    rw [hval, abs_mul, abs_mul, abs_of_pos hrvpos, abs_of_pos hswpos]
  rw [habsval]
  calc
    rv * sw * |A x u z| ≤ rv * sw * δ :=
      mul_le_mul_of_nonneg_left (hpair u z hu hz)
        (mul_nonneg hrvpos.le hswpos.le)
    _ = δ * Real.sqrt (q.inner x v v) * Real.sqrt (q.inner x w w) := by
      simp only [rv, sw]
      ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
