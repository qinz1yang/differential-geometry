import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottRescaling
import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottIsometryTransport
import DifferentialGeometry.Geometry.Metric.Approximation.ScaledProductCollapse
import Mathlib.Topology.MetricSpace.Isometry

set_option autoImplicit false

namespace IsometryEquiv

variable {Y : Type*} [mY : MetricSpace Y]

noncomputable def realProdRescale (c : ℝ) (hc : 0 < c) (u : ℝ) :
    @IsometryEquiv (WithLp 2 (ℝ × Y)) (WithLp 2 (ℝ × Y))
      ((inferInstance : MetricSpace (WithLp 2 (ℝ × Y))).rescale c hc).toPseudoEMetricSpace
      (MetricSpace.scaledProduct inferInstance mY c hc).toPseudoEMetricSpace := by
  let e : WithLp 2 (ℝ × Y) ≃ WithLp 2 (ℝ × Y) :=
    { toFun := fun x => WithLp.toLp 2 (c * (x.fst - u), x.snd)
      invFun := fun y => WithLp.toLp 2 (y.fst / c + u, y.snd)
      left_inv := by
        intro x
        apply (WithLp.equiv 2 _).injective
        apply Prod.ext
        · change c * (x.fst - u) / c + u = x.fst
          field_simp [hc.ne']
          ring
        · rfl
      right_inv := by
        intro y
        apply (WithLp.equiv 2 _).injective
        apply Prod.ext
        · change c * (y.fst / c + u - u) = y.fst
          field_simp [hc.ne']
          ring
        · rfl }
  refine @IsometryEquiv.mk (WithLp 2 (ℝ × Y)) (WithLp 2 (ℝ × Y))
    ((inferInstance : MetricSpace (WithLp 2 (ℝ × Y))).rescale c hc).toPseudoEMetricSpace
    (MetricSpace.scaledProduct inferInstance mY c hc).toPseudoEMetricSpace e ?_
  apply @Isometry.of_dist_eq _ _
    ((inferInstance : MetricSpace (WithLp 2 (ℝ × Y))).rescale c hc).toPseudoMetricSpace
    (MetricSpace.scaledProduct inferInstance mY c hc).toPseudoMetricSpace
  intro x y
  change @dist _ (MetricSpace.scaledProduct inferInstance mY c hc).toDist (e x) (e y) =
    c * dist x y
  rw [MetricSpace.scaledProduct_dist, WithLp.prod_dist_eq_sqrt_sq_add_sq]
  have hfst : dist (e x).fst (e y).fst = c * dist x.fst y.fst := by
    change dist (c * (x.fst - u)) (c * (y.fst - u)) = c * dist x.fst y.fst
    rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hc, sub_sub_sub_cancel_right,
      Real.dist_eq]
  rw [hfst]
  change Real.sqrt ((c * dist x.fst y.fst) ^ 2 + c ^ 2 * dist x.snd y.snd ^ 2) = _
  rw [mul_pow, ← mul_add, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]

@[simp] theorem realProdRescale_apply (c : ℝ) (hc : 0 < c) (u : ℝ)
    (x : WithLp 2 (ℝ × Y)) :
    realProdRescale c hc u x = WithLp.toLp 2 (c * (x.fst - u), x.snd) := rfl

end IsometryEquiv

namespace GC.MetricGeometry.KleinerLottApprox

variable {X Y : Type*} [mX : MetricSpace X] [mY : MetricSpace Y]
variable {p : X} {q : Y} {ε δ c : ℝ}

noncomputable def recenterRescaleRealProduct
    (f : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) ε)
    (a : X) (hc : 0 < c) (hbudget : 3 * c * ε ≤ δ) (hδ : δ < 1)
    (hdomain : dist a p + δ⁻¹ / c + 2 * ε ≤ ε⁻¹) :
    @KleinerLottApprox X (WithLp 2 (ℝ × Y)) (mX.rescale c hc)
      (MetricSpace.scaledProduct inferInstance mY c hc)
      a (WithLp.toLp 2 ((0 : ℝ), (f.toFun a).snd)) δ := by
  let g := f.recenterRescale a hc hbudget hδ hdomain
  let e := IsometryEquiv.realProdRescale (Y := Y) c hc (f.toFun a).fst
  have he : e (f.toFun a) = WithLp.toLp 2 ((0 : ℝ), (f.toFun a).snd) := by
    change WithLp.toLp 2 (c * ((f.toFun a).fst - (f.toFun a).fst), (f.toFun a).snd) = _
    rw [sub_self, mul_zero]
  exact @mapTargetIsometryAt X (WithLp 2 (ℝ × Y)) (WithLp 2 (ℝ × Y))
    (mX.rescale c hc)
    ((inferInstance : MetricSpace (WithLp 2 (ℝ × Y))).rescale c hc)
    (MetricSpace.scaledProduct inferInstance mY c hc)
    a (f.toFun a) δ g e _ he

@[simp] theorem recenterRescaleRealProduct_apply
    (f : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) ε)
    (a : X) (hc : 0 < c) (hbudget : 3 * c * ε ≤ δ) (hδ : δ < 1)
    (hdomain : dist a p + δ⁻¹ / c + 2 * ε ≤ ε⁻¹) (x : X) :
    @KleinerLottApprox.toFun X (WithLp 2 (ℝ × Y)) (mX.rescale c hc)
      (MetricSpace.scaledProduct inferInstance mY c hc)
      a (WithLp.toLp 2 ((0 : ℝ), (f.toFun a).snd)) δ
      (f.recenterRescaleRealProduct a hc hbudget hδ hdomain) x =
        WithLp.toLp 2 (c * ((f.toFun x).fst - (f.toFun a).fst), (f.toFun x).snd) := rfl

end GC.MetricGeometry.KleinerLottApprox
