import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottRescaling
import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottIsometryTransport
import DifferentialGeometry.Geometry.Metric.Approximation.ScaledProductCollapse
import Mathlib.Analysis.Normed.Module.Basic

/-!
Rescaling a normalized splitting in any real normed factor preserves its original full map.
The Euclidean coordinate is multiplied by the scale after subtracting its value at the new
centre, while the residual coordinate stays unchanged with its metric rescaled by the same factor.
-/

set_option autoImplicit false

noncomputable section

namespace IsometryEquiv

variable {E A : Type*} [normE : NormedAddCommGroup E] [spaceE : NormedSpace ℝ E]
    [mA : MetricSpace A]

def normedProdRescale (c : ℝ) (hc : 0 < c) (u : E) :
    @IsometryEquiv (WithLp 2 (E × A)) (WithLp 2 (E × A))
      ((inferInstance : MetricSpace (WithLp 2 (E × A))).rescale c hc).toPseudoEMetricSpace
      (MetricSpace.scaledProduct inferInstance mA c hc).toPseudoEMetricSpace := by
  let h : E ≃ E := (Equiv.addRight (-u)).trans (LinearEquiv.smulOfNeZero ℝ E c hc.ne').toEquiv
  let e : WithLp 2 (E × A) ≃ WithLp 2 (E × A) :=
    (WithLp.equiv 2 (E × A)).trans ((Equiv.prodCongr h (Equiv.refl A)).trans
      (WithLp.equiv 2 (E × A)).symm)
  have he (x : WithLp 2 (E × A)) : e x = WithLp.toLp 2 (c • (x.fst - u), x.snd) := by
    change WithLp.toLp 2 (c • (x.fst + -u), x.snd) = _
    rw [sub_eq_add_neg]
  refine @IsometryEquiv.mk (WithLp 2 (E × A)) (WithLp 2 (E × A))
    ((inferInstance : MetricSpace (WithLp 2 (E × A))).rescale c hc).toPseudoEMetricSpace
    (MetricSpace.scaledProduct inferInstance mA c hc).toPseudoEMetricSpace e ?_
  apply @Isometry.of_dist_eq _ _
    ((inferInstance : MetricSpace (WithLp 2 (E × A))).rescale c hc).toPseudoMetricSpace
    (MetricSpace.scaledProduct inferInstance mA c hc).toPseudoMetricSpace
  intro x y
  change @dist _ (MetricSpace.scaledProduct inferInstance mA c hc).toDist (e x) (e y) =
    c * dist x y
  rw [MetricSpace.scaledProduct_dist, he, he, WithLp.prod_dist_eq_sqrt_sq_add_sq]
  have hv : dist (c • (x.fst - u)) (c • (y.fst - u)) = c * dist x.fst y.fst := by
    rw [dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos hc, dist_eq_norm]
  change Real.sqrt (dist (c • (x.fst - u)) (c • (y.fst - u)) ^ 2 +
    c ^ 2 * dist x.snd y.snd ^ 2) = _
  rw [hv, mul_pow, ← mul_add, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]

theorem normedProdRescale_apply (c : ℝ) (hc : 0 < c) (u : E) (x : WithLp 2 (E × A)) :
    normedProdRescale (A := A) c hc u x = WithLp.toLp 2 (c • (x.fst - u), x.snd) := by
  change WithLp.toLp 2 (c • (x.fst + -u), x.snd) = _
  rw [sub_eq_add_neg]

end IsometryEquiv

namespace GC.MetricGeometry.KleinerLottApprox

variable {E A X : Type*} [normE : NormedAddCommGroup E] [spaceE : NormedSpace ℝ E]
    [mA : MetricSpace A] [mX : MetricSpace X] {p : X} {q : A} {ε δ c : ℝ}

def recenterRescaleNormedProduct
    (f : KleinerLottApprox p (WithLp.toLp 2 ((0 : E), q)) ε) (a : X) (hc : 0 < c)
    (hbudget : 3 * c * ε ≤ δ) (hδ : δ < 1)
    (hdomain : dist a p + δ⁻¹ / c + 2 * ε ≤ ε⁻¹) :
    @KleinerLottApprox X (WithLp 2 (E × A)) (mX.rescale c hc)
      (MetricSpace.scaledProduct inferInstance mA c hc)
      a (WithLp.toLp 2 ((0 : E), (f.toFun a).snd)) δ := by
  let e := IsometryEquiv.normedProdRescale (A := A) c hc (f.toFun a).fst
  have hb : e (f.toFun a) = WithLp.toLp 2 ((0 : E), (f.toFun a).snd) := by
    rw [IsometryEquiv.normedProdRescale_apply, sub_self, smul_zero]
  exact @mapTargetIsometryAt X (WithLp 2 (E × A)) (WithLp 2 (E × A))
    (mX.rescale c hc) ((inferInstance : MetricSpace (WithLp 2 (E × A))).rescale c hc)
    (MetricSpace.scaledProduct inferInstance mA c hc) a (f.toFun a) δ
    (f.recenterRescale a hc hbudget hδ hdomain) e _ hb

theorem recenterRescaleNormedProduct_apply
    (f : KleinerLottApprox p (WithLp.toLp 2 ((0 : E), q)) ε) (a : X) (hc : 0 < c)
    (hbudget : 3 * c * ε ≤ δ) (hδ : δ < 1)
    (hdomain : dist a p + δ⁻¹ / c + 2 * ε ≤ ε⁻¹) (x : X) :
    @KleinerLottApprox.toFun X (WithLp 2 (E × A)) (mX.rescale c hc)
      (MetricSpace.scaledProduct inferInstance mA c hc)
      a (WithLp.toLp 2 ((0 : E), (f.toFun a).snd)) δ
      (f.recenterRescaleNormedProduct a hc hbudget hδ hdomain) x =
        WithLp.toLp 2 (c • ((f.toFun x).fst - (f.toFun a).fst), (f.toFun x).snd) := by
  change WithLp.toLp 2
    (c • ((f.toFun x).fst + -(f.toFun a).fst), (f.toFun x).snd) = _
  rw [sub_eq_add_neg]

end GC.MetricGeometry.KleinerLottApprox
