import Mathlib.Analysis.InnerProductSpace.PiL2
import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottIsometryTransport
import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottRecentering
import DifferentialGeometry.Geometry.Metric.L2Product

set_option autoImplicit false

namespace GC.MetricGeometry.KleinerLottApprox

variable {X A : Type*} [MetricSpace X] [MetricSpace A]
variable {p : X} {a₀ : A} {k : ℕ} {ε δ C : ℝ}

noncomputable def recenterEuclidean
    (φ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), a₀)) ε)
    (c : X) (hδ : 0 < δ) (hδone : δ < 1) (hC : 0 ≤ C)
    (hε : ε ≤ recenterTolerance δ C) (hc : dist p c ≤ C) :
    KleinerLottApprox c
      (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), (φ.toFun c).snd)) δ := by
  let g := φ.recenterWithTarget c (φ.toFun c) hδ hδone hC hε hc
    (by simpa only [dist_self] using φ.error_pos.le)
  let e := IsometryEquiv.withLpProdCongr 2
    (IsometryEquiv.subRight (φ.toFun c).fst) (IsometryEquiv.refl A)
  let G := g.mapTargetIsometry e
  have he : e (φ.toFun c) = WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), (φ.toFun c).snd) := by
    change WithLp.toLp 2 ((φ.toFun c).fst - (φ.toFun c).fst, (φ.toFun c).snd) = _
    rw [sub_self]
  have hG : G.toFun = fun x => WithLp.toLp 2
      ((φ.toFun x).fst - (φ.toFun c).fst, (φ.toFun x).snd) := by
    funext x
    change e (g.toFun x) = _
    rw [φ.recenterWithTarget_self_apply c hδ hδone hC hε hc x]
    rfl
  refine ⟨hδ, hδone, fun x => WithLp.toLp 2
    ((φ.toFun x).fst - (φ.toFun c).fst, (φ.toFun x).snd), ?_, ?_, ?_⟩
  · rw [sub_self]
  · intro x hx y hy
    simpa only [hG] using G.distortion x hx y hy
  · intro y hy
    have hy' : dist y (e (φ.toFun c)) < δ⁻¹ - δ := by rwa [he]
    simpa only [hG] using G.coverage y hy'

theorem recenterEuclidean_apply
    (φ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), a₀)) ε)
    (c : X) (hδ : 0 < δ) (hδone : δ < 1) (hC : 0 ≤ C)
    (hε : ε ≤ recenterTolerance δ C) (hc : dist p c ≤ C) (x : X) :
    (φ.recenterEuclidean c hδ hδone hC hε hc).toFun x = WithLp.toLp 2
      ((φ.toFun x).fst - (φ.toFun c).fst, (φ.toFun x).snd) := rfl

end GC.MetricGeometry.KleinerLottApprox
