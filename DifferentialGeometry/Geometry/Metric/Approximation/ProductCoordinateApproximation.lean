import DifferentialGeometry.Geometry.Metric.Approximation.ProductApproximation
import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottConvergence

open Filter
open scoped Topology

namespace GC.MetricGeometry

universe u v w z
variable {X : Type u} {E : Type v} {Z : Type w} {W : Type z}
variable [MetricSpace X] [MetricSpace E] [MetricSpace Z] [MetricSpace W]
variable {p : X} {a : E} {b : Z} {w : W} {δ R ε : ℝ}

noncomputable def KleinerLottApprox.productLimitApprox
    (f : KleinerLottApprox p (WithLp.toLp 2 (a, b)) δ)
    (g : PointedBallApprox b w (R + ε) (ε / 24))
    (hε : 0 < ε) (hεR : ε < R) (hδ : δ < ε / 24) (hR : R + ε < δ⁻¹) :
    PointedBallApprox p (WithLp.toLp 2 (a, w)) R ε :=
  ((f.toClosedBall (by linarith) hR).comp
    (g.l2Product a (by linarith)) (s := R) (by linarith) (by linarith)
    (by linarith)).enlargeError (by linarith) hεR

theorem KleinerLottApprox.productLimitApprox_fst
    (f : KleinerLottApprox p (WithLp.toLp 2 (a, b)) δ)
    (g : PointedBallApprox b w (R + ε) (ε / 24))
    (hε : 0 < ε) (hεR : ε < R) (hδ : δ < ε / 24) (hR : R + ε < δ⁻¹)
    (x : BallCarrier p R) :
    ((f.productLimitApprox g hε hεR hδ hR).toFun x).fst = (f.toFun x.val).fst := rfl

theorem PointedGHConverges.eventually_product_coordinate_approximation
    {T : ℕ → Type u} {F : ℕ → Type w} [∀ i, MetricSpace (T i)] [∀ i, MetricSpace (F i)]
    {o : ∀ i, T i} {b : ∀ i, F i} {δ : ℕ → ℝ}
    (h : PointedGHConverges b w)
    (f : ∀ i, KleinerLottApprox (o i) (WithLp.toLp 2 (a, b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0)) (hε : 0 < ε) (hεR : ε < R) :
    ∀ᶠ i in atTop, ∃ G : PointedBallApprox (o i) (WithLp.toLp 2 (a, w)) R ε,
      ∀ x : BallCarrier (o i) R, (G.toFun x).fst = ((f i).toFun x.val).fst := by
  have hRpos : 0 < R := hε.trans hεR
  filter_upwards [h.eventually_approx (R := R + ε) (ε := ε / 24) (by positivity) (by linarith),
    hδ.eventually (eventually_lt_nhds (by positivity : 0 < ε / 24)),
    hδ.eventually (eventually_lt_nhds (by positivity : 0 < (R + ε + 1)⁻¹))]
    with i hi hiδ hiR
  obtain ⟨g⟩ := hi
  have hinv : R + ε < (δ i)⁻¹ := by
    have hh := (inv_lt_inv₀ (show 0 < (R + ε + 1)⁻¹ by positivity) (f i).error_pos).mpr hiR
    rw [inv_inv] at hh
    linarith
  exact ⟨(f i).productLimitApprox g hε hεR hiδ hinv,
    (f i).productLimitApprox_fst g hε hεR hiδ hinv⟩

end GC.MetricGeometry
