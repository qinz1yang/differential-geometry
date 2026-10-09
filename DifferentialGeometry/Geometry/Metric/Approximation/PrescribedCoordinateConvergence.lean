import DifferentialGeometry.Geometry.Metric.Approximation.PrescribedProductCoordinates
import DifferentialGeometry.Geometry.Metric.Approximation.PointedConvergence

namespace GC.MetricGeometry

open Filter
open scoped Topology

universe u v w z
variable {X : ℕ → Type u} {Y : Type v} {E : Type w} {Z : Type z}
variable [∀ i, MetricSpace (X i)] [MetricSpace Y] [MetricSpace E] [MetricSpace Z]
variable {p : ∀ i, X i} {q : Y} {R ε : ℕ → ℝ}

theorem eventually_prescribed_kleinerLott_approximation
    (e : Y ≃ᵢ WithLp 2 (E × Z))
    (f : ∀ i, PointedBallApprox (p i) q (R i) (ε i))
    (hR : Tendsto R atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
    (h : ∀ i, X i → E) (hp : ∀ i, h i (p i) = (e q).fst)
    (hclose : ∀ S η : ℝ, 0 < η → ∀ᶠ i in atTop,
      ∀ x : BallCarrier (p i) (R i), dist x.val (p i) ≤ S →
        dist (h i x.val) (e ((f i).toFun x)).fst ≤ η)
    {δ : ℝ} (hδ : 0 < δ) (hδone : δ < 1) :
    ∀ᶠ i in atTop, ∃ ψ : KleinerLottApprox (p i) (e q) δ,
      ∀ x : X i, (ψ.toFun x).fst = h i x := by
  let S : ℝ := δ⁻¹ + δ
  have hS : 0 < S := by dsimp [S]; positivity
  have hiS : δ⁻¹ ≤ S := by dsimp [S]; linarith
  filter_upwards [hR.eventually (eventually_ge_atTop S),
    hε.eventually (eventually_lt_nhds (by positivity : 0 < δ / 32)),
    hclose S (δ / 16) (by positivity)] with i hiR hiε hiclose
  have heS : 2 * ε i < S := by
    have hdS : δ ≤ S := by dsimp [S]; linarith [inv_pos.mpr hδ]
    linarith
  let F := ((f i).restrict heS hiR).mapTargetIsometry e
  have hF : ∀ x : BallCarrier (p i) S, dist (h i x.val) (F.toFun x).fst ≤ δ / 16 := by
    intro x
    exact hiclose ⟨x.val, x.property.trans hiR⟩ x.property
  have hsmall : 2 * ε i + 2 * (δ / 16) < δ / 2 := by linarith
  have hE : 2 * ε i + 2 * (δ / 16) < S := by
    have hdS : δ ≤ S := by dsimp [S]; linarith [inv_pos.mpr hδ]
    linarith
  let G := F.replaceFirstCoordinate (h i) (hp i) hF hE
  exact ⟨G.toKleinerLottWithFirstCoordinate (h i) hδ hδone hsmall hiS,
    G.toKleinerLottWithFirstCoordinate_fst (h i)
      (F.replaceFirstCoordinate_fst (h i) (hp i) hF hE) hδ hδone hsmall hiS⟩

end GC.MetricGeometry
