import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInteriorCompletion
import DifferentialGeometry.Geometry.Collapse.RankStrataBallLocality

/-!
# LC88 / BCP04: ranks of the interior completion (lane BDRY-1, G3)

BCP04 (master207B) defines the ranks of a carrier with boundary on `{d(·, ∂W) > 5}`; the interior
families live on the interior completion `(W°, ĝ)` of `BoundaryInteriorCompletion.lean`. With the
ball locality of the scaled rank (`RankStrataBallLocality.lean`) and the ball/distance transfer of
G2, `scaledSplittingRank_completion_eq_BDRY1` shows that the two rank functions (of
`(W°, d_ĝ, ρ ∘ val)` and of `(W, d_g, ρ)`) agree at every `q` with `4 R ρ(q) + 5 ≤ d(q, ∂W)`,
`R ≥ (β k)⁻¹` — the rank conjunct of the frozen LC88 row (`build-logs/scratch/BDRY-1/Targets.lean`),
needed to feed X121's BCP05 statements (stated with the ranks of `W`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Manifold
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry GC.Endpoint GC.MetricGeometry DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Collapse

universe u v

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1

variable (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
  (g : SmoothRiemannianMetric W.model W.Carrier)

/-- **Ranks of the interior completion.** For any `ĝ` on `W°` equal to `g°` on `{d ≥ 5}`, a scale
`ρ` on `W` and `R ≥ (β k)⁻¹` (`k ≤ 3`): at every `q ∈ W°` with `4 R ρ(q) + 5 ≤ d(q, ∂W)` the scaled
splitting rank of `(W°, d_ĝ, ρ ∘ val)` equals that of `(W, d_g, ρ)`. -/
theorem scaledSplittingRank_completion_eq_BDRY1
    (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤))
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal 5 ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x)
    (ρ : W.Carrier → ℝ) (hρ : ∀ x, 0 < ρ x) (β : ℕ → ℝ) {R : ℝ} (hR : 0 < R)
    (hβR : ∀ k ≤ 3, (β k)⁻¹ ≤ R) (q : W.pieceInterior ⊤)
    (hq : ENNReal.ofReal (4 * (R * ρ q) + 5) ≤ distanceToBoundary W g q) :
    have := connectedSpace_pieceInterior_top_BDRY1 W
    @scaledSplittingRank.{u, v} (W.pieceInterior ⊤) (inducedMetricSpace ĝ)
        (fun x => ρ x) (fun x => hρ x) β q =
      @scaledSplittingRank.{u, v} W.Carrier (inducedMetricSpace g) ρ hρ β q.val := by
  have := connectedSpace_pieceInterior_top_BDRY1 W
  have hRρ : 0 ≤ R * ρ q := (mul_pos hR (hρ q)).le
  have hq1 : ENNReal.ofReal (R * ρ q + 5) ≤ distanceToBoundary W g q :=
    (ENNReal.ofReal_le_ofReal (by linarith)).trans hq
  have hball := image_val_riemannianBallOf_completion_BDRY1 W g ĝ heq q hRρ hq1
  have hballN : @ball (W.pieceInterior ⊤) (inducedMetricSpace ĝ).toPseudoMetricSpace q
      (R * ρ q) = riemannianBallOf ĝ q (R * ρ q) := inducedMetricSpace_ball ĝ q _
  have hballW : @ball W.Carrier (inducedMetricSpace g).toPseudoMetricSpace q.val (R * ρ q) =
      riemannianBallOf g q.val (R * ρ q) := inducedMetricSpace_ball g q.val _
  refine scaledSplittingRank_eq_of_ballIsometry_BDRY1 (inducedMetricSpace g) (inducedMetricSpace ĝ)
    Subtype.val rfl ρ hρ (fun x => ρ x) (fun x => hρ x) rfl β hR hβR ?_ ?_
  · intro x hx y hy
    rw [hballN] at hx hy
    have h4 : R * ρ q = 4 * (R * ρ q) / 4 := by ring
    rw [h4] at hx hy
    have h := riemannianEDistOf_completion_eq_BDRY1 W g ĝ heq q (by linarith) hq hx hy
    rw [inducedMetricSpace_dist g, inducedMetricSpace_dist ĝ, h]
  · rw [hballN, hballW, hball]

end DifferentialGeometry.Geometry.Collapse
