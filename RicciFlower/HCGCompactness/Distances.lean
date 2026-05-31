import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false

/-!
# Distance Consequence Of Approximate Isometries

This file contains the metric-space ball-inclusion step in MSM135 Chapter 4,
Proposition `lbl367` ("Distances").  The remaining Riemannian producer is the
length/distance estimate that turns a `(eps,0)` pre-approximate isometry into
the Lipschitz hypothesis used here.
-/

namespace RicciFlower
namespace HCGCompactness

open Bundle Manifold
open scoped Manifold ContDiff ENNReal

/-- MSM135 Chapter 4, Proposition `lbl367`, length-infimum bridge.

If every smooth source path from `x` to `y` can be sent to a smooth target path
from `F x` to `F y` whose Riemannian length is at most `K` times the source
length, then the Riemannian extended distance between the images is at most
`K` times the source Riemannian extended distance.

The remaining geometric producer for F2 is the tangent-vector length comparison
coming from the `(eps,0)` pre-approximate-isometry metric bound. -/
theorem edist_le_of_path_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M N : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [TopologicalSpace N] [ChartedSpace H N] [PseudoEMetricSpace N]
    [RiemannianBundle (fun x : N => TangentSpace I x)]
    [IsRiemannianManifold I N]
    (F : M -> N) {K : ENNReal} (hK0 : K ≠ 0) (hKtop : K ≠ ⊤)
    (hpath :
      forall {x y : M}, forall γ : Path x y, CMDiff 1 γ ->
        exists η : Path (F x) (F y), CMDiff 1 η /\
          (∫⁻ t, ‖mfderiv% η t 1‖ₑ) <=
            K * (∫⁻ t, ‖mfderiv% γ t 1‖ₑ))
    (x y : M) :
    edist (F x) (F y) <= K * edist x y := by
  rw [IsRiemannianManifold.out (I := I) (F x) (F y)]
  rw [IsRiemannianManifold.out (I := I) x y]
  conv_rhs => rw [riemannianEDist]
  rw [ENNReal.mul_iInf_of_ne hK0 hKtop]
  refine le_iInf ?_
  intro γ
  rw [ENNReal.mul_iInf_of_ne hK0 hKtop]
  refine le_iInf ?_
  intro hγ
  rcases hpath γ hγ with ⟨η, hη, hlen⟩
  have htarget :
      riemannianEDist I (F x) (F y) <=
        ∫⁻ t, ‖mfderiv% η t 1‖ₑ := by
      rw [riemannianEDist]
      exact (iInf_le _ η).trans (iInf_le _ hη)
  exact htarget.trans hlen

/-- MSM135 Chapter 4, Proposition `lbl367`, pointwise distance estimate from
the checked path-length comparison layer. -/
theorem dist_le_of_path_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M N : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [PseudoMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [TopologicalSpace N] [ChartedSpace H N] [PseudoMetricSpace N]
    [RiemannianBundle (fun x : N => TangentSpace I x)]
    [IsRiemannianManifold I N]
    (F : M -> N) {eps : Real} (heps : 0 < 1 + eps)
    (hpath :
      forall {x y : M}, forall γ : Path x y, CMDiff 1 γ ->
        exists η : Path (F x) (F y), CMDiff 1 η /\
          (∫⁻ t, ‖mfderiv% η t 1‖ₑ) <=
            ENNReal.ofReal (Real.sqrt (1 + eps)) *
              (∫⁻ t, ‖mfderiv% γ t 1‖ₑ))
    (x y : M) :
    dist (F x) (F y) <= Real.sqrt (1 + eps) * dist x y := by
  have hF : LipschitzWith
      ⟨Real.sqrt (1 + eps), Real.sqrt_nonneg (1 + eps)⟩ F :=
    fun x y => by
      have hraw :=
        edist_le_of_path_comp (I := I) F
          (K := ENNReal.ofReal (Real.sqrt (1 + eps)))
          (by simp [Real.sqrt_pos.2 heps]) ENNReal.ofReal_ne_top hpath x y
      simpa [ENNReal.ofReal, Real.toNNReal_of_nonneg (Real.sqrt_nonneg (1 + eps))] using hraw
  simpa using hF.dist_le_mul x y

/-- Package the pointwise distance estimate in the proof of MSM135 Chapter 4,
Proposition `lbl367`, as a Lipschitz bound with constant `sqrt (1 + eps)`.

The remaining Riemannian step is to prove the hypothesis `hdist` from the
metric comparison along curves. -/
theorem lipschitz_sqrt_of_dist_le
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (F : X -> Y) {eps : Real}
    (hdist : forall x y : X,
      dist (F x) (F y) <= Real.sqrt (1 + eps) * dist x y) :
    LipschitzWith ⟨Real.sqrt (1 + eps), Real.sqrt_nonneg (1 + eps)⟩ F := by
  exact LipschitzWith.of_dist_le_mul hdist

/-- MSM135 Chapter 4, Proposition `lbl367`, metric-space endpoint:
if the map has Lipschitz constant `sqrt (1 + eps)`, then it sends a metric ball
of radius `r` into the corresponding enlarged metric ball.

This is the final set-theoretic step of the book proof after the length
comparison has produced the Lipschitz estimate. -/
theorem image_ball_subset_of_lipschitz_sqrt
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (F : X -> Y) {eps : Real} (heps : 0 < 1 + eps)
    (hF : LipschitzWith ⟨Real.sqrt (1 + eps), Real.sqrt_nonneg (1 + eps)⟩ F)
    (x0 : X) (r : Real) :
    F '' Metric.ball x0 r ⊆
      Metric.ball (F x0) (Real.sqrt (1 + eps) * r) := by
  have hKpos :
      0 < (⟨Real.sqrt (1 + eps), Real.sqrt_nonneg (1 + eps)⟩ : NNReal) := by
    exact_mod_cast (Real.sqrt_pos.2 heps)
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact hF.mapsTo_ball (ne_of_gt hKpos) x0 r hx

/-- F2 endpoint from the checked path-length comparison layer:
if smooth source paths have image paths with length multiplied by at most
`sqrt (1 + eps)`, then balls map into the corresponding enlarged balls.

The remaining producer is to derive `hpath` from the `(eps,0)`
pre-approximate-isometry tangent-vector metric comparison. -/
theorem image_ball_subset_of_path_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M N : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [PseudoMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [TopologicalSpace N] [ChartedSpace H N] [PseudoMetricSpace N]
    [RiemannianBundle (fun x : N => TangentSpace I x)]
    [IsRiemannianManifold I N]
    (F : M -> N) {eps : Real} (heps : 0 < 1 + eps)
    (hpath :
      forall {x y : M}, forall γ : Path x y, CMDiff 1 γ ->
        exists η : Path (F x) (F y), CMDiff 1 η /\
          (∫⁻ t, ‖mfderiv% η t 1‖ₑ) <=
            ENNReal.ofReal (Real.sqrt (1 + eps)) *
              (∫⁻ t, ‖mfderiv% γ t 1‖ₑ))
    (x0 : M) (r : Real) :
    F '' Metric.ball x0 r ⊆
      Metric.ball (F x0) (Real.sqrt (1 + eps) * r) := by
  have hF : LipschitzWith
      ⟨Real.sqrt (1 + eps), Real.sqrt_nonneg (1 + eps)⟩ F :=
    fun x y => by
      have hraw :=
        edist_le_of_path_comp (I := I) F
          (K := ENNReal.ofReal (Real.sqrt (1 + eps)))
          (by simp [Real.sqrt_pos.2 heps]) ENNReal.ofReal_ne_top hpath x y
      simpa [ENNReal.ofReal, Real.toNNReal_of_nonneg (Real.sqrt_nonneg (1 + eps))] using hraw
  exact image_ball_subset_of_lipschitz_sqrt F heps hF x0 r

end HCGCompactness
end RicciFlower
