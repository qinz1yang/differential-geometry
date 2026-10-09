import DifferentialGeometry.Analysis.Calculus.GraphCoverage
import DifferentialGeometry.Analysis.InnerProductSpace.ProjectedGraphRank
import DifferentialGeometry.Analysis.InnerProductSpace.FiniteNormalReduction
import Mathlib.Analysis.InnerProductSpace.ProdL2

set_option autoImplicit false
open Set Metric

namespace GC.MetricGeometry.X81Sol

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace E] [CompleteSpace V]

theorem hausdorffDist_actual_graph_tangent_closedBall_le
    (h : E → V) (X : Set (WithLp 2 (E × V))) (x : WithLp 2 (E × V)) (hx : x ∈ X)
    {R B e : ℝ} (hR : 0 < R) (hB : 0 ≤ B) (he : 0 ≤ e)
    (hreg : ∀ u ∈ closedBall x.fst R, ContDiffAt ℝ 2 (fun z => WithLp.toLp 2 (z, h z)) u)
    (hsecond : ∀ u ∈ closedBall x.fst R,
      ‖iteratedFDeriv ℝ 2 (fun z => WithLp.toLp 2 (z, h z)) u‖ ≤ B)
    (hforward : ∀ y ∈ X ∩ closedBall x R, dist y (WithLp.toLp 2 (y.fst, h y.fst)) ≤ e)
    (hbackward : ∀ u ∈ closedBall x.fst R,
      ∃ y ∈ X, y.fst = u ∧ dist y (WithLp.toLp 2 (y.fst, h y.fst)) ≤ e) :
    hausdorffDist (X ∩ closedBall x R)
      ((fun v => x + fderiv ℝ (fun z => WithLp.toLp 2 (z, h z)) x.fst v) ''
        (univ : Set E) ∩ closedBall x R) ≤ 3 * (2 * e + B * R ^ 2 / 2) := by
  let P : WithLp 2 (E × V) →L[ℝ] E := WithLp.fstL 2 ℝ E V
  exact hausdorffDist_graph_tangent_closedBall_le (fun z => WithLp.toLp 2 (z, h z)) P
    (fun z => WithLp.norm_fst_le E z) (fun _ => rfl) X x hx hR hB he hreg hsecond hforward
    (fun u hu => by obtain ⟨y, hy, hc, hd⟩ := hbackward u hu; exact ⟨y, hy, by simpa only [hc] using hd⟩)

end GC.MetricGeometry.X81Sol

namespace ContinuousLinearMap.X81Sol

variable {E F V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem actual_graph_projected_rank (G : F →L[ℝ] V) (L : E →L[ℝ] F)
    (D : E →L[ℝ] WithLp 2 (F × V)) {a e b l : ℝ}
    (ha : 0 < a) (he : e < a) (hl : ∀ z, a * ‖z‖ ≤ ‖L.adjoint z‖)
    (hT : ‖(WithLp.prodContinuousLinearEquiv 2 ℝ F V).symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.id ℝ F).prod G)‖ ≤ b) (hL : ‖L‖ ≤ l)
    (herror : ‖D - ((WithLp.prodContinuousLinearEquiv 2 ℝ F V).symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.id ℝ F).prod G)).comp L‖ ≤ e) :
    let T := (WithLp.prodContinuousLinearEquiv 2 ℝ F V).symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.id ℝ F).prod G)
    let P := T.range.orthogonalProjectionOnto.comp D
    Function.Surjective P ∧ ‖D - T.range.subtypeL.comp P‖ ≤ e ∧
      ∀ v ∈ P.kerᗮ, (a - e) * ‖v‖ ≤ ‖P v‖ ∧ ‖P v‖ ≤ (b * l + e) * ‖v‖ := by
  apply projected_range_surjective_of_approximation _ L D ha he hl _ hT hL herror
  intro z
  exact WithLp.norm_fst_le F (WithLp.toLp 2 (z, G z))

end ContinuousLinearMap.X81Sol
