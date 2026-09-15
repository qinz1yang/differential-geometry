import DifferentialGeometry.Geometry.Exponential.NormalBall.Recenter
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Algebra
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Derivative

noncomputable section
open Set Filter
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

open DifferentialGeometry.CheegerGromovCompactness

variable {E P H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  {p : ∀ k, M k} (c : ∀ k, NormalBallChart (I := I) (p k))

theorem mapCInfConvergence_inv_of_recenter (a : E) {r : ℝ} (hr : 0 < r)
    (hball : ∀ k, Metric.ball a r ⊆ Metric.ball (0 : E) (c k).radius)
    {U : Set P} {F : ∀ k, P → M k} {PhiInf : P → E}
    (hconv : MapCInfConvergenceOnCompacts U
      (fun k z => ((c k).recenter a hr (hball k)).inv (F k z)) PhiInf) :
    MapCInfConvergenceOnCompacts U (fun k z => (c k).inv (F k z))
      (fun z => a + PhiInf z) := by
  simpa only [recenter_inv, add_neg_cancel_left] using hconv.const_add a

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem mapCInfConvergence_inv_id_of_recenter (a : E) {r : ℝ} (hr : 0 < r)
    (hball : ∀ k, Metric.ball a r ⊆ Metric.ball (0 : E) (c k).radius)
    {U : Set E} {F : ∀ k, E → M k}
    (hconv : MapCInfConvergenceOnCompacts U
      (fun k z => ((c k).recenter a hr (hball k)).inv (F k z)) (fun z => z - a)) :
    MapCInfConvergenceOnCompacts U (fun k z => (c k).inv (F k z)) id := by
  have hid : (fun z : E => a + (z - a)) = id := by
    funext z
    dsimp
    abel
  simpa only [hid] using mapCInfConvergence_inv_of_recenter c a hr hball hconv

theorem mapCInfConvergence_inv_recenter_hom (a : E) {r : ℝ} (hr : 0 < r)
    (hball : ∀ k, Metric.ball a r ⊆ Metric.ball (0 : E) (c k).radius)
    {U : Set P} (hU : IsOpen U) {Phi : ℕ → P → E} {PhiInf : P → E}
    (hconv : MapCInfConvergenceOnCompacts U Phi PhiInf)
    (hmap : ∀ᶠ k in atTop, MapsTo (Phi k) U (Metric.ball (0 : E) r)) :
    MapCInfConvergenceOnCompacts U
      (fun k z => (c k).inv (((c k).recenter a hr (hball k)).hom (Phi k z)))
      (fun z => a + PhiInf z) := by
  apply (hconv.const_add a).congr_eventually hU
  · filter_upwards [hmap] with k hk z hz
    exact (c k).inv_recenter_hom a hr (hball k) (hk hz)
  · exact Set.eqOn_refl _ _

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem eventually_recenter_hom_mem_target (a : E) {r : ℝ} (hr : 0 < r)
    (hball : ∀ k, Metric.ball a r ⊆ Metric.ball (0 : E) (c k).radius)
    {K : Set P} {Phi : ℕ → P → E}
    (hmap : ∀ᶠ k in atTop, MapsTo (Phi k) K (Metric.ball (0 : E) r)) :
    ∀ᶠ k in atTop, ∀ z ∈ K,
      ((c k).recenter a hr (hball k)).hom (Phi k z) ∈ (c k).restrictBall.target ∧
      (c k).inv (((c k).recenter a hr (hball k)).hom (Phi k z)) = a + Phi k z := by
  filter_upwards [hmap] with k hk z hz
  refine ⟨(c k).recenter_restrict_ball_target_subset a hr (hball k) ?_,
    (c k).inv_recenter_hom a hr (hball k) (hk hz)⟩
  exact ((c k).recenter a hr (hball k)).restrictBall.map_source (hk hz)

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart
end
