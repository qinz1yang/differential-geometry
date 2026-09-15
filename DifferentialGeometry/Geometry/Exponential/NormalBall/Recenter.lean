import DifferentialGeometry.Geometry.Exponential.NormalBall.Chart

noncomputable section
open scoped ContDiff Manifold
open Set

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

private def translation (a : E) : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ where
  toPartialEquiv := (Equiv.addLeft a).toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := by
    exact (contMDiffOn_iff_contDiffOn.mpr (contDiff_const.add contDiff_id).contDiffOn)
  contMDiffOn_invFun := by
    exact (contMDiffOn_iff_contDiffOn.mpr (contDiff_const.add contDiff_id).contDiffOn)

def recenter {p : M} (c : NormalBallChart (I := I) p) (a : E)
    {r : ℝ} (hr : 0 < r) (hball : Metric.ball a r ⊆ Metric.ball (0 : E) c.radius) :
    NormalBallChart (I := I) (c.hom a) :=
  ofHigher hr ((translation a).trans c.restrictBall)
    (by
      intro z hz
      refine ⟨Set.mem_univ _, ?_⟩
      apply hball
      change dist (a + z) a < r
      simpa only [dist_zero_right, Metric.mem_ball, dist_add_left, dist_self_add_left] using hz)
    (by change c.hom (a + 0) = c.hom a; rw [add_zero])

@[simp] theorem recenter_apply {p : M} (c : NormalBallChart (I := I) p) (a : E)
    {r : ℝ} (hr : 0 < r) (hball : Metric.ball a r ⊆ Metric.ball (0 : E) c.radius) (z : E) :
    (c.recenter a hr hball).hom z = c.hom (a + z) := rfl

@[simp] theorem recenter_inv {p : M} (c : NormalBallChart (I := I) p) (a : E)
    {r : ℝ} (hr : 0 < r) (hball : Metric.ball a r ⊆ Metric.ball (0 : E) c.radius) (y : M) :
    (c.recenter a hr hball).inv y = -a + c.inv y := rfl

@[simp] theorem recenter_radius {p : M} (c : NormalBallChart (I := I) p) (a : E)
    {r : ℝ} (hr : 0 < r) (hball : Metric.ball a r ⊆ Metric.ball (0 : E) c.radius) :
    (c.recenter a hr hball).radius = r := rfl

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

end

noncomputable section
open Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

theorem metric_recenter (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) (a : E) {r : ℝ}
    (hr : 0 < r) (hball : Metric.ball a r ⊆ Metric.ball (0 : E) c.radius)
    {z : E} (hz : z ∈ Metric.ball (0 : E) r) :
    (c.recenter a hr hball).metric g z = c.metric g (a + z) := by
  have hsrc : a + z ∈ c.hom.source := by
    apply c.ball_subset
    apply hball
    simpa only [Metric.mem_ball, dist_zero_right, dist_add_left, dist_self_add_left] using hz
  have hc := c.hom.contMDiffOn_toFun.mdifferentiableOn (by norm_num) (a + z) hsrc
    |>.mdifferentiableAt (c.hom.open_source.mem_nhds hsrc)
  have ha : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z : E => a + z) z := by
    exact (contMDiff_iff_contDiff.mpr (show ContDiff ℝ ∞ (fun z : E => a + z) from contDiff_const.add contDiff_id)).mdifferentiableAt (by simp)
  have hD (v : E) : mfderiv 𝓘(ℝ, E) I (fun z : E => c.hom (a + z)) z v =
      mfderiv 𝓘(ℝ, E) I (fun z : E => c.hom z) (a + z) v := by
    have h := mfderiv_comp_apply z hc ha v
    have haD : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z : E => a + z) z v = v := by
      rw [mfderiv_eq_fderiv, fderiv_const_add]
      simp only [fderiv_fun_id]
      rfl
    rw [haD] at h
    exact h
  ext v w
  rw [metric_apply, metric_apply]
  change g.inner (c.hom (a + z))
    (mfderiv 𝓘(ℝ, E) I (fun z : E => c.hom (a + z)) z v)
    (mfderiv 𝓘(ℝ, E) I (fun z : E => c.hom (a + z)) z w) = _
  rw [hD, hD]

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

end

noncomputable section
open Set
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem MetricEquivOn.recenter (g : SmoothRiemannianMetric I M) {p : M}
    {c : NormalBallChart (I := I) p} (a : E) {r : ℝ}
    (hr : 0 < r) (hball : Metric.ball a r ⊆ Metric.ball (0 : E) c.radius)
    (h : c.MetricEquivOn g (Metric.ball a r)) :
    (c.recenter a hr hball).MetricEquivOn g (Metric.ball (0 : E) r) := by
  intro z hz v
  rw [c.metric_recenter g a hr hball hz]
  apply h (a + z)
  simpa only [Metric.mem_ball, dist_zero_right, dist_add_left, dist_self_add_left] using hz

theorem MetricEquivOn.recenter_inv (g : SmoothRiemannianMetric I M) {p : M}
    {c : NormalBallChart (I := I) p} (a : E) {r : ℝ}
    (hr : 0 < r) (hball : Metric.ball a r ⊆ Metric.ball (0 : E) c.radius)
    (h : c.MetricEquivOn g (Metric.ball (0 : E) c.radius))
    {y : M} (hy : y ∈ (c.recenter a hr hball).restrictBall.target) (v : E) :
    (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤
        (c.recenter a hr hball).metric g ((c.recenter a hr hball).inv y) v v ∧
      (c.recenter a hr hball).metric g ((c.recenter a hr hball).inv y) v v ≤
        2 * ‖v‖ ^ 2 := by
  have hz : (c.recenter a hr hball).inv y ∈ Metric.ball (0 : E) r :=
    (c.recenter a hr hball).restrictBall.map_target hy
  exact MetricEquivOn.recenter g a hr hball (fun z hz => h z (hball hz)) _ hz v

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

end

noncomputable section
open Set Filter
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem recenter_restrict_ball_target_subset {p : M} (c : NormalBallChart (I := I) p)
    (a : E) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball a r ⊆ Metric.ball (0 : E) c.radius) :
    (c.recenter a hr hball).restrictBall.target ⊆ c.restrictBall.target := by
  rintro y ⟨z, hz, rfl⟩
  refine ⟨a + z, hball ?_, rfl⟩
  change z ∈ Metric.ball (0 : E) r at hz
  simpa only [Metric.mem_ball, dist_zero_right, dist_add_left, dist_self_add_left] using hz

theorem inv_eq_add_recenter_inv {p : M} (c : NormalBallChart (I := I) p)
    (a : E) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball a r ⊆ Metric.ball (0 : E) c.radius) (y : M) :
    c.inv y = a + (c.recenter a hr hball).inv y := by
  simp only [recenter_inv, add_neg_cancel_left]

theorem inv_recenter_hom {p : M} (c : NormalBallChart (I := I) p)
    (a : E) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball a r ⊆ Metric.ball (0 : E) c.radius)
    {z : E} (hz : z ∈ Metric.ball (0 : E) r) :
    c.inv ((c.recenter a hr hball).hom z) = a + z := by
  rw [c.inv_eq_add_recenter_inv a hr hball]
  exact congrArg (a + ·) ((c.recenter a hr hball).restrictBall.left_inv hz)

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

end

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem recenter_apply_inv_of_mem_target
    {p : M} (c : NormalBallChart (I := I) p) (a : E) {r : ℝ}
    (hr : 0 < r) (hball : Metric.ball a r ⊆ Metric.ball (0 : E) c.radius)
    {atom : M} (hatom : atom ∈ c.hom.target) {ξ : E}
    (hξ : ξ ∈ Metric.ball (0 : E) r)
    (hξeq : ξ = -a + c.inv atom) :
    (c.recenter a hr hball).hom ξ = atom ∧
      (c.recenter a hr hball).inv atom = ξ ∧
      atom ∈ (c.recenter a hr hball).restrictBall.target := by
  have haξ : a + ξ = c.inv atom := by
    rw [hξeq]
    abel
  have happ : (c.recenter a hr hball).hom ξ = atom := by
    rw [recenter_apply, haξ]
    exact c.hom.right_inv hatom
  have hinv : (c.recenter a hr hball).inv atom = ξ := by
    rw [recenter_inv]
    exact hξeq.symm
  refine ⟨happ, hinv, ?_⟩
  change atom ∈ (c.recenter a hr hball).hom '' Metric.ball (0 : E) r
  exact ⟨ξ, hξ, happ⟩

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart
end
