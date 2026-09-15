import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.MetricFamilySmoothOn
import DifferentialGeometry.Geometry.Geodesic.Chart.OpenSubtype
import DifferentialGeometry.Topology.Manifold.OpenEuclideanChart

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem chartChristoffelContraction_contDiffOn
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g)
    (α : M) {s : Set X} {t : X → ℝ} {x v w : X → E}
    (ht : ContDiffOn ℝ ∞ t s) (hx : ContDiffOn ℝ ∞ x s)
    (hv : ContDiffOn ℝ ∞ v s) (hw : ContDiffOn ℝ ∞ w s)
    (htD : MapsTo t s D.regular)
    (hxα : MapsTo x s (interior (extChartAt I α).target)) :
    ContDiffOn ℝ ∞
      (fun p => chartChristoffelContraction (g (t p)) α (v p) (w p) (x p)) s := by
  classical
  unfold chartChristoffelContraction
  refine ContDiffOn.sum fun k _ => ContDiffOn.smul ?_ contDiffOn_const
  refine ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => ?_
  have hΓ := (chartChristoffelOnE_contDiffOn hg Subset.rfl D.regular_isOpen.uniqueDiffOn α i j k).comp
    (ht.prodMk hx) (fun p hp => ⟨htD hp, hxα hp⟩)
  have hvi : ContDiffOn ℝ ∞ (fun p => chartCoord (E := E) i (v p)) s :=
    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord i).toContinuousLinearMap.contDiff.comp_contDiffOn hv
  have hwj : ContDiffOn ℝ ∞ (fun p => chartCoord (E := E) j (w p)) s :=
    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord j).toContinuousLinearMap.contDiff.comp_contDiffOn hw
  exact (hΓ.mul hvi).mul hwj

theorem chartChristoffelContraction_euclidean_contDiffOn
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) E}
    (hg : MetricFamilySmoothOn D g)
    {s : Set X} {t : X → ℝ} {x v w : X → E}
    (ht : ContDiffOn ℝ ∞ t s) (hx : ContDiffOn ℝ ∞ x s)
    (hv : ContDiffOn ℝ ∞ v s) (hw : ContDiffOn ℝ ∞ w s)
    (htD : MapsTo t s D.regular) :
    ContDiffOn ℝ ∞
      (fun p => chartChristoffelContraction (g (t p)) (x p) (v p) (w p) (x p)) s := by
  exact chartChristoffelContraction_contDiffOn hg (0 : E) ht hx hv hw htD
    (by intro p hp; simp [chartAt_self_eq])

theorem chartChristoffelContraction_euclidean_joint_contDiffOn
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) E}
    (hg : MetricFamilySmoothOn D g)
    {J : Set ℝ} (hJ : J ⊆ D.regular) (V : Set E) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E × E => chartChristoffelContraction (g p.1) p.2.1 p.2.2 p.2.2 p.2.1)
      (J ×ˢ V ×ˢ (Set.univ : Set E)) := by
  apply chartChristoffelContraction_euclidean_contDiffOn hg
  · fun_prop
  · fun_prop
  · fun_prop
  · fun_prop
  · intro p hp
    exact hJ hp.1

theorem chartChristoffelContraction_opens_contDiffOn
    {U : TopologicalSpace.Opens E} {D : RealTimeInterval}
    {g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) U}
    (hg : MetricFamilySmoothOn D g) (α : U)
    {s : Set X} {t : X → ℝ} {x v w : X → E}
    (ht : ContDiffOn ℝ ∞ t s) (hx : ContDiffOn ℝ ∞ x s)
    (hv : ContDiffOn ℝ ∞ v s) (hw : ContDiffOn ℝ ∞ w s)
    (htD : MapsTo t s D.regular) (hxU : MapsTo x s U) :
    ContDiffOn ℝ ∞
      (fun p => chartChristoffelContraction (g (t p)) α (v p) (w p) (x p)) s := by
  apply chartChristoffelContraction_contDiffOn hg α ht hx hv hw htD
  rwa [interior_extChartAt_opens_target]

theorem chartChristoffelContraction_opens_joint_contDiffOn
    {U : TopologicalSpace.Opens E} {D : RealTimeInterval}
    {g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) U}
    (hg : MetricFamilySmoothOn D g) (α : U)
    {J : Set ℝ} (hJ : J ⊆ D.regular) {V : Set E} (hV : V ⊆ U) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E × E => chartChristoffelContraction (g p.1) α p.2.2 p.2.2 p.2.1)
      (J ×ˢ V ×ˢ (Set.univ : Set E)) := by
  apply chartChristoffelContraction_opens_contDiffOn hg α
  · fun_prop
  · fun_prop
  · fun_prop
  · fun_prop
  · intro p hp
    exact hJ hp.1
  · intro p hp
    exact hV hp.2.1

end DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
