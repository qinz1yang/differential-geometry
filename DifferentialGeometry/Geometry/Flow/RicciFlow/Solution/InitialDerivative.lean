import Mathlib.Analysis.Calculus.FDeriv.Extend
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita

set_option autoImplicit false
noncomputable section
open Set Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]

theorem metric_right_derivative_of_interior
    {a b : ℝ} (hab : a < b) (g : ℝ → SmoothRiemannianMetric I M)
    (hg : ∀ (x : M) (v w : TangentSpace I x),
      ContinuousOn (fun t => (g t).inner x v w) (Ico a b))
    (hRic : ∀ (x : M) (v w : TangentSpace I x),
      ContinuousOn (fun t => ricciTensor (g t) x v w) (Ico a b))
    (hRF : ∀ t ∈ Ioo a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivAt (fun s => (g s).inner x v w) (-2 * ricciTensor (g t) x v w) t)
    (x : M) (v w : TangentSpace I x) :
    HasDerivWithinAt (fun t => (g t).inner x v w)
      (-2 * ricciTensor (g a) x v w) (Ici a) a := by
  have ha : a ∈ Ico a b := ⟨le_rfl, hab⟩
  have hlim := ((hRic x v w) a ha).mono Ioo_subset_Ico_self
  change Tendsto (fun t => ricciTensor (g t) x v w)
    (𝓝[Ioo a b] a) (𝓝 (ricciTensor (g a) x v w)) at hlim
  rw [nhdsWithin_Ioo_eq_nhdsGT hab] at hlim
  apply hasDerivWithinAt_Ici_of_tendsto_deriv
    (fun t ht => (hRF t ht x v w).differentiableAt.differentiableWithinAt)
    (((hg x v w) a ha).mono Ioo_subset_Ico_self) (Ioo_mem_nhdsGT hab)
  apply (tendsto_const_nhds.mul hlim).congr'
  filter_upwards [Ioo_mem_nhdsGT hab] with t ht
  exact (hRF t ht x v w).deriv.symm

variable [CompleteSpace E]

theorem initial_metric_derivative
    {a b : ℝ} (hab : a < b)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen a b hab))
    (hS : IsSolutionOn S) (x : M) (v w : TangentSpace I x) :
    HasDerivWithinAt (fun t => (S.base.metric t).inner x v w)
      (-2 * ricciTensor (S.base.metric a) x v w) (Ici a) a := by
  apply metric_right_derivative_of_interior hab S.base.metric
  · exact hS.smoothMetric.coeff_cont
  · intro y u z
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun t : Ico a b => ricciTensor (S.base.metric t.val) y u z)
    have h := hS.ricciCont.eval_continuous
      (P := Ico a b) (τ := Subtype.val) (b := fun _ => y)
      continuous_subtype_val (fun t => t.property) continuous_const
      (v := fun i _ => vec2 u z i) (fun _ => continuous_const)
    simpa only [SolutionOn.ricci, SolutionFamily.ricci_apply, SolutionFamily.ricciAt,
      metricRicciAt_apply_eq_ricciTensor] using h
  · intro t ht y u z
    have h := metricDerivAt S hS ⟨t, ht⟩ y u z
    change HasDerivAt (fun s => (S.base.metric s).inner y u z)
      (-2 * metricRicciAt (S.base.metric t) y (vec2 u z)) t at h
    rw [metricRicciAt_apply_eq_ricciTensor] at h
    exact h
end DifferentialGeometry.PDE.RicciFlow
