import DifferentialGeometry.Geometry.Metric.Pullback.Retraction
import DifferentialGeometry.Topology.Manifold.ChartPartialDiffeomorph
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

noncomputable section

open Set Filter Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {V F E H M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

theorem pullbackMetricCoefficients_fderiv_of_eventuallyEq
    (g : SmoothRiemannianMetric I M) {f : V → F} {ψ : F → M} {r : V → M} {x : V}
    (hf : DifferentiableAt ℝ f x)
    (hψ : MDifferentiableAt 𝓘(ℝ, F) I ψ (f x))
    (heq : ψ ∘ f =ᶠ[𝓝 x] r) (v w : V) :
    pullbackMetricCoefficients g ψ (f x) (fderiv ℝ f x v) (fderiv ℝ f x w) =
      pullbackMetricCoefficients g r x v w := by
  have hd : (mfderiv 𝓘(ℝ, F) I ψ (f x) : F →L[ℝ] E).comp (fderiv ℝ f x) =
      (mfderiv 𝓘(ℝ, V) I r x : V →L[ℝ] E) := by
    have hc := mfderiv_comp x hψ hf.mdifferentiableAt
    rw [mfderiv_eq_fderiv] at hc
    exact hc.symm.trans heq.mfderiv_eq
  change (g.inner (ψ (f x)) : E →L[ℝ] E →L[ℝ] ℝ)
    (((mfderiv 𝓘(ℝ, F) I ψ (f x) : F →L[ℝ] E).comp (fderiv ℝ f x)) v)
    (((mfderiv 𝓘(ℝ, F) I ψ (f x) : F →L[ℝ] E).comp (fderiv ℝ f x)) w) = _
  rw [hd]
  change (g.inner (ψ (f x)) : E →L[ℝ] E →L[ℝ] ℝ)
    (mfderiv 𝓘(ℝ, V) I r x v) (mfderiv 𝓘(ℝ, V) I r x w) = _
  have hval : ψ (f x) = r x := heq.eq_of_nhds
  rw [hval]
  rfl

theorem pullbackMetricCoefficients_fderiv_of_eqOn
    (g : SmoothRiemannianMetric I M) {f : V → F} {ψ : F → M} {r : V → M}
    {W : Set V} (hW : IsOpen W) {x : V} (hx : x ∈ W)
    (hf : DifferentiableAt ℝ f x)
    (hψ : MDifferentiableAt 𝓘(ℝ, F) I ψ (f x))
    (heq : EqOn (ψ ∘ f) r W) (v w : V) :
    pullbackMetricCoefficients g ψ (f x) (fderiv ℝ f x v) (fderiv ℝ f x w) =
      pullbackMetricCoefficients g r x v w :=
  pullbackMetricCoefficients_fderiv_of_eventuallyEq g hf hψ
    (Filter.eventuallyEq_of_mem (hW.mem_nhds hx) heq) v w

section Chart

variable [FiniteDimensional ℝ E] [I.Boundaryless]

local notation "Eucl" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem pullbackMetricCoefficients_chart_fderiv
    (g : SmoothRiemannianMetric I M) (p : M)
    {r : V → M} {U : Set V} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, V) I ∞ r U) {x : V}
    (hx : x ∈ U ∩ r ⁻¹' (extChartAt I p).source) (v w : V) :
    let χ : V → Eucl := fun y => toEuclidean (extChartAt I p (r y))
    let ψ : Eucl → M := fun y => (extChartAt I p).symm ((toEuclidean (E := E)).symm y)
    pullbackMetricCoefficients g ψ (χ x) (fderiv ℝ χ x v) (fderiv ℝ χ x w) =
      pullbackMetricCoefficients g r x v w := by
  let chart := extChartAtPartialDiffeomorph I ∞ p
  let W : Set V := U ∩ r ⁻¹' chart.source
  let χ : V → Eucl := fun y => toEuclidean (chart (r y))
  let ψ : Eucl → M := fun y => chart.symm ((toEuclidean (E := E)).symm y)
  have hW : IsOpen W := hr.continuousOn.isOpen_inter_preimage hU chart.open_source
  have hχ : ContDiffOn ℝ ∞ χ W := by
    have hchart : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ (chart ∘ r) W :=
      chart.contMDiffOn_toFun.comp (hr.mono inter_subset_left) inter_subset_right
    exact ((toEuclidean (E := E)).contDiff.contMDiff.comp_contMDiffOn hchart).contDiffOn
  have hχx : DifferentiableAt ℝ χ x :=
    (hχ.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp)
  have htarget : (toEuclidean (E := E)).symm (χ x) ∈ chart.target := by
    change (toEuclidean (E := E)).symm (toEuclidean (chart (r x))) ∈ chart.target
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact chart.toOpenPartialHomeomorph.map_source hx.2
  have hψ : MDifferentiableAt 𝓘(ℝ, Eucl) I ψ (χ x) :=
    ((chart.contMDiffOn_invFun.contMDiffAt (chart.open_target.mem_nhds htarget)).mdifferentiableAt
      (by simp)).comp (χ x) (toEuclidean (E := E)).symm.differentiableAt.mdifferentiableAt
  apply pullbackMetricCoefficients_fderiv_of_eqOn g hW hx hχx hψ
  intro y hy
  change chart.symm ((toEuclidean (E := E)).symm (toEuclidean (chart (r y)))) = r y
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact chart.toOpenPartialHomeomorph.left_inv hy.2

theorem pullbackMetricCoefficients_inverse_chart_of_leftInverse
    (g : SmoothRiemannianMetric I M) (p : M) {e : M → F} {r : F → M}
    (he : ContMDiff I 𝓘(ℝ, F) ∞ e) {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) I ∞ r U) (heU : range e ⊆ U)
    (hleft : Function.LeftInverse r e) {y : Eucl}
    (hy : (toEuclidean (E := E)).symm y ∈ (extChartAt I p).target) (v w : Eucl) :
    let ψ : Eucl → M := fun z => (extChartAt I p).symm ((toEuclidean (E := E)).symm z)
    let β : Eucl → F := e ∘ ψ
    pullbackMetricCoefficients g r (β y) (fderiv ℝ β y v) (fderiv ℝ β y w) =
      pullbackMetricCoefficients g ψ y v w := by
  let chart := extChartAtPartialDiffeomorph I ∞ p
  let ψ : Eucl → M := fun z => chart.symm ((toEuclidean (E := E)).symm z)
  have hψ : MDifferentiableAt 𝓘(ℝ, Eucl) I ψ y :=
    ((chart.contMDiffOn_invFun.contMDiffAt (chart.open_target.mem_nhds hy)).mdifferentiableAt
      (by simp)).comp y (toEuclidean (E := E)).symm.differentiableAt.mdifferentiableAt
  exact pullbackMetricCoefficients_comp_fderiv_of_leftInverse g
    (he.mdifferentiableAt (by simp))
    ((hr.contMDiffAt (hU.mem_nhds (heU (mem_range_self (ψ y))))).mdifferentiableAt (by simp))
    hleft hψ v w

end Chart

end DifferentialGeometry.Geometry

end
