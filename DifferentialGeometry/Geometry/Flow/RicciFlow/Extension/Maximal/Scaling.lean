import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Maximal.Flow
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling

set_option autoImplicit false

noncomputable section

open Set Bundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

def FlowTo.scale {g₀ : SmoothRiemannianMetric I M} {T : ℝ}
    (F : FlowTo g₀ T) (c : ℝ) (hc : 0 < c) :
    FlowTo (scaleMetric c hc g₀) (c * T) := by
  have hT : 0 < c * T := mul_pos hc F.time_pos
  let g : ℝ → SmoothRiemannianMetric I M :=
    fun t => scaleMetric c hc (F.S.base.metric (t / c))
  have hmaps : MapsTo (fun t : ℝ => t / c) (Ico 0 (c * T)) (Ico 0 T) := by
    intro t ht
    exact ⟨div_nonneg ht.1 hc.le, (div_lt_iff₀ hc).mpr (by nlinarith [ht.2])⟩
  have hjoint : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          (g p.1) x₀ p.2 i j)
        (Ico 0 (c * T) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    intro x₀ i j
    have hmap : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
        (fun p : ℝ × M => (p.1 / c, p.2)) :=
      (contMDiff_fst.div_const c).prodMk contMDiff_snd
    have hmapsto : MapsTo (fun p : ℝ × M => (p.1 / c, p.2))
        (Ico 0 (c * T) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)
        (Ico 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
      fun _ hp => ⟨hmaps hp.1, hp.2⟩
    have hh := (F.joint x₀ i j).comp hmap.contMDiffOn hmapsto
    convert! (contMDiffOn_const (c := c)).mul hh using 1
  have hpde : ∀ t ∈ Ico 0 (c * T), ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => (g s).inner x v w)
        (-2 * ricciTensor (g t) x v w) (Ici 0) t := by
    intro t ht x v w
    have hd := (F.pde (t / c) (hmaps ht) x v w).comp t
      ((hasDerivAt_id t).div_const c).hasDerivWithinAt
      (fun r hr => div_nonneg hr hc.le)
    have hh := hd.const_mul c
    have heq : c * (-2 * ricciTensor (F.S.base.metric (t / c)) x v w * (1 / c)) =
        -2 * ricciTensor (F.S.base.metric (t / c)) x v w := by field_simp
    convert! hh using 1
    simp only [g, scaleMetric_inner, ricciTensor_scaleMetric,
      Function.comp_def, id_eq, SolutionOn.family_metric, heq]
    rfl
  let S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 (c * T) hT) :=
    { base := { metric := g } }
  refine ⟨hT, S, solutionOn_of_joint hT g hjoint hpde, ?_, hjoint, hpde⟩
  change scaleMetric c hc (F.S.base.metric (0 / c)) = _
  rw [zero_div]
  exact congrArg (scaleMetric c hc) F.start

@[simp] theorem FlowTo.scale_metric {g₀ : SmoothRiemannianMetric I M} {T : ℝ}
    (F : FlowTo g₀ T) (c : ℝ) (hc : 0 < c) (t : ℝ) :
    (F.scale c hc).S.base.metric t = scaleMetric c hc (F.S.base.metric (t / c)) := rfl

end DifferentialGeometry.PDE.RicciFlow
