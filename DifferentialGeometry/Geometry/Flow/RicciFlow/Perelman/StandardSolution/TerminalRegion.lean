import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Geometry.Metric.DerivativeENorm

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Filter DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def terminalRegularRegion (g : ℝ → SmoothRiemannianMetric I M) (a s : ℝ) : Opens M :=
  ⟨{x | ∃ U : Opens M, x ∈ U ∧ ∃ a' ∈ Ico a s, ∃ K : ℝ, 0 ≤ K ∧
    ∀ y ∈ U, ∀ t ∈ Ico a' s, Real.sqrt (normSq0S (g t) y 4 (metricRm04 (g t) y)) ≤ K}, by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨U, hxU, a', ha', K, hK, hb⟩ := hx
    exact Filter.mem_of_superset (U.isOpen.mem_nhds hxU)
      (fun y hy => ⟨U, hy, a', ha', K, hK, hb⟩)⟩

theorem mem_terminalRegularRegion (g : ℝ → SmoothRiemannianMetric I M) (a s : ℝ) (x : M) :
    x ∈ terminalRegularRegion g a s ↔
      ∃ U : Opens M, x ∈ U ∧ ∃ a' ∈ Ico a s, ∃ K : ℝ, 0 ≤ K ∧
        ∀ y ∈ U, ∀ t ∈ Ico a' s,
          Real.sqrt (normSq0S (g t) y 4 (metricRm04 (g t) y)) ≤ K := Iff.rfl

theorem subset_terminalRegularRegion_of_bound
    (g : ℝ → SmoothRiemannianMetric I M) (a s : ℝ) (U : Opens M)
    (a' : ℝ) (ha' : a' ∈ Ico a s) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ y ∈ U, ∀ t ∈ Ico a' s,
      Real.sqrt (normSq0S (g t) y 4 (metricRm04 (g t) y)) ≤ K) :
    U ≤ terminalRegularRegion g a s := fun _ hy => ⟨U, hy, a', ha', K, hK, hb⟩

theorem terminalRegularRegion_eq_top_of_uniform_bound
    (g : ℝ → SmoothRiemannianMetric I M) (a s : ℝ) (has : a < s)
    (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ t ∈ Ico a s, ∀ y : M,
      Real.sqrt (normSq0S (g t) y 4 (metricRm04 (g t) y)) ≤ K) :
    terminalRegularRegion g a s = ⊤ := by
  apply top_unique
  exact subset_terminalRegularRegion_of_bound g a s ⊤ a ⟨le_rfl, has⟩ K hK
    (fun y _ t ht => hb t ht y)

theorem terminalRegularRegion_const (g : SmoothRiemannianMetric I M)
    (a s : ℝ) (has : a < s) : terminalRegularRegion (fun _ => g) a s = ⊤ := by
  apply top_unique
  intro x _
  let f : M → ℝ := fun y => Real.sqrt (normSq0S g y 4 (metricRm04 g y))
  have hf : Continuous f := Real.continuous_sqrt.comp (DifferentialGeometry.Tensor.RSTensor.normSq0S_smooth g (metricRm04 g)).continuous
  let U : Opens M := ⟨{y | f y < f x + 1}, isOpen_lt hf continuous_const⟩
  refine ⟨U, ?_, a, ⟨le_rfl, has⟩, f x + 1, ?_, ?_⟩
  · change f x < f x + 1; linarith
  · have hx : 0 ≤ f x := Real.sqrt_nonneg _; linarith
  · intro y hy t _
    exact hy.le

def IsTerminalLimitMetric (g : ℝ → SmoothRiemannianMetric I M) (a s : ℝ)
    (gLimit : SmoothRiemannianMetric I (terminalRegularRegion g a s)) : Prop :=
  ∀ K : Set (terminalRegularRegion g a s), IsCompact K → ∀ j : ℕ,
    Tendsto (fun t => metricDerivENormSupOn K j
      ((g t).restrictOpen (terminalRegularRegion g a s)) gLimit gLimit) (𝓝[<] s) (𝓝 0)

theorem isTerminalLimitMetric_const (g : SmoothRiemannianMetric I M) (a s : ℝ) :
    IsTerminalLimitMetric (fun _ => g) a s (g.restrictOpen (terminalRegularRegion (fun _ => g) a s)) := by
  intro K _ j
  simpa only [metricDerivENormSupOn_self] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ≥0∞)) (𝓝[<] s) (𝓝 0))
end DifferentialGeometry.PDE.RicciFlow
