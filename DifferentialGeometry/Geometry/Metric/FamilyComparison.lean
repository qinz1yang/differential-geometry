import DifferentialGeometry.Geometry.Metric.CompactTangentBall
import Mathlib.Topology.Compactness.Compact








noncomputable section

open Bundle Set Filter Manifold DifferentialGeometry
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {T E : Type*} [TopologicalSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]



theorem eventually_metric_quad_bounds
    (G : T → SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hG : Continuous (fun p : T × TangentBundle 𝓘(ℝ, E) M =>
      (G p.1).inner p.2.proj p.2.2 p.2.2)) (t₀ : T) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 t₀, ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x),
      (1 - ε) * (G t₀).inner x v v ≤ (G t).inner x v v ∧
        (G t).inner x v v ≤ (1 + ε) * (G t₀).inner x v v := by
  have hcont : Continuous (fun p : T × MetricUnitTangent (G t₀) =>
      (G p.1).inner (MetricUnitTangent.base p.2) (MetricUnitTangent.vec p.2)
        (MetricUnitTangent.vec p.2)) :=
    hG.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hu : ∀ᶠ t in 𝓝 t₀, ∀ u : MetricUnitTangent (G t₀),
      |(G t).inner (MetricUnitTangent.base u) (MetricUnitTangent.vec u)
        (MetricUnitTangent.vec u) - 1| < ε := by
    have he := (metricUnit_compact (G t₀)).eventually_forall_of_forall_eventually
      (x₀ := t₀) (P := fun t u => |(G t).inner (MetricUnitTangent.base u)
        (MetricUnitTangent.vec u) (MetricUnitTangent.vec u) - 1| < ε) (fun u _ => ?_)
    · filter_upwards [he] with t ht u
      exact ht u (mem_univ u)
    · apply ((hcont.sub continuous_const).abs.continuousAt).eventually_lt_const
      simpa only [Pi.sub_apply, MetricUnitTangent.unit, sub_self, abs_zero] using hε
  filter_upwards [hu] with t ht x v
  by_cases hv : v = 0
  · subst v
    simp only [map_zero, mul_zero, le_refl, and_self]
  let r := Real.sqrt ((G t₀).inner x v v)
  have hr : 0 < r := Real.sqrt_pos.mpr ((G t₀).pos x v hv)
  have hrr : r * r = (G t₀).inner x v v := Real.mul_self_sqrt ((G t₀).pos x v hv).le
  have hunit : (G t₀).inner x (r⁻¹ • v) (r⁻¹ • v) = 1 := by
    rw [metric_smul2, ← hrr]
    field_simp
  let u : MetricUnitTangent (G t₀) := ⟨TotalSpace.mk' E x (r⁻¹ • v), hunit⟩
  have hb := abs_lt.mp (ht u)
  have heq : (G t).inner x v v = r * r *
      (G t).inner (MetricUnitTangent.base u) (MetricUnitTangent.vec u) (MetricUnitTangent.vec u) := by
    change (G t).inner x v v = r * r * (G t).inner x (r⁻¹ • v) (r⁻¹ • v)
    rw [metric_smul2]
    field_simp
  rw [heq, ← hrr]
  constructor
  · have hmul := mul_le_mul_of_nonneg_left (show 1 - ε ≤ (G t).inner
        (MetricUnitTangent.base u) (MetricUnitTangent.vec u) (MetricUnitTangent.vec u) by linarith)
      (mul_nonneg hr.le hr.le)
    nlinarith only [hmul]
  · have hmul := mul_le_mul_of_nonneg_left (show (G t).inner
        (MetricUnitTangent.base u) (MetricUnitTangent.vec u) (MetricUnitTangent.vec u) ≤ 1 + ε by linarith)
      (mul_nonneg hr.le hr.le)
    nlinarith only [hmul]

end DifferentialGeometry.Geometry
