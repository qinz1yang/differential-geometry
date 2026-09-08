import DifferentialGeometry.Geometry.Metric.Family.Basic

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem eventually_metric_comparison_on_compact
    [T2Space M] (g : ℝ → SmoothRiemannianMetric I M)
    {J : Set ℝ}
    (hg : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 J
      (fun t x => Tensor0SBundle.metricTensorField (I := I) (g t) x))
    {t₀ : ℝ} (ht₀ : t₀ ∈ J) {K : Set M} (hK : IsCompact K)
    {c C : ℝ} (hc : c < 1) (hC : 1 < C) :
    ∀ᶠ t in nhdsWithin t₀ J, ∀ x ∈ K, ∀ v : TangentSpace I x,
      c * (g t₀).inner x v v ≤ (g t).inner x v v ∧
        (g t).inner x v v ≤ C * (g t₀).inner x v v := by
  let U := MetricUnitTangent (I := I) (M := M) (g t₀)
  let S : Set U := {p | MetricUnitTangent.base (I := I) (M := M) p ∈ K}
  have hS : IsCompact S := metricUnitOn_compact (I := I) (g t₀) hK
  let f : J × U → ℝ := fun p => (g p.1.1).inner p.2.1.proj p.2.1.2 p.2.1.2
  have hf : Continuous f := by
    have hq := tensor0SFamily_quadCont (I := I) (M := M) hg
    have hpull : Continuous (fun p : J × U => (p.1, p.2.1)) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    have hcomp := hq.comp hpull
    simpa only [f, quad02, Tensor0SBundle.metricTensorField_apply, Function.comp_def] using hcomp
  have he : ∀ᶠ t : J in nhds ⟨t₀, ht₀⟩, ∀ p ∈ S, c < f (t, p) ∧ f (t, p) < C := by
    apply hS.eventually_forall_of_forall_eventually
    intro p hp
    have hpunit : f (⟨t₀, ht₀⟩, p) = 1 := p.2
    exact (hf.continuousAt.eventually (Ioo_mem_nhds
      (by simpa only [hpunit] using hc) (by simpa only [hpunit] using hC)))
  rw [nhdsWithin_eq_map_subtype_coe ht₀]
  change ∀ᶠ t : J in nhds ⟨t₀, ht₀⟩, _
  filter_upwards [he] with t ht
  intro x hx v
  by_cases hv : v = 0
  · subst v
    simp
  have hvpos : 0 < (g t₀).inner x v v := (g t₀).pos x v hv
  let s : ℝ := Real.sqrt ((g t₀).inner x v v)
  have hspos : 0 < s := Real.sqrt_pos.mpr hvpos
  have hsne : s ≠ 0 := hspos.ne'
  have hss : s * s = (g t₀).inner x v v := by
    simpa only [s, sq] using Real.sq_sqrt hvpos.le
  have hunit : (g t₀).inner x (s⁻¹ • v) (s⁻¹ • v) = 1 := by
    rw [metric_smul2]
    field_simp [hsne]
    linarith [hss]
  let p : U := ⟨(⟨x, s⁻¹ • v⟩ : TangentBundle I M), hunit⟩
  have hpS : p ∈ S := hx
  have hbounds := ht p hpS
  have hfp : f (t, p) = s⁻¹ * s⁻¹ * (g t.1).inner x v v := by
    exact metric_smul2 (g t.1) s⁻¹ v
  rw [hfp] at hbounds
  have heq : (s⁻¹ * s⁻¹ * (g t.1).inner x v v) * (s * s) =
      (g t.1).inner x v v := by field_simp
  constructor
  · have h := mul_le_mul_of_nonneg_right hbounds.1.le (mul_self_nonneg s)
    rwa [heq, hss] at h
  · have h := mul_le_mul_of_nonneg_right hbounds.2.le (mul_self_nonneg s)
    rwa [heq, hss] at h

end DifferentialGeometry.Geometry.Curvature
