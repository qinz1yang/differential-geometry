import DifferentialGeometry.Geometry.Metric.FamilyQuadraticDerivative
import DifferentialGeometry.Geometry.Metric.CompactTangentBall
import Mathlib.Analysis.Calculus.MeanValue
import DifferentialGeometry.Geometry.Metric.ParameterDerivative



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]





theorem exists_metricFamily_quadratic_deriv_bound
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t₀ : ℝ} (ht₀ : D.regular ∈ 𝓝 t₀) :
    ∃ r K : ℝ, 0 < r ∧ 0 ≤ K ∧ Metric.ball t₀ r ⊆ D.regular ∧
      ∀ t ∈ Metric.ball t₀ r, ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x),
        ‖deriv (fun s => (G s).inner x v v) t‖ ≤ K * (G t₀).inner x v v := by
  obtain ⟨a, ha, haD⟩ := Metric.mem_nhds_iff.mp ht₀
  let H : ℝ × MetricUnitTangent (G t₀) → ℝ := fun q =>
    deriv (fun s => (G s).inner (MetricUnitTangent.base q.2)
      (MetricUnitTangent.vec q.2) (MetricUnitTangent.vec q.2)) q.1
  have hH : ContinuousOn H (Metric.ball t₀ a ×ˢ univ) := by
    intro q hq
    have hreg : D.regular ∈ 𝓝 q.1 :=
      mem_of_superset (Metric.isOpen_ball.mem_nhds hq.1) haD
    have hmap : ContinuousAt (fun p : ℝ × MetricUnitTangent (G t₀) => (p.1, p.2.val)) q :=
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousAt
    exact ((continuousAt_metricFamilyQuadratic_deriv hG hreg q.2.val).comp
      (f := fun p : ℝ × MetricUnitTangent (G t₀) => (p.1, p.2.val)) hmap).continuousWithinAt
  have hKc := (isCompact_closedBall t₀ (a / 2)).prod (metricUnit_compact (G t₀))
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn
    (hH.mono (Set.prod_mono (Metric.closedBall_subset_ball (by linarith : a / 2 < a)) Subset.rfl))
  refine ⟨a / 2, max C 0, by linarith, le_max_right _ _,
    (Metric.ball_subset_ball (by linarith : a / 2 ≤ a)).trans haD, ?_⟩
  intro t ht x v
  have hreg : D.regular ∈ 𝓝 t := mem_of_superset
    (Metric.isOpen_ball.mem_nhds ((Metric.ball_subset_ball (by linarith : a / 2 ≤ a)) ht)) haD
  by_cases hv : v = 0
  · subst v
    simp only [map_zero]
    simp
  let s := Real.sqrt ((G t₀).inner x v v)
  have hs : 0 < s := Real.sqrt_pos.mpr ((G t₀).pos x v hv)
  have hss : s * s = (G t₀).inner x v v := Real.mul_self_sqrt ((G t₀).pos x v hv).le
  have hunit : (G t₀).inner x (s⁻¹ • v) (s⁻¹ • v) = 1 := by
    rw [metric_smul2, ← hss]
    field_simp
  let u : MetricUnitTangent (G t₀) := ⟨TotalSpace.mk' E x (s⁻¹ • v), hunit⟩
  have hu : ‖H (t, u)‖ ≤ max C 0 :=
    (hC (t, u) ⟨Metric.ball_subset_closedBall ht, mem_univ _⟩).trans (le_max_left _ _)
  have he (τ : ℝ) : (G τ).inner x v v = (G t₀).inner x v v *
      (G τ).inner (MetricUnitTangent.base u) (MetricUnitTangent.vec u) (MetricUnitTangent.vec u) := by
    change (G τ).inner x v v = (G t₀).inner x v v * (G τ).inner x (s⁻¹ • v) (s⁻¹ • v)
    rw [metric_smul2, ← hss]
    field_simp
  have hd := (((hG.coeff x (s⁻¹ • v) (s⁻¹ • v)).contDiffAt hreg).differentiableAt (by simp))
  have he' : deriv (fun τ => (G τ).inner x v v) t = (G t₀).inner x v v * H (t, u) := by
    rw [show (fun τ => (G τ).inner x v v) = (fun τ => (G t₀).inner x v v *
      (G τ).inner x (s⁻¹ • v) (s⁻¹ • v)) from funext he]
    exact deriv_const_mul _ hd
  rw [he', norm_mul, Real.norm_eq_abs, abs_of_pos ((G t₀).pos x v hv)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hu ((G t₀).pos x v hv).le



theorem exists_metricFamily_quadratic_time_bounds
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t₀ : ℝ} (ht₀ : D.regular ∈ 𝓝 t₀) :
    ∃ r K : ℝ, 0 < r ∧ 0 ≤ K ∧ Metric.ball t₀ r ⊆ D.regular ∧
      (∀ t ∈ Metric.ball t₀ r, ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x),
        (1 / 2 : ℝ) * (G t₀).inner x v v ≤ (G t).inner x v v ∧
          (G t).inner x v v ≤ 2 * (G t₀).inner x v v) ∧
      (∀ t ∈ Metric.ball t₀ r, ∀ s ∈ Metric.ball t₀ r,
        ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x),
          |(G t).inner x v v - (G s).inner x v v| ≤ K * |t - s| * (G t₀).inner x v v) := by
  obtain ⟨r, K, hr, hK, hrD, hbound⟩ := exists_metricFamily_quadratic_deriv_bound hG ht₀
  have hlip (t : ℝ) (ht : t ∈ Metric.ball t₀ r) (s : ℝ) (hs : s ∈ Metric.ball t₀ r)
      (x : M) (v : TangentSpace 𝓘(ℝ, E) x) :
      |(G t).inner x v v - (G s).inner x v v| ≤ K * |t - s| * (G t₀).inner x v v := by
    have h := (convex_ball t₀ r).norm_image_sub_le_of_norm_deriv_le
      (fun τ hτ => (((hG.coeff x v v).contDiffAt
        (D.regular_isOpen.mem_nhds (hrD hτ))).differentiableAt (by simp)))
      (fun τ hτ => hbound τ hτ x v) hs ht
    simpa only [Real.norm_eq_abs, mul_assoc, mul_left_comm, mul_comm] using h
  let δ := min r (1 / (2 * (K + 1)))
  have hδ : 0 < δ := lt_min hr (by positivity)
  have hδr : Metric.ball t₀ δ ⊆ Metric.ball t₀ r := Metric.ball_subset_ball (min_le_left _ _)
  refine ⟨δ, K, hδ, hK, hδr.trans hrD, ?_, fun t ht s hs x v => hlip t (hδr ht) s (hδr hs) x v⟩
  intro t ht x v
  have hgv : 0 ≤ (G t₀).inner x v v := by
    by_cases hv : v = 0
    · subst v; simp
    · exact ((G t₀).pos x v hv).le
  have hdist : |t - t₀| < δ := by simpa only [Metric.mem_ball, Real.dist_eq] using ht
  have hδbound : δ * (2 * (K + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 2 * (K + 1))).mp (min_le_right r (1 / (2 * (K + 1))))
  have hsmall : K * |t - t₀| ≤ 1 / 2 := by nlinarith [abs_nonneg (t - t₀)]
  have hb := (hlip t (hδr ht) t₀ (Metric.mem_ball_self hr) x v).trans
    (mul_le_mul_of_nonneg_right hsmall hgv)
  have h := abs_le.mp hb
  constructor <;> linarith

end DifferentialGeometry.Geometry

end

section

noncomputable section
open Set Function Bundle Manifold DifferentialGeometry Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Topology ContDiff Bundle Manifold
namespace DifferentialGeometry.Geometry
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]

theorem exists_quadratic_derivWithin_bound_on_Icc
    {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M} {a b t₀ : ℝ} (hab : a < b)
    (hG : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E))) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × TangentBundle 𝓘(ℝ, E) M => (G q.1).inner q.2.proj q.2.2 q.2.2)
      (Icc a b ×ˢ univ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a b, ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x),
      ‖derivWithin (fun s => (G s).inner x v v) (Icc a b) t‖ ≤ K * (G t₀).inner x v v := by
  let H : ℝ × MetricUnitTangent (G t₀) → ℝ := fun q =>
    derivWithin (fun s => (G s).inner (MetricUnitTangent.base q.2)
      (MetricUnitTangent.vec q.2) (MetricUnitTangent.vec q.2)) (Icc a b) q.1
  have hder : ContinuousOn (fun q : ℝ × TangentBundle 𝓘(ℝ, E) M =>
      derivWithin (fun s => (G s).inner q.2.proj q.2.2 q.2.2) (Icc a b) q.1)
      (Icc a b ×ˢ univ) :=
    (contMDiffOn_derivWithin_fst (I := (𝓘(ℝ, E).prod 𝓘(ℝ, E)))
      (M := TangentBundle 𝓘(ℝ, E) M) (uniqueDiffOn_Icc hab) hG).continuousOn
  have hmap : Continuous (fun p : ℝ × MetricUnitTangent (G t₀) => (p.1, p.2.val)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hH : ContinuousOn H (Icc a b ×ˢ univ) := by
    apply hder.comp hmap.continuousOn
    intro p hp
    exact ⟨hp.1, mem_univ _⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (metricUnit_compact (G t₀))).exists_bound_of_continuousOn hH
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht x v
  by_cases hv : v = 0
  · subst v
    simp only [map_zero]
    simp
  let s := Real.sqrt ((G t₀).inner x v v)
  have hs : 0 < s := Real.sqrt_pos.mpr ((G t₀).pos x v hv)
  have hss : s * s = (G t₀).inner x v v := Real.mul_self_sqrt ((G t₀).pos x v hv).le
  have hunit : (G t₀).inner x (s⁻¹ • v) (s⁻¹ • v) = 1 := by
    rw [metric_smul2, ← hss]
    field_simp
  let u : MetricUnitTangent (G t₀) := ⟨TotalSpace.mk' E x (s⁻¹ • v), hunit⟩
  have hu : ‖H (t, u)‖ ≤ max C 0 :=
    (hC (t, u) ⟨ht, mem_univ _⟩).trans (le_max_left _ _)
  have he (τ : ℝ) : (G τ).inner x v v = (G t₀).inner x v v *
      (G τ).inner (MetricUnitTangent.base u) (MetricUnitTangent.vec u) (MetricUnitTangent.vec u) := by
    change (G τ).inner x v v = (G t₀).inner x v v * (G τ).inner x (s⁻¹ • v) (s⁻¹ • v)
    rw [metric_smul2, ← hss]
    field_simp
  have hd : DifferentiableWithinAt ℝ (fun r => (G r).inner x (s⁻¹ • v) (s⁻¹ • v))
      (Icc a b) t := by
    have hc := (hG (t, TotalSpace.mk' E x (s⁻¹ • v)) ⟨ht, trivial⟩).comp
      (f := fun r : ℝ => (r, TotalSpace.mk' E x (s⁻¹ • v))) t
      (contMDiffWithinAt_id.prodMk contMDiffWithinAt_const)
      (fun r hr => ⟨hr, trivial⟩)
    exact hc.contDiffWithinAt.differentiableWithinAt (by simp)
  have he' : derivWithin (fun τ => (G τ).inner x v v) (Icc a b) t = (G t₀).inner x v v * H (t, u) := by
    rw [show (fun τ => (G τ).inner x v v) = (fun τ => (G t₀).inner x v v *
      (G τ).inner x (s⁻¹ • v) (s⁻¹ • v)) from funext he]
    exact derivWithin_const_mul _ hd
  rw [he', norm_mul, Real.norm_eq_abs, abs_of_pos ((G t₀).pos x v hv)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hu ((G t₀).pos x v hv).le

theorem exists_quadratic_time_bounds_on_Icc
    {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M} {a b t₀ : ℝ} (hab : a < b)
    (ht₀ : t₀ ∈ Icc a b)
    (hG : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E))) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × TangentBundle 𝓘(ℝ, E) M => (G q.1).inner q.2.proj q.2.2 q.2.2)
      (Icc a b ×ˢ univ)) :
    ∃ r K : ℝ, 0 < r ∧ 0 ≤ K ∧
      (∀ t ∈ Icc a b ∩ Metric.ball t₀ r, ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x),
        (1 / 2 : ℝ) * (G t₀).inner x v v ≤ (G t).inner x v v ∧
          (G t).inner x v v ≤ 2 * (G t₀).inner x v v) ∧
      (∀ t ∈ Icc a b, ∀ s ∈ Icc a b, ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x),
        |(G t).inner x v v - (G s).inner x v v| ≤ K * |t - s| * (G t₀).inner x v v) := by
  obtain ⟨K, hK, hbound⟩ := exists_quadratic_derivWithin_bound_on_Icc (t₀ := t₀) hab hG
  have hlip (t : ℝ) (ht : t ∈ Icc a b) (s : ℝ) (hs : s ∈ Icc a b)
      (x : M) (v : TangentSpace 𝓘(ℝ, E) x) :
      |(G t).inner x v v - (G s).inner x v v| ≤ K * |t - s| * (G t₀).inner x v v := by
    have hdiff : DifferentiableOn ℝ (fun r => (G r).inner x v v) (Icc a b) := by
      intro r hr
      have hc := (hG (r, TotalSpace.mk' E x v) ⟨hr, trivial⟩).comp
        (f := fun u : ℝ => (u, TotalSpace.mk' E x v)) r
        (contMDiffWithinAt_id.prodMk contMDiffWithinAt_const)
        (fun u hu => ⟨hu, trivial⟩)
      exact hc.contDiffWithinAt.differentiableWithinAt (by simp)
    have h := Convex.norm_image_sub_le_of_norm_derivWithin_le hdiff
      (fun r hr => hbound r hr x v) (convex_Icc a b) hs ht
    simpa only [Real.norm_eq_abs, mul_assoc, mul_left_comm, mul_comm] using h
  let δ := 1 / (2 * (K + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, K, hδ, hK, ?_, hlip⟩
  intro t ht x v
  have hgv : 0 ≤ (G t₀).inner x v v := by
    by_cases hv : v = 0
    · subst v; simp
    · exact ((G t₀).pos x v hv).le
  have hdist : |t - t₀| < δ := by
    simpa only [Metric.mem_ball, Real.dist_eq] using ht.2
  have hδbound : δ * (2 * (K + 1)) = 1 := by
    dsimp [δ]
    field_simp
  have hsmall : K * |t - t₀| ≤ 1 / 2 := by nlinarith [abs_nonneg (t - t₀)]
  have hb := (hlip t ht.1 t₀ ht₀ x v).trans (mul_le_mul_of_nonneg_right hsmall hgv)
  have h := abs_le.mp hb
  constructor <;> linarith

end DifferentialGeometry.Geometry

end

end
