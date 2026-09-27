import DifferentialGeometry.Bundle.VelocityLift.Continuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Basic
import DifferentialGeometry.Geometry.Metric.Family.Basic

open Set Bundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M]

theorem immersedOn_closure_of_speed_lower_bound
    {g : ℝ → SmoothRiemannianMetric I M} {J : Set ℝ} {c : CurveMap M} {m : ℝ → ℝ}
    (hspeed : ∀ x, ContinuousOn (fun t => c.speed g x t) (closure J))
    (hm : ∀ x, 0 < m x) (hbound : ∀ x t, t ∈ J → m x ≤ c.speed g x t) :
    c.ImmersedOn (I := I) (closure J) := by
  intro x t ht
  have hs : ContinuousOn (fun t => c.speed g x t) (closure J) := hspeed x
  have hclosed : m x ≤ c.speed g x t :=
    le_on_closure (fun s hs => hbound x s hs) continuousOn_const hs ht
  intro hzero
  have hzero' : c.speed g x t = 0 := by simp [speed, hzero]
  exact (hm x).not_ge (hzero' ▸ hclosed)

variable [FiniteDimensional ℝ E]

theorem continuousOn_speed_of_leftInverse
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g)
    {J : Set ℝ} (hJ : J ⊆ D.carrier) {c : CurveMap M}
    (e : M → F) (r : F → M) {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) I 1 r U)
    (hmem : ∀ x t, t ∈ J → e (c.lift x t) ∈ U)
    (hleft : ∀ x t, t ∈ J → r (e (c.lift x t)) = c.lift x t)
    (hslice : ∀ t ∈ J, Differentiable ℝ (fun x => e (c.lift x t)))
    (hval : ContinuousOn (fun p : ℝ × ℝ => e (c.lift p.1 p.2)) (univ ×ˢ J))
    (hder : ContinuousOn (fun p : ℝ × ℝ => deriv (fun x => e (c.lift x p.2)) p.1)
      (univ ×ˢ J)) :
    ContinuousOn (fun p : ℝ × ℝ => c.speed g p.1 p.2) (univ ×ˢ J) := by
  have hX := continuousOn_velocityLift_slice_of_leftInverse c.lift e r hU hr
    hmem hleft hslice hval hder
  rw [continuousOn_iff_continuous_domRestrict]
  have hXs := continuousOn_iff_continuous_domRestrict.mp hX
  have ht : Continuous (fun p : ↥(univ ×ˢ J) => (⟨p.1.2, p.2.2⟩ : J)) :=
    (show Continuous (fun p : ↥((univ : Set ℝ) ×ˢ J) => p.1.2) from
      continuous_snd.comp continuous_subtype_val).subtype_mk _
  have hq := (metricTimeBundleQuad_cont_of_metricFamilySmoothOn g hG hJ).comp
    (ht.prodMk hXs)
  exact Real.continuous_sqrt.comp hq

theorem immersedOn_Icc_of_leftInverse_of_speed_lower_bound
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g)
    {a T m : ℝ} (haT : a < T) (hJ : Icc a T ⊆ D.carrier)
    {c : CurveMap M} (e : M → F) (r : F → M) {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) I 1 r U)
    (hmem : ∀ x t, t ∈ Icc a T → e (c.lift x t) ∈ U)
    (hleft : ∀ x t, t ∈ Icc a T → r (e (c.lift x t)) = c.lift x t)
    (hslice : ∀ t ∈ Icc a T, Differentiable ℝ (fun x => e (c.lift x t)))
    (hval : ContinuousOn (fun p : ℝ × ℝ => e (c.lift p.1 p.2)) (univ ×ˢ Icc a T))
    (hder : ContinuousOn (fun p : ℝ × ℝ => deriv (fun x => e (c.lift x p.2)) p.1)
      (univ ×ˢ Icc a T))
    (hm : 0 < m) (hbound : ∀ x t, t ∈ Ico a T → m ≤ c.speed g x t) :
    c.ImmersedOn (I := I) (Icc a T) := by
  have hspeed := continuousOn_speed_of_leftInverse hG hJ e r hU hr
    hmem hleft hslice hval hder
  have hclosure : closure (Ico a T) = Icc a T := closure_Ico haT.ne
  rw [← hclosure] at hspeed ⊢
  apply immersedOn_closure_of_speed_lower_bound (m := fun _ => m) ?_ (fun _ => hm) hbound
  intro x
  exact hspeed.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun s hs => ⟨mem_univ x, hs⟩)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap
