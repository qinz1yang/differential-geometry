import Batteries.Tactic.Alias
import DifferentialGeometry.Geometry.Geodesic.Local
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Basic

noncomputable section

open Bundle Filter Manifold Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem isGeodesicAt_zero_of_equation
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {U : Set ℝ}
    (hU : U ∈ 𝓝 (0 : ℝ)) (hgeo : IsGeodesicOn (I := I) g γ U)
    (hcont : ContinuousOn γ U) : IsGeodesicAt (I := I) g γ 0 := by
  obtain ⟨η, f, hfzero, hηf, hηzero, hf, hη⟩ :=
    exists_geodesic_with_initial_velocity_at g (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 1)
  have hvel : (mfderiv 𝓘(ℝ, ℝ) I η 0 1 : E) = mfderiv 𝓘(ℝ, ℝ) I γ 0 1 := by
    have hh := hf.mfderiv_proj_one (by rw [hfzero]; exact mem_chart_source H (γ 0))
    rw [hηf]
    exact hh.trans (congrArg (fun z : TangentBundle I M ↦ (z.snd : E)) hfzero)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hU (eventually_isGeodesicAt hη))
  have heq := geo_eqOn_of_initial g Metric.isOpen_ball (convex_ball (0 : ℝ) ε).isPreconnected
    (Metric.mem_ball_self hε)
    (fun s hs ↦ (hball hs).2.hasGeodesicEquationAt)
    (fun s hs ↦ hgeo s (hball hs).1)
    (fun s hs ↦ (hball hs).2.continuousAt.continuousWithinAt)
    (hcont.mono fun _ hs ↦ (hball hs).1) hηzero hvel
  exact isGeodesicAt_congr hη
    (eventually_of_mem (Metric.ball_mem_nhds 0 hε) fun s hs ↦ (heq hs).symm)

theorem isGeodesicAt_of_isGeodesicOn
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {U : Set ℝ} {t : ℝ}
    (hU : U ∈ 𝓝 t) (hgeo : IsGeodesicOn (I := I) g γ U)
    (hcont : ContinuousOn γ U) : IsGeodesicAt (I := I) g γ t := by
  let V : Set ℝ := {s | s + t ∈ U}
  have hV : V ∈ 𝓝 (0 : ℝ) := by
    have hc : Tendsto (fun s : ℝ ↦ s + t) (𝓝 0) (𝓝 t) := by
      simpa only [zero_add] using (continuous_add_const t).tendsto 0
    exact hc hU
  have hshift : IsGeodesicOn (I := I) g (fun s ↦ γ (s + t)) V := by
    simpa only [one_mul] using isGeodesicOn_comp_affine (c := 1) (d := t) hgeo
  have hshiftcont : ContinuousOn (fun s ↦ γ (s + t)) V :=
    hcont.comp (continuous_add_const t).continuousOn (fun _ hs ↦ hs)
  have hh := isGeodesicAt_zero_of_equation g hV hshift hshiftcont
  simpa only [zero_sub, neg_neg, neg_add_cancel_right] using isGeodesicAt_comp_add hh (-t)

end DifferentialGeometry.Geometry

namespace Poincare.Geometry

alias isGeodesicAt_of_isGeodesicOn := DifferentialGeometry.Geometry.isGeodesicAt_of_isGeodesicOn

end Poincare.Geometry
