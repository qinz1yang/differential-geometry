import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

/-!
# Derivatives of limits on a closed interval, and uniform composition

Helpers for the geodesic-limit package CM4 (lane CM-L).

* `hasDerivWithinAt_of_tendsto_of_tendstoUniformlyOn_deriv`: if `f i → g` pointwise on `Icc a b`,
  each `f i` has derivative `f' i` within `Icc a b`, and `f' i → g'` uniformly on `Icc a b` with `g'`
  continuous, then `g` has derivative `g'` within `Icc a b` at every point, endpoints included.
* `TendstoUniformlyOn.comp_continuousAt_of_isCompact`: post-composition with a map continuous at every
  point of a compact set containing the limit values preserves uniform convergence.
* `TendstoUniformlyOn.comp_continuousOn_of_isCompact`: the same with all values in the compact set and
  continuity on it.
-/

set_option autoImplicit false

noncomputable section

open Filter Set Topology Metric

namespace DifferentialGeometry.Analysis.ODE.GeodesicLimits

/-- Derivative of a pointwise limit on a closed interval whose derivatives converge uniformly to a
continuous function (one-sided at the endpoints). -/
theorem hasDerivWithinAt_of_tendsto_of_tendstoUniformlyOn_deriv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a b : ℝ} {f f' : ℕ → ℝ → F} {g g' : ℝ → F}
    (hf : ∀ i, ∀ t ∈ Icc a b, HasDerivWithinAt (f i) (f' i t) (Icc a b) t)
    (hlim : ∀ t ∈ Icc a b, Tendsto (fun i => f i t) atTop (𝓝 (g t)))
    (hderiv : TendstoUniformlyOn f' g' atTop (Icc a b))
    (hg' : ContinuousOn g' (Icc a b)) :
    ∀ t ∈ Icc a b, HasDerivWithinAt g (g' t) (Icc a b) t := by
  intro t ht
  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousWithinAt_iff.mp (hg' t ht) (ε / 3) (by positivity)
  have hS : Icc a b ∩ ball t δ ∈ 𝓝[Icc a b] t :=
    inter_mem_nhdsWithin _ (ball_mem_nhds t hδ)
  filter_upwards [hS] with s hs
  -- the estimate for each late `i`
  have hunif := Metric.tendstoUniformlyOn_iff.mp hderiv (ε / 3) (by positivity)
  have hbound : ∀ᶠ i in atTop,
      ‖(f i s - (s - t) • f' i t) - (f i t - (t - t) • f' i t)‖ ≤ ε * ‖s - t‖ := by
    filter_upwards [hunif] with i hi
    have hconv : Convex ℝ (Icc a b ∩ ball t δ) := (convex_Icc a b).inter (convex_ball t δ)
    have htS : t ∈ Icc a b ∩ ball t δ := ⟨ht, mem_ball_self hδ⟩
    refine hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun u => f i u - (u - t) • f' i t) (f' := fun u => f' i u - f' i t) ?_ ?_ htS hs
    · intro u hu
      have h1 := (hf i u hu.1).mono (inter_subset_left (t := ball t δ))
      have h2 : HasDerivWithinAt (fun u : ℝ => (u - t) • f' i t) ((1 : ℝ) • f' i t)
          (Icc a b ∩ ball t δ) u :=
        ((hasDerivWithinAt_id u _).sub_const t).smul_const (f' i t)
      have h3 := h1.sub h2
      rw [one_smul] at h3
      exact h3
    · intro u hu
      have hu1 : dist (g' u) (f' i u) < ε / 3 := hi u hu.1
      have hu2 : dist (g' u) (g' t) < ε / 3 := hδg hu.1 hu.2
      have hu3 : dist (g' t) (f' i t) < ε / 3 := hi t ht
      rw [dist_eq_norm] at hu1 hu2 hu3
      calc ‖f' i u - f' i t‖
          = ‖-(g' u - f' i u) + (g' u - g' t) + (g' t - f' i t)‖ := by congr 1; abel
        _ ≤ ‖-(g' u - f' i u)‖ + ‖g' u - g' t‖ + ‖g' t - f' i t‖ := norm_add₃_le
        _ ≤ ε := by rw [norm_neg]; linarith
  have hlimit : Tendsto (fun i => ‖(f i s - (s - t) • f' i t) - (f i t - (t - t) • f' i t)‖)
      atTop (𝓝 ‖(g s - (s - t) • g' t) - (g t - (t - t) • g' t)‖) := by
    have hft : Tendsto (fun i => f' i t) atTop (𝓝 (g' t)) := hderiv.tendsto_at ht
    exact (((hlim s hs.1).sub (tendsto_const_nhds.smul hft)).sub
      ((hlim t ht).sub (tendsto_const_nhds.smul hft))).norm
  have hle := le_of_tendsto hlimit hbound
  have heq : (g s - (s - t) • g' t) - (g t - (t - t) • g' t) = g s - g t - (s - t) • g' t := by
    rw [sub_self, zero_smul, sub_zero]; abel
  rwa [heq] at hle

/-- Post-composition with a map continuous at every point of a compact set containing the limit
values preserves uniform convergence. -/
theorem _root_.TendstoUniformlyOn.comp_continuousAt_of_isCompact
    {α β γ ι : Type*} [PseudoMetricSpace β] [PseudoMetricSpace γ] {p : Filter ι}
    {F : ι → α → β} {f : α → β} {s : Set α} {K : Set β} (hK : IsCompact K)
    (hfK : ∀ x ∈ s, f x ∈ K) {Ψ : β → γ} (hΨ : ∀ y ∈ K, ContinuousAt Ψ y)
    (h : TendstoUniformlyOn F f p s) :
    TendstoUniformlyOn (fun i x => Ψ (F i x)) (fun x => Ψ (f x)) p s := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  have hU := hK.uniformContinuousAt_of_continuousAt Ψ hΨ (Metric.dist_mem_uniformity hε)
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_uniformity_dist.mp hU
  filter_upwards [h δ hδ] with i hi x hx
  exact hδU (hi x hx) (hfK x hx)

/-- Post-composition with a map continuous on a compact set containing all values preserves uniform
convergence. -/
theorem _root_.TendstoUniformlyOn.comp_continuousOn_of_isCompact
    {α β γ ι : Type*} [PseudoMetricSpace β] [PseudoMetricSpace γ] {p : Filter ι}
    {F : ι → α → β} {f : α → β} {s : Set α} {K : Set β} (hK : IsCompact K)
    (hFK : ∀ i, ∀ x ∈ s, F i x ∈ K) (hfK : ∀ x ∈ s, f x ∈ K) {Ψ : β → γ}
    (hΨ : ContinuousOn Ψ K) (h : TendstoUniformlyOn F f p s) :
    TendstoUniformlyOn (fun i x => Ψ (F i x)) (fun x => Ψ (f x)) p s :=
  (hK.uniformContinuousOn_of_continuous hΨ).comp_tendstoUniformlyOn_eventually
    (Eventually.of_forall hFK) hfK h

end DifferentialGeometry.Analysis.ODE.GeodesicLimits
