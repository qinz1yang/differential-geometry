import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornRayUniqueness

set_option autoImplicit false
noncomputable section
open Filter Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W]

theorem finiteHorn_lift_completion_segment
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) (i : ℕ)
    {r : ℝ} (hr : 0 < r) (x : W)
    (f : Icc (0 : ℝ) 1 → UniformSpace.Completion W)
    (hf0 : f ⟨0, by norm_num⟩ = H.endpoint) (hf1 : f ⟨1, by norm_num⟩ = x)
    (hfK : ∀ s, f s ∈ closure ((fun y : W => (y : UniformSpace.Completion W)) '' H.subend i))
    (hfDist : ∀ s t, dist (f s) (f t) = r * dist s t) :
    ∃ a : EndRay H.endpoint, a.length = r ∧ a.point r = x ∧
      ∀ s : Icc (0 : ℝ) 1, 0 < (s : ℝ) →
        (a.point (r * s) : UniformSpace.Completion W) = f s := by
  classical
  let tau (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) r) : Icc (0 : ℝ) 1 :=
    ⟨s / r, ⟨div_nonneg hs.1.le hr.le, (div_le_one hr).mpr hs.2⟩⟩
  have htau (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) r) :
      dist (f (tau s hs)) H.endpoint = s := by
    have h := hfDist (tau s hs) ⟨0, by norm_num⟩
    rw [hf0] at h
    change dist (f (tau s hs)) H.endpoint = r * |s / r - 0| at h
    rw [sub_zero, abs_of_nonneg (div_nonneg hs.1.le hr.le)] at h
    simpa only [mul_div_cancel₀ _ hr.ne'] using h
  have hrealized (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) r) :
      ∃ z : W, (z : UniformSpace.Completion W) = f (tau s hs) := by
    apply finiteHorn_mem_range_of_mem_closure_subend g H i (hfK (tau s hs))
    intro heq
    have h := htau s hs
    rw [heq, dist_self] at h
    exact hs.1.ne' h.symm
  let point (s : ℝ) : W := if hs : s ∈ Ioc (0 : ℝ) r then
      Classical.choose (hrealized s hs) else x
  have hpoint (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) r) :
      (point s : UniformSpace.Completion W) = f (tau s hs) := by
    dsimp only [point]
    rw [dif_pos hs]
    exact Classical.choose_spec (hrealized s hs)
  let a : EndRay H.endpoint := {
    length := r
    length_pos := hr
    point := point
    radial := by
      intro s hs
      rw [hpoint s hs]
      exact htau s hs
    minimizing := by
      intro s hs t ht
      calc
        dist (point s) (point t) =
            dist (point s : UniformSpace.Completion W) (point t : UniformSpace.Completion W) := by
              rw [UniformSpace.Completion.dist_eq]
        _ = dist (f (tau s hs)) (f (tau t ht)) := by rw [hpoint s hs, hpoint t ht]
        _ = r * |s / r - t / r| := hfDist _ _
        _ = |s - t| := by
          rw [← sub_div, abs_div, abs_of_pos hr]
          exact mul_div_cancel₀ _ hr.ne'
  }
  have hparam (s : Icc (0 : ℝ) 1) (hs : 0 < (s : ℝ)) : r * s ∈ Ioc (0 : ℝ) r :=
    ⟨mul_pos hr hs, by simpa only [mul_one] using mul_le_mul_of_nonneg_left s.property.2 hr.le⟩
  have hall (s : Icc (0 : ℝ) 1) (hs : 0 < (s : ℝ)) :
      (a.point (r * s) : UniformSpace.Completion W) = f s := by
    have htau_eq : tau (r * s) (hparam s hs) = s := by
      apply Subtype.ext
      exact mul_div_cancel_left₀ (s : ℝ) hr.ne'
    exact (hpoint (r * s) (hparam s hs)).trans (congrArg f htau_eq)
  refine ⟨a, rfl, ?_, hall⟩
  apply UniformSpace.Completion.coe_injective W
  have h := hall ⟨1, by norm_num⟩ (by norm_num)
  simpa only [mul_one, hf1] using h

variable [SigmaCompactSpace W]

theorem finiteHorn_completion_segment_eq_endRay
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : EndRay H.endpoint, ∀ r : ℝ,
      0 < r → r < min a.length d → ∀ i : ℕ,
      ∀ f : Icc (0 : ℝ) 1 → UniformSpace.Completion W,
        f ⟨0, by norm_num⟩ = H.endpoint → f ⟨1, by norm_num⟩ = a.point r →
        (∀ s, f s ∈ closure ((fun y : W => (y : UniformSpace.Completion W)) '' H.subend i)) →
        (∀ s t, dist (f s) (f t) = r * dist s t) →
        ∀ s : Icc (0 : ℝ) 1, 0 < (s : ℝ) → f s = (a.point (r * s) : UniformSpace.Completion W) := by
  obtain ⟨d, hd, hunique⟩ := finiteHorn_endRay_unique_inward g H
  refine ⟨d, hd, ?_⟩
  intro a r hr hrd i f hf0 hf1 hfK hfDist
  obtain ⟨b, hbLength, hbEnd, hbPoint⟩ :=
    finiteHorn_lift_completion_segment g H i hr (a.point r) f hf0 hf1 hfK hfDist
  have hagree := hunique a b r hr hrd (by rw [hbLength]) hbEnd.symm
  intro s hs
  have hparam : r * s ∈ Ioc (0 : ℝ) r :=
    ⟨mul_pos hr hs, by simpa only [mul_one] using mul_le_mul_of_nonneg_left s.property.2 hr.le⟩
  exact (hbPoint s hs).symm.trans (congrArg
    (fun x : W => (x : UniformSpace.Completion W)) (hagree (r * s) hparam).symm)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
