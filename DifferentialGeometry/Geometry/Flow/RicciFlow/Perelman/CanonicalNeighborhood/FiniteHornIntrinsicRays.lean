import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornInteriorMinimizers
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornInteriorSpheres
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactMetricSegment
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
noncomputable section
open Filter Manifold Set
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W]

theorem lipschitzOnWith_of_subinterval_lengths
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    {gamma : ℝ → W} (hsmooth : ContMDiff 𝓘(ℝ, ℝ) I3 ∞ gamma)
    {rho : ℝ} (hrho : 0 ≤ rho) {L : ℝ≥0} (hL : rho ≤ L)
    (hsub : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
      metricPathELength g gamma a b = ENNReal.ofReal (b - a) * ENNReal.ofReal rho) :
    LipschitzOnWith L gamma (Icc (0 : ℝ) 1) := by
  have hordered (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
      (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) (hab : a ≤ b) :
      dist (gamma a) (gamma b) ≤ (L : ℝ) * dist a b := by
    have hC1 : ContMDiffOn 𝓘(ℝ, ℝ) I3 1 gamma (Icc a b) :=
      (hsmooth.of_le (by decide)).contMDiffOn
    have hbound := edistOf_le_metricPathELength g hab hC1
    rw [H.edist_eq_ofReal_dist, hsub a ha b hb,
      ← ENNReal.ofReal_mul (sub_nonneg.mpr hab)] at hbound
    have hreal : dist (gamma a) (gamma b) ≤ (b - a) * rho :=
      (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sub_nonneg.mpr hab) hrho)).mp hbound
    calc
      _ ≤ (b - a) * rho := hreal
      _ ≤ (b - a) * (L : ℝ) := mul_le_mul_of_nonneg_left hL (sub_nonneg.mpr hab)
      _ = _ := by rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hab)]; ring
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro a ha b hb
  rcases le_total a b with hab | hba
  · exact hordered a ha b hb hab
  · simpa only [dist_comm] using hordered b hb a ha hba

variable [SigmaCompactSpace W]

private theorem finiteHorn_exists_completion_segment
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) :
    ∃ d : ℝ, 0 < d ∧ ∀ x : W,
      dist (x : UniformSpace.Completion W) H.endpoint < d →
      ∃ f : Icc (0 : ℝ) 1 → UniformSpace.Completion W,
        f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = H.endpoint ∧
        (∀ s, f s ∈ closure ((fun y : W => (y : UniformSpace.Completion W)) '' H.subend 0)) ∧
        ∀ s t, dist (f s) (f t) =
          dist (x : UniformSpace.Completion W) H.endpoint * dist s t := by
  classical
  let : IsManifold I3 1 W := IsManifold.of_le (n := (∞ : WithTop ℕ∞)) (by decide)
  let : T2Space (TangentBundle I3 W) := inferInstance
  obtain ⟨d, hd, hmin⟩ := finiteHorn_exists_subradial_minimizer g H
  obtain ⟨delta, hdelta, htail⟩ := finiteHorn_ball_subset_subend g H 0
  refine ⟨min d (delta / 4), lt_min hd (by positivity), ?_⟩
  intro x hx
  let r : ℝ := dist (x : UniformSpace.Completion W) H.endpoint
  have hr : 0 < r := dist_pos.mpr (H.endpoint_missing x)
  have hrd : r < d := hx.trans_le (min_le_left _ _)
  have hrdelta : r < delta / 4 := hx.trans_le (min_le_right _ _)
  let rho (n : ℕ) : ℝ := r * (n : ℝ) / ((n : ℝ) + 1)
  have hrho (n : ℕ) : 0 ≤ rho n := by positivity
  have hrhol (n : ℕ) : rho n < r := by
    have hden : 0 < (n : ℝ) + 1 := by positivity
    exact (div_lt_iff₀ hden).mpr (by nlinarith)
  have hrhot : Tendsto rho atTop (𝓝 r) := by
    simpa only [rho, mul_div_assoc, mul_one] using
      (tendsto_natCast_div_add_atTop (1 : ℝ)).const_mul r
  have hspheres (n : ℕ) : ∃ y : W, dist x y = rho n ∧
      dist (y : UniformSpace.Completion W) H.endpoint < 2 * (r - rho n) :=
    finiteHorn_exists_sphere_point_near_endpoint g H x (hrho n) (hrhol n)
  choose y hyDist hyEnd using hspheres
  have hcurves (n : ℕ) := hmin x hrd (y n) (by rw [hyDist n]; exact hrhol n)
  choose R hRl hRh hRc gamma hg0 hg1 hgSmooth hgMem hgLength hgSub using hcurves
  let L : ℝ≥0 := ⟨r, hr.le⟩
  have hLip (n : ℕ) : LipschitzOnWith L (gamma n) (Icc (0 : ℝ) 1) := by
    apply lipschitzOnWith_of_subinterval_lengths (L := L) g H
      (hgSmooth n) (hrho n) (hrhol n).le
    intro a ha b hb
    simpa only [hyDist n] using hgSub n a ha b hb
  let c (n : ℕ) (s : ℝ) : UniformSpace.Completion W := gamma n s
  let K : Set (UniformSpace.Completion W) :=
    closure ((fun y : W => (y : UniformSpace.Completion W)) '' H.subend 0)
  have hK : IsCompact K := finiteHorn_isCompact_closure_subend g H 0
  have hc (n : ℕ) : ContinuousOn (c n) (Icc (0 : ℝ) 1) :=
    ((UniformSpace.Completion.continuous_coe W).comp (hgSmooth n).continuous).continuousOn
  have hcK (n : ℕ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : c n s ∈ K := by
    have hball : dist (gamma n s) x ≤ R n := hgMem n s hs
    have hnear : dist (gamma n s : UniformSpace.Completion W) H.endpoint < delta := by
      have htri := dist_triangle (gamma n s : UniformSpace.Completion W)
        (x : UniformSpace.Completion W) H.endpoint
      rw [UniformSpace.Completion.dist_eq] at htri
      change dist (gamma n s : UniformSpace.Completion W) H.endpoint ≤ dist (gamma n s) x + r at htri
      have hR : R n < r := hRh n
      linarith
    exact subset_closure ⟨gamma n s, htail _ hnear, rfl⟩
  have hcLip (n : ℕ) : LipschitzOnWith L (c n) (Icc (0 : ℝ) 1) := by
    apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro a ha b hb
    simpa only [c, UniformSpace.Completion.dist_eq] using
      (lipschitzOnWith_iff_dist_le_mul.mp (hLip n)) a ha b hb
  have hc0 : Tendsto (fun n => c n 0) atTop (𝓝 (x : UniformSpace.Completion W)) := by
    simpa only [c, hg0] using (tendsto_const_nhds (x := (x : UniformSpace.Completion W)))
  have hyT : Tendsto (fun n => (y n : UniformSpace.Completion W)) atTop (𝓝 H.endpoint) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hgap : Tendsto (fun n => 2 * (r - rho n)) atTop (𝓝 (0 : ℝ)) := by
      simpa using ((tendsto_const_nhds (x := r)).sub hrhot).const_mul 2
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => (hyEnd n).le) hgap
  have hc1 : Tendsto (fun n => c n 1) atTop (𝓝 H.endpoint) := by
    simpa only [c, hg1] using hyT
  obtain ⟨f, _hf, hf0, hf1, hfK, hfDist⟩ :=
    exists_metric_segment_of_compact_lipschitz_curves hK
      (L := L) (p := (x : UniformSpace.Completion W)) (q := H.endpoint) rfl
      c hc hcK hcLip hc0 hc1
  exact ⟨f, hf0, hf1, hfK, hfDist⟩

omit [SigmaCompactSpace W] in
private theorem endRay_of_completion_segment
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) (x : W)
    (f : Icc (0 : ℝ) 1 → UniformSpace.Completion W)
    (hf0 : f ⟨0, by norm_num⟩ = x) (hf1 : f ⟨1, by norm_num⟩ = H.endpoint)
    (hfK : ∀ s, f s ∈ closure ((fun y : W => (y : UniformSpace.Completion W)) '' H.subend 0))
    (hfDist : ∀ s t, dist (f s) (f t) =
      dist (x : UniformSpace.Completion W) H.endpoint * dist s t) :
    ∃ a : EndRay H.endpoint, a.point a.length = x := by
  classical
  let r : ℝ := dist (x : UniformSpace.Completion W) H.endpoint
  have hr : 0 < r := dist_pos.mpr (H.endpoint_missing x)
  let tau (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) r) : Icc (0 : ℝ) 1 :=
    ⟨1 - s / r, by
      constructor
      · exact sub_nonneg.mpr ((div_le_one hr).mpr hs.2)
      · exact sub_le_self _ (div_nonneg hs.1.le hr.le)⟩
  have htau (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) r) :
      dist (f (tau s hs)) H.endpoint = s := by
    have h := hfDist (tau s hs) ⟨1, by norm_num⟩
    rw [hf1] at h
    change dist (f (tau s hs)) H.endpoint = r * |(1 - s / r) - 1| at h
    rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg (div_nonneg hs.1.le hr.le)] at h
    simpa only [mul_div_cancel₀ _ hr.ne'] using h
  have hrealized (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) r) :
      ∃ z : W, (z : UniformSpace.Completion W) = f (tau s hs) := by
    apply finiteHorn_mem_range_of_mem_closure_subend g H 0 (hfK (tau s hs))
    intro heq
    have hd := htau s hs
    rw [heq, dist_self] at hd
    exact hs.1.ne' hd.symm
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
        _ = r * |(1 - s / r) - (1 - t / r)| := hfDist _ _
        _ = |s - t| := by
          have heq : (1 - s / r) - (1 - t / r) = -(s - t) / r := by ring
          rw [heq, abs_div, abs_neg, abs_of_pos hr]
          exact mul_div_cancel₀ _ hr.ne'
  }
  refine ⟨a, ?_⟩
  have hrmem : r ∈ Ioc (0 : ℝ) r := ⟨hr, le_rfl⟩
  have htauEnd : tau r hrmem = ⟨0, by norm_num⟩ := by
    apply Subtype.ext
    simp [tau, hr.ne']
  have heq : (point r : UniformSpace.Completion W) = x := by
    rw [hpoint r hrmem, htauEnd, hf0]
  change point r = x
  exact (UniformSpace.Completion.coe_injective W) heq

theorem finiteHorn_exists_intrinsic_endRay_near_endpoint
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) :
    ∃ d : ℝ, 0 < d ∧ ∀ x : W,
      dist (x : UniformSpace.Completion W) H.endpoint < d →
      ∃ a : EndRay H.endpoint, a.point a.length = x := by
  obtain ⟨d, hd, hsegment⟩ := finiteHorn_exists_completion_segment g H
  refine ⟨d, hd, ?_⟩
  intro x hx
  obtain ⟨f, hf0, hf1, hfK, hfDist⟩ := hsegment x hx
  exact endRay_of_completion_segment g H x f hf0 hf1 hfK hfDist

theorem finiteHorn_intrinsic_rays (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) :
    ∃ i, ∀ x ∈ H.subend i, ∃ a : EndRay H.endpoint, a.point a.length = x := by
  obtain ⟨d, hd, hrays⟩ := finiteHorn_exists_intrinsic_endRay_near_endpoint g H
  obtain ⟨i, hi⟩ := finiteHorn_subend_radial_small g H hd
  exact ⟨i, fun x hx => hrays x (hi x hx)⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
