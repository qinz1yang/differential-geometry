import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactArmLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornSegmentLift

set_option autoImplicit false
noncomputable section
open Filter Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

theorem finiteHorn_arm_subsequence_eq_endRay
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : EndRay H.endpoint, ∀ r : ℝ,
      0 < r → r < min a.length d → ∀ i : ℕ,
      ∀ (length : ℕ → ℝ) (c : ℕ → Icc (0 : ℝ) 1 → W),
        (∀ n, 0 ≤ length n) → Tendsto length atTop (𝓝 r) →
        (∀ n s, c n s ∈ H.subend i) →
        (∀ n s t, dist (c n s) (c n t) = length n * dist s t) →
        Tendsto (fun n => (c n ⟨0, by norm_num⟩ : UniformSpace.Completion W)) atTop (𝓝 H.endpoint) →
        (∀ n, c n ⟨1, by norm_num⟩ = a.point r) →
        ∃ phi : ℕ → ℕ, StrictMono phi ∧
          TendstoUniformly (fun n s => (c (phi n) s : UniformSpace.Completion W))
            (fun s : Icc (0 : ℝ) 1 => if (s : ℝ) = 0 then H.endpoint
              else (a.point (r * s) : UniformSpace.Completion W)) atTop := by
  obtain ⟨d, hd, hidentify⟩ := finiteHorn_completion_segment_eq_endRay g H
  refine ⟨d, hd, ?_⟩
  intro a r hr hrd i length c hlength hlengthT hmem hdist hbase hend
  let C (n : ℕ) (s : Icc (0 : ℝ) 1) : UniformSpace.Completion W := c n s
  have hK := finiteHorn_isCompact_closure_subend g H i
  have hCK (n : ℕ) (s : Icc (0 : ℝ) 1) :
      C n s ∈ closure ((fun y : W => (y : UniformSpace.Completion W)) '' H.subend i) :=
    subset_closure ⟨c n s, hmem n s, rfl⟩
  have hCDist (n : ℕ) (s t : Icc (0 : ℝ) 1) :
      dist (C n s) (C n t) = length n * dist s t := by
    simpa only [C, UniformSpace.Completion.dist_eq] using hdist n s t
  have hCend : Tendsto (fun n => C n ⟨1, by norm_num⟩) atTop
      (𝓝 (a.point r : UniformSpace.Completion W)) := by
    simpa only [C, hend] using
      (tendsto_const_nhds (x := (a.point r : UniformSpace.Completion W)))
  obtain ⟨f, phi, hphi, _hfcont, huniform, hf0, hf1, hfK, hfDist⟩ :=
    exists_uniform_limit_of_compact_metric_segments hK hlength hlengthT C hCK hCDist hbase hCend
  have hfRay := hidentify a r hr hrd i f hf0 hf1 hfK hfDist
  have heq : f = fun s : Icc (0 : ℝ) 1 => if (s : ℝ) = 0 then H.endpoint
      else (a.point (r * s) : UniformSpace.Completion W) := by
    funext s
    by_cases hs : (s : ℝ) = 0
    · have hsz : s = ⟨0, by norm_num⟩ := Subtype.ext hs
      rw [if_pos hs]
      exact (congrArg f hsz).trans hf0
    · rw [if_neg hs]
      exact hfRay s (lt_of_le_of_ne s.property.1 (Ne.symm hs))
  rw [heq] at huniform
  exact ⟨phi, hphi, huniform⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
