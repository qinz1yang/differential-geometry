import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AmbientCollarShortening
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornStructure

set_option autoImplicit false
noncomputable section
open Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W]

theorem finiteHorn_tail_ball_capture (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) :
    ∃ i, ∀ x ∈ H.subend i,
      ∃ (F : PartialDiffeomorph IC I3 Cylinder W ∞) (p : Sphere 2),
        F (p, 0) = x ∧ univ ×ˢ Icc (-H.collar_depth) H.collar_depth ⊆ F.source ∧
        ∃ hQ : 0 < metricScalarAt g x,
          riemannianBallOf (scaleMetric (metricScalarAt g x) hQ g) x (H.collar_depth / 2) ⊆
            F '' (univ ×ˢ Icc (-H.collar_depth) H.collar_depth) ∧
          ∀ r : ℝ, r < H.collar_depth / 2 →
            IsCompact (riemannianClosedBallOf (scaleMetric (metricScalarAt g x) hQ g) x r) := by
  obtain ⟨i, htail⟩ := H.cylindrical_tail
  refine ⟨i, ?_⟩
  intro x hx
  obtain ⟨C, F, p, hcenter, _hsection, hsource, hQ, ⟨cmp⟩⟩ := htail x hx
  refine ⟨F, p, hcenter, hsource, hQ, ?_, ?_⟩
  · have hc := collar_ball_subset_image C (fun _ => scaleMetric (metricScalarAt g x) hQ g) F
      cmp rfl (by linarith [H.neck_precision_small]) (by simp) H.collar_depth_pos
      hsource (fun _ hy => hy) p
    simpa only [hcenter] using hc
  · intro r hr
    have hc := collar_isCompact_closedBall C (fun _ => scaleMetric (metricScalarAt g x) hQ g) F
      cmp rfl (by linarith [H.neck_precision_small]) (by simp) H.collar_depth_pos hr
      hsource (fun _ hy => hy) p
    simpa only [hcenter] using hc

theorem exists_finiteHorn_ambient_collar_trapping_depth :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ∃ i, ∀ x ∈ H.subend i,
      ∃ (F : PartialDiffeomorph IC I3 Cylinder W ∞) (p : Sphere 2),
        F (p, 0) = x ∧ univ ×ˢ Icc (-H₀) H₀ ⊆ F.source ∧
        IsCompact (F '' (univ ×ˢ Icc (-H₀) H₀)) ∧
        ∃ hQ : 0 < metricScalarAt g x, ∀ (q r : Sphere 2) (gamma : ℝ → W),
          ContMDiffOn 𝓘(ℝ, ℝ) I3 1 gamma (Icc (0 : ℝ) 1) →
          gamma 0 = F (q, 0) → gamma 1 = F (r, 0) →
          metricPathELength (scaleMetric (metricScalarAt g x) hQ g) gamma 0 1 ≤
            riemannianEDistOf (scaleMetric (metricScalarAt g x) hQ g) (gamma 0) (gamma 1) +
              ENNReal.ofReal (1 / 2 : ℝ) →
          ∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ F '' (univ ×ˢ Icc (-H₀) H₀) := by
  obtain ⟨H₀, hH₀, htrap⟩ := exists_fixed_ambient_collar_trapping_constants (M := W)
  refine ⟨H₀, hH₀, ?_⟩
  intro g H hdepth
  obtain ⟨i, htail⟩ := H.cylindrical_tail
  refine ⟨i, ?_⟩
  intro x hx
  obtain ⟨C, F, p, hcenter, _hsection, hsource, hQ, ⟨cmp⟩⟩ := htail x hx
  have hsubset : (univ ×ˢ Icc (-H₀) H₀ : Set Cylinder) ⊆
      univ ×ˢ Icc (-H.collar_depth) H.collar_depth := by
    intro z hz
    exact ⟨hz.1, ⟨(neg_le_neg hdepth).trans hz.2.1, hz.2.2.trans hdepth⟩⟩
  have hcpt : IsCompact (F '' (univ ×ˢ Icc (-H₀) H₀)) :=
    ((isCompact_univ : IsCompact (univ : Set (Sphere 2))).prod isCompact_Icc).image_of_continuousOn
      (F.contMDiffOn_toFun.continuousOn.mono (hsubset.trans hsource))
  refine ⟨F, p, hcenter, hsubset.trans hsource, hcpt, hQ, ?_⟩
  exact htrap C (fun _ => C.metric 0)
    (fun _ => scaleMetric (metricScalarAt g x) hQ g) F
    (univ ×ˢ Icc (-H.collar_depth) H.collar_depth) {0}
    (⌈H.neck_precision⁻¹⌉₊) H.neck_precision cmp rfl H.neck_precision_pos.le
    (by linarith [H.neck_precision_small]) (by simp) hsource hsubset

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
