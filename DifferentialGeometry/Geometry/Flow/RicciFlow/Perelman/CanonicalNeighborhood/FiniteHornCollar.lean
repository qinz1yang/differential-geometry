import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CollarNoReturn
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

theorem exists_finiteHorn_collar_shortening_depth :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ∃ i, ∀ x ∈ H.subend i,
      ∃ (F : PartialDiffeomorph IC I3 Cylinder W ∞) (p : Sphere 2),
        F (p, 0) = x ∧ univ ×ˢ Icc (-H₀) H₀ ⊆ F.source ∧
        ∃ hQ : 0 < metricScalarAt g x, ∀ gamma : ℝ → Cylinder,
          ContMDiffOn 𝓘(ℝ, ℝ) IC 1 gamma (Icc (0 : ℝ) 1) →
          (∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ univ ×ˢ Icc (-H₀) H₀) →
          (gamma 0).2 = 0 → (gamma 1).2 = 0 →
          (∃ s ∈ Icc (0 : ℝ) 1, H₀ ≤ |(gamma s).2|) →
          ∃ shortcut : ℝ → W,
            shortcut 0 = F (gamma 0) ∧ shortcut 1 = F (gamma 1) ∧
            ContMDiffOn 𝓘(ℝ, ℝ) I3 1 shortcut (Icc (0 : ℝ) 1) ∧
            (∀ s ∈ Icc (0 : ℝ) 1, shortcut s ∈ F '' (univ ×ˢ ({0} : Set ℝ))) ∧
            metricPathELength (scaleMetric (metricScalarAt g x) hQ g) shortcut 0 1 +
                ENNReal.ofReal (1 / 2 : ℝ) <
              metricPathELength (scaleMetric (metricScalarAt g x) hQ g)
                ((F : Cylinder → W) ∘ gamma) 0 1 := by
  obtain ⟨H₀, hH₀, hshortening⟩ := exists_fixed_collar_shortening_constants (M := W)
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
  refine ⟨F, p, hcenter, hsubset.trans hsource, hQ, ?_⟩
  intro gamma hgamma hU hstart hend hvisit
  exact hshortening C (fun _ => C.metric 0)
    (fun _ => scaleMetric (metricScalarAt g x) hQ g) F
    (univ ×ˢ Icc (-H.collar_depth) H.collar_depth) {0}
    (⌈H.neck_precision⁻¹⌉₊) H.neck_precision cmp rfl H.neck_precision_pos.le
    (by linarith [H.neck_precision_small]) (by simp) hsource
    (fun y => ⟨mem_univ y, by constructor <;> linarith [H.collar_depth_pos]⟩)
    gamma hgamma (fun s hs => hsubset (hU s hs)) hstart hend hvisit

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
