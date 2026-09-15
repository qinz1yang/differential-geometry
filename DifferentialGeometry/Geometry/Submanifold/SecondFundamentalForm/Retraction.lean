import DifferentialGeometry.Geometry.Metric.Retraction
import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.Composition
import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.Product

noncomputable section

open Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem hasVanishingSecondFundamentalFormAlongCurves_retractionMetric
    (g : SmoothRiemannianMetric I M)
    {e : M → F} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {r : F → M} {U : TopologicalSpace.Opens F}
    (hr : ContMDiffOn 𝓘(ℝ, F) I ∞ r U)
    (hEU : range e ⊆ U) (hleft : ∀ p, r (e p) = p) :
    hasVanishingSecondFundamentalFormAlongCurves g (retractionMetric g he hr)
      (fun p : M => (⟨e p, hEU (mem_range_self p)⟩ : U)) := by
  let f : M → U := fun p => ⟨e p, hEU (mem_range_self p)⟩
  let G : U → M × F := fun x => retractionGraph e r x
  have hf : ContMDiff I 𝓘(ℝ, F) ∞ f :=
    (ContMDiff.subtypeVal_comp_iff U f).mp he
  have hG := contMDiff_retractionGraph he hr
  have hcomp : G ∘ f = (fun p : M => (p, (0 : F))) := by
    funext p
    change (r (e p), e p - e (r (e p))) = (p, 0)
    rw [hleft p, sub_self]
  apply hasVanishingSecondFundamentalFormAlongCurves_of_comp_of_inner_map
    (g₃ := g.prod (euclideanMetric (E := F))) hG (fun _ _ _ => rfl) hf
  rw [hcomp]
  exact hasVanishingSecondFundamentalFormAlongCurves_prod_left g euclideanMetric 0

end DifferentialGeometry.Geometry.Riemannian
