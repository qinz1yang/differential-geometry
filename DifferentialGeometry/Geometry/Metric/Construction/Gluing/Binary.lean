import DifferentialGeometry.Geometry.Metric.Construction.Gluing.Family
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype
import Mathlib.Geometry.Manifold.VectorField.Pullback
import DifferentialGeometry.Bundle.ContinuousLinearMapSection.Basic

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Geometry.Metric
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

def glueMetric (U V : TopologicalSpace.Opens M)
    (gU : SmoothRiemannianMetric I U) (gV : SmoothRiemannianMetric I V)
    (heq : ∀ (x : M) (hxU : x ∈ U) (hxV : x ∈ V) (v w : TangentSpace I x),
      gU.inner ⟨x, hxU⟩ v w = gV.inner ⟨x, hxV⟩ v w) :
    SmoothRiemannianMetric I ↥(U ⊔ V) := by
  let O : Bool → TopologicalSpace.Opens M := fun b => cond b U V
  let g : ∀ b, SmoothRiemannianMetric I (O b) := fun b => by
    cases b
    · exact gV
    · exact gU
  exact glueMetricFamilyOn O g (U ⊔ V)
    (by
      intro b
      cases b
      · exact le_sup_right
      · exact le_sup_left)
    (by
      intro x
      rcases x.property with hx | hx
      · exact ⟨true, hx⟩
      · exact ⟨false, hx⟩)
    (by
      intro b c x hb hc v w
      cases b <;> cases c
      · rfl
      · exact (heq x hc hb v w).symm
      · exact heq x hb hc v w
      · rfl)

theorem glueMetric_inner_left (U V : TopologicalSpace.Opens M)
    (gU : SmoothRiemannianMetric I U) (gV : SmoothRiemannianMetric I V)
    (heq : ∀ (x : M) (hxU : x ∈ U) (hxV : x ∈ V) (v w : TangentSpace I x),
      gU.inner ⟨x, hxU⟩ v w = gV.inner ⟨x, hxV⟩ v w)
    (x : U) (v w : TangentSpace I x) :
    (glueMetric U V gU gV heq).inner (TopologicalSpace.Opens.inclusion le_sup_left x) v w =
      gU.inner x v w := by
  unfold glueMetric
  exact glueMetricFamilyOn_inner (fun b => cond b U V) _ (U ⊔ V) _ _ _ true x v w

theorem glueMetric_inner_right (U V : TopologicalSpace.Opens M)
    (gU : SmoothRiemannianMetric I U) (gV : SmoothRiemannianMetric I V)
    (heq : ∀ (x : M) (hxU : x ∈ U) (hxV : x ∈ V) (v w : TangentSpace I x),
      gU.inner ⟨x, hxU⟩ v w = gV.inner ⟨x, hxV⟩ v w)
    (x : V) (v w : TangentSpace I x) :
    (glueMetric U V gU gV heq).inner (TopologicalSpace.Opens.inclusion le_sup_right x) v w =
      gV.inner x v w := by
  unfold glueMetric
  exact glueMetricFamilyOn_inner (fun b => cond b U V) _ (U ⊔ V) _ _ _ false x v w

theorem glueMetric_restrict_left (U V : TopologicalSpace.Opens M)
    (gU : SmoothRiemannianMetric I U) (gV : SmoothRiemannianMetric I V)
    (heq : ∀ (x : M) (hxU : x ∈ U) (hxV : x ∈ V) (v w : TangentSpace I x),
      gU.inner ⟨x, hxU⟩ v w = gV.inner ⟨x, hxV⟩ v w) :
    (glueMetric U V gU gV heq).restrictOpenOfSubset le_sup_left = gU := by
  apply SmoothRiemannianMetric.ext_inner
  exact glueMetric_inner_left U V gU gV heq

theorem glueMetric_restrict_right (U V : TopologicalSpace.Opens M)
    (gU : SmoothRiemannianMetric I U) (gV : SmoothRiemannianMetric I V)
    (heq : ∀ (x : M) (hxU : x ∈ U) (hxV : x ∈ V) (v w : TangentSpace I x),
      gU.inner ⟨x, hxU⟩ v w = gV.inner ⟨x, hxV⟩ v w) :
    (glueMetric U V gU gV heq).restrictOpenOfSubset le_sup_right = gV := by
  apply SmoothRiemannianMetric.ext_inner
  exact glueMetric_inner_right U V gU gV heq

end DifferentialGeometry.Geometry.Metric
