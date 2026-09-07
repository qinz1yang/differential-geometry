import DifferentialGeometry.Geometry.Comparison.MinimizingRay

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ENNReal Manifold

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

section IsMinimizingLineDef

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
def IsMinimizingLine
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) : Prop :=
  IsGeodesic (I := I) g γ ∧
    ∀ ⦃s t : ℝ⦄, s ≤ t →
      riemannianEDist I (γ s) (γ t) = ENNReal.ofReal (t - s)

end IsMinimizingLineDef

namespace IsMinimizingLine

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem isGeodesic
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsMinimizingLine (I := I) g γ) :
    IsGeodesic (I := I) g γ :=
  hγ.1

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem edist_eq
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsMinimizingLine (I := I) g γ)
    ⦃s t : ℝ⦄ (hst : s ≤ t) :
    riemannianEDist I (γ s) (γ t) = ENNReal.ofReal (t - s) :=
  hγ.2 hst

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [T2Space (TangentBundle I M)]
    [SigmaCompactSpace M] in
theorem positive_ray
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsMinimizingLine (I := I) g γ) :
    IsMinimizingRay (I := I) g (γ 0) γ := by
  refine ⟨rfl, hγ.isGeodesic.isGeodesicOn (Set.Ici 0), ?_⟩
  intro s t _ hst
  exact hγ.edist_eq hst

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [T2Space (TangentBundle I M)]
    [SigmaCompactSpace M] in
theorem negative_ray
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsMinimizingLine (I := I) g γ) :
    IsMinimizingRay (I := I) g (γ 0) (fun t : ℝ ↦ γ (-t)) := by
  refine ⟨by simp, (isGeodesic_comp_neg hγ.isGeodesic).isGeodesicOn (Set.Ici 0), ?_⟩
  intro s t _ hst
  have hdist := hγ.edist_eq (neg_le_neg hst)
  simpa only [Manifold.riemannianEDist_comm, neg_sub_neg] using hdist

end IsMinimizingLine

end Riemannian
end Geometry
end DifferentialGeometry
