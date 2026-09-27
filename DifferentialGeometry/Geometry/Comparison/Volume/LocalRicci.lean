import DifferentialGeometry.Geometry.Comparison.BonnetMyers.RicciBound

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

def ricciBoundedBelowOn (g : SmoothRiemannianMetric I M) (s : Set M) (κ : ℝ) : Prop :=
  ∀ x ∈ s, ∀ v : TangentSpace I x,
    κ * (g.inner x v v : ℝ) ≤ ricciTensor (I := I) g x v v

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem ricciBoundedBelowOn_mono {g : SmoothRiemannianMetric I M}
    {s t : Set M} {κ : ℝ} (hst : s ⊆ t) (h : ricciBoundedBelowOn g t κ) :
    ricciBoundedBelowOn g s κ := by
  intro x hx v
  exact h x (hst hx) v

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem ricciBoundedBelowOn_of_global {g : SmoothRiemannianMetric I M}
    {s : Set M} {κ : ℝ}
    (h : BonnetMyers.RicciBoundedBelow (I := I) g κ) :
    ricciBoundedBelowOn g s κ := by
  intro x _ v
  exact h x v

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem ricciBoundedBelowOn_univ_iff {g : SmoothRiemannianMetric I M} {κ : ℝ} :
    ricciBoundedBelowOn g Set.univ κ ↔
      BonnetMyers.RicciBoundedBelow (I := I) g κ := by
  constructor
  · intro h x v
    exact h x (Set.mem_univ x) v
  · exact ricciBoundedBelowOn_of_global

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem ricciBoundedBelowOn_apply {g : SmoothRiemannianMetric I M}
    {s : Set M} {κ : ℝ} (h : ricciBoundedBelowOn g s κ)
    {x : M} (hx : x ∈ s) (v : TangentSpace I x) :
    κ * (g.inner x v v : ℝ) ≤ ricciTensor (I := I) g x v v :=
  h x hx v

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
