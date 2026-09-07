import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Operator.Scalar.Calculus

open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Operator

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (∞ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]

def IsLaplacianLEBarrierAt
    (g : SmoothRiemannianMetric I M) (u : M → Real) (c : Real) (x : M) : Prop :=
  ∀ ε : Real, 0 < ε →
    ∃ φ : M → Real,
      ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞) φ x ∧
      φ x = u x ∧
      (∀ᶠ y in 𝓝 x, u y ≤ φ y) ∧
      laplacian (I := I) (LeviCivita (I := I) g) g φ x ≤ c + ε

def IsLaplacianLEBarrierOn
    (g : SmoothRiemannianMetric I M) (u b : M → Real) (s : Set M) : Prop :=
  ∀ x ∈ s, IsLaplacianLEBarrierAt (I := I) g u (b x) x

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
theorem IsLaplacianLEBarrierAt.of_upperSupport
    (g : SmoothRiemannianMetric I M)
    {u φ : M → Real} {c : Real} {x : M}
    (hφ : ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞) φ x)
    (hφx : φ x = u x)
    (huφ : ∀ᶠ y in 𝓝 x, u y ≤ φ y)
    (hlap : laplacian (I := I) (LeviCivita (I := I) g) g φ x ≤ c) :
    IsLaplacianLEBarrierAt (I := I) g u c x := by
  intro ε hε
  exact ⟨φ, hφ, hφx, huφ,
    le_trans hlap (le_add_of_nonneg_right (le_of_lt hε))⟩

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
theorem IsLaplacianLEBarrierAt.mono
    {g : SmoothRiemannianMetric I M} {u : M → Real}
    {c d : Real} {x : M}
    (h : IsLaplacianLEBarrierAt (I := I) g u c x) (hcd : c ≤ d) :
    IsLaplacianLEBarrierAt (I := I) g u d x := by
  intro ε hε
  obtain ⟨φ, hφ, hφx, huφ, hlap⟩ := h ε hε
  exact ⟨φ, hφ, hφx, huφ, le_trans hlap (add_le_add_left hcd ε)⟩

end DifferentialGeometry.Geometry.Operator
