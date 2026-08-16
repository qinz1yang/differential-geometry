import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.SemilinearConvex

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis.Parabolic

open Bundle Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology RealInnerProductSpace

universe u uE uH uF

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]
variable {F : Type uF} [NormedAddCommGroup F] [InnerProductSpace Real F] [CompleteSpace F]
variable {V : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
variable [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]

def bundleInnerScalarization
    (u : Real → (x : M) → V x) (ν : (x : M) → V x) : Real → M → Real :=
  fun t x => inner ℝ (u t x) (ν x)

def IsBundleConvexSupportFamily
    (C : Real → (x : M) → Set (V x)) (support : Real → (x : M) → V x → Real) : Prop :=
  ∀ t x p, p ∈ C t x ↔
    ∀ ν : Cₛ^∞⟮I; F, V⟯, inner ℝ p (ν x) ≤ support t x (ν x)

structure IsBundleHeatReactionOn
    (D : RealTimeInterval) (G : MetricConnectionFamily (I := I) (M := M) Real)
    (source : Real → (x : M) → V x → V x → Real)
    (u : Real → (x : M) → V x) : Prop where
  scalarSliceSmooth :
    ∀ ν : Cₛ^∞⟮I; F, V⟯, ∀ t : Real, t ∈ D.carrier →
      ContMDiff I 𝓘(Real, Real) ∞ (bundleInnerScalarization u ν t)
  equation :
    ∀ ν : Cₛ^∞⟮I; F, V⟯, ∀ t : Real, t ∈ D.regular → ∀ x : M,
      HasDerivAt (fun s : Real => bundleInnerScalarization u ν s x)
        (laplacianAt (I := I) G t (bundleInnerScalarization u ν t) x +
          source t x (u t x) (ν x)) t

end DifferentialGeometry.Analysis.Parabolic
