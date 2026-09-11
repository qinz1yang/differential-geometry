import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

section normedSpaceCompatibility

attribute [-instance] InnerProductSpace.toNormedSpace

open Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

def lCost
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (x y : M) (tau : Real) : Real :=
  sInf {r : Real | ∃ alpha : Real → M,
    ContMDiff (modelWithCornersSelf Real Real) I 1 alpha ∧
      alpha 0 = x ∧ alpha (Real.sqrt tau) = y ∧
      lLength S T (squareRootReparametrization alpha) 0 tau = r}

end normedSpaceCompatibility

section

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]
  {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

def lRegularizedCostC1
    (S : SolutionOn (I := I) (M := M) D) (T a b : ℝ) (x y : M) : ℝ :=
  sInf {r : ℝ | ∃ alpha : ℝ → M,
    ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha ∧
      alpha a = x ∧ alpha b = y ∧ lRegularizedAction S T alpha a b = r}

theorem lRegularizedCostC1_le_bdd
    (S : SolutionOn (I := I) (M := M) D) (T a b : ℝ) (x y : M)
    (hbdd : BddBelow {r : ℝ | ∃ alpha : ℝ → M,
      ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha ∧
        alpha a = x ∧ alpha b = y ∧ lRegularizedAction S T alpha a b = r})
    (alpha : ℝ → M)
    (halpha : ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha)
    (hxa : alpha a = x) (hyb : alpha b = y) :
    lRegularizedCostC1 S T a b x y ≤ lRegularizedAction S T alpha a b := by
  unfold lRegularizedCostC1
  exact csInf_le hbdd ⟨alpha, halpha, hxa, hyb, rfl⟩

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
