import RicciFlower.GlobalGeometry.Myers.HopfRinow
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Covering.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Fundamental-group finiteness interface for Myers

This file records the topological endpoint of the Bonnet-Myers package:
positive Ricci lower bound implies finite fundamental group.  The native
checked core is deliberately small: finiteness transfers across an equivalence
between a universal-cover fiber and the fundamental group.

The missing construction is the global covering/Riemannian package: universal
cover as a smooth Riemannian manifold, lifted metric and Ricci bound,
completeness of the lifted metric, compactness of the cover by Myers, finiteness
of a covering fiber, and the fiber/fundamental-group monodromy equivalence.
-/

noncomputable section

namespace RicciFlower
namespace GlobalGeometry
namespace Myers

open Bundle
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

universe u

/-- Minimal universal-cover package needed by the fundamental-group finiteness
argument.

The equivalence field is intentionally part of the data: mathlib has covering
maps and fundamental groups, but this project does not yet have the universal
cover construction with the monodromy/fiber identification in the Riemannian
manifold layer. -/
structure UniversalCoverData (M : Type u) [TopologicalSpace M] (x0 : M) where
  Cover : Type u
  [coverTop : TopologicalSpace Cover]
  proj : Cover -> M
  covering : IsCoveringMap proj
  fiberEquivFundamentalGroup :
    {y : Cover // proj y = x0} ≃ FundamentalGroup M x0

attribute [instance] UniversalCoverData.coverTop

/-- Finiteness transfers from the universal-cover fiber to the fundamental
group through the stored monodromy equivalence. -/
theorem finite_fundamentalGroup_of_finite_cover_fiber
    {M : Type*} [TopologicalSpace M] {x0 : M}
    (D : UniversalCoverData M x0)
    (hD : Finite {y : D.Cover // D.proj y = x0}) :
    Finite (FundamentalGroup M x0) := by
  letI : Finite {y : D.Cover // D.proj y = x0} := hD
  exact Finite.of_equiv _ D.fiberEquivFundamentalGroup

/-- Global universal-cover/Riemannian frontier needed for Bonnet-Myers
fundamental-group finiteness.

Mathematically, the universal cover carries the pulled-back metric and Ricci
lower bound, remains complete, is compact by Myers, and has finite fiber over
the basepoint; the fiber is equivalent to `pi_1(M, x0)`. -/
theorem exists_universalCover_finite_fiber_of_ricci_lower_bound
    [hb : RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [CompleteSpace M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (Ric : Curvature.Tensor02Section (I := I) (M := M))
    {n : Nat} {k : Real}
    (_hdim : Module.finrank Real E = n)
    (_hk : 0 < k)
    (_hRic :
      RicciLowerBound (I := I) (M := M) g Ric (((n - 1 : Nat) : Real) * k))
    (_hg : ∀ (x : M) (v w : TangentSpace I x), (inner ℝ v w : ℝ) = g.inner x v w)
    (x0 : M) :
    ∃ D : UniversalCoverData M x0, Finite {y : D.Cover // D.proj y = x0} := by
  sorry

/-- Bonnet-Myers fundamental-group finiteness, routed through the universal
cover frontier and the checked finite-transfer lemma. -/
theorem finite_fundamentalGroup_of_ricci_lower_bound
    [hb : RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [CompleteSpace M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (Ric : Curvature.Tensor02Section (I := I) (M := M))
    {n : Nat} {k : Real}
    (hdim : Module.finrank Real E = n)
    (hk : 0 < k)
    (hRic :
      RicciLowerBound (I := I) (M := M) g Ric (((n - 1 : Nat) : Real) * k))
    (hg : ∀ (x : M) (v w : TangentSpace I x), (inner ℝ v w : ℝ) = g.inner x v w)
    (x0 : M) :
    Finite (FundamentalGroup M x0) := by
  obtain ⟨D, hD⟩ :=
    exists_universalCover_finite_fiber_of_ricci_lower_bound
      (I := I) (M := M) g Ric hdim hk hRic hg x0
  exact finite_fundamentalGroup_of_finite_cover_fiber D hD

end Myers
end GlobalGeometry
end RicciFlower
