import RicciFlower.DimensionThree.CurvatureAlgebra
import RicciFlower.Realized.CurvatureComponents
import RicciFlower.LeviCivita.Curvature

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Realized bridge for the 3D Riemann-from-Ricci formula

This file connects the checked `Fin 3` algebra in
`DimensionThree.CurvatureAlgebra` to realized pointwise curvature components.

The bridge is intentionally explicit about conventions.  RicciFlower's lowered
curvature convention is `Rm04(W,X,Y,Z) = g(W, R(X,Y)Z)`, while the algebraic
theorem uses the standard component convention
`R i j k l = g(R(e_i,e_j)e_k,e_l)`.  The adapter below performs the slot
permutation `R i j k l := Rm04(e_l,e_i,e_j,e_k)`.
-/

noncomputable section

namespace RicciFlower
namespace DimensionThree

open Realized
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {x : M}

/-- Pointwise orthonormality for a `Fin 3` tangent basis. -/
def OrthonormalBasisAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) : Prop :=
  forall i j : Fin 3, g.inner x (basis i) (basis j) = delta3 i j

/-- Standard algebraic curvature components obtained from RicciFlower's
lowered curvature convention by the slot permutation
`R i j k l = Rm04(e_l,e_i,e_j,e_k)`. -/
def standardRmCompAt
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (i j k l : Fin 3) : Real :=
  rm04CompAt (I := I) basis Rm04 l i j k

@[simp]
theorem standardRmCompAt_apply
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (i j k l : Fin 3) :
    standardRmCompAt basis Rm04 i j k l =
      rm04CompAt (I := I) basis Rm04 l i j k := rfl

/-- Lemma 14.2 as a pointwise `Rm04` component formula with the Ricci and
scalar terms taken to be the canonical traces of the same standard curvature
component array.

This is the assumption-free trace-data form of the realized bridge: the only
geometric input is the algebraic curvature symmetry package for the adapted
components `standardRmCompAt basis Rm04`. -/
theorem rm04Comp_displayedRiemannFromRicci3D_at_of_curvature_symmetries
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    {Rm04 : Tensor04At (I := I) (M := M) x}
    (h : AlgebraicCurvatureSymmetries3 (standardRmCompAt basis Rm04)) :
    forall i j k l : Fin 3,
      rm04CompAt (I := I) basis Rm04 k i j l =
        stdRicci3 (standardRmCompAt basis Rm04) i l * delta3 j k
          - stdRicci3 (standardRmCompAt basis Rm04) j l * delta3 i k
          - stdRicci3 (standardRmCompAt basis Rm04) i k * delta3 j l
          + stdRicci3 (standardRmCompAt basis Rm04) j k * delta3 i l
          - (1 / 2 : Real) * stdScalar3 (standardRmCompAt basis Rm04) *
              (delta3 i l * delta3 j k - delta3 j l * delta3 i k) := by
  intro i j k l
  have hformula :=
    displayedRiemannFromRicci3D_of_algebraic_curvature_symmetries
      h i j k l
  simpa [displayedRiemannFromRicciRhs3, standardRmCompAt_apply] using hformula

/-- Local-frame wrapper for
`rm04Comp_displayedRiemannFromRicci3D_at_of_curvature_symmetries`. -/
theorem rm04Comp_displayedRiemannFromRicci3D_frame_of_curvature_symmetries
    {Rm04 : Tensor04Section (I := I) (M := M)}
    {u : Set M}
    {frame : Fin 3 -> (x : M) -> TangentSpace I x}
    (hframe : IsLocalFrameOn I E ∞ frame u)
    {x : M} (hx : x ∈ u)
    (h : AlgebraicCurvatureSymmetries3
      (standardRmCompAt (I := I) (M := M) (hframe.toBasisAt hx) (Rm04 x))) :
    forall i j k l : Fin 3,
      rm04CompAt (I := I) (hframe.toBasisAt hx) (Rm04 x) k i j l =
        stdRicci3 (standardRmCompAt (I := I) (M := M)
          (hframe.toBasisAt hx) (Rm04 x)) i l * delta3 j k
          - stdRicci3 (standardRmCompAt (I := I) (M := M)
            (hframe.toBasisAt hx) (Rm04 x)) j l * delta3 i k
          - stdRicci3 (standardRmCompAt (I := I) (M := M)
            (hframe.toBasisAt hx) (Rm04 x)) i k * delta3 j l
          + stdRicci3 (standardRmCompAt (I := I) (M := M)
            (hframe.toBasisAt hx) (Rm04 x)) j k * delta3 i l
          - (1 / 2 : Real) * stdScalar3 (standardRmCompAt (I := I) (M := M)
            (hframe.toBasisAt hx) (Rm04 x)) *
              (delta3 i l * delta3 j k - delta3 j l * delta3 i k) :=
  rm04Comp_displayedRiemannFromRicci3D_at_of_curvature_symmetries
    (I := I) h

/-- Levi-Civita lowered curvature supplies the three standard algebraic
curvature symmetries needed by the dimension-three algebra file. -/
theorem algebraicCurvatureSymmetries3_standardRmCompAt_of_leviCivita_realizes
    [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M] [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) (1 : WithTop ℕ∞))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRm04 : Rm04RealizesConnection (I := I) g
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) Rm04)
    {x : M} (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) :
    AlgebraicCurvatureSymmetries3 (standardRmCompAt (I := I) basis (Rm04 x)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j k l
    simpa [standardRmCompAt_apply] using
      (LeviCivita.rm04InputSkewAt_of_leviCivita_realizes
        (I := I) g Rm04 hRm04 (basis l) (basis i) (basis j) (basis k))
  · intro i j k l
    simpa [standardRmCompAt_apply] using
      (LeviCivita.rm04OutputSkewAt_of_leviCivita_realizes
        (I := I) g hcov Rm04 hRm04 (basis k) (basis i) (basis j) (basis l))
  · intro i j k l
    simpa [standardRmCompAt_apply] using
      (LeviCivita.rm04PairSymmAt_of_leviCivita_realizes
        (I := I) g hcov Rm04 hRm04 (basis j) (basis k) (basis l) (basis i))

/-- Lemma 14.2 for a Levi-Civita lowered curvature realization, with Ricci and
scalar terms expressed as canonical traces of the same curvature array. -/
theorem rm04Comp_displayedRiemannFromRicci3D_at_of_leviCivita_realizes
    [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M] [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) (1 : WithTop ℕ∞))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRm04 : Rm04RealizesConnection (I := I) g
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) Rm04)
    {x : M} (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) :
    forall i j k l : Fin 3,
      rm04CompAt (I := I) basis (Rm04 x) k i j l =
        stdRicci3 (standardRmCompAt (I := I) basis (Rm04 x)) i l * delta3 j k
          - stdRicci3 (standardRmCompAt (I := I) basis (Rm04 x)) j l * delta3 i k
          - stdRicci3 (standardRmCompAt (I := I) basis (Rm04 x)) i k * delta3 j l
          + stdRicci3 (standardRmCompAt (I := I) basis (Rm04 x)) j k * delta3 i l
          - (1 / 2 : Real) * stdScalar3 (standardRmCompAt (I := I) basis (Rm04 x)) *
              (delta3 i l * delta3 j k - delta3 j l * delta3 i k) :=
  rm04Comp_displayedRiemannFromRicci3D_at_of_curvature_symmetries (I := I)
    (algebraicCurvatureSymmetries3_standardRmCompAt_of_leviCivita_realizes
      (I := I) g hcov Rm04 hRm04 basis)

/-- Pointwise data needed to feed the realized 3D bridge.

The trace equalities are deliberately stated for the standard slot adapter,
not inferred from the existing realized Ricci trace interfaces.  This keeps the
bridge convention-auditable. -/
structure RiemannFromRicci3DTraceDataAt
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02At (I := I) (M := M) x)
    (scalar : Real)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) : Prop where
  orthonormal : OrthonormalBasisAt g x basis
  curvature_symmetries :
    AlgebraicCurvatureSymmetries3 (standardRmCompAt basis Rm04)
  ricci_trace : forall i j : Fin 3,
    ricciCompAt (I := I) basis Ric i j =
      stdRicci3 (standardRmCompAt basis Rm04) i j
  scalar_trace :
    scalar = stdScalar3 (standardRmCompAt basis Rm04)

/-- Lemma 14.2 as a realized pointwise `Rm04` component formula in an
orthonormal `Fin 3` basis.

The left side is `rm04CompAt basis Rm04 k i j l`, which is the RicciFlower
component corresponding to the displayed convention after the adapter
`R i j l k = Rm04(e_k,e_i,e_j,e_l)`. -/
theorem rm04Comp_displayedRiemannFromRicci3D_at
    {g : SmoothRiemannianMetric I M}
    {Ric : Tensor02At (I := I) (M := M) x}
    {scalar : Real}
    {Rm04 : Tensor04At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (h : RiemannFromRicci3DTraceDataAt g Ric scalar Rm04 basis) :
    forall i j k l : Fin 3,
      rm04CompAt (I := I) basis Rm04 k i j l =
        ricciCompAt (I := I) basis Ric i l * delta3 j k
          - ricciCompAt (I := I) basis Ric j l * delta3 i k
          - ricciCompAt (I := I) basis Ric i k * delta3 j l
          + ricciCompAt (I := I) basis Ric j k * delta3 i l
          - (1 / 2 : Real) * scalar *
              (delta3 i l * delta3 j k - delta3 j l * delta3 i k) := by
  intro i j k l
  have hformula :=
    displayedRiemannFromRicci3D_of_algebraic_curvature_symmetries
      h.curvature_symmetries i j k l
  simp only [standardRmCompAt_apply] at hformula
  rw [hformula]
  unfold displayedRiemannFromRicciRhs3
  rw [← h.ricci_trace i l, ← h.ricci_trace j l, ← h.ricci_trace i k,
    ← h.ricci_trace j k, ← h.scalar_trace]

/-- Local-frame wrapper for the pointwise bridge. -/
theorem rm04Comp_displayedRiemannFromRicci3D_frame
    {g : SmoothRiemannianMetric I M}
    {Ric : Tensor02Section (I := I) (M := M)}
    {scalar : M -> Real}
    {Rm04 : Tensor04Section (I := I) (M := M)}
    {u : Set M}
    {frame : Fin 3 -> (x : M) -> TangentSpace I x}
    (hframe : IsLocalFrameOn I E ∞ frame u)
    {x : M} (hx : x ∈ u)
    (h : RiemannFromRicci3DTraceDataAt g (Ric x) (scalar x)
      (Rm04 x) (hframe.toBasisAt hx)) :
    forall i j k l : Fin 3,
      rm04CompAt (I := I) (hframe.toBasisAt hx) (Rm04 x) k i j l =
        ricciCompAt (I := I) (hframe.toBasisAt hx) (Ric x) i l * delta3 j k
          - ricciCompAt (I := I) (hframe.toBasisAt hx) (Ric x) j l * delta3 i k
          - ricciCompAt (I := I) (hframe.toBasisAt hx) (Ric x) i k * delta3 j l
          + ricciCompAt (I := I) (hframe.toBasisAt hx) (Ric x) j k * delta3 i l
          - (1 / 2 : Real) * scalar x *
              (delta3 i l * delta3 j k - delta3 j l * delta3 i k) :=
  rm04Comp_displayedRiemannFromRicci3D_at (I := I) h

end DimensionThree
end RicciFlower
