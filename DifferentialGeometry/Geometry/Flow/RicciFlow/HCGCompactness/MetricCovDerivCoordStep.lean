import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivLinear
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.CoordFrameStep

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Coordinate-frame component recursion for the metric covariant tower (P3 Gap B)

The `a → a+1` step of the background covariant tower, written in the coordinate
frame.  Combines the tower unfolding (`metricCovDeriv_succ` +
`metricCovDerivStep_apply` + `totalNabla0SFun_apply_section`) with the
rank-general coordinate covariant-step component formula
`nabla0SFun_eval_coordFrame` (producer 2).  This is the algebraic heart of the
single-`φ` induction: a covariant component of order `a+1` is the coordinate
directional derivative of the order-`a` component minus a fixed
`gRef`-Christoffel sum of order-`a` components.
-/

noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.Coordinates
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- General-`a` unfolding of one `metricCovDeriv` step against a smooth section
in the leading slot: it is the directional covariant derivative `nabla0SFun` of
the order-`a` tower tensor. -/
theorem metricCovDeriv_succ_apply_section
    (h gRef : SmoothRiemannianMetric I M) (a : Nat)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) (slots : Fin (a + 2) → TangentSpace I x) :
    metricCovDeriv (I := I) h gRef (a + 1) x (Fin.cons (X x) slots) =
      Tensor0SBundle.nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (a + 2) (leviCivitaConnectionOfMetric (I := I) gRef) X
        (metricCovDeriv (I := I) h gRef a) x slots := by
  rw [metricCovDeriv_succ, metricCovDerivStep_apply, totalNabla0SFun_apply_section]

/-- **Smooth-slots recursion for the metric covariant tower.**  General-`a`
analogue of `metricCovDeriv_one_eval_smooth_slots`: one tower step evaluated on a
leading section `X` and smooth section slots `V` is the directional derivative of
the order-`a` slot scalar minus the `gRef`-connection corrections.  This is the
form the section-based Gap-B convergence induction consumes (directional term →
B2, corrections → frame expansion + mulLeft + IH), with NO coordinate-frame /
germ-localisation detour. -/
theorem metricCovDeriv_succ_eval_smooth_slots
    (h gRef : SmoothRiemannianMetric I M) (a : Nat)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin (a + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    metricCovDeriv (I := I) h gRef (a + 1) x
        (Fin.cons (X x) (fun q : Fin (a + 2) => V q x)) =
      extDerivFun (I := I)
          (fun y : M => metricCovDeriv (I := I) h gRef a y
            (fun q : Fin (a + 2) => V q y)) x (X x) -
        ∑ p : Fin (a + 2),
          metricCovDeriv (I := I) h gRef a x
            (Function.update (fun q : Fin (a + 2) => V q x) p
              (((leviCivitaConnectionOfMetric (I := I) gRef)
                  (fun y : M => V p y) x) (X x))) := by
  rw [metricCovDeriv_succ_apply_section]
  exact nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (leviCivitaConnectionOfMetric (I := I) gRef) X V (metricCovDeriv (I := I) h gRef a) x

/-- **Coordinate-frame component recursion for the metric covariant tower.**
The order-`a+1` covariant component in the coordinate frame is the coordinate
directional derivative of the order-`a` component (leading slot the derivative
direction) minus the fixed `gRef`-Christoffel correction sum over the remaining
slots.  This is producer (2) (`nabla0SFun_eval_coordFrame`) specialised to
`α = metricCovDeriv h gRef a`, with the leading derivative slot realised by a
local section of the coordinate frame. -/
theorem metricCovDeriv_succ_component_coordFrame
    (h gRef : SmoothRiemannianMetric I M) (a : Nat) (x : M)
    (I0 : Fin (a + 3) → CoordinateIdx (𝕜 := Real) E) :
    component0S (I := I) (coordinateFrameAt_toBasis (I := I) x)
        (metricCovDeriv (I := I) h gRef (a + 1) x) I0 =
      coordDeriv0SAt (I := I) (coordinateFrameAt (I := I) x (I0 0)) x
          (metricCovDeriv (I := I) h gRef a) (Fin.tail I0)
        - ∑ p : Fin (a + 2), ∑ k : CoordinateIdx (𝕜 := Real) E,
            christoffelAlongInFrame (leviCivitaConnectionOfMetric (I := I) gRef)
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x
              (coordinateFrameAt (I := I) x (I0 0) x) (Fin.tail I0 p) k *
            coordComponent0SAt (I := I) (metricCovDeriv (I := I) h gRef a x)
              (Function.update (Fin.tail I0) p k) := by
  classical
  rw [component0S_apply]
  simp only [coordinateFrameAt_toBasis_apply]
  obtain ⟨sec, hsec⟩ :=
    (coordinateFrameAt_isLocalFrame (I := I) x).exists_contMDiffSection_eqOn_nhd
      (coordinateFrameSet_open (I := I) x) (coordinateFrameAt_mem (I := I) x)
  have hsecx : ∀ i : CoordinateIdx (𝕜 := Real) E,
      sec i x = coordinateFrameAt (I := I) x i x :=
    fun i => (hsec.mono fun y hy => hy i).self_of_nhds
  have hslots :
      (fun q : Fin (a + 3) => coordinateFrameAt (I := I) x (I0 q) x) =
        Fin.cons (sec (I0 0) x)
          (fun p : Fin (a + 2) => coordinateFrameAt (I := I) x (Fin.tail I0 p) x) := by
    funext q
    refine Fin.cases ?_ (fun p => ?_) q
    · rw [Fin.cons_zero, hsecx (I0 0)]
    · rw [Fin.cons_succ]; rfl
  have hcd :
      coordDeriv0SAt (I := I) (fun y : M => sec (I0 0) y) x
          (fun y : M => metricCovDeriv (I := I) h gRef a y) (Fin.tail I0) =
        coordDeriv0SAt (I := I) (coordinateFrameAt (I := I) x (I0 0)) x
          (metricCovDeriv (I := I) h gRef a) (Fin.tail I0) := by
    simp only [coordDeriv0SAt]
    rw [hsecx (I0 0)]
  rw [hslots,
    metricCovDeriv_succ_apply_section (I := I) h gRef a (sec (I0 0)) x
      (fun p : Fin (a + 2) => coordinateFrameAt (I := I) x (Fin.tail I0 p) x),
    nabla0SFun_eval_coordFrame (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
      (sec (I0 0)) (metricCovDeriv (I := I) h gRef a) x (Fin.tail I0)]
  simp only [hsecx]
  rw [hcd]

end HCGCompactness
end DifferentialGeometry
