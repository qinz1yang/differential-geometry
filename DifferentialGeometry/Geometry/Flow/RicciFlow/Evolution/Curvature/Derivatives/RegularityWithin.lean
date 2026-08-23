import DifferentialGeometry.Bundle.PartialMfderiv.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Components

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

theorem iterRmComp_joint
    {Idx : Type*} [Fintype Idx]
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {J : Set Real} {u : Set M}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {t : Real} {x : M} (ht : t ∈ J) (hx : x ∈ u)
    (chr : Real -> M -> Idx -> Idx -> Idx -> Real)
    (base : Real -> M -> (Fin 4 -> Idx) -> Real)
    (hchr : ∀ i j k : Idx,
      ContMDiffWithinAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) (∞ : WithTop ℕ∞)
        (fun q : Real × M => chr q.1 q.2 i j k) (J ×ˢ u) (t, x))
    (hbase : ∀ m : Fin 4 -> Idx,
      ContMDiffWithinAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) (∞ : WithTop ℕ∞)
        (fun q : Real × M => base q.1 q.2 m) (J ×ˢ u) (t, x)) :
    ∀ k : Nat, ∀ m : Fin (4 + k) -> Idx,
      ContMDiffWithinAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) (∞ : WithTop ℕ∞)
        (fun q : Real × M =>
          iteratedRmComp (I := I) frame chr base k q.1 q.2 m)
        (J ×ˢ u) (t, x) := by
  classical
  intro k
  induction k with
  | zero =>
      intro m
      simpa [iteratedRmComp_zero] using hbase m
  | succ k ih =>
      intro n
      have hext := prodExtDeriv_joint (I := I) hu ht hx
        (hF := ih (Fin.tail n))
        (hX := hframe.contMDiffAt hu hx (n 0))
      have hsum :
          ContMDiffWithinAt ((modelWithCornersSelf Real Real).prod I)
            (modelWithCornersSelf Real Real) (∞ : WithTop ℕ∞)
            (fun q : Real × M =>
              ∑ s : Fin (4 + k), ∑ p : Idx,
                chr q.1 q.2 (n 0) (Fin.tail n s) p *
                  iteratedRmComp (I := I) frame chr base k q.1 q.2
                    (Function.update (Fin.tail n) s p))
            (J ×ˢ u) (t, x) := by
        refine ContMDiffWithinAt.sum fun s _ =>
          ContMDiffWithinAt.sum fun p _ => ?_
        exact (hchr (n 0) (Fin.tail n s) p).mul
          (ih (Function.update (Fin.tail n) s p))
      have hstep := hext.sub hsum
      simpa [iteratedRmComp_succ, covDerivStepComp, frameExtData] using hstep

end DifferentialGeometry.PDE.RicciFlow
