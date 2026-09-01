import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Defs

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold

variable {E : Type uE} [NormedAddCommGroup E]
variable [NormedSpace Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

structure BallMultiplicityBound
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  dist : PointedRiemannianSeq.Distance (I := I) X
  r0 : Real
  r0_pos : 0 < r0
  multiplicity : Real → Nat
  card_le :
    ∀ (m : Real) (k : Nat) {α : Type u}, [Fintype α] → [DecidableEq α] →
      ∀ centers : α → (X.obj k).M, ∀ r : Real, 0 < r → m * r ≤ r0 →
        (∀ i j : α, i ≠ j → r ≤ dist k (centers i) (centers j)) →
        ∀ z : (X.obj k).M, ∀ J : Finset α,
          (∀ j : α, j ∈ J → dist k (centers j) z ≤ m * r) →
          J.card ≤ multiplicity m

namespace BallMultiplicityBound

def subseq {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : BallMultiplicityBound (I := I) X) (f : Nat → Nat) :
    BallMultiplicityBound (I := I) (X.subseq f) where
  dist := fun k x y => h.dist (f k) x y
  r0 := h.r0
  r0_pos := h.r0_pos
  multiplicity := h.multiplicity
  card_le := by
    intro m k α _ _ centers r hr hcap hsep z J hJz
    exact h.card_le m (f k) centers r hr hcap hsep z J hJz

end BallMultiplicityBound

end HCGCompactness
end DifferentialGeometry
