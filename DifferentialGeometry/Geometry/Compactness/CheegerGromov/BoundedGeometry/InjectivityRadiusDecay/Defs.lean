import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.InjectivityRadius
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Metric.Instances

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff Topology ENNReal Bundle

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

structure InjectivityRadiusDecay
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  baseInj : BaseInjBound (I := I) X
  dist : PointedRiemannianSeq.Distance (I := I) X
  a : Real
  C : Real
  a_pos : 0 < a
  C_nonneg : 0 <= C
  decay :
    forall k : Nat, forall x : (X.obj k).M,
      HasInjRadiusAt (I := I) (X.obj k) x
        (a * (min baseInj.ρ 1) ^ Module.finrank Real E *
          Real.exp (-C * dist k x (X.obj k).basepoint))

namespace InjectivityRadiusDecay

def subseq {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjectivityRadiusDecay (I := I) X) (f : Nat -> Nat) :
    InjectivityRadiusDecay (I := I) (X.subseq f) where
  baseInj := hd.baseInj.subseq f
  dist := fun k x y => hd.dist (f k) x y
  a := hd.a
  C := hd.C
  a_pos := hd.a_pos
  C_nonneg := hd.C_nonneg
  decay := by
    intro k x
    change HasInjRadiusAt (I := I) (X.obj (f k)) x
      (hd.a * (min hd.baseInj.ρ 1) ^ Module.finrank Real E *
        Real.exp (-hd.C * hd.dist (f k) x (X.obj (f k)).basepoint))
    exact hd.decay (f k) x

noncomputable def mu {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjectivityRadiusDecay (I := I) X) (r : Real) : Real :=
  hd.a * (min hd.baseInj.ρ 1) ^ (Module.finrank Real E) * Real.exp (-hd.C * r)

omit [CompleteSpace E] in
theorem mu_pos {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjectivityRadiusDecay (I := I) X) (r : Real) : 0 < hd.mu r :=
  mul_pos (mul_pos hd.a_pos (pow_pos (lt_min hd.baseInj.pos one_pos) _)) (Real.exp_pos _)

omit [CompleteSpace E] in
theorem mu_nonneg {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjectivityRadiusDecay (I := I) X) (r : Real) : 0 ≤ hd.mu r :=
  (hd.mu_pos r).le

omit [CompleteSpace E] in
theorem mu_antitone {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjectivityRadiusDecay (I := I) X) : Antitone hd.mu := by
  intro r₁ r₂ h
  have hK : 0 ≤ hd.a * (min hd.baseInj.ρ 1) ^ (Module.finrank Real E) :=
    (mul_pos hd.a_pos (pow_pos (lt_min hd.baseInj.pos one_pos) _)).le
  have hexp : Real.exp (-hd.C * r₂) ≤ Real.exp (-hd.C * r₁) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left h hd.C_nonneg])
  exact mul_le_mul_of_nonneg_left hexp hK

structure RealizesDistance {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjectivityRadiusDecay (I := I) X) : Prop where
  dist_nonneg : ∀ (k : Nat) (x y : (X.obj k).M), 0 ≤ hd.dist k x y
  edist_eq : ∀ (k : Nat) (x y : (X.obj k).M),
    (letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
     edist x y) = ENNReal.ofReal (hd.dist k x y)

namespace RealizesDistance

omit [CompleteSpace E] in
theorem subseq {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (hre : hd.RealizesDistance) (f : Nat → Nat) :
    (hd.subseq f).RealizesDistance := by
  refine ⟨?_, ?_⟩
  · intro k x y
    exact hre.dist_nonneg (f k) x y
  · intro k x y
    with_unfolding_all exact hre.edist_eq (f k) x y

end RealizesDistance

end InjectivityRadiusDecay

end HCGCompactness
end DifferentialGeometry
