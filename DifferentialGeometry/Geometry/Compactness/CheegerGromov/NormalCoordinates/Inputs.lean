import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.InjectivityRadius


import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.EMetric

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

abbrev PointedSeqDistance
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) : Type _ :=
  forall k : Nat, (X.obj k).M -> (X.obj k).M -> Real

structure InjRadiusDecayInput
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  baseInj : BaseInjBound (I := I) X
  dist : PointedSeqDistance (I := I) X
  a : Real
  C : Real
  a_pos : 0 < a
  C_nonneg : 0 <= C
  decay :
    forall k : Nat, forall x : (X.obj k).M,
      HasInjRadiusAt (I := I) (X.obj k) x
        (a * (min baseInj.ρ 1) ^ Module.finrank Real E *
          Real.exp (-C * dist k x (X.obj k).basepoint))

namespace InjRadiusDecayInput

def subseq {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) (f : Nat -> Nat) :
    InjRadiusDecayInput (I := I) (X.subseq f) where
  baseInj := hd.baseInj.subseq f
  dist := fun k x y => hd.dist (f k) x y
  a := hd.a
  C := hd.C
  a_pos := hd.a_pos
  C_nonneg := hd.C_nonneg
  decay := by
    intro k x
    simpa [PointedRiemannianSeq.subseq] using hd.decay (f k) x

noncomputable def mu {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) (r : Real) : Real :=
  hd.a * (min hd.baseInj.ρ 1) ^ (Module.finrank Real E) * Real.exp (-hd.C * r)

omit [CompleteSpace E] in
theorem mu_pos {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) (r : Real) : 0 < hd.mu r :=
  mul_pos (mul_pos hd.a_pos (pow_pos (lt_min hd.baseInj.pos one_pos) _)) (Real.exp_pos _)

omit [CompleteSpace E] in
theorem mu_nonneg {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) (r : Real) : 0 ≤ hd.mu r :=
  (hd.mu_pos r).le

omit [CompleteSpace E] in
theorem mu_antitone {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) : Antitone hd.mu := by
  intro r₁ r₂ h
  have hK : 0 ≤ hd.a * (min hd.baseInj.ρ 1) ^ (Module.finrank Real E) :=
    (mul_pos hd.a_pos (pow_pos (lt_min hd.baseInj.pos one_pos) _)).le
  have hexp : Real.exp (-hd.C * r₂) ≤ Real.exp (-hd.C * r₁) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left h hd.C_nonneg])
  exact mul_le_mul_of_nonneg_left hexp hK

structure RealizesEdist {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) : Prop where
  dist_nonneg : ∀ (k : Nat) (x y : (X.obj k).M), 0 ≤ hd.dist k x y
  edist_eq : ∀ (k : Nat) (x y : (X.obj k).M),
    (letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
     edist x y) = ENNReal.ofReal (hd.dist k x y)

namespace RealizesEdist

omit [CompleteSpace E] in
theorem subseq {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (hre : hd.RealizesEdist) (f : Nat → Nat) :
    (hd.subseq f).RealizesEdist := by
  refine ⟨?_, ?_⟩
  · intro k x y
    exact hre.dist_nonneg (f k) x y
  · intro k x y
    simpa [InjRadiusDecayInput.subseq, PointedRiemannianSeq.subseq] using
      hre.edist_eq (f k) x y

end RealizesEdist

end InjRadiusDecayInput

structure VolumeComparisonInput
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  dist : PointedSeqDistance (I := I) X
  r0 : Real
  r0_pos : 0 < r0
  Imult : Real -> Nat

  ballMult :
    forall (m : Real), forall k : Nat, forall {α : Type u}, [Fintype α] -> [DecidableEq α] ->
      forall centers : α -> (X.obj k).M, forall r : Real, 0 < r -> m * r <= r0 ->
        (forall i j : α, i ≠ j ->
          r <= dist k (centers i) (centers j)) ->
        forall z : (X.obj k).M, forall J : Finset α,
          (forall j : α, j ∈ J ->
            dist k (centers j) z <= m * r) ->
          J.card <= Imult m

namespace VolumeComparisonInput

def subseq {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (vc : VolumeComparisonInput (I := I) X) (f : Nat -> Nat) :
    VolumeComparisonInput (I := I) (X.subseq f) where
  dist := fun k x y => vc.dist (f k) x y
  r0 := vc.r0
  r0_pos := vc.r0_pos
  Imult := vc.Imult
  ballMult := by
    intro m k α _ _ centers r hr hcap hsep z J hJz
    exact vc.ballMult m (f k) centers r hr hcap hsep z J hJz

end VolumeComparisonInput

end HCGCompactness
end DifferentialGeometry
