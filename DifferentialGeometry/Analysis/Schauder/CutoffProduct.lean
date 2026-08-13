import DifferentialGeometry.Analysis.Schauder.Localization
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Topology.ContinuousMap.Bounded.Normed

noncomputable section

namespace DifferentialGeometry.Analysis.Schauder

open BoundedContinuousFunction
open scoped BoundedContinuousFunction

variable {X A B C : Type*} [TopologicalSpace X]
  [NormedAddCommGroup A] [NormedSpace Real A]
  [NormedAddCommGroup B] [NormedSpace Real B]
  [NormedAddCommGroup C] [NormedSpace Real C]

def bilinearBcf
    (L : A →L[Real] B →L[Real] C)
    (f : BoundedContinuousFunction X A)
    (g : BoundedContinuousFunction X B) :
    BoundedContinuousFunction X C :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x ↦ L (f x) (g x))
    (L.continuous₂.comp₂ f.continuous g.continuous)
    (‖L‖ * ‖f‖ * ‖g‖)
    (fun x ↦ (L.le_opNorm₂ (f x) (g x)).trans (by
      gcongr
      · exact f.norm_coe_le_norm x
      · exact g.norm_coe_le_norm x))

@[simp]
theorem bilinearBcf_apply
    (L : A →L[Real] B →L[Real] C)
    (f : BoundedContinuousFunction X A)
    (g : BoundedContinuousFunction X B) (x : X) :
    bilinearBcf L f g x = L (f x) (g x) := rfl

section Cutoff

variable {V F : Type*}
  [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup F] [NormedSpace Real F]

def cutoffValue
    (chi : BoundedContinuousFunction V Real)
    (u : BoundedContinuousFunction V F) :
    BoundedContinuousFunction V F :=
  chi • u

def cutoffTimeJet
    (chi dchi : Real → BoundedContinuousFunction V Real)
    (u du : Real → BoundedContinuousFunction V F) (t : Real) :
    BoundedContinuousFunction V F :=
  cutoffValue (chi t) (du t) + cutoffValue (dchi t) (u t)

omit [NormedSpace Real V] in
@[simp]
theorem cutoffValue_apply
    (chi : BoundedContinuousFunction V Real)
    (u : BoundedContinuousFunction V F) (x : V) :
    cutoffValue chi u x = chi x • u x := rfl

omit [NormedSpace Real V] in
@[simp]
theorem cutoffTimeJet_apply
    (chi dchi : Real → BoundedContinuousFunction V Real)
    (u du : Real → BoundedContinuousFunction V F) (t : Real) (x : V) :
    cutoffTimeJet chi dchi u du t x =
      chi t x • du t x + dchi t x • u t x := rfl

def cutoffJet1
    (chi : BoundedContinuousFunction V Real)
    (dchi : BoundedContinuousFunction V (V →L[Real] Real))
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[Real] F)) :
    BoundedContinuousFunction V (V →L[Real] F) :=
  chi • du +
    bilinearBcf (ContinuousLinearMap.smulRightL Real V F) dchi u

@[simp]
theorem cutoffJet1_apply
    (chi : BoundedContinuousFunction V Real)
    (dchi : BoundedContinuousFunction V (V →L[Real] Real))
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[Real] F)) (x : V) :
    cutoffJet1 chi dchi u du x =
      chi x • du x + (dchi x).smulRight (u x) := rfl

def cutoffJet2
    (chi : BoundedContinuousFunction V Real)
    (dchi : BoundedContinuousFunction V (V →L[Real] Real))
    (d2chi : BoundedContinuousFunction V (V →L[Real] V →L[Real] Real))
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (d2u : BoundedContinuousFunction V (V →L[Real] V →L[Real] F)) :
    BoundedContinuousFunction V (V →L[Real] V →L[Real] F) :=
  chi • d2u +
    bilinearBcf (ContinuousLinearMap.smulRightL Real V (V →L[Real] F))
      dchi du +
    bilinearBcf (ContinuousLinearMap.precompR V
      (ContinuousLinearMap.smulRightL Real V F)) dchi du +
    bilinearBcf (ContinuousLinearMap.precompL V
      (ContinuousLinearMap.smulRightL Real V F)) d2chi u

@[simp]
theorem cutoffJet2_apply
    (chi : BoundedContinuousFunction V Real)
    (dchi : BoundedContinuousFunction V (V →L[Real] Real))
    (d2chi : BoundedContinuousFunction V (V →L[Real] V →L[Real] Real))
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (d2u : BoundedContinuousFunction V (V →L[Real] V →L[Real] F))
    (x : V) :
    cutoffJet2 chi dchi d2chi u du d2u x =
      chi x • d2u x +
        (dchi x).smulRight (du x) +
        (ContinuousLinearMap.smulRightL Real V F).precompR V
          (dchi x) (du x) +
        (ContinuousLinearMap.smulRightL Real V F).precompL V
          (d2chi x) (u x) := rfl

theorem cutoffValue_hasFDerivAt
    (chi : BoundedContinuousFunction V Real)
    (dchi : BoundedContinuousFunction V (V →L[Real] Real))
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (hchi : ∀ x, HasFDerivAt (chi : V → Real) (dchi x) x)
    (hu : ∀ x, HasFDerivAt (u : V → F) (du x) x)
    (x : V) :
    HasFDerivAt (cutoffValue chi u : V → F)
      (cutoffJet1 chi dchi u du x) x := by
  simpa only [cutoffValue_apply, cutoffJet1_apply] using
    (hchi x).smul (hu x)

omit [NormedSpace Real V] in
theorem cutoffValue_hasDerivAt
    (chi dchi : Real → BoundedContinuousFunction V Real)
    (u du : Real → BoundedContinuousFunction V F)
    (t : Real)
    (hchi : HasDerivAt chi (dchi t) t)
    (hu : HasDerivAt u (du t) t) :
    HasDerivAt (fun s ↦ cutoffValue (chi s) (u s))
      (cutoffTimeJet chi dchi u du t) t := by
  simpa only [cutoffValue, cutoffTimeJet] using hchi.smul hu

theorem cutoffJet1_hasFDerivAt
    (chi : BoundedContinuousFunction V Real)
    (dchi : BoundedContinuousFunction V (V →L[Real] Real))
    (d2chi : BoundedContinuousFunction V (V →L[Real] V →L[Real] Real))
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (d2u : BoundedContinuousFunction V (V →L[Real] V →L[Real] F))
    (hchi : ∀ x, HasFDerivAt (chi : V → Real) (dchi x) x)
    (hdchi : ∀ x, HasFDerivAt (dchi : V → V →L[Real] Real) (d2chi x) x)
    (hu : ∀ x, HasFDerivAt (u : V → F) (du x) x)
    (hdu : ∀ x, HasFDerivAt (du : V → V →L[Real] F) (d2u x) x)
    (x : V) :
    HasFDerivAt (cutoffJet1 chi dchi u du : V → V →L[Real] F)
      (cutoffJet2 chi dchi d2chi u du d2u x) x := by
  have hleft := (hchi x).smul (hdu x)
  have hright :=
    (ContinuousLinearMap.smulRightL Real V F).hasFDerivAt_of_bilinear
      (hdchi x) (hu x)
  change HasFDerivAt
    (fun y ↦ chi y • du y + (dchi y).smulRight (u y))
    (cutoffJet2 chi dchi d2chi u du d2u x) x
  simpa only [cutoffJet2_apply, add_assoc] using hleft.add hright

end Cutoff

end DifferentialGeometry.Analysis.Schauder

end
