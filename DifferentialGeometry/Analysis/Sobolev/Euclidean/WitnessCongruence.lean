import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Witnesses
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Basic

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace DeGiorgi

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

def MemW1pWitness.congr
    {p : ℝ≥0∞} {Ω : Set V} {u v : V → ℝ}
    (hu : MemW1pWitness p u Ω) (huv : u =ᵐ[volume.restrict Ω] v) :
    MemW1pWitness p v Ω where
  memLp := MemLp.ae_eq huv hu.memLp
  weakGrad := hu.weakGrad
  weakGrad_component_memLp := hu.weakGrad_component_memLp
  isWeakGrad := fun j => (hu.isWeakGrad j).congr_ae huv Filter.EventuallyEq.rfl

theorem MemW1pWitness.congr_weakGrad
    {p : ℝ≥0∞} {Ω : Set V} {u v : V → ℝ}
    (hu : MemW1pWitness p u Ω) (huv : u =ᵐ[volume.restrict Ω] v) :
    (hu.congr huv).weakGrad = hu.weakGrad := rfl

end DeGiorgi
