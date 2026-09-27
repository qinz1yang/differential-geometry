import DifferentialGeometry.Topology.Homology.CoveringTransferExact
import DifferentialGeometry.Topology.Homology.CoveringTransferNaturality
import Mathlib.Algebra.Homology.HomologySequenceLemmas

open CategoryTheory

noncomputable section

universe u

namespace DifferentialGeometry.Homology

variable {E E' B B' : TopCat.{u}} (p : E ⟶ B) (q : E' ⟶ B')
  (g : E ⟶ E') (f : B ⟶ B') (hsq : g ≫ q = p ≫ f)
  (hbij : ∀ b : B, Function.Bijective
    (fun e : p ⁻¹' {b} =>
      (⟨g e, by
        change q (g e.val) = f b
        exact (ConcreteCategory.congr_hom hsq e.val).trans
          (congrArg f (show p e.val = b from e.property))⟩ : q ⁻¹' {f b})))
  (hp : IsCoveringMap p) (hq : IsCoveringMap q)
  (hfinP : ∀ b : B, (p ⁻¹' {b}).Finite) (hfinQ : ∀ b : B', (q ⁻¹' {b}).Finite)
  (hcardP : ∀ b : B, Nat.card (p ⁻¹' {b}) = 2)
  (hcardQ : ∀ b : B', Nat.card (q ⁻¹' {b}) = 2)
  (A : ModuleCat.{u} (ZMod 2))

def singularTransferShortComplexMap :
    singularTransferShortComplex p hp hfinP hcardP A ⟶
      singularTransferShortComplex q hq hfinQ hcardQ A where
  τ₁ := SSet.chainComplexMap (TopCat.toSSet.map f) A
  τ₂ := SSet.chainComplexMap (TopCat.toSSet.map g) A
  τ₃ := SSet.chainComplexMap (TopCat.toSSet.map f) A
  comm₁₂ := (singularTransfer_naturality p q g f hsq hbij hp hq hfinP hfinQ A).symm
  comm₂₃ := by
    change SSet.chainComplexMap (TopCat.toSSet.map g) A ≫
      SSet.chainComplexMap (TopCat.toSSet.map q) A =
      SSet.chainComplexMap (TopCat.toSSet.map p) A ≫
        SSet.chainComplexMap (TopCat.toSSet.map f) A
    simp only [SSet.chainComplexMap, ← Functor.map_comp, hsq]

include hsq hbij in
theorem singularTransferShortComplex_δ_naturality (n : ℕ) :
    (singularTransferShortComplex_shortExact p hp hfinP hcardP A).δ (n + 1) n rfl ≫
        HomologicalComplex.homologyMap (SSet.chainComplexMap (TopCat.toSSet.map f) A) n =
      HomologicalComplex.homologyMap (SSet.chainComplexMap (TopCat.toSSet.map f) A) (n + 1) ≫
        (singularTransferShortComplex_shortExact q hq hfinQ hcardQ A).δ (n + 1) n rfl :=
  HomologicalComplex.HomologySequence.δ_naturality
    (singularTransferShortComplexMap p q g f hsq hbij hp hq hfinP hfinQ hcardP hcardQ A)
    (singularTransferShortComplex_shortExact p hp hfinP hcardP A)
    (singularTransferShortComplex_shortExact q hq hfinQ hcardQ A) (n + 1) n rfl

end DifferentialGeometry.Homology
