import DifferentialGeometry.Topology.Homology.Local.Neighborhood
import Mathlib.Topology.OpenPartialHomeomorph.Basic

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Set
namespace DifferentialGeometry.Homology
universe u
variable {X Y : TopCat.{u}} (e : OpenPartialHomeomorph X Y) (x : X) (hx : x ∈ e.source)
  {k : Type u} [Ring k] (R : ModuleCat.{u} k)

theorem chart_puncture_iff (y : e.source) :
    y ∈ ({(⟨x, hx⟩ : e.source)}ᶜ : Set e.source) ↔
      e.toHomeomorphSourceTarget y ∈
        ({(⟨e x, e.map_source hx⟩ : e.target)}ᶜ : Set e.target) := by
  change y ≠ ⟨x, hx⟩ ↔ e.toHomeomorphSourceTarget y ≠ ⟨e x, e.map_source hx⟩
  exact not_congr e.toHomeomorphSourceTarget.injective.eq_iff.symm


def chartSourceTargetHomologyIso (n : ℕ) :
    relativeHomology (TopCat.of e.source) ({(⟨x, hx⟩ : e.source)}ᶜ : Set e.source) R n ≅
      relativeHomology (TopCat.of e.target)
        ({(⟨e x, e.map_source hx⟩ : e.target)}ᶜ : Set e.target) R n :=
  relativeHomologyIso R e.toHomeomorphSourceTarget (chart_puncture_iff e x hx) n

def chartLocalHomologyIso [T1Space X] [T1Space Y] (n : ℕ) :
    relativeHomology X ({x}ᶜ : Set X) R n ≅
      relativeHomology Y ({e x}ᶜ : Set Y) R n :=
  (puncturedNeighborhoodHomologyIso X e.source x hx R e.open_source n).symm ≪≫
    chartSourceTargetHomologyIso e x hx R n ≪≫
      puncturedNeighborhoodHomologyIso Y e.target (e x) (e.map_source hx) R e.open_target n

@[reassoc]
theorem chartLocalHomologyIso_inclusion [T1Space X] [T1Space Y] (n : ℕ) :
    (puncturedNeighborhoodHomologyIso X e.source x hx R e.open_source n).hom ≫
        (chartLocalHomologyIso e x hx R n).hom =
      (chartSourceTargetHomologyIso e x hx R n).hom ≫
        (puncturedNeighborhoodHomologyIso Y e.target (e x) (e.map_source hx)
          R e.open_target n).hom := by
  simp only [chartLocalHomologyIso, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

section Field
variable (k : Type u) [Field k]
include hx


theorem relativeEulerChar_chart [T1Space X] [T1Space Y] :
    relativeEulerChar X ({x}ᶜ : Set X) k = relativeEulerChar Y ({e x}ᶜ : Set Y) k := by
  apply finsum_congr
  intro n
  exact congrArg (fun d : ℕ => ((ComplexShape.down ℕ).χ n : ℤ) * (d : ℤ))
    (chartLocalHomologyIso e x hx (ModuleCat.of k k) n).toLinearEquiv.finrank_eq


theorem finiteHomologyType_chart_iff [T1Space X] [T1Space Y] :
    DifferentialGeometry.HomologicalComplex.finiteHomologyType
        (relativeChainComplex X ({x}ᶜ : Set X) (ModuleCat.of k k)) ↔
      DifferentialGeometry.HomologicalComplex.finiteHomologyType
        (relativeChainComplex Y ({e x}ᶜ : Set Y) (ModuleCat.of k k)) := by
  have transfer {A B : ChainComplex (ModuleCat.{u} k) ℕ}
      (h : ∀ n, A.homology n ≅ B.homology n)
      (hA : DifferentialGeometry.HomologicalComplex.finiteHomologyType A) :
      DifferentialGeometry.HomologicalComplex.finiteHomologyType B := by
    constructor
    · intro n
      let :=  hA.1 n
      exact (h n).toLinearEquiv.finiteDimensional
    · obtain ⟨N, hN⟩ := hA.2
      exact ⟨N, fun n hn => (hN n hn).of_iso (h n).symm⟩
  exact ⟨transfer (fun n => chartLocalHomologyIso e x hx (ModuleCat.of k k) n),
    transfer (fun n => (chartLocalHomologyIso e x hx (ModuleCat.of k k) n).symm)⟩

end Field
end DifferentialGeometry.Homology
