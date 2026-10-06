import DifferentialGeometry.Topology.FundamentalGroup.TorusMapDegree
import DifferentialGeometry.Topology.FundamentalGroup.CircleDegree
import DifferentialGeometry.Topology.FundamentalGroup.CirclePowerDegree
import DifferentialGeometry.Topology.FundamentalGroup.BasedMapComposition
import DifferentialGeometry.Topology.LoopSpace.CircleDegree

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology Set Function
open scoped ContinuousMap
namespace GC.LongTime.CuspP1

section Abstract

/-- A periodic cover `F` with the same fibres as a quotient map `Q` onto a compact space descends
to a homeomorphism. -/
theorem exists_homeo_of_same_fibres_CPA2 {P X Y : Type*} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace X] [T2Space Y] (Q : P → X) (F : P → Y)
    (hQ : _root_.Topology.IsQuotientMap Q) (hF : Continuous F) (hFs : Surjective F)
    (hfib : ∀ y z, Q y = Q z ↔ F y = F z) :
    ∃ h : X ≃ₜ Y, ∀ y, h (Q y) = F y := by
  classical
  have hQs : Surjective Q := hQ.surjective
  let g : X → Y := fun x => F (Classical.choose (hQs x))
  have hg : ∀ y, g (Q y) = F y := by
    intro y
    have h1 : Q (Classical.choose (hQs (Q y))) = Q y := Classical.choose_spec (hQs (Q y))
    exact ((hfib _ _).mp h1)
  have hgc : Continuous g := by
    rw [hQ.continuous_iff]
    have : g ∘ Q = F := funext hg
    rw [this]; exact hF
  have hinj : Injective g := by
    intro x x' hxx
    obtain ⟨y, rfl⟩ := hQs x
    obtain ⟨z, rfl⟩ := hQs x'
    rw [hg, hg] at hxx
    exact (hfib _ _).mpr hxx
  have hsurj : Surjective g := by
    intro w
    obtain ⟨y, rfl⟩ := hFs w
    exact ⟨Q y, hg y⟩
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g ⟨hinj, hsurj⟩) hgc, hg⟩

end Abstract

section Loops

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Naturality of the degree-one class of a free loop. -/
theorem loopDegreeClass_comp_CPA2 (f : C(X, Y)) (γ : freeLoop X) :
    loopDegreeClass (f.comp γ) 1 =
      FundamentalGroup.mapOfEq f (rfl : f (γ 0) = (f.comp γ) 0) (loopDegreeClass γ 1) := by
  rw [FundamentalGroup.mapOfEq_apply]
  unfold loopDegreeClass
  change Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk _
  congr 1

end Loops

end GC.LongTime.CuspP1
