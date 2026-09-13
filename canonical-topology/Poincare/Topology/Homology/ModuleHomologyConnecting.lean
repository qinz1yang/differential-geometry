import Poincare.Topology.Homology.ModuleHomologyClasses
import Mathlib.Algebra.Homology.ConcreteCategory

noncomputable section

open CategoryTheory

universe u v

namespace Poincare.Topology

variable {R : Type u} [Ring R]

private theorem moduleCycleIso_inv_eq_cyclesMk
    (S : ShortComplex (ModuleCat.{v} R)) (c : LinearMap.ker S.g.hom) :
    S.moduleCatCyclesIso.inv c = S.cyclesMk c.val c.property := by
  apply (ModuleCat.mono_iff_injective S.iCycles).mp inferInstance
  have h := congrArg (fun f : S.moduleCatLeftHomologyData.K ⟶ S.X₂ => f c)
    S.moduleCatCyclesIso_inv_iCycles
  change S.iCycles (S.moduleCatCyclesIso.inv c) = c.val at h
  exact h.trans (S.i_cyclesMk c.val c.property).symm

theorem moduleHomologyClass_connecting
    {ι : Type*} {shape : ComplexShape ι}
    {S : ShortComplex (HomologicalComplex (ModuleCat.{v} R) shape)} (hS : S.ShortExact)
    (i j : ι) (hij : shape.Rel i j) (c : LinearMap.ker (S.X₃.sc i).g.hom)
    (b : S.X₂.X i) (hb : S.g.f i b = c.val)
    (a : LinearMap.ker (S.X₁.sc j).g.hom) (ha : S.f.f j a.val = S.X₂.d i j b) :
    hS.δ i j hij (moduleHomologyClass (S.X₃.sc i) c) =
      moduleHomologyClass (S.X₁.sc j) a := by
  have hc : S.X₃.d i j c.val = 0 := by
    have h := c.property
    change S.X₃.d i (shape.next i) c.val = 0 at h
    rwa [shape.next_eq' hij] at h
  have h := hS.δ_apply i j hij c.val hc b hb a.val ha (shape.next j) rfl
  have h3 : (S.X₃.cyclesMk c.val j (shape.next_eq' hij) hc) =
      (S.X₃.sc i).moduleCatCyclesIso.inv c := by
    exact (moduleCycleIso_inv_eq_cyclesMk (S.X₃.sc i) c).symm
  have h1 : (S.X₁.cyclesMk a.val (shape.next j) rfl
      (hS.d_eq_zero_of_f_eq_d_apply i j b a.val ha _)) =
      (S.X₁.sc j).moduleCatCyclesIso.inv a := by
    exact (moduleCycleIso_inv_eq_cyclesMk (S.X₁.sc j) a).symm
  rw [h3, h1] at h
  exact h

end Poincare.Topology

end
