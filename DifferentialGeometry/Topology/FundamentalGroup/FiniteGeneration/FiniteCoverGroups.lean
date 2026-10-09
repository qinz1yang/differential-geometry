import DifferentialGeometry.Topology.FundamentalGroup.FiniteGeneration.CoverSubdivision
import Mathlib.GroupTheory.Finiteness
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set CategoryTheory
open DifferentialGeometry.Topology.VanKampen
open private conjugationFunctor from DifferentialGeometry.Topology.VanKampen.TorsionFreeCover
namespace GC.Topology
universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v} (V : ι → Set X) (x₀ : X)

structure CoverConnectors where
  path : ∀ i (x : V i), FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk x.val
  coherent : ∀ i (x y : V i)
    (p : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y),
    path i x ≫ (FundamentalGroupoid.map (subsetToAmbient (V i))).map p = path i y
  overlap : ∀ i j (x y : ↥(V i ∩ V j)),
    (path i ⟨x.val, x.property.1⟩ ≫ Groupoid.inv (path j ⟨x.val, x.property.2⟩) :
      FundamentalGroup X x₀) =
    (path i ⟨y.val, y.property.1⟩ ≫ Groupoid.inv (path j ⟨y.val, y.property.2⟩) :
      FundamentalGroup X x₀)

namespace CoverConnectors
variable {V x₀} (C : CoverConnectors V x₀)

def switch (i j : ι) (x : ↥(V i ∩ V j)) : FundamentalGroup X x₀ :=
  C.path i ⟨x.val, x.property.1⟩ ≫ Groupoid.inv (C.path j ⟨x.val, x.property.2⟩)

noncomputable def generator (i j : ι) : FundamentalGroup X x₀ := by
  classical
  exact if h : (V i ∩ V j).Nonempty then C.switch i j ⟨h.choose, h.choose_spec⟩ else 1

theorem switch_mem_closure (i j : ι) (x : ↥(V i ∩ V j)) :
    C.switch i j x ∈ Subgroup.closure (range (fun k : ι × ι => C.generator k.1 k.2)) := by
  classical
  have h : (V i ∩ V j).Nonempty := ⟨x.val, x.property⟩
  have he : C.generator i j = C.switch i j x := by
    simp only [generator, dif_pos h]
    exact C.overlap i j _ x
  rw [← he]
  exact Subgroup.subset_closure (mem_range_self (i,j))

noncomputable def pointIndex (hcover : (⋃ i, V i) = univ) (x : X) : ι :=
  (mem_iUnion.mp (show x ∈ ⋃ i, V i from hcover.symm ▸ mem_univ x)).choose

omit [TopologicalSpace X] in
theorem mem_pointIndex (hcover : (⋃ i, V i) = univ) (x : X) :
    x ∈ V (pointIndex hcover x) :=
  (mem_iUnion.mp (show x ∈ ⋃ i, V i from hcover.symm ▸ mem_univ x)).choose_spec

noncomputable def globalPath (hcover : (⋃ i, V i) = univ) (x : X) :
    FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk x :=
  C.path (pointIndex hcover x) ⟨x, mem_pointIndex hcover x⟩

noncomputable def loopFunctor (hcover : (⋃ i, V i) = univ) :
    FundamentalGroupoid X ⥤ SingleObj (FundamentalGroup X x₀) :=
  conjugationFunctor (FundamentalGroupoid.mk x₀) (fun x => C.globalPath hcover x.as)

theorem local_difference_mem (hcover : (⋃ i, V i) = univ) (i : ι) (x : V i) :
    (C.path i x ≫ Groupoid.inv (C.globalPath hcover x.val) : FundamentalGroup X x₀) ∈
      Subgroup.closure (range (fun k : ι × ι => C.generator k.1 k.2)) :=
  C.switch_mem_closure i (pointIndex hcover x.val)
    ⟨x.val, x.property, mem_pointIndex hcover x.val⟩

theorem local_path_mem (hcover : (⋃ i, V i) = univ) (i : ι)
    {a b : X} (p : _root_.Path a b) (hp : range p ⊆ V i) :
    (C.loopFunctor hcover).map (show FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b
      from ⟦p⟧) ∈ Subgroup.closure (range (fun k : ι × ι => C.generator k.1 k.2)) := by
  let x : V i := ⟨a, hp ⟨0, p.source⟩⟩
  let y : V i := ⟨b, hp ⟨1, p.target⟩⟩
  let q : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y := ⟦pathIn (V i) p hp⟧
  have hq := C.coherent i x y q
  have hmap : (FundamentalGroupoid.map (subsetToAmbient (V i))).map q =
      (show FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b from ⟦p⟧) := by
    change ⟦(pathIn (V i) p hp).map continuous_subtype_val⟧ = ⟦p⟧
    congr 1
  rw [hmap] at hq
  let dx : FundamentalGroup X x₀ := C.path i x ≫ Groupoid.inv (C.globalPath hcover a)
  let dy : FundamentalGroup X x₀ := C.path i y ≫ Groupoid.inv (C.globalPath hcover b)
  have he : (C.loopFunctor hcover).map
      (show FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b from ⟦p⟧) =
      dy * dx⁻¹ := by
    change C.globalPath hcover a ≫ ⟦p⟧ ≫ Groupoid.inv (C.globalPath hcover b) =
      Groupoid.inv (C.path i x ≫ Groupoid.inv (C.globalPath hcover a)) ≫
        (C.path i y ≫ Groupoid.inv (C.globalPath hcover b))
    rw [← hq]
    simp [Category.assoc]
  let S : Subgroup (FundamentalGroup X x₀) :=
    Subgroup.closure (range (fun k : ι × ι => C.generator k.1 k.2))
  have hm : dy * dx⁻¹ ∈ S := S.mul_mem (C.local_difference_mem hcover i y)
    (S.inv_mem (C.local_difference_mem hcover i x))
  exact he.symm ▸ hm

include C in
theorem groupFG [Finite ι] (hopen : ∀ i, IsOpen (V i))
    (hcover : (⋃ i, V i) = univ) : Group.FG (FundamentalGroup X x₀) := by
  classical
  let R := range (fun k : ι × ι => C.generator k.1 k.2)
  let S := Subgroup.closure R
  apply Group.fg_iff.mpr
  refine ⟨R, ?_, finite_range _⟩
  apply top_unique
  intro g _
  let d : FundamentalGroup X x₀ := C.globalPath hcover x₀
  let q : FundamentalGroup X x₀ := Groupoid.inv d ≫ g ≫ d
  have h := functor_path_mem_of_cover V hopen hcover (C.loopFunctor hcover) S
    (by intro i a b p hp; exact C.local_path_mem hcover i p hp) q.out
  have he : (C.loopFunctor hcover).map
      (show FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk x₀ from ⟦q.out⟧) = g := by
    rw [Quotient.out_eq]
    change d ≫ (Groupoid.inv d ≫ g ≫ d) ≫ Groupoid.inv d = g
    simp [Category.assoc]
  exact he ▸ h

end CoverConnectors
end GC.Topology
