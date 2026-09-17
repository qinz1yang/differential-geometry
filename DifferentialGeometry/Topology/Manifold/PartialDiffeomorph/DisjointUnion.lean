import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

open Set
open scoped ContDiff

namespace PartialDiffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] {n : ℕ∞ω}

noncomputable def disjointUnion (e f : PartialDiffeomorph I J M N n)
    (hs : Disjoint e.source f.source) (ht : Disjoint e.target f.target) :
    PartialDiffeomorph I J M N n := by
  classical
  refine { e.toOpenPartialHomeomorph.disjointUnion f.toOpenPartialHomeomorph hs ht with
    contMDiffOn_toFun := ?_, contMDiffOn_invFun := ?_ }
  · apply ContMDiffOn.union_of_isOpen ?_ ?_ e.open_source f.open_source
    · exact e.contMDiffOn.congr (fun x hx => if_pos hx)
    · exact f.contMDiffOn.congr (fun x hx =>
        if_neg (fun he => disjoint_left.mp hs he hx))
  · apply ContMDiffOn.union_of_isOpen ?_ ?_ e.open_target f.open_target
    · exact e.symm.contMDiffOn.congr (fun x hx => if_pos hx)
    · exact f.symm.contMDiffOn.congr (fun x hx =>
        if_neg (fun he => disjoint_left.mp ht he hx))

@[simp] theorem disjointUnion_source (e f : PartialDiffeomorph I J M N n)
    (hs : Disjoint e.source f.source) (ht : Disjoint e.target f.target) :
    (e.disjointUnion f hs ht).source = e.source ∪ f.source := rfl

@[simp] theorem disjointUnion_target (e f : PartialDiffeomorph I J M N n)
    (hs : Disjoint e.source f.source) (ht : Disjoint e.target f.target) :
    (e.disjointUnion f hs ht).target = e.target ∪ f.target := rfl

theorem disjointUnion_apply_of_mem_left (e f : PartialDiffeomorph I J M N n)
    (hs : Disjoint e.source f.source) (ht : Disjoint e.target f.target)
    {x : M} (hx : x ∈ e.source) : e.disjointUnion f hs ht x = e x := by
  classical
  exact if_pos hx

theorem disjointUnion_apply_of_mem_right (e f : PartialDiffeomorph I J M N n)
    (hs : Disjoint e.source f.source) (ht : Disjoint e.target f.target)
    {x : M} (hx : x ∈ f.source) : e.disjointUnion f hs ht x = f x := by
  classical
  exact if_neg (fun he => disjoint_left.mp hs he hx)

theorem disjointUnion_symm_apply_of_mem_left (e f : PartialDiffeomorph I J M N n)
    (hs : Disjoint e.source f.source) (ht : Disjoint e.target f.target)
    {x : N} (hx : x ∈ e.target) : (e.disjointUnion f hs ht).symm x = e.symm x := by
  classical
  exact if_pos hx

theorem disjointUnion_symm_apply_of_mem_right (e f : PartialDiffeomorph I J M N n)
    (hs : Disjoint e.source f.source) (ht : Disjoint e.target f.target)
    {x : N} (hx : x ∈ f.target) : (e.disjointUnion f hs ht).symm x = f.symm x := by
  classical
  exact if_neg (fun he => disjoint_left.mp ht he hx)

end PartialDiffeomorph
