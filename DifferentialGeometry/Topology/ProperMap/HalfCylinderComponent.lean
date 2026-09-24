import DifferentialGeometry.Topology.Connected.ComponentFilling
import DifferentialGeometry.Topology.OpenPartialHomeomorph.CollarAdvance
import DifferentialGeometry.Topology.ProperMap.HalfCylinder

open Set
open scoped NNReal

namespace DifferentialGeometry.Topology

variable {N M : Type*} [TopologicalSpace N] [CompactSpace N] [PreconnectedSpace N]
  [TopologicalSpace M] [T2Space M]

theorem connectedComponentIn_closed_exterior_eq_range_half_cylinder
    (f : N × ℝ≥0 → M) (hproper : IsProperMap f) (hinj : Function.Injective f)
    (hopen : IsOpen (f '' (univ ×ˢ Ioi (0 : ℝ≥0))))
    (A : OpenPartialHomeomorph (N × ℝ) M)
    (hA : univ ×ˢ Icc (0 : ℝ) 1 ⊆ A.source)
    (hfirst : ∀ z t (ht : t ∈ Icc (0 : ℝ) 1), f (z, ⟨t, ht.1⟩) = A (z, t))
    {W R : Set M} (hW : closure (interior W) = W) (hR : IsClosed R)
    (hfront : frontier W = range (fun z => f (z, 0)) ∪ R)
    (hdisj : Disjoint (range (fun z => f (z, 0))) R)
    (hinter : range f ∩ W = range (fun z => f (z, 0)))
    {x : M} (hx : x ∈ range f) :
    connectedComponentIn (interior W)ᶜ x = range f := by
  let B := range f
  let U := f '' (univ ×ˢ Ioi (0 : ℝ≥0))
  let L := range (fun z => f (z, 0))
  let T := A '' (univ ×ˢ Icc (0 : ℝ) 1)
  have hzero (z : N) : A (z, 0) = f (z, 0) :=
    (hfirst z 0 ⟨le_rfl, zero_le_one⟩).symm
  have hface : A '' (univ ×ˢ ({0} : Set ℝ)) = L := by
    ext y
    constructor
    · rintro ⟨⟨z, t⟩, ⟨_, ht⟩, rfl⟩
      have ht : t = 0 := ht
      subst t
      exact ⟨z, (hzero z).symm⟩
    · rintro ⟨z, rfl⟩
      exact ⟨(z, 0), ⟨mem_univ _, rfl⟩, hzero z⟩
  have hTsub : T ⊆ B := by
    rintro y ⟨⟨z, t⟩, ⟨_, ht⟩, rfl⟩
    exact ⟨(z, ⟨t, ht.1⟩), hfirst z t ht⟩
  have hclosure : closure U = B := closure_image_positive_half_cylinder_of_isProperMap f hproper
  have hUL : Disjoint U L := by
    rw [disjoint_left]
    rintro y ⟨⟨z, t⟩, ⟨_, ht⟩, rfl⟩ ⟨w, hw⟩
    have heq := congrArg Prod.snd (hinj hw)
    exact ht.ne' heq.symm
  have hUW : Disjoint U (interior W) := by
    refine disjoint_left.mpr ?_
    intro y hyU hyW
    have hyB : y ∈ B := by obtain ⟨z, _, rfl⟩ := hyU; exact mem_range_self z
    exact disjoint_left.mp hUL hyU ((Set.ext_iff.mp hinter y).mp ⟨hyB, interior_subset hyW⟩)
  have hBexterior : B ⊆ (interior W)ᶜ := by
    rw [← hclosure]
    exact (hUW.closure_left isOpen_interior).subset_compl_right
  have hTinterior : interior T = A '' (univ ×ˢ Ioo (0 : ℝ) 1) := by
    rw [← A.image_interior_of_subset_source hA, interior_prod_eq,
      interior_univ, interior_Icc]
  have hTint : interior T ⊆ U := by
    rw [hTinterior]
    rintro y ⟨⟨z, t⟩, ⟨_, ht⟩, rfl⟩
    exact ⟨(z, ⟨t, ht.1.le⟩), ⟨mem_univ _, ht.1⟩, hfirst z t ⟨ht.1.le, ht.2.le⟩⟩
  have hLfill : L ⊆ interior (W ∪ T) := by
    have hLW : L ⊆ W := fun y hy =>
      (hW ▸ isClosed_closure).frontier_subset (hfront.symm ▸ Or.inl hy)
    have hh := A.image_lower_boundary_subset_interior_union zero_lt_one hA hW hR
      (hUW.mono_left hTint) (hface ▸ hLW) (by simpa only [hface] using hfront.le)
      (by simpa only [hface] using hdisj)
    simpa only [hface, union_comm] using hh
  have hBfill : B ⊆ interior (W ∪ B) := by
    rintro y ⟨⟨z, t⟩, rfl⟩
    by_cases ht : t = 0
    · subst t
      exact interior_mono (union_subset_union_right W hTsub) (hLfill (mem_range_self z))
    · have hUsub : U ⊆ W ∪ B := by
        rintro y ⟨p, _, rfl⟩
        exact Or.inr (mem_range_self p)
      exact interior_maximal hUsub hopen
        ⟨(z, t), ⟨mem_univ _, lt_of_le_of_ne zero_le (Ne.symm ht)⟩, rfl⟩
  exact connectedComponentIn_closed_exterior_eq_of_subset_interior_union
    hproper.isClosed_range (isPreconnected_range hproper.continuous) hBexterior hBfill hx

end DifferentialGeometry.Topology
