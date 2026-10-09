import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Homeomorph.Defs

open Set

namespace ContinuousMap

variable {ι X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

noncomputable def liftClosedCover (S : ι → Set X) (φ : ∀ i, C(S i, Y))
    (hφ : ∀ (i j) (x : X) (hxi : x ∈ S i) (hxj : x ∈ S j),
      φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩)
    (hcov : ⋃ i, S i = univ) (hclosed : ∀ i, IsClosed (S i)) (hfinite : LocallyFinite S) :
    C(X, Y) :=
  mk (Set.liftCover S (fun i ↦ φ i) hφ hcov) <| hfinite.continuous hcov hclosed fun i ↦ by
    rw [continuousOn_iff_continuous_domRestrict]
    simpa +unfoldPartialApp only [Set.domRestrict, Set.liftCover_coe] using (φ i).continuous

variable {S : ι → Set X} {φ : ∀ i, C(S i, Y)}
    {hφ : ∀ (i j) (x : X) (hxi : x ∈ S i) (hxj : x ∈ S j),
      φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩}
    {hcov : ⋃ i, S i = univ} {hclosed : ∀ i, IsClosed (S i)} {hfinite : LocallyFinite S}

@[simp]
theorem liftClosedCover_coe {i : ι} (x : S i) :
    liftClosedCover S φ hφ hcov hclosed hfinite x = φ i x :=
  by
    change Set.liftCover S (fun i ↦ φ i) hφ hcov x = φ i x
    exact Set.liftCover_coe x

@[simp]
theorem liftClosedCover_restrict {i : ι} :
    (liftClosedCover S φ hφ hcov hclosed hfinite).restrict (S i) = φ i := by
  ext x
  simp only [restrict_apply, liftClosedCover_coe]

end ContinuousMap

namespace Homeomorph

variable {ι X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

noncomputable def liftClosedCover (S : ι → Set X) (T : ι → Set Y)
    (e : ∀ i, S i ≃ₜ T i)
    (he : ∀ (i j) (x : X) (hxi : x ∈ S i) (hxj : x ∈ S j),
      (e i ⟨x, hxi⟩ : Y) = e j ⟨x, hxj⟩)
    (he' : ∀ (i j) (y : Y) (hyi : y ∈ T i) (hyj : y ∈ T j),
      ((e i).symm ⟨y, hyi⟩ : X) = (e j).symm ⟨y, hyj⟩)
    (hS : ⋃ i, S i = univ) (hSc : ∀ i, IsClosed (S i)) (hSf : LocallyFinite S)
    (hT : ⋃ i, T i = univ) (hTc : ∀ i, IsClosed (T i)) (hTf : LocallyFinite T) :
    X ≃ₜ Y := by
  let f : C(X, Y) := ContinuousMap.liftClosedCover S
    (fun i => ⟨fun x => (e i x : Y), continuous_subtype_val.comp (e i).continuous⟩)
    he hS hSc hSf
  let g : C(Y, X) := ContinuousMap.liftClosedCover T
    (fun i => ⟨fun y => ((e i).symm y : X),
      continuous_subtype_val.comp (e i).symm.continuous⟩)
    he' hT hTc hTf
  have hf (i : ι) (x : S i) : f x = (e i x : Y) := by
    exact ContinuousMap.liftClosedCover_coe (φ := fun i =>
      ⟨fun x => (e i x : Y), continuous_subtype_val.comp (e i).continuous⟩)
      (hφ := he) (hcov := hS) (hclosed := hSc) (hfinite := hSf) x
  have hg (i : ι) (y : T i) : g y = ((e i).symm y : X) := by
    exact ContinuousMap.liftClosedCover_coe (φ := fun i =>
      ⟨fun y => ((e i).symm y : X), continuous_subtype_val.comp (e i).symm.continuous⟩)
      (hφ := he') (hcov := hT) (hclosed := hTc) (hfinite := hTf) y
  refine
    { toFun := f
      invFun := g
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := f.continuous
      continuous_invFun := g.continuous }
  · intro x
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hS.symm ▸ mem_univ x)
    rw [hf i ⟨x, hxi⟩, hg i (e i ⟨x, hxi⟩), symm_apply_apply]
  · intro y
    obtain ⟨i, hyi⟩ := mem_iUnion.mp (hT.symm ▸ mem_univ y)
    rw [hg i ⟨y, hyi⟩, hf i ((e i).symm ⟨y, hyi⟩), apply_symm_apply]

variable {S : ι → Set X} {T : ι → Set Y} {e : ∀ i, S i ≃ₜ T i}
    {he : ∀ (i j) (x : X) (hxi : x ∈ S i) (hxj : x ∈ S j),
      (e i ⟨x, hxi⟩ : Y) = e j ⟨x, hxj⟩}
    {he' : ∀ (i j) (y : Y) (hyi : y ∈ T i) (hyj : y ∈ T j),
      ((e i).symm ⟨y, hyi⟩ : X) = (e j).symm ⟨y, hyj⟩}
    {hS : ⋃ i, S i = univ} {hSc : ∀ i, IsClosed (S i)} {hSf : LocallyFinite S}
    {hT : ⋃ i, T i = univ} {hTc : ∀ i, IsClosed (T i)} {hTf : LocallyFinite T}

@[simp]
theorem liftClosedCover_coe {i : ι} (x : S i) :
    liftClosedCover S T e he he' hS hSc hSf hT hTc hTf x = e i x := by
  exact ContinuousMap.liftClosedCover_coe (φ := fun i =>
    ⟨fun x => (e i x : Y), continuous_subtype_val.comp (e i).continuous⟩)
      (hφ := he) (hcov := hS) (hclosed := hSc) (hfinite := hSf) x

@[simp]
theorem liftClosedCover_symm_coe {i : ι} (y : T i) :
    (liftClosedCover S T e he he' hS hSc hSf hT hTc hTf).symm y = (e i).symm y := by
  exact ContinuousMap.liftClosedCover_coe (φ := fun i =>
    ⟨fun y => ((e i).symm y : X), continuous_subtype_val.comp (e i).symm.continuous⟩)
      (hφ := he') (hcov := hT) (hclosed := hTc) (hfinite := hTf) y

end Homeomorph
