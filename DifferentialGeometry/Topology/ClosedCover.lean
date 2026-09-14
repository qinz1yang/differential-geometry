import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.LocallyFinite

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
