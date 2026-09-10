import DifferentialGeometry.Topology.SimplicialComplex.Incidence
import DifferentialGeometry.Topology.SimplicialComplex.MaximalFace

set_option autoImplicit false
noncomputable section

namespace Poincare.Topology.SimplicialComplex

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [DecidableEq E] (K : Geometry.SimplicialComplex 𝕜 E) (s : Finset E)


def geometricLink : Geometry.SimplicialComplex 𝕜 E where
  toPreAbstractSimplicialComplex := link K.toPreAbstractSimplicialComplex s
  indep ht := K.indep (link_le K.toPreAbstractSimplicialComplex s ht)
  inter_subset_convexHull ht hu := K.inter_subset_convexHull
    (link_le K.toPreAbstractSimplicialComplex s ht)
    (link_le K.toPreAbstractSimplicialComplex s hu)


@[simp]
theorem geometricLink_toPreAbstractSimplicialComplex :
    (geometricLink K s).toPreAbstractSimplicialComplex = link K.toPreAbstractSimplicialComplex s := rfl


theorem geometricLink_le : geometricLink K s ≤ K := link_le K.toPreAbstractSimplicialComplex s


instance finite_geometricLink_faces [Finite K.faces] : Finite (geometricLink K s).faces :=
  inferInstanceAs (Finite (link K.toPreAbstractSimplicialComplex s).faces)


theorem mem_geometricLink_singleton (p : E) (t : Finset E) :
    t ∈ (geometricLink K {p}).faces ↔ t.Nonempty ∧ p ∉ t ∧ insert p t ∈ K.faces := by
  change (t.Nonempty ∧ Disjoint {p} t ∧ {p} ∪ t ∈ K.faces) ↔ _
  simp only [Finset.disjoint_singleton_left, Finset.singleton_union]


theorem geometricLink_singleton_le_costar (p : E) :
    geometricLink K {p} ≤ geometricFaceCostar K {p} := by
  intro t ht
  refine ⟨geometricLink_le K {p} ht, ?_⟩
  have hp := (mem_geometricLink_singleton K p t).mp ht |>.2.1
  simpa only [Finset.singleton_subset_iff] using hp


theorem geometricLink_singleton_space_subset_costar (p : E) :
    (geometricLink K {p}).space ⊆ (geometricFaceCostar K {p}).space := by
  intro x hx
  obtain ⟨t, ht, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
  exact Geometry.SimplicialComplex.mem_space_iff.mpr
    ⟨t, geometricLink_singleton_le_costar K p ht, hx⟩

end Poincare.Topology.SimplicialComplex
