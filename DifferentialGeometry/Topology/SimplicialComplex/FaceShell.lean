import DifferentialGeometry.Topology.SimplicialComplex.GeometricLink

set_option autoImplicit false
noncomputable section

namespace Poincare.Topology.SimplicialComplex

variable {ι : Type*} [DecidableEq ι] (K : PreAbstractSimplicialComplex ι) (s : Finset ι)


def faceShell : PreAbstractSimplicialComplex ι where
  faces := {t | t ∈ K ∧ t ∪ s ∈ K ∧ ¬s ⊆ t}
  isRelLowerSet_faces := by
    intro t ht
    refine ⟨(K.isRelLowerSet_faces ht.1).1, ?_⟩
    intro u hut hu
    refine ⟨(K.isRelLowerSet_faces ht.1).2 hut hu,
      (K.isRelLowerSet_faces ht.2.1).2 (Finset.union_subset_union hut (Finset.Subset.refl _))
        (hu.mono Finset.subset_union_left), ?_⟩
    exact fun hsu ↦ ht.2.2 (hsu.trans hut)


@[simp]
theorem mem_faceShell (t : Finset ι) :
    t ∈ faceShell K s ↔ t ∈ K ∧ t ∪ s ∈ K ∧ ¬s ⊆ t := Iff.rfl


theorem faceShell_le_costar : faceShell K s ≤ faceCostar K s :=
  fun _ ht ↦ ⟨ht.1, ht.2.2⟩


theorem faceShell_le : faceShell K s ≤ K := fun _ ht ↦ ht.1


instance finite_faceShell_faces [Finite K.faces] : Finite (faceShell K s).faces :=
  Set.Finite.to_subtype ((Set.toFinite K.faces).subset (faceShell_le K s))


theorem faceShell_singleton (p : ι) : faceShell K {p} = link K {p} := by
  apply PreAbstractSimplicialComplex.ext
  ext t
  change (t ∈ K ∧ t ∪ {p} ∈ K ∧ ¬{p} ⊆ t) ↔
    (t.Nonempty ∧ Disjoint {p} t ∧ {p} ∪ t ∈ K)
  simp only [Finset.singleton_subset_iff, Finset.disjoint_singleton_left]
  constructor
  · rintro ⟨ht, htp, hp⟩
    exact ⟨(K.isRelLowerSet_faces ht).1, hp, by simpa only [Finset.union_comm] using htp⟩
  · rintro ⟨ht, hp, hpt⟩
    exact ⟨(K.isRelLowerSet_faces hpt).2 Finset.subset_union_right ht,
      by simpa only [Finset.union_comm] using hpt, hp⟩

section Geometry

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [DecidableEq E] (K : Geometry.SimplicialComplex 𝕜 E) (s : Finset E)


def geometricFaceShell : Geometry.SimplicialComplex 𝕜 E where
  toPreAbstractSimplicialComplex := faceShell K.toPreAbstractSimplicialComplex s
  indep ht := K.indep ht.1
  inter_subset_convexHull ht hu := K.inter_subset_convexHull ht.1 hu.1


@[simp]
theorem geometricFaceShell_toPreAbstractSimplicialComplex :
    (geometricFaceShell K s).toPreAbstractSimplicialComplex =
      faceShell K.toPreAbstractSimplicialComplex s := rfl


theorem geometricFaceShell_le : geometricFaceShell K s ≤ K := fun _ ht ↦ ht.1


theorem geometricFaceShell_le_costar : geometricFaceShell K s ≤ geometricFaceCostar K s :=
  fun _ ht ↦ ⟨ht.1, ht.2.2⟩


instance finite_geometricFaceShell_faces [Finite K.faces] : Finite (geometricFaceShell K s).faces :=
  inferInstanceAs (Finite (faceShell K.toPreAbstractSimplicialComplex s).faces)

theorem geometricFaceShell_singleton (p : E) : geometricFaceShell K {p} = geometricLink K {p} :=
  Geometry.SimplicialComplex.ext (congrArg PreAbstractSimplicialComplex.faces
    (faceShell_singleton K.toPreAbstractSimplicialComplex p))

end Geometry

end Poincare.Topology.SimplicialComplex
