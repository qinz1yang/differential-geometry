import DifferentialGeometry.Topology.PiecewiseLinear.ConeBaseFlat
import DifferentialGeometry.Topology.PiecewiseLinear.ConeComplex
import DifferentialGeometry.Topology.PiecewiseLinear.ConeEuler

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq (E × ℝ)]

theorem capFaces_inter_cross {A L : Geometry.SimplicialComplex ℝ (E × ℝ)} {x₀ : E}
    (h : IsConeBase ((x₀, 1) : E × ℝ) L) (hA : ∀ q ∈ A.space, (q : E × ℝ).2 = 0)
    (hLA : L.faces ⊆ A.faces) {s t : Finset (E × ℝ)} (hs : s ∈ A.faces)
    (ht : t ∈ coneFaces ((x₀, 1) : E × ℝ) L) :
    convexHull ℝ (s : Set (E × ℝ)) ∩ convexHull ℝ (t : Set (E × ℝ)) ⊆
      convexHull ℝ ((s : Set (E × ℝ)) ∩ (t : Set (E × ℝ))) := by
  rcases ht with htL | rfl | ⟨σ, hσ, rfl⟩
  · exact A.inter_subset_convexHull hs (hLA htL)
  · rintro z ⟨hzs, hzp⟩
    rw [Finset.coe_singleton, convexHull_singleton] at hzp
    have hz1 : z.2 = 1 := by rw [hzp]
    have hz0 : z.2 = 0 := hA _ (A.convexHull_subset_space hs hzs)
    rw [hz0] at hz1
    norm_num at hz1
  · rintro z ⟨hzs, hzt⟩
    have hz0 : z.2 = 0 := hA _ (A.convexHull_subset_space hs hzs)
    have hpσ : ((x₀, 1) : E × ℝ) ∉ σ := h.notMem_face hσ
    rcases exists_combo_of_mem_convexHull_insert hpσ hzt with hzp | ⟨w, hw, u, hu0, hu1, hzeq⟩
    · rw [hzp] at hz0
      norm_num at hz0
    · have hw0 : w.2 = 0 := hA _ (A.convexHull_subset_space (hLA hσ) hw)
      have hsnd : z.2 = 1 + u * (w.2 - 1) := by
        rw [hzeq]
        simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
      rw [hz0, hw0] at hsnd
      have hu : u = 1 := by linarith
      rw [hu, one_smul, add_sub_cancel] at hzeq
      have hzσ : z ∈ convexHull ℝ (σ : Set (E × ℝ)) := hzeq ▸ hw
      have hmem := A.inter_subset_convexHull hs (hLA hσ) ⟨hzs, hzσ⟩
      refine convexHull_mono (Set.inter_subset_inter_right _ ?_) hmem
      exact_mod_cast Finset.coe_subset.mpr (Finset.subset_insert ((x₀, 1) : E × ℝ) σ)

def capComplex (A L : Geometry.SimplicialComplex ℝ (E × ℝ)) {x₀ : E}
    (h : IsConeBase ((x₀, 1) : E × ℝ) L) (hA : ∀ q ∈ A.space, (q : E × ℝ).2 = 0)
    (hLA : L.faces ⊆ A.faces) : Geometry.SimplicialComplex ℝ (E × ℝ) where
  faces := A.faces ∪ coneFaces ((x₀, 1) : E × ℝ) L
  isRelLowerSet_faces :=
    IsRelLowerSet.union A.isRelLowerSet_faces (coneFaces_isRelLowerSet ((x₀, 1) : E × ℝ) L)
  indep := by
    rintro t (ht | ht)
    · exact A.indep ht
    · exact coneFaces_indep h ht
  inter_subset_convexHull := by
    rintro s t (hs | hs) (ht | ht)
    · exact A.inter_subset_convexHull hs ht
    · exact capFaces_inter_cross h hA hLA hs ht
    · intro z hz
      have hz' : z ∈ convexHull ℝ (t : Set (E × ℝ)) ∩ convexHull ℝ (s : Set (E × ℝ)) :=
        ⟨hz.2, hz.1⟩
      have hmem := capFaces_inter_cross h hA hLA ht hs hz'
      rwa [Set.inter_comm] at hmem
    · exact coneFaces_inter h hs ht

theorem capComplex_faces (A L : Geometry.SimplicialComplex ℝ (E × ℝ)) {x₀ : E}
    (h : IsConeBase ((x₀, 1) : E × ℝ) L) (hA : ∀ q ∈ A.space, (q : E × ℝ).2 = 0)
    (hLA : L.faces ⊆ A.faces) :
    (capComplex A L h hA hLA).faces = A.faces ∪ (coneComplex h).faces := rfl

theorem capComplex_faces_finite (A L : Geometry.SimplicialComplex ℝ (E × ℝ)) {x₀ : E}
    (h : IsConeBase ((x₀, 1) : E × ℝ) L) (hA : ∀ q ∈ A.space, (q : E × ℝ).2 = 0)
    (hLA : L.faces ⊆ A.faces) (hAfin : A.faces.Finite) (hLfin : L.faces.Finite) :
    (capComplex A L h hA hLA).faces.Finite :=
  hAfin.union (coneComplex_faces_finite h hLfin)

end General

section Euler

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq (E × ℝ)]

theorem intersectionComplex_capComplex_faces (A L : Geometry.SimplicialComplex ℝ (E × ℝ))
    {x₀ : E} (h : IsConeBase ((x₀, 1) : E × ℝ) L) (hA : ∀ q ∈ A.space, (q : E × ℝ).2 = 0)
    (hLA : L.faces ⊆ A.faces) :
    (intersectionComplex A (coneComplex h)).faces = L.faces := by
  ext σ
  constructor
  · rintro ⟨hσA, hσc⟩
    rcases hσc with hσL | rfl | ⟨τ, hτ, rfl⟩
    · exact hσL
    · have hp : ((x₀, 1) : E × ℝ) ∈ A.space :=
        A.convexHull_subset_space hσA (subset_convexHull ℝ _ (by simp))
      have := hA _ hp
      norm_num at this
    · have hp : ((x₀, 1) : E × ℝ) ∈ A.space :=
        A.convexHull_subset_space hσA
          (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_insert_self _ _)))
      have := hA _ hp
      norm_num at this
  · intro hσ
    exact ⟨hLA hσ, Or.inl hσ⟩

omit [DecidableEq (E × ℝ)] in
theorem space_eq_of_faces_eq {K K' : Geometry.SimplicialComplex ℝ (E × ℝ)}
    (hfaces : K.faces = K'.faces) : K.space = K'.space := by
  ext x
  rw [K.mem_space_iff, K'.mem_space_iff, hfaces]

theorem eulerChar_capComplex [FiniteDimensional ℝ E]
    (A L : Geometry.SimplicialComplex ℝ (E × ℝ)) {x₀ : E}
    (h : IsConeBase ((x₀, 1) : E × ℝ) L) (hA : ∀ q ∈ A.space, (q : E × ℝ).2 = 0)
    (hLA : L.faces ⊆ A.faces) [Finite A.faces] [Finite L.faces]
    [Finite (coneComplex h).faces] [Finite (capComplex A L h hA hLA).faces]
    (hL : IsPLSphere 1 L.space) :
    eulerChar (capComplex A L h hA hLA) = eulerChar A + 1 := by
  refine eulerChar_eq_add_one_of_faces_union_coneComplex _ A h rfl ?_
  rw [space_eq_of_faces_eq (intersectionComplex_capComplex_faces A L h hA hLA)]
  exact hL

end Euler

end DifferentialGeometry.Topology.PiecewiseLinear
