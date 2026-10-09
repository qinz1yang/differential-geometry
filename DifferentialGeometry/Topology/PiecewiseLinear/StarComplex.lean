/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Gluing
import DifferentialGeometry.Topology.PiecewiseLinear.LinkSubdivision

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

section Star

variable [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E) (v : E)

def starComplex : Geometry.SimplicialComplex ℝ E where
  faces := {s ∈ K.faces | insert v s ∈ K.faces}
  isRelLowerSet_faces := by
    rintro s ⟨hs, hvs⟩
    exact ⟨K.nonempty_of_mem_faces hs, fun t hts ht => ⟨K.down_closed hs hts ht,
      K.down_closed hvs (Finset.insert_subset_insert v hts) (Finset.insert_nonempty v t)⟩⟩
  indep hs := K.indep hs.1
  inter_subset_convexHull hs ht := K.inter_subset_convexHull hs.1 ht.1

theorem mem_starComplex_faces_iff {s : Finset E} :
    s ∈ (starComplex K v).faces ↔ s ∈ K.faces ∧ insert v s ∈ K.faces := Iff.rfl

theorem starComplex_faces_subset : (starComplex K v).faces ⊆ K.faces := fun _ hs => hs.1

theorem starComplex_faces_finite [Finite K.faces] : (starComplex K v).faces.Finite :=
  (Set.toFinite K.faces).subset (starComplex_faces_subset K v)

theorem starComplex_space (hv : {v} ∈ K.faces) : (starComplex K v).space = closedStar K v := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s, ⟨hs, hvs⟩, hxs⟩ := (starComplex K v).mem_space_iff.mp hx
    refine mem_biUnion (x := insert v s) ⟨hvs, subset_convexHull ℝ _ (by simp)⟩ ?_
    exact convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert v s)) hxs
  · intro x hx
    obtain ⟨s, ⟨hs, hvs⟩, hxs⟩ := mem_iUnion₂.mp hx
    have hvs' : v ∈ s := mem_of_mem_convexHull_of_singleton_mem K hv hs hvs
    refine (starComplex K v).convexHull_subset_space ⟨hs, ?_⟩ hxs
    rw [Finset.insert_eq_of_mem hvs']
    exact hs

theorem geometricLink_starComplex :
    SimplicialComplex.geometricLink (starComplex K v) {v} = SimplicialComplex.geometricLink K {v} :=
        by
  ext t
  rw [SimplicialComplex.mem_geometricLink_singleton, SimplicialComplex.mem_geometricLink_singleton,
    mem_starComplex_faces_iff, Finset.insert_idem]
  tauto

theorem singleton_mem_starComplex (hv : {v} ∈ K.faces) : {v} ∈ (starComplex K v).faces := by
  refine ⟨hv, ?_⟩
  rw [Finset.insert_eq_of_mem (Finset.mem_singleton_self v)]
  exact hv

end Star

section LinkIso

variable [DecidableEq E] [DecidableEq F] {K : Geometry.SimplicialComplex ℝ E}
  {L : Geometry.SimplicialComplex ℝ F} {φ : E → F} {φ' : F → E}

theorem IsGlueIso.isPLHomeomorphOn [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [Finite K.faces] [Finite L.faces] (h : IsGlueIso K L φ φ') :
    IsPLHomeomorphOn (simplicialMap K φ) K.space L.space :=
  isPLHomeomorphOn_simplicialMap K L φ φ' h.image₁ h.image₂ h.left h.right

theorem IsGlueIso.notMem_image (h : IsGlueIso K L φ φ') {t : Finset E} {v : E}
    (hvt : insert v t ∈ K.faces) (hv : v ∉ t) : φ v ∉ t.image φ := by
  intro hmem
  obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hmem
  have h1 := h.left _ hvt w (Finset.mem_insert_of_mem hw)
  have h2 := h.left _ hvt v (Finset.mem_insert_self v t)
  rw [hwv] at h1
  rw [h1] at h2
  exact hv (h2 ▸ hw)

theorem IsGlueIso.geometricLink (h : IsGlueIso K L φ φ') {v : E} (hv : {v} ∈ K.faces) :
    IsGlueIso (SimplicialComplex.geometricLink K {v}) (SimplicialComplex.geometricLink L {φ v})
      φ φ' := by
  have hφv : {φ v} ∈ L.faces := h.singleton_mem hv
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [SimplicialComplex.mem_geometricLink_singleton] at ht ⊢
    obtain ⟨htne, hvt, hins⟩ := ht
    refine ⟨htne.image φ, h.notMem_image hins hvt, ?_⟩
    rw [← Finset.image_insert]
    exact h.image₁ _ hins
  · intro t ht
    rw [SimplicialComplex.mem_geometricLink_singleton] at ht ⊢
    obtain ⟨htne, hvt, hins⟩ := ht
    have hins' := h.image₂ _ hins
    rw [Finset.image_insert, h.left _ hv v (Finset.mem_singleton_self v)] at hins'
    refine ⟨htne.image φ', ?_, hins'⟩
    have := h.symm.notMem_image hins hvt
    rwa [h.left _ hv v (Finset.mem_singleton_self v)] at this
  · intro t ht w hw
    rw [SimplicialComplex.mem_geometricLink_singleton] at ht
    exact h.left _ ht.2.2 w (Finset.mem_insert_of_mem hw)
  · intro t ht u hu
    rw [SimplicialComplex.mem_geometricLink_singleton] at ht
    exact h.right _ ht.2.2 u (Finset.mem_insert_of_mem hu)

theorem IsGlueIso.isPLSphere_geometricLink [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [Finite K.faces] [Finite L.faces] (h : IsGlueIso K L φ φ') {v : E} (hv : {v} ∈ K.faces)
    {n : ℕ} (hL : IsPLSphere n (SimplicialComplex.geometricLink L {φ v}).space) :
    IsPLSphere n (SimplicialComplex.geometricLink K {v}).space := by
  have hfinK : Finite (SimplicialComplex.geometricLink K {v}).faces :=
    ((Set.toFinite K.faces).subset (SimplicialComplex.geometricLink_le K {v})).to_subtype
  have hfinL : Finite (SimplicialComplex.geometricLink L {φ v}).faces :=
    ((Set.toFinite L.faces).subset (SimplicialComplex.geometricLink_le L {φ v})).to_subtype
  exact hL.of_isPLHomeomorphOn (h.geometricLink hv).symm.isPLHomeomorphOn

end LinkIso

end DifferentialGeometry.Topology.PiecewiseLinear
