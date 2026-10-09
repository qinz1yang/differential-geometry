/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GenericVertexMapLinesPlanes
import DifferentialGeometry.Topology.PiecewiseLinear.AdmissibleVertexMapVocabulary
import DifferentialGeometry.Topology.PiecewiseLinear.WallChartLocalPicture
import DifferentialGeometry.Topology.PiecewiseLinear.GenericDoublePointSheets
import DifferentialGeometry.Topology.PiecewiseLinear.GluedDoublePointFaces

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem simplicialMap_eq_of_eqOn_affineMap {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (K : Geometry.SimplicialComplex ℝ E) (f : E → F)
    {s : Finset E} (hs : s ∈ K.faces) {A : E →ᵃ[ℝ] F} (hA : EqOn f A (convexHull ℝ (s : Set E)))
    {x : E} (hx : x ∈ convexHull ℝ (s : Set E)) : simplicialMap K f x = f x := by
  rw [simplicialMap_eq_of_mem K f hs hx, hA hx]
  have hw := sum_weights hx
  have h1 : ∑ v ∈ s, weights s x v • v = s.affineCombination ℝ id (weights s x) :=
    (Finset.affineCombination_eq_linear_combination s id (weights s x) hw).symm
  have h2 : ∑ v ∈ s, weights s x v • A v = s.affineCombination ℝ (A ∘ id) (weights s x) :=
    (Finset.affineCombination_eq_linear_combination s (A ∘ id) (weights s x) hw).symm
  calc ∑ v ∈ s, weights s x v • f v
      = ∑ v ∈ s, weights s x v • A v := Finset.sum_congr rfl fun v hv => by
          rw [hA (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv))]
    _ = A (∑ v ∈ s, weights s x v • v) := by
        rw [h1, h2, Finset.map_affineCombination s id (weights s x) hw A]
    _ = A x := by rw [sum_weights_smul hx]

open Classical in
theorem faces_cases_of_simplicialMap_eq_of_guard
    {R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    {Bv : Finset (EuclideanSpace ℝ (Fin 2))}
    {φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} (hℓ : ℓ ≠ 0)
    (hguard : ∀ s : Finset (EuclideanSpace ℝ (Fin 2)),
      (s : Set (EuclideanSpace ℝ (Fin 2))) ⊆ R.vertices → s.card ≤ 4 →
        (s ∩ Bv).card ≤ Module.finrank ℝ (LinearMap.ker ℓ) + 1 →
        AffineIndependent ℝ
          (fun v : (s.filter fun x => x ∈ Ac.space) => φ (v : EuclideanSpace ℝ (Fin 2))) →
        AffineIndependent ℝ (fun v : s => φ (v : EuclideanSpace ℝ (Fin 2))))
    (htri : ∀ σ ∈ R.faces, σ.card = 3 → ¬σ ⊆ Bv)
    {σ₁ σ₂ : Finset (EuclideanSpace ℝ (Fin 2))} (hσ₁ : σ₁ ∈ R.faces) (hσ₂ : σ₂ ∈ R.faces)
    (hfr₁ : ∀ v ∈ σ₁, v ∉ Ac.space) (hfr₂ : ∀ v ∈ σ₂, v ∉ Ac.space)
    {x₁ x₂ : EuclideanSpace ℝ (Fin 2)} (hx₁ : x₁ ∈ openSimplex σ₁) (hx₂ : x₂ ∈ openSimplex σ₂)
    (hne : x₁ ≠ x₂) (heq : simplicialMap R φ x₁ = simplicialMap R φ x₂) :
    (σ₁.card = 3 ∧ σ₂.card = 3 ∧ (σ₁ ∩ σ₂).card ≤ 1) ∨
      (σ₁.card = 2 ∧ σ₂.card = 3 ∧ Disjoint σ₁ σ₂) ∨
      (σ₁.card = 3 ∧ σ₂.card = 2 ∧ Disjoint σ₁ σ₂) ∨
      (σ₁.card = 2 ∧ σ₂.card = 2 ∧ Disjoint σ₁ σ₂ ∧ σ₁ ∪ σ₂ ⊆ Bv) := by
  have hvert : ∀ σ ∈ R.faces, (σ : Set (EuclideanSpace ℝ (Fin 2))) ⊆ R.vertices :=
    fun σ hσ v hv => R.down_closed hσ (Finset.singleton_subset_iff.mpr (Finset.mem_coe.mp hv))
      (Finset.singleton_nonempty v)
  have hcard3 : ∀ σ ∈ R.faces, σ.card ≤ 3 := by
    intro σ hσ
    have h := (R.indep hσ).card_le_finrank_succ
    have h2 := Submodule.finrank_le
      (vectorSpan ℝ (Set.range ((↑) : σ → EuclideanSpace ℝ (Fin 2))))
    rw [Fintype.card_coe] at h
    rw [finrank_euclideanSpace_fin] at h2
    omega
  have hx₁h := openSimplex_subset_convexHull σ₁ hx₁
  have hx₂h := openSimplex_subset_convexHull σ₂ hx₂
  have key : (σ₁ ∪ σ₂).card ≤ 4 → ((σ₁ ∪ σ₂) ∩ Bv).card ≤ 3 → False := by
    intro h4 h3
    have hsR : ((σ₁ ∪ σ₂ : Finset _) : Set (EuclideanSpace ℝ (Fin 2))) ⊆ R.vertices := by
      rw [Finset.coe_union]
      exact union_subset (hvert σ₁ hσ₁) (hvert σ₂ hσ₂)
    have hfree : ∀ v ∈ σ₁ ∪ σ₂, v ∉ Ac.space := by
      intro v hv
      rcases Finset.mem_union.mp hv with h | h
      · exact hfr₁ v h
      · exact hfr₂ v h
    exact hne (eq_of_simplicialMap_eq_of_affineIndependent R φ hσ₁ hσ₂ hx₁h hx₂h
      (affineIndependent_of_wallGuard hℓ hguard hsR h4 h3 hfree) heq)
  have hc₁ := hcard3 σ₁ hσ₁
  have hc₂ := hcard3 σ₂ hσ₂
  have hui := Finset.card_union_add_card_inter σ₁ σ₂
  by_cases hB : σ₁ ∪ σ₂ ⊆ Bv
  · have h1 : σ₁.card ≤ 2 := by
      by_contra h
      exact htri σ₁ hσ₁ (by omega) (Finset.subset_union_left.trans hB)
    have h2 : σ₂.card ≤ 2 := by
      by_contra h
      exact htri σ₂ hσ₂ (by omega) (Finset.subset_union_right.trans hB)
    have hinter : (σ₁ ∪ σ₂) ∩ Bv = σ₁ ∪ σ₂ := Finset.inter_eq_left.mpr hB
    by_cases h4 : (σ₁ ∪ σ₂).card ≤ 3
    · exact (key (by omega) (by rw [hinter]; exact h4)).elim
    · have hdis : (σ₁ ∩ σ₂).card = 0 := by omega
      exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega,
        Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hdis), hB⟩))
  · have hlt : ((σ₁ ∪ σ₂) ∩ Bv).card < (σ₁ ∪ σ₂).card := by
      refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left,
        fun h => hB ?_⟩)
      rw [← h]
      exact Finset.inter_subset_right
    have h5 : 5 ≤ (σ₁ ∪ σ₂).card := by
      by_contra h
      exact key (by omega) (by omega)
    by_cases h0 : (σ₁ ∩ σ₂).card = 0
    · have hdisj : Disjoint σ₁ σ₂ :=
        Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp h0)
      have hcases : (σ₁.card = 3 ∧ σ₂.card = 3) ∨ (σ₁.card = 2 ∧ σ₂.card = 3) ∨
          (σ₁.card = 3 ∧ σ₂.card = 2) := by omega
      rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2, by omega⟩
      · exact Or.inr (Or.inl ⟨h1, h2, hdisj⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, hdisj⟩))
    · exact Or.inl ⟨by omega, by omega, by omega⟩

section MetricAmbient

variable {M : Type u} [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]

theorem not_subset_boundary_of_card_eq_three_of_eqOn_affineMap (D : SingularTwoCell M)
    {BdM V : Set M} (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hVec : V ⊆ ec.source) (hBdchart : ∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)
    {Rc R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))} (hsub : IsSubdivision R Rc)
    (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    {Bv : Finset (EuclideanSpace ℝ (Fin 2))}
    (hB0 : ∀ v ∈ R.vertices, v ∈ Bv → ℓ (ec (D v)) = 0)
    {σ : Finset (EuclideanSpace ℝ (Fin 2))} (hσ : σ ∈ R.faces) (h3 : σ.card = 3)
    {A : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)}
    (hA : EqOn (fun x => ec (D x)) A (convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))))) :
    ¬σ ⊆ Bv := by
  intro hB
  have hσR : ∀ z ∈ convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))), z ∈ Rc.space :=
    fun z hz => hsub.space_eq ▸ R.convexHull_subset_space hσ hz
  have hzero : convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))) ⊆
      (ℓ.toAffineMap.comp A) ⁻¹' {0} := by
    refine convexHull_min (fun v hv => ?_) ((convex_singleton (0 : ℝ)).affine_preimage _)
    have hvV : v ∈ R.vertices := R.down_closed hσ (Finset.singleton_subset_iff.mpr hv)
      (Finset.singleton_nonempty v)
    have h0 : ℓ (ec (D v)) = 0 := hB0 v hvV (hB hv)
    have hAv : ec (D v) = A v := hA (subset_convexHull ℝ _ hv)
    rw [hAv] at h0
    exact h0
  have hint : interior (convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2)))) = openSimplex σ :=
    interior_convexHull_eq_openSimplex (R.indep hσ) (by rw [h3, finrank_euclideanSpace_fin])
  have hc := centroid_mem_openSimplex (R.nonempty_of_mem_faces hσ)
  rw [← hint] at hc
  have hcR := hσR _ (interior_subset hc)
  have hcS : σ.centroid ℝ id ∈ interior D.domain :=
    interior_mono (fun z hz => hRdom (hσR z hz)) hc
  have hAc : ec (D (σ.centroid ℝ id)) = A (σ.centroid ℝ id) := hA (interior_subset hc)
  have hℓc : ℓ (ec (D (σ.centroid ℝ id))) = 0 := by
    rw [hAc]
    exact hzero (interior_subset hc)
  have hBd : D (σ.centroid ℝ id) ∈ BdM := (hBdchart _ (hVec (hRV hcR))).mpr hℓc
  have hfr : σ.centroid ℝ id ∈ frontier D.domain := by
    rw [← hproper]
    exact ⟨hRdom hcR, hBd⟩
  exact hfr.2 hcS

open Classical in
theorem notMem_wallSystemSkeleton_of_generic (D : SingularTwoCell M) {Eb : Set M}
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) {Q : Geometry.SimplicialComplex ℝ Ea}
    {ρ : M → Ea} {Rc Ac R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    (hsub : IsSubdivision R Rc) {Bv Vf : Finset (EuclideanSpace ℝ (Fin 2))}
    {φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    (hguard : ∀ s : Finset (EuclideanSpace ℝ (Fin 2)),
      (s : Set (EuclideanSpace ℝ (Fin 2))) ⊆ R.vertices → s.card ≤ 4 →
        (s ∩ Bv).card ≤ Module.finrank ℝ (LinearMap.ker ℓ) + 1 →
        AffineIndependent ℝ
          (fun v : (s.filter fun x => x ∈ Ac.space) => φ (v : EuclideanSpace ℝ (Fin 2))) →
        AffineIndependent ℝ (fun v : s => φ (v : EuclideanSpace ℝ (Fin 2))))
    (htri : ∀ σ ∈ R.faces, σ.card = 3 → ¬σ ⊆ Bv)
    (hsubVf : ∀ σ ∈ R.faces, (∀ v ∈ σ, v ∉ Ac.space) → σ ⊆ Vf)
    (hgR : ∀ x ∈ Rc.space, regionGluedMap D ec R φ Rc x ∈ Eb ∧
      ec (regionGluedMap D ec R φ Rc x) = simplicialMap R φ x)
    {ιS : Type*} (S : ιS → AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
    (hSk : ∀ y ∈ Eb, y ∈ wallSystemSkeleton Q ρ → ∃ j, ec y ∈ S j)
    (hskel : ∀ α ⊆ Vf, ∀ β ⊆ Vf,
      ((α.card = 3 ∧ β.card = 3 ∧ ¬α ⊆ Bv ∧ ¬β ⊆ Bv ∧ (α ∩ β).card ≤ 1) ∨
        (α.card = 3 ∧ ¬α ⊆ Bv ∧ β.card = 2 ∧ Disjoint α β) ∨
        (α.card = 2 ∧ β.card = 2 ∧ α ⊆ Bv ∧ β ⊆ Bv ∧ Disjoint α β)) →
      ∀ j (w w' : EuclideanSpace ℝ (Fin 2) → ℝ), (∀ u ∈ α, 0 < w u) → ∑ u ∈ α, w u = 1 →
        (∀ u ∈ β, 0 < w' u) → ∑ u ∈ β, w' u = 1 → ∑ u ∈ α, w u • φ u = ∑ u ∈ β, w' u • φ u →
          ∑ u ∈ α, w u • φ u ∉ S j) :
    ∀ y ∈ doublePointSet (regionGluedMap D ec R φ Rc) D.domain,
      FreeSourceGerm R Ac (regionGluedMap D ec R φ Rc) D.domain y →
        y ∉ wallSystemSkeleton Q ρ := by
  rintro y ⟨x₁, hx₁S, x₂, hx₂S, hne, hgx₁, hgx₂⟩ hfree hyskel
  have hG₁ := hfree x₁ ⟨hx₁S, hgx₁⟩
  have hG₂ := hfree x₂ ⟨hx₂S, hgx₂⟩
  have hx₁R : x₁ ∈ R.space := mem_of_mem_nhdsWithin hx₁S hG₁.1
  have hx₂R : x₂ ∈ R.space := mem_of_mem_nhdsWithin hx₂S hG₂.1
  have hRx₁ : x₁ ∈ Rc.space := hsub.space_eq ▸ hx₁R
  have hRx₂ : x₂ ∈ Rc.space := hsub.space_eq ▸ hx₂R
  have hσ₁ := carrierFace_mem hx₁R
  have hσ₂ := carrierFace_mem hx₂R
  have hx₁o := mem_openSimplex_carrierFace hx₁R
  have hx₂o := mem_openSimplex_carrierFace hx₂R
  have hfr₁ := hG₁.2 _ hσ₁ (mem_convexHull_carrierFace hx₁R)
  have hfr₂ := hG₂.2 _ hσ₂ (mem_convexHull_carrierFace hx₂R)
  have hpeq : simplicialMap R φ x₁ = simplicialMap R φ x₂ := by
    rw [← (hgR x₁ hRx₁).2, ← (hgR x₂ hRx₂).2, hgx₁, hgx₂]
  have hcases := faces_cases_of_simplicialMap_eq_of_guard hℓ hguard htri hσ₁ hσ₂ hfr₁ hfr₂
    hx₁o hx₂o hne hpeq
  have hyE : y ∈ Eb := hgx₁ ▸ (hgR x₁ hRx₁).1
  obtain ⟨j, hj⟩ := hSk y hyE hyskel
  have hzS : simplicialMap R φ x₁ ∈ S j := by
    rw [← (hgR x₁ hRx₁).2, hgx₁]
    exact hj
  have hx₁h := openSimplex_subset_convexHull _ hx₁o
  have hx₂h := openSimplex_subset_convexHull _ hx₂o
  have hw₁p : ∀ v ∈ carrierFace R x₁, 0 < weights (carrierFace R x₁) x₁ v := fun v hv =>
    ((mem_openSimplex_iff_weights_pos (R.indep hσ₁) subset_rfl hx₁h).mp hx₁o v hv).mpr hv
  have hw₂p : ∀ v ∈ carrierFace R x₂, 0 < weights (carrierFace R x₂) x₂ v := fun v hv =>
    ((mem_openSimplex_iff_weights_pos (R.indep hσ₂) subset_rfl hx₂h).mp hx₂o v hv).mpr hv
  have hp₁ := simplicialMap_eq_of_mem R φ hσ₁ hx₁h
  have hp₂ := simplicialMap_eq_of_mem R φ hσ₂ hx₂h
  have hσ₁V := hsubVf _ hσ₁ hfr₁
  have hσ₂V := hsubVf _ hσ₂ hfr₂
  have hsums : ∑ v ∈ carrierFace R x₁, weights (carrierFace R x₁) x₁ v • φ v =
      ∑ v ∈ carrierFace R x₂, weights (carrierFace R x₂) x₂ v • φ v := by
    rw [← hp₁, ← hp₂, hpeq]
  have hz₁ : ∑ v ∈ carrierFace R x₁, weights (carrierFace R x₁) x₁ v • φ v ∈ S j := by
    rw [← hp₁]
    exact hzS
  have hz₂ : ∑ v ∈ carrierFace R x₂, weights (carrierFace R x₂) x₂ v • φ v ∈ S j := by
    rw [← hp₂, ← hpeq]
    exact hzS
  rcases hcases with ⟨h3₁, h3₂, hint⟩ | ⟨h2₁, h3₂, hd⟩ | ⟨h3₁, h2₂, hd⟩ | ⟨h2₁, h2₂, hd, hB⟩
  · exact hskel _ hσ₁V _ hσ₂V (Or.inl ⟨h3₁, h3₂, htri _ hσ₁ h3₁, htri _ hσ₂ h3₂, hint⟩) j _ _
      hw₁p (sum_weights hx₁h) hw₂p (sum_weights hx₂h) hsums hz₁
  · exact hskel _ hσ₂V _ hσ₁V (Or.inr (Or.inl ⟨h3₂, htri _ hσ₂ h3₂, h2₁, hd.symm⟩)) j _ _
      hw₂p (sum_weights hx₂h) hw₁p (sum_weights hx₁h) hsums.symm hz₂
  · exact hskel _ hσ₁V _ hσ₂V (Or.inr (Or.inl ⟨h3₁, htri _ hσ₁ h3₁, h2₂, hd⟩)) j _ _
      hw₁p (sum_weights hx₁h) hw₂p (sum_weights hx₂h) hsums hz₁
  · exact hskel _ hσ₁V _ hσ₂V (Or.inr (Or.inr ⟨h2₁, h2₂, Finset.subset_union_left.trans hB,
      Finset.subset_union_right.trans hB, hd⟩)) j _ _ hw₁p (sum_weights hx₁h) hw₂p
      (sum_weights hx₂h) hsums hz₁

open Classical in
theorem notMem_wallSystemCell_of_generic_edge (D : SingularTwoCell M) {BdM Eb : Set M}
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hker : Module.finrank ℝ (LinearMap.ker ℓ) = 2)
    (hBdchart : ∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0) {Q : Geometry.SimplicialComplex ℝ Ea}
    {ρ : M → Ea} {Rc Ac R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    (hsub : IsSubdivision R Rc) (hRdom : Rc.space ⊆ D.domain)
    {Bv Vf : Finset (EuclideanSpace ℝ (Fin 2))}
    {φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    (hguard : ∀ s : Finset (EuclideanSpace ℝ (Fin 2)),
      (s : Set (EuclideanSpace ℝ (Fin 2))) ⊆ R.vertices → s.card ≤ 4 →
        (s ∩ Bv).card ≤ Module.finrank ℝ (LinearMap.ker ℓ) + 1 →
        AffineIndependent ℝ
          (fun v : (s.filter fun x => x ∈ Ac.space) => φ (v : EuclideanSpace ℝ (Fin 2))) →
        AffineIndependent ℝ (fun v : s => φ (v : EuclideanSpace ℝ (Fin 2))))
    (htri : ∀ σ ∈ R.faces, σ.card = 3 → ¬σ ⊆ Bv)
    (hℓv : ∀ v ∈ R.vertices, (v ∈ Bv → ℓ (φ v) = 0) ∧ (v ∉ Bv → 0 < ℓ (φ v)))
    (hsubVf : ∀ σ ∈ R.faces, (∀ v ∈ σ, v ∉ Ac.space) → σ ⊆ Vf)
    (hgR : ∀ x ∈ Rc.space, regionGluedMap D ec R φ Rc x ∈ Eb ∧
      regionGluedMap D ec R φ Rc x ∈ ec.source ∧
        ec (regionGluedMap D ec R φ Rc x) = simplicialMap R φ x)
    {ιP : Type*} (P : ιP → AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
    (hP : ∀ j, Module.finrank ℝ (P j).direction ≤ 2)
    (hPw : ∀ y ∈ Eb, ∀ w ∈ wallSystemWalls Q, y ∈ wallSystemCell ρ w →
      ∃ j, ∀ x ∈ wallSystemCell ρ w, ec x ∈ P j)
    (hfold : ∀ α ⊆ Vf, ∀ β ⊆ Vf, α.card = 3 → ¬α ⊆ Bv → β.card = 2 → ¬β ⊆ Bv →
      Disjoint α β → ∀ j, ¬(LinearMap.ker ℓ).toAffineSubspace ≤ P j →
        ∀ w w' : EuclideanSpace ℝ (Fin 2) → ℝ, (∀ u ∈ α, 0 < w u) → ∑ u ∈ α, w u = 1 →
          (∀ u ∈ β, 0 < w' u) → ∑ u ∈ β, w' u = 1 →
          ∑ u ∈ α, w u • φ u = ∑ u ∈ β, w' u • φ u → ∑ u ∈ α, w u • φ u ∉ P j) :
    ∀ y ∈ doublePointSet (regionGluedMap D ec R φ Rc) D.domain,
      IsFreeDoubleGerm R Ac (regionGluedMap D ec R φ Rc) D.domain BdM y →
        ∀ σ ∈ R.faces, σ.card ≤ 2 →
          y ∈ regionGluedMap D ec R φ Rc ''
              (Rc.space ∩ convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2)))) →
            ∀ w ∈ wallSystemWalls Q, y ∉ wallSystemCell ρ w := by
  intro y hyd hfree σ hσ hσ2 hyim w hw hyw
  obtain ⟨hyB, hfr⟩ := hfree
  obtain ⟨x₁, ⟨hRx₁, hx₁σ⟩, hgx₁⟩ := hyim
  obtain ⟨a, haS, b, hbS, hab, hga, hgb⟩ := hyd
  obtain ⟨x₂, hx₂S, hne, hgx₂⟩ : ∃ x₂ ∈ D.domain, x₁ ≠ x₂ ∧
      regionGluedMap D ec R φ Rc x₂ = y := by
    by_cases hax : a = x₁
    · exact ⟨b, hbS, fun h => hab (hax.trans h), hgb⟩
    · exact ⟨a, haS, fun h => hax h.symm, hga⟩
  have hx₁S : x₁ ∈ D.domain := hRdom hRx₁
  have hG₁ := hfr x₁ ⟨hx₁S, hgx₁⟩
  have hG₂ := hfr x₂ ⟨hx₂S, hgx₂⟩
  have hx₁R : x₁ ∈ R.space := mem_of_mem_nhdsWithin hx₁S hG₁.1
  have hx₂R : x₂ ∈ R.space := mem_of_mem_nhdsWithin hx₂S hG₂.1
  have hRx₂ : x₂ ∈ Rc.space := hsub.space_eq ▸ hx₂R
  have hσ₁ := carrierFace_mem hx₁R
  have hσ₂ := carrierFace_mem hx₂R
  have hx₁o := mem_openSimplex_carrierFace hx₁R
  have hx₂o := mem_openSimplex_carrierFace hx₂R
  have hfr₁ := hG₁.2 _ hσ₁ (mem_convexHull_carrierFace hx₁R)
  have hfr₂ := hG₂.2 _ hσ₂ (mem_convexHull_carrierFace hx₂R)
  have hc₁ : (carrierFace R x₁).card ≤ 2 :=
    (Finset.card_le_card (carrierFace_subset hx₁R hσ hx₁σ)).trans hσ2
  have hpeq : simplicialMap R φ x₁ = simplicialMap R φ x₂ := by
    rw [← (hgR x₁ hRx₁).2.2, ← (hgR x₂ hRx₂).2.2, hgx₁, hgx₂]
  have hcases := faces_cases_of_simplicialMap_eq_of_guard hℓ hguard htri hσ₁ hσ₂ hfr₁ hfr₂
    hx₁o hx₂o hne hpeq
  have hx₁h := openSimplex_subset_convexHull _ hx₁o
  have hx₂h := openSimplex_subset_convexHull _ hx₂o
  have hw₁p : ∀ v ∈ carrierFace R x₁, 0 < weights (carrierFace R x₁) x₁ v := fun v hv =>
    ((mem_openSimplex_iff_weights_pos (R.indep hσ₁) subset_rfl hx₁h).mp hx₁o v hv).mpr hv
  have hw₂p : ∀ v ∈ carrierFace R x₂, 0 < weights (carrierFace R x₂) x₂ v := fun v hv =>
    ((mem_openSimplex_iff_weights_pos (R.indep hσ₂) subset_rfl hx₂h).mp hx₂o v hv).mpr hv
  have hp₁ := simplicialMap_eq_of_mem R φ hσ₁ hx₁h
  have hp₂ := simplicialMap_eq_of_mem R φ hσ₂ hx₂h
  have hvert : ∀ v ∈ carrierFace R x₁, v ∈ R.vertices := fun v hv =>
    R.down_closed hσ₁ (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  have hℓz : ℓ (simplicialMap R φ x₁) =
      ∑ v ∈ carrierFace R x₁, weights (carrierFace R x₁) x₁ v * ℓ (φ v) := by
    rw [hp₁, map_sum]
    simp only [map_smul, smul_eq_mul]
  have hzy : simplicialMap R φ x₁ = ec y := by
    rw [← (hgR x₁ hRx₁).2.2, hgx₁]
  have hysrc : y ∈ ec.source := hgx₁ ▸ (hgR x₁ hRx₁).2.1
  have hyE : y ∈ Eb := hgx₁ ▸ (hgR x₁ hRx₁).1
  have hnotB : ¬carrierFace R x₁ ⊆ Bv := fun hB => hyB ((hBdchart y hysrc).mpr (by
    rw [← hzy, hℓz]
    exact Finset.sum_eq_zero fun u hu => by rw [((hℓv u (hvert u hu)).1 (hB hu)), mul_zero]))
  have hpos : 0 < ℓ (simplicialMap R φ x₁) := by
    rw [hℓz]
    obtain ⟨v, hvσ, hvB⟩ := Finset.not_subset.mp hnotB
    refine Finset.sum_pos' (fun u hu => mul_nonneg (hw₁p u hu).le ?_)
      ⟨v, hvσ, mul_pos (hw₁p v hvσ) ((hℓv v (hvert v hvσ)).2 hvB)⟩
    by_cases huB : u ∈ Bv
    · exact ((hℓv u (hvert u hu)).1 huB).ge
    · exact ((hℓv u (hvert u hu)).2 huB).le
  rcases hcases with ⟨h3₁, -, -⟩ | ⟨h2₁, h3₂, hd⟩ | ⟨h3₁, -, -⟩ | ⟨-, -, -, hB⟩
  · omega
  · obtain ⟨j, hj⟩ := hPw y hyE w hw hyw
    have hzP : simplicialMap R φ x₁ ∈ P j := by
      rw [hzy]
      exact hj y hyw
    by_cases hkerle : (LinearMap.ker ℓ).toAffineSubspace ≤ P j
    · have heq := eq_of_le_of_finrank_direction_le hkerle
        ⟨0, Submodule.mem_toAffineSubspace.mpr (Submodule.zero_mem _)⟩
        (by rw [Submodule.toAffineSubspace_direction, hker]; exact hP j)
      rw [← heq] at hzP
      exact hpos.ne' (LinearMap.mem_ker.mp (Submodule.mem_toAffineSubspace.mp hzP))
    · have hz₂ : ∑ v ∈ carrierFace R x₂, weights (carrierFace R x₂) x₂ v • φ v ∈ P j := by
        rw [← hp₂, ← hpeq]
        exact hzP
      exact hfold _ (hsubVf _ hσ₂ hfr₂) _ (hsubVf _ hσ₁ hfr₁) h3₂ (htri _ hσ₂ h3₂) h2₁ hnotB
        hd.symm j hkerle _ _ hw₂p (sum_weights hx₂h) hw₁p (sum_weights hx₁h)
        (by rw [← hp₁, ← hp₂, hpeq]) hz₂
  · omega
  · exact hnotB (Finset.subset_union_left.trans hB)

open Classical in
theorem exists_wallSystemCells_of_generic_crossing (D : SingularTwoCell M) {BdM C : Set M}
    {ι : Type} (ecf : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓf : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)) (Eb Eb' : ι → Set M)
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea} {Cf Bf : Set (Finset Ea)} (i₀ : ι)
    (hsys : IsCommonWallSystem Q ρ Cf Bf BdM C ecf ℓf Eb Eb')
    (hker : Module.finrank ℝ (LinearMap.ker (ℓf i₀)) = 2)
    {Rc Ac R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    (hsub : IsSubdivision R Rc) (hRdom : Rc.space ⊆ D.domain)
    {Bv Vf : Finset (EuclideanSpace ℝ (Fin 2))}
    {φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    (hguard : ∀ s : Finset (EuclideanSpace ℝ (Fin 2)),
      (s : Set (EuclideanSpace ℝ (Fin 2))) ⊆ R.vertices → s.card ≤ 4 →
        (s ∩ Bv).card ≤ Module.finrank ℝ (LinearMap.ker (ℓf i₀)) + 1 →
        AffineIndependent ℝ
          (fun v : (s.filter fun x => x ∈ Ac.space) => φ (v : EuclideanSpace ℝ (Fin 2))) →
        AffineIndependent ℝ (fun v : s => φ (v : EuclideanSpace ℝ (Fin 2))))
    (htri : ∀ σ ∈ R.faces, σ.card = 3 → ¬σ ⊆ Bv)
    (hℓv : ∀ v ∈ R.vertices, (v ∈ Bv → ℓf i₀ (φ v) = 0) ∧ (v ∉ Bv → 0 < ℓf i₀ (φ v)))
    (hsubVf : ∀ σ ∈ R.faces, (∀ v ∈ σ, v ∉ Ac.space) → σ ⊆ Vf)
    (hgR : ∀ x ∈ Rc.space, regionGluedMap D (ecf i₀) R φ Rc x ∈ Eb i₀ ∧
      regionGluedMap D (ecf i₀) R φ Rc x ∈ (ecf i₀).source ∧
        ecf i₀ (regionGluedMap D (ecf i₀) R φ Rc x) = simplicialMap R φ x)
    {ιP : Type*} (P : ιP → AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
    (hP : ∀ j, Module.finrank ℝ (P j).direction ≤ 2)
    (hPw : ∀ y ∈ Eb i₀, ∀ w ∈ wallSystemWalls Q, y ∈ wallSystemCell ρ w →
      ∃ j, ∀ x ∈ wallSystemCell ρ w, ecf i₀ x ∈ P j)
    (hplane : ∀ u ∈ Vf, ∀ j, (u ∈ Bv → ¬(LinearMap.ker (ℓf i₀)).toAffineSubspace ≤ P j) →
      φ u ∉ P j)
    (hcross : ∀ α ⊆ Vf, ∀ β ⊆ Vf, α.card = 3 → β.card = 3 → ¬α ⊆ Bv → ¬β ⊆ Bv →
      Disjoint α β → ∀ j, ¬(LinearMap.ker (ℓf i₀)).toAffineSubspace ≤ P j →
        ∀ w w' : EuclideanSpace ℝ (Fin 2) → ℝ, (∀ u ∈ α, 0 < w u) → ∑ u ∈ α, w u = 1 →
          (∀ u ∈ β, 0 < w' u) → ∑ u ∈ β, w' u = 1 →
          ∑ u ∈ α, w u • φ u = ∑ u ∈ β, w' u • φ u → ∑ u ∈ α, w u • φ u ∈ P j →
            ¬affineSpan ℝ (φ '' ↑α) ⊓ affineSpan ℝ (φ '' ↑β) ≤ P j)
    (hskelgen : ∀ y ∈ doublePointSet (regionGluedMap D (ecf i₀) R φ Rc) D.domain,
      FreeSourceGerm R Ac (regionGluedMap D (ecf i₀) R φ Rc) D.domain y →
        y ∉ wallSystemSkeleton Q ρ) :
    ∀ y ∈ doublePointSet (regionGluedMap D (ecf i₀) R φ Rc) D.domain,
      IsFreeInteriorDoubleGerm R Ac (regionGluedMap D (ecf i₀) R φ Rc) D.domain BdM y →
        ∀ w ∈ wallSystemWalls Q, y ∈ wallSystemCell ρ w →
          ∃ cm ∈ wallSystemCells Q, ∃ cp ∈ wallSystemCells Q, cm ≠ cp ∧
            y ∈ wallSystemCell ρ cm ∧ y ∈ wallSystemCell ρ cp ∧
            ∀ U ∈ 𝓝 y,
              (doublePointSet (regionGluedMap D (ecf i₀) R φ Rc) D.domain ∩ U ∩
                wallSystemCellInt ρ cm).Nonempty ∧
              (doublePointSet (regionGluedMap D (ecf i₀) R φ Rc) D.domain ∩ U ∩
                wallSystemCellInt ρ cp).Nonempty := by
  set ec := ecf i₀ with hecdef
  set ℓ := ℓf i₀ with hℓdef
  have hℓ : ℓ ≠ 0 := hsys.normalNe i₀
  intro y hyd hint w hw hyw
  obtain ⟨⟨hyB, hfr⟩, hint3⟩ := hint
  have hyskel := hskelgen y hyd hfr
  obtain ⟨x₁, hx₁S, x₂, hx₂S, hne, hgx₁, hgx₂⟩ := hyd
  obtain ⟨σ₁, hσ₁, h3₁, hx₁i⟩ := hint3 x₁ ⟨hx₁S, hgx₁⟩
  obtain ⟨σ₂, hσ₂, h3₂, hx₂i⟩ := hint3 x₂ ⟨hx₂S, hgx₂⟩
  have hint₁ : interior (convexHull ℝ (σ₁ : Set (EuclideanSpace ℝ (Fin 2)))) =
      openSimplex σ₁ :=
    interior_convexHull_eq_openSimplex (R.indep hσ₁) (by rw [h3₁, finrank_euclideanSpace_fin])
  have hint₂ : interior (convexHull ℝ (σ₂ : Set (EuclideanSpace ℝ (Fin 2)))) =
      openSimplex σ₂ :=
    interior_convexHull_eq_openSimplex (R.indep hσ₂) (by rw [h3₂, finrank_euclideanSpace_fin])
  have hx₁o : x₁ ∈ openSimplex σ₁ := hint₁ ▸ hx₁i
  have hx₂o : x₂ ∈ openSimplex σ₂ := hint₂ ▸ hx₂i
  have hRx₁ : x₁ ∈ Rc.space :=
    hsub.space_eq ▸ R.convexHull_subset_space hσ₁ (interior_subset hx₁i)
  have hRx₂ : x₂ ∈ Rc.space :=
    hsub.space_eq ▸ R.convexHull_subset_space hσ₂ (interior_subset hx₂i)
  have hfr₁ := (hfr x₁ ⟨hx₁S, hgx₁⟩).2 σ₁ hσ₁ (interior_subset hx₁i)
  have hfr₂ := (hfr x₂ ⟨hx₂S, hgx₂⟩).2 σ₂ hσ₂ (interior_subset hx₂i)
  have hpeq : simplicialMap R φ x₁ = simplicialMap R φ x₂ := by
    rw [← (hgR x₁ hRx₁).2.2, ← (hgR x₂ hRx₂).2.2, hgx₁, hgx₂]
  have hint12 : (σ₁ ∩ σ₂).card ≤ 1 := by
    rcases faces_cases_of_simplicialMap_eq_of_guard hℓ hguard htri hσ₁ hσ₂ hfr₁ hfr₂ hx₁o
      hx₂o hne hpeq with ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨h, -⟩
    · exact h
    · omega
    · omega
    · omega
  have hσne : σ₁ ≠ σ₂ := fun h => by
    rw [h, Finset.inter_self] at hint12
    omega
  have hx₁h := openSimplex_subset_convexHull _ hx₁o
  have hx₂h := openSimplex_subset_convexHull _ hx₂o
  have hw₁p : ∀ v ∈ σ₁, 0 < weights σ₁ x₁ v := fun v hv =>
    ((mem_openSimplex_iff_weights_pos (R.indep hσ₁) subset_rfl hx₁h).mp hx₁o v hv).mpr hv
  have hw₂p : ∀ v ∈ σ₂, 0 < weights σ₂ x₂ v := fun v hv =>
    ((mem_openSimplex_iff_weights_pos (R.indep hσ₂) subset_rfl hx₂h).mp hx₂o v hv).mpr hv
  have hp₁ := simplicialMap_eq_of_mem R φ hσ₁ hx₁h
  have hp₂ := simplicialMap_eq_of_mem R φ hσ₂ hx₂h
  have hσ₁V := hsubVf _ hσ₁ hfr₁
  have hσ₂V := hsubVf _ hσ₂ hfr₂
  have hzy : simplicialMap R φ x₁ = ec y := by
    rw [← (hgR x₁ hRx₁).2.2, hgx₁]
  have hysrc : y ∈ ec.source := hgx₁ ▸ (hgR x₁ hRx₁).2.1
  have hyE : y ∈ Eb i₀ := hgx₁ ▸ (hgR x₁ hRx₁).1
  obtain ⟨cm, hcm, cp, hcp, hcmp, hwm, hwp, ν, U', hU'o, hyU', -, -, -, -, -, hνw, -, -, hνm,
    hνp⟩ := hsys.exists_wallChart_sides i₀ hw hyw hyskel hyE
  refine ⟨cm, hcm, cp, hcp, hcmp, convexHull_mono (Finset.coe_subset.mpr hwm) hyw,
    convexHull_mono (Finset.coe_subset.mpr hwp) hyw, ?_⟩
  obtain ⟨j, hPcell⟩ := hPw y hyE w hw hyw
  have hvert : ∀ v ∈ σ₁, v ∈ R.vertices := fun v hv =>
    R.down_closed hσ₁ (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  set z := simplicialMap R φ x₁ with hzdef
  have hzP : z ∈ P j := by
    rw [hzy]
    exact hPcell y hyw
  have hℓz : 0 < ℓ z := by
    rw [hp₁, map_sum]
    simp only [map_smul, smul_eq_mul]
    obtain ⟨v, hvσ, hvB⟩ := Finset.not_subset.mp (htri σ₁ hσ₁ h3₁)
    refine Finset.sum_pos' (fun u hu => mul_nonneg (hw₁p u hu).le ?_)
      ⟨v, hvσ, mul_pos (hw₁p v hvσ) ((hℓv v (hvert v hvσ)).2 hvB)⟩
    by_cases huB : u ∈ Bv
    · exact ((hℓv u (hvert u hu)).1 huB).ge
    · exact ((hℓv u (hvert u hu)).2 huB).le
  have hkerle : ¬(LinearMap.ker ℓ).toAffineSubspace ≤ P j := fun hle => by
    have heq := eq_of_le_of_finrank_direction_le hle
      ⟨0, Submodule.mem_toAffineSubspace.mpr (Submodule.zero_mem _)⟩
      (by rw [Submodule.toAffineSubspace_direction, hker]; exact hP j)
    have hz0 : z ∈ (LinearMap.ker ℓ).toAffineSubspace := by
      rw [heq]
      exact hzP
    exact hℓz.ne' (LinearMap.mem_ker.mp (Submodule.mem_toAffineSubspace.mp hz0))
  have hnotle : ¬affineSpan ℝ (φ '' ↑σ₁) ⊓ affineSpan ℝ (φ '' ↑σ₂) ≤ P j := by
    by_cases hd : Disjoint σ₁ σ₂
    · exact hcross _ hσ₁V _ hσ₂V h3₁ h3₂ (htri σ₁ hσ₁ h3₁) (htri σ₂ hσ₂ h3₂) hd j hkerle _ _
        hw₁p (sum_weights hx₁h) hw₂p (sum_weights hx₂h) (by rw [← hp₁, ← hp₂, hpeq])
        (by rw [← hp₁]; exact hzP)
    · obtain ⟨v, hv₁, hv₂⟩ := Finset.not_disjoint_iff.mp hd
      intro hle
      exact hplane v (hσ₁V hv₁) j (fun _ => hkerle) (hle ((AffineSubspace.mem_inf_iff _ _ _).mpr
        ⟨subset_affineSpan ℝ _ (mem_image_of_mem φ hv₁),
          subset_affineSpan ℝ _ (mem_image_of_mem φ hv₂)⟩))
  obtain ⟨q, hqL, hqnot⟩ := IsConcreteLE.not_le_iff_exists.mp hnotle
  obtain ⟨hq₁, hq₂⟩ := (AffineSubspace.mem_inf_iff _ _ _).mp hqL
  set d := q - z with hd
  have hdir : ∀ {σ : Finset (EuclideanSpace ℝ (Fin 2))}
      {A : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)}, σ ∈ R.faces →
      σ.card = 3 → EqOn (simplicialMap R φ) A (convexHull ℝ (σ : Set _)) →
      ∀ q' ∈ affineSpan ℝ (φ '' ↑σ), ∀ z' ∈ affineSpan ℝ (φ '' ↑σ),
        ∃ e : EuclideanSpace ℝ (Fin 2), A.linear e = q' - z' := by
    intro σ A hσ h3 hA q' hq' z' hz'
    have himg : φ '' ↑σ = A '' ↑σ := image_congr fun v hv => by
      rw [← hA (subset_convexHull ℝ _ hv), simplicialMap_vertex R φ
        (R.down_closed hσ (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))]
    have hrange : Set.range ((↑) : σ → EuclideanSpace ℝ (Fin 2)) =
        (σ : Set (EuclideanSpace ℝ (Fin 2))) := by
      ext
      simp
    have htop : affineSpan ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))) = ⊤ := by
      rw [← hrange]
      exact (R.indep hσ).affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
        (by rw [Fintype.card_coe, h3, finrank_euclideanSpace_fin])
    have hmem : q' -ᵥ z' ∈ (affineSpan ℝ (φ '' ↑σ)).direction :=
      AffineSubspace.vsub_mem_direction hq' hz'
    rw [himg, ← AffineSubspace.map_span, htop, AffineSubspace.map_direction,
      AffineSubspace.direction_top] at hmem
    obtain ⟨e, -, he⟩ := Submodule.mem_map.mp hmem
    exact ⟨e, he⟩
  obtain ⟨A₁, hA₁⟩ := exists_affineMap_eqOn_simplicialMap R φ hσ₁
  obtain ⟨A₂, hA₂⟩ := exists_affineMap_eqOn_simplicialMap R φ hσ₂
  have hz₁ : z ∈ affineSpan ℝ (φ '' ↑σ₁) := by
    rw [hp₁]
    exact sum_smul_mem_affineSpan_image (sum_weights hx₁h) φ
  have hz₂ : z ∈ affineSpan ℝ (φ '' ↑σ₂) := by
    rw [hpeq, hp₂]
    exact sum_smul_mem_affineSpan_image (sum_weights hx₂h) φ
  obtain ⟨e₁, he₁⟩ := hdir hσ₁ h3₁ hA₁ q hq₁ z hz₁
  obtain ⟨e₂, he₂⟩ := hdir hσ₂ h3₂ hA₂ q hq₂ z hz₂
  have hAx : ∀ {A : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)}
      {x e : EuclideanSpace ℝ (Fin 2)}, A x = z → A.linear e = d → ∀ t : ℝ,
        A (x + t • e) = z + t • d := by
    intro A x e hx he t
    rw [add_comm x, ← vadd_eq_add, AffineMap.map_vadd, vadd_eq_add, map_smul, he, hx,
      add_comm]
  have hA₁x : A₁ x₁ = z := (hA₁ (interior_subset hx₁i)).symm
  have hA₂x : A₂ x₂ = z := by
    rw [← hA₂ (interior_subset hx₂i), hpeq]
  have hzt : z ∈ ec.target := by
    rw [hzy]
    exact ec.map_source hysrc
  have hy0 : ec.symm z = y := by
    rw [hzy, ec.left_inv hysrc]
  have hev : ∀ Uy ∈ 𝓝 y, ∀ᶠ t in 𝓝 (0 : ℝ),
      x₁ + t • e₁ ∈ interior (convexHull ℝ (σ₁ : Set (EuclideanSpace ℝ (Fin 2)))) ∧
      x₂ + t • e₂ ∈ interior (convexHull ℝ (σ₂ : Set (EuclideanSpace ℝ (Fin 2)))) ∧
      z + t • d ∈ ec.target ∧ ec.symm (z + t • d) ∈ Uy ∩ U' := by
    intro Uy hUy
    have hc₁ : Continuous fun t : ℝ => x₁ + t • e₁ := by fun_prop
    have hc₂ : Continuous fun t : ℝ => x₂ + t • e₂ := by fun_prop
    have hcz : Continuous fun t : ℝ => z + t • d := by fun_prop
    have hsymm : ContinuousAt (fun t : ℝ => ec.symm (z + t • d)) 0 :=
      (ec.continuousAt_symm hzt).comp_of_eq hcz.continuousAt (by simp)
    refine (hc₁.continuousAt.eventually_mem ?_).and ((hc₂.continuousAt.eventually_mem ?_).and
      ((hcz.continuousAt.eventually_mem ?_).and (hsymm.eventually_mem ?_)))
    · simpa using isOpen_interior.mem_nhds hx₁i
    · simpa using isOpen_interior.mem_nhds hx₂i
    · simpa using ec.open_target.mem_nhds hzt
    · show Uy ∩ U' ∈ 𝓝 (ec.symm (z + (0 : ℝ) • d))
      rw [zero_smul, add_zero, hy0]
      exact Filter.inter_mem hUy (hU'o.mem_nhds hyU')
  have hdp : ∀ t : ℝ,
      x₁ + t • e₁ ∈ interior (convexHull ℝ (σ₁ : Set (EuclideanSpace ℝ (Fin 2)))) →
      x₂ + t • e₂ ∈ interior (convexHull ℝ (σ₂ : Set (EuclideanSpace ℝ (Fin 2)))) →
      ec.symm (z + t • d) ∈ doublePointSet (regionGluedMap D ec R φ Rc) D.domain := by
    intro t h₁ h₂
    have hR₁ : x₁ + t • e₁ ∈ Rc.space :=
      hsub.space_eq ▸ R.convexHull_subset_space hσ₁ (interior_subset h₁)
    have hR₂ : x₂ + t • e₂ ∈ Rc.space :=
      hsub.space_eq ▸ R.convexHull_subset_space hσ₂ (interior_subset h₂)
    have hg₁ : regionGluedMap D ec R φ Rc (x₁ + t • e₁) = ec.symm (z + t • d) := by
      rw [regionGluedMap_of_mem D ec R φ hR₁, hA₁ (interior_subset h₁), hAx hA₁x he₁ t]
    have hg₂ : regionGluedMap D ec R φ Rc (x₂ + t • e₂) = ec.symm (z + t • d) := by
      rw [regionGluedMap_of_mem D ec R φ hR₂, hA₂ (interior_subset h₂), hAx hA₂x he₂ t]
    refine ⟨x₁ + t • e₁, hRdom hR₁, x₂ + t • e₂, hRdom hR₂, fun heq => hσne ?_, hg₁, hg₂⟩
    have ho₁ : x₁ + t • e₁ ∈ openSimplex σ₁ := hint₁ ▸ h₁
    have ho₂ : x₁ + t • e₁ ∈ openSimplex σ₂ := by
      rw [heq, ← hint₂]
      exact h₂
    exact Finset.Subset.antisymm
      (face_subset_of_mem_openSimplex_of_mem_convexHull R hσ₁ hσ₂ ho₁
        (openSimplex_subset_convexHull σ₂ ho₂))
      (face_subset_of_mem_openSimplex_of_mem_convexHull R hσ₂ hσ₁ ho₂
        (openSimplex_subset_convexHull σ₁ ho₁))
  have hνz : ν z = 0 := by
    rw [hzy]
    exact (hνw y hyU').mp hyw
  have hνt : ∀ t : ℝ, ν (z + t • d) = t * ν.linear d := fun t => by
    rw [add_comm, ← vadd_eq_add, AffineMap.map_vadd, vadd_eq_add, hνz, add_zero, map_smul,
      smul_eq_mul]
  have hνd : ν.linear d ≠ 0 := by
    intro h0
    obtain ⟨t, ⟨-, -, h₃, h₄⟩, ht⟩ := (((hev U' (hU'o.mem_nhds hyU')).filter_mono
      nhdsWithin_le_nhds).and (eventually_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))).exists
    have hν0 : ν (ec (ec.symm (z + t • d))) = 0 := by
      rw [ec.right_inv h₃, hνt, h0, mul_zero]
    have hyw' : ec.symm (z + t • d) ∈ wallSystemCell ρ w := (hνw _ h₄.2).mpr hν0
    have hmemP : z + t • d ∈ P j := by
      have h := hPcell _ hyw'
      rwa [ec.right_inv h₃] at h
    have hdP : d ∈ (P j).direction := by
      have hv := AffineSubspace.vsub_mem_direction hmemP hzP
      rw [vsub_eq_sub, add_sub_cancel_left] at hv
      have h := (P j).direction.smul_mem t⁻¹ hv
      rwa [smul_smul, inv_mul_cancel₀ (ne_of_gt ht), one_smul] at h
    apply hqnot
    have h := AffineSubspace.vadd_mem_of_mem_direction hdP hzP
    rwa [vadd_eq_add, hd, sub_add_cancel] at h
  intro Uy hUy
  obtain ⟨t₁, ⟨h₁, h₂, h₃, h₄⟩, ht₁⟩ := (((hev Uy hUy).filter_mono nhdsWithin_le_nhds).and
    (eventually_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))).exists
  obtain ⟨t₂, ⟨k₁, k₂, k₃, k₄⟩, ht₂⟩ := (((hev Uy hUy).filter_mono nhdsWithin_le_nhds).and
    (eventually_mem_nhdsWithin (s := Iio (0 : ℝ)) (a := 0))).exists
  have hν₁ : ν (ec (ec.symm (z + t₁ • d))) = t₁ * ν.linear d := by
    rw [ec.right_inv h₃, hνt]
  have hν₂ : ν (ec (ec.symm (z + t₂ • d))) = t₂ * ν.linear d := by
    rw [ec.right_inv k₃, hνt]
  have ht₁' : 0 < t₁ := ht₁
  have ht₂' : t₂ < 0 := ht₂
  rcases lt_or_gt_of_ne hνd with hneg | hpos
  · exact ⟨⟨_, ⟨hdp t₁ h₁ h₂, h₄.1⟩, hνm _ h₄.2 (by
        rw [hν₁]
        exact mul_neg_of_pos_of_neg ht₁' hneg)⟩,
      ⟨_, ⟨hdp t₂ k₁ k₂, k₄.1⟩, hνp _ k₄.2 (by
        rw [hν₂]
        exact mul_pos_of_neg_of_neg ht₂' hneg)⟩⟩
  · exact ⟨⟨_, ⟨hdp t₂ k₁ k₂, k₄.1⟩, hνm _ k₄.2 (by
        rw [hν₂]
        exact mul_neg_of_neg_of_pos ht₂' hpos)⟩,
      ⟨_, ⟨hdp t₁ h₁ h₂, h₄.1⟩, hνp _ h₄.2 (by
        rw [hν₁]
        exact mul_pos ht₁' hpos)⟩⟩

open Classical in
theorem exists_wallGenericVertexMap (D : SingularTwoCell M) {BdM C V : Set M} {ι : Type}
    (ecf : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓf : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)) (Eb Eb' : ι → Set M)
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea} {Cf Bf : Set (Finset Ea)} (i₀ : ι)
    (hsys : IsCommonWallSystem Q ρ Cf Bf BdM C ecf ℓf Eb Eb')
    (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hmapC : MapsTo (⇑D) D.domain C) (hVec : V ⊆ (ecf i₀).source)
    (hVE : closure V ⊆ interior (Eb i₀))
    (Rc Lc Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (hLR : Lc.faces ⊆ Rc.faces) (hAR : Ac.faces ⊆ Rc.faces)
    (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hLspace : Lc.space = Rc.space ∩ frontier D.domain)
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (hsub : IsSubdivision R Rc) (hRsfin : R.faces.Finite)
    (hlinear : ∀ s ∈ R.faces,
      ∃ A : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3),
        EqOn (fun x => ecf i₀ (D x)) A (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 2)))))
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ (Bv : Finset (EuclideanSpace ℝ (Fin 2)))
      (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)),
      AdmissibleVertexMap D (ecf i₀) (ℓf i₀) Lc Ac R Bv φ τ ∧
        (∀ s : Finset (EuclideanSpace ℝ (Fin 2)),
          (s : Set (EuclideanSpace ℝ (Fin 2))) ⊆ R.vertices → s.card ≤ 4 →
            (s ∩ Bv).card ≤ Module.finrank ℝ (LinearMap.ker (ℓf i₀)) + 1 →
            AffineIndependent ℝ
              (fun v : (s.filter fun x => x ∈ Ac.space) => φ (v : EuclideanSpace ℝ (Fin 2))) →
            AffineIndependent ℝ (fun v : s => φ (v : EuclideanSpace ℝ (Fin 2)))) ∧
        (∀ y ∈ doublePointSet (regionGluedMap D (ecf i₀) R φ Rc) D.domain,
          FreeSourceGerm R Ac (regionGluedMap D (ecf i₀) R φ Rc) D.domain y →
            y ∉ wallSystemSkeleton Q ρ) ∧
        (∀ y ∈ doublePointSet (regionGluedMap D (ecf i₀) R φ Rc) D.domain,
          IsFreeDoubleGerm R Ac (regionGluedMap D (ecf i₀) R φ Rc) D.domain BdM y →
            ∀ σ ∈ R.faces, σ.card ≤ 2 →
              y ∈ regionGluedMap D (ecf i₀) R φ Rc ''
                  (Rc.space ∩ convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2)))) →
                ∀ w ∈ wallSystemWalls Q, y ∉ wallSystemCell ρ w) ∧
        ∀ y ∈ doublePointSet (regionGluedMap D (ecf i₀) R φ Rc) D.domain,
          IsFreeInteriorDoubleGerm R Ac (regionGluedMap D (ecf i₀) R φ Rc) D.domain BdM y →
            ∀ w ∈ wallSystemWalls Q, y ∈ wallSystemCell ρ w →
              ∃ cm ∈ wallSystemCells Q, ∃ cp ∈ wallSystemCells Q, cm ≠ cp ∧
                y ∈ wallSystemCell ρ cm ∧ y ∈ wallSystemCell ρ cp ∧
                ∀ U ∈ 𝓝 y,
                  (doublePointSet (regionGluedMap D (ecf i₀) R φ Rc) D.domain ∩ U ∩
                    wallSystemCellInt ρ cm).Nonempty ∧
                  (doublePointSet (regionGluedMap D (ecf i₀) R φ Rc) D.domain ∩ U ∩
                    wallSystemCellInt ρ cp).Nonempty := by
  let _ := hLR
  let _ := hAR
  set ec := ecf i₀ with hecdef
  set ℓ := ℓf i₀ with hℓdef
  have hℓ : ℓ ≠ 0 := hsys.normalNe i₀
  have hker2 : Module.finrank ℝ (LinearMap.ker ℓ) = 2 := by
    have hrange : LinearMap.range ℓ = ⊤ := by
      obtain ⟨q, hq⟩ : ∃ q, ℓ q ≠ 0 := by
        by_contra h
        push Not at h
        exact hℓ (LinearMap.ext h)
      refine eq_top_iff.mpr fun r _ => ⟨(r / ℓ q) • q, ?_⟩
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ r hq]
    have h := LinearMap.finrank_range_add_finrank_ker ℓ
    rw [hrange, finrank_top, Module.finrank_self, finrank_euclideanSpace_fin] at h
    omega
  have hvfin : R.vertices.Finite := Set.Finite.preimage Finset.singleton_injective.injOn hRsfin
  have hvert : ∀ σ ∈ R.faces, ∀ v ∈ σ, v ∈ R.vertices := fun σ hσ v hv =>
    R.down_closed hσ (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  obtain ⟨Bv, hBvR, hBvL, -, -, hB0, hBpos⟩ := exists_admissibleVertexMap_of_adaptedChart D
    hproper hmapC ec ℓ hVec (hsys.chartC i₀) (hsys.chartBd i₀) Rc Lc Ac R hRsfin hsub hRdom hRV
    hLspace one_pos
  obtain ⟨U, hU⟩ : ∃ U : Finset (EuclideanSpace ℝ (Fin 2)), U = hvfin.toFinset := ⟨_, rfl⟩
  have hmemU : ∀ v, v ∈ U ↔ v ∈ R.vertices := fun v => by
    rw [hU]
    exact hvfin.mem_toFinset
  obtain ⟨Vf, hVfdef⟩ : ∃ Vf : Finset (EuclideanSpace ℝ (Fin 2)),
      Vf = U.filter fun v => v ∉ Ac.space := ⟨_, rfl⟩
  have hVf : ∀ u, u ∈ Vf ↔ u ∈ U ∧ u ∉ Ac.space := fun u => by
    rw [hVfdef, Finset.mem_filter]
  have hφ₀ : ∀ u ∈ U, (ℓ (ec (D u)) = 0 ↔ u ∈ Bv) ∧ 0 ≤ ℓ (ec (D u)) := by
    intro u hu
    have huR := (hmemU u).mp hu
    by_cases huB : u ∈ Bv
    · exact ⟨⟨fun _ => huB, fun _ => hB0 u huR huB⟩, (hB0 u huR huB).ge⟩
    · exact ⟨⟨fun h => absurd h (hBpos u huR huB).ne', fun h => absurd h huB⟩,
        (hBpos u huR huB).le⟩
  have hAc : ∀ c : Finset Ea, ∃ A : Ea →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3), c ∈ Q.faces →
      wallSystemCell ρ c ⊆ Eb' i₀ → ∀ x ∈ wallSystemCell ρ c, ec x = A (ρ x) := by
    intro c
    by_cases h : c ∈ Q.faces ∧ wallSystemCell ρ c ⊆ Eb' i₀
    · obtain ⟨A, hA⟩ := hsys.chartAffine i₀ c h.1 h.2
      exact ⟨A, fun _ _ => hA⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose Af hAf using hAc
  obtain ⟨e₀, he₀⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin 3))
  obtain ⟨SS, hSS⟩ : ∃ SS : Set (Finset Ea × Ea × Ea),
      SS = {q | q.1 ∈ Q.faces ∧ q.2.1 ∈ q.1 ∧ q.2.2 ∈ q.1} := ⟨_, rfl⟩
  have hSSfin : SS.Finite := by
    rw [hSS]
    refine (hsys.finiteFaces.prod ((hsys.finiteFaces.biUnion fun c _ => c.finite_toSet).prod
      (hsys.finiteFaces.biUnion fun c _ => c.finite_toSet))).subset fun q hq => ?_
    exact ⟨hq.1, mem_biUnion hq.1 hq.2.1, mem_biUnion hq.1 hq.2.2⟩
  have : Finite SS := hSSfin.to_subtype
  obtain ⟨dv, hdv⟩ : ∃ dv : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →
      EuclideanSpace ℝ (Fin 3), dv = fun a b => if b = a then e₀ else b - a := ⟨_, rfl⟩
  have hdvne : ∀ a b, dv a b ≠ 0 := by
    intro a b
    rw [hdv]
    dsimp only
    split_ifs with h
    · exact he₀
    · exact sub_ne_zero.mpr h
  have hdvmem : ∀ a b, b -ᵥ a ∈ ℝ ∙ dv a b := by
    intro a b
    rw [hdv]
    dsimp only
    split_ifs with h
    · rw [h, vsub_self]
      exact Submodule.zero_mem _
    · exact Submodule.mem_span_singleton_self _
  obtain ⟨S, hSdef⟩ : ∃ S : SS → AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)),
      S = fun q => AffineSubspace.mk' (Af q.1.1 q.1.2.1)
        (ℝ ∙ dv (Af q.1.1 q.1.2.1) (Af q.1.1 q.1.2.2)) := ⟨_, rfl⟩
  have hS : ∀ j, Module.finrank ℝ (S j).direction = 1 := fun j => by
    rw [hSdef]
    dsimp only
    rw [AffineSubspace.direction_mk']
    exact finrank_span_singleton (hdvne _ _)
  obtain ⟨SP, hSP⟩ : ∃ SP : Set (Finset Ea × Finset Ea),
      SP = {q | q.1 ∈ Q.faces ∧ q.2 ∈ Q.faces ∧ q.2 ⊆ q.1 ∧ q.2.card = 3} := ⟨_, rfl⟩
  have hSPfin : SP.Finite := by
    rw [hSP]
    exact (hsys.finiteFaces.prod hsys.finiteFaces).subset fun q hq => ⟨hq.1, hq.2.1⟩
  have : Finite SP := hSPfin.to_subtype
  obtain ⟨P, hPdef⟩ : ∃ P : SP → AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)),
      P = fun q => affineSpan ℝ (Af q.1.1 '' ↑q.1.2) := ⟨_, rfl⟩
  have hmemSP : ∀ q, q ∈ SP → q.2.card = 3 := fun q hq => by
    rw [hSP] at hq
    exact hq.2.2.2
  have hP : ∀ j, Module.finrank ℝ (P j).direction ≤ 2 := fun j => by
    have h := finrank_direction_affineSpan_image_le_card_sub_one j.1.2 (Af j.1.1)
    have h3 : j.1.2.card = 3 := hmemSP j.1 j.2
    rw [hPdef]
    dsimp only
    omega
  have hRcomp : IsCompact Rc.space := by
    rw [← hsub.space_eq]
    exact hRsfin.isCompact_biUnion fun s _ => s.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hKc : IsCompact ((fun x => ec (D x)) '' Rc.space) :=
    hRcomp.image_of_continuousOn (ec.continuousOn.comp (D.continuousOn.mono hRdom)
      fun x hx => hVec (hRV hx))
  have hOopen : IsOpen (ec '' (interior (Eb i₀) ∩ ec.source)) :=
    ec.isOpen_image_of_subset_source (isOpen_interior.inter ec.open_source) inter_subset_right
  have hKO : (fun x => ec (D x)) '' Rc.space ⊆ ec '' (interior (Eb i₀) ∩ ec.source) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨D x, ⟨hVE (subset_closure (hRV hx)), hVec (hRV hx)⟩, rfl⟩
  obtain ⟨δ, hδ, hδO⟩ := hKc.exists_cthickening_subset_open hOopen hKO
  obtain ⟨φ, hfix, hclose, hlay, hguard, hplane, hskel, hfold, hcross⟩ :=
    exists_small_vertexMap_generic_lines_planes_in_halfSpace U Vf Bv Ac.space hVf ℓ hℓ
      (fun v => ec (D v)) hφ₀ S hS P hP (lt_min hτ hδ)
  have hℓv : ∀ v ∈ R.vertices, (v ∈ Bv → ℓ (φ v) = 0) ∧ (v ∉ Bv → 0 < ℓ (φ v)) := by
    intro v hv
    by_cases hvV : v ∈ Vf
    · exact hlay v hvV
    · rw [hfix hvV]
      exact ⟨hB0 v hv, hBpos v hv⟩
  have hadm : AdmissibleVertexMap D ec ℓ Lc Ac R Bv φ τ :=
    ⟨hBvR, hBvL, fun v _ => lt_of_lt_of_le (hclose v) (min_le_left _ _),
      fun v _ hvA => hfix fun h => ((hVf v).mp h).2 hvA, fun v hv hvB => (hℓv v hv).1 hvB,
      fun v hv hvB => (hℓv v hv).2 hvB⟩
  have hguardleaf : ∀ s : Finset (EuclideanSpace ℝ (Fin 2)),
      (s : Set (EuclideanSpace ℝ (Fin 2))) ⊆ R.vertices → s.card ≤ 4 →
        (s ∩ Bv).card ≤ Module.finrank ℝ (LinearMap.ker ℓ) + 1 →
        AffineIndependent ℝ
          (fun v : (s.filter fun x => x ∈ Ac.space) => φ (v : EuclideanSpace ℝ (Fin 2))) →
        AffineIndependent ℝ (fun v : s => φ (v : EuclideanSpace ℝ (Fin 2))) := by
    intro s hs h4 h3 hind
    exact hguard s (fun v hv => (hmemU v).mpr (hs hv)) h4 (by rw [hker2] at h3; exact h3) hind
  have htri : ∀ σ ∈ R.faces, σ.card = 3 → ¬σ ⊆ Bv := fun σ hσ h3 => by
    obtain ⟨A, hA⟩ := hlinear σ hσ
    exact not_subset_boundary_of_card_eq_three_of_eqOn_affineMap D ec ℓ hproper hVec
      (hsys.chartBd i₀) hsub hRdom hRV hB0 hσ h3 hA
  have hp₀ : ∀ x ∈ Rc.space, simplicialMap R (fun v => ec (D v)) x = ec (D x) := by
    intro x hx
    have hxR : x ∈ R.space := by
      rw [hsub.space_eq]
      exact hx
    obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hxR
    obtain ⟨A, hA⟩ := hlinear s hs
    exact simplicialMap_eq_of_eqOn_affineMap R _ hs hA hxs
  have hgR : ∀ x ∈ Rc.space, regionGluedMap D ec R φ Rc x ∈ Eb i₀ ∧
      regionGluedMap D ec R φ Rc x ∈ ec.source ∧
        ec (regionGluedMap D ec R φ Rc x) = simplicialMap R φ x := by
    intro x hx
    have hxR : x ∈ R.space := by
      rw [hsub.space_eq]
      exact hx
    have hd := dist_simplicialMap_lt_of_dist_vertices_lt R (φ := φ) (ψ := fun v => ec (D v))
      (fun v _ => lt_of_lt_of_le (hclose v) (min_le_right _ _)) hxR
    rw [hp₀ x hx] at hd
    obtain ⟨q, ⟨hqE, hqs⟩, hq⟩ := hδO (mem_cthickening_of_dist_le _ (ec (D x)) δ _
      ⟨x, hx, rfl⟩ hd.le)
    rw [regionGluedMap_of_mem D ec R φ hx, ← hq, ec.left_inv hqs]
    exact ⟨interior_subset hqE, hqs, rfl⟩
  have hsubVf : ∀ σ ∈ R.faces, (∀ v ∈ σ, v ∉ Ac.space) → σ ⊆ Vf := fun σ hσ hfr v hv =>
    (hVf v).mpr ⟨(hmemU v).mpr (hvert σ hσ v hv), hfr v hv⟩
  have hSk : ∀ y ∈ Eb i₀, y ∈ wallSystemSkeleton Q ρ → ∃ j, ec y ∈ S j := by
    intro y hyE hyskel
    unfold wallSystemSkeleton at hyskel
    obtain ⟨e, ⟨he, he2⟩, hye⟩ := mem_iUnion₂.mp hyskel
    obtain ⟨c, hc, hec⟩ := hsys.memCell e he
    have hyc : y ∈ wallSystemCell ρ c := convexHull_mono (Finset.coe_subset.mpr hec) hye
    have hcE : wallSystemCell ρ c ⊆ Eb' i₀ := hsys.starLayer i₀ c hc ⟨y, hyc, hyE⟩
    have hecy : ec y = Af c (ρ y) := hAf c hc.1 hcE y hyc
    have hene : e.Nonempty := Q.nonempty_of_mem_faces he
    obtain ⟨e0, e1, he0, he1, hesub⟩ : ∃ e0 e1, e0 ∈ e ∧ e1 ∈ e ∧ e ⊆ {e0, e1} := by
      obtain ⟨a, ha⟩ := hene
      by_cases hsub1 : e ⊆ {a}
      · exact ⟨a, a, ha, ha, fun v hv => Finset.mem_insert_of_mem (hsub1 hv)⟩
      · obtain ⟨b, hb, hba⟩ := Finset.not_subset.mp hsub1
        have hab : b ≠ a := fun h => hba (by rw [h]; exact Finset.mem_singleton_self a)
        refine ⟨a, b, ha, hb, fun u hu => ?_⟩
        by_contra hu'
        have hsub3 : ({a, b, u} : Finset Ea) ⊆ e := by
          intro v hv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl | rfl
          · exact ha
          · exact hb
          · exact hu
        have hcard : ({a, b, u} : Finset Ea).card = 3 := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu'
          rw [Finset.card_insert_of_notMem (by simp [hab.symm, Ne.symm hu'.1]),
            Finset.card_insert_of_notMem (by simp [Ne.symm hu'.2]), Finset.card_singleton]
        have := Finset.card_le_card hsub3
        omega
    have hq : ((c, e0, e1) : Finset Ea × Ea × Ea) ∈ SS := by
      rw [hSS]
      exact ⟨hc.1, hec he0, hec he1⟩
    refine ⟨⟨_, hq⟩, ?_⟩
    rw [hecy, hSdef]
    dsimp only
    have hρ : ρ y ∈ convexHull ℝ ({e0, e1} : Set Ea) := by
      refine convexHull_mono ?_ hye
      rw [← Finset.coe_pair]
      exact Finset.coe_subset.mpr hesub
    have himg := mem_image_of_mem (Af c) hρ
    rw [AffineMap.image_convexHull, image_pair] at himg
    refine convexHull_min ?_ (AffineSubspace.convex _) himg
    rintro _ (rfl | rfl)
    · exact AffineSubspace.self_mem_mk' _ _
    · exact AffineSubspace.mem_mk'.mpr (hdvmem _ _)
  have hPw : ∀ y ∈ Eb i₀, ∀ w ∈ wallSystemWalls Q, y ∈ wallSystemCell ρ w →
      ∃ j, ∀ x ∈ wallSystemCell ρ w, ec x ∈ P j := by
    intro y hyE w hw hyw
    obtain ⟨c, hc, hwc⟩ := hsys.memCell w hw.1
    have hyc : y ∈ wallSystemCell ρ c := convexHull_mono (Finset.coe_subset.mpr hwc) hyw
    have hcE : wallSystemCell ρ c ⊆ Eb' i₀ := hsys.starLayer i₀ c hc ⟨y, hyc, hyE⟩
    have hq : ((c, w) : Finset Ea × Finset Ea) ∈ SP := by
      rw [hSP]
      exact ⟨hc.1, hw.1, hwc, hw.2⟩
    refine ⟨⟨_, hq⟩, fun x hx => ?_⟩
    rw [hAf c hc.1 hcE x (convexHull_mono (Finset.coe_subset.mpr hwc) hx), hPdef]
    dsimp only
    refine convexHull_subset_affineSpan _ ?_
    rw [← AffineMap.image_convexHull]
    exact mem_image_of_mem _ hx
  have hskelgen := notMem_wallSystemSkeleton_of_generic D ec ℓ hℓ hsub hguardleaf htri hsubVf
    (fun x hx => ⟨(hgR x hx).1, (hgR x hx).2.2⟩) S hSk hskel
  exact ⟨Bv, φ, hadm, hguardleaf, hskelgen,
    notMem_wallSystemCell_of_generic_edge D ec ℓ hℓ hker2 (hsys.chartBd i₀) hsub hRdom
      hguardleaf htri hℓv hsubVf hgR P hP hPw hfold,
    exists_wallSystemCells_of_generic_crossing D ecf ℓf Eb Eb' i₀ hsys hker2 hsub hRdom
      hguardleaf htri hℓv hsubVf hgR P hP hPw hplane hcross hskelgen⟩

end MetricAmbient

end DifferentialGeometry.Topology.PiecewiseLinear
