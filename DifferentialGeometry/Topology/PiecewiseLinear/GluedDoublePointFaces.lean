/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialMap
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Subdivision
import DifferentialGeometry.Topology.PiecewiseLinear.Derived

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Algebra

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem eq_on_of_sum_smul_eq_of_affineIndependent {s : Finset E} {φ : E → F}
    (hs : AffineIndependent ℝ (fun v : s => φ (v : E))) {w w' : E → ℝ}
    (hw : ∑ v ∈ s, w v = 1) (hw' : ∑ v ∈ s, w' v = 1)
    (h : ∑ v ∈ s, w v • φ v = ∑ v ∈ s, w' v • φ v) : ∀ v ∈ s, w v = w' v := by
  have hw₁ : ∑ i : s, w i = 1 := by
    rw [Finset.sum_coe_sort s w]
    exact hw
  have hw₂ : ∑ i : s, w' i = 1 := by
    rw [Finset.sum_coe_sort s w']
    exact hw'
  have key := (hs.affineCombination_eq_iff_eq (s := Finset.univ) hw₁ hw₂).mp ?_
  · intro v hv
    exact key ⟨v, hv⟩ (Finset.mem_univ _)
  · rw [Finset.affineCombination_eq_linear_combination _ _ _ hw₁,
      Finset.affineCombination_eq_linear_combination _ _ _ hw₂]
    change ∑ i : s, w i • φ (i : E) = ∑ i : s, w' i • φ (i : E)
    rw [Finset.sum_coe_sort s (fun v => w v • φ v), Finset.sum_coe_sort s (fun v => w' v • φ v)]
    exact h

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem not_affineIndependent_insert_of_eq_sum [DecidableEq E] {s : Finset E} {v : E}
    (hv : v ∉ s) {φ : E → F} {w : E → ℝ} (hw : ∑ u ∈ s, w u = 1)
    (h : φ v = ∑ u ∈ s, w u • φ u) :
    ¬ AffineIndependent ℝ (fun u : (insert v s : Finset E) => φ (u : E)) := by
  intro hind
  have hne : ∀ u ∈ s, u ≠ v := fun u hu h => hv (h ▸ hu)
  have hδ : ∑ u ∈ insert v s, (if u = v then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_insert hv, ite_eq_left rfl, Finset.sum_eq_zero fun u hu => ite_eq_right (hne u hu),
      add_zero]
  have hw'₁ : ∑ u ∈ insert v s, (if u = v then (0 : ℝ) else w u) = 1 := by
    rw [Finset.sum_insert hv, ite_eq_left rfl, zero_add, ← hw]
    exact Finset.sum_congr rfl fun u hu => ite_eq_right (hne u hu)
  have hcomb : ∑ u ∈ insert v s, (if u = v then (1 : ℝ) else 0) • φ u =
      ∑ u ∈ insert v s, (if u = v then (0 : ℝ) else w u) • φ u := by
    rw [Finset.sum_insert hv, Finset.sum_insert hv, ite_eq_left rfl, ite_eq_left rfl, one_smul, zero_smul,
      zero_add, Finset.sum_eq_zero fun u hu => by rw [ite_eq_right (hne u hu), zero_smul], add_zero, h]
    exact Finset.sum_congr rfl fun u hu => by rw [ite_eq_right (hne u hu)]
  have hvv := eq_on_of_sum_smul_eq_of_affineIndependent hind hδ hw'₁ hcomb v
    (Finset.mem_insert_self v s)
  rw [ite_eq_left rfl, ite_eq_left rfl] at hvv
  exact one_ne_zero hvv

theorem eq_of_simplicialMap_eq_of_affineIndependent [DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) (φ : E → F) {σ τ : Finset E} (hσ : σ ∈ K.faces)
    (hτ : τ ∈ K.faces) {x z : E} (hx : x ∈ convexHull ℝ (σ : Set E))
    (hz : z ∈ convexHull ℝ (τ : Set E))
    (hind : AffineIndependent ℝ (fun v : (σ ∪ τ : Finset E) => φ (v : E)))
    (heq : simplicialMap K φ x = simplicialMap K φ z) : x = z := by
  have hsum : ∀ (t : Finset E) (g : E → ℝ) (G : E → F), t ⊆ σ ∪ τ →
      ∑ v ∈ σ ∪ τ, (if v ∈ t then g v else 0) • G v = ∑ v ∈ t, g v • G v := by
    intro t g G ht
    simp only [ite_smul, zero_smul]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr ht]
  have hsum' : ∀ (t : Finset E) (g : E → ℝ), t ⊆ σ ∪ τ →
      ∑ v ∈ σ ∪ τ, (if v ∈ t then g v else 0) = ∑ v ∈ t, g v := by
    intro t g ht
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr ht]
  have hw : ∑ v ∈ σ ∪ τ, (if v ∈ σ then weights σ x v else 0) = 1 := by
    rw [hsum' σ _ Finset.subset_union_left]
    exact sum_weights hx
  have hw' : ∑ v ∈ σ ∪ τ, (if v ∈ τ then weights τ z v else 0) = 1 := by
    rw [hsum' τ _ Finset.subset_union_right]
    exact sum_weights hz
  have hcomb : ∑ v ∈ σ ∪ τ, (if v ∈ σ then weights σ x v else 0) • φ v =
      ∑ v ∈ σ ∪ τ, (if v ∈ τ then weights τ z v else 0) • φ v := by
    rw [hsum σ _ _ Finset.subset_union_left, hsum τ _ _ Finset.subset_union_right,
      ← simplicialMap_eq_of_mem K φ hσ hx, ← simplicialMap_eq_of_mem K φ hτ hz]
    exact heq
  have hww := eq_on_of_sum_smul_eq_of_affineIndependent hind hw hw' hcomb
  have hsumE : ∀ (t : Finset E) (g : E → ℝ), t ⊆ σ ∪ τ →
      ∑ v ∈ σ ∪ τ, (if v ∈ t then g v else 0) • v = ∑ v ∈ t, g v • v := by
    intro t g ht
    simp only [ite_smul, zero_smul]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr ht]
  have hx' : ∑ v ∈ σ ∪ τ, (if v ∈ σ then weights σ x v else 0) • v = x := by
    rw [hsumE σ _ Finset.subset_union_left]
    exact sum_weights_smul hx
  have hz' : ∑ v ∈ σ ∪ τ, (if v ∈ τ then weights τ z v else 0) • v = z := by
    rw [hsumE τ _ Finset.subset_union_right]
    exact sum_weights_smul hz
  rw [← hx', ← hz']
  exact Finset.sum_congr rfl fun v hv => by rw [hww v hv]

end Algebra

section Glued

open Classical in
theorem affineIndependent_of_wallGuard
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
    {s : Finset (EuclideanSpace ℝ (Fin 2))}
    (hsR : (s : Set (EuclideanSpace ℝ (Fin 2))) ⊆ R.vertices) (h4 : s.card ≤ 4)
    (h3 : (s ∩ Bv).card ≤ 3) (hfree : ∀ v ∈ s, v ∉ Ac.space) :
    AffineIndependent ℝ (fun v : s => φ (v : EuclideanSpace ℝ (Fin 2))) := by
  have hrange : LinearMap.range ℓ = ⊤ := by
    obtain ⟨v, hv⟩ : ∃ v, ℓ v ≠ 0 := by
      by_contra h
      apply hℓ
      ext v
      by_contra hv
      exact h ⟨v, hv⟩
    refine eq_top_iff.mpr fun r _ => ⟨(r / ℓ v) • v, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ r hv]
  have hker : Module.finrank ℝ (LinearMap.ker ℓ) = 2 := by
    have h := LinearMap.finrank_range_add_finrank_ker ℓ
    rw [hrange, finrank_top, Module.finrank_self, finrank_euclideanSpace_fin] at h
    omega
  refine hguard s hsR h4 (by rw [hker]; exact h3) ?_
  have hempty : IsEmpty (s.filter fun x => x ∈ Ac.space) := by
    refine ⟨fun v => ?_⟩
    obtain ⟨hvs, hvA⟩ := Finset.mem_filter.mp v.2
    exact hfree v hvs hvA
  exact affineIndependent_of_subsingleton ℝ _

theorem convexHull_subset_of_subset_boundaryVertices
    {R Lc Rc : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    {Bv : Finset (EuclideanSpace ℝ (Fin 2))}
    {φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} (hsub : IsSubdivision R Rc)
    (hBvL : ∀ v ∈ R.vertices, v ∈ Bv ↔ v ∈ Lc.space)
    (hpzero : ∀ x ∈ Rc.space, ℓ (simplicialMap R φ x) = 0 ↔ x ∈ Lc.space)
    {σ : Finset (EuclideanSpace ℝ (Fin 2))} (hσ : σ ∈ R.faces) (hB : σ ⊆ Bv) :
    convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Lc.space := by
  have hR : ∀ z ∈ convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))), z ∈ Rc.space :=
    fun z hz => hsub.space_eq ▸ R.convexHull_subset_space hσ hz
  obtain ⟨A, hA⟩ := exists_affineMap_eqOn_simplicialMap R φ hσ
  have hconv : Convex ℝ ((ℓ.toAffineMap.comp A) ⁻¹' {0}) :=
    (convex_singleton (0 : ℝ)).affine_preimage _
  have hzero : convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))) ⊆
      (ℓ.toAffineMap.comp A) ⁻¹' {0} := by
    refine convexHull_min (fun v hv => ?_) hconv
    have hvσ : v ∈ σ := Finset.mem_coe.mp hv
    have hvV : v ∈ R.vertices :=
      R.down_closed hσ (Finset.singleton_subset_iff.mpr hvσ) (Finset.singleton_nonempty v)
    have hvL : v ∈ Lc.space := (hBvL v hvV).mp (hB hvσ)
    have h0 := (hpzero v (hR v (subset_convexHull ℝ _ hv))).mpr hvL
    rw [hA (subset_convexHull ℝ _ hv)] at h0
    exact h0
  intro z hz
  refine (hpzero z (hR z hz)).mp ?_
  rw [hA hz]
  exact hzero hz

theorem not_subset_boundaryVertices_of_card_eq_three
    {R Lc Rc : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    {Bv : Finset (EuclideanSpace ℝ (Fin 2))}
    {φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {S : Set (EuclideanSpace ℝ (Fin 2))}
    (hsub : IsSubdivision R Rc) (hRdom : Rc.space ⊆ S)
    (hLspace : Lc.space = Rc.space ∩ frontier S)
    (hBvL : ∀ v ∈ R.vertices, v ∈ Bv ↔ v ∈ Lc.space)
    (hpzero : ∀ x ∈ Rc.space, ℓ (simplicialMap R φ x) = 0 ↔ x ∈ Lc.space)
    {σ : Finset (EuclideanSpace ℝ (Fin 2))} (hσ : σ ∈ R.faces) (h3 : σ.card = 3) :
    ¬ σ ⊆ Bv := by
  intro hB
  have hne : σ.Nonempty := R.nonempty_of_mem_faces hσ
  have hc := centroid_mem_openSimplex hne
  have hint : interior (convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2)))) = openSimplex σ :=
    interior_convexHull_eq_openSimplex (R.indep hσ) (by rw [h3, finrank_euclideanSpace_fin])
  rw [← hint] at hc
  have hS : convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))) ⊆ S :=
    fun z hz => hRdom (hsub.space_eq ▸ R.convexHull_subset_space hσ hz)
  have hcS : σ.centroid ℝ id ∈ interior S := interior_mono hS hc
  have hcL := convexHull_subset_of_subset_boundaryVertices hsub hBvL hpzero hσ hB
    (interior_subset hc)
  rw [hLspace] at hcL
  exact hcL.2.2 hcS

open Classical in
theorem faces_cases_of_simplicialMap_eq
    {R Ac Lc Rc : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    {Bv : Finset (EuclideanSpace ℝ (Fin 2))}
    {φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {S : Set (EuclideanSpace ℝ (Fin 2))} {κ : ℝ}
    (hℓ : ℓ ≠ 0) (hsub : IsSubdivision R Rc) (hRdom : Rc.space ⊆ S)
    (hLspace : Lc.space = Rc.space ∩ frontier S)
    (hBvL : ∀ v ∈ R.vertices, v ∈ Bv ↔ v ∈ Lc.space)
    (hpzero : ∀ x ∈ Rc.space, ℓ (simplicialMap R φ x) = 0 ↔ x ∈ Lc.space)
    (hguard : ∀ s : Finset (EuclideanSpace ℝ (Fin 2)),
      (s : Set (EuclideanSpace ℝ (Fin 2))) ⊆ R.vertices → s.card ≤ 4 →
        (s ∩ Bv).card ≤ Module.finrank ℝ (LinearMap.ker ℓ) + 1 →
        AffineIndependent ℝ
          (fun v : (s.filter fun x => x ∈ Ac.space) => φ (v : EuclideanSpace ℝ (Fin 2))) →
        AffineIndependent ℝ (fun v : s => φ (v : EuclideanSpace ℝ (Fin 2))))
    (hκ : 0 < κ)
    (hinj : ∀ x ∈ Rc.space, ∀ z ∈ Rc.space, dist x z < κ →
      simplicialMap R φ x = simplicialMap R φ z → x = z)
    {σ₁ σ₂ : Finset (EuclideanSpace ℝ (Fin 2))} (hσ₁ : σ₁ ∈ R.faces) (hσ₂ : σ₂ ∈ R.faces)
    (hfr₁ : ∀ v ∈ σ₁, v ∉ Ac.space) (hfr₂ : ∀ v ∈ σ₂, v ∉ Ac.space)
    {x₁ x₂ : EuclideanSpace ℝ (Fin 2)} (hx₁ : x₁ ∈ openSimplex σ₁) (hx₂ : x₂ ∈ openSimplex σ₂)
    (hne : x₁ ≠ x₂) (heq : simplicialMap R φ x₁ = simplicialMap R φ x₂) :
    Disjoint σ₁ σ₂ ∧ ((σ₁.card = 3 ∧ σ₂.card = 3) ∨ (σ₁.card = 2 ∧ σ₂.card = 3) ∨
      (σ₁.card = 3 ∧ σ₂.card = 2) ∨ (σ₁.card = 2 ∧ σ₂.card = 2 ∧ σ₁ ∪ σ₂ ⊆ Bv)) := by
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
  have htri : ∀ σ ∈ R.faces, σ.card = 3 → ¬ σ ⊆ Bv := fun σ hσ h3 =>
    not_subset_boundaryVertices_of_card_eq_three hsub hRdom hLspace hBvL hpzero hσ h3
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
      exact ⟨Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hdis),
        Or.inr (Or.inr (Or.inr ⟨by omega, by omega, hB⟩))⟩
  · have hlt : ((σ₁ ∪ σ₂) ∩ Bv).card < (σ₁ ∪ σ₂).card := by
      refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left,
        fun h => hB ?_⟩)
      rw [← h]
      exact Finset.inter_subset_right
    have h5 : 5 ≤ (σ₁ ∪ σ₂).card := by
      by_contra h
      exact key (by omega) (by omega)
    by_cases h0 : (σ₁ ∩ σ₂).card = 0
    · refine ⟨Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp h0), ?_⟩
      have hcases : (σ₁.card = 3 ∧ σ₂.card = 3) ∨ (σ₁.card = 2 ∧ σ₂.card = 3) ∨
          (σ₁.card = 3 ∧ σ₂.card = 2) := by omega
      rcases hcases with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · exfalso
      have h1 : (σ₁ ∩ σ₂).card = 1 := by omega
      have hc₁' : σ₁.card = 3 := by omega
      have hc₂' : σ₂.card = 3 := by omega
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
      have haσ : a ∈ σ₁ ∩ σ₂ := by rw [ha]; exact Finset.mem_singleton_self a
      have ha₁ : a ∈ convexHull ℝ (σ₁ : Set (EuclideanSpace ℝ (Fin 2))) :=
        subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_inter.mp haσ).1)
      have ha₂ : a ∈ convexHull ℝ (σ₂ : Set (EuclideanSpace ℝ (Fin 2))) :=
        subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_inter.mp haσ).2)
      obtain ⟨A₁, hA₁⟩ := exists_affineMap_eqOn_simplicialMap R φ hσ₁
      obtain ⟨A₂, hA₂⟩ := exists_affineMap_eqOn_simplicialMap R φ hσ₂
      have hd : 0 < ‖x₁ - x₂‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
      set t : ℝ := min 1 (κ / (2 * ‖x₁ - x₂‖)) with ht
      have htpos : 0 < t := lt_min one_pos (div_pos hκ (by positivity))
      have ht1 : t ≤ 1 := min_le_left _ _
      have htd : t * ‖x₁ - x₂‖ < κ := by
        have h := min_le_right 1 (κ / (2 * ‖x₁ - x₂‖))
        rw [← ht] at h
        calc t * ‖x₁ - x₂‖ ≤ κ / (2 * ‖x₁ - x₂‖) * ‖x₁ - x₂‖ :=
              mul_le_mul_of_nonneg_right h hd.le
          _ = κ / 2 := by field_simp
          _ < κ := by linarith
      have hz₁ : AffineMap.lineMap a x₁ t ∈ convexHull ℝ (σ₁ : Set (EuclideanSpace ℝ (Fin 2))) :=
        (convex_convexHull ℝ _).lineMap_mem ha₁ hx₁h ⟨htpos.le, ht1⟩
      have hz₂ : AffineMap.lineMap a x₂ t ∈ convexHull ℝ (σ₂ : Set (EuclideanSpace ℝ (Fin 2))) :=
        (convex_convexHull ℝ _).lineMap_mem ha₂ hx₂h ⟨htpos.le, ht1⟩
      have hp : simplicialMap R φ (AffineMap.lineMap a x₁ t) =
          simplicialMap R φ (AffineMap.lineMap a x₂ t) := by
        rw [hA₁ hz₁, hA₂ hz₂, AffineMap.apply_lineMap, AffineMap.apply_lineMap, ← hA₁ ha₁,
          ← hA₂ ha₂, ← hA₁ hx₁h, ← hA₂ hx₂h, heq]
      have hdist : dist (AffineMap.lineMap a x₁ t) (AffineMap.lineMap a x₂ t) < κ := by
        rw [dist_eq_norm, AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module']
        have heq' : t • (x₁ - a) + a - (t • (x₂ - a) + a) = t • (x₁ - x₂) := by
          simp only [smul_sub]
          abel
        rw [heq', norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
        exact htd
      have hRz : ∀ {σ : Finset (EuclideanSpace ℝ (Fin 2))}, σ ∈ R.faces →
          ∀ z ∈ convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))), z ∈ Rc.space :=
        fun hσ z hz => hsub.space_eq ▸ R.convexHull_subset_space hσ hz
      have hzz := hinj _ (hRz hσ₁ _ hz₁) _ (hRz hσ₂ _ hz₂) hdist hp
      rw [AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module'] at hzz
      have h' : t • (x₁ - x₂) = 0 := by
        have h2 : t • (x₁ - a) = t • (x₂ - a) := add_right_cancel hzz
        have h3 : t • (x₁ - x₂) = t • (x₁ - a) - t • (x₂ - a) := by
          simp only [smul_sub]
          abel
        rw [h3, h2, sub_self]
      rcases smul_eq_zero.mp h' with h | h
      · exact htpos.ne' h
      · exact hne (sub_eq_zero.mp h)

end Glued

end DifferentialGeometry.Topology.PiecewiseLinear
