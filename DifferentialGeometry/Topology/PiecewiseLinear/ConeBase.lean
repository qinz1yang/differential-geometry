import DifferentialGeometry.Topology.PiecewiseLinear.ConeComplex
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.RadialProjection
import DifferentialGeometry.Topology.PiecewiseLinear.Subdivision

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Insert

variable [DecidableEq E]

theorem affineIndependent_insert_iff {p : E} {τ : Finset E} (hpτ : p ∉ τ)
    (hτ : AffineIndependent ℝ ((↑) : τ → E)) :
    AffineIndependent ℝ ((↑) : {x // x ∈ (insert p τ : Finset E)} → E) ↔
      ¬ ∃ c : E → ℝ, ∑ v ∈ τ, c v = 1 ∧ ∑ v ∈ τ, c v • v = p := by
  constructor
  · rintro h ⟨c, hc₁, hcp⟩
    let e : E → ℝ := fun u => if u = p then 1 else -c u
    have he : ∀ u ∈ τ, e u = -c u := fun u hu => by
      simp only [e, if_neg (ne_of_mem_of_not_mem hu hpτ)]
    have h₀ : ∑ u ∈ insert p τ, e u = 0 := by
      rw [Finset.sum_insert hpτ, Finset.sum_congr rfl he, Finset.sum_neg_distrib, hc₁]
      simp [e]
    have h₁ : ∑ u ∈ insert p τ, e u • u = 0 := by
      rw [Finset.sum_insert hpτ, Finset.sum_congr rfl fun u hu => by rw [he u hu]]
      simp only [e, if_true, one_smul, neg_smul, Finset.sum_neg_distrib, hcp, add_neg_cancel]
    have := eq_zero_of_sum_eq_zero_of_affineIndependent h h₀ h₁ p (Finset.mem_insert_self p τ)
    simp [e] at this
  · intro hnot
    refine affineIndependent_of_forall_eq_zero fun a ha₀ ha₁ => ?_
    rw [Finset.sum_insert hpτ] at ha₀ ha₁
    by_cases hap : a p = 0
    · rw [hap, zero_add] at ha₀
      rw [hap, zero_smul, zero_add] at ha₁
      have := eq_zero_of_sum_eq_zero_of_affineIndependent hτ ha₀ ha₁
      intro u hu
      rcases Finset.mem_insert.mp hu with h | h
      · rw [h]
        exact hap
      · exact this u h
    · exfalso
      refine hnot ⟨fun v => -(a p)⁻¹ * a v, ?_, ?_⟩
      · rw [← Finset.mul_sum]
        have : ∑ v ∈ τ, a v = -a p := by linarith
        rw [this, neg_mul, mul_neg, neg_neg, inv_mul_cancel₀ hap]
      · simp_rw [mul_smul]
        rw [← Finset.smul_sum, eq_neg_of_add_eq_zero_right ha₁, neg_smul, smul_neg, neg_neg,
          smul_smul, inv_mul_cancel₀ hap, one_smul]

end Insert

theorem IsConeBase.of_isSubdivision {p : E} {L L₁ : Geometry.SimplicialComplex ℝ E}
    (h : IsConeBase p L) (h₁ : IsSubdivision L₁ L) : IsConeBase p L₁ where
  notMem_space := by
    rw [h₁.space_eq]
    exact h.notMem_space
  radial := by
    rw [h₁.space_eq]
    exact h.radial
  indep := by
    classical
    intro σ₁ hσ₁
    obtain ⟨σ, hσ, hsub⟩ := h₁.exists_face_subset hσ₁
    have hpσ₁ : p ∉ σ₁ := fun hp => h.notMem_space
      (h₁.space_eq ▸ L₁.convexHull_subset_space hσ₁ (subset_convexHull ℝ _ (Finset.mem_coe.mpr hp)))
    have hpσ : p ∉ σ := h.notMem_face hσ
    have hindσ : AffineIndependent ℝ ((↑) : {x // x ∈ (insert p σ : Finset E)} → E) := by
      have := h.indep σ hσ
      rwa [← Finset.coe_insert] at this
    have hmem : ∀ v ∈ σ₁, v ∈ convexHull ℝ (σ : Set E) := fun v hv =>
      hsub (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv))
    rw [← Finset.coe_insert]
    refine (affineIndependent_insert_iff hpσ₁ (L₁.indep hσ₁)).mpr ?_
    rintro ⟨c, hc₁, hcp⟩
    refine (affineIndependent_insert_iff hpσ (L.indep hσ)).mp hindσ
      ⟨fun u => ∑ v ∈ σ₁, c v * weights σ v u, ?_, ?_⟩
    · rw [Finset.sum_comm, ← hc₁]
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [← Finset.mul_sum, sum_weights (hmem v hv), mul_one]
    · simp_rw [Finset.sum_smul, mul_smul]
      rw [Finset.sum_comm, ← hcp]
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [← Finset.smul_sum, sum_weights_smul (hmem v hv)]

theorem isConeBase_simplexBoundary {T : Finset E} (hT : AffineIndependent ℝ ((↑) : T → E))
    (hcard : 2 ≤ T.card) {p : E} (hp : p ∈ openSimplex T) :
    IsConeBase p (simplexBoundary T hT) where
  notMem_space := by
    classical
    rw [simplexBoundary_space T hT hcard]
    exact notMem_boundary_of_mem_openSimplex hT hp
  radial := by
    classical
    rw [simplexBoundary_space T hT hcard]
    exact isRadiallyInjective_boundary hT hp
  indep := by
    classical
    rintro τ ⟨hτT, -, hτ⟩
    have hpT : p ∈ convexHull ℝ (T : Set E) := openSimplex_subset_convexHull T hp
    have hpos := (mem_openSimplex_self_iff hT hpT).mp hp
    obtain ⟨v, hvT, hvτ⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hτT, hτ⟩)
    have hpτ : p ∉ τ := fun h => notMem_erase_of_mem_openSimplex hT hp hvT
      (Finset.mem_erase.mpr ⟨ne_of_mem_of_not_mem h hvτ, hτT h⟩)
    rw [← Finset.coe_insert]
    refine (affineIndependent_insert_iff hpτ (affineIndependent_of_subset hT hτT)).mpr ?_
    rintro ⟨c, hc₁, hcp⟩
    let c' : E → ℝ := fun u => if u ∈ τ then c u else 0
    have h := weights_eq hT hpT (w := c') ?_ ?_ v hvT
    · simp only [c', if_neg hvτ] at h
      exact (hpos v hvT).ne' h
    · simp only [c']
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hτT]
      exact hc₁
    · simp only [c', ite_smul, zero_smul]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hτT]
      exact hcp

section ConeSubdivision

variable [DecidableEq E]

theorem coneComplex_isSubdivision {p : E} {L L₁ : Geometry.SimplicialComplex ℝ E}
    (h : IsConeBase p L) (h₁ : IsSubdivision L₁ L) :
    IsSubdivision (coneComplex (h.of_isSubdivision h₁)) (coneComplex h) := by
  refine ⟨?_, ?_⟩
  · ext x
    rw [mem_coneComplex_space_iff, mem_coneComplex_space_iff, h₁.space_eq]
  · rintro t (ht | rfl | ⟨σ₁, hσ₁, rfl⟩)
    · obtain ⟨σ, hσ, hsub⟩ := h₁.exists_face_subset ht
      exact ⟨σ, Or.inl hσ, hsub⟩
    · exact ⟨{p}, Or.inr (Or.inl rfl), subset_rfl⟩
    · obtain ⟨σ, hσ, hsub⟩ := h₁.exists_face_subset hσ₁
      refine ⟨insert p σ, Or.inr (Or.inr ⟨σ, hσ, rfl⟩), ?_⟩
      refine convexHull_min ?_ (convex_convexHull ℝ _)
      intro u hu
      rcases Finset.mem_insert.mp (Finset.mem_coe.mp hu) with h' | h'
      · rw [h']
        exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_insert_self p σ))
      · exact convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert p σ))
          (hsub (subset_convexHull ℝ _ (Finset.mem_coe.mpr h')))

end ConeSubdivision

end DifferentialGeometry.Topology.PiecewiseLinear
