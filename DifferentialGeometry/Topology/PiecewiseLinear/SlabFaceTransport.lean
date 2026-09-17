import DifferentialGeometry.Topology.PiecewiseLinear.SimplexSlab

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_isPLHomeomorphOn_face_slab_prism
    (K : Geometry.SimplicialComplex ℝ E) {T : Finset E} (hT : T ∈ K.faces)
    (ℓ : E →ₗ[ℝ] ℝ) {a b r : ℝ} (hr : r ∈ Icc a b)
    (hvertices : ∀ v ∈ T, ℓ v < a ∨ b < ℓ v) :
    ∃ f : E → E × ℝ,
      IsPLHomeomorphOn f (convexHull ℝ (T : Set E) ∩ {x | a ≤ ℓ x ∧ ℓ x ≤ b})
        ((convexHull ℝ (T : Set E) ∩ {x | ℓ x = r}) ×ˢ Icc a b) ∧
      ∀ x ∈ convexHull ℝ (T : Set E) ∩ {x | a ≤ ℓ x ∧ ℓ x ≤ b},
        (∀ A : Geometry.SimplicialComplex ℝ E, A.faces ⊆ K.faces →
          ((f x).1 ∈ A.space ↔ x ∈ A.space)) ∧
        ((f x).2 = a ↔ ℓ x = a) ∧ ((f x).2 = b ↔ ℓ x = b) := by
  classical
  obtain ⟨f, hf, hcontrol⟩ := exists_isPLHomeomorphOn_convexHull_slab_prism T (K.indep hT) ℓ hr hvertices
  refine ⟨f, hf, ?_⟩
  intro x hx
  obtain ⟨hfaces, hlow, hhigh⟩ := hcontrol x hx
  have hy := hf.bijOn.mapsTo hx
  have hface (t : Finset E) (ht : t ∈ K.faces) :
      (f x).1 ∈ convexHull ℝ (t : Set E) ↔ x ∈ convexHull ℝ (t : Set E) := by
    have hsub := hfaces (T ∩ t) Finset.inter_subset_left
    constructor
    · intro hyt
      have hyi : (f x).1 ∈ convexHull ℝ ((T ∩ t : Finset E) : Set E) := by
        simpa only [Finset.coe_inter] using K.inter_subset_convexHull hT ht ⟨hy.1.1, hyt⟩
      exact convexHull_mono (Finset.coe_subset.mpr Finset.inter_subset_right) (hsub.mp hyi)
    · intro hxt
      have hxi : x ∈ convexHull ℝ ((T ∩ t : Finset E) : Set E) := by
        simpa only [Finset.coe_inter] using K.inter_subset_convexHull hT ht ⟨hx.1, hxt⟩
      exact convexHull_mono (Finset.coe_subset.mpr Finset.inter_subset_right) (hsub.mpr hxi)
  refine ⟨?_, hlow, hhigh⟩
  intro A hA
  constructor
  · intro hyA
    obtain ⟨t, ht, hyt⟩ := A.mem_space_iff.mp hyA
    exact A.convexHull_subset_space ht ((hface t (hA ht)).mp hyt)
  · intro hxA
    obtain ⟨t, ht, hxt⟩ := A.mem_space_iff.mp hxA
    exact A.convexHull_subset_space ht ((hface t (hA ht)).mpr hxt)

end DifferentialGeometry.Topology.PiecewiseLinear
