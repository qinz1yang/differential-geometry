import DifferentialGeometry.Topology.PiecewiseLinear.ParameterizedTriangleCap

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem levelPolygons_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (f : E → ℝ) (r : ℝ) :
    levelPolygons S (fun x => -f x) (-r) = levelPolygons S f r := by
  ext J
  simp only [levelPolygons, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hJ, hsub⟩
    exact ⟨hJ, fun x hx => by
      simpa only [mem_inter_iff, Set.mem_ofPred_eq, neg_inj] using hsub hx⟩
  · rintro ⟨hJ, hsub⟩
    exact ⟨hJ, fun x hx => by
      simpa only [mem_inter_iff, Set.mem_ofPred_eq, neg_inj] using hsub hx⟩

theorem heightSingularPoints_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (f : E → ℝ) :
    heightSingularPoints S (fun x => -f x) = heightSingularPoints S f := by
  ext p
  simp only [heightSingularPoints, Set.mem_ofPred_eq, neg_inj]

theorem exists_triangulation_triangle_cap_with_nonsingular_boundary_of_ge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [dE : DecidableEq E] (hdimE : Module.finrank ℝ E = 3)
    {Q D J : Set E} {u v : (Fin 3 → ℝ) → E}
    (hu : IsPLHomeomorphOn u (stdSimplex ℝ (Fin 3)) Q)
    (hv : IsPLHomeomorphOn v (stdSimplex ℝ (Fin 3)) D)
    (huJ : u '' stdSimplexBoundary 2 = J) (hvJ : v '' stdSimplexBoundary 2 = J)
    (hQD : IsPLSphere 2 (Q ∪ D)) (H : E ≃ₜ E) (hH : IsPLHomeomorphOn H univ univ)
    (ℓ : E →L[ℝ] ℝ) (hheight : ∀ x, ℓ (H x) = ℓ x)
    (e : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] E)
    (T : Finset (EuclideanSpace ℝ (Fin 2)))
    (hT : AffineIndependent ℝ ((↑) : T → EuclideanSpace ℝ (Fin 2)))
    (hcard : T.card = 3) (he : Function.Injective e)
    (htriangle : H '' D = e '' convexHull ℝ (T : Set _)) {p : E}
    (hhalf : ∀ q ∈ J \ {p}, ∀ᶠ x in 𝓝 q, x ∈ Q → ℓ q ≤ ℓ x)
    (hboundary : ∀ q ∈ J \ {p},
      ∀ᶠ x in 𝓝 q, x ∈ J ↔ x ∈ Q ∧ ℓ x = ℓ q) :
    ∃ R : Geometry.SimplicialComplex ℝ E, R.faces.Finite ∧
      R.space = H '' (Q ∪ D) ∧ IsPLSphere 2 R.space ∧
      (restrict R (H '' Q)).space = H '' Q ∧
      (restrict R (H '' D)).space = H '' D ∧
      (boundaryComplex 2 (restrict R (H '' Q))).space = H '' J ∧
      (boundaryComplex 2 (restrict R (H '' D))).space = H '' J ∧
      (∀ s ∈ R.faces,
        s ∈ (restrict R (H '' Q)).faces ∨ s ∈ (restrict R (H '' D)).faces) ∧
      ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ,
        InjOn f (R.vertices ∪ ((T.image e : Finset E) : Set E)) →
        ∀ q ∈ (boundaryComplex 2 (restrict R (H '' Q))).vertices \ {H p},
          q ∉ heightSingularPoints R.space f := by
  have hheightNeg : ∀ x, (-ℓ) (H x) = (-ℓ) x := by
    intro x
    simp only [neg_apply, hheight]
  have hhalfNeg : ∀ q ∈ J \ {p},
      ∀ᶠ x in 𝓝 q, x ∈ Q → (-ℓ) x ≤ (-ℓ) q := by
    intro q hq
    filter_upwards [hhalf q hq] with x hx
    intro hxQ
    simpa only [neg_apply, neg_le_neg_iff] using hx hxQ
  have hboundaryNeg : ∀ q ∈ J \ {p},
      ∀ᶠ x in 𝓝 q, x ∈ J ↔ x ∈ Q ∧ (-ℓ) x = (-ℓ) q := by
    intro q hq
    simpa only [neg_apply, neg_inj] using hboundary q hq
  obtain ⟨R, hRfin, hRspace, hR, hRQ, hRD, hRQboundary, hRDboundary,
      hcover, hregular⟩ :=
    exists_triangulation_triangle_cap_with_nonsingular_boundary hdimE hu hv huJ hvJ
      hQD H hH (-ℓ) hheightNeg e T hT hcard he htriangle hhalfNeg hboundaryNeg
  have ht : Filter.Tendsto (fun f : E →L[ℝ] ℝ => -f) (𝓝 ℓ) (𝓝 (-ℓ)) := by
    have hcont : Continuous (fun f : E →L[ℝ] ℝ => -f) := continuous_neg
    exact hcont.continuousAt
  have hregular' := ht.eventually hregular
  refine ⟨R, hRfin, hRspace, hR, hRQ, hRD, hRQboundary, hRDboundary, hcover, ?_⟩
  filter_upwards [hregular'] with f hf
  intro hfinj q hq
  have hfinjNeg : InjOn (-f) (R.vertices ∪ ((T.image e : Finset E) : Set E)) := by
    intro x hx y hy hxy
    exact hfinj hx hy (neg_injective hxy)
  have hnot := hf hfinjNeg q hq
  change q ∉ heightSingularPoints R.space (fun x => (-f) x) at hnot
  have hnegfun : (fun x => (-f) x) = fun x => -f x := by
    funext x
    exact neg_apply f x
  rw [hnegfun, heightSingularPoints_neg] at hnot
  exact hnot

end DifferentialGeometry.Topology.PiecewiseLinear
