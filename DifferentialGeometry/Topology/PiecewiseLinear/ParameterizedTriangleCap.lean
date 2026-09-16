import DifferentialGeometry.Topology.PiecewiseLinear.HeightGermTransport
import DifferentialGeometry.Topology.PiecewiseLinear.ParameterizedDiskUnion
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleBoundaryNonsingular

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem eventually_mem_inter_iff_left_and_eq_of_opposite_halfSpaces
    {X : Type*} [TopologicalSpace X] {A B S J : Set X} (hinter : A ∩ B = J)
    (f : X → ℝ) (r : ℝ) {q : X}
    (hA : ∀ᶠ x in 𝓝 q, x ∈ A ↔ x ∈ S ∧ r ≤ f x)
    (hB : ∀ᶠ x in 𝓝 q, x ∈ B ↔ x ∈ S ∧ f x ≤ r) :
    ∀ᶠ x in 𝓝 q, x ∈ J ↔ x ∈ A ∧ f x = r := by
  filter_upwards [hA, hB] with x hxA hxB
  constructor
  · intro hxJ
    have hxAB : x ∈ A ∩ B := hinter.symm.subset hxJ
    exact ⟨hxAB.1, le_antisymm (hxB.mp hxAB.2).2 (hxA.mp hxAB.1).2⟩
  · rintro ⟨hxA', hxeq⟩
    apply hinter.subset
    exact ⟨hxA', hxB.mpr ⟨(hxA.mp hxA').1, hxeq.le⟩⟩

theorem exists_triangulation_triangle_cap_with_nonsingular_boundary
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
    (hhalf : ∀ q ∈ J \ {p}, ∀ᶠ x in 𝓝 q, x ∈ Q → ℓ x ≤ ℓ q)
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
  classical
  cases Subsingleton.elim dE (Classical.decEq E)
  let U : Finset E := T.image e
  have hU : AffineIndependent ℝ ((↑) : U → E) :=
    affineIndependent_image_of_injOn_convexHull e hT he.injOn
  have hUcard : U.card = 3 := by
    rw [Finset.card_image_of_injective _ he, hcard]
  have hDtriangle : H '' D = convexHull ℝ (U : Set E) := by
    rw [htriangle]
    change e '' convexHull ℝ (T : Set _) = convexHull ℝ ((T.image e : Finset E) : Set E)
    rw [AffineMap.image_convexHull, Finset.coe_image]
  have hQ : IsPLBall 2 Q := ⟨u, hu⟩
  have hD : IsPLBall 2 D := ⟨v, hv⟩
  have hHQ : IsPLHomeomorphOn H Q (H '' Q) :=
    hH.restrict hQ.isPolyhedron (subset_univ Q)
  have hHD : IsPLHomeomorphOn H D (H '' D) :=
    hH.restrict hD.isPolyhedron (subset_univ D)
  have huH : IsPLHomeomorphOn (H ∘ u) (stdSimplex ℝ (Fin 3)) (H '' Q) :=
    hu.trans hHQ
  have hvH : IsPLHomeomorphOn (H ∘ v) (stdSimplex ℝ (Fin 3)) (H '' D) :=
    hv.trans hHD
  have huHJ : (H ∘ u) '' stdSimplexBoundary 2 = H '' J := by
    rw [image_comp, huJ]
  have hvHJ : (H ∘ v) '' stdSimplexBoundary 2 = H '' J := by
    rw [image_comp, hvJ]
  obtain ⟨R, hRfin, hRspace', hRQ, hRD, hRQball, -, hRQboundary, hRDboundary,
      hcover, -⟩ :=
    exists_triangulation_parameterized_disk_union huH hvH huHJ hvHJ
      ℓ.toLinearMap.toAffineMap (ℓ p)
  let _ : Finite R.faces := hRfin.to_subtype
  let M := restrict R (H '' Q)
  let N := restrict R (H '' D)
  let _ : Finite M.faces := (restrict_faces_finite R (H '' Q)).to_subtype
  let _ : Finite N.faces := (restrict_faces_finite R (H '' D)).to_subtype
  have hRspace : R.space = H '' (Q ∪ D) := by
    simpa only [image_union] using hRspace'
  have hHcap : IsPLSphere 2 (H '' (Q ∪ D)) :=
    hQD.of_isPLHomeomorphOn (hH.restrict hQD.isPolyhedron (subset_univ _))
  have hR : IsPLSphere 2 R.space := hRspace.symm ▸ hHcap
  have hhalfH : ∀ q ∈ H '' J \ {H p},
      ∀ᶠ x in 𝓝 q, x ∈ H '' Q → ℓ x ≤ ℓ q := by
    rintro _ ⟨⟨q, hqJ, rfl⟩, hqHp⟩
    have hqp : q ≠ p := by
      intro hqp
      apply hqHp
      rw [mem_singleton_iff]
      exact congrArg H hqp
    have hqnot : q ∉ ({p} : Set E) := by
      rw [mem_singleton_iff]
      exact hqp
    exact eventually_image_mem_le_of_height_preserving_homeomorph H ℓ hheight
      (hhalf q ⟨hqJ, hqnot⟩)
  have hboundaryH : ∀ q ∈ H '' J \ {H p},
      ∀ᶠ x in 𝓝 q, x ∈ H '' J ↔ x ∈ H '' Q ∧ ℓ x = ℓ q := by
    rintro _ ⟨⟨q, hqJ, rfl⟩, hqHp⟩
    have hqp : q ≠ p := by
      intro hqp
      apply hqHp
      rw [mem_singleton_iff]
      exact congrArg H hqp
    have hqnot : q ∉ ({p} : Set E) := by
      rw [mem_singleton_iff]
      exact hqp
    exact eventually_image_boundary_fiber_iff_of_height_preserving_homeomorph H ℓ hheight
      (hboundary q ⟨hqJ, hqnot⟩)
  have hhalfM : ∀ q ∈ (boundaryComplex 2 M).space \ {H p},
      ∀ᶠ x in 𝓝 q, x ∈ M.space → ℓ x ≤ ℓ q := by
    intro q hq
    have hq' : q ∈ H '' J \ {H p} := by simpa only [M, hRQboundary] using hq
    simpa only [M, hRQ] using hhalfH q hq'
  have hboundaryM : ∀ q ∈ (boundaryComplex 2 M).space \ {H p},
      ∀ᶠ x in 𝓝 q,
        x ∈ (boundaryComplex 2 M).space ↔ x ∈ M.space ∧ ℓ x = ℓ q := by
    intro q hq
    have hq' : q ∈ H '' J \ {H p} := by simpa only [M, hRQboundary] using hq
    simpa only [M, hRQboundary, hRQ] using hboundaryH q hq'
  have hregular := eventually_notMem_heightSingularPoints_on_triangle_boundary
    hdimE R M N hR (restrict_faces_subset R (H '' Q)) hcover hRQball U hU hUcard
      (by simpa only [N] using hRD.trans hDtriangle)
      (by simpa only [M, N] using hRQboundary.trans hRDboundary.symm)
      (H p) ℓ hhalfM hboundaryM
  have hregular' : ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ,
      InjOn f (R.vertices ∪ (U : Set E)) →
      ∀ q ∈ (boundaryComplex 2 M).vertices \ {H p},
        q ∉ heightSingularPoints R.space f := by
    filter_upwards [hregular] with f hf
    intro hfinj
    have hUne : U.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨a, ha, hmin⟩ := U.exists_min_image f hUne
    apply hf a ha hfinj
    apply linearMap_lt_on_convexHull_sdiff_singleton f.toLinearMap U a
    intro b hb hba
    have hne : f a ≠ f b := by
      intro heq
      exact hba (hfinj (Or.inr ha) (Or.inr hb) heq).symm
    exact lt_of_le_of_ne (hmin b hb) hne
  exact ⟨R, hRfin, hRspace, hR, hRQ, hRD, hRQboundary, hRDboundary, hcover,
    by simpa only [M, U] using hregular'⟩

end DifferentialGeometry.Topology.PiecewiseLinear
