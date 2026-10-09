import DifferentialGeometry.Topology.PiecewiseLinear.Approximation.RelativeApproximation
import DifferentialGeometry.Topology.SimplicialComplex.Barycentric.Subdivision.BarycentricSubcomplex

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology

noncomputable section

set_option linter.unusedSectionVars false

variable {E : Type*} [DecidableEq E]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_relative_barycentric_approximation {n d : ℕ}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (L : SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces)
    (hd : ∀ s ∈ K.faces, s.card ≤ d + 1)
    (g : C(K.space, EuclideanSpace ℝ (Fin n)))
    (hPL : ∀ s ∈ L.faces, ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x : K.space, x.val ∈ convexHull ℝ (s : Set E) → g x = A x.val)
    (hinj : InjOn g (Subtype.val ⁻¹' L.space)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ w : E → EuclideanSpace ℝ (Fin n),
      ∃ H : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n),
      let P := barycentricSubdivisionIter K N
      let hP := barycentricSubdivisionIter_finite_faces K hK N
      let hspace := barycentricSubdivisionIter_space K N
      (∀ s : Finset E, (s : Set E) ⊆ P.vertices → s.card ≤ n + 1 →
        AffineIndependent ℝ (fun a : s => w a)) ∧
      (∀ x : P.space, x.val ∈ L.space →
        correctedInterpolant P hP w H x = g (Homeomorph.setCongr hspace x)) ∧
      (∀ x : P.space,
        ‖correctedInterpolant P hP w H x - g (Homeomorph.setCongr hspace x)‖ < ε) ∧
      (∃ R : SimplicialComplex ℝ E, R.faces.Finite ∧ R.space = P.space ∧
        simplicialRefines R P ∧ (∀ s ∈ R.faces, s.card ≤ d + 1) ∧
        ∀ s ∈ R.faces, ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
          ∀ x : P.space, x.val ∈ convexHull ℝ (s : Set E) →
            correctedInterpolant P hP w H x = A x.val) ∧
      (∀ y, ‖H y - y‖ < ε) ∧ (∀ y, ‖H.symm y - y‖ < ε) := by
  classical
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp (isCompact_space_of_finite_faces K hK)
  obtain ⟨δ, hδ, hgδ⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous g.continuous) (ε / 2) (by positivity)
  obtain ⟨D, hD, hmesh⟩ := exists_mesh_bound K hK
  obtain ⟨N, hN⟩ := exists_barycentric_mesh_bound_lt d D hδ
  let P := barycentricSubdivisionIter K N
  let hP := barycentricSubdivisionIter_finite_faces K hK N
  let hspace := barycentricSubdivisionIter_space K N
  let J := barycentricSubdivisionIter L N
  have hJP : J.faces ⊆ P.faces := barycentricSubdivisionIter_faces_subset hLK N
  have hJspace : J.space = L.space := barycentricSubdivisionIter_space L N
  have hJref : simplicialRefines J L := barycentricSubdivisionIter_refines L N
  have hPdim : ∀ s ∈ P.faces, s.card ≤ d + 1 := barycentricSubdivisionIter_face_card_le K hd N
  have hPmesh : ∀ s ∈ P.faces, diam (convexHull ℝ (s : Set E)) < δ := by
    intro s hs
    exact (hmesh.barycentricSubdivisionIter_of_face_card_le hD hd N s hs).trans_lt (hN N le_rfl)
  have hLspace : L.space ⊆ K.space := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    exact K.convexHull_subset_space (hLK hs) hxs
  let gP : C(P.space, EuclideanSpace ℝ (Fin n)) :=
    g.comp ⟨Homeomorph.setCongr hspace, (Homeomorph.setCongr hspace).continuous⟩
  let v : E → EuclideanSpace ℝ (Fin n) :=
    fun x => if hx : x ∈ K.space then g ⟨x, hx⟩ else 0
  have hveq (x : E) (hx : x ∈ K.space) : v x = g ⟨x, hx⟩ := dite_eq_left hx
  have hvJ : ∀ s ∈ J.faces, ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      EqOn v A (convexHull ℝ (s : Set E)) := by
    intro s hs
    obtain ⟨t, ht, hst⟩ := hJref s hs
    obtain ⟨A, hA⟩ := hPL t ht
    refine ⟨A, fun x hx => ?_⟩
    have hxK := K.convexHull_subset_space (hLK ht) (hst hx)
    exact (hveq x hxK).trans (hA ⟨x, hxK⟩ (hst hx))
  have hvInj : InjOn v J.space := by
    intro x hx y hy he
    have hxL : x ∈ L.space := hJspace.subset hx
    have hyL : y ∈ L.space := hJspace.subset hy
    rw [hveq x (hLspace hxL), hveq y (hLspace hyL)] at he
    exact congrArg Subtype.val (hinj (x₁ := ⟨x, hLspace hxL⟩)
      (x₂ := ⟨y, hLspace hyL⟩) hxL hyL he)
  obtain ⟨w, H, Q, hQ, hgp, hrel, hnear, hmap, hHaff, hHsmall, hHinvSmall⟩ :=
    exists_relative_interpolant_of_embedded_subcomplex_with_correction_control P hP J hJP v hvJ hvInj
      (show 0 < ε / 2 by positivity)
  have hvertex (a : E) (ha : a ∈ P.vertices) :
      v a = gP ⟨a, P.vertices_subset_space ha⟩ := by
    exact hveq a (hspace.subset (P.vertices_subset_space ha))
  have hosc (s : P.faces) (x y : P.space)
      (hx : x.val ∈ convexHull ℝ (s.val : Set E))
      (hy : y.val ∈ convexHull ℝ (s.val : Set E)) : ‖gP x - gP y‖ < ε / 2 := by
    rw [← dist_eq_norm]
    apply hgδ
    change dist x.val y.val < δ
    exact (dist_le_diam_of_mem (s.val.finite_toSet.isCompact_convexHull ℝ).isBounded hx hy).trans_lt
      (hPmesh s.val s.property)
  have happrox (x : P.space) : ‖interpolateVertices P hP v x - gP x‖ < ε / 2 := by
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp x.property
    apply interpolateVertices_norm_sub_lt_of_face P hP v ⟨s, hs⟩ x hxs (gP x)
    intro a ha
    have haP := face_vertices_subset P ⟨s, hs⟩ ha
    rw [hvertex a haP]
    exact hosc ⟨s, hs⟩ ⟨a, P.vertices_subset_space haP⟩ x (subset_convexHull ℝ _ ha) hxs
  refine ⟨N, w, H, hgp, ?_, ?_,
    exists_subdivision_correctedInterpolant P hP w H Q hQ hmap hHaff hPdim,
    fun y => (hHsmall y).trans (by linarith), fun y => (hHinvSmall y).trans (by linarith)⟩
  · intro x hx
    exact (hrel x (hJspace.symm.subset hx)).trans (hveq x.val (hspace.subset x.property))
  · intro x
    change ‖correctedInterpolant P hP w H x - gP x‖ < ε
    calc
      _ ≤ ‖correctedInterpolant P hP w H x - interpolateVertices P hP v x‖ +
          ‖interpolateVertices P hP v x - gP x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hnear x) (happrox x)
      _ = ε := add_halves ε

end

end DifferentialGeometry.Topology.Engulfing
