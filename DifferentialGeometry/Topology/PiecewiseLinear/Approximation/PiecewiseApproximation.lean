import DifferentialGeometry.Topology.PiecewiseLinear.Approximation.OptimalMap
import DifferentialGeometry.Topology.SimplicialComplex.Barycentric.Subdivision.FineSubdivision
import Mathlib.Topology.UniformSpace.HeineCantor

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Topology _root_.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem isCompact_space_of_finite_faces (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    IsCompact K.space :=
  hK.isCompact_biUnion (fun s _ => s.finite_toSet.isCompact_convexHull ℝ)

theorem exists_piecewise_affine_generalPosition_approximation_of_face_card_le {n d : ℕ}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hd : ∀ s ∈ K.faces, s.card ≤ d + 1)
    (g : C(K.space, EuclideanSpace ℝ (Fin n))) {ε : ℝ} (hε : 0 < ε) :
    ∃ (L : SimplicialComplex ℝ E) (hL : L.faces.Finite) (hspace : L.space = K.space),
      simplicialRefines L K ∧ (∀ s ∈ L.faces, s.card ≤ d + 1) ∧
      ∃ w : E → EuclideanSpace ℝ (Fin n),
        (∀ s : Finset E, (s : Set E) ⊆ L.vertices → s.card ≤ n + 1 →
          AffineIndependent ℝ (fun v : s => w v)) ∧
        ∀ x : L.space,
          ‖interpolateVertices L hL w x - g (Homeomorph.setCongr hspace x)‖ < ε := by
  classical
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp (isCompact_space_of_finite_faces K hK)
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨δ, hδ, hgδ⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous g.continuous)
    (ε / 2) hε2
  obtain ⟨L, hL, hspace, href, hmesh, hdim⟩ := exists_fine_subdivision_of_face_card_le K hK hd hδ
  let e : L.space ≃ₜ K.space := Homeomorph.setCongr hspace
  let gL : C(L.space, EuclideanSpace ℝ (Fin n)) := g.comp ⟨e, e.continuous⟩
  have hosc (s : L.faces) (x y : L.space)
      (hx : x.1 ∈ convexHull ℝ (s.1 : Set E)) (hy : y.1 ∈ convexHull ℝ (s.1 : Set E)) :
      ‖gL x - gL y‖ < ε / 2 := by
    rw [← dist_eq_norm]
    apply hgδ
    change dist x.1 y.1 < δ
    exact (dist_le_diam_of_mem (s.1.finite_toSet.isCompact_convexHull ℝ).isBounded hx hy).trans_lt
      (hmesh s.1 s.2)
  obtain ⟨w, hgp, hw⟩ := exists_generalPosition_interpolant L hL gL hε2 hosc
  refine ⟨L, hL, hspace, href, hdim, w, hgp, fun x => ?_⟩
  simpa [gL, e, add_halves] using hw x

theorem exists_piecewise_affine_generalPosition_approximation {n : ℕ}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : C(K.space, EuclideanSpace ℝ (Fin n))) {ε : ℝ} (hε : 0 < ε) :
    ∃ (L : SimplicialComplex ℝ E) (hL : L.faces.Finite) (hspace : L.space = K.space),
      simplicialRefines L K ∧ ∃ w : E → EuclideanSpace ℝ (Fin n),
        (∀ s : Finset E, (s : Set E) ⊆ L.vertices → s.card ≤ n + 1 →
          AffineIndependent ℝ (fun v : s => w v)) ∧
        ∀ x : L.space,
          ‖interpolateVertices L hL w x - g (Homeomorph.setCongr hspace x)‖ < ε := by
  have hd : ∀ s ∈ K.faces, s.card ≤ Module.finrank ℝ E + 1 := by
    intro s hs
    simpa only [Fintype.card_coe] using (K.indep hs).card_le_finrank_succ.trans
      (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  obtain ⟨L, hL, heq, href, -, hw⟩ :=
    exists_piecewise_affine_generalPosition_approximation_of_face_card_le K hK hd g hε
  exact ⟨L, hL, heq, href, hw⟩

end DifferentialGeometry.Topology.Engulfing
