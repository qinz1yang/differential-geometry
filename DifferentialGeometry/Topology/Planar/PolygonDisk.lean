import DifferentialGeometry.Topology.Planar.PolygonRounding
import DifferentialGeometry.Topology.Planar.TriangleRounding
import DifferentialGeometry.External.ClassificationOfSurfaces.TriangleMeshGeometricFree

open Set Metric
open scoped ContDiff Manifold

namespace Schoenflies

private theorem PrePolygon.exists_diffeomorph_corner_replacement_of_triangle_mesh
    {m : ℕ} (P : PrePolygon m)
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (hsupport : M.toPlaneComplex.support = closure (inside P.carrier))
    (hfrontier : frontier M.toPlaneComplex.support = P.carrier) :
    let I := {i : ZMod (m + 3) //
      Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0}
    ∀ (e : I → Plane ≃ᵃ[ℝ] Plane) (U : I → Set Plane) (r σ ε R : I → ℝ),
      (∀ i, 0 < r i ∧ e i (P.vertex (i.val - 1)) = Plane.mk (-1) 0 ∧
        e i (P.vertex (i.val + 1)) = Plane.mk (r i) (r i) ∧ e i (P.vertex i) = 0) →
      (∀ i, IsOpen (U i)) → (∀ i, σ i = -1 ∨ σ i = 1) →
      (∀ i, 0 < ε i) → (∀ i, 3 * ε i < R i) →
      (∀ i, e i ⁻¹' closedBall (0 : Plane) (R i) ⊆ U i) →
      (Pairwise fun i j => Disjoint (U i) (U j)) →
      (∀ i, ∀ x ∈ U i, x ∈ closure (inside P.carrier) ↔
        0 ≤ σ i * ((e i x) 1 - max ((e i x) 0) 0)) →
      ∃ Φ : Plane ≃ₘ[ℝ] Plane,
        Φ '' closedBall (0 : Plane) 1 =
          (closure (inside P.carrier) \ ⋃ i, e i ⁻¹' ball (0 : Plane) (R i)) ∪
            ⋃ i, (e i ⁻¹' closedBall (0 : Plane) (R i)) ∩
              {x | 0 ≤ σ i * ((e i x) 1 - Real.smoothMax (ε i) ((e i x) 0) 0)} := by
  classical
  induction hcard : M.triangles.card using Nat.strong_induction_on generalizing M m with
  | h N ih =>
    dsimp only
    intro e U r σ ε R hnorm hU hσ hε hR hKU hdisj hside
    obtain ⟨x, hx⟩ := P.isSeparating_carrier.isConnected_inside.nonempty
    have hxS : x ∈ M.toPlaneComplex.support := hsupport ▸ subset_closure hx
    rw [M.toPlaneComplex_support] at hxS
    obtain ⟨t, ht, _⟩ := Set.mem_iUnion₂.mp hxS
    have hpos : 0 < M.triangles.card := Finset.card_pos.mpr ⟨t, ht⟩
    by_cases hcardone : M.triangles.card = 1
    · obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hcardone
      let T : M.Triangle := ⟨t, by rw [ht]; exact Finset.mem_singleton_self t⟩
      let b := LeanEval.Topology.ClassificationOfSurfaces.Moise.affineBasisOfTriangle
        (M.position ∘ M.orderedVertex T) (M.orderedVertex_affineIndependent T)
      have hrange : range b = M.position '' (t : Set M.Vertex) := by
        change range (M.position ∘ M.orderedVertex T) = _
        rw [Set.range_comp, M.range_orderedVertex T]
      have htriangle : convexHull ℝ (range b) = M.triangleCarrier t := by
        rw [hrange]
        rfl
      have hs : M.toPlaneComplex.support = M.triangleCarrier t := by
        rw [M.toPlaneComplex_support, ht]
        simp only [Finset.mem_singleton, iUnion_iUnion_eq_left]
        rfl
      have hregion : closure (inside P.carrier) = convexHull ℝ (range b) :=
        hsupport.symm.trans (hs.trans htriangle.symm)
      exact P.exists_diffeomorph_corner_replacement_of_triangle b hregion
        e U r σ ε R hnorm hU hσ hε hR hKU hdisj hside
    · have hmore : 1 < M.triangles.card := by omega
      obtain ⟨T, _, _, hfree, _⟩ :=
        M.exists_two_geometrically_free_triangles_of_jordan_support P.carrier
          P.isJordanCurve_carrier hsupport hmore
      obtain ⟨n, Q, hQ, hQB, f, V, s, η, A, g, W, s', η', A', H, C,
        hf, hVdisj, hg, hWdisj, _, _, _, _, _, himage, _, _⟩ :=
        P.exists_corner_replacement_isotopy_of_geometrically_free_triangle M hfrontier T hfree
      have hlt : (M.eraseTriangle T.1).triangles.card < N := by
        have hc := M.card_eraseTriangle_triangles T.2
        omega
      choose ρ hρ hfprev hfnext using fun i => (hf i).2.2.2.2.2.2.2.2
      choose ρ' hρ' hgprev hgnext using fun i => (hg i).2.2.2.2.2.2.2.2
      obtain ⟨Φ, hΦ⟩ := ih _ hlt Q (M.eraseTriangle T.1) hQB hQ.symm rfl
        g W ρ' s' η' A'
        (fun i => ⟨hρ' i, hgprev i, hgnext i, (hg i).2.2.1⟩)
        (fun i => (hg i).1) (fun i => (hg i).2.2.2.1)
        (fun i => (hg i).2.2.2.2.1) (fun i => (hg i).2.2.2.2.2.1)
        (fun i => (hg i).2.2.2.2.2.2.1) hWdisj
        (fun i => (hg i).2.2.2.2.2.2.2.1)
      let I := {i : ZMod (m + 3) //
        Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0}
      let D := (closure (inside P.carrier) \ ⋃ i, f i ⁻¹' ball (0 : Plane) (A i)) ∪
        ⋃ i, (f i ⁻¹' closedBall (0 : Plane) (A i)) ∩
          {x | 0 ≤ s i * ((f i x) 1 - Real.smoothMax (η i) ((f i x) 0) 0)}
      have hΦD : (Φ.trans (H 1).symm) '' closedBall (0 : Plane) 1 = D := by
        change (fun x => (H 1).symm (Φ x)) '' closedBall (0 : Plane) 1 = D
        rw [← Set.image_image, hΦ, ← himage]
        exact (H 1).symm_image_image D
      obtain ⟨Ψ, _, _, _, _, _, _, _, hΨ, _, _⟩ :=
        exists_isotopy_between_normalized_corner_replacements
          ![f, e] (fun i : I => P.vertex (i.val - 1))
          (fun i : I => P.vertex (i.val + 1)) (fun i : I => P.vertex i)
          ![V, U] ![ρ, r] (fun _ _ => 1) ![s, σ] ![η, ε] ![A, R]
          (D := closure (inside P.carrier))
          (by
            intro k i
            fin_cases k
            · exact ⟨hρ i, hfprev i, by simpa using hfnext i,
                (hf i).2.2.1⟩
            · simpa using hnorm i)
          (by
            intro k
            fin_cases k
            · exact fun i => (hf i).1
            · exact hU)
          (fun _ _ => Or.inr rfl)
          (by
            intro k
            fin_cases k
            · exact fun i => (hf i).2.2.2.1
            · exact hσ)
          (by
            intro k
            fin_cases k
            · exact fun i => (hf i).2.2.2.2.1
            · exact hε)
          (by
            intro k
            fin_cases k
            · exact fun i => (hf i).2.2.2.2.2.1
            · exact hR)
          (by
            intro k
            fin_cases k
            · exact fun i => (hf i).2.2.2.2.2.2.1
            · exact hKU)
          (by
            intro k
            fin_cases k
            · exact hVdisj
            · exact hdisj)
          (by
            intro k
            fin_cases k
            · simpa using fun i => (hf i).2.2.2.2.2.2.2.1
            · simpa using hside)
      refine ⟨(Φ.trans (H 1).symm).trans (Ψ 1), ?_⟩
      change (fun x => Ψ 1 ((Φ.trans (H 1).symm) x)) '' closedBall (0 : Plane) 1 = _
      rw [← Set.image_image, hΦD]
      simpa using hΨ

theorem PrePolygon.exists_diffeomorph_corner_replacement
    {m : ℕ} (P : PrePolygon m) :
    let I := {i : ZMod (m + 3) //
      Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0}
    ∀ (e : I → Plane ≃ᵃ[ℝ] Plane) (U : I → Set Plane) (r σ ε R : I → ℝ),
      (∀ i, 0 < r i ∧ e i (P.vertex (i.val - 1)) = Plane.mk (-1) 0 ∧
        e i (P.vertex (i.val + 1)) = Plane.mk (r i) (r i) ∧ e i (P.vertex i) = 0) →
      (∀ i, IsOpen (U i)) → (∀ i, σ i = -1 ∨ σ i = 1) →
      (∀ i, 0 < ε i) → (∀ i, 3 * ε i < R i) →
      (∀ i, e i ⁻¹' closedBall (0 : Plane) (R i) ⊆ U i) →
      (Pairwise fun i j => Disjoint (U i) (U j)) →
      (∀ i, ∀ x ∈ U i, x ∈ closure (inside P.carrier) ↔
        0 ≤ σ i * ((e i x) 1 - max ((e i x) 0) 0)) →
      ∃ Φ : Plane ≃ₘ[ℝ] Plane,
        Φ '' closedBall (0 : Plane) 1 =
          (closure (inside P.carrier) \ ⋃ i, e i ⁻¹' ball (0 : Plane) (R i)) ∪
            ⋃ i, (e i ⁻¹' closedBall (0 : Plane) (R i)) ∩
              {x | 0 ≤ σ i * ((e i x) 1 - Real.smoothMax (ε i) ((e i x) 0) 0)} := by
  obtain ⟨M, hsupport, hfrontier⟩ := P.exists_triangle_mesh_inside
  exact P.exists_diffeomorph_corner_replacement_of_triangle_mesh M hsupport hfrontier

private theorem normalized_corner_det_eq_zero
    (e : Plane ≃ᵃ[ℝ] Plane) {a p b : Plane} {r d : ℝ}
    (hr : r ≠ 0) (ha : e a = Plane.mk (-1) 0) (hp : e p = 0)
    (hb : e b = Plane.mk r (d * r)) :
    d = 0 ↔ Plane.det (a - p) (b - p) = 0 := by
  have he (x y : Plane) : e.linear (x - y) = e x - e y :=
    e.toAffineMap.linearMap_vsub x y
  have hea : e.linear (a - p) = Plane.mk (-1) 0 := by rw [he, ha, hp, sub_zero]
  have heb : e.linear (b - p) = Plane.mk r (d * r) := by rw [he, hb, hp, sub_zero]
  have hane : a - p ≠ 0 := by
    intro h
    have hz := congrArg (fun x => (e.linear x) 0) h
    rw [hea, map_zero] at hz
    norm_num [Plane.mk] at hz
  rw [Plane.det_eq_zero_iff_smul _ _ hane]
  constructor
  · intro hd
    refine ⟨-r, e.linear.injective ?_⟩
    rw [map_smul, hea, heb, hd, zero_mul]
    ext i
    fin_cases i <;> simp [Plane.mk]
  · rintro ⟨t, ht⟩
    have heq := congrArg e.linear ht
    rw [map_smul, hea, heb] at heq
    have hzero : d * r = 0 := by
      simpa [Plane.mk] using congrArg (fun x : Plane => x 1) heq
    exact (mul_eq_zero.mp hzero).resolve_right hr

theorem PrePolygon.exists_diffeomorph_vertex_rounding
    {m : ℕ} (P : PrePolygon m)
    (e : ZMod (m + 3) → Plane ≃ᵃ[ℝ] Plane)
    (U : ZMod (m + 3) → Set Plane) (r d σ ε R : ZMod (m + 3) → ℝ)
    (hnorm : ∀ i, 0 < r i ∧ e i (P.vertex (i - 1)) = Plane.mk (-1) 0 ∧
      e i (P.vertex (i + 1)) = Plane.mk (r i) (d i * r i) ∧ e i (P.vertex i) = 0)
    (hU : ∀ i, IsOpen (U i)) (hd : ∀ i, d i = 0 ∨ d i = 1)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 1) (hε : ∀ i, 0 < ε i)
    (hR : ∀ i, 3 * ε i < R i)
    (hKU : ∀ i, e i ⁻¹' closedBall (0 : Plane) (R i) ⊆ U i)
    (hdisj : Pairwise fun i j => Disjoint (U i) (U j))
    (hside : ∀ i, ∀ x ∈ U i, x ∈ closure (inside P.carrier) ↔
      0 ≤ σ i * ((e i x) 1 - d i * max ((e i x) 0) 0)) :
    ∃ Φ : Plane ≃ₘ[ℝ] Plane,
      Φ '' closedBall (0 : Plane) 1 =
        (closure (inside P.carrier) \ ⋃ i, e i ⁻¹' ball (0 : Plane) (R i)) ∪
          ⋃ i, (e i ⁻¹' closedBall (0 : Plane) (R i)) ∩
            {x | 0 ≤ σ i * ((e i x) 1 - d i * Real.smoothMax (ε i) ((e i x) 0) 0)} := by
  let I := {i : ZMod (m + 3) //
    Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0}
  have hstraight (i : ZMod (m + 3)) : d i = 0 ↔
      Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) = 0 :=
    normalized_corner_det_eq_zero (e i) (hnorm i).1.ne'
      (hnorm i).2.1 (hnorm i).2.2.2 (hnorm i).2.2.1
  have hdI (i : I) : d i = 1 :=
    (hd i).resolve_left (fun h => i.property ((hstraight i).mp h))
  obtain ⟨Φ, hΦ⟩ := P.exists_diffeomorph_corner_replacement
    (fun i : I => e i) (fun i : I => U i) (fun i : I => r i)
    (fun i : I => σ i) (fun i : I => ε i) (fun i : I => R i)
    (fun i => by simpa only [hdI i, one_mul] using hnorm i)
    (fun i => hU i) (fun i => hσ i) (fun i => hε i) (fun i => hR i)
    (fun i => hKU i)
    (fun i j hij => hdisj (fun h => hij (Subtype.ext h)))
    (fun i => by simpa only [hdI i, one_mul] using hside i)
  have heq := Set.indexed_replacement_eq_subtype_of_inactive (closure (inside P.carrier))
    (fun i => e i ⁻¹' ball (0 : Plane) (R i))
    (fun i => e i ⁻¹' closedBall (0 : Plane) (R i))
    (fun i => {x | 0 ≤ σ i * ((e i x) 1 - d i * Real.smoothMax (ε i) ((e i x) 0) 0)})
    (fun i => Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0)
    (fun i => preimage_mono (f := e i) ball_subset_closedBall)
    (fun i j hij => (hdisj hij).mono (hKU i) (hKU j))
    (fun i hi x hx => by
      have hd0 : d i = 0 := (hstraight i).mpr (not_ne_iff.mp hi)
      simpa only [mem_ofPred_eq, hd0, zero_mul, sub_zero] using (hside i x (hKU i hx)).symm)
  refine ⟨Φ, ?_⟩
  rw [heq]
  simpa only [hdI, one_mul] using hΦ

end Schoenflies
