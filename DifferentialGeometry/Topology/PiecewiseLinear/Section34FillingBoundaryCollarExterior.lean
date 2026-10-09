import DifferentialGeometry.Topology.PiecewiseLinear.Section34PairedCornerCollarExterior
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FillingExteriorModel
import DifferentialGeometry.Topology.PiecewiseLinear.Collar.RelativeExtension

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_filling_boundary_exterior_collar_preserving_corners
    {P : Set (EuclideanSpace ℝ (Fin 3))} (hP : IsPLBall 3 P)
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite R.faces]
    (hR : IsCombinatorialManifoldWithBoundary 3 R) (hRP : R.space ⊆ interior P)
    {f : Fin 2 → (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)}
    {C : Fin 2 → Set (EuclideanSpace ℝ (Fin 3))} {X Y O : Set (EuclideanSpace ℝ (Fin 3))}
    (hf : ∀ k, IsCylindricalDiagram (f k) spliceSquare (C k))
    (hends : ∀ k, ∀ p ∈ spliceSquare, f k (p, 0) = f k (p, 1)) (a b : Fin 2 → Bool)
    (hfirst : ∀ k, f k '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2) =
      C k ∩ frontier X)
    (hsecond : ∀ k, f k '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3) =
      C k ∩ frontier Y)
    (hpages : ∀ k, ∀ i : Fin 4, f k '' section34MarkedRibbon i = C k ∩
      ![frontier X ∩ Y, frontier Y ∩ X, frontier X \ interior Y, frontier Y \ interior X] i)
    (hX : IsClosed X) (hY : IsClosed Y)
    (hquad : ∀ k, f k '' (section34CrossingQuadrant (a k) (b k) ×ˢ Icc (0 : ℝ) 1) =
      C k ∩ R.space)
    (hcontactX : R.space ∩ frontier X ⊆ frontier R.space)
    (hcontactY : R.space ∩ frontier Y ⊆ frontier R.space)
    (hfrontR : frontier R.space ⊆ frontier X ∪ frontier Y)
    (haxisC : ∀ k, f k '' section34MarkedAxis ⊆ interior (C k))
    (hdis : Disjoint (C 0) (C 1)) (hCP : ∀ k, C k ⊆ interior P)
    (hO : O ∈ 𝓝ˢ[P] (frontier R.space)) :
    let J := (f 0 '' section34MarkedAxis) ∪ (f 1 '' section34MarkedAxis)
    let B := fun k => f k '' (section34CornerBase (a k) (b k) ×ˢ Icc (0 : ℝ) 1)
    ∃ (c : ℝ) (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (W : Set (EuclideanSpace ℝ (Fin 3)))
      (ρ : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3)),
      0 < c ∧ c ≤ 1 ∧ L.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 2 L ∧
      L.space ⊆ frontier R.space ∩ (B 0 ∪ B 1) ∧ J ⊆ L.space ∧
      (∀ x ∈ J, L.space ∈ 𝓝[frontier R.space] x) ∧
      IsPolyhedron W ∧ W ⊆ interior P ∩ O ∧
      IsPLHomeomorphOn ρ (frontier R.space ×ˢ Icc (0 : ℝ) c) W ∧
      (∀ x ∈ frontier R.space, ρ (x, 0) = x) ∧ W ∩ R.space = frontier R.space ∧
      MapsTo ρ (frontier R.space ×ˢ Ioc (0 : ℝ) c) (interior P \ R.space) ∧
      ∀ k, ∀ p ∈ section34CornerBase (a k) (b k), ∀ s ∈ Icc (0 : ℝ) 1,
        f k (p, s) ∈ L.space → ∀ t ∈ Icc (0 : ℝ) c,
          ρ (f k (p, s), t) = f k (section34CornerExteriorPush (a k) (b k) (p, t), s) ∧
          (ρ (f k (p, s), t) ∈ frontier X ↔ p.2 = (if b k then t / 2 else -t / 2)) ∧
          (ρ (f k (p, s), t) ∈ frontier Y ↔ p.1 = (if a k then t / 2 else -t / 2)) := by
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  let J := (f 0 '' section34MarkedAxis) ∪ (f 1 '' section34MarkedAxis)
  let B := fun k => f k '' (section34CornerBase (a k) (b k) ×ˢ Icc (0 : ℝ) 1)
  let V := fun k => f k '' ((section34CornerExteriorPush (a k) (b k) ''
    (section34CornerBase (a k) (b k) ×ˢ Icc (0 : ℝ) 1)) ×ˢ Icc (0 : ℝ) 1)
  have hRc := (isPolyhedron_space R).isClosed
  obtain ⟨K, hKfin, hK, -, hKP, hRK, hreadK⟩ :=
    exists_section34_filling_exterior_model hP R hR hRP
  let _ : Finite K.faces := hKfin.to_subtype
  have hKfront : (boundaryComplex 3 K).space = frontier K.space :=
    (frontier_space_eq_boundaryComplex_space_of_finrank (by simp) K hK).symm
  obtain ⟨ρ₀, hρ₀, -, -, hbottom₀, hconj, -, hW₀C, hBfront, -, htrace₀, -, hread₀, hbase⟩ :=
    exists_paired_crossing_corner_exterior_collar hf hends a b hfirst hsecond hpages hX hY
      hRc hquad hcontactX hcontactY hfrontR haxisC hdis
  have hW₀P := hW₀C.trans (inter_subset_left.trans (union_subset (hCP 0) (hCP 1)))
  have hW₀K := fun y hy => (hreadK y (hW₀P hy)).1.mpr
    (by simpa only [closure_compl, mem_compl_iff] using (hW₀C hy).2)
  have htraceK : (V 0 ∪ V 1) ∩ (boundaryComplex 3 K).space = B 0 ∪ B 1 := by
    rw [hKfront]
    apply Subset.antisymm
    · intro y hy
      exact htrace₀.subset ⟨hy.1, (hreadK y (hW₀P hy.1)).2.2.mp hy.2⟩
    · intro y hy
      have hm := htrace₀.symm.subset hy
      exact ⟨hm.1, hRK hm.2⟩
  have hzero (k : Fin 2) : (0 : ℝ × ℝ) ∈ section34CornerBase (a k) (b k) := by
    cases a k <;> cases b k <;> norm_num [section34CornerBase]
  have hJB (k : Fin 2) : f k '' section34MarkedAxis ⊆ B k :=
    image_mono (prod_mono (singleton_subset_iff.mpr (hzero k)) subset_rfl)
  have hJfront : J ⊆ frontier R.space := (union_subset_union (hJB 0) (hJB 1)).trans hBfront
  have haxis : IsPolyhedron section34MarkedAxis :=
    (isHPolytope_singleton (0 : ℝ × ℝ)).isPolyhedron.prod isHPolytope_Icc.isPolyhedron
  have haxissub : section34MarkedAxis ⊆ spliceCylinder :=
    (section34_marked_axis_subset_ribbon 0).trans (section34_marked_ribbon_subset_cylinder 0)
  have hJpoly (k : Fin 2) : IsPolyhedron (f k '' section34MarkedAxis) :=
    ((hf k).isPiecewiseAffineOn.mono_of_isPolyhedron haxis haxissub).isPolyhedron_image haxis
  let H := boundaryComplex 3 R
  let _ : Finite H.faces := (boundaryComplex_faces_finite 3 R).to_subtype
  have hH : IsCombinatorialManifoldWithBoundary 2 H :=
    (isCombinatorialManifold_boundaryComplex R hR).isCombinatorialManifoldWithBoundary
  have hHspace : H.space = frontier R.space :=
    (frontier_space_eq_boundaryComplex_space_of_finrank (by simp) R hR).symm
  have hHK : H.space ⊆ (boundaryComplex 3 K).space := by
    rw [hHspace, hKfront]
    exact hRK
  have hOK : O ∩ interior P ∈ 𝓝ˢ[K.space] H.space := by
    obtain ⟨V, hV, hRV, hVP⟩ := mem_nhdsSetWithin.mp hO
    refine mem_nhdsSetWithin.mpr ⟨V ∩ interior P, hV.inter isOpen_interior, ?_, ?_⟩
    · intro x hx
      exact ⟨hRV (hHspace.subset hx), hRP (hRc.frontier_subset (hHspace.subset hx))⟩
    · intro x hx
      exact ⟨hVP ⟨hx.1.1, hKP hx.2⟩, hx.1.2⟩
  obtain ⟨c, L, W, ρ, _, hc, hc1, hLfin, hL, hLB, hLnhds, hW, hWO, hρ, hfix,
    hbottom, htrace, hpositive, -⟩ :=
    exists_relative_collar_extension_of_polyhedral_mark_with_support K H hK hH hHK
      ((hJpoly 0).union (hJpoly 1)) (by rw [hHspace]; exact hJfront)
      (by rw [hHspace]; exact hbase) hOK (by norm_num : (0 : ℝ) < 1)
      hρ₀ hW₀K hbottom₀ htraceK
  rw [hHspace] at hLB hLnhds hρ hbottom htrace hpositive
  have hfrontW : frontier R.space ⊆ W := htrace.symm.subset.trans inter_subset_left
  have hWR : W ∩ R.space = frontier R.space := by
    apply Subset.antisymm
    · intro x hx
      exact ⟨subset_closure hx.2, (hreadK x (hWO hx.1).2.2).1.mp (hWO hx.1).1⟩
    · exact subset_inter hfrontW hRc.frontier_subset
  refine ⟨c, L, W, ρ, hc, hc1, hLfin, hL, hLB,
    fun x hx => mem_of_mem_nhdsWithin (hJfront hx) (hLnhds x hx), hLnhds,
    hW, fun x hx => ⟨(hWO hx).2.2, (hWO hx).2.1⟩, hρ, hbottom, hWR, ?_, ?_⟩
  · intro z hz
    have hm := hpositive hz
    have hp := (hWO (hρ.bijOn.mapsTo ⟨hz.1, hz.2.1.le, hz.2.2⟩)).2.2
    refine ⟨hp, (hreadK _ hp).2.1.mp ?_⟩
    apply (mem_interior_iff_notMem_frontier hm.1).mpr
    rw [← hKfront]
    exact hm.2
  · intro k p hp s hs hLps t ht
    have he : ρ (f k (p, s), t) = ρ₀ (f k (p, s), t) := hfix ⟨hLps, ht⟩
    refine ⟨he.trans (hconj k p hp s hs t ⟨ht.1, ht.2.trans hc1⟩), ?_⟩
    rw [he]
    exact hread₀ k p hp s hs t ⟨ht.1, ht.2.trans hc1⟩

end DifferentialGeometry.Topology.PiecewiseLinear
