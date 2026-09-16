import DifferentialGeometry.Topology.PiecewiseLinear.CrosscutExtension
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement
import DifferentialGeometry.External.Schoenflies.AccessibleJoin

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem isPolygonal_of_isPLBall_one {A : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : IsPLBall 1 A) : Schoenflies.IsPolygonal A := by
  obtain ⟨γ, hγ⟩ := exists_isPLHomeomorphOn_Icc_of_isPLBall_one hA
  have harc : Schoenflies.IsArcBetween A (γ 0) (γ 1) :=
    ⟨γ, hγ.isPiecewiseAffineOn.continuousOn, hγ.bijOn.injOn, hγ.image_eq, rfl, rfl⟩
  have hne : γ 0 ≠ γ 1 :=
    fun h => zero_ne_one (hγ.bijOn.injOn (by norm_num) (by norm_num) h)
  obtain ⟨K, hKfin, hKA⟩ := hA.isPolyhedron.exists_simplicialComplex
  have : Finite K.faces := hKfin.to_subtype
  have hK : IsPLBall 1 K.space := hKA.symm ▸ hA
  have hpoly : ∀ s ∈ K.faces,
      Schoenflies.IsPolygonal (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 2)))) := by
    intro s hs
    have hcard := card_le_of_isPLBall K hK hs
    have hpos := Finset.card_pos.mpr (K.nonempty_of_mem_faces hs)
    by_cases hsmall : s.card = 1
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hsmall
      simpa only [Finset.coe_singleton, convexHull_singleton, segment_same] using
        Schoenflies.isPolygonal_segment a a
    · obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.mp (show s.card = 2 by omega)
      simpa only [Finset.coe_pair, convexHull_pair] using Schoenflies.isPolygonal_segment a b
  have hspace : (⋃ s ∈ K.faces, convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 2)))) = A := hKA
  obtain ⟨vs, -, -, -, hsub, hvs⟩ := Schoenflies.exists_simple_poly_of_biUnion_finite hKfin hpoly
    (hspace.symm ▸ hA.isConnected.isPreconnected) hne
    (hspace.symm ▸ harc.left_mem) (hspace.symm ▸ harc.right_mem)
  rw [hspace] at hsub
  exact ⟨vs, (harc.eq_of_subset hvs hsub).symm⟩

theorem isCrosscut_image_of_disk_arc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {D J P : Set E} {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hC : IsPLSphere 1 C) {s : E → EuclideanSpace ℝ (Fin 2)}
    (hs : IsPLHomeomorphOn s D (closure (Schoenflies.inside C))) (hsJ : s '' J = C)
    (hJD : J ⊆ D) {γ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) P)
    (hPD : P ⊆ D) (hinter : P ∩ J = {γ 0, γ 1}) :
    Schoenflies.IsCrosscut C (s '' P) (s (γ 0)) (s (γ 1)) := by
  have hP : IsPLBall 1 P := (isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn hγ
  have hsP := hs.restrict hP.isPolyhedron hPD
  have hη := hγ.trans hsP
  have harc : Schoenflies.IsArcBetween (s '' P) (s (γ 0)) (s (γ 1)) :=
    ⟨s ∘ γ, hη.isPiecewiseAffineOn.continuousOn, hη.bijOn.injOn, hη.image_eq, rfl, rfl⟩
  have hmeet : s '' P ∩ C = {s (γ 0), s (γ 1)} := by
    rw [← hsJ, ← hs.bijOn.injOn.image_inter hPD hJD, hinter, image_pair]
  refine ⟨isJordanCurve_of_isPLSphere_one hC, harc,
    isPolygonal_of_isPLBall_one (hP.of_isPLHomeomorphOn hsP), ?_, ?_, ?_⟩
  · exact (hmeet.symm.subset (by simp)).2
  · exact (hmeet.symm.subset (by simp)).2
  · intro x hx
    have hxD : x ∈ closure (Schoenflies.inside C) := by
      obtain ⟨y, hy, rfl⟩ := hx.1
      exact hs.bijOn.mapsTo (hPD hy)
    rw [(Schoenflies.IsRegionOf.inside C).closure_eq
      (Schoenflies.jordan_curve_theorem (isJordanCurve_of_isPLSphere_one hC))] at hxD
    exact hxD.resolve_right fun hxC => hx.2 (hmeet.subset ⟨hx.1, hxC⟩)

private theorem exists_planar_disk_coordinates {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {D : Set E} (hD : IsPLBall 2 D) :
    ∃ (C : Set (EuclideanSpace ℝ (Fin 2))) (s : E → EuclideanSpace ℝ (Fin 2)),
      IsPLSphere 1 C ∧ IsPLHomeomorphOn s D (closure (Schoenflies.inside C)) := by
  obtain ⟨T, hT, hcard, -, -, -⟩ := exists_affineIndependent_openSimplex_subset
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1)
    (0 : EuclideanSpace ℝ (Fin 2)) (Filter.univ_mem : univ ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin 2)))
  have hC := (isPLBall_convexHull_of_affineIndependent T hT hcard).isPLSphere_frontier
  obtain ⟨u, hu⟩ := hD
  obtain ⟨v, hv⟩ := isPLBall_closure_inside_of_isPLSphere_one hC
  exact ⟨_, _, hC, hu.symm.trans hv⟩

theorem exists_isPLHomeomorphOn_eqOn_disk_crosscut
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {D J P : Set E} {D' J' P' : Set F}
    {u : (Fin 3 → ℝ) → E} (hu : IsPLHomeomorphOn u (stdSimplex ℝ (Fin 3)) D)
    (huJ : u '' stdSimplexBoundary 2 = J)
    {u' : (Fin 3 → ℝ) → F} (hu' : IsPLHomeomorphOn u' (stdSimplex ℝ (Fin 3)) D')
    (huJ' : u' '' stdSimplexBoundary 2 = J')
    {γ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) P)
    (hPD : P ⊆ D) (hinter : P ∩ J = {γ 0, γ 1}) (hPD' : P' ⊆ D')
    {f : E → F} (hf : IsPLHomeomorphOn f (J ∪ P) (J' ∪ P'))
    (hfJ : f '' J = J') (hfP : f '' P = P') :
    ∃ G : E → F, IsPLHomeomorphOn G D D' ∧ EqOn G f (J ∪ P) := by
  have hJ : IsPLSphere 1 J := huJ ▸ hu.isPLSphere_image_stdSimplexBoundary
  have hJ' : IsPLSphere 1 J' := huJ' ▸ hu'.isPLSphere_image_stdSimplexBoundary
  have hJD : J ⊆ D := by
    rw [← huJ]
    rintro x ⟨y, hy, rfl⟩
    exact hu.bijOn.mapsTo hy.1
  have hJD' : J' ⊆ D' := by
    rw [← huJ']
    rintro x ⟨y, hy, rfl⟩
    exact hu'.bijOn.mapsTo hy.1
  have hP : IsPLBall 1 P := (isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn hγ
  have hfP' : IsPLHomeomorphOn f P P' := hfP ▸ hf.restrict hP.isPolyhedron subset_union_right
  have hP' := hP.of_isPLHomeomorphOn hfP'
  have hγ' := hγ.trans hfP'
  have hinter' : P' ∩ J' = {(f ∘ γ) 0, (f ∘ γ) 1} := by
    rw [← hfP, ← hfJ, ← hf.bijOn.injOn.image_inter subset_union_right subset_union_left,
      hinter, image_pair]
    rfl
  obtain ⟨C, s, hC, hs⟩ := exists_planar_disk_coordinates ⟨u, hu⟩
  obtain ⟨C', t, hC', ht⟩ := exists_planar_disk_coordinates ⟨u', hu'⟩
  have hsJ : s '' J = C := by
    rw [← huJ, ← image_comp]
    exact (hu.trans hs).image_stdSimplexBoundary.trans (frontier_closure_inside_of_isPLSphere_one hC)
  have htJ : t '' J' = C' := by
    rw [← huJ', ← image_comp]
    exact (hu'.trans ht).image_stdSimplexBoundary.trans (frontier_closure_inside_of_isPLSphere_one hC')
  have hcross := isCrosscut_image_of_disk_arc hC hs hsJ hJD hγ hPD hinter
  have hcross' := isCrosscut_image_of_disk_arc hC' ht htJ hJD' hγ' hPD' hinter'
  have hsJP : IsPLHomeomorphOn s (J ∪ P) (C ∪ s '' P) := by
    have h := hs.restrict (hJ.isPolyhedron.union hP.isPolyhedron) (union_subset hJD hPD)
    rwa [image_union, hsJ] at h
  have htJP : IsPLHomeomorphOn t (J' ∪ P') (C' ∪ t '' P') := by
    have h := ht.restrict (hJ'.isPolyhedron.union hP'.isPolyhedron) (union_subset hJD' hPD')
    rwa [image_union, htJ] at h
  let v := Function.invFunOn s (J ∪ P)
  let b := t ∘ f ∘ v
  have hb : IsPLHomeomorphOn b (C ∪ s '' P) (C' ∪ t '' P') := (hsJP.symm.trans hf).trans htJP
  have hv : ∀ x ∈ J ∪ P, v (s x) = x := fun x hx => hsJP.bijOn.invOn_invFunOn.1 hx
  have hvC : v '' C = J := by
    rw [← hsJ, image_image]
    exact (show EqOn (v ∘ s) id J from fun x hx => hv x (Or.inl hx)).image_eq.trans (image_id J)
  have hvP : v '' (s '' P) = P := by
    rw [image_image]
    exact (show EqOn (v ∘ s) id P from fun x hx => hv x (Or.inr hx)).image_eq.trans (image_id P)
  have hbC : b '' C = C' := by rw [show b = t ∘ f ∘ v from rfl, image_comp, image_comp, hvC, hfJ, htJ]
  have hbP : b '' (s '' P) = t '' P' := by
    rw [show b = t ∘ f ∘ v from rfl, image_comp, image_comp, hvP, hfP]
  have hb0 : b (s (γ 0)) = t (f (γ 0)) := by
    change t (f (v (s (γ 0)))) = _
    rw [hv _ (Or.inr (hγ.bijOn.mapsTo (by norm_num)))]
  have hb1 : b (s (γ 1)) = t (f (γ 1)) := by
    change t (f (v (s (γ 1)))) = _
    rw [hv _ (Or.inr (hγ.bijOn.mapsTo (by norm_num)))]
  obtain ⟨H, hH, hHb⟩ := exists_isPLHomeomorphOn_eqOn_crosscut hC
    (hP.of_isPLHomeomorphOn (hs.restrict hP.isPolyhedron hPD)) hcross hb hbC hbP (by
      rw [hb0, hb1]
      exact hcross')
  refine ⟨_, (hs.trans hH).trans ht.symm, ?_⟩
  intro x hx
  change Function.invFunOn t D' (H (s x)) = f x
  rw [hHb (hsJP.bijOn.mapsTo hx)]
  change Function.invFunOn t D' (t (f (v (s x)))) = f x
  rw [hv x hx]
  exact ht.bijOn.invOn_invFunOn.1 ((union_subset hJD' hPD') (hf.bijOn.mapsTo hx))

end DifferentialGeometry.Topology.PiecewiseLinear
