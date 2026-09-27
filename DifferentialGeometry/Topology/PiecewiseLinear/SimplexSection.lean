/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PolytopeSection
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexAffine
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.HeightIndex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_lt_and_gt_of_mem_convexHull_fiber {E : Type*} [AddCommGroup E] [Module ℝ E]
    (s : Finset E) (a : E →ᵃ[ℝ] ℝ) {r : ℝ}
    (havoid : ∀ v ∈ s, a v ≠ r)
    (hne : (convexHull ℝ (s : Set E) ∩ {x | a x = r}).Nonempty) :
    (∃ x ∈ s, a x < r) ∧ ∃ y ∈ s, r < a y := by
  obtain ⟨p, hp, hpr⟩ := hne
  constructor
  · by_contra hno
    push Not at hno
    have hsub : (s : Set E) ⊆ a ⁻¹' Ioi r := by
      intro v hv
      exact lt_of_le_of_ne (hno v hv) (havoid v hv).symm
    have hpgt := convexHull_min hsub ((convex_Ioi r).affine_preimage a) hp
    exact (show r < a p from hpgt).ne hpr.symm
  · by_contra hno
    push Not at hno
    have hsub : (s : Set E) ⊆ a ⁻¹' Iio r := by
      intro v hv
      exact lt_of_le_of_ne (hno v hv) (havoid v hv)
    have hplt := convexHull_min hsub ((convex_Iio r).affine_preimage a) hp
    exact (show a p < r from hplt).ne hpr

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem isPLBall_convexHull_inter_fiber_of_affineIndependent {n : ℕ}
    (s : Finset E) (hs : AffineIndependent ℝ ((↑) : s → E)) (hcard : s.card = n + 2)
    (a : E →ᵃ[ℝ] ℝ) {r : ℝ}
    (hbelow : ∃ x ∈ s, a x < r) (habove : ∃ y ∈ s, r < a y) :
    IsPLBall n (convexHull ℝ (s : Set E) ∩ {x | a x = r}) := by
  obtain ⟨T, hT, hTcard, -⟩ := exists_affineIndependent_openSimplex_superset (n + 1)
    (show Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1 by simp)
    (show Bornology.IsBounded (∅ : Set (EuclideanSpace ℝ (Fin (n + 1)))) from
        Bornology.isBounded_empty)
  obtain ⟨A, hA⟩ := exists_isPLHomeomorphOn_affine_of_card_eq hT hs (by omega)
  let g := (a.comp A).linear
  let c := a (A 0)
  have hheight (x : EuclideanSpace ℝ (Fin (n + 1))) : a (A x) = g x + c := by
    simpa only [vadd_eq_add, add_zero, AffineMap.comp_apply] using (a.comp A).map_vadd 0 x
  have hlow : ∃ x ∈ convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin (n + 1)))), g x < r - c := by
    obtain ⟨x, hx, hxr⟩ := hbelow
    obtain ⟨y, hy, hyx⟩ := hA.bijOn.surjOn (subset_convexHull ℝ _ hx)
    refine ⟨y, hy, ?_⟩
    rw [← hyx, hheight] at hxr
    linarith
  have hhigh : ∃ y ∈ convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin (n + 1)))), r - c < g y := by
    obtain ⟨x, hx, hrx⟩ := habove
    obtain ⟨y, hy, hyx⟩ := hA.bijOn.surjOn (subset_convexHull ℝ _ hx)
    refine ⟨y, hy, ?_⟩
    rw [← hyx, hheight] at hrx
    linarith
  have hg : g ≠ 0 := by
    intro hz
    obtain ⟨x, -, hx⟩ := hlow
    obtain ⟨y, -, hy⟩ := hhigh
    rw [hz, LinearMap.zero_apply] at hx hy
    exact (hx.trans hy).false
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  have hinter : (interior (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin (n + 1)))))).Nonempty := by
    rw [interior_convexHull_eq_openSimplex hT (by simpa using hTcard)]
    exact ⟨T.centroid ℝ id, centroid_mem_openSimplex hTne⟩
  have hball := (isHPolytope_convexHull_of_affineIndependent T hT).isPLBall_inter_fiber_of_lt_of_lt
    (n := n) (by simp) hinter g hg hlow hhigh
  have himage : A '' (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∩
      {x | g x = r - c}) = convexHull ℝ (s : Set E) ∩ {x | a x = r} := by
    ext x
    constructor
    · rintro ⟨y, ⟨hy, hyr⟩, rfl⟩
      refine ⟨hA.bijOn.mapsTo hy, ?_⟩
      change a (A y) = r
      rw [hheight, hyr, sub_add_cancel]
    · rintro ⟨hx, hxr⟩
      obtain ⟨y, hy, hyx⟩ := hA.bijOn.surjOn hx
      refine ⟨y, ⟨hy, ?_⟩, hyx⟩
      change g y = r - c
      have hh := hheight y
      rw [hyx, hxr] at hh
      linarith
  exact himage ▸ hball.of_isPLHomeomorphOn (hA.restrict hball.isPolyhedron inter_subset_left)

theorem isPLBall_convexHull_inter_fiber_of_ne_vertex_heights {n : ℕ}
    (s : Finset E) (hs : AffineIndependent ℝ ((↑) : s → E)) (hcard : s.card = n + 2)
    (a : E →ᵃ[ℝ] ℝ) {r : ℝ} (havoid : ∀ v ∈ s, a v ≠ r)
    (hne : (convexHull ℝ (s : Set E) ∩ {x | a x = r}).Nonempty) :
    IsPLBall n (convexHull ℝ (s : Set E) ∩ {x | a x = r}) := by
  obtain ⟨hbelow, habove⟩ := exists_lt_and_gt_of_mem_convexHull_fiber s a havoid hne
  exact isPLBall_convexHull_inter_fiber_of_affineIndependent s hs hcard a hbelow habove

omit [FiniteDimensional ℝ E] in
theorem convexHull_inter_fiber_eq_singleton_or_exists_lt_and_gt
    (s : Finset E) (hs : AffineIndependent ℝ ((↑) : s → E))
    (ℓ : E →ₗ[ℝ] ℝ) (hinj : InjOn ℓ (s : Set E)) {r : ℝ}
    (hne : (convexHull ℝ (s : Set E) ∩ {x | ℓ x = r}).Nonempty) :
    (∃ v ∈ s, convexHull ℝ (s : Set E) ∩ {x | ℓ x = r} = {v}) ∨
      ((∃ v ∈ s, ℓ v < r) ∧ ∃ w ∈ s, r < ℓ w) := by
  let K := simplexComplex s hs
  let _ : Finite K.faces := (simplexComplex_faces_finite s hs).to_subtype
  have hsne : s.Nonempty := by
    by_contra hno
    have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hno
    simp only [he, Finset.coe_empty, convexHull_empty, empty_inter, Set.not_nonempty_empty] at hne
  have hspace : K.space = convexHull ℝ (s : Set E) := simplexComplex_space s hs hsne
  have hverts : K.vertices ⊆ (s : Set E) :=
    fun v hv => hv.2 (Finset.mem_singleton_self v)
  obtain ⟨p, hp, hpr⟩ := hne
  have hpK : p ∈ K.space := hspace.symm.subset hp
  obtain ⟨v, hv, w, hw, hbounds, hmin, hmax⟩ :=
    exists_extreme_height_fibers K ⟨p, hpK⟩ ℓ (hinj.mono hverts)
  by_cases hvr : ℓ v = r
  · refine Or.inl ⟨v, hverts hv, ?_⟩
    rwa [hspace, hvr] at hmin
  by_cases hwr : ℓ w = r
  · refine Or.inl ⟨w, hverts hw, ?_⟩
    rwa [hspace, hwr] at hmax
  have hbd := hbounds p hpK
  rw [show ℓ p = r from hpr] at hbd
  exact Or.inr ⟨⟨v, hverts hv, lt_of_le_of_ne hbd.1 hvr⟩,
    ⟨w, hverts hw, lt_of_le_of_ne hbd.2 (Ne.symm hwr)⟩⟩

theorem isPLBall_zero_or_isPLBall_convexHull_inter_fiber
    (s : Finset E) (hs : AffineIndependent ℝ ((↑) : s → E))
    (ℓ : E →ₗ[ℝ] ℝ) (hinj : InjOn ℓ (s : Set E)) {r : ℝ}
    (hne : (convexHull ℝ (s : Set E) ∩ {x | ℓ x = r}).Nonempty) :
    IsPLBall 0 (convexHull ℝ (s : Set E) ∩ {x | ℓ x = r}) ∨
      IsPLBall (s.card - 2) (convexHull ℝ (s : Set E) ∩ {x | ℓ x = r}) := by
  rcases convexHull_inter_fiber_eq_singleton_or_exists_lt_and_gt s hs ℓ hinj hne with
    ⟨v, -, heq⟩ | ⟨hbelow, habove⟩
  · exact Or.inl (isPLBall_zero_iff.mpr ⟨v, heq⟩)
  · have hcard : 2 ≤ s.card := by
      obtain ⟨v, hv, hvr⟩ := hbelow
      obtain ⟨w, hw, hrw⟩ := habove
      by_contra hno
      have hle : s.card ≤ 1 := by omega
      have hvw := Finset.card_le_one.mp hle v hv w hw
      exact (hvr.trans hrw).ne (congrArg ℓ hvw)
    exact Or.inr (isPLBall_convexHull_inter_fiber_of_affineIndependent s hs
      (Nat.sub_add_cancel hcard).symm ℓ.toAffineMap hbelow habove)

open Classical in
theorem isPLBall_zero_or_one_inter_face_fibers
    (K : Geometry.SimplicialComplex ℝ E) {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hscard : s.card ≤ 4) (htcard : t.card ≤ 4)
    (hne : s ≠ t) (ℓ : E →ₗ[ℝ] ℝ) (hinj : InjOn ℓ K.vertices) (r : ℝ)
    (hinter : ((convexHull ℝ (s : Set E) ∩ {x | ℓ x = r}) ∩
      (convexHull ℝ (t : Set E) ∩ {x | ℓ x = r})).Nonempty) :
    IsPLBall 0 ((convexHull ℝ (s : Set E) ∩ {x | ℓ x = r}) ∩
      (convexHull ℝ (t : Set E) ∩ {x | ℓ x = r})) ∨
    IsPLBall 1 ((convexHull ℝ (s : Set E) ∩ {x | ℓ x = r}) ∩
      (convexHull ℝ (t : Set E) ∩ {x | ℓ x = r})) := by
  have hcard : (s ∩ t).card ≤ 3 := by
    by_contra! hbig
    have hsEq : s ∩ t = s := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have htEq : s ∩ t = t := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    exact hne (hsEq.symm.trans htEq)
  have heq : ((convexHull ℝ (s : Set E) ∩ {x | ℓ x = r}) ∩
      (convexHull ℝ (t : Set E) ∩ {x | ℓ x = r})) =
      convexHull ℝ ((s ∩ t : Finset E) : Set E) ∩ {x | ℓ x = r} := by
    ext x
    constructor
    · rintro ⟨⟨hxs, hxr⟩, hxt, -⟩
      exact ⟨by simpa only [Finset.coe_inter] using K.inter_subset_convexHull hs ht ⟨hxs, hxt⟩, hxr⟩
    · rintro ⟨hx, hxr⟩
      exact ⟨⟨convexHull_mono (Finset.coe_subset.mpr Finset.inter_subset_left) hx, hxr⟩,
        convexHull_mono (Finset.coe_subset.mpr Finset.inter_subset_right) hx, hxr⟩
  have hverts : ((s ∩ t : Finset E) : Set E) ⊆ K.vertices := fun v hv =>
    K.down_closed hs (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mp hv).1)
      (Finset.singleton_nonempty v)
  rw [heq] at hinter ⊢
  rcases isPLBall_zero_or_isPLBall_convexHull_inter_fiber (s ∩ t)
    (affineIndependent_of_subset (K.indep hs) Finset.inter_subset_left) ℓ (hinj.mono hverts) hinter
        with h | h
  · exact Or.inl h
  · have hdim : (s ∩ t).card - 2 = 0 ∨ (s ∩ t).card - 2 = 1 := by omega
    exact hdim.elim (fun hz => Or.inl (hz ▸ h)) (fun hz => Or.inr (hz ▸ h))
end DifferentialGeometry.Topology.PiecewiseLinear
