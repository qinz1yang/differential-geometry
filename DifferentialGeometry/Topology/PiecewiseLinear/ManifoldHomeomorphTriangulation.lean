/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.IsomorphicSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.PLMap
import DifferentialGeometry.Topology.PiecewiseLinear.PieceMap
import DifferentialGeometry.Topology.PiecewiseLinear.PieceTransition

/-!
# Triangulating PL manifold homeomorphisms
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {m n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

theorem PLPieceIn.isPLHomeomorphOn_conjugate
    (T : PLPieceIn (EuclideanSpace ℝ (Fin m)) n X univ) (h : X ≃ₜ X)
    (hh : IsPL n n h) :
    IsPLHomeomorphOn
      (Function.invFunOn T.map T.complex.space ∘ (h : X → X) ∘ T.map)
      T.complex.space T.complex.space := by
  have hid : IsPiecewiseAffineOn (id : EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℝ (Fin m)) T.complex.space :=
    (isPiecewiseAffineOn_id isOpen_univ).mono_of_isPolyhedron T.isPolyhedron_space
      (subset_univ _)
  have hT : IsPLOn m n T.map T.complex.space := by
    simpa only [Function.comp_id] using T.isPLOn_comp hid fun _ hx => hx
  have hcomp : IsPLOn m n ((h : X → X) ∘ T.map) T.complex.space :=
    hh.comp_isPLOn hT
  have hpa : IsPiecewiseAffineOn
      (Function.invFunOn T.map T.complex.space ∘ ((h : X → X) ∘ T.map))
      T.complex.space := by
    simpa only [preimage_univ, inter_univ] using
      T.isPiecewiseAffineOn_invFunOn_comp hcomp
  have hinv : BijOn (Function.invFunOn T.map T.complex.space) univ T.complex.space :=
    T.bijOn.invOn_invFunOn.symm.bijOn T.bijOn.surjOn.mapsTo_invFunOn T.bijOn.mapsTo
  have hbij : BijOn
      (Function.invFunOn T.map T.complex.space ∘ (h : X → X) ∘ T.map)
      T.complex.space T.complex.space :=
    hinv.comp (h.bijective.bijOn_univ.comp T.bijOn)
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn T.isPolyhedron_space hpa hbij

theorem PLPieceIn.map_conjugate_eqOn
    (T : PLPieceIn (EuclideanSpace ℝ (Fin m)) n X univ) (h : X ≃ₜ X) :
    EqOn
      (T.map ∘ (Function.invFunOn T.map T.complex.space ∘ (h : X → X) ∘ T.map))
      ((h : X → X) ∘ T.map) T.complex.space := by
  intro x _
  exact T.bijOn.invOn_invFunOn.2 (mem_univ (h (T.map x)))

open Classical in
theorem PLPieceIn.exists_compatible_isGlueIso_of_homeomorph
    (T : PLPieceIn (EuclideanSpace ℝ (Fin m)) n X univ) (h : X ≃ₜ X)
    (hh : IsPL n n h) {J : Type*} [Finite J]
    (Q : J → Set (EuclideanSpace ℝ (Fin m))) (hQ : ∀ j, IsPolyhedron (Q j))
    (hQK : ∀ j, Q j ⊆ T.complex.space) :
    ∃ (K₀ K₁ : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m)))
        (q' : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
        (D : J → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))),
      IsSubdivision K₀ T.complex ∧ K₀.faces.Finite ∧
      IsSubdivision K₁ T.complex ∧ K₁.faces.Finite ∧
      IsGlueIso K₀ K₁
        (Function.invFunOn T.map T.complex.space ∘ (h : X → X) ∘ T.map) q' ∧
      EqOn
        (simplicialMap K₀
          (Function.invFunOn T.map T.complex.space ∘ (h : X → X) ∘ T.map))
        (Function.invFunOn T.map T.complex.space ∘ (h : X → X) ∘ T.map)
        T.complex.space ∧
      (∀ j, (DifferentialGeometry.Topology.PiecewiseLinear.restrict K₀ (Q j)).space = Q j) ∧
      ∀ j, (D j).faces ⊆ K₁.faces ∧
        IsGlueIso (DifferentialGeometry.Topology.PiecewiseLinear.restrict K₀ (Q j)) (D j)
          (Function.invFunOn T.map T.complex.space ∘ (h : X → X) ∘ T.map) q' ∧
        (D j).space =
          (Function.invFunOn T.map T.complex.space ∘ (h : X → X) ∘ T.map) '' Q j := by
  let _ : Finite T.complex.faces := T.finite_faces.to_subtype
  let q := Function.invFunOn T.map T.complex.space ∘ (h : X → X) ∘ T.map
  obtain ⟨R, hRT, hRfin, hQR⟩ :=
    exists_isSubdivision_subcomplexes T.complex Q hQ hQK
  let _ : Finite R.faces := hRfin.to_subtype
  have hq : IsPLHomeomorphOn q R.space R.space := by
    simpa only [q, hRT.space_eq] using T.isPLHomeomorphOn_conjugate h hh
  obtain ⟨K₀, K₁, q', hK₀R, hK₀fin, hK₁R, hK₁fin, hglue, hsimple⟩ :=
    exists_isGlueIso_of_isPLHomeomorphOn R R hq
  have hsource (j : J) :
      (DifferentialGeometry.Topology.PiecewiseLinear.restrict K₀ (Q j)).space = Q j := by
    have hRsource :
        (DifferentialGeometry.Topology.PiecewiseLinear.restrict R (Q j)).space = Q j :=
      restrict_space_of_eq_biUnion R (Q j) (hQR j)
    have hsub := hK₀R.restrict
      (DifferentialGeometry.Topology.PiecewiseLinear.restrict R (Q j))
      (restrict_faces_subset R (Q j))
    have hspace := hsub.space_eq
    rw [hRsource] at hspace
    exact hspace
  have hexists (j : J) :
      ∃ D : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m)),
        D.faces ⊆ K₁.faces ∧
          IsGlueIso (DifferentialGeometry.Topology.PiecewiseLinear.restrict K₀ (Q j)) D q q' :=
    hglue.exists_subcomplex
      (DifferentialGeometry.Topology.PiecewiseLinear.restrict K₀ (Q j))
      (restrict_faces_subset K₀ (Q j))
  choose D hDK₁ hD using hexists
  have himage (j : J) : (D j).space = q '' Q j := by
    have heq : EqOn
        (simplicialMap (DifferentialGeometry.Topology.PiecewiseLinear.restrict K₀ (Q j)) q) q
        (DifferentialGeometry.Topology.PiecewiseLinear.restrict K₀ (Q j)).space := by
      intro x hx
      have hxK₀ : x ∈ K₀.space :=
        space_mono_of_faces_subset (restrict_faces_subset K₀ (Q j)) hx
      have hxR : x ∈ R.space := hK₀R.space_eq ▸ hxK₀
      have hsubmap : simplicialMap K₀ q x =
          simplicialMap (DifferentialGeometry.Topology.PiecewiseLinear.restrict K₀ (Q j)) q x := by
        obtain ⟨s, hs, hxs⟩ :=
          (DifferentialGeometry.Topology.PiecewiseLinear.restrict K₀ (Q j)).mem_space_iff.mp hx
        rw [simplicialMap_eq_of_mem K₀ q (restrict_faces_subset K₀ (Q j) hs) hxs,
          simplicialMap_eq_of_mem
            (DifferentialGeometry.Topology.PiecewiseLinear.restrict K₀ (Q j)) q hs hxs]
      exact hsubmap.symm.trans (hsimple hxR)
    exact (hD j).image_left.symm.trans ((heq.image_eq).trans (by rw [hsource j]))
  refine ⟨K₀, K₁, q', D, hK₀R.trans hRT, hK₀fin, hK₁R.trans hRT, hK₁fin,
    hglue, ?_, hsource, ?_⟩
  · simpa only [q, hRT.space_eq] using hsimple
  · intro j
    exact ⟨hDK₁ j, hD j, himage j⟩

end DifferentialGeometry.Topology.PiecewiseLinear
