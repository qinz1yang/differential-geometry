/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.IsomorphicSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.PLMap
import DifferentialGeometry.Topology.PiecewiseLinear.PieceMap
import DifferentialGeometry.Topology.PiecewiseLinear.PieceTransition

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

theorem PLPieceIn.isPLHomeomorphOn_conjugate
    (T : PLPieceIn E n X univ) (h : X ≃ₜ X)
    (hh : IsPL n n h) :
    IsPLHomeomorphOn
      (Function.invFunOn T.map T.complex.space ∘ (h : X → X) ∘ T.map)
      T.complex.space T.complex.space := by
  let d := Module.finrank ℝ E
  let e : E ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
    (Module.finBasis ℝ E).equivFun.trans (WithLp.linearEquiv 2 ℝ _).symm
  let P := e '' T.complex.space
  have he' : IsPiecewiseAffineOn (e : E → EuclideanSpace ℝ (Fin d)) T.complex.space :=
    (isPiecewiseAffineOn_of_affine e.toLinearMap.toAffineMap isOpen_univ).mono_of_isPolyhedron
      T.isPolyhedron_space (subset_univ _)
  have hP : IsPolyhedron P :=
    T.isPolyhedron_space.image_of_isPiecewiseAffineOn he' e.injective.injOn
  have he : IsPiecewiseAffineOn (e.symm : EuclideanSpace ℝ (Fin d) → E) P :=
    (isPiecewiseAffineOn_of_affine e.symm.toLinearMap.toAffineMap isOpen_univ).mono_of_isPolyhedron
      hP (subset_univ _)
  have hemap : MapsTo (e.symm : EuclideanSpace ℝ (Fin d) → E) P T.complex.space := by
    rintro y ⟨x, hx, rfl⟩
    simpa only [LinearEquiv.symm_apply_apply] using hx
  have hT : IsPLOn d n (T.map ∘ (e.symm : EuclideanSpace ℝ (Fin d) → E)) P :=
    T.isPLOn_comp he hemap
  have hcomp : IsPLOn d n
      ((h : X → X) ∘ T.map ∘ (e.symm : EuclideanSpace ℝ (Fin d) → E)) P := by
    simpa only [Function.comp_assoc] using hh.comp_isPLOn hT
  let q := Function.invFunOn T.map T.complex.space ∘ (h : X → X) ∘ T.map
  have hqe : IsPiecewiseAffineOn
      (q ∘ (e.symm : EuclideanSpace ℝ (Fin d) → E)) P := by
    simpa only [q, Function.comp_assoc, preimage_univ, inter_univ] using
      T.isPiecewiseAffineOn_invFunOn_comp hcomp
  have hpa' := hqe.comp he'
  have hemap' : MapsTo (e : E → EuclideanSpace ℝ (Fin d)) T.complex.space P :=
    fun x hx => ⟨x, hx, rfl⟩
  have hdomain : T.complex.space ∩ e ⁻¹' P = T.complex.space :=
    inter_eq_left.mpr hemap'
  rw [hdomain] at hpa'
  have hpa : IsPiecewiseAffineOn q T.complex.space :=
    hpa'.congr fun x _ => by simp only [Function.comp_apply, LinearEquiv.symm_apply_apply]
  have hinv : BijOn (Function.invFunOn T.map T.complex.space) univ T.complex.space :=
    T.bijOn.invOn_invFunOn.symm.bijOn T.bijOn.surjOn.mapsTo_invFunOn T.bijOn.mapsTo
  have hbij : BijOn q T.complex.space T.complex.space :=
    hinv.comp (h.bijective.bijOn_univ.comp T.bijOn)
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn T.isPolyhedron_space hpa hbij

omit [FiniteDimensional ℝ E] in
theorem PLPieceIn.map_conjugate_eqOn
    (T : PLPieceIn E n X univ) (h : X ≃ₜ X) :
    EqOn
      (T.map ∘ (Function.invFunOn T.map T.complex.space ∘ (h : X → X) ∘ T.map))
      ((h : X → X) ∘ T.map) T.complex.space := by
  intro x _
  exact T.bijOn.invOn_invFunOn.2 (mem_univ (h (T.map x)))

open Classical in
theorem PLPieceIn.exists_compatible_isGlueIso_of_homeomorph
    (T : PLPieceIn E n X univ) (h : X ≃ₜ X)
    (hh : IsPL n n h) {J : Type*} [Finite J]
    (Q : J → Set E) (hQ : ∀ j, IsPolyhedron (Q j))
    (hQK : ∀ j, Q j ⊆ T.complex.space) :
    ∃ (K₀ K₁ : Geometry.SimplicialComplex ℝ E) (q' : E → E)
        (D : J → Geometry.SimplicialComplex ℝ E),
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
      ∃ D : Geometry.SimplicialComplex ℝ E,
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
