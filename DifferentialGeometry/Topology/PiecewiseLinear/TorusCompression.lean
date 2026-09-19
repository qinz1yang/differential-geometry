/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleSolidTorus
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalCircle
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalCompression

/-!
# Embedded torus compression along a nonseparating essential circle
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_embedded_torus_compression :
    ∃ (f : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3))
      (K R P : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (hKfin : K.faces.Finite) (hRfin : R.faces.Finite) (hPfin : P.faces.Finite),
      letI := hKfin.to_subtype
      letI := hRfin.to_subtype
      letI := hPfin.to_subtype
      let J := stdSimplexBoundary 2
      let C := f '' (J ×ˢ {(1 / 4 : ℝ)})
      let W := f '' (J ×ˢ Icc (0 : ℝ) (1 / 2))
      let D₀ := f '' (stdSimplex ℝ (Fin 3) ×ˢ {(0 : ℝ)})
      let D₁ := f '' (stdSimplex ℝ (Fin 3) ×ˢ {(1 / 2 : ℝ)})
      let D := f '' (stdSimplex ℝ (Fin 3) ×ˢ {(1 / 4 : ℝ)})
      IsCombinatorialManifold 2 K ∧ IsConnected K.space ∧
      Nonempty (K.space ≃ₜ (loopCircle × loopCircle)) ∧
      K.space = f '' (J ×ˢ Icc (0 : ℝ) 1) ∧
      IsCombinatorialManifoldWithBoundary 2 R ∧ IsConnected R.space ∧
      R.space = closure (K.space \ W) ∧ W ∪ R.space = K.space ∧
      W ∩ R.space = f '' (J ×ˢ {(0 : ℝ), 1 / 2}) ∧
      (boundaryComplex 2 R).space = f '' (J ×ˢ {(0 : ℝ), 1 / 2}) ∧
      IsPLHomeomorphOn f (J ×ˢ Icc (0 : ℝ) (1 / 2)) W ∧
      IsPLSphere 1 C ∧ (∀ x ∈ C, W ∈ 𝓝[K.space] x) ∧
      (∃ hCK : C ⊆ K.space,
        ¬ (⟨Set.inclusion hCK, continuous_inclusion hCK⟩ : C(C, K.space)).Nullhomotopic) ∧
      IsConnected (K.space \ C) ∧
      IsPLHomeomorphOn (fun x => f (x, 1 / 4)) (stdSimplex ℝ (Fin 3)) D ∧
      K.space ∩ D = C ∧
      IsPLHomeomorphOn (fun x => f (x, 0)) (stdSimplex ℝ (Fin 3)) D₀ ∧
      IsPLHomeomorphOn (fun x => f (x, 1 / 2)) (stdSimplex ℝ (Fin 3)) D₁ ∧
      Disjoint D₀ D₁ ∧
      K.space ∩ D₀ = (fun x => f (x, 0)) '' stdSimplexBoundary 2 ∧
      K.space ∩ D₁ = (fun x => f (x, 1 / 2)) '' stdSimplexBoundary 2 ∧
      R.space ∩ D₀ = (fun x => f (x, 0)) '' stdSimplexBoundary 2 ∧
      R.space ∩ D₁ = (fun x => f (x, 1 / 2)) '' stdSimplexBoundary 2 ∧
      (fun x => f (x, 0)) '' stdSimplexBoundary 2 = f '' (J ×ˢ {(0 : ℝ)}) ∧
      (fun x => f (x, 1 / 2)) '' stdSimplexBoundary 2 = f '' (J ×ˢ {(1 / 2 : ℝ)}) ∧
      IsPLSphere 2 P.space ∧ P.space = R.space ∪ D₀ ∪ D₁ ∧
      Homology.bettiOne K.space = 2 ∧ Homology.bettiOne P.space = 0 ∧
      Homology.bettiOne P.space < Homology.bettiOne K.space := by
  let _ : DecidableEq (Fin 3 → ℝ) := Classical.decEq _
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  let J := stdSimplexBoundary 2
  have hJ : IsPLSphere 1 J := by
    rw [show J = stdSimplexBoundary 2 from rfl, ← simplexBoundary_stdVertices_space 1]
    exact isPLSphere_simplexBoundary_std 1
  let e := (EuclideanSpace.equiv (Fin 3) ℝ).symm
  have he : IsPLHomeomorphOn e J (e '' J) := by
    apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hJ.isPolyhedron
      ((isPiecewiseAffineOn_of_affine e.toLinearMap.toAffineMap isOpen_univ).mono_of_isPolyhedron
        hJ.isPolyhedron (subset_univ _))
    exact e.injective.injOn.bijOn_image
  obtain ⟨N, f, hNfin, -, -, -, hf, hends⟩ :=
    (hJ.of_isPLHomeomorphOn he).exists_solid_torus_neighborhood (by simp)
  let _ : Finite N.faces := hNfin.to_subtype
  obtain ⟨D, hDfin, hDsp⟩ := (isPLBall_stdSimplex 2).isPolyhedron.exists_simplicialComplex
  let _ : Finite D.faces := hDfin.to_subtype
  have hp : IsPLHomeomorphOn id (stdSimplex ℝ (Fin 3)) D.space := by
    rw [hDsp]
    exact (isPLBall_stdSimplex 2).isPolyhedron.isPLHomeomorphOn_id
  have hD : IsPLBall 2 D.space := ⟨id, hp⟩
  have hDJ : (boundaryComplex 2 D).space = J := by
    rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex D hp,
      simplexBoundary_stdVertices_space, image_id]
  have hfD : IsCylindricalDiagram f D.space N.space := hDsp.symm ▸ hf
  have hendsD : ∀ x ∈ D.space, f (x, 0) = f (x, 1) := hDsp.symm ▸ hends
  have hcompression := hfD.exists_capped_surface_of_eq_ends D hp hendsD
    (by simp) (a := 1 / 2) (by norm_num)
  simp only [hDsp, hDJ, id_eq] at hcompression
  obtain ⟨K, R, P, hKfin, hRfin, hPfin, hK, hKc, hKsp, hR, hRc, hRsp,
    hcover, htrace, hRbd, hr₀, hr₁, hdis, hKmeet₀, hKmeet₁, hmeet₀, hmeet₁, hbd₀, hbd₁,
    hP, hPsp, hβK, hβP, hlt⟩ := hcompression
  let _ : Finite K.faces := hKfin.to_subtype
  let _ : Finite R.faces := hRfin.to_subtype
  let _ : Finite P.faces := hPfin.to_subtype
  have hside : IsCylindricalDiagram f J (f '' (J ×ˢ Icc (0 : ℝ) 1)) := by
    have h := hfD.boundary D hD.isCombinatorialManifoldWithBoundary
    change IsCylindricalDiagram f (boundaryComplex 2 D).space
      (f '' ((boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1)) at h
    rwa [hDJ] at h
  have hJsub : J ⊆ stdSimplex ℝ (Fin 3) := fun _ hx => hx.1
  have hendJ : ∀ x ∈ J, f (x, 0) = f (x, 1) := fun x hx => hends x (hJsub hx)
  obtain ⟨u, -⟩ := hside.exists_homeomorph_prod_circle_of_eq_ends
    hJ.isPolyhedron.isCompact hendJ
  obtain ⟨v⟩ := nonempty_homeomorph_loopCircle_of_isPLSphere_one hJ
  have htorus : Nonempty (K.space ≃ₜ (loopCircle × loopCircle)) :=
    ⟨(Homeomorph.setCongr hKsp).trans
      (u.trans (Homeomorph.prodCongr v.symm (Homeomorph.refl _)))⟩
  have hRcl : R.space = closure (K.space \ f '' (J ×ˢ Icc (0 : ℝ) (1 / 2))) := by
    rw [hKsp, hside.closure_sdiff_image_strip hJ.isPolyhedron.isCompact
      (a := 1 / 2) (by norm_num), hRsp]
  have hW := hside.isPLHomeomorphOn_strip hJ.isPolyhedron
    (a := 0) (b := 1 / 2) (by norm_num) (by norm_num) (Or.inr (by norm_num))
  have hcore := hside.isPLHomeomorphOn_slice hJ.isPolyhedron
    (t := 1 / 4) (by norm_num)
  let C := f '' (J ×ˢ {(1 / 4 : ℝ)})
  have hCK : C ⊆ K.space := by
    rw [hKsp]
    exact image_mono (fun _ hz => ⟨hz.1, hz.2.symm ▸ by norm_num⟩)
  have hnon : ¬ (⟨Set.inclusion hCK, continuous_inclusion hCK⟩ : C(C, K.space)).Nullhomotopic := by
    intro hn
    let w : C(K.space, f '' (J ×ˢ Icc (0 : ℝ) 1)) := Homeomorph.setCongr hKsp
    have hn' := (hn.comp_left (hcore.homeomorph : C(J, C))).comp_right w
    apply hside.not_nullhomotopic_slice hJ hendJ (t := 1 / 4) (by norm_num)
    convert hn' using 1
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    rfl
  have hCc : IsConnected (K.space \ C) := by
    rw [hKsp]
    exact hside.isConnected_sdiff_slice hJ.isConnected (by norm_num)
  have hDmid := hf.isPLHomeomorphOn_slice (isPLBall_stdSimplex 2).isPolyhedron
    (t := 1 / 4) (by norm_num)
  have hDmeet : K.space ∩ f '' (stdSimplex ℝ (Fin 3) ×ˢ {(1 / 4 : ℝ)}) = C := by
    rw [hKsp]
    exact hf.image_subcylinder_inter_slice hJsub hends (by norm_num)
  have hWnhds : ∀ x ∈ C, f '' (J ×ˢ Icc (0 : ℝ) (1 / 2)) ∈ 𝓝[K.space] x := by
    rintro x ⟨z, hz, rfl⟩
    have hzt : z.2 = 1 / 4 := hz.2
    rw [hKsp]
    exact hside.image_strip_mem_nhdsWithin hJ.isPolyhedron.isCompact
      (a := 0) (b := 1 / 2) (t := z.2)
      (by norm_num) (by norm_num) (by rw [hzt]; norm_num) (by rw [hzt]; norm_num) hz.1
  refine ⟨f, K, R, P, hKfin, hRfin, hPfin, hK, hKc, htorus, hKsp, hR, hRc, hRcl,
    hcover, htrace, ?_, hW, hJ.of_isPLHomeomorphOn hcore, hWnhds, ⟨hCK, hnon⟩, hCc,
    hDmid, hDmeet, hr₀, hr₁, hdis, hKmeet₀, hKmeet₁, hmeet₀, hmeet₁,
    hbd₀, hbd₁, hP, hPsp, hβK, hβP, hlt⟩
  exact (congrArg (fun d : DecidableEq (EuclideanSpace ℝ (Fin 3)) =>
    (@boundaryComplex _ _ _ d 2 R).space) (Subsingleton.elim _ _)).trans hRbd

end DifferentialGeometry.Topology.PiecewiseLinear
