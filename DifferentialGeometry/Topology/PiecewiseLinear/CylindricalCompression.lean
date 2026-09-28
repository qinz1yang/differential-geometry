/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalSurface
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalMonodromy
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusCapping
import DifferentialGeometry.Topology.PiecewiseLinear.PrismSphere

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem IsCylindricalDiagram.exists_capped_surface
    (D : Geometry.SimplicialComplex ℝ E) [Finite D.faces]
    {p : (Fin 3 → ℝ) → E} (hp : IsPLHomeomorphOn p (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D.space)
    {f : E × ℝ → F} {S : Set F} (hf : IsCylindricalDiagram f D.space S)
    (hdim : Module.finrank ℝ F = 3) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    let J := (boundaryComplex 2 D).space
    let D₀ := f '' (D.space ×ˢ {0})
    let D₁ := f '' (D.space ×ˢ {a})
    ∃ (K R P : Geometry.SimplicialComplex ℝ F)
      (hKfin : K.faces.Finite) (hRfin : R.faces.Finite) (hPfin : P.faces.Finite),
      letI := hKfin.to_subtype
      letI := hRfin.to_subtype
      letI := hPfin.to_subtype
      IsCombinatorialManifold 2 K ∧ IsConnected K.space ∧
      K.space = f '' (J ×ˢ Icc (0 : ℝ) 1) ∧
      IsCombinatorialManifoldWithBoundary 2 R ∧ IsConnected R.space ∧
      R.space = f '' (J ×ˢ Icc a 1) ∧
      f '' (J ×ˢ Icc 0 a) ∪ R.space = K.space ∧
      f '' (J ×ˢ Icc 0 a) ∩ R.space = f '' (J ×ˢ {0, a}) ∧
      (boundaryComplex 2 R).space = f '' (J ×ˢ {0, a}) ∧
      IsPLHomeomorphOn (fun x => f (p x, 0)) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀ ∧
      IsPLHomeomorphOn (fun x => f (p x, a)) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁ ∧
      Disjoint D₀ D₁ ∧
      K.space ∩ D₀ = (fun x => f (p x, 0)) '' stdSimplexBoundary 2 ∧
      K.space ∩ D₁ = (fun x => f (p x, a)) '' stdSimplexBoundary 2 ∧
      R.space ∩ D₀ = (fun x => f (p x, 0)) '' stdSimplexBoundary 2 ∧
      R.space ∩ D₁ = (fun x => f (p x, a)) '' stdSimplexBoundary 2 ∧
      (fun x => f (p x, 0)) '' stdSimplexBoundary 2 = f '' (J ×ˢ {0}) ∧
      (fun x => f (p x, a)) '' stdSimplexBoundary 2 = f '' (J ×ˢ {a}) ∧
      IsPLSphere 2 P.space ∧ P.space = R.space ∪ D₀ ∪ D₁ ∧
      Homology.bettiOne K.space = 2 ∧ Homology.bettiOne P.space = 0 ∧
      Homology.bettiOne P.space < Homology.bettiOne K.space := by
  let J := (boundaryComplex 2 D).space
  have hD : IsPLBall 2 D.space := ⟨p, hp⟩
  have hJ : IsPLSphere 1 J := isPLSphere_boundaryComplex_space_of_isPLBall D hD
  have hJP : J ⊆ D.space := boundaryComplex_space_subset 2 D
  have hJp : p '' stdSimplexBoundary 2 = J := by
    rw [show J = (boundaryComplex 2 D).space from rfl,
      boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex D hp,
      simplexBoundary_stdVertices_space]
  have hside := hf.boundary D hD.isCombinatorialManifoldWithBoundary
  obtain ⟨K, A, R, hKfin, hAfin, hRfin, hK, hKc, hKsp, -, -, hR, hRc,
    hAsp, hRsp, hcover, htrace, -, hRbd⟩ := hside.exists_surface_annulus_pair hJ ha
  let _ : Finite K.faces := hKfin.to_subtype
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite R.faces := hRfin.to_subtype
  have hleft := hf.isPLHomeomorphOn_strip hD.isPolyhedron le_rfl ha.2.le (Or.inr ha.2)
  have hright := hf.isPLHomeomorphOn_strip hD.isPolyhedron ha.1.le le_rfl (Or.inl ha.1)
  have hcap (t : ℝ) (ht : t ∈ Icc (0 : ℝ) a) :
      IsPLHomeomorphOn (fun x => f (p x, t)) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
        (f '' (D.space ×ˢ {t})) := by
    have hPt := hD.isPolyhedron.isPLHomeomorphOn_prod_const t
    have hrest := hleft.restrict
      (hD.of_isPLHomeomorphOn hPt).isPolyhedron
      (fun z hz => ⟨hz.1, hz.2.symm ▸ ht⟩)
    exact (hp.trans hPt).trans hrest
  have hcapbd (t : ℝ) :
      (fun x => f (p x, t)) '' stdSimplexBoundary 2 = f '' (J ×ˢ {t}) := by
    rw [prod_singleton, ← hJp, image_image, image_image]
  have hRside : R.space ⊆ f '' (J ×ˢ Icc (0 : ℝ) 1) := by
    rw [hRsp]
    exact image_mono (fun z hz => ⟨hz.1, ha.1.le.trans hz.2.1, hz.2.2⟩)
  have hKmeet (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      K.space ∩ f '' (D.space ×ˢ {t}) =
        (fun x => f (p x, t)) '' stdSimplexBoundary 2 := by
    rw [hKsp, hcapbd]
    exact hf.image_subcylinder_inter_slice hJP hside.image_top_eq_bottom ht
  have hmeet (t : ℝ) (ht : t = 0 ∨ t = a) :
      R.space ∩ f '' (D.space ×ˢ {t}) =
        (fun x => f (p x, t)) '' stdSimplexBoundary 2 := by
    rw [hcapbd]
    have htI : t ∈ Icc (0 : ℝ) 1 := by
      rcases ht with rfl | rfl <;> constructor <;> linarith [ha.1, ha.2]
    apply Subset.antisymm
    · intro z hz
      exact (hf.image_subcylinder_inter_slice hJP hside.image_top_eq_bottom htI).subset
        ⟨hRside hz.1, hz.2⟩
    · rintro z ⟨x, hx, rfl⟩
      refine ⟨boundaryComplex_space_subset 2 R (hRbd.symm.subset ?_),
        ⟨x, ⟨hJP hx.1, hx.2⟩, rfl⟩⟩
      exact ⟨x, ⟨hx.1, hx.2.symm ▸ ht⟩, rfl⟩
  have hr₀ := hcap 0 ⟨le_rfl, ha.1.le⟩
  have hr₁ := hcap a ⟨ha.1.le, le_rfl⟩
  have hdis := hf.disjoint_image_bottom_slice ha
  have hρ := hside.isPLHomeomorphOn_strip hJ.isPolyhedron le_rfl ha.2.le (Or.inr ha.2)
  obtain ⟨P, hPfin, hP, hPc, hPo, -, hbetti, hlt, hPsp⟩ :=
    hK.exists_capped_annulus_complement K R hKc hdim hR hRc hJ ha.1 hρ
      (hAsp ▸ hcover) (hAsp ▸ htrace) hRbd hr₀ hr₁ hdis
      (hmeet 0 (Or.inl rfl)) (hmeet a (Or.inr rfl)) (hcapbd 0) (hcapbd a)
  let _ : Finite P.faces := hPfin.to_subtype
  have hprism := hp.isPLSphere_prism_boundary ha.2
  rw [hJp] at hprism
  have hprismSub : D.space ×ˢ {a, 1} ∪ J ×ˢ Icc a 1 ⊆ D.space ×ˢ Icc a 1 := by
    rintro z (⟨hz, ht⟩ | ⟨hz, ht⟩)
    · rcases ht with ht | ht
      · exact ⟨hz, ht.symm ▸ ⟨le_rfl, ha.2.le⟩⟩
      · exact ⟨hz, ht.symm ▸ ⟨ha.2.le, le_rfl⟩⟩
    · exact ⟨hJP hz, ht⟩
  have hsphere := hprism.of_isPLHomeomorphOn
    (hright.restrict hprism.isPolyhedron hprismSub)
  have hsphereP : IsPLSphere 2 P.space := by
    have himage : f '' (D.space ×ˢ {a, 1} ∪ J ×ˢ Icc a 1) = P.space := by
      rw [image_union, show D.space ×ˢ {a, (1 : ℝ)} =
        D.space ×ˢ {a} ∪ D.space ×ˢ {1} by rw [← prod_union, singleton_union],
        image_union, hf.image_top_eq_bottom, ← hRsp, hPsp]
      ext z
      simp only [mem_union]
      tauto
    exact himage ▸ hsphere
  have hχ := eulerChar_of_isPLSphere P hsphereP
  have hχβ := hP.eulerChar_eq_two_sub_bettiOne_of_isOrientable P hPc hPo
  have hzero : Homology.bettiOne P.space = 0 := by norm_num at hχ; omega
  refine ⟨K, R, P, hKfin, hRfin, hPfin, hK, hKc, hKsp, hR, hRc, hRsp,
    hAsp ▸ hcover, hAsp ▸ htrace, hRbd, hr₀, hr₁, hdis,
    hKmeet 0 ⟨le_rfl, zero_le_one⟩, hKmeet a ⟨ha.1.le, ha.2.le⟩,
    hmeet 0 (Or.inl rfl), hmeet a (Or.inr rfl), hcapbd 0, hcapbd a,
    hsphereP, hPsp, ?_, hzero, hlt⟩
  omega

end DifferentialGeometry.Topology.PiecewiseLinear
