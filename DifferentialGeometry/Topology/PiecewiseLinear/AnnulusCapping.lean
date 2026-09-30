/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceBoundaryCapping
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusEuler
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusComponents
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCapping
import DifferentialGeometry.Topology.PiecewiseLinear.EuclideanSurfaceOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceHomology
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSphereRecognition

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem IsCombinatorialManifold.exists_capped_annulus_complement
    (K R : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite R.faces]
    (hK : IsCombinatorialManifold 2 K) (hKc : IsConnected K.space)
    (hdim : Module.finrank ℝ E = 3)
    (hR : IsCombinatorialManifoldWithBoundary 2 R) (hRc : IsConnected R.space)
    {J : Set F} (hJ : IsPLSphere 1 J) {a b : ℝ} (hab : a < b)
    {W : Set E} {ρ : F × ℝ → E} (hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc a b) W)
    (hcover : W ∪ R.space = K.space) (htrace : W ∩ R.space = ρ '' (J ×ˢ {a, b}))
    (hboundary : (boundaryComplex 2 R).space = ρ '' (J ×ˢ {a, b}))
    {D₀ D₁ : Set E} {r₀ r₁ : (Fin 3 → ℝ) → E}
    (hr₀ : IsPLHomeomorphOn r₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀)
    (hr₁ : IsPLHomeomorphOn r₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁) (hdis : Disjoint D₀ D₁)
    (hmeet₀ : R.space ∩ D₀ = r₀ '' stdSimplexBoundary 2)
    (hmeet₁ : R.space ∩ D₁ = r₁ '' stdSimplexBoundary 2)
    (hbd₀ : r₀ '' stdSimplexBoundary 2 = ρ '' (J ×ˢ {a}))
    (hbd₁ : r₁ '' stdSimplexBoundary 2 = ρ '' (J ×ˢ {b})) :
    ∃ (P : Geometry.SimplicialComplex ℝ E) (hPfin : P.faces.Finite),
      letI := hPfin.to_subtype
      IsCombinatorialManifold 2 P ∧ IsConnected P.space ∧ IsOrientable 2 P ∧
      eulerChar P = eulerChar K + 2 ∧
      Homology.bettiOne P.space + 2 = Homology.bettiOne K.space ∧
      Homology.bettiOne P.space < Homology.bettiOne K.space ∧
      P.space = R.space ∪ D₀ ∪ D₁ := by
  have hW : IsPolyhedron W := hρ.image_eq ▸
    (hJ.isPolyhedron.prod (isPLBall_Icc hab).isPolyhedron).image_of_isPiecewiseAffineOn
      hρ.isPiecewiseAffineOn hρ.bijOn.injOn
  obtain ⟨A, hAfin, hAspace⟩ := hW.exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  have hRχ : eulerChar R = eulerChar K :=
    eulerChar_eq_of_annulus_complement K A R hJ hab (hAspace.symm ▸ hρ)
      (by rwa [hAspace]) (by rwa [hAspace])
  have hRbd : (boundaryComplex 2 R).space =
      r₀ '' stdSimplexBoundary 2 ∪ r₁ '' stdSimplexBoundary 2 := by
    rw [hboundary, hbd₀, hbd₁, ← image_union, ← prod_union, singleton_union]
  obtain ⟨P, hPfin, hP, hPc, hPχ, hPspace⟩ :=
    hR.exists_closed_of_disk_pair R hRc hr₀ hr₁ hdis hmeet₀ hmeet₁ hRbd
  let _ : Finite P.faces := hPfin.to_subtype
  have hPo := hP.isOrientable_of_finrank_eq_three P hdim hPc
  have hKo := hK.isOrientable_of_finrank_eq_three K hdim hKc
  have hχK := hK.eulerChar_eq_two_sub_bettiOne_of_isOrientable K hKc hKo
  have hχP := hP.eulerChar_eq_two_sub_bettiOne_of_isOrientable P hPc hPo
  exact ⟨P, hPfin, hP, hPc, hPo, by omega, by omega, by omega, hPspace⟩

open Classical in
theorem IsCombinatorialManifold.exists_capped_pair_of_separating_essential_annulus
    (K R : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite R.faces]
    (hK : IsCombinatorialManifold 2 K) (hKc : IsConnected K.space)
    (hdim : Module.finrank ℝ E = 3) (hR : IsCombinatorialManifoldWithBoundary 2 R)
    {J W : Set E} (hJ : IsPLSphere 1 J) (hJK : J ⊆ K.space) {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 1) W)
    (hzero : ∀ x ∈ J, ρ (x, 0) = x) (hWnhds : W ∈ 𝓝ˢ[K.space] J)
    (hcover : W ∪ R.space = K.space)
    (htrace : W ∩ R.space = ρ '' (J ×ˢ {(-1 : ℝ), 1}))
    (hboundary : (boundaryComplex 2 R).space = ρ '' (J ×ˢ {(-1 : ℝ), 1}))
    (hsep : ¬ IsPreconnected (K.space \ J))
    (hnon : ¬ (⟨Set.inclusion hJK, continuous_inclusion hJK⟩ : C(J, K.space)).Nullhomotopic)
    {D₀ D₁ : Set E} {r₀ r₁ : (Fin 3 → ℝ) → E}
    (hr₀ : IsPLHomeomorphOn r₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀)
    (hr₁ : IsPLHomeomorphOn r₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁) (hdis : Disjoint D₀ D₁)
    (hmeet₀ : R.space ∩ D₀ = r₀ '' stdSimplexBoundary 2)
    (hmeet₁ : R.space ∩ D₁ = r₁ '' stdSimplexBoundary 2)
    (hbd₀ : r₀ '' stdSimplexBoundary 2 = ρ '' (J ×ˢ {(-1 : ℝ)}))
    (hbd₁ : r₁ '' stdSimplexBoundary 2 = ρ '' (J ×ˢ {(1 : ℝ)})) :
    ∃ (P Q : Geometry.SimplicialComplex ℝ E) (hPfin : P.faces.Finite) (hQfin : Q.faces.Finite),
      letI := hPfin.to_subtype
      letI := hQfin.to_subtype
      IsCombinatorialManifold 2 P ∧ IsCombinatorialManifold 2 Q ∧
      IsConnected P.space ∧ IsConnected Q.space ∧ IsOrientable 2 P ∧ IsOrientable 2 Q ∧
      ¬ IsPLSphere 2 P.space ∧ ¬ IsPLSphere 2 Q.space ∧ Disjoint P.space Q.space ∧
      eulerChar P + eulerChar Q = eulerChar K + 2 ∧
      Homology.bettiOne P.space + Homology.bettiOne Q.space = Homology.bettiOne K.space ∧
      Homology.bettiOne P.space < Homology.bettiOne K.space ∧
      Homology.bettiOne Q.space < Homology.bettiOne K.space ∧
      P.space ∪ Q.space = R.space ∪ D₀ ∪ D₁ := by
  obtain ⟨A, B, hAfin, hBfin, hA, hB, hAc, hBc, hAB, hABcover, hAbd, hBbd⟩ :=
    hR.exists_component_pair_of_separating_annulus K R hKc.isPreconnected hJ hρ hzero
      hWnhds hcover htrace hboundary hsep
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite B.faces := hBfin.to_subtype
  have hAboundary : (boundaryComplex 2 A).space = r₀ '' stdSimplexBoundary 2 :=
    hAbd.trans hbd₀.symm
  have hBboundary : (boundaryComplex 2 B).space = r₁ '' stdSimplexBoundary 2 :=
    hBbd.trans hbd₁.symm
  obtain ⟨P, Q, hPfin, hQfin, hP, hQ, hPc, hQc, hPQ, hχ, hPspace, hQspace⟩ :=
    hA.exists_closed_pair_of_disks A B hB hAc hBc hAB hr₀ hr₁ hdis
      (by rwa [hABcover]) (by rwa [hABcover]) hAboundary hBboundary
  let _ : Finite P.faces := hPfin.to_subtype
  let _ : Finite Q.faces := hQfin.to_subtype
  have hAR : A.space ⊆ R.space := subset_union_left.trans hABcover.subset
  have hBR : B.space ⊆ R.space := subset_union_right.trans hABcover.subset
  have hRK : R.space ⊆ K.space := subset_union_right.trans hcover.subset
  have hAD : A.space ∩ D₀ = r₀ '' stdSimplexBoundary 2 :=
    Subset.antisymm (fun _ hx => hmeet₀.subset ⟨hAR hx.1, hx.2⟩)
      (fun _ hx => ⟨boundaryComplex_space_subset 2 A (hAboundary.symm.subset hx),
        (hmeet₀.symm.subset hx).2⟩)
  have hBD : B.space ∩ D₁ = r₁ '' stdSimplexBoundary 2 :=
    Subset.antisymm (fun _ hx => hmeet₁.subset ⟨hBR hx.1, hx.2⟩)
      (fun _ hx => ⟨boundaryComplex_space_subset 2 B (hBboundary.symm.subset hx),
        (hmeet₁.symm.subset hx).2⟩)
  have hnonsphere (M : Geometry.SimplicialComplex ℝ E) [Finite M.faces]
      {D : Set E} {r : (Fin 3 → ℝ) → E}
      (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
      (hMD : M.space ∩ D = r '' stdSimplexBoundary 2) (hMK : M.space ⊆ K.space)
      {t : ℝ} (ht : t = -1 ∨ t = 1)
      (hbd : r '' stdSimplexBoundary 2 = ρ '' (J ×ˢ {t})) :
      ¬ IsPLSphere 2 (M.space ∪ D) := by
    intro hSphere
    let σ : E × ℝ → E := fun z => ρ (z.1, t * z.2)
    have hdom : MapsTo (fun z : E × ℝ => (z.1, t * z.2))
        (J ×ˢ Icc (0 : ℝ) 1) (J ×ˢ Icc (-1 : ℝ) 1) := by
      intro z hz
      refine ⟨hz.1, ?_⟩
      rcases ht with rfl | rfl <;> constructor <;> nlinarith [hz.2.1, hz.2.2]
    have hσ : ContinuousOn σ (J ×ˢ Icc (0 : ℝ) 1) :=
      hρ.isPiecewiseAffineOn.continuousOn.comp
        (continuous_fst.prodMk (continuous_const.mul continuous_snd)).continuousOn hdom
    have hσK : MapsTo σ (J ×ˢ Icc (0 : ℝ) 1) K.space :=
      fun _ hz => hcover.subset (Or.inl (hρ.bijOn.mapsTo (hdom hz)))
    have hσzero : ∀ x ∈ J, σ (x, 0) = x := by
      intro x hx
      simpa only [σ, mul_zero] using hzero x hx
    have hσone : ∀ x ∈ J, σ (x, 1) ∈ M.space := by
      intro x hx
      exact (hMD.symm.subset (hbd.symm.subset
        ⟨(x, t), ⟨hx, rfl⟩, by simp only [σ, mul_one]⟩)).1
    exact hnon (hSphere.nullhomotopic_inclusion_of_cylinder_into_complement hr hMD
      (isPolyhedron_space M).isPLHomeomorphOn_id hMK hJK hσ hσK hσzero hσone)
  have hPsphere : ¬ IsPLSphere 2 P.space := by
    rw [hPspace]
    exact hnonsphere A hr₀ hAD (hAR.trans hRK) (Or.inl rfl) hbd₀
  have hQsphere : ¬ IsPLSphere 2 Q.space := by
    rw [hQspace]
    exact hnonsphere B hr₁ hBD (hBR.trans hRK) (Or.inr rfl) hbd₁
  have hW : IsPolyhedron W := hρ.image_eq ▸
    (hJ.isPolyhedron.prod isHPolytope_Icc.isPolyhedron).image_of_isPiecewiseAffineOn
      hρ.isPiecewiseAffineOn hρ.bijOn.injOn
  obtain ⟨L, hLfin, hLspace⟩ := hW.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  have hRχ := eulerChar_eq_of_annulus_complement K L R hJ
    (by norm_num : (-1 : ℝ) < 1) (hLspace.symm ▸ hρ)
    (by rwa [hLspace]) (by rwa [hLspace])
  have hABχ := eulerChar_eq_add_of_space_disjoint_union R A B hABcover.symm hAB
  have hsumχ : eulerChar P + eulerChar Q = eulerChar K + 2 := by omega
  have hKo := hK.isOrientable_of_finrank_eq_three K hdim hKc
  have hPo := hP.isOrientable_of_finrank_eq_three P hdim hPc
  have hQo := hQ.isOrientable_of_finrank_eq_three Q hdim hQc
  have hχK := hK.eulerChar_eq_two_sub_bettiOne_of_isOrientable K hKc hKo
  have hχP := hP.eulerChar_eq_two_sub_bettiOne_of_isOrientable P hPc hPo
  have hχQ := hQ.eulerChar_eq_two_sub_bettiOne_of_isOrientable Q hQc hQo
  have hsum : Homology.bettiOne P.space + Homology.bettiOne Q.space =
      Homology.bettiOne K.space := by omega
  have hPpos := hP.bettiOne_pos_of_isOrientable_of_eulerChar_ne_two P hPc hPo
    (fun h => hPsphere (hP.isPLSphere_two_of_faceEulerChar_eq_two P hPc h))
  have hQpos := hQ.bettiOne_pos_of_isOrientable_of_eulerChar_ne_two Q hQc hQo
    (fun h => hQsphere (hQ.isPLSphere_two_of_faceEulerChar_eq_two Q hQc h))
  refine ⟨P, Q, hPfin, hQfin, hP, hQ, hPc, hQc, hPo, hQo, hPsphere, hQsphere,
    hPQ, hsumχ, hsum, by omega, by omega, ?_⟩
  rw [hPspace, hQspace, ← hABcover]
  ext x
  simp only [mem_union]
  tauto

end DifferentialGeometry.Topology.PiecewiseLinear
