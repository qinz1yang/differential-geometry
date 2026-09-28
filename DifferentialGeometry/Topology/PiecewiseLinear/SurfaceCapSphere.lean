/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.HandlePieceEulerChar

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isPLSphere_cap
    (M : Geometry.SimplicialComplex ℝ E) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 2 M) (hconn : IsConnected M.space)
    {ι : Type} [Fintype ι] (J : ι → Set E) (hJ : ∀ i, IsPLSphere 1 (J i))
    (hdisj : Pairwise fun i j => Disjoint (J i) (J j))
    (hbd : (boundaryComplex 2 M).space = ⋃ i, J i)
    (hχ : SimplicialComplex.faceEulerChar M.toPreAbstractSimplicialComplex = 2 - Nat.card ι) :
    ∃ (S : Set (E × (ι → ℝ))) (D : ι → Set (E × (ι → ℝ)))
      (q : ι → (Fin 3 → ℝ) → E × (ι → ℝ)),
      IsPLSphere 2 S ∧ S = LinearMap.inl ℝ E (ι → ℝ) '' M.space ∪ ⋃ i, D i ∧
      (∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D i)) ∧
      (∀ i, q i '' stdSimplexBoundary 2 = LinearMap.inl ℝ E (ι → ℝ) '' J i) ∧
      (∀ i, D i ∩ LinearMap.inl ℝ E (ι → ℝ) '' M.space = LinearMap.inl ℝ E (ι → ℝ) '' J i) ∧
      Pairwise fun i j => Disjoint (D i) (D j) := by
  classical
  let _ : DecidableEq (E × (ι → ℝ)) := fun a b => Classical.propDecidable (a = b)
  let ι₀ : E →ₗ[ℝ] E × (ι → ℝ) := LinearMap.inl ℝ E (ι → ℝ)
  have hι₀ : Function.Injective ι₀ := LinearMap.inl_injective
  have hMpoly := isPolyhedron_space M
  have hι₀M := hMpoly.isPLHomeomorphOn_linearMap_image ι₀ hι₀
  obtain ⟨M', hM'fin, hM'space⟩ := (hMpoly.image_of_isPiecewiseAffineOn
    hι₀M.isPiecewiseAffineOn hι₀.injOn).exists_simplicialComplex
  let _ : Finite M'.faces := hM'fin.to_subtype
  have hι : IsPLHomeomorphOn ι₀ M.space M'.space := by
    rw [hM'space]
    exact hι₀M
  have hM' : IsCombinatorialManifoldWithBoundary 2 M' := hM.of_isPLHomeomorphOn hι
  have hJM : ∀ i, J i ⊆ M.space := fun i =>
    (subset_iUnion J i).trans (hbd.symm.subset.trans (boundaryComplex_space_subset 2 M))
  have hM'bd : (boundaryComplex 2 M').space = ⋃ i, ι₀ '' J i := by
    change (boundaryComplex (1 + 1) M').space = _
    rw [boundaryComplex_space_of_isPLHomeomorphOn M M' hM hι, hbd, image_iUnion]
  have hdisk : ∀ i : ι, ∃ (D : Set (E × (ι → ℝ))) (r : (Fin 3 → ℝ) → E × (ι → ℝ)),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ r '' stdSimplexBoundary 2 = ι₀ '' J i ∧
      D ∩ M'.space = ι₀ '' J i ∧
      ∀ y ∈ D, ∃ s : ℝ, y.2 = s • Pi.single i (1 : ℝ) ∧ (s = 0 → y ∈ ι₀ '' J i) := by
    intro i
    obtain ⟨D, r, hr, hrbd, hD⟩ := exists_cone_disk_of_isPLSphere_one (hJ i)
    let Λ : E × ℝ →ₗ[ℝ] E × (ι → ℝ) := LinearMap.prodMap LinearMap.id
      ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (Pi.single i (1 : ℝ)))
    have hΛapply : ∀ z : E × ℝ, Λ z = (z.1, z.2 • Pi.single i (1 : ℝ)) := fun z => rfl
    have hΛ : Function.Injective Λ := by
      intro z z' hzz
      rw [hΛapply, hΛapply, Prod.mk.injEq] at hzz
      have h2 := congrFun hzz.2 i
      simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h2
      exact Prod.ext hzz.1 h2
    have hball : IsPLBall 2 D := ⟨r, hr⟩
    have hr' := hr.trans (hball.isPolyhedron.isPLHomeomorphOn_linearMap_image Λ hΛ)
    have hΛJ : Λ '' (J i ×ˢ {0}) = ι₀ '' J i := by
      ext y
      simp only [mem_image, mem_prod, mem_singleton_iff, Prod.exists]
      constructor
      · rintro ⟨x, s, ⟨hx, rfl⟩, rfl⟩
        exact ⟨x, hx, by rw [hΛapply]; simp [ι₀]⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, 0, ⟨hx, rfl⟩, by rw [hΛapply]; simp [ι₀]⟩
    have hpt : ∀ y ∈ Λ '' D, ∃ s : ℝ, y.2 = s • Pi.single i (1 : ℝ) ∧
        (s = 0 → y ∈ ι₀ '' J i) := by
      rintro _ ⟨z, hz, rfl⟩
      refine ⟨z.2, by rw [hΛapply], fun hs => ?_⟩
      have hzJ := (hD z hz).2 hs
      rw [← hΛJ]
      exact mem_image_of_mem Λ hzJ
    refine ⟨Λ '' D, Λ ∘ r, hr', by rw [image_comp, hrbd, hΛJ], ?_, hpt⟩
    apply Subset.antisymm
    · rintro y ⟨hyD, hyM⟩
      obtain ⟨s, hs, hsJ⟩ := hpt y hyD
      refine hsJ ?_
      rw [hM'space] at hyM
      obtain ⟨x, -, rfl⟩ := hyM
      have h0 := congrFun hs i
      simpa [ι₀] using h0.symm
    · intro y hy
      refine ⟨?_, ?_⟩
      · rw [← hΛJ, ← hrbd] at hy
        exact image_mono ((image_mono fun x hx => hx.1).trans hr.image_eq.subset) hy
      · rw [hM'space]
        exact image_mono (hJM i) hy
  choose D r hr hrbd hDM hDpt using hdisk
  have hDdisj : Pairwise fun i j => Disjoint (D i) (D j) := by
    intro i j hij
    rw [disjoint_left]
    intro y hyi hyj
    obtain ⟨s, hs, hsJ⟩ := hDpt i y hyi
    obtain ⟨s', hs', hs'J⟩ := hDpt j y hyj
    have hsi : s = 0 := by
      have h := congrFun (hs.symm.trans hs') i
      simpa [Pi.single_apply, hij] using h
    have hs'j : s' = 0 := by
      have h := congrFun (hs.symm.trans hs') j
      simpa [Pi.single_apply, Ne.symm hij] using h.symm
    obtain ⟨x, hx, rfl⟩ := hsJ hsi
    obtain ⟨x', hx', hxx'⟩ := hs'J hs'j
    have hxeq : x' = x := hι₀ hxx'
    rw [hxeq] at hx'
    exact disjoint_left.mp (hdisj hij) hx hx'
  have hunion : ∀ W : Finset ι, ∃ L : Geometry.SimplicialComplex ℝ (E × (ι → ℝ)),
      L.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 2 L ∧ L.space = ⋃ i ∈ W, D i ∧
      (boundaryComplex 2 L).space = ⋃ i ∈ W, ι₀ '' J i := by
    intro W
    induction W using Finset.induction_on with
    | empty =>
      refine ⟨⊥, by simp [Geometry.SimplicialComplex.faces_bot], fun v hv => ?_, ?_, ?_⟩
      · simp [Geometry.SimplicialComplex.faces_bot] at hv
      · rw [Geometry.SimplicialComplex.space_bot]
        ext y
        simp
      · have h : (boundaryComplex 2 (⊥ : Geometry.SimplicialComplex ℝ (E × (ι → ℝ)))).space =
            ∅ := by
          ext y
          simp only [mem_empty_iff_false, iff_false]
          intro hy
          obtain ⟨t, ht, -⟩ := (boundaryComplex 2 _).mem_space_iff.mp hy
          simpa [Geometry.SimplicialComplex.faces_bot] using
            boundaryComplex_faces_subset 2 _ ht
        rw [h]
        ext y
        simp
    | insert i W hi ih =>
      obtain ⟨LW, hLWfin, hLW, hLWspace, hLWbd⟩ := ih
      let _ : Finite LW.faces := hLWfin.to_subtype
      have hball : IsPLBall 2 (D i) := ⟨r i, hr i⟩
      obtain ⟨Li, hLifin, hLispace⟩ := hball.isPolyhedron.exists_simplicialComplex
      let _ : Finite Li.faces := hLifin.to_subtype
      have hLi : IsCombinatorialManifoldWithBoundary 2 Li :=
        (hLispace.symm ▸ hball).isCombinatorialManifoldWithBoundary
      have hLibd : (boundaryComplex 2 Li).space = ι₀ '' J i := by
        change (boundaryComplex (1 + 1) Li).space = _
        rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex Li (hLispace.symm ▸ hr i),
          simplexBoundary_stdVertices_space, hrbd i]
      have hdis : Disjoint LW.space Li.space := by
        rw [hLWspace, hLispace, Set.disjoint_iUnion₂_left]
        intro j hj
        exact hDdisj fun h => hi (h ▸ hj)
      obtain ⟨R, hRfin, hR, hRspace, hRbd⟩ := hLW.exists_space_disjoint_union LW Li hLi hdis
      refine ⟨R, hRfin, hR, ?_, ?_⟩
      · rw [hRspace, hLWspace, hLispace, Finset.set_biUnion_insert, union_comm]
      · rw [hRbd, hLWbd, hLibd, Finset.set_biUnion_insert, union_comm]
  obtain ⟨L, hLfin, hL, hLspace, hLbd⟩ := hunion Finset.univ
  let _ : Finite L.faces := hLfin.to_subtype
  have hLspace' : L.space = ⋃ i, D i := by
    rw [hLspace]
    ext y
    simp
  have hinter : M'.space ∩ L.space = ⋃ i, ι₀ '' J i := by
    rw [hLspace', inter_iUnion]
    exact iUnion_congr fun i => by rw [inter_comm, hDM i]
  have hLbd' : (boundaryComplex 2 L).space = ⋃ i, ι₀ '' J i := by
    rw [hLbd]
    ext y
    simp
  obtain ⟨R, hRfin, hR, hRspace⟩ := exists_isCombinatorialManifold_space_union M' L hM' hL
    (hinter.trans hM'bd.symm) (hinter.trans hLbd'.symm)
  let _ : Finite R.faces := hRfin.to_subtype
  have hM'c : IsConnected M'.space := by
    rw [hM'space]
    exact hconn.image ι₀ ι₀.continuous_of_finiteDimensional.continuousOn
  have hRc : IsConnected R.space := by
    have h := IsConnected.union_biUnion hM'c Finset.univ
      (fun i _ => IsPLBall.isConnected ⟨r i, hr i⟩) fun i _ => by
        rw [inter_comm, hDM i]
        exact (hJ i).nonempty.image ι₀
    rw [hRspace, hLspace']
    simpa using h
  let Bd := boundaryComplex 2 M'
  let _ : Finite Bd.faces := (boundaryComplex_faces_finite 2 M').to_subtype
  have hsplit := eulerChar_eq_add_sub_of_space_union R M' L Bd hRspace
    (by rw [hinter]; exact hM'bd)
  have hχM := eulerChar_eq_of_isPLHomeomorphOn M M' hι
  have hχL : eulerChar L = Nat.card ι := by
    rw [eulerChar_eq_singular L ℚ, hLspace]
    have h := IsPolyhedron.eulerChar_biUnion (Finset.univ : Finset ι)
      (fun i _ => IsPLBall.isPolyhedron ⟨r i, hr i⟩) (fun i _ j _ hij => hDdisj hij)
    rw [h.2, Finset.sum_congr rfl fun i _ => IsPLBall.homologyEulerChar_eq_one ⟨r i, hr i⟩]
    simp [Nat.card_eq_fintype_card]
  have hχBd : eulerChar Bd = 0 := by
    rw [eulerChar_eq_singular Bd ℚ, hM'bd]
    have hsph : ∀ i : ι, IsPLSphere 1 (ι₀ '' J i) := fun i =>
      (hJ i).of_isPLHomeomorphOn
        ((hJ i).isPolyhedron.isPLHomeomorphOn_linearMap_image ι₀ hι₀)
    have hU : (⋃ i : ι, ι₀ '' J i) = ⋃ i ∈ (Finset.univ : Finset ι), ι₀ '' J i := by
      ext y
      simp
    rw [hU]
    have h := IsPolyhedron.eulerChar_biUnion (Finset.univ : Finset ι)
      (fun i _ => (hsph i).isPolyhedron) fun i _ j _ hij =>
        (hdisj hij).image hι₀.injOn (subset_univ _) (subset_univ _)
    rw [h.2]
    exact Finset.sum_eq_zero fun i _ => (hsph i).homologyEulerChar_eq_zero
  have hχR : SimplicialComplex.faceEulerChar R.toPreAbstractSimplicialComplex = 2 := by
    change eulerChar R = 2
    rw [hsplit, hχBd, hχL, ← hχM, sub_zero]
    change SimplicialComplex.faceEulerChar M.toPreAbstractSimplicialComplex + _ = 2
    rw [hχ]
    ring
  refine ⟨R.space, D, r, hR.isPLSphere_two_of_faceEulerChar_eq_two R hRc hχR, ?_, hr, hrbd,
    fun i => by rw [← hM'space]; exact hDM i, hDdisj⟩
  rw [hRspace, hLspace', hM'space]

end DifferentialGeometry.Topology.PiecewiseLinear
