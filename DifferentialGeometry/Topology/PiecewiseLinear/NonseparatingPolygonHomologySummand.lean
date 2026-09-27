/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homology.FirstHomologyProduct
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SphereTopHomology
import DifferentialGeometry.Topology.PiecewiseLinear.EssentialPolygonProductCoordinates
import DifferentialGeometry.Topology.Simplex.NormedBall

open Set Topology
open scoped ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLSphere.nonempty_integralSingularHomologyOne_equiv_int
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {G : Set E} (hG : IsPLSphere 1 G) :
    Nonempty (integralSingularHomology 1 G ≃ₗ[ℤ] ℤ) := by
  obtain ⟨f, hf⟩ := hG
  let β : stdSimplexBoundary 2 ≃ₜ DifferentialGeometry.Simplex.boundary (Fin 3) :=
    { toFun := fun z => ⟨⟨z.1, z.2.1⟩, z.2.2⟩
      invFun := fun z => ⟨z.1.1, z.1.2, z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.subtype_mk fun z => z.2.1).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  let e := (hf.homeomorph.symm.trans β).trans
    (DifferentialGeometry.Simplex.stdSimplexNormedBoundarySphereHomeomorph
      (EuclideanSpace.equiv (Fin 2) ℝ).symm)
  exact ⟨(integralSingularHomologyHomotopyEquiv 1 e.toHomotopyEquiv).trans
    (integralSphereTopHomologyEquiv 0 (EuclideanSpace ℝ (Fin 2)) (by simp))⟩

private theorem exists_product_chart_nonseparating {T G : Set E3}
    (hT : IsPLTorus T) (hG : IsPLSphere 1 G) (hGT : G ⊆ T)
    (hnonsep : IsPreconnected (T \ G)) :
    ∃ (J Q : Set E3) (f : E3 × E3 → E3) (q : E3), IsPLSphere 1 J ∧
      IsPLSphere 1 Q ∧ IsPLHomeomorphOn f (J ×ˢ Q) T ∧ q ∈ Q ∧
      f '' (J ×ˢ {q}) = G := by
  obtain ⟨L, hLfin, hL, hLc, hLT⟩ := hT.exists_combinatorial_triangulation
  let _ : Finite L.faces := hLfin.to_subtype
  have hLo := hL.isOrientable_euclidean_three L hLc
  have hβ := hT.bettiOne_le_two
  rw [← hLT] at hβ
  have hχ := hL.eulerChar_eq_two_sub_bettiOne_of_isOrientable L hLc hLo
  have hGL : G ⊆ L.space := hLT ▸ hGT
  have hnonsep' : IsPreconnected (L.space \ G) := by rwa [hLT]
  obtain ⟨R, hRfin, hR, -, hRc, hRχ, W, ρ, -, -, -, -, hρ, hzero, -, -, hRbd,
      hWR, hcover, hGm, hGp, hdisjpm⟩ :=
    hL.exists_connected_annulus_complement L hLo hG hGL hnonsep' Filter.univ_mem
  let _ : Finite R.faces := hRfin.to_subtype
  have hRbd' := hRbd.trans (show ρ '' (G ×ˢ {(-1 : ℝ), 1}) =
      ρ '' (G ×ˢ {(-1 : ℝ)}) ∪ ρ '' (G ×ˢ {(1 : ℝ)}) by
    rw [← singleton_union, prod_union, image_union])
  have hRχ0 : eulerChar R = 0 := by
    have hle := hR.eulerChar_nonpos_of_boundary_eq_union R hRc hGm hGp hdisjpm hRbd'
    omega
  obtain ⟨h, hh, hh0, hh1⟩ :=
    hR.exists_isPLHomeomorphOn_annulus_of_eulerChar_eq_zero R hRc hRχ0 hGm hGp hdisjpm hRbd'
  obtain ⟨g, hg, -, hg34⟩ :=
    exists_isCylindricalDiagram_of_annulus_bicollar hh hh0 hh1 hG.isPolyhedron hρ hzero hWR
  have hRW : R.space ∪ W = T := by rw [union_comm, hcover, hLT]
  obtain ⟨g', hg', hends, hgg'⟩ := hg.exists_eq_ends_of_isOrientable L
    hL.isCombinatorialManifoldWithBoundary hLo (hRW.trans hLT.symm).subset
    (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)
  obtain ⟨J, Q, f, γ, hJ, hQ, hf, hγQ, -, hfib⟩ := hg'.exists_prod_chart_of_eq_ends hends
  refine ⟨J, Q, f, γ (3 / 4), hJ, hQ, hRW ▸ hf, hγQ _ (by norm_num), ?_⟩
  rw [hfib _ (by norm_num), image_congr fun z hz =>
    hgg' z ⟨hz.1, by rw [mem_singleton_iff.mp hz.2]; norm_num⟩, hg34]

private theorem exists_homeomorph_pinned_product {T G J Q : Set E3}
    {f : E3 × E3 → E3} (hf : IsPLHomeomorphOn f (J ×ˢ Q) T)
    {q : E3} (hq : q ∈ Q) (hfib : f '' (J ×ˢ {q}) = G) (hGT : G ⊆ T) :
    ∃ e : T ≃ₜ G × Q, ∀ x : G, e (inclusion hGT x) = (x, ⟨q, hq⟩) := by
  let e₀ : J × Q ≃ₜ T := (Homeomorph.Set.prod J Q).symm.trans hf.homeomorph
  let q₀ : Q := ⟨q, hq⟩
  let i : C(G, T) := ⟨inclusion hGT, continuous_inclusion hGT⟩
  have hmem (x : J) : (e₀ (x, q₀) : E3) ∈ G := by
    rw [← hfib]
    exact ⟨(x, q), ⟨x.2, rfl⟩, rfl⟩
  have hsnd (x : G) : (e₀.symm (i x)).2 = q₀ := by
    obtain ⟨z, hz, hez⟩ := hfib.symm.subset x.2
    have hzq : z.2 = q := hz.2
    have he : e₀ (⟨z.1, hz.1⟩, q₀) = i x := by
      apply Subtype.ext
      change f (z.1, q) = x
      rw [← hzq]
      exact hez
    rw [← he, e₀.symm_apply_apply]
  let k : J ≃ₜ G :=
    { toFun := fun x => ⟨e₀ (x, q₀), hmem x⟩
      invFun := fun x => (e₀.symm (i x)).1
      left_inv := fun x => by
        change (e₀.symm (e₀ (x, q₀))).1 = x
        rw [e₀.symm_apply_apply]
      right_inv := fun x => by
        apply Subtype.ext
        change (e₀ ((e₀.symm (i x)).1, q₀) : E3) = x
        rw [← hsnd x, Prod.mk.eta, e₀.apply_symm_apply]
        rfl
      continuous_toFun := ((continuous_subtype_val.comp e₀.continuous).comp
        (continuous_id.prodMk continuous_const)).subtype_mk _
      continuous_invFun := (e₀.symm.continuous.comp i.continuous).fst }
  let e : T ≃ₜ G × Q := e₀.symm.trans (k.prodCongr (Homeomorph.refl Q))
  refine ⟨e, fun x => ?_⟩
  apply Prod.ext
  · change k ((e₀.symm (i x)).1) = x
    exact k.apply_symm_apply x
  · exact hsnd x

theorem IsPLTorus.exists_firstHomology_equiv_prod_of_nonseparating {T G : Set E3}
    (hT : IsPLTorus T) (hG : IsPLSphere 1 G) (hGT : G ⊆ T)
    (hnonsep : IsPreconnected (T \ G)) :
    ∃ e : integralSingularHomology 1 T ≃ₗ[ℤ] integralSingularHomology 1 G × ℤ,
      ∀ a : integralSingularHomology 1 G,
        e (integralSingularHomologyMap 1
          (⟨inclusion hGT, continuous_inclusion hGT⟩ : C(G, T)) a) = (a, 0) := by
  obtain ⟨J, Q, f, q, -, hQ, hf, hq, hfib⟩ :=
    exists_product_chart_nonseparating hT hG hGT hnonsep
  obtain ⟨e, he⟩ := exists_homeomorph_pinned_product hf hq hfib hGT
  obtain ⟨eQ⟩ := hQ.nonempty_integralSingularHomologyOne_equiv_int
  let _ : PathConnectedSpace G := isPathConnected_iff_pathConnectedSpace.mp hG.isPathConnected_one
  let _ : PathConnectedSpace Q := isPathConnected_iff_pathConnectedSpace.mp hQ.isPathConnected_one
  let i : C(G, T) := ⟨inclusion hGT, continuous_inclusion hGT⟩
  let j : C(G, G × Q) := ⟨fun x => (x, ⟨q, hq⟩), continuous_id.prodMk continuous_const⟩
  have hei : (e : C(T, G × Q)).comp i = j := ContinuousMap.ext he
  let eP := ((AddEquiv.refl (integralSingularHomology 1 G)).prodCongr eQ.toAddEquiv)
  let eH := (integralSingularHomologyHomotopyEquiv 1 e.toHomotopyEquiv).trans
    integralSingularHomologyOneProdEquiv
  refine ⟨(eH.toAddEquiv.trans eP).toIntLinearEquiv, ?_⟩
  intro a
  change eP
    (integralSingularHomologyOneProdEquiv
      (integralSingularHomologyMap 1 (e : C(T, G × Q))
        (integralSingularHomologyMap 1 i a))) = (a, 0)
  rw [← LinearMap.comp_apply, ← integralSingularHomologyMap_comp, hei,
    integralSingularHomologyOneProdEquiv_apply]
  have hfst : ContinuousMap.fst.comp j = ContinuousMap.id G := rfl
  have hsnd : ContinuousMap.snd.comp j = ContinuousMap.const G (⟨q, hq⟩ : Q) := rfl
  rw [← LinearMap.comp_apply, ← integralSingularHomologyMap_comp, hfst,
    integralSingularHomologyMap_id, LinearMap.id_apply,
    ← LinearMap.comp_apply, ← integralSingularHomologyMap_comp, hsnd,
    integralSingularHomologyMap_const 1 one_ne_zero, LinearMap.zero_apply]
  exact Prod.ext rfl (map_zero eQ)

theorem IsPLTorus.exists_homotopic_inclusion_in_complement {T G : Set E3}
    (hT : IsPLTorus T) (hG : IsPLSphere 1 G) (hGT : G ⊆ T)
    (hnonsep : IsPreconnected (T \ G)) :
    ∃ j : C(G, ↥(T \ G)),
      ContinuousMap.Homotopic
        ((⟨inclusion sdiff_subset, continuous_inclusion sdiff_subset⟩ : C(↥(T \ G), T)).comp j)
        (⟨inclusion hGT, continuous_inclusion hGT⟩ : C(G, T)) := by
  obtain ⟨J, Q, f, q, -, hQ, hf, hq, hfib⟩ :=
    exists_product_chart_nonseparating hT hG hGT hnonsep
  obtain ⟨e, he⟩ := exists_homeomorph_pinned_product hf hq hfib hGT
  obtain ⟨a, ha, b, hb, hab⟩ := exists_ne_mem_of_isPLSphere_one hQ
  have hne : ∃ q' : Q, q' ≠ (⟨q, hq⟩ : Q) := by
    by_cases haq : a = q
    · exact ⟨⟨b, hb⟩, fun h => hab (haq.trans (congrArg Subtype.val h).symm)⟩
    · exact ⟨⟨a, ha⟩, fun h => haq (congrArg Subtype.val h)⟩
  obtain ⟨q', hq'⟩ := hne
  let _ : PathConnectedSpace Q := isPathConnected_iff_pathConnectedSpace.mp hQ.isPathConnected_one
  obtain ⟨p⟩ := PathConnectedSpace.joined q' (⟨q, hq⟩ : Q)
  have hoff (x : G) : (e.symm (x, q') : E3) ∉ G := by
    intro hx
    have hei := he (⟨e.symm (x, q'), hx⟩ : G)
    have hval : inclusion hGT (⟨e.symm (x, q'), hx⟩ : G) = e.symm (x, q') := rfl
    rw [hval, e.apply_symm_apply] at hei
    exact hq' (congrArg Prod.snd hei)
  let j : C(G, ↥(T \ G)) :=
    ⟨fun x => ⟨e.symm (x, q'), (e.symm (x, q')).2, hoff x⟩,
      ((continuous_subtype_val.comp e.symm.continuous).comp
        (continuous_id.prodMk continuous_const)).subtype_mk _⟩
  refine ⟨j, ⟨{
    toFun := fun z => e.symm (z.2, p z.1)
    continuous_toFun := e.symm.continuous.comp
      (continuous_snd.prodMk (p.continuous.comp continuous_fst))
    map_zero_left := fun x => by change e.symm (x, p 0) = _; rw [p.source]; rfl
    map_one_left := fun x => by
      change e.symm (x, p 1) = inclusion hGT x
      rw [p.target, ← he x, e.symm_apply_apply] }⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
