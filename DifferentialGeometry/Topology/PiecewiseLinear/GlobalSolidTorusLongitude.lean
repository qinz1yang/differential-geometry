/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homology.FirstHomologyAdditiveMap
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SphereHomologyVanishing
import DifferentialGeometry.Topology.PiecewiseLinear.NonseparatingPolygonHomologySummand
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalTorusSlope
import DifferentialGeometry.Topology.PiecewiseLinear.SolidTorusComplementHomology

open Set Topology
open scoped ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "C2" => Metric.sphere (0 : E2) 1

private noncomputable def boundarySphereHomeomorph (n : ℕ) :
    stdSimplexBoundary (n + 1) ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
  let β : stdSimplexBoundary (n + 1) ≃ₜ DifferentialGeometry.Simplex.boundary (Fin (n + 2)) :=
    { toFun := fun z => ⟨⟨z.1, z.2.1⟩, z.2.2⟩
      invFun := fun z => ⟨z.1.1, z.1.2, z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.subtype_mk fun z => z.2.1).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  exact β.trans (DifferentialGeometry.Simplex.stdSimplexNormedBoundarySphereHomeomorph
    (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm)

private theorem nonempty_solidTorus_firstHomology_equiv_int {S : Set E3}
    (hS : IsTopologicalSolidTorus S) :
    Nonempty (integralSingularHomology 1 S ≃ₗ[ℤ] ℤ) := by
  obtain ⟨φ⟩ := hS
  let D := Metric.closedBall (0 : E2) 1
  let p : D := ⟨0, by simp [D]⟩
  let e : S ≃ₕ C2 := φ.toHomotopyEquiv.trans
    ((Homeomorph.prodComm D C2).toHomotopyEquiv.trans
      (DifferentialGeometry.HomotopyEquiv.productConvex C2 (convex_closedBall _ _) p))
  exact ⟨(integralSingularHomologyHomotopyEquiv 1 e).trans
    (integralSphereTopHomologyEquiv 0 E2 (by simp))⟩

private theorem exists_nonseparating_polygon_of_isPLTorus {T : Set E3} (hT : IsPLTorus T) :
    ∃ G : Set E3, IsPLSphere 1 G ∧ G ⊆ T ∧ IsPreconnected (T \ G) := by
  obtain ⟨L, hLfin, hL, hLc, hLT⟩ := hT.exists_combinatorial_triangulation
  let _ : Finite L.faces := hLfin.to_subtype
  have hχ : eulerChar L ≠ 2 := by
    intro hχ
    have hs := hL.isPLSphere_two_of_faceEulerChar_eq_two L hLc hχ
    rw [hLT] at hs
    obtain ⟨r, hr⟩ := hs
    let eS := hr.homeomorph.symm.trans (boundarySphereHomeomorph 2)
    let _ := integralSphereHomology_subsingleton 2 1 E3 (by simp) one_ne_zero (by norm_num)
    let _ : Subsingleton (integralSingularHomology 1 T) :=
      (integralSingularHomologyHomotopyEquiv 1 eS.toHomotopyEquiv).toEquiv.subsingleton
    obtain ⟨e⟩ := hT.2
    let _ : PathConnectedSpace C2 := isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere (by simp [← Module.finrank_eq_rank]) 0 zero_le_one)
    let q := integralSphereTopHomologyEquiv 0 E2 (by simp)
    let eH : integralSingularHomology 1 T ≃ₗ[ℤ] (ℤ × ℤ) :=
      (((integralSingularHomologyHomotopyEquiv 1 e.toHomotopyEquiv).toAddEquiv.trans
        integralSingularHomologyOneProdEquiv.toAddEquiv).trans
          (q.toAddEquiv.prodCongr q.toAddEquiv)).toIntLinearEquiv
    have h := congrArg eH
      (Subsingleton.elim (eH.symm (0, 0)) (eH.symm (1, 0)))
    have hz := congrArg Prod.fst h
    simp only [LinearEquiv.apply_symm_apply] at hz
    exact zero_ne_one hz
  obtain ⟨G, hG, hGL, hnonsep⟩ :=
    hL.exists_isPLSphere_one_isPreconnected_sdiff L hLc hχ
  exact ⟨G, hG, hGL.trans hLT.subset, by rwa [hLT] at hnonsep⟩

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

private theorem exists_primitive_polygon_coordinates {T : Set E3} (hT : IsPLTorus T) :
    ∃ e : (loopCircle × loopCircle) ≃ₜ T, ∀ m n u v : ℤ, u * m + v * n = 1 →
      IsPLSphere 1 (range fun t : loopCircle => (e (m • t, n • t) : E3)) := by
  obtain ⟨G, hG, hGT, hn⟩ := exists_nonseparating_polygon_of_isPLTorus hT
  obtain ⟨J, Q, f, -, hJ, hQ, hf, -, -⟩ :=
    exists_product_chart_nonseparating hT hG hGT hn
  exact hf.exists_polygonal_circle_product_coordinates hJ hQ

theorem IsCombinatorialSolidTorus.exists_isPLSphere_one_carriesFirstHomologyOnto_frontier
    {S : Set E3} (hS : IsCombinatorialSolidTorus S) :
    ∃ G : Set E3, IsPLSphere 1 G ∧ G ⊆ frontier S ∧ CarriesFirstHomologyOnto G S := by
  obtain ⟨e, he⟩ := exists_primitive_polygon_coordinates hS.isPLTorus_frontier
  obtain ⟨eS⟩ := nonempty_solidTorus_firstHomology_equiv_int hS.1
  let hCS := hS.isPolyhedron.isClosed.frontier_subset
  let i : C(frontier S, S) := ⟨inclusion hCS, continuous_inclusion hCS⟩
  let R : C(loopCircle × loopCircle, S) := i.comp ⟨e, e.continuous⟩
  have hi : Function.Surjective (integralSingularHomologyMap 1 i) := by
    intro a
    obtain ⟨x, hx⟩ := hS.bijective_integralSingularHomologyMap_frontier_pair.2 (a, 0)
    exact ⟨x, congrArg Prod.fst hx⟩
  have hR : Function.Surjective (integralSingularHomologyMap 1 R) := by
    change Function.Surjective (integralSingularHomologyMap 1
      (i.comp (⟨e, e.continuous⟩ : C(loopCircle × loopCircle, frontier S))))
    rw [integralSingularHomologyMap_comp]
    exact hi.comp (integralSingularHomologyHomotopyEquiv 1 e.toHomotopyEquiv).surjective
  let c := stdTriangleCircleHomeomorph.trans (boundarySphereHomeomorph 1)
  let _ : PathConnectedSpace C2 := isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_sphere (by simp [← Module.finrank_eq_rank]) 0 zero_le_one)
  let _ : PathConnectedSpace loopCircle := c.symm.surjective.pathConnectedSpace c.symm.continuous
  let eC : integralSingularHomology 1 loopCircle ≃ₗ[ℤ] ℤ :=
    (integralSingularHomologyHomotopyEquiv 1 c.toHomotopyEquiv).trans
      (integralSphereTopHomologyEquiv 0 E2 (by simp))
  let eP : integralSingularHomology 1 (loopCircle × loopCircle) ≃ₗ[ℤ] (ℤ × ℤ) :=
    (integralSingularHomologyOneProdEquiv.toAddEquiv.trans
      (eC.toAddEquiv.prodCongr eC.toAddEquiv)).toIntLinearEquiv
  let A : (ℤ × ℤ) →ₗ[ℤ] ℤ := eS.toLinearMap.comp
    ((integralSingularHomologyMap 1 R).comp eP.symm.toLinearMap)
  have hA : Function.Surjective A := eS.surjective.comp (hR.comp eP.symm.surjective)
  obtain ⟨x, hx⟩ := hA 1
  let m := x.1
  let n := x.2
  let u := A (1, 0)
  let v := A (0, 1)
  have hbez : u * m + v * n = 1 := by
    have hx' : x = m • (1, 0) + n • (0, 1) := by
      ext <;> simp [m, n]
    rw [hx', map_add, map_smul, map_smul] at hx
    simpa only [smul_eq_mul, mul_comm] using hx
  let p : C(loopCircle, loopCircle × loopCircle) :=
    ⟨fun t => (m • t, n • t),
      (continuous_id.zsmul m).prodMk (continuous_id.zsmul n)⟩
  let b := eC.symm 1
  have hp₁ : integralSingularHomologyMap 1 ContinuousMap.fst
      (integralSingularHomologyMap 1 p b) = m • b := by
    rw [← LinearMap.comp_apply, ← integralSingularHomologyMap_comp]
    change integralSingularHomologyMap 1 (m • ContinuousMap.id loopCircle) b = m • b
    rw [integralSingularHomologyMap_one_zsmul, integralSingularHomologyMap_id]
    rfl
  have hp₂ : integralSingularHomologyMap 1 ContinuousMap.snd
      (integralSingularHomologyMap 1 p b) = n • b := by
    rw [← LinearMap.comp_apply, ← integralSingularHomologyMap_comp]
    change integralSingularHomologyMap 1 (n • ContinuousMap.id loopCircle) b = n • b
    rw [integralSingularHomologyMap_one_zsmul, integralSingularHomologyMap_id]
    rfl
  have hmb : eC (m • b) = m • eC b := map_zsmul eC.toAddEquiv m b
  have hnb : eC (n • b) = n • eC b := map_zsmul eC.toAddEquiv n b
  have hpx : eP (integralSingularHomologyMap 1 p b) = x := by
    change (eC (integralSingularHomologyMap 1 ContinuousMap.fst
        (integralSingularHomologyMap 1 p b)),
      eC (integralSingularHomologyMap 1 ContinuousMap.snd
        (integralSingularHomologyMap 1 p b))) = x
    rw [hp₁, hp₂, hmb, hnb]
    simp [b, m, n]
  have hgen : integralSingularHomologyMap 1 R
      (integralSingularHomologyMap 1 p b) = eS.symm 1 := by
    apply eS.injective
    rw [LinearEquiv.apply_symm_apply]
    have hp' := congrArg eP.symm hpx
    rw [LinearEquiv.symm_apply_apply] at hp'
    rw [hp']
    exact hx
  let G : Set E3 := range fun t : loopCircle => (e (p t) : E3)
  have hG : IsPLSphere 1 G := he m n u v hbez
  have hGT : G ⊆ frontier S := by
    rintro y ⟨t, rfl⟩
    exact (e (p t)).2
  have hGS : G ⊆ S := hGT.trans hCS
  let q : C(loopCircle, G) :=
    ⟨fun t => ⟨e (p t), ⟨t, rfl⟩⟩,
      (continuous_subtype_val.comp (e.continuous.comp p.continuous)).subtype_mk _⟩
  refine ⟨G, hG, hGT, hGS, fun hsub a => ?_⟩
  let j : C(G, S) := ⟨inclusion hsub, continuous_inclusion hsub⟩
  have hj : j.comp q = R.comp p := by ext t; rfl
  have hjgen : integralSingularHomologyMap 1 j
      (integralSingularHomologyMap 1 q b) = eS.symm 1 := by
    rw [← LinearMap.comp_apply, ← integralSingularHomologyMap_comp, hj,
      integralSingularHomologyMap_comp]
    exact hgen
  refine ⟨eS a • integralSingularHomologyMap 1 q b, ?_⟩
  change integralSingularHomologyMap 1 j (eS a • integralSingularHomologyMap 1 q b) = a
  have hscale : integralSingularHomologyMap 1 j
      (eS a • integralSingularHomologyMap 1 q b) =
      eS a • integralSingularHomologyMap 1 j (integralSingularHomologyMap 1 q b) :=
    map_zsmul (integralSingularHomologyMap 1 j).toAddMonoidHom (eS a) _
  rw [hscale, hjgen]
  apply eS.injective
  have hscaleS : eS (eS a • eS.symm 1) = eS a • eS (eS.symm 1) :=
    map_zsmul eS.toAddEquiv (eS a) _
  rw [hscaleS, LinearEquiv.apply_symm_apply]
  simp

end DifferentialGeometry.Topology.PiecewiseLinear
