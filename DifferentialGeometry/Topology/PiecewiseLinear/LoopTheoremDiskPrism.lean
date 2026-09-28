/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement
import DifferentialGeometry.Topology.PiecewiseLinear.ComponentComplex
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsIsPLBallSupersetOfExteriorCompression
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskVocabulary
import DifferentialGeometry.Topology.PiecewiseLinear.PLBallSphere
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedronLocalConnectedness
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBoundaryImage
import DifferentialGeometry.Topology.PiecewiseLinear.SpanningDiskPrism

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem isPolyhedron_stdSimplexBoundary_two : IsPolyhedron (stdSimplexBoundary 2) := by
  have : Finite (simplexBoundary (stdVertices 1) (stdVertices_affineIndependent 1)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  rw [← simplexBoundary_stdVertices_space 1]
  exact isPolyhedron_space _

theorem exists_prism_of_inter_frontier_eq (XK : Geometry.SimplicialComplex ℝ E3)
    [Finite XK.faces] (hX : IsCombinatorialManifoldWithBoundary 3 XK) {V : Set E3}
    (hV : IsOpen V) {Δ : Set E3} {r : (Fin 3 → ℝ) → E3}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ) (hΔV : Δ ⊆ V)
    (hΔB : Δ ∩ frontier XK.space = r '' stdSimplexBoundary 2) :
    ∃ (N : Set E3) (f : (Fin 3 → ℝ) × ℝ → E3),
      IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) N ∧ N ⊆ V ∧
      (∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), f (x, 0) = r x) ∧
      frontier XK.space ∩ N = f '' (stdSimplexBoundary 2 ×ˢ Icc (-1 : ℝ) 1) ∧ Δ ⊆ N := by
  classical
  obtain ⟨L, hLfin, hL, hLeq⟩ :=
    hX.exists_isCombinatorialManifold_space_eq_frontier (n := 2) finrank_euclideanSpace_fin
  have : Finite L.faces := hLfin.to_subtype
  obtain ⟨y₀, hy₀⟩ := (isConnected_stdSimplexBoundary 0).nonempty
  have hbdΔ : r '' stdSimplexBoundary 2 ⊆ L.space := by
    rw [hLeq, ← hΔB]
    exact inter_subset_right
  have hp₀ : r y₀ ∈ L.space := hbdΔ ⟨y₀, hy₀, rfl⟩
  let S := restrict L (connectedComponentIn L.space (r y₀))
  have : Finite S.faces := (restrict_faces_finite L _).to_subtype
  have hSspace : S.space = connectedComponentIn L.space (r y₀) :=
    restrict_connectedComponentIn_space L (r y₀)
  have hS : IsCombinatorialManifold 2 S := hL.restrict_connectedComponentIn (r y₀)
  have hSc : IsConnected S.space := by
    rw [hSspace]
    exact isConnected_connectedComponentIn_iff.mpr hp₀
  have hconnB : IsPreconnected (r '' stdSimplexBoundary 2) :=
    (isConnected_stdSimplexBoundary 0).isPreconnected.image r
      (hr.isPiecewiseAffineOn.continuousOn.mono fun x hx => hx.1)
  have hBS : r '' stdSimplexBoundary 2 ⊆ S.space := by
    rw [hSspace]
    exact hconnB.subset_connectedComponentIn ⟨y₀, hy₀, rfl⟩ hbdΔ
  have hSL : S.space ⊆ L.space := by
    rw [hSspace]
    exact connectedComponentIn_subset _ _
  have hmeet : Δ ∩ S.space = r '' stdSimplexBoundary 2 := by
    apply Subset.antisymm
    · rintro y ⟨hyΔ, hyS⟩
      rw [← hΔB]
      refine ⟨hyΔ, ?_⟩
      rw [← hLeq]
      exact hSL hyS
    · intro y hy
      have hyΔ : y ∈ Δ ∩ frontier XK.space := by
        rw [hΔB]
        exact hy
      exact ⟨hyΔ.1, hBS hy⟩
  have hLcl : IsClosed L.space := (isPolyhedron_space L).isClosed
  have hrest : IsClosed (L.space \ S.space) := by
    let _ : LocallyConnectedSpace L.space := locallyConnectedSpace_space L
    have hc : IsClosed (connectedComponent (⟨r y₀, hp₀⟩ : L.space))ᶜ :=
      (isClopen_connectedComponent).isOpen.isClosed_compl
    have himg := hLcl.isClosedMap_subtype_val _ hc
    convert himg using 1
    rw [hSspace, connectedComponentIn_eq_image hp₀]
    ext y
    constructor
    · rintro ⟨hyL, hyS⟩
      exact ⟨⟨y, hyL⟩, fun hy => hyS ⟨⟨y, hyL⟩, hy, rfl⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.2, ?_⟩
      rintro ⟨w, hw, hwz⟩
      exact hz (Subtype.ext hwz ▸ hw)
  have hU : IsOpen (V \ (L.space \ S.space)) := hV.sdiff hrest
  have hΔU : Δ ⊆ V \ (L.space \ S.space) := by
    intro y hy
    refine ⟨hΔV hy, fun hyL => hyL.2 ?_⟩
    have hyB : y ∈ Δ ∩ frontier XK.space := ⟨hy, hLeq ▸ hyL.1⟩
    rw [hΔB] at hyB
    exact hBS hyB
  obtain ⟨N, f, hf, hNU, hzero, hwall, hΔN⟩ :=
    IsCombinatorialManifold.exists_centered_prism_neighborhood_of_spanning_disk S hS hSc
      finrank_euclideanSpace_fin hr hmeet hU hΔU
  refine ⟨N, f, hf, fun y hy => (hNU hy).1, hzero, ?_, hΔN⟩
  rw [← hwall, ← hLeq]
  apply Subset.antisymm
  · rintro y ⟨hyL, hyN⟩
    by_contra hyS
    exact (hNU hyN).2 ⟨hyL, fun h => hyS ⟨h, hyN⟩⟩
  · rintro y ⟨hyS, hyN⟩
    exact ⟨hSL hyS, hyN⟩

theorem isPLHomeomorphOn_prism_level {N : Set E3} {f : (Fin 3 → ℝ) × ℝ → E3}
    (hf : IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) N) {s : ℝ}
    (hs : s ∈ Icc (-1 : ℝ) 1) :
    IsPLHomeomorphOn (fun x => f (x, s)) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
      ((fun x => f (x, s)) '' Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) := by
  have hσ : IsPolyhedron (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) := (isHPolytope_stdSimplex (Fin 3)).isPolyhedron
  have hι : IsPiecewiseAffineOn (fun x : Fin 3 → ℝ => (x, s)) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) :=
    ((isPiecewiseAffineOn_id isOpen_univ).prod_mk
      (isPiecewiseAffineOn_of_affine (AffineMap.const ℝ (Fin 3 → ℝ) s)
        isOpen_univ)).mono_of_isPolyhedron hσ (subset_univ _)
  have hιinj : InjOn (fun x : Fin 3 → ℝ => (x, s)) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) :=
    fun x _ y _ h => (Prod.mk.inj h).1
  have hιpl := isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hσ hι hιinj.bijOn_image
  have hPpoly : IsPolyhedron ((fun x : Fin 3 → ℝ => (x, s)) '' Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) :=
    hσ.image_of_isPiecewiseAffineOn hι hιinj
  have hsub : (fun x : Fin 3 → ℝ => (x, s)) '' Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ⊆
      Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hx, hs⟩
  have htr := hιpl.trans (hf.restrict hPpoly hsub)
  rw [image_image] at htr
  exact htr

theorem prism_level_inter_eq {N : Set E3} {f : (Fin 3 → ℝ) × ℝ → E3}
    (hf : IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) N) {B : Set E3}
    (hwall : B ∩ N = f '' (stdSimplexBoundary 2 ×ˢ Icc (-1 : ℝ) 1)) {s : ℝ}
    (hs : s ∈ Icc (-1 : ℝ) 1) :
    (fun x => f (x, s)) '' Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ∩ B =
      (fun x => f (x, s)) '' stdSimplexBoundary 2 := by
  apply Subset.antisymm
  · rintro _ ⟨⟨x, hx, rfl⟩, hxB⟩
    have hN : f (x, s) ∈ N := hf.bijOn.mapsTo ⟨hx, hs⟩
    have hmem : f (x, s) ∈ B ∩ N := ⟨hxB, hN⟩
    rw [hwall] at hmem
    obtain ⟨⟨x', t'⟩, ⟨hx', ht'⟩, heq⟩ := hmem
    have hpair := hf.bijOn.injOn ⟨hx'.1, ht'⟩ ⟨hx, hs⟩ heq
    obtain ⟨rfl, -⟩ := Prod.mk.inj hpair
    exact ⟨x', hx', rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
    have hmem : f (x, s) ∈ B ∩ N := by
      rw [hwall]
      exact ⟨(x, s), ⟨hx, hs⟩, rfl⟩
    exact hmem.1

theorem not_nullhomotopic_prism_level {N : Set E3} {f : (Fin 3 → ℝ) × ℝ → E3}
    (hf : IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) N) {B : Set E3}
    (hwall : B ∩ N = f '' (stdSimplexBoundary 2 ×ˢ Icc (-1 : ℝ) 1)) {Δ : Set E3}
    {r : (Fin 3 → ℝ) → E3} (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ)
    (hzero : ∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), f (x, 0) = r x) (hb : r '' stdSimplexBoundary 2 ⊆ B)
    (hnull : ¬ (⟨Set.inclusion hb, continuous_inclusion hb⟩ :
      C(r '' stdSimplexBoundary 2, B)).Nullhomotopic)
    {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) (hbs : (fun x => f (x, s)) '' stdSimplexBoundary 2 ⊆ B) :
    ¬ (⟨Set.inclusion hbs, continuous_inclusion hbs⟩ :
      C((fun x => f (x, s)) '' stdSimplexBoundary 2, B)).Nullhomotopic := by
  intro hns
  have hBdσ : stdSimplexBoundary 2 ⊆ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) := fun x hx => hx.1
  have hmemB : ∀ x ∈ stdSimplexBoundary 2, ∀ t ∈ Icc (-1 : ℝ) 1, f (x, t) ∈ B := by
    intro x hx t ht
    have hmem : f (x, t) ∈ B ∩ N := by
      rw [hwall]
      exact ⟨(x, t), ⟨hx, ht⟩, rfl⟩
    exact hmem.1
  have hfc : ContinuousOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) :=
    hf.isPiecewiseAffineOn.continuousOn
  have hτ : ∀ τ : unitInterval, (τ : ℝ) * s ∈ Icc (-1 : ℝ) 1 := by
    intro τ
    obtain ⟨h0, h1⟩ := τ.2
    obtain ⟨hs0, hs1⟩ := hs
    constructor <;> nlinarith
  have hHc : Continuous fun p : unitInterval × stdSimplexBoundary 2 =>
      f ((p.2 : Fin 3 → ℝ), (p.1 : ℝ) * s) :=
    hfc.comp_continuous ((continuous_subtype_val.comp continuous_snd).prodMk
      ((continuous_subtype_val.comp continuous_fst).mul continuous_const))
      fun p => ⟨hBdσ p.2.2, hτ p.1⟩
  have hc0 : Continuous fun x : stdSimplexBoundary 2 => f ((x : Fin 3 → ℝ), (0 : ℝ)) :=
    hfc.comp_continuous (continuous_subtype_val.prodMk continuous_const)
      fun x => ⟨hBdσ x.2, by norm_num⟩
  have hcs : Continuous fun x : stdSimplexBoundary 2 => f ((x : Fin 3 → ℝ), s) :=
    hfc.comp_continuous (continuous_subtype_val.prodMk continuous_const)
      fun x => ⟨hBdσ x.2, hs⟩
  let φ₀ : C(stdSimplexBoundary 2, B) :=
    ⟨fun x => ⟨f (x, 0), hmemB x x.2 0 (by norm_num)⟩, hc0.subtype_mk _⟩
  let φs : C(stdSimplexBoundary 2, B) := ⟨fun x => ⟨f (x, s), hmemB x x.2 s hs⟩, hcs.subtype_mk _⟩
  let H : ContinuousMap.Homotopy φ₀ φs :=
    { toFun := fun p => ⟨f ((p.2 : Fin 3 → ℝ), (p.1 : ℝ) * s), hmemB _ p.2.2 _ (hτ p.1)⟩
      continuous_toFun := hHc.subtype_mk _
      map_zero_left := fun x => by
        apply Subtype.ext
        simp only [Set.Icc.coe_zero, zero_mul]
        rfl
      map_one_left := fun x => by
        apply Subtype.ext
        simp only [Set.Icc.coe_one, one_mul]
        rfl }
  let ks : C(stdSimplexBoundary 2, (fun x => f (x, s)) '' stdSimplexBoundary 2) :=
    ⟨fun x => ⟨f (x, s), ⟨x, x.2, rfl⟩⟩, hcs.subtype_mk _⟩
  obtain ⟨y, hy⟩ := hns.comp_left ks
  have hφ₀ : φ₀.Nullhomotopic := ⟨y, ContinuousMap.Homotopic.trans ⟨H⟩ hy⟩
  have hBd : IsPLHomeomorphOn r (stdSimplexBoundary 2) (r '' stdSimplexBoundary 2) :=
    hr.restrict isPolyhedron_stdSimplexBoundary_two hBdσ
  let kinv : C(r '' stdSimplexBoundary 2, stdSimplexBoundary 2) :=
    ⟨hBd.homeomorph.symm, hBd.homeomorph.symm.continuous⟩
  apply hnull
  convert hφ₀.comp_left kinv using 1
  refine ContinuousMap.ext fun z => Subtype.ext ?_
  change (z : E3) = f ((hBd.homeomorph.symm z : Fin 3 → ℝ), 0)
  rw [hzero _ (hBdσ (hBd.homeomorph.symm z).2)]
  have h := congrArg Subtype.val (hBd.homeomorph.apply_symm_apply z)
  exact h.symm

end DifferentialGeometry.Topology.PiecewiseLinear
