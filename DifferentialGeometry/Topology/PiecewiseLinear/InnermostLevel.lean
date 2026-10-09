/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SingularLevelPolygons
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PlanarJordan.Innermost
import DifferentialGeometry.Topology.ConvexFrontier

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_innermost_isPLBall {C : Set (Set (EuclideanSpace ℝ (Fin 2)))}
    (hC : C.Finite) (hne : C.Nonempty) (hsphere : ∀ J ∈ C, IsPLSphere 1 J)
    (p : EuclideanSpace ℝ (Fin 2))
    (hinter : ∀ J ∈ C, ∀ T ∈ C, J ≠ T → J ∩ T ⊆ {p}) :
    ∃ J ∈ C, ∃ D : Set (EuclideanSpace ℝ (Fin 2)),
      IsPLBall 2 D ∧ frontier D = J ∧ (⋃₀ C) ∩ D = J := by
  classical
  obtain ⟨J, hJ, hinside⟩ := PlanarJordan.exists_innermost_jordan_curve_of_inter_subset_singleton
    hC.toFinset (by simpa only [Set.Finite.toFinset_nonempty] using hne)
    (fun J hJ => isJordanCurve_of_isPLSphere_one (hsphere J (hC.mem_toFinset.mp hJ))) p
    (fun J hJ T hT hJT => hinter J (hC.mem_toFinset.mp hJ) T (hC.mem_toFinset.mp hT) hJT)
  have hJC : J ∈ C := hC.mem_toFinset.mp hJ
  have hJsep := Schoenflies.jordan_curve_theorem (isJordanCurve_of_isPLSphere_one (hsphere J hJC))
  let D := closure (Schoenflies.inside J)
  have hD : IsPLBall 2 D := isPLBall_closure_inside_of_isPLSphere_one (hsphere J hJC)
  have hfront : frontier D = J := frontier_closure_inside_of_isPLSphere_one (hsphere J hJC)
  have hDunion : D = Schoenflies.inside J ∪ J := by
    dsimp only [D]
    rw [closure_eq_self_union_frontier, hJsep.frontier_inside]
  refine ⟨J, hJC, D, hD, hfront, ?_⟩
  ext x
  constructor
  · rintro ⟨hxC, hxD⟩
    rcases hDunion.subset hxD with hxinside | hxJ
    · obtain ⟨T, hT, hxT⟩ := mem_sUnion.mp hxC
      exact (Set.disjoint_left.mp (hinside T (hC.mem_toFinset.mpr hT)) hxinside hxT).elim
    · exact hxJ
  · intro hxJ
    exact ⟨mem_sUnion.mpr ⟨J, hJC, hxJ⟩, hDunion.symm.subset (Or.inr hxJ)⟩

theorem exists_spanning_disk_of_mem_heightSingularPoints {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    {p : E} (hp : p ∈ heightSingularPoints K.space ℓ)
    {W : Set E} (hW : IsOpen W) (hWconv : Convex ℝ W) (hKW : K.space ⊆ W) :
    ∃ (D : Set E) (f : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧
      (f '' stdSimplexBoundary 2) ∈ levelPolygons K.space ℓ (ℓ p) ∧
      K.space ∩ D = f '' stdSimplexBoundary 2 ∧ D ⊆ W ∩ {x | ℓ x = ℓ p} ∧
      D ∉ 𝓝[{x | ℓ x = ℓ p}] p := by
  classical
  let C := levelPolygons K.space ℓ (ℓ p)
  let F := {x | ℓ x = ℓ p}
  have hCfin : C.Finite :=
    finite_levelPolygons K (fun s hs => hK.card_le K hs) hdimE ℓ hℓ hinj (ℓ p)
  have hpC : p ∈ ⋃₀ C := mem_sUnion_levelPolygons_of_mem_heightSingularPoints K hK hdimE ℓ hℓ hinj
      hp
  have hCne : C.Nonempty := by
    obtain ⟨J, hJ, -⟩ := mem_sUnion.mp hpC
    exact ⟨J, hJ⟩
  have hpv := heightSingularPoints_subset_vertices K hK.isCombinatorialManifoldWithBoundary hdimE ℓ
      hℓ hinj hp
  have hcover : K.space ∩ F = ⋃₀ C := by
    rw [show F = {x | ℓ x = ℓ p} from rfl,
      fiber_eq_singleton_union_sUnion_levelPolygons K hK hdimE ℓ hℓ hinj hpv,
      union_eq_right.mpr (singleton_subset_iff.mpr hpC)]
  obtain ⟨e, π, hleft, hfixed, heheight⟩ := exists_affine_coordinates_of_linear_fiber hdimE ℓ hℓ (ℓ
      p)
  have hπinj : InjOn π F := by
    intro x hx y hy hxy
    exact ((hfixed x).mpr hx).symm.trans ((congrArg e hxy).trans ((hfixed y).mpr hy))
  have hπJ : ∀ J ∈ C, IsPLHomeomorphOn π J (π '' J) := by
    intro J hJ
    exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hJ.1.isPolyhedron
      ((isPiecewiseAffineOn_of_affine π.toAffineMap isOpen_univ).mono_of_isPolyhedron
        hJ.1.isPolyhedron (subset_univ _))
      ⟨mapsTo_image _ _, hπinj.mono (hJ.2.trans inter_subset_right), fun _ h => h⟩
  have heπJ : ∀ J ∈ C, e '' (π '' J) = J := by
    intro J hJ
    rw [image_image]
    have heq : EqOn (e ∘ π) id J := fun x hx => (hfixed x).mpr (hJ.2 hx).2
    exact heq.image_eq.trans (image_id _)
  let C' := (fun J => π '' J) '' C
  have hC'fin : C'.Finite := hCfin.image _
  have hC'ne : C'.Nonempty := hCne.image _
  have hC'sphere : ∀ J ∈ C', IsPLSphere 1 J := by
    rintro J ⟨A, hA, rfl⟩
    exact hA.1.of_isPLHomeomorphOn (hπJ A hA)
  have hC'inter : ∀ J ∈ C', ∀ T ∈ C', J ≠ T → J ∩ T ⊆ {π p} := by
    rintro J ⟨A, hA, rfl⟩ T ⟨B, hB, rfl⟩ hne x ⟨⟨a, ha, hax⟩, b, hb, hbx⟩
    have hab : a = b := hπinj (hA.2 ha).2 (hB.2 hb).2 (hax.trans hbx.symm)
    have hAB : A ≠ B := fun h => hne (congrArg (fun J => π '' J) h)
    have hap : a = p := inter_subset_singleton_levelPolygons_of_ne K hK hdimE ℓ hℓ hinj hpv
      hA hB hAB ⟨ha, hab.symm ▸ hb⟩
    exact hax.symm.trans (congrArg π hap)
  obtain ⟨J', hJ', A, hA, hAfr, hAinter⟩ :=
    exists_innermost_isPLBall hC'fin hC'ne hC'sphere (π p) hC'inter
  obtain ⟨J, hJ, rfl⟩ := hJ'
  have heA : IsPLHomeomorphOn e A (e '' A) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hA.isPolyhedron
      ((isPiecewiseAffineOn_of_affine e isOpen_univ).mono_of_isPolyhedron hA.isPolyhedron
          (subset_univ _))
      ⟨mapsTo_image _ _, hleft.injective.injOn, fun _ h => h⟩
  have hπcover : π '' (K.space ∩ F) = ⋃₀ C' := by
    rw [hcover, image_sUnion]
  have hJA : π '' J ⊆ A :=
    hAfr.symm.subset.trans (frontier_subset_closure.trans
        hA.isPolyhedron.isClosed.closure_eq.subset)
  have hSD : K.space ∩ (e '' A) = J := by
    apply Subset.antisymm
    · rintro x ⟨hxK, y, hyA, rfl⟩
      have hyC : y ∈ ⋃₀ C' := by
        rw [← hπcover]
        exact ⟨e y, ⟨hxK, heheight y⟩, hleft y⟩
      have hyJ : y ∈ π '' J := hAinter.subset ⟨hyC, hyA⟩
      exact (heπJ J hJ).subset (mem_image_of_mem e hyJ)
    · intro x hxJ
      exact ⟨(hJ.2 hxJ).1, π x, hJA (mem_image_of_mem π hxJ), (hfixed x).mpr (hJ.2 hxJ).2⟩
  have hecont : Continuous e :=
    continuousOn_univ.mp (isPiecewiseAffineOn_of_affine e isOpen_univ).continuousOn
  have hJW : π '' J ⊆ e ⁻¹' W := by
    rintro y ⟨x, hxJ, rfl⟩
    change e (π x) ∈ W
    rw [(hfixed x).mpr (hJ.2 hxJ).2]
    exact hKW (hJ.2 hxJ).1
  have hAW : A ⊆ e ⁻¹' W := subset_of_isCompact_of_frontier_subset_open_convex
    hA.isPolyhedron.isCompact (hW.preimage hecont) (hWconv.affine_preimage e)
    ((hJ.1.nonempty.image π).mono hJW) (hAfr.trans_le hJW)
  have hepp : e (π p) = p := (hfixed p).mpr rfl
  have hpnot : π p ∉ interior A := by
    intro hpA
    have hpJ : p ∈ J := hSD.subset ⟨hp.1, π p, interior_subset hpA, hepp⟩
    have hpfr : π p ∈ frontier A := hAfr.symm.subset (mem_image_of_mem π hpJ)
    exact hpfr.2 hpA
  obtain ⟨u, hu⟩ := hA
  have hboundary : (e ∘ u) '' stdSimplexBoundary 2 = J := by
    rw [image_comp, IsPLHomeomorphOn.image_stdSimplexBoundary hu, hAfr, heπJ J hJ]
  refine ⟨e '' A, e ∘ u, hu.trans heA, hboundary.symm ▸ hJ, ?_, ?_, ?_⟩
  · exact hSD.trans hboundary.symm
  · rintro x ⟨y, hy, rfl⟩
    exact ⟨hAW hy, heheight y⟩
  · intro hDnhds
    have het : Filter.Tendsto e (𝓝 (π p)) (𝓝[F] p) := tendsto_nhdsWithin_iff.mpr
      ⟨by simpa only [hepp] using (hecont.continuousAt (x := π p)).tendsto,
        Filter.Eventually.of_forall heheight⟩
    have hAnhds := het hDnhds
    change e ⁻¹' (e '' A) ∈ 𝓝 (π p) at hAnhds
    rw [hleft.injective.preimage_image] at hAnhds
    exact hpnot (mem_interior_iff_mem_nhds.mpr hAnhds)

end DifferentialGeometry.Topology.PiecewiseLinear
