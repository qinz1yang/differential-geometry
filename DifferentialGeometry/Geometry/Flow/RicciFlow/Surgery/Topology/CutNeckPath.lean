import DifferentialGeometry.Geometry.Neck.RelativeNeckPath
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CylindricalCoreCapping
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutBandCylinder

noncomputable section

open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] (T : TubeSystem M)

omit [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] in
private theorem boundarySphere_subset_closedBands
    (b : T.Boundary) : range (T.boundarySphere b) ⊆
      ⋃ i, T.tube i '' {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1} := by
  rintro z ⟨q,rfl⟩
  apply mem_iUnion.mpr
  exact ⟨b.1,(q,boundaryLevel b.2),by cases b.2 <;> norm_num [boundaryLevel],rfl⟩

omit [CompactSpace M] in
theorem exists_cut_neck_cylinder_stop_or_return_tolerance :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M]
        (T : TubeSystem M) (g : SmoothRiemannianMetric I3 M) (point : T.Index → M)
        (neck : ∀ i, SpatialNeck g eps (point i)),
        (∀ i (q : TubeDomain), T.tube i q = (neck i).map (q.1,q.2.val)) →
        ∀ b : T.Boundary,
          let W := ⋃ i, T.tube i '' {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1}
          (∃ (R : PartialDiffeomorph IC I3 Cylinder M ∞) (p : M)
            (nk : SpatialNeck g eps p) (a : ℝ) (κ : Sphere 2 ≃ₘ⟮I2,I2⟯ Sphere 2),
            univ ×ˢ Icc (0 : ℝ) 1 ⊆ R.source ∧ |a| ≤ 4 ∧
            (∀ q : Sphere 2, R (q,0) = T.boundarySphere b q) ∧
            (∀ q : Sphere 2, R (q,1) = nk.map (κ q,a)) ∧
            R '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ W = range (T.boundarySphere b) ∧
            Disjoint (range (fun q : Sphere 2 => nk.map (q,a))) W ∧
            closure (interior (W ∪ R '' (univ ×ˢ Icc (0 : ℝ) 1))) =
              W ∪ R '' (univ ×ˢ Icc (0 : ℝ) 1) ∧
            frontier (W ∪ R '' (univ ×ˢ Icc (0 : ℝ) 1)) =
              range (fun q : Sphere 2 => nk.map (q,a)) ∪
                ⋃ c : {c : T.Boundary // c ≠ b}, range (T.boundarySphere c.val) ∧
            ¬ Nonempty (SpatialNeck g eps (nk.map (nk.center,a)))) ∨
          (∃ (c : T.Boundary), c ≠ b ∧ ∃ (ρ : Sphere 2 ≃ₘ⟮I2,I2⟯ Sphere 2)
            (R : PartialDiffeomorph IC I3 Cylinder M ∞),
            univ ×ˢ Icc (0 : ℝ) 1 ⊆ R.source ∧
            (∀ q : Sphere 2, R (q,0) = T.boundarySphere b q) ∧
            (∀ q : Sphere 2, R (q,1) = T.boundarySphere c (ρ q)) ∧
            R '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ W =
              range (T.boundarySphere b) ∪ range (T.boundarySphere c) ∧
            closure (interior (W ∪ R '' (univ ×ˢ Icc (0 : ℝ) 1))) =
              W ∪ R '' (univ ×ˢ Icc (0 : ℝ) 1) ∧
            frontier (W ∪ R '' (univ ×ˢ Icc (0 : ℝ) 1)) =
              ⋃ d : {d : T.Boundary // d ≠ b ∧ d ≠ c}, range (T.boundarySphere d.val)) := by
  obtain ⟨eta,heta,hmain⟩ := exists_spatial_neck_cylinder_stop_or_return_tolerance.{u,0}
  refine ⟨eta,heta,?_⟩
  intro eps heps M _ _ _ _ _ T g point neck hmap b W
  have hsrc (i : T.Index) : univ ×ˢ Icc (-(3/2) : ℝ) (3/2) ⊆ (neck i).map.source := by
    intro q hq
    have hinv : (2 : ℝ) < eps⁻¹ :=
      lt_inv_of_lt_inv₀ (neck i).eps_pos ((neck i).eps_small.trans (by norm_num))
    exact (neck i).domain ⟨hq.1,by linarith [hq.2.1],by linarith [hq.2.2]⟩
  obtain ⟨hWcompact,hWreg,hWfront,A,hA,_,hA0,hA1,ha,hinter,hout,hreg,hfront⟩ :=
    T.exists_outward_cut_cylinder_of_partialDiffeomorph (fun i => (neck i).map) hsrc hmap b
  let I := {c : T.Boundary // c ≠ b}
  let savedPoint : I → M := fun c => point c.val.1
  let savedNeck : ∀ c : I, SpatialNeck g eps (savedPoint c) := fun c => neck c.val.1
  let savedLevel : I → ℝ := fun c => (boundaryLevel c.val.2).val
  have hs (c : I) (q : Sphere 2) :
      (savedNeck c).map (q,savedLevel c) = T.boundarySphere c.val q :=
    (hmap c.val.1 (q,boundaryLevel c.val.2)).symm
  have hsrange (c : I) : range (fun q : Sphere 2 => (savedNeck c).map (q,savedLevel c)) =
      range (T.boundarySphere c.val) := by congr 1; exact funext (hs c)
  have hlevels (c : I) : |savedLevel c| ≤ 4 := by
    dsimp [savedLevel]
    cases c.val.2 <;> norm_num [boundaryLevel]
  have hsave (c : I) : range (fun q : Sphere 2 => (savedNeck c).map (q,savedLevel c)) ⊆ W := by
    rw [hsrange]
    exact T.boundarySphere_subset_closedBands c.val
  have hpairs : Pairwise fun c d : I =>
      Disjoint (range (fun q : Sphere 2 => (savedNeck c).map (q,savedLevel c)))
        (range (fun q : Sphere 2 => (savedNeck d).map (q,savedLevel d))) := by
    intro c d hcd
    rw [hsrange,hsrange]
    exact T.pairwise_disjoint_range_boundarySphere (fun h => hcd (Subtype.ext h))
  have hlower (c : I) : Disjoint (range (fun q : Sphere 2 => A (q,0)))
      (range (fun q : Sphere 2 => (savedNeck c).map (q,savedLevel c))) := by
    simp only [hA0,hsrange]
    exact T.pairwise_disjoint_range_boundarySphere c.property.symm
  have hfront' : frontier (W ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1)) =
      range (fun q : Sphere 2 => (neck b.1).map (q,if b.2 then 3/2 else -(3/2))) ∪
        ⋃ c : I, range (fun q : Sphere 2 => (savedNeck c).map (q,savedLevel c)) := by
    simpa only [hsrange] using hfront
  have hi' : A '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ W = range (fun q : Sphere 2 => A (q,0)) := by
    simpa only [hA0] using hinter
  rcases hmain eps heps M g I savedPoint savedNeck savedLevel W (isClosed_closure.isCompact)
      hlevels hsave hpairs A hA hlower (point b.1) (neck b.1)
      (if b.2 then 3/2 else -(3/2)) (Diffeomorph.refl I2 (Sphere 2) ∞) ha hA1 hi' hout hreg hfront' with hstop | hreturn
  · obtain ⟨R,p,nk,a,κ,hR,ha,hR0,hR1,_,hRW,hRo,hRreg,hRf,hstop⟩ := hstop
    exact Or.inl ⟨R,p,nk,a,κ,hR,ha,fun q => (hR0 q).trans (hA0 q),hR1,
      by simpa only [hA0] using hRW,hRo,hRreg,by simpa only [hsrange] using hRf,hstop⟩
  · obtain ⟨c,ρ,R,hR,hR0,hR1,_,hRW,hRreg,hRf⟩ := hreturn
    refine Or.inr ⟨c.val,c.property,ρ,R,hR,fun q => (hR0 q).trans (hA0 q),
      fun q => (hR1 q).trans (hs c (ρ q)),by simpa only [hA0,hsrange] using hRW,hRreg,?_⟩
    rw [hRf]
    ext z
    simp only [mem_iUnion,hsrange]
    constructor
    · rintro ⟨d,hd⟩
      exact ⟨⟨d.val.val,d.val.property,fun he => d.property (Subtype.ext he)⟩,hd⟩
    · rintro ⟨d,hd⟩
      exact ⟨⟨⟨d.val,d.property.1⟩,fun he => d.property.2 (congrArg Subtype.val he)⟩,hd⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

section

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

universe u

theorem exists_cut_neck_standard_or_stopped_tolerance :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ (M N : ClosedOrientedManifold.{u} 3) (T : SphericalTubeSystem M)
        (C : SphericalCapping M N T) (g : SmoothRiemannianMetric I3 M.Carrier)
        (point : T.Index → M.Carrier) (neck : ∀ i, SpatialNeck g eps (point i)),
        (∀ i (q : TubeDomain), T.tube i q = (neck i).map (q.1,q.2.val)) →
        ∀ b : T.Boundary,
          let W := ⋃ i, T.tube i '' {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1}
          (∀ q : Sphere 2, isPoincareStandard
            (N.component (ConnectedComponents.mk (C.coreInclusion (T.coreBoundarySphere b q)))).Carrier) ∨
          (∃ (R : PartialDiffeomorph IC I3 Cylinder M.Carrier ∞) (p : M.Carrier)
            (nk : SpatialNeck g eps p) (a : ℝ) (κ : Sphere 2 ≃ₘ⟮I2,I2⟯ Sphere 2),
            univ ×ˢ Icc (0 : ℝ) 1 ⊆ R.source ∧ |a| ≤ 4 ∧
            (∀ q : Sphere 2, R (q,0) = T.boundarySphere b q) ∧
            (∀ q : Sphere 2, R (q,1) = nk.map (κ q,a)) ∧
            R '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ W = range (T.boundarySphere b) ∧
            Disjoint (range (fun q : Sphere 2 => nk.map (q,a))) W ∧
            closure (interior (W ∪ R '' (univ ×ˢ Icc (0 : ℝ) 1))) =
              W ∪ R '' (univ ×ˢ Icc (0 : ℝ) 1) ∧
            frontier (W ∪ R '' (univ ×ˢ Icc (0 : ℝ) 1)) =
              range (fun q : Sphere 2 => nk.map (q,a)) ∪
                ⋃ c : {c : T.Boundary // c ≠ b}, range (T.boundarySphere c.val) ∧
            ¬ Nonempty (SpatialNeck g eps (nk.map (nk.center,a)))) := by
  obtain ⟨eta,heta,hpath⟩ := TubeSystem.exists_cut_neck_cylinder_stop_or_return_tolerance.{u}
  refine ⟨eta,heta,?_⟩
  intro eps heps M N T C g point neck hmap b W
  rcases hpath eps heps M.Carrier T.toTopological g point neck hmap b with hstop | hreturn
  · exact Or.inr hstop
  · left
    obtain ⟨c,hcb,ρ,R,hR,hR0,hR1,hRW,_,hfront⟩ := hreturn
    have hlo : range (fun q : Sphere 2 => R (q,0)) = range (T.boundarySphere b) := by
      simp only [hR0]
      rfl
    have hhi : range (fun q : Sphere 2 => R (q,1)) = range (T.boundarySphere c) := by
      ext y
      constructor
      · rintro ⟨q,rfl⟩
        exact ⟨ρ q,(hR1 q).symm⟩
      · rintro ⟨q,rfl⟩
        refine ⟨ρ.symm q,?_⟩
        change R (ρ.symm q,1) = _
        rw [hR1,ρ.apply_symm_apply]
        rfl
    intro q
    apply C.isPoincareStandard_component_of_returned_cylinder R hR b c hlo hhi hRW
      (fun z hz => hfront ▸ hz) (T.coreBoundarySphere b q)
    exact ⟨(q,0),⟨mem_univ _,by norm_num⟩,hR0 q⟩

end DifferentialGeometry.Topology.SphericalCapping

end
