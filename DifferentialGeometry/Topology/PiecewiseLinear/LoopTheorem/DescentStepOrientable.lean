/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryAdaptation
import DifferentialGeometry.Topology.PiecewiseLinear.LoopClassReparametrization
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryCaseFromReading
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryCaseFromTube
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchNestedDescent
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ComplexityInduction
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.LemmaTwoOrientable
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossQuarterTurn
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryNeighborhoodRealization
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchDisjointDescent
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedCellReading
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryTubeProducerDouble
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.AdaptedCleanCap
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchCaseOne

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v w

theorem not_branchPreimage_eq_of_isOrientable
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (L : Geometry.SimplicialComplex ℝ F) [Finite L.faces]
    (hL : IsCombinatorialManifold 3 L) (hor : IsOrientable 3 L) :
    letI := combinatorialChartedSpace L hL
    ∀ {D : SingularTwoCell L.space} {BdM B : Set L.space}
      (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch},
      ¬hD.singularSet.IsBoundaryBranch c →
      ∀ {J : Set (EuclideanSpace ℝ (Fin 2))}, IsPLSphere 1 J →
        hD.branchPreimage c = J → False := by
  exact NormalSingularCellData.not_branchPreimage_eq_of_isOrientable L hL hor

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

theorem exists_descendingSurgery_of_disjoint_innermost_cleanDisk [T2Space M]
    [HasGroupoid M (plGroupoid 3)]
    (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : ¬hD.singularSet.IsBoundaryBranch c)
    {J T Q E : Set (EuclideanSpace ℝ (Fin 2))}
    {k : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hJ : IsPLSphere 1 J) (hT : IsPLSphere 1 T) (hJT : Disjoint J T)
    (hpre : hD.branchPreimage c = J ∪ T)
    (hQ : IsPLBall 2 Q) (hQsub : Q ⊆ interior D.domain) (hfrontQ : frontier Q = J)
    (hclean : doublePointPreimage (⇑D) D.domain ∩ Q = J) (hinj : InjOn (⇑D) Q)
    (hE : IsPLBall 2 E) (hfrontE : frontier E = T)
    (hk : IsPLHomeomorphOn k E Q) (hkT : k '' T = J) (hkcompat : EqOn (⇑D) (⇑D ∘ k) T)
    (hdisjoint : Disjoint Q E)
    {C : Set M} (hside : IsPLBoundarySide D C BdM)
    (hbuffer : ∀ z ∈ Set.range D.boundary, B ∈ 𝓝[BdM] z)
    {Θ : Type v} [TopologicalSpace Θ] {Y : Type w} {ρ : M → Y} {γ : Θ → Y}
    (e : Θ ≃ₜ frontier D.domain) (hloop : ∀ θ, ρ (⇑D (e θ)) = γ θ) :
    ∃ Sg : hD.DescendingSurgery, MapsTo (⇑Sg.cell) Sg.cell.domain C ∧
      (∀ z ∈ Set.range Sg.cell.boundary, B ∈ 𝓝[BdM] z) ∧
        ∃ e' : Θ ≃ₜ frontier Sg.cell.domain, ∀ θ, ρ (⇑Sg.cell (e' θ)) = γ θ := by
  have hQopen : Q ⊆ D.domain \ frontier D.domain := fun z hz =>
    ⟨interior_subset (hQsub hz), fun hfr =>
      (mem_frontier_iff_notMem_interior (interior_subset (hQsub hz))).mp hfr (hQsub hz)⟩
  have hQV : ⇑D '' Q ⊆ interior (C \ BdM) :=
    (Set.image_mono hQopen).trans
      (hside.image_sdiff_frontier_subset_interior_sdiff hD.preimage_boundary_eq_frontier)
  obtain ⟨E', Δ, hE', hEE', hE'int, hQE', hE'clean, hΔdom, hΔinj, hΔside, hΔbd, hΔmeet⟩ :=
    hD.exists_adaptedCleanCap_of_disjoint_innermost_cleanDisk hc hJ hT hJT hpre hQ hQsub
      hfrontQ hclean hinj hE hfrontE hk hkT hkcompat hdisjoint isOpen_interior hQV
      (Set.disjoint_left.mpr fun _ hz hzBd => (interior_subset hz).2 hzBd)
  exact hD.exists_descendingSurgery_of_adaptedCleanCap hc hJ hT hJT hpre hQ hQsub hfrontQ
    hclean hinj hE hfrontE hk hkT hkcompat hdisjoint hside hbuffer Δ hE' hEE' hE'int hQE'
    hE'clean hΔdom hΔinj hΔside hΔbd hΔmeet e hloop

end NormalSingularCellData

def crossSeamTubeDataQuarterTurn {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {D : SingularTwoCell M} {BdM B U : Set M}
    {hD : NormalSingularCellData D BdM B} {c : hD.singularSet.Branch}
    (T : CrossSeamTubeData hD c U) : CrossSeamTubeData hD c U where
  chart := T.chart ∘ crossQuarterTurn
  isTube :=
    { isOpen_tube := T.isTube.isOpen_tube
      continuousOn_chart := T.isTube.continuousOn_chart.comp
        continuous_crossQuarterTurn.continuousOn mapsTo_crossQuarterTurn_spliceCylinder
      injOn_chart := T.isTube.injOn_chart.comp injective_crossQuarterTurn.injOn
        mapsTo_crossQuarterTurn_spliceCylinder
      image_subset_tube := by
        rw [Set.image_comp, image_crossQuarterTurn_spliceCylinder]
        exact T.isTube.image_subset_tube
      image_spliceCore := by
        rw [Set.image_comp, image_crossQuarterTurn_spliceCore]
        exact T.isTube.image_spliceCore
      image_crossingFigure := by
        rw [Set.image_comp, image_crossQuarterTurn_crossingFigure, Set.image_comp,
          image_crossQuarterTurn_spliceCylinder]
        exact T.isTube.image_crossingFigure
      double_inter_tube := T.isTube.double_inter_tube }

theorem crossSeamTubeDataQuarterTurn_chart {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {D : SingularTwoCell M} {BdM B U : Set M}
    {hD : NormalSingularCellData D BdM B} {c : hD.singularSet.Branch}
    (T : CrossSeamTubeData hD c U) :
    (crossSeamTubeDataQuarterTurn T).chart = T.chart ∘ crossQuarterTurn := rfl

theorem image_crossSeamTubeDataQuarterTurn_spliceCylinder {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {D : SingularTwoCell M} {BdM B U : Set M}
    {hD : NormalSingularCellData D BdM B} {c : hD.singularSet.Branch}
    (T : CrossSeamTubeData hD c U) :
    (crossSeamTubeDataQuarterTurn T).chart '' spliceCylinder = T.chart '' spliceCylinder := by
  rw [crossSeamTubeDataQuarterTurn_chart, Set.image_comp, image_crossQuarterTurn_spliceCylinder]

theorem image_crossSeamTubeDataQuarterTurn_spliceEndDisks {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {D : SingularTwoCell M} {BdM B U : Set M}
    {hD : NormalSingularCellData D BdM B} {c : hD.singularSet.Branch}
    (T : CrossSeamTubeData hD c U) :
    (crossSeamTubeDataQuarterTurn T).chart '' spliceEndDisks = T.chart '' spliceEndDisks := by
  rw [crossSeamTubeDataQuarterTurn_chart, Set.image_comp, image_crossQuarterTurn_spliceEndDisks]

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

theorem exists_descendingSurgery_of_crossSeamReading [T2Space M] {U W : Set M}
    {hD : NormalSingularCellData D BdM B} {c : hD.singularSet.Branch}
    (T : CrossSeamTubeData hD c U) (Ct : PLSeamTubeChart M T.chart)
    {G : SingularTwoCell M} (R : PLCrossSeamReading T.chart G)
    (hG : hD.IsCrossRegluedCell c G)
    (hendDisks : T.chart '' spliceEndDisks ⊆ B)
    (htubeBdM : T.chart '' spliceCylinder ∩ BdM ⊆ T.chart '' spliceEndDisks)
    (hBdM : B ⊆ BdM)
    (hside : MapsTo (⇑D) D.domain W)
    (htubeW : T.chart '' spliceCylinder ⊆ W)
    (hbufferD : ∀ z ∈ Set.range D.boundary, B ∈ 𝓝[BdM] z)
    (hendBuffer : ∀ z ∈ T.chart '' spliceEndDisks, B ∈ 𝓝[BdM] z)
    {Gd : SingularTwoCell M} (hGd : hD.IsBoundarySurgeryCell c Gd)
    {Θ : Type w} [TopologicalSpace Θ] {p' q' u' v' : Θ}
    (σ₀ : Path p' q') (τ₀ : Path q' u') (υ₀ : Path u' v') (φ₀ : Path v' p')
    (ev : loopCircle → Θ)
    (hev : ∀ θ, ev θ = pathToCircle (σ₀.trans (τ₀.trans (υ₀.trans φ₀))) θ)
    {X : Type v} [TopologicalSpace X] [PathConnectedSpace X] (f : Θ → X) {x : X}
    (γ : freeLoop X) (hγ : ∀ θ, γ θ = f (ev θ))
    {N : Subgroup (FundamentalGroup X x)} [N.Normal] (hγN : ¬loopClassMeets γ x N)
    {ρ : X → M} (hρ : IsEmbedding ρ) (hrange : B ⊆ Set.range ρ)
    (hcase :
      (∃ (a b : X) (σ υ : Path a b) (τ φ : Path b a),
          (∀ t, σ t = f (σ₀ t)) ∧ (∀ t, τ t = f (τ₀ t)) ∧
          (∀ t, υ t = f (υ₀ t)) ∧ (∀ t, φ t = f (φ₀ t)) ∧
          Nonempty (BoundaryWordWitness Gd ρ (pathToCircle (σ.trans υ.symm))) ∧
          Nonempty (BoundaryWordWitness G ρ
            (pathToCircle (σ.trans (φ.trans (υ.trans τ)))))) ∨
        (∃ (a b : X) (σ : Path a b) (τ : Path b b) (υ : Path b a) (φ : Path a a),
          (∀ t, σ t = f (σ₀ t)) ∧ (∀ t, τ t = f (τ₀ t)) ∧
          (∀ t, υ t = f (υ₀ t)) ∧ (∀ t, φ t = f (φ₀ t)) ∧
          Nonempty (BoundaryWordWitness Gd ρ (pathToCircle (σ.trans υ))) ∧
          Nonempty (BoundaryWordWitness G ρ
            (pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm))))))) :
    ∃ (Sg : hD.DescendingSurgery) (e : loopCircle ≃ₜ frontier Sg.cell.domain)
      (δ : freeLoop X),
      MapsTo (⇑Sg.cell) Sg.cell.domain W ∧
      (∀ z ∈ Set.range Sg.cell.boundary, B ∈ 𝓝[BdM] z) ∧
      (∀ θ, ρ (δ θ) = Sg.cell (e θ)) ∧ ¬loopClassMeets δ x N := by
  have hends : ∀ z ∈ G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder),
      z ∈ frontier G.domain ↔ (R.coord z).2.2 = 0 ∨ (R.coord z).2.2 = 1 := by
    intro z hz
    have hz' : z ∈ R.tubeSource := by
      rw [R.tubeSource_eq]
      exact hz
    exact R.boundary_iff_end z hz'
  have hdomainR : (R.resolvedCell Ct).domain = G.domain := rfl
  have hcoordR : BijOn R.coord (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder))
      bentSource := by
    rw [← R.tubeSource_eq]
    exact R.bijOn_coord
  have hregluedR : EqOn (⇑G) (T.chart ∘ crossSeamInclude ∘ R.coord)
      (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) := by
    rw [← R.tubeSource_eq]
    exact R.reglued_eq
  have hresolvedR : EqOn (⇑(R.resolvedCell Ct)) (T.chart ∘ crossSeamResolve ∘ R.coord)
      (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) := by
    rw [← R.tubeSource_eq]
    intro z hz
    exact R.resolvedCell_apply_of_mem Ct hz
  have hcomplR : EqOn (⇑(R.resolvedCell Ct)) (⇑G)
      (G.domain \ ⇑G ⁻¹' (T.chart '' spliceCylinder)) := by
    intro z hz
    refine R.resolvedCell_apply_of_notMem Ct fun hzs => ?_
    rw [R.tubeSource_eq] at hzs
    exact hz.2 hzs.2
  rcases hcase with ⟨a, b, σ, υ, τ, φ, hσ, hτ, hυ, hφ, ⟨Wd⟩, ⟨Wr⟩⟩ |
    ⟨a, b, σ, τ, υ, φ, hσ, hτ, hυ, hφ, ⟨Wd⟩, ⟨Wr⟩⟩
  · obtain ⟨Ω₁, Ω₂, hΩ₁, hΩ₂, hcover, hcocont, hΩ₁tube, hΩ₁max, hlateral⟩ :=
      R.exists_boundary_cover Wr.param
    exact exists_descendingSurgery_side_buffer_of_crossSeamTube_reversing T hdomainR hcoordR
      hregluedR hresolvedR hcomplR hG hendDisks hends htubeBdM hBdM hside htubeW hbufferD
      hendBuffer hGd σ₀ τ₀ υ₀ φ₀ ev hev hσ hτ hυ hφ γ hγ hγN hρ hrange Wd Wr hΩ₁ hΩ₂ hcover
      hcocont hΩ₁tube hΩ₁max hlateral
  · obtain ⟨Ω₁, Ω₂, hΩ₁, hΩ₂, hcover, hcocont, hΩ₁tube, hΩ₁max, hlateral⟩ :=
      R.exists_boundary_cover Wr.param
    exact exists_descendingSurgery_side_buffer_of_crossSeamTube_preserving T hdomainR hcoordR
      hregluedR hresolvedR hcomplR hG hendDisks hends htubeBdM hBdM hside htubeW hbufferD
      hendBuffer hGd σ₀ τ₀ υ₀ φ₀ ev hev hσ hτ hυ hφ γ hγ hγN hρ hrange Wd Wr hΩ₁ hΩ₂ hcover
      hcocont hΩ₁tube hΩ₁max hlateral

end NormalSingularCellData

open Classical in
theorem descentStepOrientableStatement : DescentStepOrientableStatement := by
  classical
  intro E _ _ _ S hor K
  let _ : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
  let _ := combinatorialChartedSpace (double 3 K)
    (isCombinatorialManifold_double_succ_succ K S.isManifold)
  let _ := combinatorialChartedSpace_hasGroupoid (double 3 K)
    (isCombinatorialManifold_double_succ_succ K S.isManifold)
  intro ι C Bd B D₀ hD₀ hcomplexity hmapC hbuffer hloop
  obtain ⟨cD, δ, hδ, hδN⟩ := hloop
  have hsideC : IsPLBoundarySide D₀ C Bd :=
    isPLBoundarySide_double_of_normal K S.isManifold hD₀ hmapC
  by_cases hclosed : ∃ b : hD₀.singularSet.Branch, ¬hD₀.singularSet.IsBoundaryBranch b
  · obtain ⟨c, J, Q, hc, hJ, hQ, hQsub, hfrontQ, hclean, hsplit⟩ :=
      hD₀.exists_innermost_cleanDisk_replacement_of_exists_not_boundaryBranch hclosed
    rcases hsplit with hsingle | ⟨T, Ed, k, hT, hJT, hpre, hinj, hE, hfrontE, hk, hkT,
      hkcompat, hdich⟩
    · exact absurd hsingle (fun h =>
        not_branchPreimage_eq_of_isOrientable (double 3 K)
          (isCombinatorialManifold_double_succ_succ K S.isManifold)
          (S.isOrientable_double_manifoldComplex hor) hD₀ hc hJ h)
    · rcases hdich with hnested | hdisjoint
      · obtain ⟨Sg, hSgC, hSgB, e', he'⟩ :=
          hD₀.exists_descendingSurgery_of_nested_innermost_cleanDisk hc hJ hT hJT hpre hQ
            hfrontQ hclean hinj hE hfrontE hk hkT hkcompat hnested hmapC hbuffer cD hδ
        exact ⟨Sg, hSgC, hSgB, e', δ, he', hδN⟩
      · obtain ⟨Sg, hSgC, hSgB, e', he'⟩ :=
          hD₀.exists_descendingSurgery_of_disjoint_innermost_cleanDisk hc hJ hT hJT hpre hQ
            hQsub hfrontQ hclean hinj hE hfrontE hk hkT hkcompat hdisjoint hsideC hbuffer cD hδ
        exact ⟨Sg, hSgC, hSgB, e', δ, he', hδN⟩
  · have hallBoundary : ∀ b : hD₀.singularSet.Branch, hD₀.singularSet.IsBoundaryBranch b :=
      fun b => not_not.mp fun h => hclosed ⟨b, h⟩
    obtain ⟨c⟩ := hD₀.singularSet.nonempty_branch_of_complexity_ne_zero hcomplexity
    have hc : hD₀.singularSet.IsBoundaryBranch c := hallBoundary c
    obtain ⟨_, Tt, ⟨Ct⟩, htubeC, htubeBd, hendBuffer⟩ :=
      isPLBoundaryTubeProducer_double K S.isManifold D₀ Bd B C hD₀ c hc hsideC hbuffer
    have hendSub : Tt.chart '' spliceEndDisks ⊆ Bd := by
      rw [← htubeBd]
      exact fun z hz => hz.2
    have hendDisks : Tt.chart '' spliceEndDisks ⊆ B := fun z hz =>
      mem_of_mem_nhdsWithin (hendSub hz) (hendBuffer z hz)
    have hBBd : B ⊆ Bd := by
      rintro z ⟨y, hy, hzy⟩
      exact ⟨y, derivedNeighborhood_space_subset S.boundaryComplex S.loopComplex hy, hzy⟩
    obtain ⟨Acut, Ccut, p, q, r, s, gid, D₁, D₂, D₃, hcut⟩ :=
      hD₀.exists_isBoundaryBranchCut_of_boundaryBranch hc
    obtain ⟨ρ, fr, hρ, hρrange, hfr, hρι, hfrρ⟩ :=
      S.exists_boundaryNeighborhood_realization hD₀.boundary_image_subset
    obtain ⟨p', q', u', v', σ₀, τ₀, υ₀, φ₀, ev, Gd, G, hGd, hG, hev, hcase⟩ :=
      hD₀.exists_boundaryWordWitnesses_of_cut hcut hρ hρrange fr hfr hfrρ
    have hδf : ∀ θ, δ θ = fr (cD θ) := by
      intro θ
      apply hρ.injective
      rw [hfrρ (cD θ)]
      apply Subtype.ext
      rw [hρι (δ θ)]
      exact (hδ θ).symm
    have hcont : Continuous fun θ => fr (ev θ) := hfr.comp ev.continuous
    have hγN : ¬loopClassMeets
        (⟨fun θ => fr (ev θ), hcont⟩ : freeLoop S.boundaryNeighborhoodSpace)
        S.basepoint S.normalSubgroup := by
      have hγcomp : (⟨fun θ => fr (ev θ), hcont⟩ : freeLoop S.boundaryNeighborhoodSpace) =
          δ.comp ⟨ev.trans cD.symm, (ev.trans cD.symm).continuous⟩ :=
        ContinuousMap.ext fun θ => by
          change fr (ev θ) = δ (cD.symm (ev θ))
          rw [hδf (cD.symm (ev θ))]
          exact congrArg fr (cD.apply_symm_apply (ev θ)).symm
      rw [hγcomp]
      exact fun hmeet =>
        hδN ((loopClassMeets_comp_circleHomeomorph_iff δ (ev.trans cD.symm) _ _).mp hmeet)
    have := S.normal
    rcases exists_plCrossSeamReading_of_isCrossRegluedCell Tt Ct htubeBd hG with hR | hR
    · obtain ⟨R⟩ := hR
      obtain ⟨Sg, e', δ', hSgC, hSgB, hSge, hSgN⟩ :=
        NormalSingularCellData.exists_descendingSurgery_of_crossSeamReading Tt Ct R hG
          hendDisks htubeBd.subset hBBd hmapC htubeC hbuffer hendBuffer hGd σ₀ τ₀ υ₀ φ₀
          (fun θ => ev θ) hev fr ⟨fun θ => fr (ev θ), hcont⟩ (fun _ => rfl) hγN hρ hρrange
          hcase
      refine ⟨Sg, hSgC, hSgB, e', δ', fun θ => ?_, hSgN⟩
      rw [← hSge θ]
      exact hρι (δ' θ)
    · obtain ⟨R⟩ := hR
      obtain ⟨Ct'⟩ := nonempty_plSeamTubeChart_comp_crossQuarterTurn Ct
      have Rt : PLCrossSeamReading (crossSeamTubeDataQuarterTurn Tt).chart G := R
      have Ctt : PLSeamTubeChart _ (crossSeamTubeDataQuarterTurn Tt).chart := Ct'
      have hcyl : (crossSeamTubeDataQuarterTurn Tt).chart '' spliceCylinder =
          Tt.chart '' spliceCylinder :=
        image_crossSeamTubeDataQuarterTurn_spliceCylinder Tt
      have hend : (crossSeamTubeDataQuarterTurn Tt).chart '' spliceEndDisks =
          Tt.chart '' spliceEndDisks :=
        image_crossSeamTubeDataQuarterTurn_spliceEndDisks Tt
      have hendDisks' : (crossSeamTubeDataQuarterTurn Tt).chart '' spliceEndDisks ⊆ B := by
        rw [hend]
        exact hendDisks
      have htubeBd' : (crossSeamTubeDataQuarterTurn Tt).chart '' spliceCylinder ∩ Bd ⊆
          (crossSeamTubeDataQuarterTurn Tt).chart '' spliceEndDisks := by
        rw [hcyl, hend]
        exact htubeBd.subset
      have htubeC' : (crossSeamTubeDataQuarterTurn Tt).chart '' spliceCylinder ⊆ C := by
        rw [hcyl]
        exact htubeC
      have hendBuffer' : ∀ z ∈ (crossSeamTubeDataQuarterTurn Tt).chart '' spliceEndDisks,
          B ∈ 𝓝[Bd] z := by
        rw [hend]
        exact hendBuffer
      obtain ⟨Sg, e', δ', hSgC, hSgB, hSge, hSgN⟩ :=
        NormalSingularCellData.exists_descendingSurgery_of_crossSeamReading
          (crossSeamTubeDataQuarterTurn Tt) Ctt Rt hG hendDisks' htubeBd' hBBd hmapC htubeC'
          hbuffer hendBuffer' hGd σ₀ τ₀ υ₀ φ₀ (fun θ => ev θ) hev fr
          ⟨fun θ => fr (ev θ), hcont⟩ (fun _ => rfl) hγN hρ hρrange hcase
      refine ⟨Sg, hSgC, hSgB, e', δ', fun θ => ?_, hSgN⟩
      rw [← hSge θ]
      exact hρι (δ' θ)

end DifferentialGeometry.Topology.PiecewiseLinear
