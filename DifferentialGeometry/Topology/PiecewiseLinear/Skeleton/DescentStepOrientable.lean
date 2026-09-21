/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryAdaptation
import DifferentialGeometry.Topology.PiecewiseLinear.LoopClassReparametrization
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryCaseFromReading
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchNestedDescent
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ComplexityInduction
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.LemmaTwoOrientable

/-!
# Sorry-first skeleton of the orientable descent step

The assembly `descentStepOrientableStatement` below is proved for real from the eight leaves of
this file and from the proved producers of the tree; every `sorry` is a leaf, none is inside the
assembly.  The leaves are open obligations and none of them has been reviewed.

`not_branchPreimage_eq_of_isOrientable` (lane C, C-or1, not yet reviewed): in an orientable
combinatorial 3-manifold no closed branch of a normal singular two cell has a connected complete
preimage.  Shape taken from `consult/C-or1-design.md`, final theorem, stated for an arbitrary
orientable complex rather than only for the double.

`NormalSingularCellData.exists_descendingSurgery_of_disjoint_innermost_cleanDisk` (lane C, 2b,
not yet reviewed): the descending surgery of the second closed case when the innermost clean
disk `Q` is disjoint from the disk `E` bounded by the other preimage circle.  Hypotheses are
those of the proved nested endpoint `exists_descendingSurgery_of_nested_innermost_cleanDisk`,
with `Disjoint Q E` in place of `Q ⊆ interior E`, with `Q ⊆ interior D.domain` added because the
adapted clean cap has to be chosen inside the side, and with the side hypothesis strengthened
from `MapsTo D D.domain C` to `IsPLBoundarySide D C BdM`, which is what places the image of `Q`
in the interior of the side.

`isPLBoundaryTubeProducer_double` (lane S, not yet reviewed): the double of a combinatorial
3-manifold with boundary admits boundary-relative PL product tubes around boundary branches.
The statement is `IsPLBoundaryTubeProducer` of `BoundaryAdaptation` verbatim, at the double.

`NormalSingularCellData.exists_boundaryWordWitnesses_of_cut` (lane F, F9, not yet reviewed):
from one boundary branch cut, both candidates together with both boundary word witnesses over
the four arc words, in the endpoint reversing and in the endpoint preserving alternative.  The
cell-level half of this conclusion is already proved by
`NormalSingularCellData.exists_boundaryCandidates_of_cut`; what is open is the passage from the
recorded two arc parametrisations to the witnesses, through the source-arc matches of
`LoopTheorem.BoundaryCaseFromSource`.

`exists_plCrossSeamReading_of_isCrossRegluedCell` (lane F and lane S seam, not yet reviewed):
the cross reglued cell of a boundary branch is read in the normal form of any PL boundary tube
around that branch.  This is the touching seam of Moise's Case 3/4.

`NormalSystem.exists_boundaryNeighborhood_realization` (new, not yet reviewed): the boundary
neighborhood of a normal system embeds in the double compatibly with `ι`, and the boundary
circle of a normal cell factors continuously through it.  This is the ambient loop space the
boundary word witnesses are stated over.

`exists_descendingSurgery_side_buffer_of_crossSeamTube_reversing` and
`..._preserving` (lane F, F10, not yet reviewed): the two boundary case assemblies of
`LoopTheorem.BoundarySurgeryCellPredicate` with the side and the boundary buffer added to the
conclusion.  They supersede those two assemblies, whose conclusion records neither clause, so
the skeleton calls these and not them; the four added hypotheses are the side of `D`, the
containment of the parametrised cylinder in the side, the buffer of `D` and the buffer of the
end disks, all supplied by `isPLBoundarySide_double_of_normal` and by the tube producer.
-/

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
  sorry

theorem isPLBoundaryTubeProducer_double
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) :
    letI := combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K hK)
    IsPLBoundaryTubeProducer (double 3 K).space := by
  sorry

open Classical in
theorem NormalSystem.exists_boundaryNeighborhood_realization
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S : NormalSystem E) :
    letI : Finite S.manifoldComplex.faces := S.manifoldComplex_faces_finite.to_subtype
    letI := combinatorialChartedSpace (double 3 S.manifoldComplex)
      (isCombinatorialManifold_double_succ_succ S.manifoldComplex S.isManifold)
    let ι := simplicialMap S.manifoldComplex
      (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 S.manifoldComplex) id)
    let B := ((↑) : (double 3 S.manifoldComplex).space → E × E × ℝ) ⁻¹'
      (ι '' S.boundaryNeighborhood.space)
    ∀ {D : SingularTwoCell (double 3 S.manifoldComplex).space},
      Set.range D.boundary ⊆ B →
      ∃ (ρ : S.boundaryNeighborhoodSpace → (double 3 S.manifoldComplex).space)
        (f : frontier D.domain → S.boundaryNeighborhoodSpace),
        IsEmbedding ρ ∧ B ⊆ Set.range ρ ∧ Continuous f ∧
          (∀ y : S.boundaryNeighborhoodSpace,
            ((ρ y : (double 3 S.manifoldComplex).space) : E × E × ℝ) = ι (y : E)) ∧
          ∀ z : frontier D.domain, ρ (f z) = D z := by
  sorry

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

theorem exists_descendingSurgery_of_disjoint_innermost_cleanDisk [T2Space M]
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
  sorry

theorem exists_boundaryWordWitnesses_of_cut [T2Space M]
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    {A Cc : Set (EuclideanSpace ℝ (Fin 2))} {p q r s : EuclideanSpace ℝ (Fin 2)}
    {g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {D₁ D₂ D₃ : SingularTwoCell M}
    (hcut : hD.IsBoundaryBranchCut c A Cc p q r s g D₁ D₂ D₃)
    {X : Type v} [TopologicalSpace X] [PathConnectedSpace X]
    {ρ : X → M} (hρ : IsEmbedding ρ) (hrange : B ⊆ Set.range ρ)
    (f : frontier D.domain → X) (hf : Continuous f)
    (hfρ : ∀ z : frontier D.domain, ρ (f z) = ⇑D z) :
    ∃ (p' q' u' v' : frontier D.domain) (σ₀ : Path p' q') (τ₀ : Path q' u')
        (υ₀ : Path u' v') (φ₀ : Path v' p') (ev : loopCircle ≃ₜ frontier D.domain)
        (Gd G : SingularTwoCell M),
      hD.IsBoundarySurgeryCell c Gd ∧ hD.IsCrossRegluedCell c G ∧
      (∀ θ, ev θ = pathToCircle (σ₀.trans (τ₀.trans (υ₀.trans φ₀))) θ) ∧
      ((∃ (a b : X) (σ υ : Path a b) (τ φ : Path b a),
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
            (pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm))))))) := by
  sorry

end NormalSingularCellData

theorem exists_plCrossSeamReading_of_isCrossRegluedCell
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [T2Space M]
    {D : SingularTwoCell M} {BdM B U : Set M} {hD : NormalSingularCellData D BdM B}
    {c : hD.singularSet.Branch} (T : CrossSeamTubeData hD c U)
    (hchart : PLSeamTubeChart M T.chart)
    {G : SingularTwoCell M} (hG : hD.IsCrossRegluedCell c G) :
    Nonempty (PLCrossSeamReading T.chart G) := by
  sorry

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

theorem exists_descendingSurgery_side_buffer_of_crossSeamTube_reversing
    [T2Space M] {U : Set M} {hD : NormalSingularCellData D BdM B}
    {c : hD.singularSet.Branch}
    (T : CrossSeamTubeData hD c U) {G cell : SingularTwoCell M}
    {coord : EuclideanSpace ℝ (Fin 2) → Bool × ((ℝ × ℝ) × ℝ)}
    (hdomain : cell.domain = G.domain)
    (hcoord : BijOn coord (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) bentSource)
    (hreglued : EqOn G (T.chart ∘ crossSeamInclude ∘ coord)
      (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)))
    (hresolved : EqOn cell (T.chart ∘ crossSeamResolve ∘ coord)
      (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)))
    (hcompl : EqOn cell G (G.domain \ ⇑G ⁻¹' (T.chart '' spliceCylinder)))
    (hG : hD.IsCrossRegluedCell c G)
    (hendDisks : T.chart '' spliceEndDisks ⊆ B)
    (hends : ∀ x ∈ G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder),
      x ∈ frontier G.domain ↔ (coord x).2.2 = 0 ∨ (coord x).2.2 = 1)
    (htubeBdM : T.chart '' spliceCylinder ∩ BdM ⊆ T.chart '' spliceEndDisks)
    (hBdM : B ⊆ BdM)
    {W : Set M} (hside : MapsTo (⇑D) D.domain W)
    (htubeW : T.chart '' spliceCylinder ⊆ W)
    (hbufferD : ∀ z ∈ Set.range D.boundary, B ∈ 𝓝[BdM] z)
    (hendBuffer : ∀ z ∈ T.chart '' spliceEndDisks, B ∈ 𝓝[BdM] z)
    {Gd : SingularTwoCell M} (hGd : hD.IsBoundarySurgeryCell c Gd)
    {Q : Type w} [TopologicalSpace Q] {p' q' u' v' : Q}
    (σ₀ : Path p' q') (τ₀ : Path q' u') (υ₀ : Path u' v') (φ₀ : Path v' p')
    (ev : loopCircle → Q)
    (hev : ∀ θ, ev θ = pathToCircle (σ₀.trans (τ₀.trans (υ₀.trans φ₀))) θ)
    {X : Type v} [TopologicalSpace X] [PathConnectedSpace X] {f : Q → X} {x a b : X}
    {σ υ : Path a b} {τ φ : Path b a}
    (hσ : ∀ t, σ t = f (σ₀ t)) (hτ : ∀ t, τ t = f (τ₀ t)) (hυ : ∀ t, υ t = f (υ₀ t))
    (hφ : ∀ t, φ t = f (φ₀ t)) (γ : freeLoop X) (hγ : ∀ θ, γ θ = f (ev θ))
    {N : Subgroup (FundamentalGroup X x)} [N.Normal] (hγN : ¬loopClassMeets γ x N)
    {ρ : X → M} (hρ : IsEmbedding ρ) (hrange : B ⊆ Set.range ρ)
    (Wdirect : BoundaryWordWitness Gd ρ (pathToCircle (σ.trans υ.symm)))
    (Wraw : BoundaryWordWitness G ρ (pathToCircle (σ.trans (φ.trans (υ.trans τ)))))
    {Ω₁ Ω₂ : Set loopCircle} (hΩ₁ : IsClosed Ω₁) (hΩ₂ : IsClosed Ω₂)
    (hcover : Ω₁ ∪ Ω₂ = univ)
    (hcocont : ContinuousOn (fun θ => coord ↑(Wraw.param θ)) Ω₁)
    (hΩ₁tube : ∀ θ ∈ Ω₁, ⇑G ↑(Wraw.param θ) ∈ T.chart '' spliceCylinder)
    (hΩ₁max : ∀ θ, ⇑G ↑(Wraw.param θ) ∈ T.chart '' spliceCylinder → θ ∈ Ω₁)
    (hlateral : ∀ θ ∈ Ω₁ ∩ Ω₂, (coord ↑(Wraw.param θ)).2.1 ∈ spliceSquareBoundary) :
    ∃ (Sg : hD.DescendingSurgery) (e : loopCircle ≃ₜ frontier Sg.cell.domain)
      (δ : freeLoop X),
      MapsTo (⇑Sg.cell) Sg.cell.domain W ∧
      (∀ z ∈ Set.range Sg.cell.boundary, B ∈ 𝓝[BdM] z) ∧
      (∀ θ, ρ (δ θ) = Sg.cell (e θ)) ∧ ¬loopClassMeets δ x N := by
  sorry

theorem exists_descendingSurgery_side_buffer_of_crossSeamTube_preserving
    [T2Space M] {U : Set M} {hD : NormalSingularCellData D BdM B}
    {c : hD.singularSet.Branch}
    (T : CrossSeamTubeData hD c U) {G cell : SingularTwoCell M}
    {coord : EuclideanSpace ℝ (Fin 2) → Bool × ((ℝ × ℝ) × ℝ)}
    (hdomain : cell.domain = G.domain)
    (hcoord : BijOn coord (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) bentSource)
    (hreglued : EqOn G (T.chart ∘ crossSeamInclude ∘ coord)
      (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)))
    (hresolved : EqOn cell (T.chart ∘ crossSeamResolve ∘ coord)
      (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)))
    (hcompl : EqOn cell G (G.domain \ ⇑G ⁻¹' (T.chart '' spliceCylinder)))
    (hG : hD.IsCrossRegluedCell c G)
    (hendDisks : T.chart '' spliceEndDisks ⊆ B)
    (hends : ∀ x ∈ G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder),
      x ∈ frontier G.domain ↔ (coord x).2.2 = 0 ∨ (coord x).2.2 = 1)
    (htubeBdM : T.chart '' spliceCylinder ∩ BdM ⊆ T.chart '' spliceEndDisks)
    (hBdM : B ⊆ BdM)
    {W : Set M} (hside : MapsTo (⇑D) D.domain W)
    (htubeW : T.chart '' spliceCylinder ⊆ W)
    (hbufferD : ∀ z ∈ Set.range D.boundary, B ∈ 𝓝[BdM] z)
    (hendBuffer : ∀ z ∈ T.chart '' spliceEndDisks, B ∈ 𝓝[BdM] z)
    {Gd : SingularTwoCell M} (hGd : hD.IsBoundarySurgeryCell c Gd)
    {Q : Type w} [TopologicalSpace Q] {p' q' u' v' : Q}
    (σ₀ : Path p' q') (τ₀ : Path q' u') (υ₀ : Path u' v') (φ₀ : Path v' p')
    (ev : loopCircle → Q)
    (hev : ∀ θ, ev θ = pathToCircle (σ₀.trans (τ₀.trans (υ₀.trans φ₀))) θ)
    {X : Type v} [TopologicalSpace X] [PathConnectedSpace X] {f : Q → X} {x a b : X}
    {σ : Path a b} {τ : Path b b} {υ : Path b a} {φ : Path a a}
    (hσ : ∀ t, σ t = f (σ₀ t)) (hτ : ∀ t, τ t = f (τ₀ t)) (hυ : ∀ t, υ t = f (υ₀ t))
    (hφ : ∀ t, φ t = f (φ₀ t)) (γ : freeLoop X) (hγ : ∀ θ, γ θ = f (ev θ))
    {N : Subgroup (FundamentalGroup X x)} [N.Normal] (hγN : ¬loopClassMeets γ x N)
    {ρ : X → M} (hρ : IsEmbedding ρ) (hrange : B ⊆ Set.range ρ)
    (Wdirect : BoundaryWordWitness Gd ρ (pathToCircle (σ.trans υ)))
    (Wraw : BoundaryWordWitness G ρ
      (pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm)))))
    {Ω₁ Ω₂ : Set loopCircle} (hΩ₁ : IsClosed Ω₁) (hΩ₂ : IsClosed Ω₂)
    (hcover : Ω₁ ∪ Ω₂ = univ)
    (hcocont : ContinuousOn (fun θ => coord ↑(Wraw.param θ)) Ω₁)
    (hΩ₁tube : ∀ θ ∈ Ω₁, ⇑G ↑(Wraw.param θ) ∈ T.chart '' spliceCylinder)
    (hΩ₁max : ∀ θ, ⇑G ↑(Wraw.param θ) ∈ T.chart '' spliceCylinder → θ ∈ Ω₁)
    (hlateral : ∀ θ ∈ Ω₁ ∩ Ω₂, (coord ↑(Wraw.param θ)).2.1 ∈ spliceSquareBoundary) :
    ∃ (Sg : hD.DescendingSurgery) (e : loopCircle ≃ₜ frontier Sg.cell.domain)
      (δ : freeLoop X),
      MapsTo (⇑Sg.cell) Sg.cell.domain W ∧
      (∀ z ∈ Set.range Sg.cell.boundary, B ∈ 𝓝[BdM] z) ∧
      (∀ θ, ρ (δ θ) = Sg.cell (e θ)) ∧ ¬loopClassMeets δ x N := by
  sorry

end NormalSingularCellData

open Classical in
theorem descentStepOrientableStatement : DescentStepOrientableStatement := by
  classical
  intro E _ _ _ S hor K
  let _ : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
  let _ := combinatorialChartedSpace (double 3 K)
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
    obtain ⟨R⟩ := exists_plCrossSeamReading_of_isCrossRegluedCell Tt Ct hG
    have hends : ∀ z ∈ G.domain ∩ ⇑G ⁻¹' (Tt.chart '' spliceCylinder),
        z ∈ frontier G.domain ↔ (R.coord z).2.2 = 0 ∨ (R.coord z).2.2 = 1 := by
      intro z hz
      have hz' : z ∈ R.tubeSource := by
        rw [R.tubeSource_eq]
        exact hz
      exact R.boundary_iff_end z hz'
    have hdomainR : (R.resolvedCell Ct).domain = G.domain := rfl
    have hcoordR : BijOn R.coord (G.domain ∩ ⇑G ⁻¹' (Tt.chart '' spliceCylinder))
        bentSource := by
      rw [← R.tubeSource_eq]
      exact R.bijOn_coord
    have hregluedR : EqOn (⇑G) (Tt.chart ∘ crossSeamInclude ∘ R.coord)
        (G.domain ∩ ⇑G ⁻¹' (Tt.chart '' spliceCylinder)) := by
      rw [← R.tubeSource_eq]
      exact R.reglued_eq
    have hresolvedR : EqOn (⇑(R.resolvedCell Ct)) (Tt.chart ∘ crossSeamResolve ∘ R.coord)
        (G.domain ∩ ⇑G ⁻¹' (Tt.chart '' spliceCylinder)) := by
      rw [← R.tubeSource_eq]
      intro z hz
      exact R.resolvedCell_apply_of_mem Ct hz
    have hcomplR : EqOn (⇑(R.resolvedCell Ct)) (⇑G)
        (G.domain \ ⇑G ⁻¹' (Tt.chart '' spliceCylinder)) := by
      intro z hz
      refine R.resolvedCell_apply_of_notMem Ct fun hzs => ?_
      rw [R.tubeSource_eq] at hzs
      exact hz.2 hzs.2
    have := S.normal
    rcases hcase with ⟨a, b, σ, υ, τ, φ, hσ, hτ, hυ, hφ, ⟨Wd⟩, ⟨Wr⟩⟩ |
      ⟨a, b, σ, τ, υ, φ, hσ, hτ, hυ, hφ, ⟨Wd⟩, ⟨Wr⟩⟩
    · obtain ⟨Ω₁, Ω₂, hΩ₁, hΩ₂, hcover, hcocont, hΩ₁tube, hΩ₁max, hlateral⟩ :=
        R.exists_boundary_cover Wr.param
      obtain ⟨Sg, e', δ', hSgC, hSgB, hSge, hSgN⟩ :=
        NormalSingularCellData.exists_descendingSurgery_side_buffer_of_crossSeamTube_reversing
          Tt hdomainR hcoordR hregluedR hresolvedR hcomplR hG hendDisks hends htubeBd.subset
          hBBd hmapC htubeC hbuffer hendBuffer hGd σ₀ τ₀ υ₀ φ₀ (fun θ => ev θ) hev hσ hτ hυ hφ
          ⟨fun θ => fr (ev θ), hcont⟩ (fun _ => rfl) hγN hρ hρrange Wd Wr hΩ₁ hΩ₂ hcover
          hcocont hΩ₁tube hΩ₁max hlateral
      refine ⟨Sg, hSgC, hSgB, e', δ', fun θ => ?_, hSgN⟩
      rw [← hSge θ]
      exact hρι (δ' θ)
    · obtain ⟨Ω₁, Ω₂, hΩ₁, hΩ₂, hcover, hcocont, hΩ₁tube, hΩ₁max, hlateral⟩ :=
        R.exists_boundary_cover Wr.param
      obtain ⟨Sg, e', δ', hSgC, hSgB, hSge, hSgN⟩ :=
        NormalSingularCellData.exists_descendingSurgery_side_buffer_of_crossSeamTube_preserving
          Tt hdomainR hcoordR hregluedR hresolvedR hcomplR hG hendDisks hends htubeBd.subset
          hBBd hmapC htubeC hbuffer hendBuffer hGd σ₀ τ₀ υ₀ φ₀ (fun θ => ev θ) hev hσ hτ hυ hφ
          ⟨fun θ => fr (ev θ), hcont⟩ (fun _ => rfl) hγN hρ hρrange Wd Wr hΩ₁ hΩ₂ hcover
          hcocont hΩ₁tube hΩ₁max hlateral
      refine ⟨Sg, hSgC, hSgB, e', δ', fun θ => ?_, hSgN⟩
      rw [← hSge θ]
      exact hρι (δ' θ)

end DifferentialGeometry.Topology.PiecewiseLinear
