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

The assembly `descentStepOrientableStatement` below is proved for real from the ten leaves of
this file and from the proved producers of the tree; every `sorry` is a leaf, none is inside an
assembly.  An external review of the 2026-09-20 snapshot `06a96eb1de64` is digested in
`consult/G-descent-skeleton-review-digest.md`; the three defects it found are repaired here.

Repair 1, boundary separation.  `IsPLBoundarySide` now carries `IsClosed BdM`, without which the
universally quantified `BdM` may swallow an open set around an interior point of a branch and no
tube can satisfy `chart '' spliceCylinder ∩ BdM = chart '' spliceEndDisks`.
`IsPLBoundarySide.image_sdiff_frontier_subset_interior_sdiff` is the consequence the surgery
consumers use, `D '' (D.domain \ frontier D.domain) ⊆ interior (W \ BdM)`, from properness.

Repair 2, the 2b split.  The old single 2b leaf is now the proved theorem
`exists_descendingSurgery_of_disjoint_innermost_cleanDisk`, which chooses
`V := interior (C \ BdM)` by repair 1 and then calls the two new leaves: the geometric cap
producer `exists_adaptedCleanCap_of_disjoint_innermost_cleanDisk`, whose conclusion mentions no
surgery, and the cut and paste consumer `exists_descendingSurgery_of_adaptedCleanCap`.

Repair 3, the reading leaf.  `crossQuarterTurn` is the quarter turn `(x, y, t) ↦ (-y, x, t)` of
the model cylinder, which fixes `spliceCylinder`, `spliceCore`, `crossingFigure`,
`spliceEndDisks` and the lateral wall but exchanges the two adjacent bent sheet pairings, so a
reading exists only up to it; the leaf receives the tube boundary equality and concludes a
disjunction.  `crossSeamTubeDataQuarterTurn` repackages the tube along that turn for real, and
the invariance of the four producer conclusions is proved from the image equalities; only the
piecewise linear structure of the turned chart is left open.

The leaves, with owner and review state.

`not_branchPreimage_eq_of_isOrientable` (lane C, C-or1, reviewed 2026-09-21 (external),
statement frozen): in an orientable combinatorial 3-manifold no closed branch of a normal
singular two cell has a connected complete preimage.

`isPLBoundaryTubeProducer_double` (lane S, reviewed 2026-09-21 (external), repaired by repair 1,
statement frozen): the double of a combinatorial 3-manifold with boundary admits
boundary-relative PL product tubes around boundary branches.  The statement is
`IsPLBoundaryTubeProducer` of `BoundaryAdaptation` verbatim, at the double; the closedness of
`BdM` now travels inside `IsPLBoundarySide`.

`NormalSystem.exists_boundaryNeighborhood_realization` (lane S, reviewed 2026-09-21 (external),
statement frozen): the boundary neighborhood of a normal system embeds in the double compatibly
with `ι`, and the boundary circle of a normal cell factors continuously through it.

`NormalSingularCellData.exists_adaptedCleanCap_of_disjoint_innermost_cleanDisk` (lane C, 2b cap,
reviewed 2026-09-21 (external), repaired by adding `[HasGroupoid M (plGroupoid 3)]`, statement
frozen): in a PL manifold, for every open `V` with `D '' Q ⊆ V ⊆ interior (W \ BdM)` there
are a larger source disk `E'` and a
PL embedded cap parametrised by a singular two cell on `E'`, lying in `V`, agreeing with `D` on
`frontier E'` and meeting `D '' D.domain` in that circle only.  No surgery occurs in the
conclusion; the expensive step behind it is the adapted-neighbourhood trace theorem.  Without
compatibility of the atlas the statement is false: with the two global charts `id` and
`g (x, y, z) = (x, y, z + (1 + x² + y²) z³)`, the first used on the image of the cell and the
second off it, the old cell stays piecewise linear but no piecewise linear cap exists, since a
rank two affine piece that is affine in both charts lies in the plane `z = 0`.  That the old
cell is piecewise linear in its charts does not give a compatible three dimensional piecewise
linear neighbourhood of its image; the groupoid instance does.

`NormalSingularCellData.exists_descendingSurgery_of_adaptedCleanCap` (lane C, 2b surgery,
reviewed 2026-09-21 (external), statement frozen): from that cap data, the descending surgery
with the three invariants, in the
style of the proved nested endpoint `exists_descendingSurgery_of_isNestedDiskReplacementCell`.
It is cut and paste along `frontier E'` plus whole or nothing branch retention, and it is left
open because the disjoint analogue of `IsNestedDiskReplacementCell`, of its normality producer
and of its branch injection is not in the tree.

`NormalSingularCellData.exists_boundaryWordWitnesses_of_cut` (lane F, F9, reviewed 2026-09-21
(external), statement frozen): from one boundary branch cut, both candidates together with both
boundary word witnesses over the four arc words, in the endpoint reversing and in the endpoint
preserving alternative.  The preserving word is the one the review confirmed; no
orientation-preserving comparison is added.

`exists_plCrossSeamReading_of_isCrossRegluedCell` (lane F and lane S seam, reviewed 2026-09-21
(external), repaired by repair 3, statement frozen): the cross reglued cell of a boundary branch
is read in the normal form of the given PL boundary tube, or in the normal form of its quarter
turn.  The hypothesis `T.chart '' spliceCylinder ∩ BdM = T.chart '' spliceEndDisks` is the tube
boundary equality the reading's boundary clause needs and the old statement did not receive.

`nonempty_plSeamTubeChart_comp_crossQuarterTurn` (lane S, reviewed 2026-09-21 (external),
statement frozen): the quarter
turn of a PL seam tube chart is again one.  Everything else about the turned tube is proved in
`crossSeamTubeDataQuarterTurn`; what is open is only the transport of `PLPieceIn` along the
linear automorphism `crossQuarterTurn`, which preserves `spliceCylinder`.

`exists_descendingSurgery_side_buffer_of_crossSeamTube_reversing` and `..._preserving` (lane F,
F10, reviewed 2026-09-21 (external), statement frozen): the two boundary case assemblies of
`LoopTheorem.BoundarySurgeryCellPredicate` with the side and the boundary buffer added to the
conclusion.  They supersede those two assemblies, whose conclusion records neither clause; the
four added hypotheses are supplied by `isPLBoundarySide_double_of_normal` and by the tube
producer.  Both leaves share one inheritance lemma.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v w

def crossQuarterTurn (p : (ℝ × ℝ) × ℝ) : (ℝ × ℝ) × ℝ := ((-p.1.2, p.1.1), p.2)

theorem crossQuarterTurn_iterate_four (p : (ℝ × ℝ) × ℝ) :
    crossQuarterTurn (crossQuarterTurn (crossQuarterTurn (crossQuarterTurn p))) = p := by
  obtain ⟨⟨a, b⟩, t⟩ := p
  simp [crossQuarterTurn]

theorem injective_crossQuarterTurn : Function.Injective crossQuarterTurn :=
  Function.LeftInverse.injective
    (g := fun p => crossQuarterTurn (crossQuarterTurn (crossQuarterTurn p)))
    crossQuarterTurn_iterate_four

theorem continuous_crossQuarterTurn : Continuous crossQuarterTurn := by
  unfold crossQuarterTurn
  exact (continuous_fst.snd.neg.prodMk continuous_fst.fst).prodMk continuous_snd

theorem image_crossQuarterTurn_of_mapsTo {S : Set ((ℝ × ℝ) × ℝ)}
    (h : MapsTo crossQuarterTurn S S) : crossQuarterTurn '' S = S := by
  refine Subset.antisymm ?_ fun p hp => ⟨_, h (h (h hp)), crossQuarterTurn_iterate_four p⟩
  rintro _ ⟨p, hp, rfl⟩
  exact h hp

theorem mapsTo_crossQuarterTurn_prod {S : Set (ℝ × ℝ)} {I : Set ℝ}
    (hS : MapsTo (fun q : ℝ × ℝ => (-q.2, q.1)) S S) :
    MapsTo crossQuarterTurn (S ×ˢ I) (S ×ˢ I) :=
  fun _ hp => ⟨hS hp.1, hp.2⟩

theorem mapsTo_crossQuarterTurn_spliceSquare :
    MapsTo (fun q : ℝ × ℝ => (-q.2, q.1)) spliceSquare spliceSquare := by
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  refine ⟨?_, ha⟩
  rw [Set.mem_Icc] at hb ⊢
  exact ⟨by linarith [hb.2], by linarith [hb.1]⟩

theorem mapsTo_crossQuarterTurn_origin :
    MapsTo (fun q : ℝ × ℝ => (-q.2, q.1)) ({((0 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ))
      ({((0 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ)) := by
  intro q hq
  rw [Set.mem_singleton_iff] at hq
  subst hq
  simp

theorem mapsTo_crossQuarterTurn_crossingArc :
    MapsTo (fun q : ℝ × ℝ => (-q.2, q.1)) (crossingArcX ∪ crossingArcY)
      (crossingArcX ∪ crossingArcY) := by
  rintro q (⟨hq, hx⟩ | ⟨hq, hy⟩)
  · exact Or.inr ⟨mapsTo_crossQuarterTurn_spliceSquare hq, hx⟩
  · refine Or.inl ⟨mapsTo_crossQuarterTurn_spliceSquare hq, ?_⟩
    change -q.2 = 0
    simp [hy]

theorem mapsTo_crossQuarterTurn_spliceSquareBoundary :
    MapsTo (fun q : ℝ × ℝ => (-q.2, q.1)) spliceSquareBoundary spliceSquareBoundary := by
  rintro q ⟨hq, hb⟩
  refine ⟨mapsTo_crossQuarterTurn_spliceSquare hq, ?_⟩
  rcases hb with h | h | h | h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · refine Or.inr (Or.inl ?_)
    change -q.2 = 1
    simp [h]
  · refine Or.inl ?_
    change -q.2 = -1
    simp [h]

theorem mapsTo_crossQuarterTurn_spliceCylinder :
    MapsTo crossQuarterTurn spliceCylinder spliceCylinder :=
  mapsTo_crossQuarterTurn_prod mapsTo_crossQuarterTurn_spliceSquare

theorem mapsTo_crossQuarterTurn_spliceEndDisks :
    MapsTo crossQuarterTurn spliceEndDisks spliceEndDisks :=
  mapsTo_crossQuarterTurn_prod mapsTo_crossQuarterTurn_spliceSquare

theorem mapsTo_crossQuarterTurn_spliceCore :
    MapsTo crossQuarterTurn spliceCore spliceCore :=
  mapsTo_crossQuarterTurn_prod mapsTo_crossQuarterTurn_origin

theorem mapsTo_crossQuarterTurn_crossingFigure :
    MapsTo crossQuarterTurn crossingFigure crossingFigure :=
  mapsTo_crossQuarterTurn_prod mapsTo_crossQuarterTurn_crossingArc

theorem mapsTo_crossQuarterTurn_lateral :
    MapsTo crossQuarterTurn (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1)
      (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1) :=
  mapsTo_crossQuarterTurn_prod mapsTo_crossQuarterTurn_spliceSquareBoundary

theorem image_crossQuarterTurn_spliceCylinder :
    crossQuarterTurn '' spliceCylinder = spliceCylinder :=
  image_crossQuarterTurn_of_mapsTo mapsTo_crossQuarterTurn_spliceCylinder

theorem image_crossQuarterTurn_spliceEndDisks :
    crossQuarterTurn '' spliceEndDisks = spliceEndDisks :=
  image_crossQuarterTurn_of_mapsTo mapsTo_crossQuarterTurn_spliceEndDisks

theorem image_crossQuarterTurn_spliceCore :
    crossQuarterTurn '' spliceCore = spliceCore :=
  image_crossQuarterTurn_of_mapsTo mapsTo_crossQuarterTurn_spliceCore

theorem image_crossQuarterTurn_crossingFigure :
    crossQuarterTurn '' crossingFigure = crossingFigure :=
  image_crossQuarterTurn_of_mapsTo mapsTo_crossQuarterTurn_crossingFigure

theorem image_crossQuarterTurn_lateral :
    crossQuarterTurn '' (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1) =
      spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1 :=
  image_crossQuarterTurn_of_mapsTo mapsTo_crossQuarterTurn_lateral

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

theorem exists_adaptedCleanCap_of_disjoint_innermost_cleanDisk [T2Space M]
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
    {V W : Set M} (hV : IsOpen V) (hQV : ⇑D '' Q ⊆ V) (hVW : V ⊆ interior (W \ BdM)) :
    ∃ (E' : Set (EuclideanSpace ℝ (Fin 2))) (Δ : SingularTwoCell M),
      IsPLBall 2 E' ∧ E ⊆ interior E' ∧ E' ⊆ interior D.domain ∧ Disjoint Q E' ∧
        (E' \ E) ∩ doublePointPreimage (⇑D) D.domain = ∅ ∧
          Δ.domain = E' ∧ InjOn (⇑Δ) E' ∧ ⇑Δ '' E' ⊆ V ∧ EqOn (⇑Δ) (⇑D) (frontier E') ∧
            ⇑Δ '' E' ∩ ⇑D '' D.domain = ⇑D '' frontier E' := by
  sorry

theorem exists_descendingSurgery_of_adaptedCleanCap [T2Space M]
    (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : ¬hD.singularSet.IsBoundaryBranch c)
    {J T Q E E' : Set (EuclideanSpace ℝ (Fin 2))}
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
    (Δ : SingularTwoCell M)
    (hE' : IsPLBall 2 E') (hEE' : E ⊆ interior E') (hE'int : E' ⊆ interior D.domain)
    (hQE' : Disjoint Q E') (hE'clean : (E' \ E) ∩ doublePointPreimage (⇑D) D.domain = ∅)
    (hΔdom : Δ.domain = E') (hΔinj : InjOn (⇑Δ) E')
    (hΔside : ⇑Δ '' E' ⊆ interior (C \ BdM)) (hΔbd : EqOn (⇑Δ) (⇑D) (frontier E'))
    (hΔmeet : ⇑Δ '' E' ∩ ⇑D '' D.domain = ⇑D '' frontier E')
    {Θ : Type v} [TopologicalSpace Θ] {Y : Type w} {ρ : M → Y} {γ : Θ → Y}
    (e : Θ ≃ₜ frontier D.domain) (hloop : ∀ θ, ρ (⇑D (e θ)) = γ θ) :
    ∃ Sg : hD.DescendingSurgery, MapsTo (⇑Sg.cell) Sg.cell.domain C ∧
      (∀ z ∈ Set.range Sg.cell.boundary, B ∈ 𝓝[BdM] z) ∧
        ∃ e' : Θ ≃ₜ frontier Sg.cell.domain, ∀ θ, ρ (⇑Sg.cell (e' θ)) = γ θ := by
  sorry

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
      hfrontQ hclean hinj hE hfrontE hk hkT hkcompat hdisjoint isOpen_interior hQV Subset.rfl
  exact hD.exists_descendingSurgery_of_adaptedCleanCap hc hJ hT hJT hpre hQ hQsub hfrontQ
    hclean hinj hE hfrontE hk hkT hkcompat hdisjoint hside hbuffer Δ hE' hEE' hE'int hQE'
    hE'clean hΔdom hΔinj hΔside hΔbd hΔmeet e hloop

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
    (htubeBdM : T.chart '' spliceCylinder ∩ BdM = T.chart '' spliceEndDisks)
    {G : SingularTwoCell M} (hG : hD.IsCrossRegluedCell c G) :
    Nonempty (PLCrossSeamReading T.chart G) ∨
      Nonempty (PLCrossSeamReading (T.chart ∘ crossQuarterTurn) G) := by
  sorry

theorem nonempty_plSeamTubeChart_comp_crossQuarterTurn
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {chart : (ℝ × ℝ) × ℝ → M} (C : PLSeamTubeChart M chart) :
    Nonempty (PLSeamTubeChart M (chart ∘ crossQuarterTurn)) := by
  sorry

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
