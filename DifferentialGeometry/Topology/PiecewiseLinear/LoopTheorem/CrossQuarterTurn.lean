/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CylinderSplice
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceTubeRestriction
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamResolvedCell

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

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

def crossQuarterTurnLinear : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] ((ℝ × ℝ) × ℝ) where
  toFun := crossQuarterTurn
  map_add' p q := by
    rcases p with ⟨⟨p1, p2⟩, p3⟩
    rcases q with ⟨⟨q1, q2⟩, q3⟩
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · change -(p2 + q2) = -p2 + -q2
      ring
    · change p1 + q1 = p1 + q1
      rfl
    · change p3 + q3 = p3 + q3
      rfl
  map_smul' c p := by
    rcases p with ⟨⟨p1, p2⟩, p3⟩
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · change -(c * p2) = c * -p2
      ring
    · change c * p1 = c * p1
      rfl
    · change c * p3 = c * p3
      rfl

theorem isPiecewiseAffineOn_crossQuarterTurn :
    IsPiecewiseAffineOn crossQuarterTurn spliceCylinder :=
  (isPiecewiseAffineOn_of_affine_of_isHPolytope
    crossQuarterTurnLinear.toAffineMap isHPolytope_spliceCylinder).congr
    fun _ _ => rfl

theorem isPLHomeomorphOn_crossQuarterTurn_spliceCylinder :
    IsPLHomeomorphOn crossQuarterTurn spliceCylinder spliceCylinder := by
  have hbij : BijOn crossQuarterTurn spliceCylinder spliceCylinder := by
    have h := injective_crossQuarterTurn.injOn.bijOn_image (s := spliceCylinder)
    rwa [image_crossQuarterTurn_spliceCylinder] at h
  refine ⟨hbij, isPiecewiseAffineOn_crossQuarterTurn, ?_⟩
  let L3 := crossQuarterTurnLinear.comp (crossQuarterTurnLinear.comp crossQuarterTurnLinear)
  have hPA : IsPiecewiseAffineOn L3.toAffineMap spliceCylinder :=
    isPiecewiseAffineOn_of_affine_of_isHPolytope L3.toAffineMap isHPolytope_spliceCylinder
  refine hPA.congr fun y hy => ?_
  apply injective_crossQuarterTurn
  rw [hbij.invOn_invFunOn.2 hy]
  change y = crossQuarterTurn (crossQuarterTurn (crossQuarterTurn (crossQuarterTurn y)))
  rw [crossQuarterTurn_iterate_four]

theorem nonempty_plSeamTubeChart_comp_crossQuarterTurn
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {chart : (ℝ × ℝ) × ℝ → M} (C : PLSeamTubeChart M chart) :
    Nonempty (PLSeamTubeChart M (chart ∘ crossQuarterTurn)) := by
  have hPL : IsPLHomeomorphOn crossQuarterTurn spliceCylinder
      (crossQuarterTurn '' spliceCylinder) := by
    rw [image_crossQuarterTurn_spliceCylinder]
    exact isPLHomeomorphOn_crossQuarterTurn_spliceCylinder
  exact PLSeamTubeChart.nonempty_precomp C hPL mapsTo_crossQuarterTurn_spliceCylinder

end DifferentialGeometry.Topology.PiecewiseLinear
