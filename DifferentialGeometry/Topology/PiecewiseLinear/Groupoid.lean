/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PiecewiseAffine
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.HasGroupoid

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable (n : ℕ)

def plPregroupoid : Pregroupoid (EuclideanSpace ℝ (Fin n)) where
  property f u := IsPiecewiseAffineOn f u
  comp hf hg _ _ _ := hg.comp hf
  id_mem := isPiecewiseAffineOn_id isOpen_univ
  locality _ h := isPiecewiseAffineOn_of_locally h
  congr _ hfg hf := hf.congr fun x hx => hfg x hx

def plGroupoid : StructureGroupoid (EuclideanSpace ℝ (Fin n)) := (plPregroupoid n).groupoid

variable {n}

theorem mem_plGroupoid_iff
    {e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))} :
    e ∈ plGroupoid n ↔ IsPiecewiseAffineOn e e.source ∧ IsPiecewiseAffineOn e.symm e.target :=
  mem_groupoid_of_pregroupoid

theorem mem_plGroupoid_of_isPiecewiseAffineOn
    {e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))}
    (he : IsPiecewiseAffineOn e e.source) : e ∈ plGroupoid n :=
  mem_plGroupoid_iff.mpr ⟨he, he.symm⟩

theorem ofSet_mem_plGroupoid {s : Set (EuclideanSpace ℝ (Fin n))} (hs : IsOpen s) :
    OpenPartialHomeomorph.ofSet s hs ∈ plGroupoid n :=
  mem_plGroupoid_of_isPiecewiseAffineOn (isPiecewiseAffineOn_id hs)

instance : ClosedUnderRestriction (plGroupoid n) :=
  (closedUnderRestriction_iff_id_le _).mpr <| by
    rw [StructureGroupoid.le_iff]
    rintro e ⟨s, hs, hes⟩
    exact (plGroupoid n).mem_of_eqOnSource (ofSet_mem_plGroupoid hs) hes

end DifferentialGeometry.Topology.PiecewiseLinear
