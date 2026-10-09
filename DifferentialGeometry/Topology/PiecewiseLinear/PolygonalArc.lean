/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedra
import DifferentialGeometry.External.Schoenflies.PolyLocal
import DifferentialGeometry.External.Schoenflies.MatchedArc

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPolyhedron.isLocallyPolyConnected {P : Set (EuclideanSpace ℝ (Fin 2))}
    (hP : IsPolyhedron P) : Schoenflies.IsLocallyPolyConnected P := by
  obtain ⟨ι, hι, C, hC, rfl⟩ := hP
  let _ : Finite ι := hι
  apply Schoenflies.IsLocallyPolyConn.isLocallyPolyConnected
  intro p hp
  let U := (⋃ i : {i // p ∉ C i}, C i.1)ᶜ
  have hU : IsOpen U := (isClosed_iUnion_of_finite fun i : {i // p ∉ C i} => (hC
      i.1).isClosed).isOpen_compl
  have hpU : p ∈ U := by
    intro hp'
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp'
    exact i.2 hi
  refine Schoenflies.isLocallyPolyConnAt_of_star (C := fun i : {i // p ∈ C i} => C i.1)
    hU hpU ?_ (fun i => subset_iUnion C i.1) (fun i => (hC i.1).convex) (fun i _ _ => i.2)
  intro x hx
  obtain ⟨i, hxi⟩ := mem_iUnion.mp hx.2
  have hpi : p ∈ C i := by
    by_contra hpi
    exact hx.1 (mem_iUnion.mpr ⟨⟨i, hpi⟩, hxi⟩)
  exact mem_iUnion.mpr ⟨⟨i, hpi⟩, hxi⟩

theorem IsPolyhedron.isPolygonal_of_isArcBetween
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : IsPolyhedron A)
    {p q : EuclideanSpace ℝ (Fin 2)} (harc : Schoenflies.IsArcBetween A p q) :
    Schoenflies.IsPolygonal A := by
  have hconn := harc.isArc.isConnected.isPreconnected
  have hpq : p ≠ q := by
    obtain ⟨f, _, hi, _, hf0, hf1⟩ := harc
    intro hpq
    exact zero_ne_one (hi Schoenflies.zero_mem_I Schoenflies.one_mem_I
      (hf0.trans (hpq.trans hf1.symm)))
  obtain ⟨vs, hvs, hsub, hhead, hlast⟩ :=
    (Schoenflies.PolyReaches.of_isPreconnected hA.isLocallyPolyConnected
      hconn harc.left_mem harc.right_mem).exists_poly
  obtain ⟨ws, _, _, _, hws, hwArc⟩ := Schoenflies.exists_simple_poly_of_isPolygonal
    (show Schoenflies.IsPolygonal (Schoenflies.poly vs) from ⟨vs, rfl⟩)
    (Schoenflies.isConnected_poly hvs).isPreconnected hpq
    (hhead ▸ Schoenflies.head_mem_poly hvs) (hlast ▸ Schoenflies.getLast_mem_poly hvs)
  exact ⟨ws, (harc.eq_of_subset hwArc (hws.trans hsub)).symm⟩

end DifferentialGeometry.Topology.PiecewiseLinear
