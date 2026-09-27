/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.VanKampen.CellAttachmentFundamentalGroup
import DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainRimCircle

open scoped ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem surjective_fundamentalGroup_map_comp_of_surjective_comp
    {A B C Z : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] [TopologicalSpace Z] [PathConnectedSpace B]
    (a : C(A, B)) (g : C(C, B)) (f : C(B, Z)) (x : A) (y : C)
    (hfa : Function.Surjective (FundamentalGroup.map (f.comp a) x))
    (hg : Function.Surjective (FundamentalGroup.map g y)) :
    Function.Surjective (FundamentalGroup.map (f.comp g) y) := by
  have hbase : Function.Surjective (FundamentalGroup.map f (a x)) := by
    intro z
    obtain ⟨w, hw⟩ := hfa z
    refine ⟨FundamentalGroup.map a x w, ?_⟩
    change Path.Homotopic.Quotient.map w (f.comp a) = z at hw
    rw [Path.Homotopic.Quotient.map_comp] at hw
    exact hw
  let p := PathConnectedSpace.somePath (g y) (a x)
  let eB := FundamentalGroup.fundamentalGroupMulEquivOfPath p
  let eZ := FundamentalGroup.fundamentalGroupMulEquivOfPath (p.map f.continuous)
  have hbase' : Function.Surjective (FundamentalGroup.map f (g y)) := by
    intro z
    obtain ⟨w, hw⟩ := hbase (eZ z)
    refine ⟨eB.symm w, eZ.injective ?_⟩
    rw [DifferentialGeometry.Topology.fundamentalGroup_map_changeBasepoint]
    simpa only [eB, MulEquiv.apply_symm_apply] using hw
  intro z
  obtain ⟨w, hw⟩ := hbase' z
  obtain ⟨v, hv⟩ := hg w
  refine ⟨v, ?_⟩
  change Path.Homotopic.Quotient.map v (f.comp g) = z
  rw [Path.Homotopic.Quotient.map_comp]
  change FundamentalGroup.map f (g y) (FundamentalGroup.map g y v) = z
  rw [hv, hw]

theorem surjective_of_fundamentalGroup_map_surjective_to_homeomorphic_circle
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : Y ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
    (f : C(X, Y)) (x : X) (h : Function.Surjective (FundamentalGroup.map f x)) :
    Function.Surjective f := by
  let a : C(Y, Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := ⟨e, e.continuous⟩
  have ha : Function.Surjective (FundamentalGroup.map a (f x)) := by
    intro z
    obtain ⟨w, hw⟩ := (fundamentalGroup_mapOfEq_bijective_of_homotopyEquiv
      e.toHomotopyEquiv (f x) (e (f x)) rfl).2 z
    refine ⟨w, ?_⟩
    have hv := FundamentalGroup.mapOfEq_apply e.toHomotopyEquiv.toFun rfl w
    rw [Path.Homotopic.Quotient.cast_rfl_rfl] at hv
    exact hv.symm.trans hw
  have hcomp : Function.Surjective (FundamentalGroup.map (a.comp f) x) := by
    intro z
    obtain ⟨w, hw⟩ := ha z
    obtain ⟨v, hv⟩ := h w
    refine ⟨v, ?_⟩
    change Path.Homotopic.Quotient.map v (a.comp f) = z
    rw [Path.Homotopic.Quotient.map_comp]
    change FundamentalGroup.map a (f x) (FundamentalGroup.map f x v) = z
    rw [hv, hw]
  intro y
  obtain ⟨z, hz⟩ := surjective_of_fundamentalGroup_map_surjective_to_circle
    (a.comp f) x hcomp (e y)
  exact ⟨z, e.injective hz⟩

end DifferentialGeometry.Topology.PiecewiseLinear
