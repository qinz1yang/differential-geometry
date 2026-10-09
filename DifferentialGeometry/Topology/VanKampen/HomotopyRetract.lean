import Mathlib.Topology.Homotopy.Equiv
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

noncomputable section

open scoped ContinuousMap

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

def homotopyEquivOfRetraction {K U : Type*} [TopologicalSpace K] [TopologicalSpace U]
    (i : C(K, U)) (r : C(U, K)) (hri : r.comp i = ContinuousMap.id K)
    (hh : (i.comp r).Homotopic (ContinuousMap.id U)) : K ≃ₕ U where
  toFun := i
  invFun := r
  left_inv := by simpa only [hri] using ContinuousMap.Homotopic.refl (ContinuousMap.id K)
  right_inv := hh

theorem simplyConnectedSpace_iff_of_homotopyRetract {K U : Type*} [TopologicalSpace K]
    [TopologicalSpace U] (i : C(K, U)) (r : C(U, K))
    (hri : r.comp i = ContinuousMap.id K)
    (hh : (i.comp r).Homotopic (ContinuousMap.id U)) :
    SimplyConnectedSpace K ↔ SimplyConnectedSpace U :=
  (homotopyEquivOfRetraction i r hri hh).simplyConnectedSpace_iff

theorem simplyConnectedSpace_of_homotopyRetract {K U : Type*} [TopologicalSpace K]
    [TopologicalSpace U] (i : C(K, U)) (r : C(U, K))
    (hri : r.comp i = ContinuousMap.id K)
    (hh : (i.comp r).Homotopic (ContinuousMap.id U)) [SimplyConnectedSpace K] :
    SimplyConnectedSpace U :=
  (simplyConnectedSpace_iff_of_homotopyRetract i r hri hh).mp ‹_›

theorem simplyConnectedSpace_of_homotopySection {K U : Type*} [TopologicalSpace K]
    [TopologicalSpace U] (i : C(K, U)) (r : C(U, K))
    (hri : r.comp i = ContinuousMap.id K)
    (hh : (i.comp r).Homotopic (ContinuousMap.id U)) [SimplyConnectedSpace U] :
    SimplyConnectedSpace K :=
  (simplyConnectedSpace_iff_of_homotopyRetract i r hri hh).mpr ‹_›

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
