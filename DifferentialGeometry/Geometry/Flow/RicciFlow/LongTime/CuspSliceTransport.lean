/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Hyperbolic.CuspSlice
import DifferentialGeometry.Topology.FundamentalGroup.MarkedMapComposition
import Mathlib.Analysis.Convex.PathConnected

set_option autoImplicit false
noncomputable section
open DifferentialGeometry GC.Endpoint

namespace GC.LongTime
open DifferentialGeometry.Geometry.Hyperbolic GC.Topology
open scoped ContinuousMap

def cuspHeightPath (r s : EuclideanHalfSpace 1) : Path r s where
  toFun t := ⟨Path.segment r.val s.val t,
    EuclideanHalfSpace.convex.segment_subset r.property s.property (by
      rw [← Path.range_segment]
      exact Set.mem_range_self t)⟩
  continuous_toFun := (Path.segment r.val s.val).continuous.subtype_mk _
  source' := Subtype.ext (Path.segment r.val s.val).source
  target' := Subtype.ext (Path.segment r.val s.val).target

theorem cuspHeightPath_apply (r s : EuclideanHalfSpace 1) (t : unitInterval) :
    (cuspHeightPath r s t).val = (1 - (t : ℝ)) • r.val + (t : ℝ) • s.val := by
  change Path.segment r.val s.val t = _
  rw [Path.segment_apply, AffineMap.lineMap_apply_module]

def cuspSliceHomotopy (r s : EuclideanHalfSpace 1) :
    (cuspSlice r).Homotopy (cuspSlice s) where
  toFun p := (p.2, cuspHeightPath r s p.1)
  continuous_toFun := continuous_snd.prodMk
    ((cuspHeightPath r s).continuous.comp continuous_fst)
  map_zero_left x := by simp [cuspSlice]
  map_one_left x := by simp [cuspSlice]

theorem cuspSliceHomotopy_evalAt (r s : EuclideanHalfSpace 1)
    (x : GC.Endpoint.Torus) (t : unitInterval) :
    (cuspSliceHomotopy r s).evalAt x t = (x, cuspHeightPath r s t) := rfl

theorem cuspSlice_markedMap_comp {X : Type*} [TopologicalSpace X]
    (j : C(CuspHalfSpace, X)) (r s : EuclideanHalfSpace 1)
    (x : GC.Endpoint.Torus) (y : X) (α : Path y (j (cuspSlice r x))) :
    markedMap (j.comp (cuspSlice s)) x
      (α.trans (((ContinuousMap.Homotopy.refl j).comp
        (cuspSliceHomotopy r s)).evalAt x)) =
      markedMap (j.comp (cuspSlice r)) x α :=
  markedMap_homotopy_track _ _
    ((ContinuousMap.Homotopy.refl j).comp (cuspSliceHomotopy r s)) x α

theorem cuspSlice_kernel_comp {X : Type*} [TopologicalSpace X]
    (j : C(CuspHalfSpace, X)) (r s : EuclideanHalfSpace 1) (x : GC.Endpoint.Torus) :
    (FundamentalGroup.map (j.comp (cuspSlice r)) x).ker =
      (FundamentalGroup.map (j.comp (cuspSlice s)) x).ker :=
  homotopic_kernel _ _
    ((ContinuousMap.Homotopy.refl j).comp (cuspSliceHomotopy r s)) x

theorem cuspFundamentalGroupEquiv_changeBasepoint (r s : EuclideanHalfSpace 1)
    (a : FundamentalGroup CuspHalfSpace ((1, 1), s)) :
    cuspFundamentalGroupEquiv r
      (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint
        ((cuspSliceHomotopy r s).evalAt (1, 1)) a) =
      cuspFundamentalGroupEquiv s a := by
  obtain ⟨b, rfl⟩ := (cuspSlice_fundamentalGroup_bijective s (1, 1)).surjective a
  have ht := congrArg (fun k => k b)
    (homotopy_track (cuspSlice r) (cuspSlice s) (cuspSliceHomotopy r s) (1, 1))
  change DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint
    ((cuspSliceHomotopy r s).evalAt (1, 1))
      (FundamentalGroup.map (cuspSlice s) (1, 1) b) =
      FundamentalGroup.map (cuspSlice r) (1, 1) b at ht
  rw [ht, cuspFundamentalGroupEquiv_map, cuspFundamentalGroupEquiv_map]

end GC.LongTime
