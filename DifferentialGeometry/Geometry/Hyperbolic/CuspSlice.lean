/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Hyperbolic.CuspMetric
import DifferentialGeometry.Topology.FundamentalGroup.Product.Slice
import DifferentialGeometry.Topology.ThreeManifold.TorusCut.TorusCylinder
import Mathlib.Analysis.Convex.Contractible

set_option autoImplicit false
noncomputable section

open DifferentialGeometry GC.Endpoint
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Hyperbolic

def cuspSlice (r : EuclideanHalfSpace 1) : C(Torus, CuspHalfSpace) :=
  (ContinuousMap.id Torus).prodMk (ContinuousMap.const Torus r)

@[simp] theorem cuspSlice_apply (r : EuclideanHalfSpace 1) (x : Torus) :
    cuspSlice r x = (x, r) := rfl

theorem cuspSlice_contMDiff (r : EuclideanHalfSpace 1) :
    ContMDiff torusModel halfCollarModel ∞ (cuspSlice r) :=
  contMDiff_id.prodMk contMDiff_const

theorem cuspSlice_isEmbedding (r : EuclideanHalfSpace 1) :
    _root_.Topology.IsEmbedding (cuspSlice r) :=
  _root_.isEmbedding_prodMkLeft r

theorem cuspSlice_fundamentalGroup_bijective (r : EuclideanHalfSpace 1) (x : Torus) :
    Function.Bijective (FundamentalGroup.map (cuspSlice r) x) := by
  let : ContractibleSpace (EuclideanHalfSpace 1) :=
    EuclideanHalfSpace.convex.contractibleSpace ⟨0, by simp⟩
  exact DifferentialGeometry.Topology.bijective_fundamentalGroup_map_prodMk_const x r

def cuspFundamentalGroupEquiv (r : EuclideanHalfSpace 1) :
    FundamentalGroup CuspHalfSpace ((1, 1), r) ≃* Multiplicative ℤ × Multiplicative ℤ :=
  (MulEquiv.ofBijective (FundamentalGroup.map (cuspSlice r) (1, 1))
    (cuspSlice_fundamentalGroup_bijective r (1, 1))).symm.trans
      GC.Topology.torusFundamentalGroup

theorem cuspFundamentalGroupEquiv_map (r : EuclideanHalfSpace 1)
    (a : FundamentalGroup Torus (1, 1)) :
    cuspFundamentalGroupEquiv r (FundamentalGroup.map (cuspSlice r) (1, 1) a) =
      GC.Topology.torusFundamentalGroup a := by
  exact congrArg GC.Topology.torusFundamentalGroup
    ((MulEquiv.ofBijective (FundamentalGroup.map (cuspSlice r) (1, 1))
      (cuspSlice_fundamentalGroup_bijective r (1, 1))).symm_apply_apply a)

theorem cuspFundamentalGroupEquiv_symm (r : EuclideanHalfSpace 1)
    (a : Multiplicative ℤ × Multiplicative ℤ) :
    (cuspFundamentalGroupEquiv r).symm a =
      FundamentalGroup.map (cuspSlice r) (1, 1) (GC.Topology.torusFundamentalGroup.symm a) := by
  apply (cuspFundamentalGroupEquiv r).injective
  rw [MulEquiv.apply_symm_apply, cuspFundamentalGroupEquiv_map,
    MulEquiv.apply_symm_apply]

theorem HyperbolicCusp.sliceMetric (H : HyperbolicCusp) (r : EuclideanHalfSpace 1) :
    H.metric.sliceFst r = scaleMetric (Real.exp (-r.val 0)) (Real.exp_pos _) H.torusMetric := by
  rw [H.metric_eq_exponentialWarpedEnd,
    SmoothRiemannianMetric.exponentialWarpedEnd_sliceFst]
  norm_num

theorem HyperbolicCusp.cuspSlice_inner (H : HyperbolicCusp)
    (r : EuclideanHalfSpace 1) (x : Torus) (v w : TangentSpace torusModel x) :
    H.metric.inner (cuspSlice r x)
      (mfderiv torusModel halfCollarModel (cuspSlice r) x v)
      (mfderiv torusModel halfCollarModel (cuspSlice r) x w) =
        Real.exp (-r.val 0) * H.torusMetric.inner x v w := by
  change H.metric.inner (x, r)
    (mfderiv torusModel halfCollarModel (fun z : Torus => (z, r)) x v)
    (mfderiv torusModel halfCollarModel (fun z : Torus => (z, r)) x w) = _
  rw [mfderiv_prod_left, H.metric_formula]
  change (0 : ℝ) * 0 + Real.exp (-r.val 0) * H.torusMetric.inner x v w = _
  simp

end DifferentialGeometry.Geometry.Hyperbolic
