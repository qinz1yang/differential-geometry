import DifferentialGeometry.Topology.GroupAction.Hom
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.MulAction

namespace MulActionHom

variable {M N X Y R : Type*} [SMul M X] {φ : M → N} [TopologicalSpace Y]

instance instContinuousAdd [AddMonoid Y] [DistribSMul N Y] [ContinuousAdd Y] :
    ContinuousAdd (X →ₑ[φ] Y) where
  continuous_add := continuous_iff.mpr (fun x =>
    ((continuous_eval x).comp continuous_fst).add ((continuous_eval x).comp continuous_snd))

instance instContinuousNeg [AddGroup Y] [DistribSMul N Y] [ContinuousNeg Y] :
    ContinuousNeg (X →ₑ[φ] Y) where
  continuous_neg := continuous_iff.mpr (fun x => (continuous_eval x).neg)

instance instIsTopologicalAddGroup [AddGroup Y] [DistribSMul N Y] [IsTopologicalAddGroup Y] :
    IsTopologicalAddGroup (X →ₑ[φ] Y) where

instance instContinuousSMul [TopologicalSpace R] [SMul N Y] [SMul R Y]
    [SMulCommClass N R Y] [ContinuousSMul R Y] : ContinuousSMul R (X →ₑ[φ] Y) where
  continuous_smul := continuous_iff.mpr (fun x =>
    continuous_fst.smul ((continuous_eval x).comp continuous_snd))

end MulActionHom
