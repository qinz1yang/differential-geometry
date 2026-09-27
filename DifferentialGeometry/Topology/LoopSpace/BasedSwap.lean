import DifferentialGeometry.Topology.LoopSpace.FreeAdjunction



noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {N X : Type*} [TopologicalSpace X]



def genLoopBasedCircleHomeomorph (x : X) :
    GenLoop N (basedCircleLoop x) (basedCircleConstant x) ≃ₜ
      basedCircleLoop (GenLoop.const : GenLoop N X x) where
  toFun p := ⟨genLoopFreeLoopHomeomorph x
    (genLoopBasedMap (basedCircleInclusion x) (basedCircleConstant x)
      (FreeLoop.constants x) rfl p), genLoopFreeLoopHomeomorph_inclusion_zero x p⟩
  invFun γ := ⟨⟨fun t => ⟨(genLoopFreeLoopHomeomorph x).symm γ.val t,
      congrArg (fun p : GenLoop N X x => p t) γ.property⟩,
      ((genLoopFreeLoopHomeomorph x).symm γ.val).val.continuous.subtype_mk _⟩,
    fun t ht => by
      apply Subtype.ext
      exact GenLoop.boundary ((genLoopFreeLoopHomeomorph x).symm γ.val) t ht⟩
  left_inv p := by ext t θ; rfl
  right_inv γ := by ext θ t; rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (genLoopFreeLoopHomeomorph x).continuous.comp
    exact ((continuous_postcomp (basedCircleInclusion x)).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_of_continuous_uncurry
    apply Continuous.subtype_mk
    change Continuous (fun z : basedCircleLoop (GenLoop.const : GenLoop N X x) ×
      (N → unitInterval) => (genLoopFreeLoopHomeomorph x).symm z.1.val |>.val z.2)
    exact continuous_eval.comp
      ((continuous_subtype_val.comp
        ((genLoopFreeLoopHomeomorph x).symm.continuous.comp
          (continuous_subtype_val.comp continuous_fst))).prodMk continuous_snd)


theorem genLoopBasedCircleHomeomorph_apply (x : X)
    (p : GenLoop N (basedCircleLoop x) (basedCircleConstant x))
    (θ : loopCircle) (t : N → unitInterval) :
    (genLoopBasedCircleHomeomorph x p).val θ t = (p t).val θ := rfl

end DifferentialGeometry.Topology
