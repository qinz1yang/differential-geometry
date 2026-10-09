import DifferentialGeometry.Topology.LoopSpace.Regular



noncomputable section

open Function ContinuousMap Manifold
open scoped Topology ContDiff

namespace DifferentialGeometry.Topology


abbrev regularContractibleLoop (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] :=
  {γ : regularLoop E M // γ.val.Nullhomotopic}

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]


@[instance_reducible] def regularContractibleLoopTopology (e : M → F)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e) : TopologicalSpace (regularContractibleLoop E M) :=
  TopologicalSpace.induced Subtype.val (regularLoopTopology e he)


def regularContractibleLoopInclusion (γ : regularContractibleLoop E M) : contractibleLoop M :=
  ⟨γ.val.val, γ.property⟩



theorem continuous_regularContractibleLoopInclusion (e : M → F)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e) (hemb : _root_.Topology.IsEmbedding e) :
    Continuous[regularContractibleLoopTopology e he, inferInstance]
      (regularContractibleLoopInclusion (E := E) (M := M)) := by
  let : TopologicalSpace (regularLoop E M) := regularLoopTopology e he
  let : TopologicalSpace (regularContractibleLoop E M) := regularContractibleLoopTopology e he
  have hval : Continuous (fun γ : regularContractibleLoop E M => γ.val) := continuous_induced_dom
  exact ((continuous_regularLoop_inclusion e he hemb).comp hval).subtype_mk _



theorem continuous_regularContractibleLoop_iff {K : Type*} [TopologicalSpace K]
    (e : M → F) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e)
    (Γ : K → regularContractibleLoop E M) :
    Continuous[inferInstance, regularContractibleLoopTopology e he] Γ ↔
      Continuous[inferInstance, regularLoopTopology e he] (fun k => (Γ k).val) :=
  continuous_induced_rng


def regularContractibleLoopConst (q : M) : regularContractibleLoop E M :=
  ⟨⟨.const loopCircle q, contMDiff_const⟩, nullhomotopic_of_constant q⟩


theorem continuous_regularContractibleLoopConst (e : M → F)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e) :
    Continuous[inferInstance, regularContractibleLoopTopology e he]
      (regularContractibleLoopConst (E := E) (M := M)) := by
  apply (continuous_regularContractibleLoop_iff e he _).mpr
  apply (continuous_regularLoop_iff e he _).mpr
  constructor
  · exact he.continuous.comp continuous_fst
  · simp only [regularContractibleLoopConst, ContinuousMap.const_apply, deriv_const]
    exact continuous_const

end DifferentialGeometry.Topology
