import Mathlib.Topology.Maps.Proper.Basic

open scoped Topology

namespace Topology

variable {T X Y : Type*} [TopologicalSpace T] [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [T2Space Y] {e : T × X → Y}

theorem isProperMap_parametric_graph (he : Continuous e) :
    IsProperMap (fun q : T × X => (q.1, e q)) := by
  rw [isProperMap_iff_ultrafilter]
  refine ⟨continuous_fst.prodMk he, ?_⟩
  intro 𝒰 p hp
  have ht : Filter.Tendsto (Prod.fst : T × X → T) 𝒰 (𝓝 p.1) :=
    (continuous_fst.tendsto p).comp hp
  obtain ⟨q, hqt, hq⟩ :=
    isProperMap_fst_of_compactSpace.ultrafilter_le_nhds_of_tendsto ht
  have hqe : e q = p.2 :=
    tendsto_nhds_unique ((he.tendsto q).mono_left hq)
      ((continuous_snd.tendsto p).comp hp)
  exact ⟨q, Prod.ext hqt hqe, hq⟩

theorem isClosedEmbedding_parametric_graph (he : Continuous e)
    (hinj : ∀ t, Function.Injective (fun x => e (t, x))) :
    IsClosedEmbedding (fun q : T × X => (q.1, e q)) := by
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_fst.prodMk he) _ (isProperMap_parametric_graph he).isClosedMap
  rintro ⟨t, x⟩ ⟨s, y⟩ h
  have hts : t = s := congrArg Prod.fst h
  subst s
  exact Prod.ext rfl (hinj t (congrArg Prod.snd h))

end Topology
