import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section

open Filter Set MeasureTheory
open scoped Topology

namespace MeasureTheory

variable {X Y ι : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] {μ : Measure X} [μ.IsOpenPosMeasure]
  [UniformSpace Y] {l : Filter ι} {F : ι → X → Y} {f : X → Y}

theorem tendstoUniformly_of_ae_tendsto_of_equicontinuous
    (hF : Equicontinuous F) (hf : Continuous f)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) l (𝓝 (f x))) :
    TendstoUniformly F f l := by
  have hclosed : IsClosed {x | Tendsto (fun i => F i x) l (𝓝 (f x))} :=
    hF.isClosed_setOfPred_tendsto hf
  have hdense : Dense {x | Tendsto (fun i => F i x) l (𝓝 (f x))} := Measure.dense_of_ae hae
  have hall : ∀ x, Tendsto (fun i => F i x) l (𝓝 (f x)) := by
    intro x
    exact hclosed.closure_subset (hdense x)
  have hpi : Tendsto F l (𝓝 f) := tendsto_pi_nhds.mpr hall
  exact UniformFun.tendsto_iff_tendstoUniformly.mp
    ((hF.tendsto_uniformFun_iff_pi l f).mpr hpi)

end MeasureTheory

end
