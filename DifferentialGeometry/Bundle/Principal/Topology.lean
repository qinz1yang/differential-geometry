import DifferentialGeometry.Bundle.Principal.Defs
import Mathlib.Topology.Algebra.Monoid

open Bundle Filter
open scoped Topology

namespace Bundle.IsPrincipalBundle

variable {G B : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] [TopologicalSpace B]
  {P : B → Type*} [∀ x, Torsor G (P x)] [∀ x, TopologicalSpace (P x)]
  [TopologicalSpace (TotalSpace G P)] [FiberBundle G P] [IsPrincipalBundle P]

theorem continuous_totalSpace_smul :
    Continuous (fun q : G × TotalSpace G P =>
      (⟨q.2.proj, q.1 • q.2.snd⟩ : TotalSpace G P)) := by
  apply continuous_iff_continuousAt.mpr
  intro q₀
  rw [FiberBundle.continuousAt_totalSpace]
  have hb : Continuous (fun q : G × TotalSpace G P => q.2.proj) :=
    (FiberBundle.continuous_proj G P).comp continuous_snd
  refine ⟨hb.continuousAt, ?_⟩
  let e := trivializationAt G P q₀.2.proj
  have he : q₀.2.proj ∈ e.baseSet := mem_baseSet_trivializationAt G P q₀.2.proj
  have hc : ContinuousAt (fun q : G × TotalSpace G P => (e q.2).2) q₀ :=
    ((e.toOpenPartialHomeomorph.continuousAt (e.mem_source.mpr he)).comp
      continuous_snd.continuousAt).snd
  have hm := continuous_fst.continuousAt.mul hc
  apply hm.congr_of_eventuallyEq
  filter_upwards [hb.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds he)] with q hq
  exact e.apply_smul hq q.1 q.2.snd

end Bundle.IsPrincipalBundle
