import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformConvergence


open Filter Set

theorem TendstoUniformlyOn.comp_continuousAt_of_isCompact_image
    {A E F N : Type*} [UniformSpace E] [UniformSpace F]
    {K : Set A} {X : N → A → E} {v : A → E} {l : Filter N}
    (hX : TendstoUniformlyOn X v l K) (hK : IsCompact (v '' K))
    {g : E → F} (hg : ∀ y ∈ v '' K, ContinuousAt g y) :
    TendstoUniformlyOn (fun n x => g (X n x)) (fun x => g (v x)) l K := by
  intro V hV
  filter_upwards [hX _ (hK.uniformContinuousAt_of_continuousAt g hg hV)] with n hn x hx
  exact (hn x hx) (mem_image_of_mem v hx)
