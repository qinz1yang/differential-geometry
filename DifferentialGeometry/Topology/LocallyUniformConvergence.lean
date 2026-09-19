import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.UniformSpace.Pi

set_option autoImplicit false
open Filter Set
open scoped Topology

theorem TendstoLocallyUniformlyOn.comp_of_continuousAt
    {α β γ ι : Type*} [TopologicalSpace α] [UniformSpace β] [UniformSpace γ]
    {F : ι → α → β} {f : α → β} {l : Filter ι} {s : Set α}
    (hF : TendstoLocallyUniformlyOn F f l s) (hf : ContinuousOn f s)
    {g : β → γ} (hg : ∀ x ∈ s, ContinuousAt g (f x)) :
    TendstoLocallyUniformlyOn (fun i x => g (F i x)) (g ∘ f) l s := by
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto] at hF ⊢
  intro x hx
  have hlim : Tendsto (fun z : ι × α => f z.2) (l ×ˢ 𝓝[s] x) (𝓝 (f x)) :=
    (show Tendsto f (𝓝[s] x) (𝓝 (f x)) from hf x hx).comp tendsto_snd
  have hseq : Tendsto (fun z : ι × α => F z.1 z.2) (l ×ˢ 𝓝[s] x) (𝓝 (f x)) :=
    hlim.congr_uniformity (hF x hx)
  exact (((hg x hx).tendsto.comp hlim).prodMk_nhds
    ((hg x hx).tendsto.comp hseq)).mono_right (nhds_le_uniformity _)

theorem tendstoLocallyUniformlyOn_pi
    {α ι κ : Type*} {β : κ → Type*} [TopologicalSpace α] [∀ k, UniformSpace (β k)]
    {F : ι → α → ∀ k, β k} {f : α → ∀ k, β k} {l : Filter ι} {s : Set α} :
    TendstoLocallyUniformlyOn F f l s ↔
      ∀ k, TendstoLocallyUniformlyOn (fun i x => F i x k) (fun x => f x k) l s := by
  simp only [tendstoLocallyUniformlyOn_iff_forall_tendsto, Pi.uniformity,
    tendsto_iInf, tendsto_comap_iff, Function.comp_def]
  exact ⟨fun h k x hx => h x hx k, fun h x hx k => h k x hx⟩

theorem ContinuousOn.tendstoLocallyUniformlyOn
    {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [UniformSpace γ]
    {s : Set α} {u : Set β} {F : α → β → γ} {a : α}
    (hF : ContinuousOn (fun z : α × β => F z.1 z.2) (s ×ˢ u)) (ha : a ∈ s) :
    TendstoLocallyUniformlyOn F (F a) (𝓝[s] a) u := by
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto]
  intro x hx
  have hsource : Tendsto (fun z : α × β => F z.1 z.2)
      ((𝓝[s] a) ×ˢ 𝓝[u] x) (𝓝 (F a x)) := by
    rw [← nhdsWithin_prod_eq]
    exact hF (a, x) ⟨ha, hx⟩
  have htarget : Tendsto (fun z : α × β => F a z.2)
      ((𝓝[s] a) ×ˢ 𝓝[u] x) (𝓝 (F a x)) := by
    have hc : ContinuousOn (F a) u := hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun y hy => ⟨ha, hy⟩)
    exact (show Tendsto (F a) (𝓝[u] x) (𝓝 (F a x)) from hc x hx).comp tendsto_snd
  exact (htarget.prodMk_nhds hsource).mono_right (nhds_le_uniformity _)

theorem TendstoLocallyUniformlyOn.mono_left
    {α β ι : Type*} [TopologicalSpace α] [UniformSpace β]
    {F : ι → α → β} {f : α → β} {l l' : Filter ι} {s : Set α}
    (hF : TendstoLocallyUniformlyOn F f l s) (hle : l' ≤ l) :
    TendstoLocallyUniformlyOn F f l' s := by
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto] at hF ⊢
  exact fun x hx => (hF x hx).mono_left (Filter.prod_mono hle le_rfl)
