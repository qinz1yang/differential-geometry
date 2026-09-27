import Mathlib.Topology.EMetricSpace.Lipschitz


open Set Topology

namespace LocallyLipschitzOn

variable {α β γ δ : Type*}
  [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  [PseudoEMetricSpace γ] [PseudoEMetricSpace δ]

theorem comp {s : Set α} {t : Set β} {f : β → γ} {g : α → β}
    (hf : LocallyLipschitzOn t f) (hg : LocallyLipschitzOn s g)
    (hgt : MapsTo g s t) : LocallyLipschitzOn s (f ∘ g) := by
  intro x hx
  obtain ⟨Kg, u, hu, hgu⟩ := hg hx
  obtain ⟨Kf, v, hv, hfv⟩ := hf (hgt hx)
  refine ⟨Kf * Kg, u ∩ g ⁻¹' v,
    Filter.inter_mem hu ((hg.continuousOn x hx).tendsto_nhdsWithin hgt hv), ?_⟩
  exact hfv.comp (hgu.mono inter_subset_left)
    ((mapsTo_preimage g v).mono_left inter_subset_right)

theorem prod_map {s : Set α} {t : Set β} {f : α → γ} {g : β → δ}
    (hf : LocallyLipschitzOn s f) (hg : LocallyLipschitzOn t g) :
    LocallyLipschitzOn (s ×ˢ t) (Prod.map f g) := by
  intro x hx
  obtain ⟨Kf, u, hu, hfu⟩ := hf hx.1
  obtain ⟨Kg, v, hv, hgv⟩ := hg hx.2
  refine ⟨max Kf Kg, u ×ˢ v,
    mem_nhdsWithin_prod_iff.mpr ⟨u, hu, v, hv, Subset.rfl⟩, ?_⟩
  have hf' : LipschitzOnWith Kf (fun z : α × β => f z.1) (u ×ˢ v) := by
    simpa only [mul_one, Function.comp_def] using
      hfu.comp LipschitzWith.prod_fst.lipschitzOnWith (fun _ hz => hz.1)
  have hg' : LipschitzOnWith Kg (fun z : α × β => g z.2) (u ×ˢ v) := by
    simpa only [mul_one, Function.comp_def] using
      hgv.comp LipschitzWith.prod_snd.lipschitzOnWith (fun _ hz => hz.2)
  exact hf'.prodMk hg'

end LocallyLipschitzOn
