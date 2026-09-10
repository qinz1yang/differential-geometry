import DifferentialGeometry.Topology.Manifold.ChartSupportedExtension

noncomputable section
open Set Filter Topology Manifold
open scoped ContDiff

namespace Poincare.Topology.Manifold

variable {E F P H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ F H}

private theorem mapsTo_of_injective_of_fix_compl {X : Type*} {f : X → X}
    (hf : Function.Injective f) {K U : Set X} (hKU : K ⊆ U)
    (hfix : ∀ x, x ∉ K → f x = x) : MapsTo f U U := by
  intro x hx
  by_contra hfx
  have he : f (f x) = f x := hfix _ (fun h ↦ hfx (hKU h))
  exact hfx ((hf he).symm ▸ hx)

theorem contMDiff_extendChartById_of_mapsTo [T2Space M]
    (e : OpenPartialHomeomorph M E)
    (he : ContMDiffOn I 𝓘(ℝ, E) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, E) I ∞ e.symm e.target)
    {f : P × E → E} (hf : ContDiff ℝ ∞ f)
    (hmap : ∀ p, MapsTo (fun z ↦ f (p, z)) e.target e.target)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ e.target)
    (hfix : ∀ p z, z ∉ K → f (p, z) = z) :
    ContMDiff (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M ↦ extendChartById e (fun z ↦ f (q.1, z)) q.2) := by
  have hKi : IsCompact (e.symm '' K) :=
    hK.image_of_continuousOn (hei.continuousOn.mono hKt)
  intro q
  by_cases hq : q.2 ∈ e.source
  · have hc : ContMDiffAt (𝓘(ℝ, P).prod I) 𝓘(ℝ, E) ∞
        (fun r : P × M ↦ e r.2) q :=
      (he.contMDiffAt (e.open_source.mem_nhds hq)).comp q contMDiffAt_snd
    have hi := hei.contMDiffAt (e.open_target.mem_nhds (hmap q.1 (e.map_source hq)))
    have hs := hi.comp q
      (hf.contMDiff.contMDiffAt.comp q (contMDiffAt_fst.prodMk_space hc))
    apply hs.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds hq)] with r hr
    exact if_pos hr
  · have hqK : q.2 ∉ e.symm '' K := by
      rintro ⟨z, hz, heq⟩
      exact hq (heq ▸ e.map_target (hKt hz))
    apply contMDiffAt_snd.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (hKi.isClosed.isOpen_compl.mem_nhds hqK)] with r hr
    exact extendChartById_eq_of_notMem_image e _ (hfix r.1) hr

omit [NormedSpace ℝ E] in
theorem leftInverse_extendChartById_of_mapsTo
    (e : OpenPartialHomeomorph M E) {f g : E → E}
    (hgf : Function.LeftInverse g f) (hf : MapsTo f e.target e.target) :
    Function.LeftInverse (extendChartById e g) (extendChartById e f) := by
  intro x
  by_cases hx : x ∈ e.source
  · have hfx := hf (e.map_source hx)
    rw [show extendChartById e f x = e.symm (f (e x)) from if_pos hx,
      show extendChartById e g (e.symm (f (e x))) =
        e.symm (g (e (e.symm (f (e x))))) from if_pos (e.map_target hfx),
      e.right_inv hfx, hgf, e.left_inv hx]
  · rw [show extendChartById e f x = x from if_neg hx]
    exact if_neg hx

theorem exists_diffeomorph_extension_of_partial_chart_family [T2Space M]
    (e : OpenPartialHomeomorph M E)
    (he : ContMDiffOn I 𝓘(ℝ, E) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, E) I ∞ e.symm e.target)
    (D : P → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    (hD : ContDiff ℝ ∞ (fun q : P × E ↦ D q.1 q.2))
    (hDi : ContDiff ℝ ∞ (fun q : P × E ↦ (D q.1).symm q.2))
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ e.target)
    (hfix : ∀ p z, z ∉ K → D p z = z ∧ (D p).symm z = z) :
    ∃ J : P → Diffeomorph I I M M ∞,
      ContMDiff (𝓘(ℝ, P).prod I) I ∞ (fun q : P × M ↦ J q.1 q.2) ∧
      ContMDiff (𝓘(ℝ, P).prod I) I ∞ (fun q : P × M ↦ (J q.1).symm q.2) ∧
      (∀ p x, J p x = extendChartById e (D p) x ∧
        (J p).symm x = extendChartById e (D p).symm x) ∧
      IsCompact (e.symm '' K) ∧ e.symm '' K ⊆ e.source ∧
      ∀ p x, x ∉ e.symm '' K → J p x = x ∧ (J p).symm x = x := by
  have hmap (p : P) : MapsTo (D p) e.target e.target :=
    mapsTo_of_injective_of_fix_compl (D p).injective hKt (fun z hz ↦ (hfix p z hz).1)
  have hmapi (p : P) : MapsTo (D p).symm e.target e.target :=
    mapsTo_of_injective_of_fix_compl (D p).symm.injective hKt (fun z hz ↦ (hfix p z hz).2)
  have hF := contMDiff_extendChartById_of_mapsTo e he hei hD hmap hK hKt
    (fun p z hz ↦ (hfix p z hz).1)
  have hG := contMDiff_extendChartById_of_mapsTo e he hei hDi hmapi hK hKt
    (fun p z hz ↦ (hfix p z hz).2)
  let J (p : P) : Diffeomorph I I M M ∞ :=
    { toEquiv :=
        { toFun := extendChartById e (D p)
          invFun := extendChartById e (D p).symm
          left_inv := leftInverse_extendChartById_of_mapsTo e (D p).symm_apply_apply (hmap p)
          right_inv := leftInverse_extendChartById_of_mapsTo e (D p).apply_symm_apply (hmapi p) }
      contMDiff_toFun := hF.comp (contMDiff_const.prodMk contMDiff_id)
      contMDiff_invFun := hG.comp (contMDiff_const.prodMk contMDiff_id) }
  refine ⟨J, hF, hG, fun _ _ ↦ ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
  · exact hK.image_of_continuousOn (hei.continuousOn.mono hKt)
  · rintro x ⟨z, hz, rfl⟩
    exact e.map_target (hKt hz)
  · intro p x hx
    exact ⟨extendChartById_eq_of_notMem_image e _ (fun z hz ↦ (hfix p z hz).1) hx,
      extendChartById_eq_of_notMem_image e _ (fun z hz ↦ (hfix p z hz).2) hx⟩

end Poincare.Topology.Manifold
