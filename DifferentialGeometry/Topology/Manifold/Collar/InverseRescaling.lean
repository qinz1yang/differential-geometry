import DifferentialGeometry.Topology.Manifold.Collar.Rescaling

open Set Function Filter Manifold Topology TopologicalSpace
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace Poincare.Manifold.Collar

theorem contMDiff_rescale_homeomorph_symm
    {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B] [CompactSpace B]
    {F G M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] [TopologicalSpace M] [ChartedSpace G M] [T2Space M]
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E H} {I : ModelWithCorners ℝ F G}
    {K : ModelWithCorners ℝ E' H'} {A : Set M} [ChartedSpace H' A]
    {ε : ℝ} [Fact ((0 : ℝ) < ε)]
    (c : B × Icc (0 : ℝ) ε → M) (hc : IsEmbedding c)
    (hcs : ContMDiff (J.prod (𝓡∂ 1)) I ∞ c)
    (σ : C(Icc (0 : ℝ) ε, Icc (0 : ℝ) ε))
    (d : ℝ ≃ₘ[ℝ] ℝ) (hd : ∀ t : Icc (0 : ℝ) ε, (σ t).val = d t.val)
    {Ω : Opens (B × Icc (0 : ℝ) ε)} {Y : Opens M}
    (e : Diffeomorph (J.prod (𝓡∂ 1)) I Ω Y ∞)
    (he : ∀ q : Ω, (e q : M) = c q.val)
    {k : ℝ} (hcore : {q : B × Icc (0 : ℝ) ε | q.2.val ≤ k} ⊆ Ω)
    (hfix : ∀ t : Icc (0 : ℝ) ε, k ≤ t.val → σ t = t)
    (h : M ≃ₜ A)
    (hmap : ∀ x, (h x : M) = Poincare.Topology.Collar.rescale c hc σ x)
    (hinc : ContMDiff K I ∞ (Subtype.val : A → M)) :
    ContMDiff K I ∞ h.symm := by
  let R := Poincare.Topology.Collar.rescale c hc σ
  have hR (q : B × Icc (0 : ℝ) ε) : R (c q) = c (q.1, σ q.2) :=
    Poincare.Topology.Collar.rescale_apply c hc σ q
  have hinj : Injective σ := by
    intro t u htu
    apply Subtype.ext
    apply d.injective
    exact (hd t).symm.trans ((congrArg Subtype.val htu).trans (hd u))
  have hRinj : Injective R := Poincare.Topology.Collar.injective_rescale c hc σ hinj
  have hinverse (y : A) : R (h.symm y) = (y : M) := by
    exact (hmap (h.symm y)).symm.trans (congrArg Subtype.val (h.apply_symm_apply y))
  have hpreimage (y : A) (q : B × Icc (0 : ℝ) ε) (hq : (y : M) = c q) :
      ∃ t : Icc (0 : ℝ) ε, σ t = q.2 ∧ h.symm y = c (q.1, t) := by
    have hp : h.symm y ∈ range c := by
      by_contra hp
      have hh := Poincare.Topology.Collar.rescale_of_not_mem c hc σ hp
      exact hp ⟨q, hq.symm.trans ((hinverse y).symm.trans hh)⟩
    obtain ⟨p, hp⟩ := hp
    have heq : (p.1, σ p.2) = q := hc.injective (by rw [← hR, hp, hinverse, hq])
    refine ⟨p.2, congrArg Prod.snd heq, ?_⟩
    rw [← hp, ← congrArg Prod.fst heq]
  let C := c '' {q : B × Icc (0 : ℝ) ε | q.2.val ≤ k}
  have hC : IsCompact C :=
    ((isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const).isCompact).image hc.continuous
  have hCY : C ⊆ Y := by
    rintro _ ⟨q, hq, rfl⟩
    rw [← he ⟨q, hcore hq⟩]
    exact (e ⟨q, hcore hq⟩).property
  let U : Opens A := ⟨Subtype.val ⁻¹' Y, Y.isOpen.preimage continuous_subtype_val⟩
  let j : U → Y := fun y => ⟨y.val.val, y.property⟩
  have hjs : ContMDiff K I ∞ j :=
    (ContMDiff.subtypeVal_comp_iff Y j).mp (hinc.comp contMDiff_subtype_val)
  let g : U → B × Icc (0 : ℝ) ε := fun y => (e.symm (j y)).val
  have hgs : ContMDiff K (J.prod (𝓡∂ 1)) ∞ g :=
    contMDiff_subtype_val.comp (e.symm.contMDiff.comp hjs)
  have hgy (y : U) : c (g y) = y.val.val := by
    rw [← he (e.symm (j y)), e.apply_symm_apply]
  have hbound (y : U) : d.symm ((g y).2.val) ∈ Icc (0 : ℝ) ε := by
    obtain ⟨t, ht, _⟩ := hpreimage y.val (g y) (hgy y).symm
    rw [← ht, hd, d.symm_apply_apply]
    exact t.property
  let τ : U → Icc (0 : ℝ) ε := fun y => ⟨d.symm ((g y).2.val), hbound y⟩
  have hτs : ContMDiff K (𝓡∂ 1) ∞ τ := by
    apply contMDiff_iff_comp_subtypeVal_Icc.mpr
    refine ⟨?_, ?_⟩
    · exact (d.symm.continuous.comp (continuous_subtype_val.comp hgs.continuous.snd)).subtype_mk _
    · exact d.symm.contMDiff.comp (contMDiff_subtypeVal_Icc.comp hgs.snd)
  have hlocal : ContMDiff K I ∞ (fun y : U => h.symm y.val) := by
    apply (hcs.comp (hgs.fst.prodMk hτs)).congr
    intro y
    obtain ⟨t, ht, hyt⟩ := hpreimage y.val (g y) (hgy y).symm
    have hτ : τ y = t := by
      apply Subtype.ext
      change d.symm ((g y).2.val) = t.val
      rw [← ht, hd, d.symm_apply_apply]
    exact hyt.trans (congrArg (fun t => c ((g y).1, t)) hτ.symm)
  intro y
  by_cases hyY : (y : M) ∈ Y
  · exact (contMDiffAt_subtype_iff (x := (⟨y, hyY⟩ : U))).mp hlocal.contMDiffAt
  · have hyC : (y : M) ∉ C := fun hy => hyY (hCY hy)
    apply hinc.contMDiffAt.congr_of_eventuallyEq
    filter_upwards [hinc.continuous.continuousAt.preimage_mem_nhds (hC.isClosed.isOpen_compl.mem_nhds hyC)] with z hz
    apply hRinj
    rw [hinverse]
    by_cases hzc : (z : M) ∈ range c
    · obtain ⟨q, hq⟩ := hzc
      have ht : k ≤ q.2.val := le_of_lt (lt_of_not_ge (fun ht => hz ⟨q, ht, hq⟩))
      rw [← hq, hR, hfix q.2 ht]
    · exact (Poincare.Topology.Collar.rescale_of_not_mem c hc σ hzc).symm

end Poincare.Manifold.Collar
