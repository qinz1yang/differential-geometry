import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike

open Set Filter Function Topology Manifold
open scoped ContDiff

namespace Poincare.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]

set_option backward.isDefEq.respectTransparency false in
theorem exists_eqOn_initial_Icc_of_isMIntegralCurveOn
    {v : (x : M) → TangentSpace I x} {γ η : ℝ → M} {T : ℝ}
    (hT : 0 < T)
    (hv : ContMDiffAt I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) (γ 0))
    (hγ : IsMIntegralCurveOn γ v (Icc 0 T))
    (hη : IsMIntegralCurveOn η v (Icc 0 T)) (hinit : γ 0 = η 0) :
    ∃ δ > 0, δ < T ∧ EqOn γ η (Icc 0 δ) := by
  let c := extChartAt I (γ 0)
  let w : E → E := fun x ↦
    tangentCoordChange I (c.symm x) (γ 0) (c.symm x) (v (c.symm x))
  obtain ⟨_, hv'⟩ := contMDiffAt_iff.mp hv
  obtain ⟨K, S, hS, hw⟩ : ∃ K, ∃ S ∈ 𝓝[range I] (c (γ 0)), LipschitzOnWith K w S :=
    hv'.snd.exists_lipschitzOnWith I.convex_range
  have hc : Tendsto c (𝓝 (γ 0)) (𝓝[range I] (c (γ 0))) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨continuousAt_extChartAt _, ?_⟩
    exact Eventually.of_forall (fun x ↦ ⟨(chartAt H (γ 0)) x, rfl⟩)
  have hN : c.source ∩ c ⁻¹' S ∈ 𝓝 (γ 0) :=
    inter_mem (extChartAt_source_mem_nhds _) (hc hS)
  have hboth : {t | γ t ∈ c.source ∩ c ⁻¹' S ∧ η t ∈ c.source ∩ c ⁻¹' S}
      ∈ 𝓝[Icc 0 T] 0 :=
    inter_mem ((hγ.continuousWithinAt ⟨le_rfl, hT.le⟩).preimage_mem_nhdsWithin hN)
      ((hη.continuousWithinAt ⟨le_rfl, hT.le⟩).preimage_mem_nhdsWithin (hinit ▸ hN))
  obtain ⟨A, hA, hAboth⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hboth
  obtain ⟨r, hr, hrA⟩ := Metric.mem_nhds_iff.mp hA
  let δ := min (T / 2) (r / 2)
  have hδ : 0 < δ := lt_min (half_pos hT) (half_pos hr)
  have hδT : δ < T := (min_le_left _ _).trans_lt (half_lt_self hT)
  have hconf : ∀ t ∈ Icc 0 δ,
      γ t ∈ c.source ∩ c ⁻¹' S ∧ η t ∈ c.source ∩ c ⁻¹' S := by
    intro t ht
    apply hAboth
    refine ⟨hrA ?_, ht.1, ht.2.trans hδT.le⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    exact (ht.2.trans (min_le_right _ _)).trans_lt (half_lt_self hr)
  have htime : ∀ t ∈ Ico 0 δ, Icc 0 T ∈ 𝓝[Ici t] t := by
    intro t ht
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (ht.2.trans hδT))] with s hs hsT
    exact ⟨ht.1.trans hs, hsT.le⟩
  have hγc : ContinuousOn (c ∘ γ) (Icc 0 δ) := by
    intro t ht
    exact (continuousAt_extChartAt' (hconf t ht).1.1).comp_continuousWithinAt
      ((hγ.continuousWithinAt ⟨ht.1, ht.2.trans hδT.le⟩).mono (Icc_subset_Icc_right hδT.le))
  have hηc : ContinuousOn (c ∘ η) (Icc 0 δ) := by
    intro t ht
    exact (continuousAt_extChartAt' (hconf t ht).2.1).comp_continuousWithinAt
      ((hη.continuousWithinAt ⟨ht.1, ht.2.trans hδT.le⟩).mono (Icc_subset_Icc_right hδT.le))
  have hγd : ∀ t ∈ Ico 0 δ, HasDerivWithinAt (c ∘ γ) (w (c (γ t))) (Ici t) t := by
    intro t ht
    have h := (hγ.hasDerivWithinAt (t₀ := 0) ⟨ht.1, ht.2.le.trans hδT.le⟩
      (hconf t (Ico_subset_Icc_self ht)).1.1).mono_of_mem_nhdsWithin (htime t ht)
    dsimp only [w]
    rw [c.left_inv (hconf t (Ico_subset_Icc_self ht)).1.1]
    exact h
  have hηd : ∀ t ∈ Ico 0 δ, HasDerivWithinAt (c ∘ η) (w (c (η t))) (Ici t) t := by
    intro t ht
    have hsrc : η t ∈ (extChartAt I (η 0)).source :=
      hinit ▸ (hconf t (Ico_subset_Icc_self ht)).2.1
    have h := (hη.hasDerivWithinAt (t₀ := 0) ⟨ht.1, ht.2.le.trans hδT.le⟩ hsrc).mono_of_mem_nhdsWithin
      (htime t ht)
    rw [← hinit] at h
    dsimp only [w]
    rw [c.left_inv (hconf t (Ico_subset_Icc_self ht)).2.1]
    exact h
  have heq : EqOn (c ∘ γ) (c ∘ η) (Icc 0 δ) :=
    ODE_solution_unique_of_mem_Icc_right (fun _ _ ↦ hw) hγc hγd
      (fun t ht ↦ (hconf t (Ico_subset_Icc_self ht)).1.2) hηc hηd
      (fun t ht ↦ (hconf t (Ico_subset_Icc_self ht)).2.2)
      (congrArg c hinit)
  refine ⟨δ, hδ, hδT, ?_⟩
  intro t ht
  exact c.injOn (hconf t ht).1.1 (hconf t ht).2.1 (heq ht)

set_option backward.isDefEq.respectTransparency false in
theorem isMIntegralCurveAt_eventuallyEq
    {v : (x : M) → TangentSpace I x} {γ η : ℝ → M} {t₀ : ℝ}
    (hv : ContMDiffAt I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) (γ t₀))
    (hγ : IsMIntegralCurveAt γ v t₀) (hη : IsMIntegralCurveAt η v t₀)
    (h : γ t₀ = η t₀) : γ =ᶠ[𝓝 t₀] η := by
  set v' : E → E := fun x ↦
    tangentCoordChange I ((extChartAt I (γ t₀)).symm x) (γ t₀) ((extChartAt I (γ t₀)).symm x)
      (v ((extChartAt I (γ t₀)).symm x)) with hv'
  rw [contMDiffAt_iff] at hv
  obtain ⟨_, hv⟩ := hv
  obtain ⟨K, s, hs, hlip⟩ : ∃ K, ∃ s ∈ 𝓝[range I] _, LipschitzOnWith K v' s :=
    hv.snd.exists_lipschitzOnWith I.convex_range
  have hlip (t : ℝ) : LipschitzOnWith K ((fun _ ↦ v') t) ((fun _ ↦ s) t) := hlip
  have hsrc {g} (hg : IsMIntegralCurveAt g v t₀) :
    ∀ᶠ t in 𝓝 t₀, g ⁻¹' (extChartAt I (g t₀)).source ∈ 𝓝 t := eventually_mem_nhds_iff.mpr <|
      continuousAt_def.mp hg.continuousAt _ <| extChartAt_source_mem_nhds (g t₀)
  have hmem {g : ℝ → M} {t} (ht : g ⁻¹' (extChartAt I (g t₀)).source ∈ 𝓝 t) :
    g t ∈ (extChartAt I (g t₀)).source := mem_preimage.mp <| mem_of_mem_nhds ht
  have hdrv {g} (hg : IsMIntegralCurveAt g v t₀) (h' : γ t₀ = g t₀) : ∀ᶠ t in 𝓝 t₀,
      HasDerivAt ((extChartAt I (g t₀)) ∘ g) ((fun _ ↦ v') t (((extChartAt I (g t₀)) ∘ g) t)) t ∧
      ((extChartAt I (g t₀)) ∘ g) t ∈ (fun _ ↦ s) t := by
    apply Filter.Eventually.and
    · apply (hsrc hg |>.and hg.eventually_hasDerivAt).mono
      rintro t ⟨ht1, ht2⟩
      rw [hv', h']
      apply ht2.congr_deriv
      congr <;>
      rw [Function.comp_apply, PartialEquiv.left_inv _ (hmem ht1)]
    · have hc : Tendsto ((extChartAt I (g t₀)) ∘ g) (𝓝 t₀)
          (𝓝[range I] (extChartAt I (g t₀) (g t₀))) := by
        refine tendsto_nhdsWithin_iff.mpr
          ⟨(continuousAt_extChartAt (g t₀)).comp hg.continuousAt, ?_⟩
        exact Eventually.of_forall (fun t ↦ ⟨(chartAt H (g t₀)) (g t), rfl⟩)
      apply hc
      simpa only [h'] using hs
  have heq {g} (hg : IsMIntegralCurveAt g v t₀) :
    g =ᶠ[𝓝 t₀] (extChartAt I (g t₀)).symm ∘ ↑(extChartAt I (g t₀)) ∘ g := by
    apply (hsrc hg).mono
    intro t ht
    rw [Function.comp_apply, Function.comp_apply, PartialEquiv.left_inv _ (hmem ht)]
  suffices (extChartAt I (γ t₀)) ∘ γ =ᶠ[𝓝 t₀] (extChartAt I (η t₀)) ∘ η from
    (heq hγ).trans <| (this.fun_comp (extChartAt I (γ t₀)).symm).trans (h ▸ (heq hη).symm)
  exact ODE_solution_unique_of_eventually (.of_forall hlip)
    (hdrv hγ rfl) (hdrv hη h) (by rw [Function.comp_apply, Function.comp_apply, h])

theorem isMIntegralCurveOn_Ioo_eqOn [T2Space M]
    {v : (x : M) → TangentSpace I x} {γ η : ℝ → M} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b)
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsMIntegralCurveOn γ v (Ioo a b)) (hη : IsMIntegralCurveOn η v (Ioo a b))
    (h : γ t₀ = η t₀) : EqOn γ η (Ioo a b) := by
  set s := {t | γ t = η t} ∩ Ioo a b with hs
  suffices hsub : Ioo a b ⊆ s from fun t ht ↦ mem_ofPred.mp ((subset_def ▸ hsub) t ht).1
  apply isPreconnected_Ioo.subset_of_closure_inter_subset (s := Ioo a b) (u := s) _
    ⟨t₀, ⟨ht₀, ⟨h, ht₀⟩⟩⟩
  · rw [hs, inter_comm, ← Subtype.image_preimage_val, inter_comm, ← Subtype.image_preimage_val,
      image_subset_image_iff Subtype.val_injective, preimage_ofPred_eq]
    intro t ht
    rw [mem_preimage, ← closure_subtype] at ht
    revert ht t
    apply IsClosed.closure_subset (isClosed_eq _ _)
    · rw [continuous_iff_continuousAt]
      rintro ⟨_, ht⟩
      apply ContinuousAt.comp _ continuousAt_subtype_val
      rw [Subtype.coe_mk]
      exact hγ.continuousWithinAt ht |>.continuousAt (Ioo_mem_nhds ht.1 ht.2)
    · rw [continuous_iff_continuousAt]
      rintro ⟨_, ht⟩
      apply ContinuousAt.comp _ continuousAt_subtype_val
      rw [Subtype.coe_mk]
      exact hη.continuousWithinAt ht |>.continuousAt (Ioo_mem_nhds ht.1 ht.2)
  · rw [isOpen_iff_mem_nhds]
    intro t₁ ht₁
    have hmem := Ioo_mem_nhds ht₁.2.1 ht₁.2.2
    have heq : γ =ᶠ[𝓝 t₁] η := isMIntegralCurveAt_eventuallyEq hv.contMDiffAt (hγ.isMIntegralCurveAt hmem) (hη.isMIntegralCurveAt hmem) ht₁.1
    apply (heq.and hmem).mono
    exact fun _ ht ↦ ht

theorem isMIntegralCurveOn_Icc_eqOn [T2Space M]
    {v : (x : M) → TangentSpace I x} {γ η : ℝ → M} {a b : ℝ}
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsMIntegralCurveOn γ v (Icc a b)) (hη : IsMIntegralCurveOn η v (Icc a b))
    (hinit : γ a = η a) : EqOn γ η (Icc a b) := by
  by_cases hab : a < b
  · have hγshift : IsMIntegralCurveOn (γ ∘ (· + a)) v (Icc 0 (b - a)) :=
      (hγ.comp_add a).mono (fun t ht ↦ ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    have hηshift : IsMIntegralCurveOn (η ∘ (· + a)) v (Icc 0 (b - a)) :=
      (hη.comp_add a).mono (fun t ht ↦ ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    obtain ⟨δ, hδ, hδT, hearly⟩ := exists_eqOn_initial_Icc_of_isMIntegralCurveOn
      (sub_pos.mpr hab) hv.contMDiffAt hγshift hηshift (by simpa using hinit)
    have hseed : a + δ / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
    have hseedEq : γ (a + δ / 2) = η (a + δ / 2) := by
      have h := hearly (show δ / 2 ∈ Icc 0 δ from ⟨(half_pos hδ).le, (half_lt_self hδ).le⟩)
      simpa only [comp_apply, add_comm] using h
    have heq := isMIntegralCurveOn_Ioo_eqOn hseed hv
      (hγ.mono Ioo_subset_Icc_self) (hη.mono Ioo_subset_Icc_self) hseedEq
    have hclosed : IsClosed {t ∈ Icc a b | γ t = η t} :=
      isClosed_Icc.isClosed_eq hγ.continuousOn hη.continuousOn
    have hcl := closure_minimal (show Ioo a b ⊆ {t ∈ Icc a b | γ t = η t} from
      fun t ht ↦ ⟨Ioo_subset_Icc_self ht, heq ht⟩) hclosed
    rw [closure_Ioo hab.ne] at hcl
    exact fun t ht ↦ (hcl ht).2
  · intro t ht
    have hta : t = a := by linarith [ht.1, ht.2]
    simpa only [hta] using hinit

theorem isMIntegralCurveOn_Ico_eqOn [T2Space M]
    {v : (x : M) → TangentSpace I x} {γ η : ℝ → M} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Ico a b)
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsMIntegralCurveOn γ v (Ico a b)) (hη : IsMIntegralCurveOn η v (Ico a b))
    (h : γ t₀ = η t₀) : EqOn γ η (Ico a b) := by
  by_cases hstart : t₀ = a
  · subst t₀
    intro t ht
    have hsub : Icc a t ⊆ Ico a b := fun s hs ↦ ⟨hs.1, hs.2.trans_lt ht.2⟩
    exact isMIntegralCurveOn_Icc_eqOn hv (hγ.mono hsub) (hη.mono hsub) h ⟨ht.1, le_rfl⟩
  · have ht₀' : t₀ ∈ Ioo a b := ⟨lt_of_le_of_ne ht₀.1 (Ne.symm hstart), ht₀.2⟩
    have heq := isMIntegralCurveOn_Ioo_eqOn ht₀' hv
      (hγ.mono Ioo_subset_Ico_self) (hη.mono Ioo_subset_Ico_self) h
    apply heq.of_subset_closure hγ.continuousOn hη.continuousOn Ioo_subset_Ico_self
    rw [closure_Ioo (ht₀.1.trans_lt ht₀.2).ne]
    exact Ico_subset_Icc_self

end Poincare.Topology.Manifold
