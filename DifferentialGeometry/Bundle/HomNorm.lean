import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open Bundle ContinuousLinearMap Filter
open scoped Topology

private lemma exists_one_lt_mul_sq_lt {c L : ℝ} (h : c < L) :
    ∃ r : ℝ, 1 < r ∧ c * r ^ 2 < L := by
  have htend : Tendsto (fun r : ℝ => c * r ^ 2) (𝓝 1) (𝓝 c) := by
    have h1 : Tendsto (fun r : ℝ => c * r ^ 2) (𝓝 1) (𝓝 (c * (1 : ℝ) ^ 2)) :=
      tendsto_const_nhds.mul ((continuous_pow 2).tendsto 1)
    simpa using h1
  have hev : ∀ᶠ r in 𝓝 (1 : ℝ), c * r ^ 2 < L := htend.eventually (Iio_mem_nhds h)
  have hev2 : ∀ᶠ r in 𝓝[>] (1 : ℝ), c * r ^ 2 < L := hev.filter_mono nhdsWithin_le_nhds
  rcases (hev2.and self_mem_nhdsWithin).exists with ⟨r, hr2, hr1⟩
  exact ⟨r, hr1, hr2⟩

variable
    {B : Type*} [TopologicalSpace B]
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    {E₁ : B → Type*} [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, NormedAddCommGroup (E₁ x)]
      [∀ x, InnerProductSpace ℝ (E₁ x)]
      [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁] [IsContinuousRiemannianBundle F₁ E₁]
    {E₂ : B → Type*} [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, NormedAddCommGroup (E₂ x)]
      [∀ x, InnerProductSpace ℝ (E₂ x)]
      [FiberBundle F₂ E₂] [VectorBundle ℝ F₂ E₂] [IsContinuousRiemannianBundle F₂ E₂]
    {Z : Type*} [TopologicalSpace Z] {b : Z → B} {s : Set Z} {z₀ : Z}
    {Ψ : Π z : Z, E₁ (b z) →L[ℝ] E₂ (b z)}

theorem ContinuousWithinAt.hom_bundle_opNorm
    (hΨ : ContinuousWithinAt (fun z : Z => TotalSpace.mk' (F₁ →L[ℝ] F₂)
      (E := fun x : B => E₁ x →L[ℝ] E₂ x) (b z) (Ψ z)) s z₀) :
    ContinuousWithinAt (fun z : Z => ‖Ψ z‖) s z₀ := by
  have hb : ContinuousWithinAt b s z₀ := by
    rw [continuousWithinAt_hom_bundle] at hΨ
    exact hΨ.1
  let x₀ := b z₀
  have hx₀a : x₀ ∈ (trivializationAt F₁ E₁ x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  have hx₀c : x₀ ∈ (trivializationAt F₂ E₂ x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  have hΦcont : ContinuousWithinAt (fun y : Z => ContinuousLinearMap.inCoordinates
      F₁ E₁ F₂ E₂ x₀ (b y) x₀ (b y) (Ψ y)) s z₀ := by
    have hcont := hΨ
    rw [continuousWithinAt_hom_bundle] at hcont
    exact hcont.2
  set Ψtil : Z → (E₁ x₀ →L[ℝ] E₂ x₀) := fun y =>
    (((trivializationAt F₂ E₂ x₀).symmL ℝ x₀).comp
        ((trivializationAt F₂ E₂ x₀).continuousLinearMapAt ℝ (b y))).comp
      ((Ψ y).comp (((trivializationAt F₁ E₁ x₀).symmL ℝ (b y)).comp
        ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt ℝ x₀)))
    with hΨtil_def
  have hΨtilcont : ContinuousWithinAt Ψtil s z₀ := by
    rw [hΨtil_def]
    refine (ContinuousWithinAt.clm_comp (g := fun _ : Z => ((trivializationAt F₂ E₂ x₀).symmL ℝ x₀))
      (f := fun y : Z => (((ContinuousLinearMap.inCoordinates F₁ E₁ F₂ E₂ x₀ (b y) x₀ (b y) (Ψ y))).comp
        ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt ℝ x₀))) continuousWithinAt_const
      (ContinuousWithinAt.clm_comp
        (g := fun y : Z => ContinuousLinearMap.inCoordinates F₁ E₁ F₂ E₂ x₀ (b y) x₀ (b y) (Ψ y))
        (f := fun _ : Z => (trivializationAt F₁ E₁ x₀).continuousLinearMapAt ℝ x₀)
        hΦcont continuousWithinAt_const)).congr ?_ ?_
    · intro y _
      rw [ContinuousLinearMap.inCoordinates]
      simp only [ContinuousLinearMap.comp_assoc]
    · rw [ContinuousLinearMap.inCoordinates]
      simp only [ContinuousLinearMap.comp_assoc]
  have hnormtil : ContinuousWithinAt (fun y => ‖Ψtil y‖) s z₀ := hΨtilcont.norm
  have hΨtil_x0 : Ψtil z₀ = Ψ z₀ := by
    rw [hΨtil_def]
    ext v
    simp only [ContinuousLinearMap.comp_apply]
    rw [(trivializationAt F₁ E₁ x₀).symmL_continuousLinearMapAt hx₀a,
      (trivializationAt F₂ E₂ x₀).symmL_continuousLinearMapAt hx₀c]
  have hnormtil_lim : Tendsto (fun y => ‖Ψtil y‖) (𝓝[s] z₀) (𝓝 ‖Ψ z₀‖) := by
    have h0 : Tendsto (fun y => ‖Ψtil y‖) (𝓝[s] z₀) (𝓝 ‖Ψtil z₀‖) := hnormtil
    rwa [hΨtil_x0] at h0
  have hbasea : ∀ᶠ y in 𝓝[s] z₀, b y ∈ (trivializationAt F₁ E₁ x₀).baseSet :=
    hb.eventually ((trivializationAt F₁ E₁ x₀).open_baseSet.mem_nhds hx₀a)
  have hbasec : ∀ᶠ y in 𝓝[s] z₀, b y ∈ (trivializationAt F₂ E₂ x₀).baseSet :=
    hb.eventually ((trivializationAt F₂ E₂ x₀).open_baseSet.mem_nhds hx₀c)
  have hfwd : ∀ {r : ℝ}, 1 < r → ∀ᶠ y in 𝓝[s] z₀, ‖Ψtil y‖ ≤ r ^ 2 * ‖Ψ y‖ := by
    intro r hr
    have hSc := hb.eventually (eventually_norm_symmL_trivializationAt_self_comp_lt F₂ E₂ x₀ hr)
    have hSa' := hb.eventually (eventually_norm_symmL_trivializationAt_comp_self_lt F₁ E₁ x₀ hr)
    filter_upwards [hSc, hSa'] with y hyc hya
    rw [hΨtil_def]
    calc ‖(((trivializationAt F₂ E₂ x₀).symmL ℝ x₀).comp
              ((trivializationAt F₂ E₂ x₀).continuousLinearMapAt ℝ (b y))).comp
            ((Ψ y).comp (((trivializationAt F₁ E₁ x₀).symmL ℝ (b y)).comp
              ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt ℝ x₀)))‖
        ≤ ‖((trivializationAt F₂ E₂ x₀).symmL ℝ x₀).comp
              ((trivializationAt F₂ E₂ x₀).continuousLinearMapAt ℝ (b y))‖ *
            ‖(Ψ y).comp (((trivializationAt F₁ E₁ x₀).symmL ℝ (b y)).comp
              ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt ℝ x₀))‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖((trivializationAt F₂ E₂ x₀).symmL ℝ x₀).comp
              ((trivializationAt F₂ E₂ x₀).continuousLinearMapAt ℝ (b y))‖ *
            (‖Ψ y‖ * ‖((trivializationAt F₁ E₁ x₀).symmL ℝ (b y)).comp
              ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt ℝ x₀)‖) := by
          gcongr
          exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ r * (‖Ψ y‖ * r) := by gcongr
      _ = r ^ 2 * ‖Ψ y‖ := by ring
  have hrev : ∀ {r : ℝ}, 1 < r → ∀ᶠ y in 𝓝[s] z₀, ‖Ψ y‖ ≤ r ^ 2 * ‖Ψtil y‖ := by
    intro r hr
    have hSc' := hb.eventually (eventually_norm_symmL_trivializationAt_comp_self_lt F₂ E₂ x₀ hr)
    have hSa := hb.eventually (eventually_norm_symmL_trivializationAt_self_comp_lt F₁ E₁ x₀ hr)
    filter_upwards [hSc', hSa, hbasea, hbasec] with y hyc hya hya_mem hyc_mem
    have hid : Ψ y =
        (((trivializationAt F₂ E₂ x₀).symmL ℝ (b y)).comp
            ((trivializationAt F₂ E₂ x₀).continuousLinearMapAt ℝ x₀)).comp
          ((Ψtil y).comp (((trivializationAt F₁ E₁ x₀).symmL ℝ x₀).comp
            ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt ℝ (b y)))) := by
      rw [hΨtil_def]
      ext v
      simp only [ContinuousLinearMap.comp_apply]
      rw [(trivializationAt F₁ E₁ x₀).continuousLinearMapAt_symmL hx₀a,
        (trivializationAt F₁ E₁ x₀).symmL_continuousLinearMapAt hya_mem,
        (trivializationAt F₂ E₂ x₀).continuousLinearMapAt_symmL hx₀c,
        (trivializationAt F₂ E₂ x₀).symmL_continuousLinearMapAt hyc_mem]
    rw [hid]
    calc ‖(((trivializationAt F₂ E₂ x₀).symmL ℝ (b y)).comp
              ((trivializationAt F₂ E₂ x₀).continuousLinearMapAt ℝ x₀)).comp
            ((Ψtil y).comp (((trivializationAt F₁ E₁ x₀).symmL ℝ x₀).comp
              ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt ℝ (b y))))‖
        ≤ ‖((trivializationAt F₂ E₂ x₀).symmL ℝ (b y)).comp
              ((trivializationAt F₂ E₂ x₀).continuousLinearMapAt ℝ x₀)‖ *
            ‖(Ψtil y).comp (((trivializationAt F₁ E₁ x₀).symmL ℝ x₀).comp
              ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt ℝ (b y)))‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖((trivializationAt F₂ E₂ x₀).symmL ℝ (b y)).comp
              ((trivializationAt F₂ E₂ x₀).continuousLinearMapAt ℝ x₀)‖ *
            (‖Ψtil y‖ * ‖((trivializationAt F₁ E₁ x₀).symmL ℝ x₀).comp
              ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt ℝ (b y))‖) := by
          gcongr
          exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ r * (‖Ψtil y‖ * r) := by gcongr
      _ = r ^ 2 * ‖Ψtil y‖ := by ring
  change Tendsto (fun y => ‖Ψ y‖) (𝓝[s] z₀) (𝓝 ‖Ψ z₀‖)
  rw [tendsto_order]
  refine ⟨?_, ?_⟩
  · intro c hc
    obtain ⟨r, hr1, hrlt⟩ := exists_one_lt_mul_sq_lt hc
    have hev1 : ∀ᶠ y in 𝓝[s] z₀, c * r ^ 2 < ‖Ψtil y‖ :=
      hnormtil_lim.eventually (lt_mem_nhds hrlt)
    filter_upwards [hev1, hfwd hr1] with y hy1 hy2
    have hr2pos : (0 : ℝ) < r ^ 2 := by positivity
    have hchain : c * r ^ 2 < ‖Ψ y‖ * r ^ 2 := by
      calc c * r ^ 2 < ‖Ψtil y‖ := hy1
        _ ≤ r ^ 2 * ‖Ψ y‖ := hy2
        _ = ‖Ψ y‖ * r ^ 2 := by ring
    exact lt_of_mul_lt_mul_right hchain (le_of_lt hr2pos)
  · intro c hc
    obtain ⟨r, hr1, hrlt⟩ := exists_one_lt_mul_sq_lt hc
    have hlim2 : Tendsto (fun y => r ^ 2 * ‖Ψtil y‖) (𝓝[s] z₀) (𝓝 (r ^ 2 * ‖Ψ z₀‖)) :=
      hnormtil_lim.const_mul _
    have hlt2 : r ^ 2 * ‖Ψ z₀‖ < c := by rw [mul_comm]; exact hrlt
    have hev1 : ∀ᶠ y in 𝓝[s] z₀, r ^ 2 * ‖Ψtil y‖ < c :=
      hlim2.eventually (Iio_mem_nhds hlt2)
    filter_upwards [hev1, hrev hr1] with y hy1 hy2
    exact lt_of_le_of_lt hy2 hy1

theorem ContinuousAt.hom_bundle_opNorm
    (hΨ : ContinuousAt (fun z : Z => TotalSpace.mk' (F₁ →L[ℝ] F₂)
      (E := fun x : B => E₁ x →L[ℝ] E₂ x) (b z) (Ψ z)) z₀) :
    ContinuousAt (fun z : Z => ‖Ψ z‖) z₀ := by
  rw [← continuousWithinAt_univ] at hΨ ⊢
  exact hΨ.hom_bundle_opNorm

theorem Continuous.hom_bundle_opNorm
    (hΨ : Continuous (fun z : Z => TotalSpace.mk' (F₁ →L[ℝ] F₂)
      (E := fun x : B => E₁ x →L[ℝ] E₂ x) (b z) (Ψ z))) :
    Continuous (fun z : Z => ‖Ψ z‖) :=
  continuous_iff_continuousAt.mpr fun _ => hΨ.continuousAt.hom_bundle_opNorm

theorem ContinuousOn.hom_bundle_opNorm
    (hΨ : ContinuousOn (fun z : Z => TotalSpace.mk' (F₁ →L[ℝ] F₂)
      (E := fun x : B => E₁ x →L[ℝ] E₂ x) (b z) (Ψ z)) s) :
    ContinuousOn (fun z : Z => ‖Ψ z‖) s :=
  fun z hz => (hΨ z hz).hom_bundle_opNorm

theorem IsCompact.exists_hom_bundle_opNorm_bound
    (hs : IsCompact s)
    (hΨ : ContinuousOn (fun z : Z => TotalSpace.mk' (F₁ →L[ℝ] F₂)
      (E := fun x : B => E₁ x →L[ℝ] E₂ x) (b z) (Ψ z)) s) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ z ∈ s, ‖Ψ z‖ ≤ R := by
  obtain ⟨R, hR⟩ := hs.bddAbove_image hΨ.hom_bundle_opNorm
  exact ⟨max R 0, le_max_right _ _, fun z hz => (hR ⟨z, hz, rfl⟩).trans (le_max_left _ _)⟩

end
