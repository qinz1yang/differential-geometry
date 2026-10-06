import DifferentialGeometry.Topology.Ehresmann.SurfaceIntervalProductEFE
import DifferentialGeometry.Topology.Manifold.LocalExtrema
import DifferentialGeometry.Topology.Order.LocalExtrema

/-!
# The end of a base arc: a regular defining function on the whole tube over a neighbourhood

Lane S-ZSP04, group G20 (ZSP05 smooth faces; draft 74 `SlimPiecesV2.endFn / endNear / endFn_level /
endFn_eq`). Blueprint `master207B.tex`, ZSP04 / ZSP05 (B:6531–6640): at a free end of the base `D₃`
the slim piece "cuts off one side" along a whole regular fibre with a product collar.

* `exists_arc_end_chart_ZSP35` (base kernel): for an injective continuous arc `γ : [0, 1] → T`
  whose germ at `γ 0` is all of `T` (isolation) in a graph-atlas base, the chart coordinate `κ_i`
  of a chart through `γ 0` is strictly monotone along `γ` near `0` (injective continuous), so near
  `γ 0` the set `T` is a ONE-SIDED coordinate interval of the base: `ψ_i(b) ∈ T ↔ 0 ≤ σ (b − a₀)`
  (`σ = ±1`), on an open set `V` with `V ∩ Bs = ψ_i((a₀ − ε, a₀ + ε))` that misses a prescribed
  closed set `E'` (the other ends). No derivative is used.
* `exists_end_defining_function_ZSP35` (kernel over a `ProperSmoothSurfaceSubmersion_EFE`): with
  `U = f⁻¹(V ∩ Bs)` and `h = σ (a₀ − κ_i ∘ f)`: `U` is open and contains the whole fibre `f⁻¹(γ 0)`,
  `h` is smooth on `U` with onto differential at EVERY point of `U`, `{h = 0} ∩ U = f⁻¹(γ 0)` (the
  whole fibre), and `f⁻¹(T) ∩ U = {h ≤ 0} ∩ U`.
* `mem_closure_pos_of_mfderiv_ne_zero_ZSP35`: a regular zero of a smooth function is a limit of
  points where it is positive (and, by `-h`, negative).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Ehresmann

open DifferentialGeometry.Topology

section ArcEndChart

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {ι : Type*} {Bs : Set H}

/-- **The arc end in a graph chart** (base kernel): see the module docstring. -/
theorem exists_arc_end_chart_ZSP35 (At : GraphAtlas1_BCF ι Bs) (R : ι → Set H)
    (hRo : ∀ i, IsOpen (R i)) (hRc : Bs ⊆ ⋃ i, R i)
    (hRp : ∀ i, R i ∩ Bs ⊆ At.param i '' At.dom i)
    {γ : ℝ → H} (hγc : ContinuousOn γ (Icc 0 1)) (hinj : InjOn γ (Icc 0 1))
    {T : Set H} (hT : γ '' Icc 0 1 ⊆ T) (hTB : T ⊆ Bs)
    (hiso : ∃ N : Set H, IsOpen N ∧ γ 0 ∈ N ∧ T ∩ N ⊆ γ '' Icc 0 1)
    {E' : Set H} (hE' : IsClosed E') (hyE : γ 0 ∉ E') :
    ∃ (i : ι) (σ ε : ℝ) (V : Set H), (σ = 1 ∨ σ = -1) ∧ 0 < ε ∧
      Icc (At.coord i (γ 0) - ε) (At.coord i (γ 0) + ε) ⊆ At.dom i ∧ IsOpen V ∧
      V ∩ Bs = At.param i '' Ioo (At.coord i (γ 0) - ε) (At.coord i (γ 0) + ε) ∧
      V ∩ Bs ⊆ R i ∧ V ∩ E' = ∅ ∧ γ 0 ∈ V ∧
      ∀ b ∈ Ioo (At.coord i (γ 0) - ε) (At.coord i (γ 0) + ε),
        (At.param i b ∈ T ↔ 0 ≤ σ * (b - At.coord i (γ 0))) := by
  have hy0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hyT : γ 0 ∈ T := hT ⟨0, hy0, rfl⟩
  have hyB : γ 0 ∈ Bs := hTB hyT
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hRc hyB)
  obtain ⟨a₀, ha₀, hya⟩ := hRp i ⟨hi, hyB⟩
  have hκy : At.coord i (γ 0) = a₀ := by
    rw [← hya]
    exact At.coord_param i a₀ ha₀
  obtain ⟨Vi, hVi, hViB⟩ := At.piece_relOpen i
  have hyVi : γ 0 ∈ Vi := by
    have : γ 0 ∈ Vi ∩ Bs := by
      rw [hViB]
      exact ⟨a₀, ha₀, hya⟩
    exact this.1
  obtain ⟨N, hN, hyN, hTN⟩ := hiso
  set W₁ : Set H := Vi ∩ R i ∩ N with hW₁
  have hW₁o : IsOpen W₁ := (hVi.inter (hRo i)).inter hN
  have hyW₁ : γ 0 ∈ W₁ := ⟨⟨hyVi, hi⟩, hyN⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hW₁o _ hyW₁
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.mp (hγc 0 hy0) r hr
  set δ₀ : ℝ := min (δ / 2) (1 / 2) with hδ₀
  have hδ₀pos : 0 < δ₀ := lt_min (by linarith) (by norm_num)
  have hδ₀1 : δ₀ ≤ 1 / 2 := min_le_right _ _
  have hsub : Icc 0 δ₀ ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc_right (by linarith)
  have hW : ∀ t ∈ Icc 0 δ₀, γ t ∈ W₁ := by
    intro t ht
    apply hball
    rw [Metric.mem_ball]
    refine hδc (hsub ht) ?_
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    linarith [ht.2, min_le_left (δ / 2) (1 / 2)]
  set κ := At.coord i with hκ
  set a : ℝ → ℝ := fun t => κ (γ t) with ha
  have hpar : ∀ t ∈ Icc 0 δ₀, γ t = At.param i (a t) ∧ a t ∈ At.dom i := by
    intro t ht
    have hγt : γ t ∈ Vi ∩ Bs := ⟨(hW t ht).1.1, hTB (hT ⟨t, hsub ht, rfl⟩)⟩
    obtain ⟨b, hb, hbt⟩ : γ t ∈ At.param i '' At.dom i := hViB ▸ hγt
    have hab : a t = b := by
      change κ (γ t) = b
      rw [← hbt]
      exact At.coord_param i b hb
    rw [hab]
    exact ⟨hbt.symm, hb⟩
  have hac : ContinuousOn a (Icc 0 δ₀) := κ.continuous.comp_continuousOn (hγc.mono hsub)
  have hainj : InjOn a (Icc 0 δ₀) := by
    intro t ht t' ht' h
    apply hinj (hsub ht) (hsub ht')
    rw [(hpar t ht).1, (hpar t' ht').1, h]
  have hκ0 : a 0 = a₀ := hκy
  obtain ⟨σ, hσ, hmono⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      StrictMonoOn (fun t => σ * (a t - a₀)) (Icc 0 δ₀) := by
    rcases hac.strictMonoOn_of_injOn_Icc' hδ₀pos.le hainj with h | h
    · refine ⟨1, Or.inl rfl, fun s hs t ht hst => ?_⟩
      have := h hs ht hst
      simpa using this
    · refine ⟨-1, Or.inr rfl, fun s hs t ht hst => ?_⟩
      have := h hs ht hst
      simp only [neg_mul, one_mul, neg_lt_neg_iff]
      linarith
  have hσ0 : σ ≠ 0 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hσabs : ∀ x : ℝ, |σ * x| = |x| := by
    intro x
    rcases hσ with h | h <;> rw [h] <;> simp
  set c : ℝ → ℝ := fun t => σ * (a t - a₀) with hc
  have hc0 : c 0 = 0 := by simp [hc, hκ0]
  have hcδ : 0 < c δ₀ := by
    have := hmono (left_mem_Icc.mpr hδ₀pos.le) (right_mem_Icc.mpr hδ₀pos.le) hδ₀pos
    rwa [hc0] at this
  have hcc : ContinuousOn c (Icc 0 δ₀) :=
    (continuousOn_const.mul (hac.sub continuousOn_const))
  have hivt := intermediate_value_Icc hδ₀pos.le hcc
  -- the shrinking neighbourhood `W₃`
  set W₃ : Set H := E'ᶜ ∩ (γ '' Icc δ₀ 1)ᶜ ∩ N ∩ R i with hW₃
  have hcmp : IsCompact (γ '' Icc δ₀ 1) :=
    isCompact_Icc.image_of_continuousOn (hγc.mono (Icc_subset_Icc_left hδ₀pos.le))
  have hW₃o : IsOpen W₃ :=
    ((hE'.isOpen_compl.inter hcmp.isClosed.isOpen_compl).inter hN).inter (hRo i)
  have hyW₃ : γ 0 ∈ W₃ := by
    refine ⟨⟨⟨hyE, ?_⟩, hyN⟩, hi⟩
    rintro ⟨t, ht, hty⟩
    have := hinj ⟨hδ₀pos.le.trans ht.1, ht.2⟩ hy0 hty
    linarith [ht.1]
  have hdomo := At.isOpen_dom i
  have hcont : ContinuousAt (At.param i) a₀ :=
    (At.continuousOn_param_BCF i).continuousAt (hdomo.mem_nhds ha₀)
  have hev : ∀ᶠ b in 𝓝 a₀, At.param i b ∈ W₃ ∧ b ∈ At.dom i :=
    (hcont.eventually (hW₃o.mem_nhds (by rw [hya]; exact hyW₃))).and (hdomo.mem_nhds ha₀)
  obtain ⟨ε₂, hε₂, hε₂h⟩ := Metric.eventually_nhds_iff.mp hev
  set ε : ℝ := min (ε₂ / 2) (c δ₀) with hε
  have hεpos : 0 < ε := lt_min (by linarith) hcδ
  have hεc : ε ≤ c δ₀ := min_le_right _ _
  have hεε₂ : ε ≤ ε₂ / 2 := min_le_left _ _
  have hIcc : Icc (a₀ - ε) (a₀ + ε) ⊆ At.dom i := by
    intro b hb
    refine (hε₂h ?_).2
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hb.1, hb.2]
  have hIoo : Ioo (a₀ - ε) (a₀ + ε) ⊆ At.dom i := Ioo_subset_Icc_self.trans hIcc
  have hparW : ∀ b ∈ Ioo (a₀ - ε) (a₀ + ε), At.param i b ∈ W₃ := by
    intro b hb
    refine (hε₂h ?_).1
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hb.1, hb.2]
  obtain ⟨V₀, hV₀, hV₀B⟩ := At.image_relOpen_BCF isOpen_Ioo hIoo
  have hIooa : a₀ ∈ Ioo (a₀ - ε) (a₀ + ε) := ⟨by linarith, by linarith⟩
  have hκy' : At.coord i (γ 0) = a₀ := hκy
  refine ⟨i, σ, ε, V₀ ∩ W₃, hσ, hεpos, ?_, hV₀.inter hW₃o, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [hκy']
  · exact hIcc
  · rw [inter_assoc, inter_comm W₃, ← inter_assoc, hV₀B]
    ext z
    constructor
    · exact fun hz => hz.1
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, hb, rfl⟩, hparW b hb⟩
  · intro z hz
    exact hz.1.2.2
  · exact eq_empty_iff_forall_notMem.mpr fun z hz => hz.1.2.1.1.1 hz.2
  · have : At.param i a₀ ∈ V₀ ∩ Bs := by
      rw [hV₀B]
      exact ⟨a₀, hIooa, rfl⟩
    rw [hya] at this
    exact ⟨this.1, hyW₃⟩
  · intro b hb
    have hbd := hIoo hb
    have hκb : κ (At.param i b) = b := At.coord_param i b hbd
    constructor
    · intro hbT
      have hzW := hparW b hb
      obtain ⟨t, ht, hzt⟩ := hTN ⟨hbT, hzW.1.2⟩
      have htδ : t ≤ δ₀ := by
        by_contra hlt
        exact hzW.1.1.2 ⟨t, ⟨(lt_of_not_ge hlt).le, ht.2⟩, hzt⟩
      have htI : t ∈ Icc 0 δ₀ := ⟨ht.1, htδ⟩
      have hbt : b = a t := by
        change b = κ (γ t)
        rw [hzt, hκb]
      have h0 := hmono.monotoneOn (left_mem_Icc.mpr hδ₀pos.le) htI htI.1
      change c 0 ≤ c t at h0
      rw [hc0] at h0
      change 0 ≤ σ * (a t - a₀) at h0
      rw [← hbt] at h0
      exact h0
    · intro hb0
      have hlt : σ * (b - a₀) ≤ ε := by
        have := hσabs (b - a₀)
        have h2 : |b - a₀| < ε := abs_lt.mpr ⟨by linarith [hb.1], by linarith [hb.2]⟩
        rw [← this] at h2
        exact (le_abs_self _).trans h2.le
      have hmem : σ * (b - a₀) ∈ Icc (c 0) (c δ₀) := ⟨by rw [hc0]; exact hb0, hlt.trans hεc⟩
      obtain ⟨t, ht, hct⟩ := hivt hmem
      have hat : a t = b := by
        have : σ * (a t - a₀) = σ * (b - a₀) := hct
        have := mul_left_cancel₀ hσ0 this
        linarith
      have hγt : γ t = At.param i b := by
        rw [(hpar t ht).1, hat]
      exact hT ⟨t, hsub ht, hγt⟩

end ArcEndChart

section Regular

variable {E HM : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]

/-- The differential of `x ↦ φ (g x)` is onto when `dg` is onto and `φ' ≠ 0`. -/
theorem surjective_mfderiv_scalar_comp_ZSP35 {g : M → ℝ} {φ : ℝ → ℝ} {x : M}
    (hg : MDifferentiableAt I 𝓘(ℝ, ℝ) g x) (hsg : Surjective (mfderiv I 𝓘(ℝ, ℝ) g x))
    (hφ : DifferentiableAt ℝ φ (g x)) (hd : deriv φ (g x) ≠ 0) :
    Surjective (mfderiv I 𝓘(ℝ, ℝ) (fun y => φ (g y)) x) := by
  have h2 := mfderiv_comp (I := I) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, ℝ)) x
    (hφ.mdifferentiableAt) hg
  have hEe : Surjective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ (g x)) := by
    rw [mfderiv_eq_fderiv]
    intro w
    let w' : ℝ := w
    refine ⟨w' / deriv φ (g x), ?_⟩
    change (fderiv ℝ φ (g x)) (w' / deriv φ (g x)) = w'
    rw [fderiv_eq_smul_deriv, smul_eq_mul]
    field_simp
  change Surjective (mfderiv I 𝓘(ℝ, ℝ) (φ ∘ g) x)
  rw [h2]
  exact hEe.comp hsg

/-- A regular zero of a smooth function on a boundaryless manifold is a limit of points where the
function is positive. -/
theorem mem_closure_pos_of_mfderiv_ne_zero_ZSP35 [I.Boundaryless] {h : M → ℝ} {x : M}
    (hh : mfderiv I 𝓘(ℝ, ℝ) h x ≠ 0) : x ∈ closure {y | h x < h y} := by
  by_contra hx
  have hmax : IsLocalMax h x := by
    by_contra hnot
    exact hx (not_isLocalMax_iff_mem_closure_gt.mp hnot)
  have h0 := hmax.mvfderiv_eq_zero (I := I) (BoundarylessManifold.isInteriorPoint (I := I))
  apply hh
  ext v
  have := congrArg (fun L => L v) h0
  change mvfderiv I h x v = 0 at this
  unfold mvfderiv at this
  exact this

end Regular

section DefiningFunction

variable {E HM : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {ι : Type*} {Bs : Set H}

/-- **A regular defining function on the whole tube over the end of a base arc** (S0/ZSP05 smooth
face; the fields `endNear / endFn / endFn_regular / endFn_level / endFn_eq` of draft 74's
`SlimPiecesV2`): for a proper smooth submersion `f` over the graph-atlas base `Bs` and an arc end
`γ 0` of `T` (injective continuous `γ` with `γ '' [0, 1] ⊆ T ⊆ Bs`, isolated in `T`), there are an
open `U ⊆ f⁻¹(Bs)` containing the WHOLE fibre `f⁻¹(γ 0)` and missing `f⁻¹(E')`, and a function `h`,
smooth on `U` with onto differential at every point of `U`, such that `{h = 0} ∩ U = f⁻¹(γ 0)`
(the whole fibre) and `f⁻¹(T) ∩ U = {h ≤ 0} ∩ U`. -/
theorem exists_end_defining_function_ZSP35
    (P : ProperSmoothSurfaceSubmersion_EFE I M ι Bs) {γ : ℝ → H}
    (hγc : ContinuousOn γ (Icc 0 1)) (hinj : InjOn γ (Icc 0 1))
    {T : Set H} (hT : γ '' Icc 0 1 ⊆ T) (hTB : T ⊆ Bs)
    (hiso : ∃ N : Set H, IsOpen N ∧ γ 0 ∈ N ∧ T ∩ N ⊆ γ '' Icc 0 1)
    {E' : Set H} (hE' : IsClosed E') (hyE : γ 0 ∉ E') :
    ∃ (U : Set M) (h : M → ℝ), IsOpen U ∧ P.toFun ⁻¹' {γ 0} ⊆ U ∧ U ⊆ P.toFun ⁻¹' Bs ∧
      Disjoint U (P.toFun ⁻¹' E') ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ h U ∧
      (∀ x ∈ U, Surjective (mfderiv I 𝓘(ℝ, ℝ) h x)) ∧
      {x | x ∈ U ∧ h x = 0} = P.toFun ⁻¹' {γ 0} ∧
      U ∩ P.toFun ⁻¹' T = {x | x ∈ U ∧ h x ≤ 0} := by
  obtain ⟨i, σ, ε, V, hσ, hε, hIcc, hV, hVB, hVR, hVE, hyV, hside⟩ :=
    exists_arc_end_chart_ZSP35 P.atlas P.region P.isOpen_region P.region_cover P.region_piece
      hγc hinj hT hTB hiso hE' hyE
  set κ := P.atlas.coord i with hκ
  set a₀ : ℝ := κ (γ 0) with ha₀
  have hσ0 : σ ≠ 0 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hfc := P.smooth.continuous
  have hUo : IsOpen (P.toFun ⁻¹' V ∩ P.toFun ⁻¹' Bs) :=
    (hV.preimage hfc).inter P.isOpen_source
  have hUB : ∀ x, x ∈ P.toFun ⁻¹' V ∩ P.toFun ⁻¹' Bs →
      ∃ b ∈ Ioo (a₀ - ε) (a₀ + ε), P.toFun x = P.atlas.param i b := by
    intro x hx
    have : P.toFun x ∈ V ∩ Bs := hx
    rw [hVB] at this
    obtain ⟨b, hb, hxb⟩ := this
    exact ⟨b, hb, hxb.symm⟩
  have hκparam : ∀ b ∈ Ioo (a₀ - ε) (a₀ + ε), κ (P.atlas.param i b) = b := fun b hb =>
    P.atlas.coord_param i b (Ioo_subset_Icc_self.trans hIcc hb)
  have hy0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hyB : γ 0 ∈ Bs := hTB (hT ⟨0, hy0, rfl⟩)
  have hpa : P.atlas.param i a₀ = γ 0 := by
    have : γ 0 ∈ V ∩ Bs := ⟨hyV, hyB⟩
    rw [hVB] at this
    obtain ⟨b, hb, hbγ⟩ := this
    have hb' : κ (γ 0) = b := by rw [← hbγ]; exact hκparam b hb
    have : a₀ = b := hb'
    rw [this, hbγ]
  have hga : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => κ (P.toFun x)) :=
    κ.contDiff.comp_contMDiff P.smooth
  have hφ : ContDiff ℝ ∞ (fun s : ℝ => σ * (a₀ - s)) :=
    contDiff_const.mul (contDiff_const.sub contDiff_id)
  refine ⟨P.toFun ⁻¹' V ∩ P.toFun ⁻¹' Bs, fun x => σ * (a₀ - κ (P.toFun x)), hUo, ?_,
    inter_subset_right, ?_, (hφ.comp_contMDiff hga).contMDiffOn, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : P.toFun x = γ 0 := hx
    exact ⟨show P.toFun x ∈ V by rw [hx']; exact hyV, show P.toFun x ∈ Bs by rw [hx']; exact hyB⟩
  · refine disjoint_left.mpr fun x hx hxE => ?_
    have : P.toFun x ∈ V ∩ E' := ⟨hx.1, hxE⟩
    rw [hVE] at this
    exact this
  · intro x hx
    have hxR : P.toFun x ∈ P.region i ∩ Bs := ⟨hVR ⟨hx.1, hx.2⟩, hx.2⟩
    have hsub := P.submersion i x hxR
    have hmd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => κ (P.toFun y)) x :=
      (hga x).mdifferentiableAt (by decide)
    have hdφ : deriv (fun s : ℝ => σ * (a₀ - s)) (κ (P.toFun x)) ≠ 0 := by
      have : deriv (fun s : ℝ => σ * (a₀ - s)) (κ (P.toFun x)) = -σ := by simp
      rw [this]
      exact neg_ne_zero.mpr hσ0
    exact surjective_mfderiv_scalar_comp_ZSP35 (φ := fun s : ℝ => σ * (a₀ - s)) hmd hsub
      (hφ.differentiable (by decide) _) hdφ
  · ext x
    constructor
    · rintro ⟨hx, hx0⟩
      obtain ⟨b, hb, hxb⟩ := hUB x hx
      have hκx : κ (P.toFun x) = b := by rw [hxb]; exact hκparam b hb
      have hba : b = a₀ := by
        have : σ * (a₀ - κ (P.toFun x)) = 0 := hx0
        have h2 := (mul_eq_zero.mp this).resolve_left hσ0
        linarith
      change P.toFun x = γ 0
      rw [hxb, hba, hpa]
    · intro hx
      have hx' : P.toFun x = γ 0 := hx
      refine ⟨⟨show P.toFun x ∈ V by rw [hx']; exact hyV,
        show P.toFun x ∈ Bs by rw [hx']; exact hyB⟩, ?_⟩
      change σ * (a₀ - κ (P.toFun x)) = 0
      rw [hx']
      simp [ha₀]
  · ext x
    constructor
    · rintro ⟨hx, hxT⟩
      refine ⟨hx, ?_⟩
      obtain ⟨b, hb, hxb⟩ := hUB x hx
      have hκx : κ (P.toFun x) = b := by rw [hxb]; exact hκparam b hb
      have h1 : 0 ≤ σ * (b - a₀) := (hside b hb).mp (hxb ▸ hxT)
      change σ * (a₀ - κ (P.toFun x)) ≤ 0
      rw [hκx]
      nlinarith
    · rintro ⟨hx, hxh⟩
      refine ⟨hx, ?_⟩
      obtain ⟨b, hb, hxb⟩ := hUB x hx
      have hκx : κ (P.toFun x) = b := by rw [hxb]; exact hκparam b hb
      have hxh' : σ * (a₀ - b) ≤ 0 := by
        have : σ * (a₀ - κ (P.toFun x)) ≤ 0 := hxh
        rwa [hκx] at this
      change P.toFun x ∈ T
      rw [hxb]
      exact (hside b hb).mpr (by nlinarith)

end DefiningFunction

section ArcEnds

variable {E HM : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {ι : Type*} {Bs : Set H}

/-- The union of all arc ends of a smooth compact one-dimensional domain, minus the point `y`. -/
theorem isClosed_otherEnds_ZSP35 (D : SmoothCompactOneDomain_BCF Bs) (y : H) :
    IsClosed ((⋃ k : Fin D.m, ({D.arc k 0, D.arc k 1} : Set H)) \ {y}) := by
  refine Set.Finite.isClosed (Set.Finite.sdiff ?_)
  exact Set.finite_iUnion fun k => (Set.finite_singleton _).insert _

/-- The isolation of an arc inside a smooth compact one-dimensional domain: a neighbourhood of any
point `y` of the arc `k` meets the carrier only in the arc. -/
theorem arc_isolated_ZSP35 (D : SmoothCompactOneDomain_BCF Bs) (k : Fin D.m) {y : H}
    (hy : y ∈ D.arc k '' Icc 0 1) :
    ∃ N : Set H, IsOpen N ∧ y ∈ N ∧ D.carrier ∩ N ⊆ D.arc k '' Icc 0 1 := by
  have hcmp : IsCompact ((⋃ k' : {k' : Fin D.m // k' ≠ k}, D.arc k'.1 '' Icc 0 1) ∪
      ⋃ j : Fin D.l, range (D.loop j)) := by
    refine (isCompact_iUnion fun k' : {k' : Fin D.m // k' ≠ k} =>
      isCompact_Icc.image_of_continuousOn (D.arc_smooth k'.1).continuousOn).union
      (isCompact_iUnion fun j => ?_)
    rw [← (D.loop_periodic j).image_Icc one_pos 0]
    exact isCompact_Icc.image (D.loop_smooth j).continuous
  refine ⟨((⋃ k' : {k' : Fin D.m // k' ≠ k}, D.arc k'.1 '' Icc 0 1) ∪
      ⋃ j : Fin D.l, range (D.loop j))ᶜ, hcmp.isClosed.isOpen_compl, ?_, ?_⟩
  · rintro (hk' | hl)
    · obtain ⟨⟨k', hne⟩, hk'⟩ := mem_iUnion.mp hk'
      exact disjoint_left.mp (D.arc_disjoint hne) hk' hy
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hl
      exact disjoint_left.mp (D.arc_loop_disjoint k j) hy hj
  · intro z ⟨hz, hzN⟩
    rw [D.carrier_eq] at hz
    rcases hz with hz | hz
    · obtain ⟨k', hk'⟩ := mem_iUnion.mp hz
      by_cases hkk : k' = k
      · subst hkk
        exact hk'
      · exact absurd (Or.inl (mem_iUnion.mpr ⟨⟨k', hkk⟩, hk'⟩)) hzN
    · exact absurd (Or.inr hz) hzN

/-- **The tube over an arc end of a smooth compact one-dimensional domain** (S0 / ZSP05 free end):
for a proper smooth submersion `f` over the base `Bs`, an end `y` of an arc of `D` and an open
`G ∋ y`, there are an open `U ⊆ f⁻¹(G ∩ Bs)` containing the whole fibre `f⁻¹(y)` and missing the
fibres over the other ends, and a function `h`, smooth on `U` with onto differential, such that
`{h = 0} ∩ U = f⁻¹(y)` and `f⁻¹(D) ∩ U = {h ≤ 0} ∩ U`. -/
theorem exists_arc_end_tube_ZSP35
    (P : ProperSmoothSurfaceSubmersion_EFE I M ι Bs) (D : SmoothCompactOneDomain_BCF Bs)
    {y : H} (hy : ∃ k : Fin D.m, y = D.arc k 0 ∨ y = D.arc k 1) {G : Set H} (hG : IsOpen G)
    (hyG : y ∈ G) :
    ∃ (U : Set M) (h : M → ℝ), IsOpen U ∧ P.toFun ⁻¹' {y} ⊆ U ∧ U ⊆ P.toFun ⁻¹' (G ∩ Bs) ∧
      Disjoint U (P.toFun ⁻¹' ((⋃ k : Fin D.m, ({D.arc k 0, D.arc k 1} : Set H)) \ {y})) ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ h U ∧ (∀ x ∈ U, Surjective (mfderiv I 𝓘(ℝ, ℝ) h x)) ∧
      {x | x ∈ U ∧ h x = 0} = P.toFun ⁻¹' {y} ∧
      U ∩ P.toFun ⁻¹' D.carrier = {x | x ∈ U ∧ h x ≤ 0} := by
  obtain ⟨k, hk⟩ := hy
  have hcarr : ∀ k : Fin D.m, D.arc k '' Icc 0 1 ⊆ D.carrier := fun k z hz => by
    rw [D.carrier_eq]
    exact Or.inl (mem_iUnion.mpr ⟨k, hz⟩)
  have hE : IsClosed (((⋃ k : Fin D.m, ({D.arc k 0, D.arc k 1} : Set H)) \ {y}) ∪ Gᶜ) :=
    (isClosed_otherEnds_ZSP35 D y).union hG.isClosed_compl
  have hyE : y ∉ ((⋃ k : Fin D.m, ({D.arc k 0, D.arc k 1} : Set H)) \ {y}) ∪ Gᶜ :=
    fun h => h.elim (fun h => h.2 rfl) (fun h => h hyG)
  have hmain : ∃ (U : Set M) (h : M → ℝ), IsOpen U ∧ P.toFun ⁻¹' {y} ⊆ U ∧
      U ⊆ P.toFun ⁻¹' Bs ∧
      Disjoint U (P.toFun ⁻¹' (((⋃ k : Fin D.m, ({D.arc k 0, D.arc k 1} : Set H)) \ {y}) ∪ Gᶜ)) ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ h U ∧ (∀ x ∈ U, Surjective (mfderiv I 𝓘(ℝ, ℝ) h x)) ∧
      {x | x ∈ U ∧ h x = 0} = P.toFun ⁻¹' {y} ∧
      U ∩ P.toFun ⁻¹' D.carrier = {x | x ∈ U ∧ h x ≤ 0} := by
    rcases hk with hk | hk
    · subst hk
      have hy0 : D.arc k 0 ∈ D.arc k '' Icc 0 1 := ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
      exact exists_end_defining_function_ZSP35 P (D.arc_smooth k).continuousOn (D.arc_injOn k)
        (hcarr k) D.subset_base (arc_isolated_ZSP35 D k hy0) hE hyE
    · subst hk
      have hy1 : D.arc k 1 ∈ D.arc k '' Icc 0 1 := ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
      have hrev : (fun s : ℝ => D.arc k (1 - s)) '' Icc 0 1 = D.arc k '' Icc 0 1 := by
        ext z
        constructor
        · rintro ⟨s, hs, rfl⟩
          exact ⟨1 - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, rfl⟩
        · rintro ⟨t, ht, rfl⟩
          exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by simp⟩
      have hiso : ∃ N : Set H, IsOpen N ∧ (fun s : ℝ => D.arc k (1 - s)) 0 ∈ N ∧
          D.carrier ∩ N ⊆ (fun s : ℝ => D.arc k (1 - s)) '' Icc 0 1 := by
        obtain ⟨N, hN, hyN, hNs⟩ := arc_isolated_ZSP35 D k hy1
        exact ⟨N, hN, by simpa using hyN, by rw [hrev]; exact hNs⟩
      have hcont : ContinuousOn (fun s : ℝ => D.arc k (1 - s)) (Icc 0 1) :=
        (D.arc_smooth k).continuousOn.comp (by fun_prop) (fun s hs =>
          ⟨by linarith [hs.2], by linarith [hs.1]⟩)
      have hinj : InjOn (fun s : ℝ => D.arc k (1 - s)) (Icc 0 1) := by
        intro s hs t ht hst
        have := D.arc_injOn k ⟨by linarith [hs.2], by linarith [hs.1]⟩
          ⟨by linarith [ht.2], by linarith [ht.1]⟩ hst
        linarith
      have := exists_end_defining_function_ZSP35 P hcont hinj
        (T := D.carrier) (by rw [hrev]; exact hcarr k) D.subset_base hiso
        (E' := ((⋃ k : Fin D.m, ({D.arc k 0, D.arc k 1} : Set H)) \ {D.arc k 1}) ∪ Gᶜ) hE
        (by simpa using hyE)
      simpa using this
  obtain ⟨U, h, hUo, hfU, hUB, hUE, hh, hsurj, hlev, hside⟩ := hmain
  refine ⟨U, h, hUo, hfU, ?_, ?_, hh, hsurj, hlev, hside⟩
  · intro x hx
    have hxB := hUB hx
    have hxG : P.toFun x ∈ G := by
      by_contra hxG
      exact disjoint_left.mp hUE hx (Or.inr hxG)
    exact ⟨hxG, hxB⟩
  · refine disjoint_left.mpr fun x hx hxe => ?_
    exact disjoint_left.mp hUE hx (Or.inl hxe)

end ArcEnds

end DifferentialGeometry.Topology.Ehresmann
