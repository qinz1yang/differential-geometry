import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

set_option autoImplicit false

noncomputable section


open Filter Function Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

def isLiftOn
    (F : E → M) (γ : Real → M) (U : Set E)
    (e₀ : E) (a t : Real) (η : Real → E) : Prop :=
  ContinuousOn η (Set.Icc a t) ∧
    η a = e₀ ∧
    ∀ s ∈ Set.Icc a t, η s ∈ U ∧ F (η s) = γ s

namespace isLiftOn

variable {F : E → M} {γ : Real → M} {U : Set E}
  {e₀ : E} {a b : Real} {η ζ : Real → E}

omit [NormedSpace Real E] [TopologicalSpace M] in
theorem continuousOn
    (hη : isLiftOn F γ U e₀ a b η) :
    ContinuousOn η (Set.Icc a b) :=
  hη.1

omit [NormedSpace Real E] [TopologicalSpace M] in
theorem mapsTo
    (hη : isLiftOn F γ U e₀ a b η) :
    Set.MapsTo η (Set.Icc a b) U :=
  fun s hs ↦ (hη.2.2 s hs).1

omit [IsManifold I ∞ M] in
theorem extend
    {t u : Real}
    (hat : a ≤ t)
    (hγ : ContinuousOn γ (Set.Icc a u))
    (hη : isLiftOn F γ U e₀ a t η)
    (φ : PartialDiffeomorph 𝓘(Real, E) I E M ∞)
    (htφ : η t ∈ φ.source)
    (hφeq : Set.EqOn F φ φ.source)
    (hγtarget : Set.MapsTo γ (Set.Icc t u) φ.target)
    (hbranchU :
      Set.MapsTo ((φ.symm : M → E) ∘ γ) (Set.Icc t u) U) :
    ∃ ζ : Real → E, isLiftOn F γ U e₀ a u ζ := by
  classical
  let branch : Real → E := (φ.symm : M → E) ∘ γ
  let ζ : Real → E := Set.piecewise (Set.Iic t) η branch
  have hγtu : ContinuousOn γ (Set.Icc t u) :=
    hγ.mono fun s hs ↦ ⟨hat.trans hs.1, hs.2⟩
  have hbranch_cont : ContinuousOn branch (Set.Icc t u) :=
    φ.contMDiffOn_invFun.continuousOn.comp hγtu hγtarget
  have hjoin : η t = branch t := by
    change η t = φ.symm (γ t)
    rw [← (hη.2.2 t ⟨hat, le_rfl⟩).2, hφeq htφ]
    exact (φ.left_inv htφ).symm
  have hζcont : ContinuousOn ζ (Set.Icc a u) := by
    apply ContinuousOn.piecewise
    · intro s hs
      have hs_eq : s = t := by
        exact Set.mem_singleton_iff.mp (frontier_Iic_subset t hs.2)
      simpa only [hs_eq] using hjoin
    · rw [closure_Iic]
      exact hη.continuousOn.mono fun s hs ↦
        ⟨hs.1.1, hs.2⟩
    · rw [compl_Iic, closure_Ioi]
      exact hbranch_cont.mono fun s hs ↦
        ⟨hs.2, hs.1.2⟩
  refine ⟨ζ, hζcont, ?_, ?_⟩
  · change Set.piecewise (Set.Iic t) η branch a = e₀
    rw [(Set.Iic t).piecewise_eq_of_mem η branch
      (show a ∈ Set.Iic t from hat)]
    exact hη.2.1
  · intro s hs
    rcases le_total s t with hst | hts
    · have hs_old : s ∈ Set.Icc a t := ⟨hs.1, hst⟩
      have hζs : ζ s = η s := by
        exact (Set.Iic t).piecewise_eq_of_mem η branch
          (show s ∈ Set.Iic t from hst)
      rw [hζs]
      exact hη.2.2 s hs_old
    · have hs_new : s ∈ Set.Icc t u := ⟨hts, hs.2⟩
      have hζs : ζ s = branch s := by
        rcases hts.eq_or_lt with rfl | hlt
        · change Set.piecewise (Set.Iic t) η branch t = branch t
          rw [(Set.Iic t).piecewise_eq_of_mem η branch
            (Set.mem_Iic.mpr (le_refl t)), hjoin]
        · exact (Set.Iic t).piecewise_eq_of_notMem η branch
            (show s ∉ Set.Iic t from not_le.mpr hlt)
      rw [hζs]
      refine ⟨hbranchU hs_new, ?_⟩
      have htarget : γ s ∈ φ.target := hγtarget hs_new
      have hsource : branch s ∈ φ.source := φ.map_target htarget
      rw [hφeq hsource]
      exact φ.right_inv htarget

omit [IsManifold I ∞ M] in
theorem contDiffOn
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞ F U)
    (hγ :
      ContMDiffOn 𝓘(Real, Real) I 1 γ (Set.Icc a b))
    (hη : isLiftOn F γ U e₀ a b η) :
    ContDiffOn Real 1 η (Set.Icc a b) := by
  intro x hx
  have hxU : η x ∈ U := hη.mapsTo hx
  obtain ⟨φ, hxφ, hφeq⟩ := hloc ⟨η x, hxU⟩
  have hxTarget : γ x ∈ φ.target := by
    rw [← (hη.2.2 x hx).2, hφeq hxφ]
    exact φ.map_source hxφ
  have hφsymm :
      ContMDiffAt I 𝓘(Real, E) 1 (φ.symm : M → E) (γ x) :=
    (φ.contMDiffOn_invFun.contMDiffAt
      (φ.open_target.mem_nhds hxTarget)).of_le (by norm_num)
  have hbranch :
      ContDiffWithinAt Real 1 ((φ.symm : M → E) ∘ γ)
        (Set.Icc a b) x :=
    (hφsymm.comp_contMDiffWithinAt x (hγ x hx)).contDiffWithinAt
  have hevSrc : ∀ᶠ y in 𝓝[Set.Icc a b] x, η y ∈ φ.source :=
    (hη.continuousOn x hx).preimage_mem_nhdsWithin
      (φ.open_source.mem_nhds hxφ)
  have heq :
      η =ᶠ[𝓝[Set.Icc a b] x] ((φ.symm : M → E) ∘ γ) := by
    filter_upwards [hevSrc, self_mem_nhdsWithin] with y hySrc hy
    change η y = φ.symm (γ y)
    rw [← (hη.2.2 y hy).2, hφeq hySrc]
    exact (φ.left_inv hySrc).symm
  exact hbranch.congr_of_eventuallyEq heq (heq.eq_of_nhdsWithin hx)

omit [IsManifold I ∞ M] in
theorem eqOn_of_eq
    {e₁ e₂ : E} {t₀ : Real}
    (hU : IsOpen U)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞ F U)
    (hη : isLiftOn F γ U e₁ a b η)
    (hζ : isLiftOn F γ U e₂ a b ζ)
    (ht₀ : t₀ ∈ Set.Icc a b)
    (heq₀ : η t₀ = ζ t₀) :
    Set.EqOn η ζ (Set.Icc a b) := by
  let Uo : Opens E := ⟨U, hU⟩
  let fU : Uo → M := fun x ↦ F x
  have hlocU :
      IsLocalDiffeomorph 𝓘(Real, E) I ∞ fU :=
    isLocalDiffeomorph_restrict_open Uo hloc
  let ηU : Set.Icc a b → Uo :=
    fun s ↦ ⟨η s, hη.mapsTo s.property⟩
  let ζU : Set.Icc a b → Uo :=
    fun s ↦ ⟨ζ s, hζ.mapsTo s.property⟩
  have hηU : Continuous ηU := by
    exact (continuousOn_iff_continuous_domRestrict.mp hη.continuousOn).codRestrict
      (fun s ↦ hη.mapsTo s.property)
  have hζU : Continuous ζU := by
    exact (continuousOn_iff_continuous_domRestrict.mp hζ.continuousOn).codRestrict
      (fun s ↦ hζ.mapsTo s.property)
  have hcomp : fU ∘ ηU = fU ∘ ζU := by
    funext s
    exact (hη.2.2 s s.property).2.trans (hζ.2.2 s s.property).2.symm
  let : PreconnectedSpace (Set.Icc a b) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hpoint : ηU ⟨t₀, ht₀⟩ = ζU ⟨t₀, ht₀⟩ := by
    apply Subtype.ext
    exact heq₀
  have heq : ηU = ζU :=
    (T2Space.isSeparatedMap fU).eq_of_comp_eq
      hlocU.isLocalHomeomorph.isLocallyInjective
      hηU hζU hcomp ⟨t₀, ht₀⟩ hpoint
  intro s hs
  have := congrFun heq ⟨s, hs⟩
  exact congrArg Subtype.val this

omit [IsManifold I ∞ M] in
theorem eqOn
    (hab : a ≤ b) (hU : IsOpen U)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞ F U)
    (hη : isLiftOn F γ U e₀ a b η)
    (hζ : isLiftOn F γ U e₀ a b ζ) :
    Set.EqOn η ζ (Set.Icc a b) :=
  eqOn_of_eq hU hloc hη hζ ⟨le_rfl, hab⟩
    (hη.2.1.trans hζ.2.1.symm)

omit [IsManifold I ∞ M] in
theorem exists_of_compact
    [T2Space M]
    {K : Set E}
    (hab : a ≤ b) (hU : IsOpen U)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞ F U)
    (hγ : ContinuousOn γ (Set.Icc a b))
    (he₀U : e₀ ∈ U) (hγa : F e₀ = γ a)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hfence :
      ∀ {t : Real}, t ∈ Set.Icc a b →
        ∀ {η : Real → E}, isLiftOn F γ U e₀ a t η → η t ∈ K) :
    ∃ η : Real → E, isLiftOn F γ U e₀ a b η := by
  classical
  let S : Set Real :=
    {t | t ∈ Set.Icc a b ∧ ∃ η : Real → E, isLiftOn F γ U e₀ a t η}
  have haS : a ∈ S := by
    refine ⟨⟨le_rfl, hab⟩, fun _ ↦ e₀, continuousOn_const, rfl, ?_⟩
    intro s hs
    have hs_eq : s = a := le_antisymm hs.2 hs.1
    subst s
    exact ⟨he₀U, hγa⟩
  have hSne : S.Nonempty := ⟨a, haS⟩
  have hSbdd : BddAbove S := ⟨b, fun t ht ↦ ht.1.2⟩
  let t₀ : Real := sSup S
  have hat₀ : a ≤ t₀ := le_csSup hSbdd haS
  have ht₀b : t₀ ≤ b := csSup_le hSne (fun t ht ↦ ht.1.2)
  have ht₀Icc : t₀ ∈ Set.Icc a b := ⟨hat₀, ht₀b⟩
  have ht₀S : t₀ ∈ S := by
    rcases hat₀.eq_or_lt with hat₀eq | hat₀lt
    · rw [← hat₀eq]
      exact haS
    · have ht₀cl : t₀ ∈ closure S := csSup_mem_closure hSne hSbdd
      obtain ⟨u, huS, hutend⟩ := mem_closure_iff_seq_limit.mp ht₀cl
      let ηn : Nat → Real → E := fun n ↦ Classical.choose (huS n).2
      have hηn : ∀ n, isLiftOn F γ U e₀ a (u n) (ηn n) :=
        fun n ↦ Classical.choose_spec (huS n).2
      let zseq : Nat → E := fun n ↦ ηn n (u n)
      have hzseqK : ∀ n, zseq n ∈ K :=
        fun n ↦ hfence (huS n).1 (hηn n)
      obtain ⟨z, hzK, ψ, hψmono, hzψtend⟩ :=
        hK.tendsto_subseq hzseqK
      have hzU : z ∈ U := hKU hzK
      have huψtend : Tendsto (u ∘ ψ) atTop (𝓝 t₀) :=
        hutend.comp hψmono.tendsto_atTop
      have huψIcc : ∀ n, u (ψ n) ∈ Set.Icc a b :=
        fun n ↦ (huS (ψ n)).1
      have hγψtend : Tendsto (γ ∘ u ∘ ψ) atTop (𝓝 (γ t₀)) := by
        exact (hγ t₀ ht₀Icc).tendsto.comp <|
          tendsto_nhdsWithin_iff.mpr
            ⟨huψtend, Filter.Eventually.of_forall huψIcc⟩
      have hFψtend :
          Tendsto (F ∘ zseq ∘ ψ) atTop (𝓝 (F z)) := by
        exact (hloc ⟨z, hzU⟩).contMDiffAt.continuousAt.tendsto.comp hzψtend
      have hFz : F z = γ t₀ := by
        apply tendsto_nhds_unique hFψtend
        convert hγψtend using 1
        funext n
        exact (hηn (ψ n)).2.2 (u (ψ n))
          ⟨(huS (ψ n)).1.1, le_rfl⟩ |>.2
      obtain ⟨φ, hzφ, hφeq⟩ := hloc ⟨z, hzU⟩
      let V : Set M := φ.target ∩ (φ.symm : M → E) ⁻¹' U
      have hVopen : IsOpen V := by
        exact φ.symm.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
          φ.open_target hU
      have hγt₀V : γ t₀ ∈ V := by
        refine ⟨?_, ?_⟩
        · rw [← hFz, hφeq hzφ]
          exact φ.map_source hzφ
        · change φ.symm (γ t₀) ∈ U
          rw [← hFz, hφeq hzφ]
          have hleft : φ.symm (φ z) = z := by
            change φ.toPartialEquiv.symm (φ.toPartialEquiv z) = z
            exact φ.toPartialEquiv.left_inv hzφ
          rw [hleft]
          exact hzU
      have hpre : γ ⁻¹' V ∈ 𝓝[Set.Icc a b] t₀ :=
        (hγ t₀ ht₀Icc).preimage_mem_nhdsWithin
          (hVopen.mem_nhds hγt₀V)
      rw [mem_nhdsWithin] at hpre
      obtain ⟨W, hWopen, ht₀W, hWsub⟩ := hpre
      obtain ⟨c, d, ht₀cd, hcdW⟩ :=
        mem_nhds_iff_exists_Ioo_subset.mp (hWopen.mem_nhds ht₀W)
      have hzψsrc : ∀ᶠ n in atTop, zseq (ψ n) ∈ φ.source :=
        hzψtend (φ.open_source.mem_nhds hzφ)
      have huψcd : ∀ᶠ n in atTop, u (ψ n) ∈ Set.Ioo c d :=
        huψtend (isOpen_Ioo.mem_nhds ht₀cd)
      obtain ⟨n, hnz, hnu⟩ := (hzψsrc.and huψcd).exists
      have hun_le : u (ψ n) ≤ t₀ :=
        le_csSup hSbdd (huS (ψ n))
      rcases hun_le.eq_or_lt with hun_eq | hun_lt
      · rw [← hun_eq]
        exact huS (ψ n)
      · have hgood :
            ∀ s ∈ Set.Icc (u (ψ n)) t₀, γ s ∈ V := by
          intro s hs
          apply hWsub
          refine ⟨hcdW ?_, ?_⟩
          · exact ⟨hnu.1.trans_le hs.1, hs.2.trans_lt ht₀cd.2⟩
          · exact ⟨(huS (ψ n)).1.1.trans hs.1, hs.2.trans ht₀b⟩
        obtain ⟨η₀, hη₀⟩ :=
          (hηn (ψ n)).extend (huS (ψ n)).1.1
            (hγ.mono (Set.Icc_subset_Icc le_rfl ht₀b))
            φ hnz hφeq
            (fun s hs ↦ (hgood s hs).1)
            (fun s hs ↦ (hgood s hs).2)
        exact ⟨ht₀Icc, η₀, hη₀⟩
  have ht₀eq : t₀ = b := by
    apply le_antisymm ht₀b
    by_contra hnot
    have ht₀ltb : t₀ < b := lt_of_not_ge hnot
    obtain ⟨η₀, hη₀⟩ := ht₀S.2
    have hzU : η₀ t₀ ∈ U :=
      hη₀.mapsTo ⟨hat₀, le_rfl⟩
    obtain ⟨φ, hzφ, hφeq⟩ := hloc ⟨η₀ t₀, hzU⟩
    let V : Set M := φ.target ∩ (φ.symm : M → E) ⁻¹' U
    have hVopen : IsOpen V := by
      exact φ.symm.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
        φ.open_target hU
    have hγt₀V : γ t₀ ∈ V := by
      refine ⟨?_, ?_⟩
      · rw [← (hη₀.2.2 t₀ ⟨hat₀, le_rfl⟩).2, hφeq hzφ]
        exact φ.map_source hzφ
      · change φ.symm (γ t₀) ∈ U
        rw [← (hη₀.2.2 t₀ ⟨hat₀, le_rfl⟩).2, hφeq hzφ]
        have hleft : φ.symm (φ (η₀ t₀)) = η₀ t₀ := by
          change φ.toPartialEquiv.symm (φ.toPartialEquiv (η₀ t₀)) = η₀ t₀
          exact φ.toPartialEquiv.left_inv hzφ
        rw [hleft]
        exact hzU
    have hpre : γ ⁻¹' V ∈ 𝓝[Set.Icc a b] t₀ :=
      (hγ t₀ ht₀Icc).preimage_mem_nhdsWithin
        (hVopen.mem_nhds hγt₀V)
    have hIcoSub : Set.Ico t₀ b ⊆ Set.Icc a b :=
      fun s hs ↦ ⟨hat₀.trans hs.1, hs.2.le⟩
    have hright : γ ⁻¹' V ∈ 𝓝[Set.Ico t₀ b] t₀ :=
      (nhdsWithin_mono t₀ hIcoSub) hpre
    rw [nhdsWithin_Ico_eq_nhdsGE ht₀ltb,
      mem_nhdsGE_iff_exists_Icc_subset] at hright
    obtain ⟨u, ht₀u, huV⟩ := hright
    let u₁ : Real := min u b
    have ht₀u₁ : t₀ < u₁ := lt_min ht₀u ht₀ltb
    have hu₁b : u₁ ≤ b := min_le_right _ _
    have hu₁u : u₁ ≤ u := min_le_left _ _
    have hgood : ∀ s ∈ Set.Icc t₀ u₁, γ s ∈ V :=
      fun s hs ↦ huV ⟨hs.1, hs.2.trans hu₁u⟩
    obtain ⟨η₁, hη₁⟩ :=
      hη₀.extend hat₀
        (hγ.mono (Set.Icc_subset_Icc le_rfl hu₁b))
        φ hzφ hφeq
        (fun s hs ↦ (hgood s hs).1)
        (fun s hs ↦ (hgood s hs).2)
    have hu₁S : u₁ ∈ S :=
      ⟨⟨hat₀.trans ht₀u₁.le, hu₁b⟩, η₁, hη₁⟩
    exact (not_le.mpr ht₀u₁) (le_csSup hSbdd hu₁S)
  rw [← ht₀eq]
  exact ht₀S.2

end isLiftOn

end DifferentialGeometry
