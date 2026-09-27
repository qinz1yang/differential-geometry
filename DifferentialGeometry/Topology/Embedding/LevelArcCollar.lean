import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.InverseFunction.ContDiffOn
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod

open Set Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology

private theorem isLocalDiffeomorphAt_of_regular_level_columns
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 2)
    {F : ℝ × ℝ → E} {f : E → ℝ} {U : Set (ℝ × ℝ)} {p : ℝ × ℝ}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (hp : p ∈ U)
    {v : E} {c : ℝ} (hv : v ≠ 0) (hc : c ≠ 0)
    (hcol : fderiv ℝ F p (0, 1) = v)
    (hdf : (fderiv ℝ f (F p)).comp (fderiv ℝ F p) =
      c • ContinuousLinearMap.fst ℝ ℝ ℝ) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ F p := by
  let L := fderiv ℝ F p
  have hLi : Function.Injective L := by
    apply (injective_iff_map_eq_zero L).mpr
    intro z hz
    have hz₁ : z.1 = 0 := by
      have he := congrArg (fun A : (ℝ × ℝ) →L[ℝ] ℝ => A z) hdf
      change fderiv ℝ f (F p) (L z) = c * z.1 at he
      rw [hz, map_zero] at he
      exact (mul_eq_zero.mp he.symm).resolve_left hc
    have hz₂ : z.2 = 0 := by
      have he : L z = z.2 • v := by
        calc
          L z = L (z.2 • ((0, 1) : ℝ × ℝ)) := congrArg L (by ext <;> simp [hz₁])
          _ = z.2 • v := by rw [map_smul]; exact congrArg (fun w : E => z.2 • w) hcol
      rw [he] at hz
      exact (smul_eq_zero.mp hz).resolve_right hv
    exact Prod.ext hz₁ hz₂
  have hdim' : Module.finrank ℝ (ℝ × ℝ) = Module.finrank ℝ E := by
    rw [hdim, Module.finrank_prod]
    norm_num
  have hLs : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim').mp hLi
  let A := ContinuousLinearEquiv.ofBijective L
    (LinearMap.ker_eq_bot.mpr hLi) (LinearMap.range_eq_top.mpr hLs)
  exact Manifold.isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv F
    hF.contMDiffOn hU p hp A ((hF.contDiffAt (hU.mem_nhds hp)).differentiableAt
      (by simp)).hasFDerivAt.hasMFDerivAt

private theorem isLocalDiffeomorphAt_level_parameter
    {E : Type*}
    {F : ℝ × ℝ → E} {f : E → ℝ} {U : Set (ℝ × ℝ)} {p : ℝ × ℝ}
    (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ (fun z => (f (F z), z.2)) U) (hp : p ∈ U)
    {c : ℝ} (hc : c ≠ 0)
    (hdf : fderiv ℝ (fun z => f (F z)) p = c • ContinuousLinearMap.fst ℝ ℝ ℝ) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun z => (f (F z), z.2)) p := by
  let A : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 c hc)).prodCongr
      (ContinuousLinearEquiv.refl ℝ ℝ)
  have hh := ((hH.contDiffAt (hU.mem_nhds hp)).fst.differentiableAt (by simp)).hasFDerivAt.prodMk
    (hasFDerivAt_snd (p := p))
  have hA : HasFDerivAt (fun z => (f (F z), z.2)) (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p := by
    apply hh.congr_fderiv
    rw [hdf]
    ext <;> simp [A, mul_comm]
  exact Manifold.isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv
    (fun z => (f (F z), z.2)) hH.contMDiffOn hU p hp A hA.hasMFDerivAt

private theorem exists_partialDiffeomorph_level_rectification
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × ℝ → E} {f : E → ℝ} {β : ℝ → E} {a l r : ℝ}
    (hlr : l ≤ r) (hβinj : InjOn β (Icc l r))
    (hbase : ∀ u ∈ Icc l r, F (a, u) = β u)
    (hlevel : ∀ u ∈ Icc l r, f (β u) = a)
    {O : Set E} (hO : IsOpen O) (hβO : β '' Icc l r ⊆ O)
    (hF : IsLocalDiffeomorphOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ F ({a} ×ˢ Icc l r))
    (hH : IsLocalDiffeomorphOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun p => (f (F p), p.2)) ({a} ×ˢ Icc l r))
    (χ : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (ℝ × ℝ) E ∞)
    (hχ : ∀ p ∈ χ.source, f (χ p) = p.1)
    (hcorners : ∀ u ∈ ({l, r} : Set ℝ), (a, u) ∈ χ.source ∧
      F =ᶠ[𝓝 (a, u)] χ) :
    ∃ D : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (ℝ × ℝ) E ∞,
      {a} ×ˢ Icc l r ⊆ D.source ∧ D.target ⊆ O ∧
      (∀ u ∈ Icc l r, D (a, u) = β u) ∧
      (∀ p ∈ D.source, f (D p) = p.1) ∧
      ∀ u ∈ ({l, r} : Set ℝ), (D : (ℝ × ℝ) → E) =ᶠ[𝓝 (a, u)] χ := by
  let K : Set (ℝ × ℝ) := {a} ×ˢ Icc l r
  have hK : IsCompact K := isCompact_singleton.prod isCompact_Icc
  have hne : K.Nonempty := ⟨(a, l), rfl, le_rfl, hlr⟩
  have hFi : InjOn F K := by
    rintro ⟨t, u⟩ ⟨ht, hu⟩ ⟨s, v⟩ ⟨hs, hv⟩ he
    have ht' : t = a := ht
    have hs' : s = a := hs
    subst t s
    rw [hbase u hu, hbase v hv] at he
    exact Prod.ext rfl (hβinj hu hv he)
  obtain ⟨C, hKC, hCF⟩ :=
    DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_isCompact
    hF hK hne hFi
  have hHid : EqOn (fun p => (f (F p), p.2)) id K := by
    rintro ⟨t, u⟩ ⟨ht, hu⟩
    have ht' : t = a := ht
    subst t
    change (f (F (a, u)), u) = (a, u)
    rw [hbase u hu, hlevel u hu]
  obtain ⟨A, hKA, hAH⟩ :=
    DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_isCompact
    hH hK hne (by intro p hp q hq he; simpa only [hHid hp, hHid hq, id_eq] using he)
  have hAK (p : ℝ × ℝ) (hp : p ∈ K) : A p = p := (congrFun hAH p).trans (hHid hp)
  have hAiK (p : ℝ × ℝ) (hp : p ∈ K) : A.symm p = p := by
    have he : A.symm (A p) = p := A.left_inv (hKA hp)
    rw [hAK p hp] at he
    exact he
  let Ψ := A.symm.trans C
  have hKΨ : K ⊆ Ψ.source := by
    intro p hp
    refine ⟨?_, ?_⟩
    · rw [← hAK p hp]
      exact A.map_source (hKA hp)
    · change A.symm p ∈ C.source
      rw [hAiK p hp]
      exact hKC hp
  have hΨbase (u : ℝ) (hu : u ∈ Icc l r) : Ψ (a, u) = β u := by
    change C (A.symm (a, u)) = β u
    rw [hAiK (a, u) (show (a, u) ∈ K from ⟨rfl, hu⟩), hCF, hbase u hu]
  let W := Ψ.source ∩ Ψ ⁻¹' O
  have hW : IsOpen W := Ψ.contMDiffOn.continuousOn.isOpen_inter_preimage Ψ.open_source hO
  have hKW : K ⊆ W := by
    rintro ⟨t, u⟩ ⟨ht, hu⟩
    have ht' : t = a := ht
    subst t
    exact ⟨hKΨ ⟨rfl, hu⟩, by change Ψ (a, u) ∈ O; rw [hΨbase u hu]; exact hβO ⟨u, hu, rfl⟩⟩
  obtain ⟨D, hDs, hDt, hDΨ⟩ :=
    DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
    (f := Ψ) (U := W) (fun p => Ψ.isLocalDiffeomorphAt _ _ _ p.property.1) hW
    (hne.mono hKW) (Ψ.toPartialEquiv.injOn.mono inter_subset_left)
  refine ⟨D, hDs ▸ hKW, ?_, ?_, ?_, ?_⟩
  · rw [hDt]
    rintro y ⟨p, hp, rfl⟩
    exact hp.2
  · intro u hu
    rw [hDΨ]
    exact hΨbase u hu
  · intro p hp
    have hpW : p ∈ W := hDs ▸ hp
    have he := A.right_inv hpW.1.1
    rw [hAH] at he
    have he' := congrArg Prod.fst he
    change f (F (A.symm p)) = p.1 at he'
    rw [hDΨ]
    change f (C (A.symm p)) = p.1
    rwa [hCF]
  · intro u hu
    have hui : u ∈ Icc l r := by
      rcases mem_insert_iff.mp hu with rfl | hh
      · exact ⟨le_rfl, hlr⟩
      · have hh' : u = r := hh; subst u; exact ⟨hlr, le_rfl⟩
    have hpK : (a, u) ∈ K := ⟨rfl, hui⟩
    obtain ⟨hpχ, hgerm⟩ := hcorners u hu
    have hAid : (A : (ℝ × ℝ) → (ℝ × ℝ)) =ᶠ[𝓝 (a, u)] id := by
      filter_upwards [hgerm, χ.open_source.mem_nhds hpχ] with p hp hpχ'
      rw [hAH]
      exact Prod.ext (by simpa only [hp, id_eq] using hχ p hpχ') rfl
    have hpAt : (a, u) ∈ A.target := by
      rw [← hAK _ hpK]
      exact A.map_source (hKA hpK)
    have hcont := A.symm.contMDiffOn.continuousOn.continuousAt (A.open_target.mem_nhds hpAt)
    have ht : Tendsto A.symm (𝓝 (a, u)) (𝓝 (a, u)) := by
      simpa only [hAiK _ hpK] using hcont.tendsto
    have hAiid : (A.symm : (ℝ × ℝ) → (ℝ × ℝ)) =ᶠ[𝓝 (a, u)] id := by
      filter_upwards [hAid.comp_tendsto ht, A.open_target.mem_nhds hpAt] with p hp hpA
      exact hp.symm.trans (A.right_inv hpA)
    filter_upwards [hAiid, hgerm] with p hpA hpF
    rw [hDΨ]
    change C (A.symm p) = χ p
    rw [hpA, hCF]
    exact hpF


private theorem linear_form_eq_smul_fst
    (L : (ℝ × ℝ) →L[ℝ] ℝ) {c : ℝ} (hfst : L (1, 0) = c) (hsnd : L (0, 1) = 0) :
    L = c • ContinuousLinearMap.fst ℝ ℝ ℝ := by
  apply ContinuousLinearMap.ext
  intro z
  have he : z = z.1 • ((1, 0) : ℝ × ℝ) + z.2 • ((0, 1) : ℝ × ℝ) := by ext <;> simp
  calc
    L z = L (z.1 • ((1, 0) : ℝ × ℝ) + z.2 • ((0, 1) : ℝ × ℝ)) := congrArg L he
    _ = c * z.1 := by rw [map_add, map_smul, map_smul, hfst, hsnd]; simp [mul_comm]
    _ = (c • ContinuousLinearMap.fst ℝ ℝ ℝ) z := rfl

private theorem exists_transverse_band_eq_corner_chart
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → ℝ} {O : Set E} (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    {β : ℝ → E} {a l r : ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβO : ∀ u ∈ Icc l r, β u ∈ O)
    (hreg : ∀ u ∈ Icc l r, fderiv ℝ f (β u) ≠ 0)
    (hlevel : ∀ u ∈ Icc l r, (fun x => f (β x)) =ᶠ[𝓝 u] (fun _ => a))
    (χ : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (ℝ × ℝ) E ∞)
    (hχ : ∀ p ∈ χ.source, f (χ p) = p.1)
    (hcorners : ∀ u ∈ ({l, r} : Set ℝ), (a, u) ∈ χ.source ∧
      β =ᶠ[𝓝 u] (fun x => χ (a, x))) :
    ∃ F : (ℝ × ℝ) → E, ∃ U : Set (ℝ × ℝ), IsOpen U ∧
      {a} ×ˢ Icc l r ⊆ U ∧ ContDiffOn ℝ ∞ F U ∧
      (∀ u, F (a, u) = β u) ∧
      (∀ u ∈ Icc l r, fderiv ℝ F (a, u) (0, 1) = deriv β u) ∧
      (∀ u ∈ Icc l r, ∃ c : ℝ, 0 < c ∧
        (fderiv ℝ f (F (a, u))).comp (fderiv ℝ F (a, u)) =
          c • ContinuousLinearMap.fst ℝ ℝ ℝ) ∧
      ∀ u ∈ ({l, r} : Set ℝ), F =ᶠ[𝓝 (a, u)] χ := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let V : Set ℝ := interior {u | β u = χ (a, u)}
  have hVc : ({l, r} : Set ℝ) ⊆ V := by
    intro u hu
    exact mem_interior_iff_mem_nhds.mpr (hcorners u hu).2
  let C : Set (ℝ × ℝ) := (fun u => (a, u)) '' ({l, r} : Set ℝ)
  have hC : IsCompact C :=
    (isCompact_singleton.insert l).image (continuous_const.prodMk continuous_id)
  let W := χ.source ∩ Prod.snd ⁻¹' V
  have hW : IsOpen W := χ.open_source.inter (isOpen_interior.preimage continuous_snd)
  have hCW : C ⊆ W := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨(hcorners u hu).1, hVc hu⟩
  obtain ⟨ρ, hρ, _, hρone, hρW, hρ01⟩ := Analysis.exists_bump_compact hC hW hCW
  let w : ℝ → E := fun u => gradient f (β u)
  let F₀ : (ℝ × ℝ) → E := fun p => β p.2 + (p.1 - a) • w p.2
  let F : (ℝ × ℝ) → E := fun p => (1 - ρ p) • F₀ p + ρ p • χ p
  let U : Set (ℝ × ℝ) := (fun p => β p.2) ⁻¹' O
  have hU : IsOpen U := hO.preimage (hβ.continuous.comp continuous_snd)
  have hKU : {a} ×ˢ Icc l r ⊆ U := fun p hp => hβO p.2 hp.2
  have hgrad : ContDiffOn ℝ ∞ (gradient f) O := by
    intro x hx
    exact (((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.contDiffAt).comp x
      ((hf.contDiffAt (hO.mem_nhds hx)).fderiv_right (by simp))).contDiffWithinAt
  have hw : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => w p.2) U :=
    hgrad.comp (hβ.comp contDiff_snd).contDiffOn (fun _ hp => hp)
  have hF₀ : ContDiffOn ℝ ∞ F₀ U := (hβ.comp contDiff_snd).contDiffOn.add
    ((contDiff_fst.sub contDiff_const).contDiffOn.smul hw)
  have hρχ : ContDiff ℝ ∞ (fun p => ρ p • χ p) := by
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p ∈ tsupport ρ
    · exact hρ.contDiffAt.smul (χ.contMDiffOn.contDiffOn.contDiffAt
        (χ.open_source.mem_nhds (hρW hp).1))
    · apply (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport ρ).isOpen_compl.mem_nhds hp] with z hz
      rw [image_eq_zero_of_notMem_tsupport hz, zero_smul]
  have hF : ContDiffOn ℝ ∞ F U := ((contDiff_const.sub hρ).contDiffOn.smul hF₀).add hρχ.contDiffOn
  have hbase (u : ℝ) : F (a, u) = β u := by
    by_cases hz : ρ (a, u) = 0
    · simp only [F, F₀, hz, sub_zero, one_smul, zero_smul, add_zero, sub_self]
    · have he : β u = χ (a, u) :=
        (interior_subset : V ⊆ {u | β u = χ (a, u)}) (hρW (subset_tsupport ρ hz)).2
      simp only [F, F₀, sub_self, zero_smul, add_zero, ← he]
      rw [← add_smul]
      simp
  have hcolu (u : ℝ) (hu : u ∈ Icc l r) : fderiv ℝ F (a, u) (0, 1) = deriv β u := by
    have hd := ((hF.contDiffAt
      (hU.mem_nhds (hKU (show (a, u) ∈ {a} ×ˢ Icc l r from ⟨rfl, hu⟩)))).differentiableAt
        (by simp)).hasFDerivAt
    have he := hd.comp_hasDerivAt u ((hasDerivAt_const u a).prodMk (hasDerivAt_id u))
    have hfun : (fun x => F (a, x)) = β := funext hbase
    simpa only [Function.comp_def, hfun] using he.deriv.symm
  have hdfu (u : ℝ) (hu : u ∈ Icc l r) : fderiv ℝ f (β u) (deriv β u) = 0 := by
    have hd := ((hf.contDiffAt (hO.mem_nhds (hβO u hu))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt u
      (hβ.differentiable (by simp) u).hasDerivAt
    have he := hd.deriv
    dsimp only [Function.comp_def] at he
    rw [(hlevel u hu).deriv_eq, deriv_const] at he
    exact he.symm
  have hwdf (u : ℝ) : fderiv ℝ f (β u) (w u) = ‖w u‖ ^ 2 := by
    rw [← inner_gradient_left]
    exact real_inner_self_eq_norm_sq _
  have hwpos (u : ℝ) (hu : u ∈ Icc l r) : 0 < ‖w u‖ ^ 2 := by
    apply sq_pos_of_pos
    apply norm_pos_iff.mpr
    intro hz
    apply hreg u hu
    have he := congrArg (InnerProductSpace.toDual ℝ E) hz
    simpa only [w, toDual_gradient, map_zero] using he
  refine ⟨F, U, hU, hKU, hF, hbase, hcolu, ?_, ?_⟩
  · intro u hu
    have hpU : (a, u) ∈ U := hKU (show (a, u) ∈ {a} ×ˢ Icc l r from ⟨rfl, hu⟩)
    have hdF := ((hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)).hasFDerivAt
    have hdtF := hdF.comp_hasDerivAt a ((hasDerivAt_id a).prodMk (hasDerivAt_const a u))
    have hdfcolu : ((fderiv ℝ f (F (a, u))).comp (fderiv ℝ F (a, u))) (0, 1) = 0 := by
      change fderiv ℝ f (F (a, u)) (fderiv ℝ F (a, u) (0, 1)) = 0
      rw [hbase, hcolu u hu, hdfu u hu]
    by_cases hpρ : (a, u) ∈ tsupport ρ
    · have hpχ := (hρW hpρ).1
      have he : β u = χ (a, u) := (interior_subset : V ⊆ {u | β u = χ (a, u)}) (hρW hpρ).2
      have hχd := ((χ.contMDiffOn.contDiffOn.contDiffAt
        (χ.open_source.mem_nhds hpχ)).differentiableAt
        (by simp)).hasFDerivAt
      let v := fderiv ℝ χ (a, u) (1, 0)
      have hχt : HasDerivAt (fun t => χ (t, u)) v a :=
        hχd.comp_hasDerivAt a ((hasDerivAt_id a).prodMk (hasDerivAt_const a u))
      have hρt := (hρ.differentiable (by simp) (a, u)).hasFDerivAt.comp_hasDerivAt a
        ((hasDerivAt_id a).prodMk (hasDerivAt_const a u))
      have hF₀t : HasDerivAt (fun t => F₀ (t, u)) (w u) a := by
        simpa only [F₀, sub_self, one_smul, zero_add, Pi.add_def, id_eq] using
          (hasDerivAt_const a (β u)).add (((hasDerivAt_id a).sub_const a).smul_const (w u))
      have ht := ((hρt.const_sub 1).smul hF₀t).add (hρt.smul hχt)
      have ht' : HasDerivAt (fun t => F (t, u)) ((1 - ρ (a, u)) • w u + ρ (a, u) • v) a := by
        apply ht.congr_deriv
        simp only [F₀, sub_self, zero_smul, add_zero, ← he, Function.comp_def, id_eq]
        module
      have hχdf : fderiv ℝ f (β u) v = 1 := by
        have hfd := ((hf.contDiffAt (hO.mem_nhds (hβO u hu))).differentiableAt
          (by simp)).hasFDerivAt
        rw [he] at hfd
        have hh := hfd.comp_hasDerivAt a hχt
        have hlocal : (fun t => f (χ (t, u))) =ᶠ[𝓝 a] id := by
          have hn := (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
            (χ.open_source.mem_nhds hpχ)
          filter_upwards [hn] with t ht
          exact hχ (t, u) ht
        have hd : deriv (fun t => f (χ (t, u))) a = fderiv ℝ f (χ (a, u)) v := hh.deriv
        have hr := hd.symm.trans hlocal.deriv_eq
        simpa only [deriv_id, ← he] using hr
      let c := (1 - ρ (a, u)) * ‖w u‖ ^ 2 + ρ (a, u)
      have hc : 0 < c := by
        have hb := hρ01 (mem_range_self (a, u))
        have hh := hwpos u hu
        dsimp only [c]
        nlinarith only [hb.1, hb.2, hh, mul_nonneg (sub_nonneg.mpr hb.2) hh.le]
      refine ⟨c, hc, linear_form_eq_smul_fst _ ?_ hdfcolu⟩
      change fderiv ℝ f (F (a, u)) (fderiv ℝ F (a, u) (1, 0)) = c
      rw [hbase, hdtF.unique ht', map_add, map_smul, map_smul, hwdf, hχdf]
      simp only [smul_eq_mul, mul_one, c]
    · have hgerm : F =ᶠ[𝓝 (a, u)] F₀ := by
        filter_upwards [(isClosed_tsupport ρ).isOpen_compl.mem_nhds hpρ] with p hp
        have hz := image_eq_zero_of_notMem_tsupport hp
        simp only [F, hz, sub_zero, one_smul, zero_smul, add_zero]
      have hdt : HasDerivAt (fun t => F₀ (t, u)) (w u) a := by
        simpa only [F₀, sub_self, one_smul, zero_add, Pi.add_def, id_eq] using
          (hasDerivAt_const a (β u)).add (((hasDerivAt_id a).sub_const a).smul_const (w u))
      have he : fderiv ℝ F (a, u) (1, 0) = w u :=
        hdtF.unique (hdt.congr_of_eventuallyEq
          (hgerm.comp_tendsto (continuous_id.prodMk continuous_const).continuousAt.tendsto))
      refine ⟨‖w u‖ ^ 2, hwpos u hu, linear_form_eq_smul_fst _ ?_ hdfcolu⟩
      change fderiv ℝ f (F (a, u)) (fderiv ℝ F (a, u) (1, 0)) = ‖w u‖ ^ 2
      rw [hbase, he, hwdf]
  · intro u hu
    have hpC : (a, u) ∈ C := ⟨u, hu, rfl⟩
    have hgerm := hρone.filter_mono (nhds_le_nhdsSet hpC)
    filter_upwards [hgerm] with p hp
    simp only [F, hp, Pi.one_apply, sub_self, zero_smul, one_smul, zero_add]


theorem exists_partialDiffeomorph_regular_level_arc_eq_corner_chart
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 2)
    {f : E → ℝ} {O : Set E} (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    {β : ℝ → E} {a l r : ℝ} (hlr : l < r) (hβ : ContDiff ℝ ∞ β)
    (hβd : ∀ u ∈ Icc l r, deriv β u ≠ 0) (hβinj : InjOn β (Icc l r))
    (hβO : ∀ u ∈ Icc l r, β u ∈ O)
    (hreg : ∀ u ∈ Icc l r, fderiv ℝ f (β u) ≠ 0)
    (hlevel : ∀ u ∈ Icc l r, f (β u) = a)
    (χ : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (ℝ × ℝ) E ∞)
    (hχ : ∀ p ∈ χ.source, f (χ p) = p.1)
    (hcorners : ∀ u ∈ ({l, r} : Set ℝ), (a, u) ∈ χ.source ∧
      β =ᶠ[𝓝 u] (fun x => χ (a, x))) :
    ∃ D : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (ℝ × ℝ) E ∞,
      {a} ×ˢ Icc l r ⊆ D.source ∧ D.target ⊆ O ∧
      (∀ u ∈ Icc l r, D (a, u) = β u) ∧
      (∀ p ∈ D.source, f (D p) = p.1) ∧
      ∀ u ∈ ({l, r} : Set ℝ), (D : (ℝ × ℝ) → E) =ᶠ[𝓝 (a, u)] χ := by
  have hlevelGerm (u : ℝ) (hu : u ∈ Icc l r) :
      (fun x => f (β x)) =ᶠ[𝓝 u] (fun _ => a) := by
    by_cases hend : u ∈ ({l, r} : Set ℝ)
    · obtain ⟨hc, hg⟩ := hcorners u hend
      have hn := (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
        (χ.open_source.mem_nhds hc)
      filter_upwards [hg, hn] with x hx hp
      rw [hx]
      exact hχ (a, x) hp
    · have hi : u ∈ Ioo l r := by
        simp only [mem_insert_iff, mem_singleton_iff, not_or] at hend
        exact ⟨lt_of_le_of_ne hu.1 (Ne.symm hend.1), lt_of_le_of_ne hu.2 hend.2⟩
      filter_upwards [isOpen_Ioo.mem_nhds hi] with x hx
      exact hlevel x (Ioo_subset_Icc_self hx)
  obtain ⟨F, U, hU, hKU, hF, hbase, hcol, hcoefficient, hgerm⟩ :=
    exists_transverse_band_eq_corner_chart hO hf hβ hβO hreg hlevelGerm χ hχ hcorners
  have hFlocal : IsLocalDiffeomorphOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ F ({a} ×ˢ Icc l r) := by
    rintro ⟨⟨t, u⟩, ht, hu⟩
    have ht' : t = a := ht
    subst t
    obtain ⟨c, hc, hcf⟩ := hcoefficient u hu
    exact isLocalDiffeomorphAt_of_regular_level_columns hdim hU hF
      (hKU ⟨rfl, hu⟩) (hβd u hu) hc.ne' (hcol u hu) hcf
  let V := U ∩ F ⁻¹' O
  have hV : IsOpen V := hF.continuousOn.isOpen_inter_preimage hU hO
  have hKV : {a} ×ˢ Icc l r ⊆ V := by
    rintro ⟨t, u⟩ ⟨ht, hu⟩
    have ht' : t = a := ht
    subst t
    exact ⟨hKU ⟨rfl, hu⟩, by change F (a, u) ∈ O; rw [hbase]; exact hβO u hu⟩
  have hfF : ContDiffOn ℝ ∞ (fun p => f (F p)) V := hf.comp (hF.mono inter_subset_left)
    (fun _ hp => hp.2)
  have hHlocal : IsLocalDiffeomorphOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun p => (f (F p), p.2)) ({a} ×ˢ Icc l r) := by
    rintro ⟨⟨t, u⟩, ht, hu⟩
    have ht' : t = a := ht
    subst t
    obtain ⟨c, hc, hcf⟩ := hcoefficient u hu
    have hdF := (hF.contDiffAt
      (hU.mem_nhds (hKU (show (a, u) ∈ {a} ×ˢ Icc l r from ⟨rfl, hu⟩)))).differentiableAt
        (by simp)
    have hfd := (hf.contDiffAt
      (hO.mem_nhds (show F (a, u) ∈ O by rw [hbase]; exact hβO u hu))).differentiableAt
        (by simp)
    have he : fderiv ℝ (fun p => f (F p)) (a, u) = c • ContinuousLinearMap.fst ℝ ℝ ℝ :=
      (hfd.hasFDerivAt.comp (a, u) hdF.hasFDerivAt).fderiv.trans hcf
    exact isLocalDiffeomorphAt_level_parameter hV (hfF.prodMk contDiffOn_snd)
      (hKV ⟨rfl, hu⟩) hc.ne' he
  exact exists_partialDiffeomorph_level_rectification hlr.le hβinj (fun u _ => hbase u)
    hlevel hO (by rintro y ⟨u, hu, rfl⟩; exact hβO u hu) hFlocal hHlocal χ hχ
    (fun u hu => ⟨(hcorners u hu).1, hgerm u hu⟩)


theorem exists_partialDiffeomorph_height_arc_eq_corner_chart
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 2) (ψ : ℝ ≃ₘ[ℝ] ℝ)
    {g : E → ℝ} {O : Set E} (hO : IsOpen O) (hg : ContDiffOn ℝ ∞ g O)
    {β : ℝ → E} {ell a l r : ℝ} (hlr : l < r) (hβ : ContDiff ℝ ∞ β)
    (hβd : ∀ u ∈ Icc l r, deriv β u ≠ 0) (hβinj : InjOn β (Icc l r))
    (hβO : ∀ u ∈ Icc l r, β u ∈ O)
    (hbottom : ∀ u ∈ Icc l r, g (β u) = ψ (ell + a) ∧ fderiv ℝ g (β u) ≠ 0)
    (χ : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (ℝ × ℝ) E ∞)
    (hχ : ∀ p ∈ χ.source, g (χ p) = ψ (ell + p.1))
    (hcorners : ∀ u ∈ ({l, r} : Set ℝ), (a, u) ∈ χ.source ∧
      β =ᶠ[𝓝 u] (fun x => χ (a, x))) :
    ∃ D : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (ℝ × ℝ) E ∞,
      {a} ×ˢ Icc l r ⊆ D.source ∧ D.target ⊆ O ∧
      (∀ u ∈ Icc l r, D (a, u) = β u) ∧
      (∀ p ∈ D.source, g (D p) = ψ (ell + p.1)) ∧
      ∀ u ∈ ({l, r} : Set ℝ), (D : (ℝ × ℝ) → E) =ᶠ[𝓝 (a, u)] χ := by
  let f : E → ℝ := fun x => ψ.symm (g x) - ell
  have hf : ContDiffOn ℝ ∞ f O := (ψ.symm.contDiff.comp_contDiffOn hg).sub contDiffOn_const
  have hlevel (u : ℝ) (hu : u ∈ Icc l r) : f (β u) = a := by
    simp only [f, (hbottom u hu).1, ψ.symm_apply_apply, add_sub_cancel_left]
  have hreg (u : ℝ) (hu : u ∈ Icc l r) : fderiv ℝ f (β u) ≠ 0 := by
    intro hz
    have hfd := (hf.contDiffAt (hO.mem_nhds (hβO u hu))).differentiableAt (by simp)
    have hd := (ψ.contDiff.differentiable (by simp) (f (β u) + ell)).hasFDerivAt.comp (β u)
      (hfd.hasFDerivAt.add_const ell)
    have he : (fun x => ψ (f x + ell)) = g := by
      funext x
      simp only [f, sub_add_cancel, ψ.apply_symm_apply]
    change HasFDerivAt (fun x => ψ (f x + ell))
      ((fderiv ℝ ψ (f (β u) + ell)).comp (fderiv ℝ f (β u))) (β u) at hd
    rw [he] at hd
    apply (hbottom u hu).2
    rw [hd.fderiv, hz, ContinuousLinearMap.comp_zero]
  have hχf (p : ℝ × ℝ) (hp : p ∈ χ.source) : f (χ p) = p.1 := by
    simp only [f, hχ p hp, ψ.symm_apply_apply, add_sub_cancel_left]
  obtain ⟨D, hDs, hDt, hDb, hDf, hDχ⟩ := exists_partialDiffeomorph_regular_level_arc_eq_corner_chart
    hdim hO hf hlr hβ hβd hβinj hβO hreg hlevel χ hχf hcorners
  refine ⟨D, hDs, hDt, hDb, ?_, hDχ⟩
  intro p hp
  have he := hDf p hp
  change ψ.symm (g (D p)) - ell = p.1 at he
  have he' : ψ.symm (g (D p)) = ell + p.1 := by linarith only [he]
  rw [← he', ψ.apply_symm_apply]

end DifferentialGeometry.Topology
