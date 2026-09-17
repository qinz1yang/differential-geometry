import DifferentialGeometry.Topology.Diffeomorph.LocalFlowExtension
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.Calculus.Deriv.Prod

open Set Filter
open scoped ContDiff Manifold Topology

namespace PartialDiffeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_contDiff_compact_isotopy_eqOn_fibers_preserving_linear_map
    (φ : PartialDiffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) ∞)
    (hφ : ∀ z ∈ φ.source, (φ z).1 = z.1)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hL : ∀ z ∈ φ.source, L (φ z).2 = L z.2)
    {A : Set E}
    (hfixed : ∀ z ∈ φ.source, z.2 ∈ A → (φ z).2 = z.2)
    (hreflect : ∀ z ∈ φ.source, (φ z).2 ∈ A → z.2 ∈ A)
    {a b : ℝ} {K : Set E} (hK : IsCompact K)
    (hsource : Icc a b ×ˢ K ⊆ φ.source)
    {O : Set E} (hO : IsOpen O) (himage : φ '' (Icc a b ×ˢ K) ⊆ univ ×ˢ O) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ Icc a b ×ˢ V ⊆ φ.source ∧
      ∃ Φ : ℝ → (E ≃ₘ[ℝ] E),
        ContDiff ℝ ∞ (fun z : ℝ × E => Φ z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × E => (Φ z.1).symm z.2) ∧
        Φ a = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
        (∀ t ∈ Icc a b, ∀ x ∈ V, Φ t (φ (a, x)).2 = (φ (t, x)).2) ∧
        (∀ t, EqOn (Φ t) id A ∧ EqOn (Φ t).symm id A) ∧
        (∀ t x, L (Φ t x) = L x) ∧
        ∃ S : Set E, IsCompact S ∧ S ⊆ O ∧ ∀ t : ℝ,
          EqOn (Φ t) id Sᶜ ∧ EqOn (Φ t).symm id Sᶜ := by
  let U := φ.source ∩ φ ⁻¹' (univ ×ˢ O)
  have hU : IsOpen U := φ.contMDiffOn.continuousOn.isOpen_inter_preimage
    φ.open_source (isOpen_univ.prod hO)
  have hKU : Icc a b ×ˢ K ⊆ U := fun z hz => ⟨hsource hz, himage ⟨z, hz, rfl⟩⟩
  have hUnhds : U ∈ (𝓝ˢ (Icc a b)) ×ˢ (𝓝ˢ K) := by
    rw [← isCompact_Icc.nhdsSet_prod_eq hK]
    exact hU.mem_nhdsSet.mpr hKU
  obtain ⟨T, hT, W, hW, hTW⟩ := Filter.mem_prod_iff.mp hUnhds
  obtain ⟨W', hW', hKW', hW'W⟩ := mem_nhdsSet_iff_exists.mp hW
  obtain ⟨C, hC, hKC, hCW⟩ := exists_compact_between hK hW' hKW'
  have hTC : Icc a b ×ˢ C ⊆ U := fun z hz =>
    hTW ⟨subset_of_mem_nhdsSet hT hz.1, hW'W (hCW hz.2)⟩
  let Q := φ '' (Icc a b ×ˢ C)
  have hQ : IsCompact Q := (isCompact_Icc.prod hC).image_of_continuousOn
    (φ.contMDiffOn.continuousOn.mono (hTC.trans inter_subset_left))
  have hQsub : Q ⊆ φ.target ∩ (univ ×ˢ O) := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨φ.map_source (hTC hz).1, (hTC hz).2⟩
  let X : ℝ × E → E := fun z => (fderiv ℝ φ (φ.symm z) (1, 0)).2
  have hX : ContDiffOn ℝ ∞ X φ.target := by
    have hd := (φ.contMDiffOn.contDiffOn.fderiv_of_isOpen φ.open_source (by simp : ∞ + 1 ≤ ∞)).comp
      φ.symm.contMDiffOn.contDiffOn (fun _ hz => φ.map_target hz)
    exact (hd.clm_apply contDiffOn_const).snd
  have hXA (z : ℝ × E) (hz : z ∈ φ.target) (hzA : z.2 ∈ A) : X z = 0 := by
    let w := φ.symm z
    have hw : w ∈ φ.source := φ.map_target hz
    have hright : φ w = z := φ.right_inv hz
    have hwA : w.2 ∈ A := hreflect w hw (by rw [hright]; exact hzA)
    have hnear : ∀ᶠ t in nhds w.1, (t, w.2) ∈ φ.source :=
      (continuous_id.prodMk continuous_const).continuousAt.eventually_mem
        (φ.open_source.mem_nhds hw)
    have heq : (fun t => (φ (t, w.2)).2) =ᶠ[nhds w.1] fun _ => w.2 := by
      filter_upwards [hnear] with t ht
      exact hfixed (t, w.2) ht hwA
    have hd := ((φ.contMDiffOn.contDiffOn.contDiffAt (φ.open_source.mem_nhds hw)).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt w.1
        ((hasDerivAt_id w.1).prodMk (hasDerivAt_const w.1 w.2))
    have hds := (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt.comp_hasDerivAt w.1 hd
    have hc : HasDerivAt (fun t => (φ (t, w.2)).2) 0 w.1 :=
      (hasDerivAt_const w.1 w.2).congr_of_eventuallyEq heq
    exact hds.unique hc
  have hXL (z : ℝ × E) (hz : z ∈ φ.target) : X z ∈ L.ker := by
    let w := φ.symm z
    have hw : w ∈ φ.source := φ.map_target hz
    have hnear : ∀ᶠ t in 𝓝 w.1, (t, w.2) ∈ φ.source :=
      (continuous_id.prodMk continuous_const).continuousAt.eventually_mem
        (φ.open_source.mem_nhds hw)
    have heq : (fun t => L (φ (t, w.2)).2) =ᶠ[𝓝 w.1] fun _ => L w.2 := by
      filter_upwards [hnear] with t ht
      exact hL (t, w.2) ht
    have hd := ((φ.contMDiffOn.contDiffOn.contDiffAt (φ.open_source.mem_nhds hw)).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt w.1
        ((hasDerivAt_id w.1).prodMk (hasDerivAt_const w.1 w.2))
    have hds := L.hasFDerivAt.comp_hasDerivAt w.1 hd.snd
    have hc : HasDerivAt (fun t => L (φ (t, w.2)).2) 0 w.1 :=
      (hasDerivAt_const w.1 (L w.2)).congr_of_eventuallyEq heq
    exact hds.unique hc
  let γ : C → ℝ → E := fun x t => (φ (t, x.val)).2
  have hγ (x : C) : ContinuousOn (γ x) (Icc a b) :=
    (φ.contMDiffOn.continuousOn.comp (continuousOn_id.prodMk continuousOn_const)
      (fun t ht => (hTC ⟨ht, x.property⟩).1)).snd
  have hγ' (x : C) (t : ℝ) (ht : t ∈ Ico a b) :
      HasDerivWithinAt (γ x) (X (t, γ x t)) (Ici t) t := by
    have htx : (t, x.val) ∈ φ.source := (hTC ⟨⟨ht.1, ht.2.le⟩, x.property⟩).1
    have hpoint : (t, γ x t) = φ (t, x.val) := Prod.ext (hφ _ htx).symm rfl
    have hd := ((φ.contMDiffOn.contDiffOn.contDiffAt (φ.open_source.mem_nhds htx)).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hasDerivAt_const t x.val))
    have hds := (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt.comp_hasDerivAt t hd
    dsimp [X]
    have hleft : φ.symm.toPartialEquiv (φ.toPartialEquiv (t, x.val)) = (t, x.val) :=
      φ.left_inv htx
    rw [hpoint, hleft]
    convert! hds.hasDerivWithinAt (s := Ici t) using 1
  have hγQ (x : C) (t : ℝ) (ht : t ∈ Icc a b) : (t, γ x t) ∈ Q := by
    refine ⟨(t, x.val), ⟨ht, x.property⟩, ?_⟩
    exact Prod.ext (hφ _ (hTC ⟨ht, x.property⟩).1) rfl
  obtain ⟨Φ, hΦ, hΦinv, hΦa, htrack, hΦA, hspan, S, hS, hSO, hfix⟩ :=
    Diffeomorph.exists_contDiff_compact_isotopy_eqOn_integralCurve_of_mem_submodule
      hO φ.open_target hQ hQsub hX hXA L.ker hXL a hγ hγ' hγQ
  refine ⟨interior C, isOpen_interior, hKC,
    fun z hz => (hTC ⟨hz.1, interior_subset hz.2⟩).1,
    Φ, hΦ, hΦinv, hΦa, ?_, hΦA, ?_, S, hS, hSO, hfix⟩
  · intro t ht x hx
    simpa only [hΦa, Diffeomorph.symm_refl, Diffeomorph.coe_refl, id_eq, γ] using
      htrack ⟨x, interior_subset hx⟩ t ht
  · intro t x
    have h := hspan t x
    change L (Φ t x - x) = 0 at h
    rwa [map_sub, sub_eq_zero] at h

theorem exists_contDiff_compact_isotopy_eqOn_fibers_of_fixed
    (φ : PartialDiffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) ∞)
    (hφ : ∀ z ∈ φ.source, (φ z).1 = z.1)
    {A : Set E}
    (hfixed : ∀ z ∈ φ.source, z.2 ∈ A → (φ z).2 = z.2)
    (hreflect : ∀ z ∈ φ.source, (φ z).2 ∈ A → z.2 ∈ A)
    {a b : ℝ} {K : Set E} (hK : IsCompact K)
    (hsource : Icc a b ×ˢ K ⊆ φ.source)
    {O : Set E} (hO : IsOpen O) (himage : φ '' (Icc a b ×ˢ K) ⊆ univ ×ˢ O) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ Icc a b ×ˢ V ⊆ φ.source ∧
      ∃ Φ : ℝ → (E ≃ₘ[ℝ] E),
        ContDiff ℝ ∞ (fun z : ℝ × E => Φ z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × E => (Φ z.1).symm z.2) ∧
        Φ a = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
        (∀ t ∈ Icc a b, ∀ x ∈ V, Φ t (φ (a, x)).2 = (φ (t, x)).2) ∧
        (∀ t, EqOn (Φ t) id A ∧ EqOn (Φ t).symm id A) ∧
        ∃ S : Set E, IsCompact S ∧ S ⊆ O ∧ ∀ t : ℝ,
          EqOn (Φ t) id Sᶜ ∧ EqOn (Φ t).symm id Sᶜ := by
  obtain ⟨V, hV, hKV, hVs, Φ, hΦ, hΦi, hΦa, htrack, hfixed, _, hsupport⟩ :=
    φ.exists_contDiff_compact_isotopy_eqOn_fibers_preserving_linear_map hφ
      (0 : E →L[ℝ] E) (fun _ _ => rfl) hfixed hreflect hK hsource hO himage
  exact ⟨V, hV, hKV, hVs, Φ, hΦ, hΦi, hΦa, htrack, hfixed, hsupport⟩

theorem exists_contDiff_compact_isotopy_eqOn_fibers
    (φ : PartialDiffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) ∞)
    (hφ : ∀ z ∈ φ.source, (φ z).1 = z.1)
    {a b : ℝ} {K : Set E} (hK : IsCompact K)
    (hsource : Icc a b ×ˢ K ⊆ φ.source)
    {O : Set E} (hO : IsOpen O) (himage : φ '' (Icc a b ×ˢ K) ⊆ univ ×ˢ O) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ Icc a b ×ˢ V ⊆ φ.source ∧
      ∃ Φ : ℝ → (E ≃ₘ[ℝ] E),
        ContDiff ℝ ∞ (fun z : ℝ × E => Φ z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × E => (Φ z.1).symm z.2) ∧
        Φ a = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
        (∀ t ∈ Icc a b, ∀ x ∈ V, Φ t (φ (a, x)).2 = (φ (t, x)).2) ∧
        ∃ S : Set E, IsCompact S ∧ S ⊆ O ∧ ∀ t : ℝ,
          EqOn (Φ t) id Sᶜ ∧ EqOn (Φ t).symm id Sᶜ := by
  obtain ⟨V, hV, hKV, hVs, Φ, hΦ, hΦi, hΦa, htrack, _, hsupport⟩ :=
    φ.exists_contDiff_compact_isotopy_eqOn_fibers_of_fixed hφ
      (A := ∅) (fun _ _ h => h.elim) (fun _ _ h => h.elim) hK hsource hO himage
  exact ⟨V, hV, hKV, hVs, Φ, hΦ, hΦi, hΦa, htrack, hsupport⟩

end PartialDiffeomorph

namespace Diffeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_contDiff_compact_isotopy_eqOn_preserving_linear_map
    (H : ℝ → (E ≃ₘ[ℝ] E))
    (hH : ContDiff ℝ ∞ (fun z : ℝ × E => H z.1 z.2))
    (hHi : ContDiff ℝ ∞ (fun z : ℝ × E => (H z.1).symm z.2))
    (L : E →L[ℝ] F) (hL : ∀ t x, L (H t x) = L x)
    {A : Set E} (hfixed : ∀ t, EqOn (H t) id A)
    {a b : ℝ} {K O : Set E} (hK : IsCompact K) (hO : IsOpen O)
    (htrace : ∀ t ∈ Icc a b, ∀ x ∈ K, H t x ∈ O) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧
      ∃ Φ : ℝ → (E ≃ₘ[ℝ] E),
        ContDiff ℝ ∞ (fun z : ℝ × E => Φ z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × E => (Φ z.1).symm z.2) ∧
        Φ a = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
        (∀ t ∈ Icc a b, ∀ x ∈ V, Φ t (H a x) = H t x) ∧
        (∀ t, EqOn (Φ t) id A ∧ EqOn (Φ t).symm id A) ∧
        (∀ t x, L (Φ t x) = L x) ∧
        ∃ S : Set E, IsCompact S ∧ S ⊆ O ∧ ∀ t,
          EqOn (Φ t) id Sᶜ ∧ EqOn (Φ t).symm id Sᶜ := by
  let φ : (ℝ × E) ≃ₘ[ℝ] (ℝ × E) :=
    { toEquiv := Equiv.prodCongrRight (fun t => (H t).toEquiv)
      contMDiff_toFun := (contDiff_fst.prodMk hH).contMDiff
      contMDiff_invFun := (contDiff_fst.prodMk hHi).contMDiff }
  have hreflect (z : ℝ × E) (hz : (φ z).2 ∈ A) : z.2 ∈ A := by
    have heq : H z.1 (H z.1 z.2) = H z.1 z.2 := hfixed z.1 hz
    exact (H z.1).injective heq ▸ hz
  obtain ⟨V, hV, hKV, _, Φ, hΦ, hΦi, hΦa, htrack, hΦA, hΦL, hsupport⟩ :=
    φ.toPartialDiffeomorph.exists_contDiff_compact_isotopy_eqOn_fibers_preserving_linear_map
      (fun _ _ => rfl) L (fun z _ => hL z.1 z.2)
      (fun z _ hz => hfixed z.1 hz) (fun z _ hz => hreflect z hz) hK
      (fun _ _ => mem_univ _) hO (by
        rintro _ ⟨z, hz, rfl⟩
        exact ⟨mem_univ _, htrace z.1 hz.1 z.2 hz.2⟩)
  exact ⟨V, hV, hKV, Φ, hΦ, hΦi, hΦa, htrack, hΦA, hΦL, hsupport⟩

end Diffeomorph
