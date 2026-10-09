import DifferentialGeometry.Topology.Ehresmann.SmoothIntervalFlow
import DifferentialGeometry.Topology.Ehresmann.SmoothLift
import DifferentialGeometry.Topology.Manifold.OpenTarget
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDifferential

/-!
# Level transport by a global flow from a proper submersion on an open set (D74-10, kernel K1)

Lane C14-EDP-FDCe. Review 74, D74-10 (interval product S0: "extract the underlying flow method:
`dπ(V) = 1`, completeness over the compact base arc, flow a standard fibre"). The tree's
`exists_interval_transport_of_proper` needs a submersion `M → ℝ` that is proper on all of `M`; the
slim stage of chapter 14 has such coordinates only on open pieces `Ω` of the compact carrier. Here:

* `exists_scalar_window_field_EFE`: a smooth compactly supported field `Z` on `ℝ` with
  `tsupport Z ⊆ (a', b')` and `Z = 1` on an open interval around `[α, β]`;
* `scalar_flow_eq_add_EFE`: its flow is the translation on that interval;
* `exists_global_interval_transport_EFE`: if `g : M → ℝ` is smooth, has compact preimages in the
  open set `Ω` of compact subsets of `(a', b')` and is a submersion on `Ω`, then for
  `[α, β] ⊆ (a', b')` there is a jointly smooth family of diffeomorphisms `D s` of the WHOLE
  manifold `M` (`D 0 = id`, `(D s)⁻¹ = D (-s)`, identity off `Ω`, preserving `Ω`) with
  `g (D (t - g x) x) = t` whenever `g x, t ∈ [α, β]`. Route: lift `Z` on the open submanifold `Ω`
  (`exists_smoothDerivativeLift_of_surjective`), compact support from properness, flow
  `compactSupportFlowDiffeomorph`, extension by the identity off the compact support.
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology Manifold Filter
open scoped ContDiff

namespace DifferentialGeometry.Topology.Ehresmann

open DifferentialGeometry.Analysis.ODE

/-- A smooth compactly supported scalar field on `ℝ`, supported in `(a', b')`, equal to `1` on an
open interval `(A, B) ⊇ [α, β]`. -/
theorem exists_scalar_window_field_EFE {a' b' α β : ℝ} (hab : α ≤ β) (ha : a' < α)
    (hb : β < b') :
    ∃ (Z : Cₛ^∞⟮𝓘(ℝ); ℝ, TangentSpace 𝓘(ℝ)⟯) (A B : ℝ),
      IsCompact (tsupport Z) ∧ tsupport Z ⊆ Ioo a' b' ∧ A < α ∧ β < B ∧
        ∀ y ∈ Ioo A B, Z y = (1 : ℝ) := by
  set η := min (α - a') (b' - β) / 4 with hη
  have hη0 : 0 < η := by
    have : 0 < min (α - a') (b' - β) := lt_min (by linarith) (by linarith)
    positivity
  have hη1 : 4 * η ≤ α - a' := by
    rw [hη]; linarith [min_le_left (α - a') (b' - β)]
  have hη2 : 4 * η ≤ b' - β := by
    rw [hη]; linarith [min_le_right (α - a') (b' - β)]
  let bu : ContDiffBump ((α + β) / 2) :=
    ⟨(β - α) / 2 + η, (β - α) / 2 + 2 * η, by linarith, by linarith⟩
  have hbu : ContMDiff 𝓘(ℝ) (𝓘(ℝ)).tangent ∞
      (fun y : ℝ ↦ (⟨y, bu y⟩ : TangentBundle 𝓘(ℝ) ℝ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr bu.contDiff
  let Z : Cₛ^∞⟮𝓘(ℝ); ℝ, TangentSpace 𝓘(ℝ)⟯ := ⟨bu, hbu⟩
  refine ⟨Z, α - η, β + η, bu.hasCompactSupport, ?_, by linarith, by linarith, ?_⟩
  · change tsupport (bu : ℝ → ℝ) ⊆ _
    rw [bu.tsupport_eq]
    intro y hy
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hy
    change -((β - α) / 2 + 2 * η) ≤ y - (α + β) / 2 ∧
      y - (α + β) / 2 ≤ (β - α) / 2 + 2 * η at hy
    constructor <;> linarith [hy.1, hy.2]
  · intro y hy
    apply bu.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    change -((β - α) / 2 + η) ≤ y - (α + β) / 2 ∧ y - (α + β) / 2 ≤ (β - α) / 2 + η
    constructor <;> linarith [hy.1, hy.2]

/-- The flow of a scalar field equal to `1` on `(A, B)` is the translation there. -/
theorem scalar_flow_eq_add_EFE
    (Z : (y : ℝ) → TangentSpace 𝓘(ℝ) y)
    (hZ : ContMDiff 𝓘(ℝ) (𝓘(ℝ)).tangent ∞
      (fun y ↦ (⟨y, Z y⟩ : TangentBundle 𝓘(ℝ) ℝ)))
    (hc : IsCompact (tsupport Z)) {A B s t : ℝ}
    (hone : ∀ y ∈ Ioo A B, Z y = (1 : ℝ))
    (hs : s ∈ Ioo A B) (ht : t ∈ Ioo A B) :
    compactSupportFlowDiffeomorph Z hZ hc (t - s) s = t := by
  let γ : ℝ → ℝ := fun r ↦ s + r
  have hγ : IsMIntegralCurveOn γ Z (Ioo (A - s) (B - s)) := by
    intro r hr
    have hyr : s + r ∈ Ioo A B := ⟨by linarith [hr.1], by linarith [hr.2]⟩
    change HasMFDerivWithinAt 𝓘(ℝ) 𝓘(ℝ) γ (Ioo (A - s) (B - s)) r
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Z (s + r)))
    rw [hone _ hyr]
    exact ((hasDerivAt_id r).const_add s).hasDerivWithinAt.hasFDerivWithinAt.hasMFDerivWithinAt
  let hcomplete := exists_globalIntegralCurve_of_compactSupport Z hZ hc
  have hzero : (0 : ℝ) ∈ Ioo (A - s) (B - s) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless hzero
    (hZ.of_le (by norm_num)) ((curveAt_integralCurve Z hcomplete s).isMIntegralCurveOn _) hγ
    (by simpa only [γ, add_zero] using curveAt_zero Z hcomplete s)
  have hh := heq (show t - s ∈ Ioo (A - s) (B - s) from
    ⟨sub_lt_sub_right ht.1 s, sub_lt_sub_right ht.2 s⟩)
  change curveAt Z hcomplete s (t - s) = t
  simpa only [γ, add_sub_cancel] using hh

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
  [T2Space M] [SecondCountableTopology M]

/-- **Global level transport from a proper submersion on an open set** (D74-10, K1). Let
`g : M → ℝ` be smooth, have compact preimages in the open set `Ω` of compact subsets of
`(a', b')`, and be a submersion on `Ω`. For `[α, β] ⊆ (a', b')` there is a
jointly smooth family of diffeomorphisms `D s` of `M` with `D 0 = id`, `(D s)⁻¹ = D (-s)`, `D s`
the identity off `Ω` and preserving `Ω`, and `g (D (t - g x) x) = t` for `x ∈ Ω`, `g x ∈ [α, β]`,
`t ∈ [α, β]`. -/
theorem exists_global_interval_transport_EFE (Ω : TopologicalSpace.Opens M) (g : M → ℝ)
    (hg : ContMDiff I 𝓘(ℝ) ∞ g) {a' b' : ℝ}
    (hprop : ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo a' b' → IsCompact {x | x ∈ Ω ∧ g x ∈ K})
    (hsub : ∀ x ∈ Ω, Surjective (mfderiv I 𝓘(ℝ) g x)) {α β : ℝ} (hαβ : α ≤ β)
    (ha : a' < α) (hb : β < b') :
    ∃ D : ℝ → M ≃ₘ⟮I, I⟯ M,
      ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × M => D p.1 p.2) ∧
      (∀ y, D 0 y = y) ∧
      (∀ s, (D s).symm = D (-s)) ∧
      (∀ s y, y ∉ Ω → D s y = y) ∧
      (∀ s y, y ∈ Ω → D s y ∈ Ω) ∧
      ∀ x ∈ Ω, g x ∈ Icc α β → ∀ t ∈ Icc α β, g (D (t - g x) x) = t := by
  classical
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  obtain ⟨Z, A, B, hZc, hZsub, hA, hB, hZ1⟩ := exists_scalar_window_field_EFE hαβ ha hb
  let gΩ : Ω → ℝ := fun x => g x
  have hgΩs : ContMDiff I 𝓘(ℝ) ∞ gΩ := hg.comp contMDiff_subtype_val
  have hsurjΩ : ∀ x : Ω, Surjective (mfderiv I 𝓘(ℝ) gΩ x) := fun x => by
    have h := DifferentialGeometry.Topology.Manifold.mfderiv_restrict_open (I := I)
      (J := 𝓘(ℝ, ℝ)) Ω g hg x
    change Surjective (mfderiv I 𝓘(ℝ) (g ∘ Subtype.val) x)
    rw [h]
    exact hsub x x.2
  obtain ⟨X, hrel, hsupp⟩ :=
    exists_smoothDerivativeLift_of_surjective gΩ hgΩs hsurjΩ Z Z.contMDiff
  have hKc : IsCompact {x | x ∈ Ω ∧ g x ∈ tsupport Z} := hprop _ hZc hZsub
  have hXc : IsCompact (tsupport X) := by
    have hK' : IsCompact (gΩ ⁻¹' tsupport Z) := by
      rw [Subtype.isCompact_iff]
      convert hKc using 1
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.2, hx⟩
      · rintro ⟨hy, hyZ⟩
        exact ⟨⟨y, hy⟩, hyZ, rfl⟩
    exact hK'.of_isClosed_subset (isClosed_tsupport _) hsupp
  let Dsub : ℝ → Ω ≃ₘ⟮I, I⟯ Ω := compactSupportFlowDiffeomorph X X.contMDiff hXc
  have hDj : ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × Ω => Dsub p.1 p.2) :=
    contMDiff_globalFlow_joint_of_compactSupport X X.contMDiff hXc
  have hlevel : ∀ s (x : Ω),
      gΩ (Dsub s x) = compactSupportFlowDiffeomorph Z Z.contMDiff hZc s (gΩ x) :=
    compactSupportFlowDiffeomorph_map_of_mfderiv_eq gΩ (hgΩs.of_le (by norm_num)) X X.contMDiff
      hXc Z Z.contMDiff hZc hrel
  have hfix : ∀ s (x : Ω), x ∉ tsupport X → Dsub s x = x := fun s x hx =>
    curveAt_eq_self_of_not_mem_tsupport X X.contMDiff
      (exists_globalIntegralCurve_of_compactSupport X X.contMDiff hXc) hx s
  set K : Set M := Subtype.val '' tsupport X with hKdef
  have hKcl : IsClosed K := (hXc.image continuous_subtype_val).isClosed
  have hKΩ : K ⊆ Ω := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  let F : ℝ → M → M := fun s y => if h : y ∈ Ω then (Dsub s ⟨y, h⟩ : M) else y
  have hFΩ : ∀ s y (h : y ∈ Ω), F s y = Dsub s ⟨y, h⟩ := fun s y h => by simp [F, h]
  have hFout : ∀ s y, y ∉ Ω → F s y = y := fun s y h => by simp [F, h]
  have hFoff : ∀ s y, y ∉ K → F s y = y := by
    intro s y hy
    by_cases h : y ∈ Ω
    · rw [hFΩ s y h, hfix s ⟨y, h⟩ (fun hx => hy ⟨⟨y, h⟩, hx, rfl⟩)]
    · exact hFout s y h
  have hFj : ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × M => F p.1 p.2) := by
    intro p
    by_cases hp : p.2 ∈ Ω
    · let W : TopologicalSpace.Opens (ℝ × M) :=
        ⟨univ ×ˢ (Ω : Set M), isOpen_univ.prod Ω.isOpen⟩
      have hpW : p ∈ W := ⟨mem_univ _, hp⟩
      let e : W → ℝ × Ω := fun w => (w.1.1, ⟨w.1.2, w.2.2⟩)
      have he : ContMDiff (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) ∞ e := by
        refine (contMDiff_fst.comp contMDiff_subtype_val).prodMk ?_
        exact (DifferentialGeometry.Topology.contMDiff_subtypeVal_comp_iff Ω
          (fun w : W => (⟨w.1.2, w.2.2⟩ : Ω))).mp (contMDiff_snd.comp contMDiff_subtype_val)
      have hcomp : (fun w : W => F w.1.1 w.1.2) =
          Subtype.val ∘ (fun q : ℝ × Ω => Dsub q.1 q.2) ∘ e := by
        funext w
        exact hFΩ _ _ w.2.2
      have h1 : ContMDiffAt (𝓘(ℝ).prod I) I ∞ (fun w : W => F w.1.1 w.1.2) ⟨p, hpW⟩ := by
        rw [hcomp]
        exact (contMDiff_subtype_val.comp (hDj.comp he)) _
      exact (contMDiffAt_subtype_iff (f := fun q : ℝ × M => F q.1 q.2)
        (x := ⟨p, hpW⟩)).mp h1
    · have hpK : p.2 ∉ K := fun h => hp (hKΩ h)
      have hev : (fun q : ℝ × M => F q.1 q.2) =ᶠ[𝓝 p] (fun q => q.2) := by
        have hn : (univ ×ˢ Kᶜ : Set (ℝ × M)) ∈ 𝓝 p :=
          (isOpen_univ.prod hKcl.isOpen_compl).mem_nhds ⟨mem_univ _, hpK⟩
        filter_upwards [hn] with q hq using hFoff q.1 q.2 hq.2
      exact contMDiffAt_snd.congr_of_eventuallyEq hev
  have hsymm : ∀ s, (Dsub s).symm = Dsub (-s) :=
    compactSupportFlowDiffeomorph_symm X X.contMDiff hXc
  have hFinv : ∀ s y, F (-s) (F s y) = y := by
    intro s y
    by_cases hy : y ∈ Ω
    · have h1 := hFΩ s y hy
      have hmem : F s y ∈ Ω := by
        rw [h1]
        exact (Dsub s ⟨y, hy⟩).2
      rw [hFΩ (-s) _ hmem]
      have h2 : (⟨F s y, hmem⟩ : Ω) = Dsub s ⟨y, hy⟩ := Subtype.ext h1
      rw [h2, ← hsymm, Diffeomorph.symm_apply_apply]
    · rw [hFout s y hy, hFout (-s) y hy]
  let D : ℝ → M ≃ₘ⟮I, I⟯ M := fun s =>
    { toEquiv := ⟨F s, F (-s), hFinv s, fun y => by simpa only [neg_neg] using hFinv (-s) y⟩
      contMDiff_toFun := hFj.comp (contMDiff_const.prodMk contMDiff_id)
      contMDiff_invFun := hFj.comp (contMDiff_const.prodMk contMDiff_id) }
  refine ⟨D, hFj, ?_, ?_, hFout, ?_, ?_⟩
  · intro y
    change F 0 y = y
    by_cases hy : y ∈ Ω
    · rw [hFΩ 0 y hy]
      change ((compactSupportFlowDiffeomorph X X.contMDiff hXc 0) ⟨y, hy⟩ : M) = y
      rw [compactSupportFlowDiffeomorph_zero]
      rfl
    · exact hFout 0 y hy
  · intro s
    exact Diffeomorph.ext fun y => rfl
  · intro s y hy
    change F s y ∈ Ω
    rw [hFΩ s y hy]
    exact (Dsub s ⟨y, hy⟩).2
  · intro x hx hgx t ht
    change g (F (t - g x) x) = t
    rw [hFΩ _ x hx]
    have h := hlevel (t - g x) ⟨x, hx⟩
    change g (Dsub (t - g x) ⟨x, hx⟩ : M) = _ at h
    rw [h]
    exact scalar_flow_eq_add_EFE Z Z.contMDiff hZc hZ1
      ⟨by linarith [hgx.1], by linarith [hgx.2]⟩ ⟨by linarith [ht.1], by linarith [ht.2]⟩

end DifferentialGeometry.Topology.Ehresmann
