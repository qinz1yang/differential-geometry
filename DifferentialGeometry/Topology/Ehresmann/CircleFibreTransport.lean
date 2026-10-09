import DifferentialGeometry.Topology.Ehresmann.ProperSubmersion
import DifferentialGeometry.Topology.Manifold.AddCircle.Circle
import DifferentialGeometry.Topology.Embedding.Lift
import DifferentialGeometry.Topology.Manifold.InjectiveLocalDiffeomorph
import DifferentialGeometry.Topology.Diffeomorph.FiberwiseAffine

/-!
# Fibre bundles over the circle: cutting along one fibre

Chapter-14 assembly, lane ASM-L3 (design `docs/geometrization/chapter14/design-fc39-fc42-assembly-20261004.md`,
§3 L3). For a smooth submersion `p : M → S¹` of a compact boundaryless manifold the vector field
`∂θ` of the unit circle (`AddCircle.parameterTangent`) lifts to a compactly supported field on `M`
(`exists_compactlySupported_relatedFlow_of_surjective`); its flow `Φ` covers the rotation,
`p (Φ t x) = p x + t` (`exists_addCircle_flow`). Cutting along the fibre `f : F → M` over `0` gives
the cut map `cutMap Φ f (z, s) = Φ s (f z)`, the monodromy `f (monodromy z) = Φ 1 (f z)`
(`cutMap_add_one`), the fibre coordinate through the embedding (`fibreCoord`), and the strip
charts: on `F × (α, α + 1)` the cut map is a partial diffeomorphism onto `p⁻¹ (S¹ ∖ {α})` with
inverse (fibre coordinate, angle) (`exists_stripChart`), hence a local diffeomorphism with bijective
differential everywhere. `exists_circleCut` packages the circle-valued form used by the L3
statements (fibre over `1 : Circle`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Ehresmann.CircleFibre

open DifferentialGeometry.Analysis.ODE

theorem isCompact_tsupport_parameterTangent :
    IsCompact (tsupport AddCircle.parameterTangent) :=
  (isClosed_tsupport _).isCompact

theorem parameterTangentFlow_apply (t : ℝ) (y : AddCircle (1 : ℝ)) :
    compactSupportFlowDiffeomorph AddCircle.parameterTangent AddCircle.contMDiff_parameterTangent
      isCompact_tsupport_parameterTangent t y = y + t := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  let γ : ℝ → AddCircle (1 : ℝ) := fun r => ((x + r : ℝ) : AddCircle (1 : ℝ))
  have hγ : IsMIntegralCurve γ AddCircle.parameterTangent := by
    intro r
    have hcoe : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) (x + r)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) (x + r)) :=
      (AddCircle.contMDiff_coe.mdifferentiableAt (by decide)).hasMFDerivAt
    have htr : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r : ℝ => x + r) r
        (ContinuousLinearMap.id ℝ ℝ) :=
      ((hasFDerivAt_id r).const_add x).hasMFDerivAt
    have hD : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) (x + r)).comp
        (ContinuousLinearMap.id ℝ ℝ) =
        (1 : ℝ →L[ℝ] ℝ).smulRight (AddCircle.parameterTangent (γ r)) := by
      apply ContinuousLinearMap.ext_ring
      change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) (x + r) 1 =
        (1 : ℝ) • AddCircle.parameterTangent (γ r)
      rw [one_smul]
      exact (AddCircle.parameterTangent_coe (x + r)).symm
    exact (hcoe.comp r htr).congr_mfderiv hD
  let hcomplete := exists_globalIntegralCurve_of_compactSupport AddCircle.parameterTangent
    AddCircle.contMDiff_parameterTangent isCompact_tsupport_parameterTangent
  have heq := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0)
    (AddCircle.contMDiff_parameterTangent.of_le (by norm_num))
    (curveAt_integralCurve _ hcomplete (x : AddCircle (1 : ℝ))) hγ
    (by rw [curveAt_zero]; simp [γ])
  rw [compactSupportFlowDiffeomorph_apply]
  change curveAt _ hcomplete _ t = _
  rw [heq]
  simp [γ]


/-! ### The angle lift off one point of the circle -/

/-- The representative in `[α, α + 1)` of a point of the unit circle. -/
def angleLift (α : ℝ) (y : AddCircle (1 : ℝ)) : ℝ := (AddCircle.equivIco 1 α y : ℝ)

theorem coe_angleLift (α : ℝ) (y : AddCircle (1 : ℝ)) :
    ((angleLift α y : ℝ) : AddCircle (1 : ℝ)) = y :=
  AddCircle.coe_equivIco

theorem angleLift_mem_Ico (α : ℝ) (y : AddCircle (1 : ℝ)) : angleLift α y ∈ Ico α (α + 1) :=
  (AddCircle.equivIco 1 α y).2

theorem angleLift_coe {α x : ℝ} (hx : x ∈ Ico α (α + 1)) :
    angleLift α (x : AddCircle (1 : ℝ)) = x := by
  unfold angleLift
  rw [AddCircle.equivIco_coe_eq hx]

theorem angleLift_mem_Ioo {α : ℝ} {y : AddCircle (1 : ℝ)} (hy : y ≠ (α : AddCircle (1 : ℝ))) :
    angleLift α y ∈ Ioo α (α + 1) := by
  refine ⟨lt_of_le_of_ne (angleLift_mem_Ico α y).1 fun h => hy ?_, (angleLift_mem_Ico α y).2⟩
  rw [← coe_angleLift α y, ← h]

theorem contMDiffAt_angleLift {α : ℝ} {y : AddCircle (1 : ℝ)} (hy : y ≠ (α : AddCircle (1 : ℝ))) :
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (angleLift α) y := by
  set s₀ := angleLift α y with hs₀
  have hd := AddCircle.isLocalDiffeomorph_coe s₀
  have hy₀ : ((s₀ : ℝ) : AddCircle (1 : ℝ)) = y := coe_angleLift α y
  have hL : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ hd.localInverse y := by
    rw [← hy₀]
    exact hd.contMDiffAt_localInverse
  apply hL.congr_of_eventuallyEq
  have hL0 : hd.localInverse y = s₀ := by
    rw [← hy₀]
    exact hd.localInverse_left_inv hd.localInverse_mem_target
  have hcont : ContinuousAt hd.localInverse y := by
    rw [← hy₀]
    exact hd.continuousAt_localInverse
  have hIoo : ∀ᶠ y' in 𝓝 y, hd.localInverse y' ∈ Ioo α (α + 1) :=
    hcont.preimage_mem_nhds (by rw [hL0]; exact isOpen_Ioo.mem_nhds (angleLift_mem_Ioo hy))
  have hright : ∀ᶠ y' in 𝓝 y,
      ((hd.localInverse y' : ℝ) : AddCircle (1 : ℝ)) = y' := by
    have h := hd.localInverse_eventuallyEq_right
    rw [hy₀] at h
    exact h
  filter_upwards [hIoo, hright] with y' h₁ h₂
  conv_lhs => rw [← h₂]
  exact angleLift_coe (Ioo_subset_Ico_self h₁)

section Flow

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]

/-- **Circle flow.** A smooth submersion `p : M → AddCircle 1` of a compact boundaryless manifold
has a smooth flow by diffeomorphisms covering the unit-speed rotation: `p (Φ t x) = p x + t`. -/
theorem exists_addCircle_flow (p : M → AddCircle (1 : ℝ)) (hp : ContMDiff I 𝓘(ℝ, ℝ) ∞ p)
    (hsub : ∀ x, Surjective (mfderiv I 𝓘(ℝ, ℝ) p x)) :
    ∃ Φ : ℝ → M ≃ₘ⟮I, I⟯ M,
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2) ∧
      Φ 0 = Diffeomorph.refl I M ∞ ∧
      (∀ s t, (Φ s).trans (Φ t) = Φ (s + t)) ∧
      ∀ t x, p (Φ t x) = p x + t := by
  obtain ⟨X, hXc, -, -, hflow⟩ := exists_compactlySupported_relatedFlow_of_surjective p
    hp.continuous.isProperMap hp hsub AddCircle.parameterTangent
    AddCircle.contMDiff_parameterTangent isCompact_tsupport_parameterTangent
  refine ⟨compactSupportFlowDiffeomorph X X.contMDiff hXc,
    contMDiff_globalFlow_joint_of_compactSupport X X.contMDiff hXc,
    compactSupportFlowDiffeomorph_zero X X.contMDiff hXc,
    compactSupportFlowDiffeomorph_trans X X.contMDiff hXc, ?_⟩
  intro t x
  rw [hflow t x, parameterTangentFlow_apply]

end Flow


theorem coe_ne_of_mem_Ioo {α x : ℝ} (hx : x ∈ Ioo α (α + 1)) :
    (x : AddCircle (1 : ℝ)) ≠ (α : AddCircle (1 : ℝ)) := by
  intro h
  have h₁ := angleLift_coe (Ioo_subset_Ico_self hx)
  rw [h, angleLift_coe ⟨le_rfl, lt_add_one α⟩] at h₁
  exact hx.1.ne h₁

theorem eq_of_coe_eq_of_mem_Ico {α x y : ℝ} (hx : x ∈ Ico α (α + 1)) (hy : y ∈ Ico α (α + 1))
    (h : (x : AddCircle (1 : ℝ)) = y) : x = y := by
  rw [← angleLift_coe hx, ← angleLift_coe hy, h]

theorem p_of_mem_range {M F : Type*} {p : M → AddCircle (1 : ℝ)} {f : F → M}
    (hr : range f = p ⁻¹' {0}) (z : F) : p (f z) = 0 := by
  have h : f z ∈ p ⁻¹' {0} := hr ▸ mem_range_self z
  exact h

/-! ### Cutting a circle flow along one fibre -/

section Fibre

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] {F : Type*}

/-- The cut map of a flow along a fibre parametrization: `(z, s) ↦ Φ s (f z)`. -/
def cutMap (Φ : ℝ → M ≃ₘ⟮I, I⟯ M) (f : F → M) (q : F × ℝ) : M := Φ q.2 (f q.1)

theorem cutMap_apply (Φ : ℝ → M ≃ₘ⟮I, I⟯ M) (f : F → M) (z : F) (s : ℝ) :
    cutMap Φ f (z, s) = Φ s (f z) := rfl

theorem flow_apply_apply {Φ : ℝ → M ≃ₘ⟮I, I⟯ M}
    (hΦadd : ∀ s t, (Φ s).trans (Φ t) = Φ (s + t)) (s t : ℝ) (x : M) :
    Φ t (Φ s x) = Φ (s + t) x := by
  rw [← hΦadd]
  rfl

theorem flow_neg_apply {Φ : ℝ → M ≃ₘ⟮I, I⟯ M} (hΦ0 : Φ 0 = Diffeomorph.refl I M ∞)
    (hΦadd : ∀ s t, (Φ s).trans (Φ t) = Φ (s + t)) (s : ℝ) (x : M) :
    Φ (-s) (Φ s x) = x := by
  rw [flow_apply_apply hΦadd, add_neg_cancel, hΦ0]
  rfl

theorem flow_apply_neg {Φ : ℝ → M ≃ₘ⟮I, I⟯ M} (hΦ0 : Φ 0 = Diffeomorph.refl I M ∞)
    (hΦadd : ∀ s t, (Φ s).trans (Φ t) = Φ (s + t)) (s : ℝ) (x : M) :
    Φ s (Φ (-s) x) = x := by
  rw [flow_apply_apply hΦadd, neg_add_cancel, hΦ0]
  rfl

variable {Φ : ℝ → M ≃ₘ⟮I, I⟯ M} {p : M → AddCircle (1 : ℝ)} {f : F → M}

theorem p_cutMap (hΦp : ∀ t x, p (Φ t x) = p x + t) (hr : range f = p ⁻¹' {0}) (q : F × ℝ) :
    p (cutMap Φ f q) = q.2 := by
  rw [cutMap, hΦp, p_of_mem_range hr, zero_add]

/-- The return of a point to the fibre over `0` along the flow, by its angle in `[α, α + 1)`. -/
def fibreReturn (Φ : ℝ → M ≃ₘ⟮I, I⟯ M) (p : M → AddCircle (1 : ℝ)) (α : ℝ) (x : M) : M :=
  Φ (-angleLift α (p x)) x

theorem p_fibreReturn (hΦp : ∀ t x, p (Φ t x) = p x + t) (α : ℝ) (x : M) :
    p (fibreReturn Φ p α x) = 0 := by
  rw [fibreReturn, hΦp, AddCircle.coe_neg, coe_angleLift, add_neg_cancel]

theorem range_fibreReturn_subset (hΦp : ∀ t x, p (Φ t x) = p x + t)
    (hr : range f = p ⁻¹' {0}) (α : ℝ) : range (fibreReturn Φ p α) ⊆ range f := by
  rintro _ ⟨x, rfl⟩
  rw [hr]
  exact p_fibreReturn hΦp α x

theorem range_flow_fibre_subset (hΦp : ∀ t x, p (Φ t x) = p x + t) (hr : range f = p ⁻¹' {0})
    {t : ℝ} (ht : (t : AddCircle (1 : ℝ)) = 0) : range (fun z => Φ t (f z)) ⊆ range f := by
  rintro _ ⟨z, rfl⟩
  rw [hr]
  change p (Φ t (f z)) = 0
  rw [hΦp, p_of_mem_range hr, zero_add, ht]

theorem coe_neg_one_addCircle : ((-1 : ℝ) : AddCircle (1 : ℝ)) = 0 := by
  rw [AddCircle.coe_neg, AddCircle.coe_period, neg_zero]

variable {EF HF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF]
  [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF} [TopologicalSpace F] [ChartedSpace HF F]

theorem contMDiff_cutMap (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2))
    (hf : ContMDiff IF I ∞ f) : ContMDiff (IF.prod 𝓘(ℝ, ℝ)) I ∞ (cutMap Φ f) :=
  hΦ.comp (contMDiff_snd.prodMk (hf.comp contMDiff_fst))

/-- The fibre coordinate of a point: its return to the fibre, read through `f`. -/
def fibreCoord (hf : IsSmoothEmbedding IF I ∞ f) (hΦp : ∀ t x, p (Φ t x) = p x + t)
    (hr : range f = p ⁻¹' {0}) (α : ℝ) : M → F :=
  hf.lift (fibreReturn Φ p α) (range_fibreReturn_subset hΦp hr α)

theorem f_fibreCoord (hf : IsSmoothEmbedding IF I ∞ f) (hΦp : ∀ t x, p (Φ t x) = p x + t)
    (hr : range f = p ⁻¹' {0}) (α : ℝ) (x : M) :
    f (fibreCoord hf hΦp hr α x) = fibreReturn Φ p α x :=
  hf.comp_lift _ x

theorem fibreCoord_eq_iff (hf : IsSmoothEmbedding IF I ∞ f) (hΦp : ∀ t x, p (Φ t x) = p x + t)
    (hr : range f = p ⁻¹' {0}) {α : ℝ} {x : M} {z : F} :
    fibreCoord hf hΦp hr α x = z ↔ f z = fibreReturn Φ p α x := by
  constructor
  · rintro rfl
    exact f_fibreCoord hf hΦp hr α x
  · intro h
    exact hf.isEmbedding.injective ((f_fibreCoord hf hΦp hr α x).trans h.symm)

theorem contMDiffAt_fibreCoord (hf : IsSmoothEmbedding IF I ∞ f)
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2))
    (hp : ContMDiff I 𝓘(ℝ, ℝ) ∞ p) (hΦp : ∀ t x, p (Φ t x) = p x + t)
    (hr : range f = p ⁻¹' {0}) {α : ℝ} {x : M} (hx : p x ≠ (α : AddCircle (1 : ℝ))) :
    ContMDiffAt I IF ∞ (fibreCoord hf hΦp hr α) x := by
  have hret : ContMDiffAt I I ∞ (fibreReturn Φ p α) x :=
    hΦ.contMDiffAt.comp x
      ((((contMDiffAt_angleLift hx).comp x hp.contMDiffAt).neg).prodMk contMDiffAt_id)
  have hcomp : f ∘ fibreCoord hf hΦp hr α = fibreReturn Φ p α :=
    funext (f_fibreCoord hf hΦp hr α)
  refine (ContMDiffAt.iff_comp_isImmersionAt (hf.isImmersion.isImmersionAt _)).mpr ⟨?_, ?_⟩
  · rw [hf.isEmbedding.isInducing.continuousAt_iff, hcomp]
    exact hret.continuousAt
  · rw [hcomp]
    exact hret

/-- The monodromy of the fibre parametrization `f` along the flow:
`f (monodromy z) = Φ 1 (f z)`. -/
def monodromy (hf : IsSmoothEmbedding IF I ∞ f) (hΦ0 : Φ 0 = Diffeomorph.refl I M ∞)
    (hΦadd : ∀ s t, (Φ s).trans (Φ t) = Φ (s + t)) (hΦp : ∀ t x, p (Φ t x) = p x + t)
    (hr : range f = p ⁻¹' {0}) : F ≃ₘ⟮IF, IF⟯ F where
  toFun := hf.lift (fun z => Φ 1 (f z)) (range_flow_fibre_subset hΦp hr (AddCircle.coe_period 1))
  invFun := hf.lift (fun z => Φ (-1) (f z)) (range_flow_fibre_subset hΦp hr coe_neg_one_addCircle)
  left_inv z := hf.isEmbedding.injective (by
    rw [hf.comp_lift, hf.comp_lift, flow_neg_apply hΦ0 hΦadd])
  right_inv z := hf.isEmbedding.injective (by
    rw [hf.comp_lift, hf.comp_lift, flow_apply_neg hΦ0 hΦadd])
  contMDiff_toFun := hf.contMDiff_lift (g := fun z => Φ 1 (f z))
    ((Φ 1).contMDiff.comp hf.isImmersion.contMDiff)
    (range_flow_fibre_subset hΦp hr (AddCircle.coe_period 1))
  contMDiff_invFun := hf.contMDiff_lift (g := fun z => Φ (-1) (f z))
    ((Φ (-1)).contMDiff.comp hf.isImmersion.contMDiff)
    (range_flow_fibre_subset hΦp hr coe_neg_one_addCircle)

theorem f_monodromy (hf : IsSmoothEmbedding IF I ∞ f) (hΦ0 : Φ 0 = Diffeomorph.refl I M ∞)
    (hΦadd : ∀ s t, (Φ s).trans (Φ t) = Φ (s + t)) (hΦp : ∀ t x, p (Φ t x) = p x + t)
    (hr : range f = p ⁻¹' {0}) (z : F) :
    f (monodromy hf hΦ0 hΦadd hΦp hr z) = Φ 1 (f z) :=
  hf.comp_lift (g := fun z => Φ 1 (f z))
    (range_flow_fibre_subset hΦp hr (AddCircle.coe_period 1)) z

theorem f_monodromy_symm (hf : IsSmoothEmbedding IF I ∞ f) (hΦ0 : Φ 0 = Diffeomorph.refl I M ∞)
    (hΦadd : ∀ s t, (Φ s).trans (Φ t) = Φ (s + t)) (hΦp : ∀ t x, p (Φ t x) = p x + t)
    (hr : range f = p ⁻¹' {0}) (z : F) :
    f ((monodromy hf hΦ0 hΦadd hΦp hr).symm z) = Φ (-1) (f z) :=
  hf.comp_lift (g := fun z => Φ (-1) (f z))
    (range_flow_fibre_subset hΦp hr coe_neg_one_addCircle) z

/-- Endpoint matching: the end `s + 1` of the cut map is the start `s`, twisted by the
monodromy. -/
theorem cutMap_add_one (hf : IsSmoothEmbedding IF I ∞ f) (hΦ0 : Φ 0 = Diffeomorph.refl I M ∞)
    (hΦadd : ∀ s t, (Φ s).trans (Φ t) = Φ (s + t)) (hΦp : ∀ t x, p (Φ t x) = p x + t)
    (hr : range f = p ⁻¹' {0}) (z : F) (s : ℝ) :
    cutMap Φ f (z, s + 1) = cutMap Φ f (monodromy hf hΦ0 hΦadd hΦp hr z, s) := by
  rw [cutMap_apply, cutMap_apply, f_monodromy hf hΦ0 hΦadd hΦp hr, flow_apply_apply hΦadd, add_comm]

theorem cutMap_surjective (hf : IsSmoothEmbedding IF I ∞ f) (hΦ0 : Φ 0 = Diffeomorph.refl I M ∞)
    (hΦadd : ∀ s t, (Φ s).trans (Φ t) = Φ (s + t)) (hΦp : ∀ t x, p (Φ t x) = p x + t)
    (hr : range f = p ⁻¹' {0}) (α : ℝ) (x : M) :
    cutMap Φ f (fibreCoord hf hΦp hr α x, angleLift α (p x)) = x := by
  rw [cutMap_apply, f_fibreCoord hf hΦp hr, fibreReturn, flow_apply_neg hΦ0 hΦadd]

theorem cutMap_injOn (hf : IsSmoothEmbedding IF I ∞ f) (hΦp : ∀ t x, p (Φ t x) = p x + t)
    (hr : range f = p ⁻¹' {0}) (α : ℝ) : InjOn (cutMap Φ f) (univ ×ˢ Ico α (α + 1)) := by
  rintro ⟨z, s⟩ ⟨-, hs⟩ ⟨z', s'⟩ ⟨-, hs'⟩ h
  have hss : s = s' := eq_of_coe_eq_of_mem_Ico hs hs' (by
    have := congrArg p h
    rwa [p_cutMap hΦp hr, p_cutMap hΦp hr] at this)
  subst hss
  rw [cutMap_apply, cutMap_apply] at h
  rw [hf.isEmbedding.injective ((Φ s).injective h)]

theorem fibreCoord_cutMap (hf : IsSmoothEmbedding IF I ∞ f) (hΦ0 : Φ 0 = Diffeomorph.refl I M ∞)
    (hΦadd : ∀ s t, (Φ s).trans (Φ t) = Φ (s + t)) (hΦp : ∀ t x, p (Φ t x) = p x + t)
    (hr : range f = p ⁻¹' {0}) {α : ℝ} {q : F × ℝ} (hq : q.2 ∈ Ico α (α + 1)) :
    fibreCoord hf hΦp hr α (cutMap Φ f q) = q.1 ∧ angleLift α (p (cutMap Φ f q)) = q.2 := by
  have hθ : angleLift α (p (cutMap Φ f q)) = q.2 := by
    rw [p_cutMap hΦp hr, angleLift_coe hq]
  refine ⟨(fibreCoord_eq_iff hf hΦp hr).mpr ?_, hθ⟩
  rw [fibreReturn, hθ, cutMap, flow_neg_apply hΦ0 hΦadd]

/-- **Strip chart (interval trivialization with endpoints, open form).** On the strip
`F × (α, α + 1)` the cut map is a diffeomorphism onto the complement of the fibre over `α`; its
inverse is (fibre coordinate, angle). -/
theorem exists_stripChart (hf : IsSmoothEmbedding IF I ∞ f)
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2))
    (hΦ0 : Φ 0 = Diffeomorph.refl I M ∞) (hΦadd : ∀ s t, (Φ s).trans (Φ t) = Φ (s + t))
    (hp : ContMDiff I 𝓘(ℝ, ℝ) ∞ p) (hΦp : ∀ t x, p (Φ t x) = p x + t)
    (hr : range f = p ⁻¹' {0}) (α : ℝ) :
    ∃ d : PartialDiffeomorph (IF.prod 𝓘(ℝ, ℝ)) I (F × ℝ) M ∞,
      d.source = univ ×ˢ Ioo α (α + 1) ∧ d.target = p ⁻¹' {(α : AddCircle (1 : ℝ))}ᶜ ∧
      (d : F × ℝ → M) = cutMap Φ f ∧
      ∀ x, d.symm x = (fibreCoord hf hΦp hr α x, angleLift α (p x)) := by
  refine ⟨{ toPartialEquiv :=
              { toFun := cutMap Φ f
                invFun := fun x => (fibreCoord hf hΦp hr α x, angleLift α (p x))
                source := univ ×ˢ Ioo α (α + 1)
                target := p ⁻¹' {(α : AddCircle (1 : ℝ))}ᶜ
                map_source' := ?_
                map_target' := ?_
                left_inv' := ?_
                right_inv' := ?_ }
            open_source := isOpen_univ.prod isOpen_Ioo
            open_target := isOpen_compl_singleton.preimage hp.continuous
            contMDiffOn_toFun := (contMDiff_cutMap hΦ hf.isImmersion.contMDiff).contMDiffOn
            contMDiffOn_invFun := ?_ }, rfl, rfl, rfl, fun _ => rfl⟩
  · rintro q ⟨-, hq⟩
    change p (cutMap Φ f q) ≠ _
    rw [p_cutMap hΦp hr]
    exact coe_ne_of_mem_Ioo hq
  · intro x hx
    exact ⟨mem_univ _, angleLift_mem_Ioo hx⟩
  · rintro q ⟨-, hq⟩
    obtain ⟨h₁, h₂⟩ := fibreCoord_cutMap hf hΦ0 hΦadd hΦp hr (Ioo_subset_Ico_self hq)
    exact Prod.ext h₁ h₂
  · intro x _
    exact cutMap_surjective hf hΦ0 hΦadd hΦp hr α x
  · intro x hx
    exact ((contMDiffAt_fibreCoord hf hΦ hp hΦp hr hx).prodMk
      ((contMDiffAt_angleLift hx).comp x hp.contMDiffAt)).contMDiffWithinAt

theorem isLocalDiffeomorph_cutMap (hf : IsSmoothEmbedding IF I ∞ f)
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2))
    (hΦ0 : Φ 0 = Diffeomorph.refl I M ∞) (hΦadd : ∀ s t, (Φ s).trans (Φ t) = Φ (s + t))
    (hp : ContMDiff I 𝓘(ℝ, ℝ) ∞ p) (hΦp : ∀ t x, p (Φ t x) = p x + t)
    (hr : range f = p ⁻¹' {0}) : IsLocalDiffeomorph (IF.prod 𝓘(ℝ, ℝ)) I ∞ (cutMap Φ f) := by
  intro q
  obtain ⟨d, hds, -, hdf, -⟩ := exists_stripChart hf hΦ hΦ0 hΦadd hp hΦp hr (q.2 - 1 / 2)
  have hq : q ∈ d.source := by
    rw [hds]
    exact ⟨mem_univ _, by constructor <;> linarith⟩
  rw [← hdf]
  exact d.isLocalDiffeomorphAt _ _ _ hq

theorem bijective_mfderiv_cutMap (hf : IsSmoothEmbedding IF I ∞ f)
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2))
    (hΦ0 : Φ 0 = Diffeomorph.refl I M ∞) (hΦadd : ∀ s t, (Φ s).trans (Φ t) = Φ (s + t))
    (hp : ContMDiff I 𝓘(ℝ, ℝ) ∞ p) (hΦp : ∀ t x, p (Φ t x) = p x + t)
    (hr : range f = p ⁻¹' {0}) (q : F × ℝ) :
    Bijective (mfderiv (IF.prod 𝓘(ℝ, ℝ)) I (cutMap Φ f) q) := by
  obtain ⟨e, he⟩ :=
    (isLocalDiffeomorph_cutMap hf hΦ hΦ0 hΦadd hp hΦp hr q).isInvertible_mfderiv (by simp)
  rw [← he]
  exact e.bijective

/-- **Affine strip chart.** Any affine reparametrization `s ↦ a + b s` (`b > 0`) of the cut map
is a partial diffeomorphism on a strip `F × (u, v)` of `b`-length at most one. -/
theorem exists_affineStripChart [Nonempty F]
    (hf : IsSmoothEmbedding IF I ∞ f)
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2))
    (hΦ0 : Φ 0 = Diffeomorph.refl I M ∞) (hΦadd : ∀ s t, (Φ s).trans (Φ t) = Φ (s + t))
    (hp : ContMDiff I 𝓘(ℝ, ℝ) ∞ p) (hΦp : ∀ t x, p (Φ t x) = p x + t)
    (hr : range f = p ⁻¹' {0}) {a b u v : ℝ} (hb : 0 < b) (hbv : b * (v - u) ≤ 1) :
    ∃ d : PartialDiffeomorph (IF.prod 𝓘(ℝ, ℝ)) I (F × ℝ) M ∞,
      d.source = univ ×ˢ Ioo u v ∧
        (d : F × ℝ → M) = fun q => cutMap Φ f (q.1, a + b * q.2) := by
  let R := Diffeomorph.fiberwiseAffine (I := IF) (n := ∞) (fun _ : F => a) (fun _ => b)
    contMDiff_const contMDiff_const (fun _ => hb.ne')
  have hloc : IsLocalDiffeomorph (IF.prod 𝓘(ℝ, ℝ)) I ∞
      (fun q : F × ℝ => cutMap Φ f (q.1, a + b * q.2)) := fun q =>
    IsLocalDiffeomorphAt.comp (hf := R.isLocalDiffeomorph q)
      (hg := isLocalDiffeomorph_cutMap hf hΦ hΦ0 hΦadd hp hΦp hr (R q))
  have hmem : ∀ s ∈ Ioo u v, a + b * s ∈ Ico (a + b * u) (a + b * u + 1) := by
    intro s hs
    constructor
    · nlinarith [hs.1]
    · nlinarith [hs.2]
  have hinj : InjOn (fun q : F × ℝ => cutMap Φ f (q.1, a + b * q.2)) (univ ×ˢ Ioo u v) := by
    rintro q ⟨-, hq⟩ q' ⟨-, hq'⟩ h
    have h' := cutMap_injOn hf hΦp hr (a + b * u) ⟨mem_univ _, hmem _ hq⟩
      ⟨mem_univ _, hmem _ hq'⟩ h
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h'
    exact Prod.ext h1 (mul_left_cancel₀ hb.ne' (add_left_cancel h2))
  obtain ⟨d, hds, -, hdf⟩ := DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_of_injOn
    (isOpen_univ.prod isOpen_Ioo) (hloc.isLocalDiffeomorphOn _) hinj
  exact ⟨d, hds, hdf⟩

end Fibre

/-! ### Circle-valued submersions -/

theorem diffeomorphCircle_coe (t : ℝ) :
    AddCircle.diffeomorphCircle (t : AddCircle (1 : ℝ)) = Circle.exp (2 * Real.pi * t) := by
  change AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero (t : AddCircle (1 : ℝ)) = _
  rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
  congr 1
  ring

theorem diffeomorphCircle_zero : AddCircle.diffeomorphCircle (0 : AddCircle (1 : ℝ)) = 1 := by
  have h := diffeomorphCircle_coe 0
  rw [mul_zero, Circle.exp_zero] at h
  exact h

section CircleCut

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
  {EF HF F : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF]
  [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF}
  [TopologicalSpace F] [ChartedSpace HF F] [Nonempty F]

/-- **Cut of a fibre bundle over the circle along one fibre (interval trivialization with
endpoints).** For a smooth submersion `p : M → S¹` of a compact boundaryless manifold and a
smooth embedding `f` onto the fibre over `1`, there are a smooth cut map `Ψ : F × ℝ → M` and a
monodromy diffeomorphism `φ` of `F` such that `Ψ (·, 0) = f`, `p ∘ Ψ` is the angle,
the ends match through `φ` (`Ψ (z, s + 1) = Ψ (φ z, s)`), `Ψ` is injective on every half-open
strip of length one and maps each such strip onto `M`, and every affine reparametrization on a strip of length at most one
is a partial diffeomorphism. -/
theorem exists_circleCut (p : M → Circle) (hp : ContMDiff I (𝓡 1) ∞ p)
    (hsub : ∀ x, Surjective (mfderiv I (𝓡 1) p x)) (f : F → M)
    (hf : IsSmoothEmbedding IF I ∞ f) (hr : range f = p ⁻¹' {1}) :
    ∃ (Ψ : F × ℝ → M) (φ : F ≃ₘ⟮IF, IF⟯ F),
      ContMDiff (IF.prod 𝓘(ℝ, ℝ)) I ∞ Ψ ∧
      (∀ z, Ψ (z, 0) = f z) ∧
      (∀ q, p (Ψ q) = Circle.exp (2 * Real.pi * q.2)) ∧
      (∀ z s, Ψ (z, s + 1) = Ψ (φ z, s)) ∧
      (∀ α, InjOn Ψ (univ ×ˢ Ico α (α + 1))) ∧
      (∀ α x, ∃ z, ∃ t ∈ Ico α (α + 1), Ψ (z, t) = x) ∧
      ∀ a b u v : ℝ, 0 < b → b * (v - u) ≤ 1 →
        ∃ d : PartialDiffeomorph (IF.prod 𝓘(ℝ, ℝ)) I (F × ℝ) M ∞,
          d.source = univ ×ˢ Ioo u v ∧ (d : F × ℝ → M) = fun q => Ψ (q.1, a + b * q.2) := by
  let e := AddCircle.diffeomorphCircle
  let p' : M → AddCircle (1 : ℝ) := fun x => e.symm (p x)
  have hp' : ContMDiff I 𝓘(ℝ, ℝ) ∞ p' := e.symm.contMDiff.comp hp
  have hsub' : ∀ x, Surjective (mfderiv I 𝓘(ℝ, ℝ) p' x) := by
    intro x
    have hcomp := mfderiv_comp (I := I) x
      (e.symm.contMDiff.mdifferentiableAt (by simp) (x := p x))
      (hp.mdifferentiableAt (by simp))
    change Surjective (mfderiv I 𝓘(ℝ, ℝ) (e.symm ∘ p) x)
    rw [hcomp]
    obtain ⟨L, hL⟩ := e.symm.isInvertible_mfderiv (x := p x) (by simp)
    rw [ContinuousLinearMap.coe_comp, ← hL]
    exact L.surjective.comp (hsub x)
  have hr' : range f = p' ⁻¹' {0} := by
    rw [hr]
    ext x
    simp only [mem_preimage, mem_singleton_iff, p']
    constructor
    · intro h
      rw [h, ← diffeomorphCircle_zero]
      exact e.symm_apply_apply 0
    · intro h
      rw [← e.apply_symm_apply (p x), h]
      exact diffeomorphCircle_zero
  obtain ⟨Φ, hΦ, hΦ0, hΦadd, hΦp⟩ := exists_addCircle_flow p' hp' hsub'
  have hpΨ : ∀ q, p (cutMap Φ f q) = Circle.exp (2 * Real.pi * q.2) := by
    intro q
    rw [← diffeomorphCircle_coe, ← p_cutMap hΦp hr' q]
    exact (e.apply_symm_apply _).symm
  refine ⟨cutMap Φ f, monodromy hf hΦ0 hΦadd hΦp hr',
    contMDiff_cutMap hΦ hf.isImmersion.contMDiff, fun z => ?_, hpΨ,
    cutMap_add_one hf hΦ0 hΦadd hΦp hr', cutMap_injOn hf hΦp hr',
    fun α x => ⟨_, _, angleLift_mem_Ico α (p' x), cutMap_surjective hf hΦ0 hΦadd hΦp hr' α x⟩,
    fun a b u v hb hbv => exists_affineStripChart hf hΦ hΦ0 hΦadd hp' hΦp hr' hb hbv⟩
  rw [cutMap_apply, hΦ0]
  rfl

end CircleCut

end DifferentialGeometry.Topology.Ehresmann.CircleFibre
