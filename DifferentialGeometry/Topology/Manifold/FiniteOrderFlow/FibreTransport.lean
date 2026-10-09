import DifferentialGeometry.Topology.Manifold.FiniteOrderFlow.Diffeomorph

/-!
# Fibre transport by a finite-order time-dependent flow (LFR03 kernel, point-fibre case)

Let `F : ℝ × M → F'` be a family of maps (`F (t, ·) = f_t`) and `X ⊆ F'`. If a time-dependent
field `V` lifts time for `F` on an open neighbourhood `O` of the trace `F ⁻¹' X`, i.e.
`dF (1, V) = 0` on `O` (`D_x f_t (V t) = -∂ₜ f_t`), then `F (t, γ t)` is constant along every
solution `γ` that meets the trace, so the flow `Φ s t` of a compactly supported `C^r` such field
carries the fibre `f_s ⁻¹' X` onto `f_t ⁻¹' X`, with the same value of `F`.

This is the isotopy step of blueprint LFR03 (A:24982–25010) in the case where one equation
`D_x F v = -∂ₜ F` holds on a whole neighbourhood of the trace, e.g. fibres over a point
(`X = {c}`), where the partition-of-unity combination of local solutions still solves the same
affine equation. For `X` with boundary the combined field is only tangent to the trace; that
"tangent ⇒ invariant" step belongs to LC82 and is not proved here.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']

/-- The graph `τ ↦ (τ, γ τ)` of a solution of the time-dependent equation has velocity
`(1, V τ (γ τ))`. -/
theorem hasMFDerivAt_graph_of_hasMFDerivAt (V : ℝ → (x : M) → TangentSpace I x) {γ : ℝ → M}
    (hγ : ∀ t, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (V t (γ t)))) (τ : ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) (fun σ : ℝ => ((σ, γ σ) : ℝ × M)) τ
      ((1 : ℝ →L[ℝ] ℝ).smulRight (((1 : ℝ), V τ (γ τ)) : ℝ × E)) := by
  refine ((hasMFDerivAt_id τ).prodMk (hγ τ)).congr_mfderiv ?_
  refine ContinuousLinearMap.ext_ring ?_
  refine Prod.ext ?_ ?_
  · change (1 : ℝ) = ((1 : ℝ) • (((1 : ℝ), V τ (γ τ)) : ℝ × E)).1
    simp
  · rfl

/-- **Transport along one solution.** Let `γ` solve `γ' = V t γ`, let `F` be continuous, and let
`dF (1, V) = 0` at every point of an open set `O` containing the trace `F ⁻¹' X`, where `F` is
differentiable. If `F (s, γ s) ∈ X`, then `F (t, γ t) = F (s, γ s)` for every `t`. -/
theorem apply_graph_eq_of_transport (V : ℝ → (x : M) → TangentSpace I x) {γ : ℝ → M}
    (hγ : ∀ t, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (V t (γ t))))
    {F : ℝ × M → F'} (hFc : Continuous F) {X : Set F'} {O : Set (ℝ × M)} (hO : IsOpen O)
    (hXO : F ⁻¹' X ⊆ O) (hF : ∀ p ∈ O, MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F') F p)
    (htransport : ∀ p ∈ O, mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F') F p ((1 : ℝ), V p.1 p.2) = 0)
    {s : ℝ} (hs : F (s, γ s) ∈ X) (t : ℝ) :
    F (t, γ t) = F (s, γ s) := by
  set c : ℝ → ℝ × M := fun σ => (σ, γ σ) with hc
  set g : ℝ → F' := fun σ => F (c σ) with hg
  have hcd := hasMFDerivAt_graph_of_hasMFDerivAt V hγ
  have hcont : Continuous c := continuous_iff_continuousAt.2 fun σ => (hcd σ).continuousAt
  have hgcont : Continuous g := hFc.comp hcont
  set A : Set ℝ := c ⁻¹' O with hA
  have hAo : IsOpen A := hO.preimage hcont
  have hderiv : ∀ σ ∈ A, HasDerivAt g 0 σ := by
    intro σ hσ
    have h := ((hF (c σ) hσ).hasMFDerivAt).comp σ (hcd σ)
    have h0 : (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F') F (c σ)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (((1 : ℝ), V σ (γ σ)) : ℝ × E)) = 0 := by
      refine ContinuousLinearMap.ext_ring ?_
      change mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F') F (c σ)
        ((1 : ℝ) • (((1 : ℝ), V σ (γ σ)) : ℝ × E)) = 0
      rw [one_smul]
      exact htransport (c σ) hσ
    have h' : HasFDerivAt g (0 : ℝ →L[ℝ] F') σ := (h.congr_mfderiv h0).hasFDerivAt
    simpa using h'.hasDerivAt
  set S : Set ℝ := g ⁻¹' {g s} with hS
  have hSA : S ⊆ A := by
    intro σ hσ
    apply hXO
    change g σ ∈ X
    rw [show g σ = g s from hσ]
    exact hs
  have hSopen : IsOpen S := by
    have h := hAo.isOpen_inter_preimage_of_deriv_eq_zero
      (fun σ hσ => (hderiv σ hσ).differentiableAt.differentiableWithinAt)
      (fun σ hσ => (hderiv σ hσ).deriv) {g s}
    rwa [inter_eq_right.2 hSA] at h
  have hSclosed : IsClosed S := isClosed_singleton.preimage hgcont
  have hSuniv : S = univ :=
    (isClopen_iff.1 ⟨hSclosed, hSopen⟩).resolve_left (Set.nonempty_iff_ne_empty.1 ⟨s, rfl⟩)
  have ht : t ∈ S := hSuniv ▸ mem_univ t
  exact ht

section Flow

variable [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]

/-- **The flow preserves `F` on the trace.** For a compactly supported jointly `C^n` field
(`1 ≤ n`) that lifts time for `F` on an open neighbourhood of `F ⁻¹' X`, the flow keeps the value
of `F` along every orbit starting on the trace: `F (t, Φ s t x) = F (s, x)`. -/
theorem finiteOrderFlow_transport [CompleteSpace E] {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (V : ℝ → (x : M) → TangentSpace I x)
    (hV : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
      (fun q : ℝ × M => (⟨q.2, V q.1 q.2⟩ : TangentBundle I M)))
    {K : Set M} (hK : IsCompact K) (hsupp : ∀ t x, x ∉ K → V t x = 0)
    {F : ℝ × M → F'} (hFc : Continuous F) {X : Set F'} {O : Set (ℝ × M)} (hO : IsOpen O)
    (hXO : F ⁻¹' X ⊆ O) (hF : ∀ p ∈ O, MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F') F p)
    (htransport : ∀ p ∈ O, mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F') F p ((1 : ℝ), V p.1 p.2) = 0)
    {s : ℝ} {x : M} (hx : F (s, x) ∈ X) (t : ℝ) :
    F (t, finiteOrderFlow V s t x) = F (s, x) := by
  have hW := (contMDiff_autonomizedFlowVF_section V hV).of_le hn
  have hself := finiteOrderFlow_self V hW hK hsupp s x
  have h := apply_graph_eq_of_transport V (γ := fun t => finiteOrderFlow V s t x)
    (hasMFDerivAt_finiteOrderFlow V hW hK hsupp s · x) hFc hO hXO hF htransport (s := s)
    (by simpa only [hself] using hx) t
  simpa only [hself] using h

/-- **The flow carries the fibre over `X` at time `s` onto the fibre at time `t`.** -/
theorem image_finiteOrderFlow_fibre [CompleteSpace E] {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (V : ℝ → (x : M) → TangentSpace I x)
    (hV : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
      (fun q : ℝ × M => (⟨q.2, V q.1 q.2⟩ : TangentBundle I M)))
    {K : Set M} (hK : IsCompact K) (hsupp : ∀ t x, x ∉ K → V t x = 0)
    {F : ℝ × M → F'} (hFc : Continuous F) {X : Set F'} {O : Set (ℝ × M)} (hO : IsOpen O)
    (hXO : F ⁻¹' X ⊆ O) (hF : ∀ p ∈ O, MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F') F p)
    (htransport : ∀ p ∈ O, mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F') F p ((1 : ℝ), V p.1 p.2) = 0)
    (s t : ℝ) :
    finiteOrderFlow V s t '' {x | F (s, x) ∈ X} = {x | F (t, x) ∈ X} := by
  have hW := (contMDiff_autonomizedFlowVF_section V hV).of_le hn
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change F (t, finiteOrderFlow V s t x) ∈ X
    rw [finiteOrderFlow_transport hn V hV hK hsupp hFc hO hXO hF htransport hx t]
    exact hx
  · intro hy
    refine ⟨finiteOrderFlow V t s y, ?_, ?_⟩
    · change F (s, finiteOrderFlow V t s y) ∈ X
      rw [finiteOrderFlow_transport hn V hV hK hsupp hFc hO hXO hF htransport hy s]
      exact hy
    · rw [finiteOrderFlow_trans V hW hK hsupp, finiteOrderFlow_self V hW hK hsupp]

end Flow

section Packaged

variable [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] [IsManifold I ∞ M]

/-- **LFR03 kernel (fibres preserved on a neighbourhood of the trace).** A jointly `C^r` field
(`1 ≤ r`) with compact spatial support `K` that lifts time for `F` on an open neighbourhood `O` of
the trace `F ⁻¹' X` generates a compactly supported `C^r` isotopy `Φ s t` (jointly `C^r`,
`Φ s s = id`, the identity off `K`) carrying `{x | F (s, x) ∈ X}` onto `{x | F (t, x) ∈ X}` and
preserving the value of `F` on it. -/
theorem exists_compactSupport_isotopy_fibre_Ck {r : ℕ} (hr : 1 ≤ r)
    (V : ℝ → (x : M) → TangentSpace I x)
    (hV : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent r
      (fun q : ℝ × M => (⟨q.2, V q.1 q.2⟩ : TangentBundle I M)))
    {K : Set M} (hK : IsCompact K) (hsupp : ∀ t x, x ∉ K → V t x = 0)
    {F : ℝ × M → F'} (hFc : Continuous F) {X : Set F'} {O : Set (ℝ × M)} (hO : IsOpen O)
    (hXO : F ⁻¹' X ⊆ O) (hF : ∀ p ∈ O, MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F') F p)
    (htransport : ∀ p ∈ O, mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F') F p ((1 : ℝ), V p.1 p.2) = 0) :
    ∃ Φ : ℝ → ℝ → M ≃ₘ^r⟮I, I⟯ M,
      ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I r
        (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2) ∧
      (∀ s, Φ s s = Diffeomorph.refl I M r) ∧
      (∀ s t x, x ∉ K → Φ s t x = x) ∧
      (∀ s t x, F (s, x) ∈ X → F (t, Φ s t x) = F (s, x)) ∧
      ∀ s t, Φ s t '' {x | F (s, x) ∈ X} = {x | F (t, x) ∈ X} := by
  have hr' : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast hr
  exact ⟨finiteOrderFlowDiffeomorph hr V hV hK hsupp,
    contMDiff_finiteOrderFlowDiffeomorph hr V hV hK hsupp,
    finiteOrderFlowDiffeomorph_self hr V hV hK hsupp,
    fun s t _ hx => finiteOrderFlowDiffeomorph_eq_self_of_not_mem hr V hV hK hsupp s t hx,
    fun s t _ hx => finiteOrderFlow_transport hr' V hV hK hsupp hFc hO hXO hF htransport hx t,
    fun s t => image_finiteOrderFlow_fibre hr' V hV hK hsupp hFc hO hXO hF htransport s t⟩

end Packaged

end DifferentialGeometry.Analysis.ODE
