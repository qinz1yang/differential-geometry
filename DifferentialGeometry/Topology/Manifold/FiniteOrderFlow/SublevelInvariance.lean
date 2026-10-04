import DifferentialGeometry.Topology.Manifold.FiniteOrderFlow.FibreTransport

/-!
# Invariance of a regular sublevel of a regular level under a time-lifting flow

Let `Ψ : ℝ × M → G` and `B : ℝ × M → ℝ` be a time-dependent defining pair of the family of
"manifolds with boundary" `W_t = {Ψ (t, ·) = 0, B (t, ·) ≥ 0}` with side boundaries
`∂W_t = {Ψ (t, ·) = 0, B (t, ·) = 0}`. If a time-dependent field `V` satisfies
`dΨ (1, V) = 0` on an open neighbourhood `O` of the trace `W = {Ψ = 0, B ≥ 0}` and
`dB (1, V) = 0` on an open neighbourhood `O'` of the boundary trace `∂W = {Ψ = 0, B = 0}`, then
along every solution `γ` of `γ' = V t γ` both traces are invariant, forwards and backwards in time
(kernel B of `build-logs/resume/sheet-W5-FLOW.md`, statement S3).

This is the "tangency preserves both strata" step of blueprint LFR03 (A:24996–25004) and LC82
(A:25133–25156) for `X = {φ = 0, β ≥ 0}` given by a global defining pair: every local solution of
the time-lifting equations solves the same affine equations, so a partition-of-unity combination
solves them on a neighbourhood of the trace and neither ODE uniqueness nor Grönwall is needed. The
proof is a clopen argument in `ℝ`: `Ψ ∘ γ` and `B ∘ γ` are locally constant wherever the graph of
`γ` lies in `O` resp. `O'`, and `B > 0` is an open condition.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold Topology

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']

/-- **Local constancy along the graph.** If `dF (1, V) = 0` on an open set `O` where `F` is
differentiable, then along a solution `γ` of `γ' = V t γ` the function `σ ↦ F (σ, γ σ)` is locally
constant on the open set of times whose graph point lies in `O`: for every `T`, the set of such
times with `F (σ, γ σ) ∈ T` is open. -/
theorem isOpen_graph_preimage_inter_of_transport (V : ℝ → (x : M) → TangentSpace I x)
    {γ : ℝ → M}
    (hγ : ∀ t, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (V t (γ t))))
    {F : ℝ × M → F'} {O : Set (ℝ × M)} (hO : IsOpen O)
    (hF : ∀ p ∈ O, MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F') F p)
    (htransport : ∀ p ∈ O, mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F') F p ((1 : ℝ), V p.1 p.2) = 0)
    (T : Set F') :
    IsOpen ({σ : ℝ | ((σ, γ σ) : ℝ × M) ∈ O} ∩ (fun σ : ℝ => F (σ, γ σ)) ⁻¹' T) := by
  set c : ℝ → ℝ × M := fun σ => (σ, γ σ) with hc
  set g : ℝ → F' := fun σ => F (c σ) with hg
  have hcd := hasMFDerivAt_graph_of_hasMFDerivAt V hγ
  have hcont : Continuous c := continuous_iff_continuousAt.2 fun σ => (hcd σ).continuousAt
  have hAo : IsOpen (c ⁻¹' O) := hO.preimage hcont
  have hderiv : ∀ σ ∈ c ⁻¹' O, HasDerivAt g 0 σ := by
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
  exact hAo.isOpen_inter_preimage_of_deriv_eq_zero
    (fun σ hσ => (hderiv σ hσ).differentiableAt.differentiableWithinAt)
    (fun σ hσ => (hderiv σ hσ).deriv) T

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Kernel B (statement S3 of W5-FLOW): invariance of a regular sublevel and of its side
boundary.** Let `γ` solve `γ' = V t γ`. Let `Ψ : ℝ × M → G` and `B : ℝ × M → ℝ` be continuous,
with `Ψ` differentiable and `dΨ (1, V) = 0` on an open set `O ⊇ {Ψ = 0, B ≥ 0}`, and `B`
differentiable and `dB (1, V) = 0` on an open set `O' ⊇ {Ψ = 0, B = 0}`. If the graph point at
time `s` lies in `{Ψ = 0, B ≥ 0}` (resp. `{Ψ = 0, B = 0}`), then so does the graph point at every
time `t`. -/
theorem mem_trace_of_transport (V : ℝ → (x : M) → TangentSpace I x) {γ : ℝ → M}
    (hγ : ∀ t, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (V t (γ t))))
    {Ψ : ℝ × M → G} (hΨc : Continuous Ψ) {B : ℝ × M → ℝ} (hBc : Continuous B)
    {O O' : Set (ℝ × M)} (hO : IsOpen O) (hO' : IsOpen O')
    (hWO : {q | Ψ q = 0 ∧ 0 ≤ B q} ⊆ O) (hbO' : {q | Ψ q = 0 ∧ B q = 0} ⊆ O')
    (hΨd : ∀ q ∈ O, MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G) Ψ q)
    (hBd : ∀ q ∈ O', MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) B q)
    (hΨt : ∀ q ∈ O, mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G) Ψ q ((1 : ℝ), V q.1 q.2) = 0)
    (hBt : ∀ q ∈ O', mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) B q ((1 : ℝ), V q.1 q.2) = 0)
    {s : ℝ} (t : ℝ) :
    ((Ψ (s, γ s) = 0 ∧ 0 ≤ B (s, γ s)) → (Ψ (t, γ t) = 0 ∧ 0 ≤ B (t, γ t))) ∧
    ((Ψ (s, γ s) = 0 ∧ B (s, γ s) = 0) → (Ψ (t, γ t) = 0 ∧ B (t, γ t) = 0)) := by
  have hcd := hasMFDerivAt_graph_of_hasMFDerivAt V hγ
  have hcont : Continuous (fun σ : ℝ => ((σ, γ σ) : ℝ × M)) :=
    continuous_iff_continuousAt.2 fun σ => (hcd σ).continuousAt
  have hg : Continuous (fun σ : ℝ => Ψ (σ, γ σ)) := hΨc.comp hcont
  have hh : Continuous (fun σ : ℝ => B (σ, γ σ)) := hBc.comp hcont
  have hU1 := isOpen_graph_preimage_inter_of_transport V hγ hO hΨd hΨt {0}
  have hU3 := isOpen_graph_preimage_inter_of_transport V hγ hO' hBd hBt {0}
  have hU2 : IsOpen ((fun σ : ℝ => B (σ, γ σ)) ⁻¹' Ioi 0) := isOpen_Ioi.preimage hh
  -- the clopen argument, for a nonempty set that is open and closed in `ℝ`
  have key : ∀ S : Set ℝ, IsOpen S → IsClosed S → s ∈ S → t ∈ S := by
    intro S hSo hSc hs
    have hSuniv : S = univ :=
      (isClopen_iff.1 ⟨hSc, hSo⟩).resolve_left (Set.nonempty_iff_ne_empty.1 ⟨s, hs⟩)
    exact hSuniv ▸ mem_univ t
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · set S : Set ℝ := {σ | Ψ (σ, γ σ) = 0 ∧ 0 ≤ B (σ, γ σ)} with hSdef
    have hSc : IsClosed S :=
      (isClosed_singleton.preimage hg).inter (isClosed_Ici.preimage hh)
    have hSeq : S = ({σ : ℝ | ((σ, γ σ) : ℝ × M) ∈ O} ∩ (fun σ : ℝ => Ψ (σ, γ σ)) ⁻¹' {0}) ∩
        ((fun σ : ℝ => B (σ, γ σ)) ⁻¹' Ioi 0 ∪
          ({σ : ℝ | ((σ, γ σ) : ℝ × M) ∈ O'} ∩ (fun σ : ℝ => B (σ, γ σ)) ⁻¹' {0})) := by
      ext σ
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨⟨hWO ⟨h1, h2⟩, h1⟩, ?_⟩
        rcases h2.lt_or_eq with h2 | h2
        · exact Or.inl h2
        · exact Or.inr ⟨hbO' ⟨h1, h2.symm⟩, h2.symm⟩
      · rintro ⟨⟨-, h1⟩, h2 | ⟨-, h2⟩⟩
        · exact ⟨h1, le_of_lt h2⟩
        · exact ⟨h1, ge_of_eq h2⟩
    have hSo : IsOpen S := hSeq ▸ hU1.inter (hU2.union hU3)
    exact key S hSo hSc hs
  · set S : Set ℝ := {σ | Ψ (σ, γ σ) = 0 ∧ B (σ, γ σ) = 0} with hSdef
    have hSc : IsClosed S :=
      (isClosed_singleton.preimage hg).inter (isClosed_singleton.preimage hh)
    have hSeq : S = ({σ : ℝ | ((σ, γ σ) : ℝ × M) ∈ O} ∩ (fun σ : ℝ => Ψ (σ, γ σ)) ⁻¹' {0}) ∩
        ({σ : ℝ | ((σ, γ σ) : ℝ × M) ∈ O'} ∩ (fun σ : ℝ => B (σ, γ σ)) ⁻¹' {0}) := by
      ext σ
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨hWO ⟨h1, h2.ge⟩, h1⟩, ⟨hbO' ⟨h1, h2⟩, h2⟩⟩
      · rintro ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
        exact ⟨h1, h2⟩
    have hSo : IsOpen S := hSeq ▸ hU1.inter hU3
    exact key S hSo hSc hs

section Flow

variable [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M] [CompleteSpace E]

/-- **The flow of a time-lifting field carries the sublevel `W_s = {Ψ (s, ·) = 0, B (s, ·) ≥ 0}`
onto `W_t`**, for a compactly supported jointly `C^n` field (`1 ≤ n`) with `dΨ (1, V) = 0` near
`{Ψ = 0, B ≥ 0}` and `dB (1, V) = 0` near `{Ψ = 0, B = 0}`. -/
theorem image_finiteOrderFlow_sublevel {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (V : ℝ → (x : M) → TangentSpace I x)
    (hV : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
      (fun q : ℝ × M => (⟨q.2, V q.1 q.2⟩ : TangentBundle I M)))
    {K : Set M} (hK : IsCompact K) (hsupp : ∀ t x, x ∉ K → V t x = 0)
    {Ψ : ℝ × M → G} (hΨc : Continuous Ψ) {B : ℝ × M → ℝ} (hBc : Continuous B)
    {O O' : Set (ℝ × M)} (hO : IsOpen O) (hO' : IsOpen O')
    (hWO : {q | Ψ q = 0 ∧ 0 ≤ B q} ⊆ O) (hbO' : {q | Ψ q = 0 ∧ B q = 0} ⊆ O')
    (hΨd : ∀ q ∈ O, MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G) Ψ q)
    (hBd : ∀ q ∈ O', MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) B q)
    (hΨt : ∀ q ∈ O, mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G) Ψ q ((1 : ℝ), V q.1 q.2) = 0)
    (hBt : ∀ q ∈ O', mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) B q ((1 : ℝ), V q.1 q.2) = 0)
    (s t : ℝ) :
    finiteOrderFlow V s t '' {x | Ψ (s, x) = 0 ∧ 0 ≤ B (s, x)} =
        {x | Ψ (t, x) = 0 ∧ 0 ≤ B (t, x)} ∧
      finiteOrderFlow V s t '' {x | Ψ (s, x) = 0 ∧ B (s, x) = 0} =
        {x | Ψ (t, x) = 0 ∧ B (t, x) = 0} := by
  have hW := (contMDiff_autonomizedFlowVF_section V hV).of_le hn
  have hmem : ∀ (a b : ℝ) (x : M),
      ((Ψ (a, x) = 0 ∧ 0 ≤ B (a, x)) →
        (Ψ (b, finiteOrderFlow V a b x) = 0 ∧ 0 ≤ B (b, finiteOrderFlow V a b x))) ∧
      ((Ψ (a, x) = 0 ∧ B (a, x) = 0) →
        (Ψ (b, finiteOrderFlow V a b x) = 0 ∧ B (b, finiteOrderFlow V a b x) = 0)) := by
    intro a b x
    have hself := finiteOrderFlow_self V hW hK hsupp a x
    have h := mem_trace_of_transport V (γ := fun τ => finiteOrderFlow V a τ x)
      (hasMFDerivAt_finiteOrderFlow V hW hK hsupp a · x) hΨc hBc hO hO' hWO hbO' hΨd hBd
      hΨt hBt (s := a) b
    simp only [hself] at h
    exact h
  have hback : ∀ y : M, finiteOrderFlow V s t (finiteOrderFlow V t s y) = y := fun y => by
    rw [finiteOrderFlow_trans V hW hK hsupp, finiteOrderFlow_self V hW hK hsupp]
  refine ⟨?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hmem s t x).1 hx
    · intro hy
      exact ⟨finiteOrderFlow V t s y, (hmem t s y).1 hy, hback y⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hmem s t x).2 hx
    · intro hy
      exact ⟨finiteOrderFlow V t s y, (hmem t s y).2 hy, hback y⟩

end Flow

end DifferentialGeometry.Analysis.ODE
