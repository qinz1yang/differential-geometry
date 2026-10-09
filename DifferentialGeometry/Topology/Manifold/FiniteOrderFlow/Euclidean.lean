import DifferentialGeometry.Topology.Manifold.FiniteOrderFlow.FibreTransport

/-!
# Finite-order time-dependent flows on a finite-dimensional vector space

The Euclidean bindings of `exists_compactSupport_flow_Ck` and
`exists_compactSupport_isotopy_fibre_Ck`: for `V : ℝ → E → E` jointly `C^r` in the ordinary sense
(`ContDiff`) with compact spatial support, the flow is jointly `C^r` in the ordinary sense, solves
`∂ₜ Φ s t x = V t (Φ s t x)` (`HasDerivAt`), and transports fibres of a family `F` whose ordinary
derivative satisfies `DF (1, V) = 0` near the trace. The tree's `Diffeomorph.timeDependentFlow`
(`Topology/Diffeomorph/TimeDependentFlow.lean`) is the `C^∞` Euclidean case.
-/

set_option autoImplicit false

noncomputable section

open Set Function Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A time-dependent field on a vector space that is jointly `C^n` in the ordinary sense is jointly
`C^n` as a map `ℝ × E → TE`. -/
theorem contMDiff_timeDependentField_of_contDiff {n : WithTop ℕ∞} {V : ℝ → E → E}
    (hV : ContDiff ℝ n (fun q : ℝ × E => V q.1 q.2)) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E).tangent n
      (fun q : ℝ × E => (⟨q.2, V q.1 q.2⟩ : TangentBundle 𝓘(ℝ, E) E)) := by
  have hV' : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) n (fun q : ℝ × E => V q.1 q.2) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact hV.contMDiff
  intro q₀
  apply Bundle.contMDiffAt_totalSpace.2
  refine ⟨contMDiff_snd.contMDiffAt, ?_⟩
  convert! (hV' q₀) with q
  simp

/-- A map `(ℝ × ℝ) × E → E` that is `C^n` for the product model is `C^n` in the ordinary sense. -/
theorem contDiff_of_contMDiff_prod_prod {n : WithTop ℕ∞} {Φ : (ℝ × ℝ) × E → E}
    (h : ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) n Φ) : ContDiff ℝ n Φ := by
  have hid : ContMDiff 𝓘(ℝ, (ℝ × ℝ) × E) ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) n
      (fun q : (ℝ × ℝ) × E => ((q.1.1, q.1.2), q.2)) :=
    ((contDiff_fst.fst.contMDiff).prodMk (contDiff_fst.snd.contMDiff)).prodMk
      contDiff_snd.contMDiff
  exact (h.comp hid).contDiff

section Bindings

variable [FiniteDimensional ℝ E]

/-- **Euclidean finite-order flow.** `V : ℝ → E → E` jointly `C^r` (`1 ≤ r`), vanishing off a
compact `K` at all times, has a global flow, jointly `C^r`, with `Φ s s = id`, the cocycle law,
`∂ₜ Φ s t x = V t (Φ s t x)`, and `Φ s t = id` off `K`. -/
theorem exists_compactSupport_flow_Ck_euclidean {r : ℕ} (hr : 1 ≤ r) {V : ℝ → E → E}
    (hV : ContDiff ℝ r (fun q : ℝ × E => V q.1 q.2)) {K : Set E} (hK : IsCompact K)
    (hsupp : ∀ t x, x ∉ K → V t x = 0) :
    ∃ Φ : ℝ → ℝ → E → E,
      ContDiff ℝ r (fun q : (ℝ × ℝ) × E => Φ q.1.1 q.1.2 q.2) ∧
      (∀ s x, Φ s s x = x) ∧
      (∀ s t u x, Φ t u (Φ s t x) = Φ s u x) ∧
      (∀ s t x, HasDerivAt (Φ s · x) (V t (Φ s t x)) t) ∧
      ∀ s t x, x ∉ K → Φ s t x = x := by
  obtain ⟨Φ, hΦ, hself, htrans, hderiv, hid, -⟩ :=
    exists_compactSupport_flow_Ck (I := 𝓘(ℝ, E)) hr V
      (contMDiff_timeDependentField_of_contDiff hV) hK hsupp
  exact ⟨Φ, contDiff_of_contMDiff_prod_prod hΦ, hself, htrans,
    fun s t x => hasDerivAt_iff_hasFDerivAt.2 (hderiv s t x).hasFDerivAt, hid⟩

/-- **Euclidean LFR03 kernel.** A jointly `C^r` field with compact spatial support whose ordinary
derivative satisfies `DF (1, V) = 0` on an open neighbourhood of the trace `F ⁻¹' X` generates a
compactly supported `C^r` isotopy carrying `{x | F (s, x) ∈ X}` onto `{x | F (t, x) ∈ X}`. -/
theorem exists_compactSupport_isotopy_fibre_Ck_euclidean {r : ℕ} (hr : 1 ≤ r)
    {V : ℝ → E → E} (hV : ContDiff ℝ r (fun q : ℝ × E => V q.1 q.2)) {K : Set E}
    (hK : IsCompact K) (hsupp : ∀ t x, x ∉ K → V t x = 0)
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {F : ℝ × E → F'} (hFc : Continuous F) {X : Set F'} {O : Set (ℝ × E)} (hO : IsOpen O)
    (hXO : F ⁻¹' X ⊆ O) (hF : ∀ p ∈ O, DifferentiableAt ℝ F p)
    (htransport : ∀ p ∈ O, fderiv ℝ F p ((1 : ℝ), V p.1 p.2) = 0) :
    ∃ Φ : ℝ → ℝ → E ≃ₘ^r⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E,
      ContDiff ℝ r (fun q : (ℝ × ℝ) × E => Φ q.1.1 q.1.2 q.2) ∧
      (∀ s, Φ s s = Diffeomorph.refl 𝓘(ℝ, E) E r) ∧
      (∀ s t x, x ∉ K → Φ s t x = x) ∧
      (∀ s t x, F (s, x) ∈ X → F (t, Φ s t x) = F (s, x)) ∧
      ∀ s t, Φ s t '' {x | F (s, x) ∈ X} = {x | F (t, x) ∈ X} := by
  have hFm : ∀ p ∈ O, MDifferentiableAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, F') F p := by
    intro p hp
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact (hF p hp).mdifferentiableAt
  have hmf : ∀ p : ℝ × E, mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, F') F p = fderiv ℝ F p := by
    intro p
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact mfderiv_eq_fderiv
  obtain ⟨Φ, hΦ, hself, hid, hval, himage⟩ :=
    exists_compactSupport_isotopy_fibre_Ck (I := 𝓘(ℝ, E)) hr V
      (contMDiff_timeDependentField_of_contDiff hV) hK hsupp hFc hO hXO hFm
      (fun p hp => by rw [hmf p]; exact htransport p hp)
  exact ⟨Φ, contDiff_of_contMDiff_prod_prod hΦ, hself, hid, hval, himage⟩

end Bindings

end DifferentialGeometry.Analysis.ODE
