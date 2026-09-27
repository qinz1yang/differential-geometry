import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.FullNeckHornCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornScalarLevel

set_option autoImplicit false
noncomputable section

open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

universe u

variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

private local instance : SigmaCompactSpace D.slab.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel D.slab.terminalRegularOpen.isOpen)

theorem exists_scale_threshold_neck_family_in_horns
    (hε : ε ≤ 1 / 8646) {δ : ℝ} (hεδ : ε ≤ δ) (hδ1 : δ < 1)
    (hfit : δ⁻¹ + 1 < ε⁻¹) (r : ∀ c, P.hornIndex c → ℝ) :
    ∃ Q₀ : ℝ, 0 < Q₀ ∧ ∀ Q : ℝ, Q₀ < Q → ∀ y : Sphere 2,
      ∃ (t δ₀ : ∀ c, P.hornIndex c → ℝ) (k : ∀ c, P.hornIndex c → ℕ)
        (N : ∀ c e, NormalizedNeck D.terminal.metric (δ₀ c e) (k c e))
        (hδ : ∀ c e, δ₀ c e ≤ δ),
        ∀ c e, 0 < t c e ∧ (N c e).center = P.horn c e (y, t c e) ∧
          (N c e).scale = Q ∧ δ₀ c e ≤ ε ∧ ⌊ε⁻¹⌋₊ + 1 ≤ k c e ∧
          (∀ q : neckBuffer δ,
            Q / 2 ≤ metricScalarAt D.terminal.metric (((N c e).monoDelta (hδ c e) hδ1).chart q)) ∧
          ∃ Θ : neckBuffer δ → positiveHornDomain,
            IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ Θ ∧
            (∀ q : neckBuffer δ,
              P.horn c e (Θ q).val = ((N c e).monoDelta (hδ c e) hδ1).chart q) ∧
            (∀ q : neckBuffer δ, r c e < (Θ q).val.2) ∧
            ∃ K : Set D.slab.terminalRegularOpen, IsCompact K ∧
              range ((N c e).monoDelta (hδ c e) hδ1).chart ⊆ K ∧
              K ⊆ P.horn c e '' (univ ×ˢ Ioi (r c e)) := by
  classical
  have hc (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c) :
      c ∈ P.component := by
    by_contra hn
    exact (P.hornIndex_empty c hn).false e
  choose C _ hC using fun c e =>
    P.exists_scale_threshold_full_neck_in_horn c (hc c e) e (r c e)
  let J := Σ c : P.component, P.hornIndex c.val
  let : Finite P.component := P.component_finite.to_subtype
  let (c : P.component) : Finite (P.hornIndex c.val) := P.hornIndex_finite c.val
  have : Finite J := inferInstance
  obtain ⟨B, hB⟩ := (finite_range (fun j : J => C j.1.val j.2)).bddAbove
  let Q₀ := max (max B (Λ * (P.coreRadius ^ 2)⁻¹)) 0 + 1
  refine ⟨Q₀, by dsimp only [Q₀]; positivity, ?_⟩
  intro Q hQ y
  have hQbase : Λ * (P.coreRadius ^ 2)⁻¹ < Q := by
    have h₁ := le_max_right B (Λ * (P.coreRadius ^ 2)⁻¹)
    have h₂ := le_max_left (max B (Λ * (P.coreRadius ^ 2)⁻¹)) 0
    dsimp only [Q₀] at hQ
    linarith
  obtain ⟨t, δ₀, k, N, hN⟩ := P.exists_neck_family_scale_eq_and_scalar_lower y hQbase hε
  let hδ : ∀ c e, δ₀ c e ≤ δ := fun c e => (hN c e).2.2.2.1.trans hεδ
  refine ⟨t, δ₀, k, N, hδ, ?_⟩
  intro c e
  obtain ⟨ht, hcenter, hscale, hδε, hk, hscalar⟩ := hN c e
  have hε1 : 1 ≤ ε⁻¹ := ((one_lt_inv₀ P.epsilon_pos).mpr (by linarith : ε < 1)).le
  have hfloor : 1 ≤ ⌊ε⁻¹⌋₊ := Nat.le_floor (by exact_mod_cast hε1)
  have hk2 : 2 ≤ k c e := by omega
  have hfit₀ : δ⁻¹ + 1 < (δ₀ c e)⁻¹ :=
    hfit.trans_le (inv_anti₀ (N c e).delta_pos hδε)
  have hCQ : C c e < (N c e).scale := by
    have hCB := hB (mem_range_self (⟨⟨c, hc c e⟩, e⟩ : J))
    have h₁ := le_max_left B (Λ * (P.coreRadius ^ 2)⁻¹)
    have h₂ := le_max_left (max B (Λ * (P.coreRadius ^ 2)⁻¹)) 0
    rw [hscale]
    dsimp only [Q₀] at hQ
    change C c e ≤ B at hCB
    linarith
  have hcenter' : (N c e).center ∈ hornHalfRange P c e := by
    rw [hcenter]
    exact ⟨⟨(y, t c e), ht.le⟩, rfl⟩
  refine ⟨ht, hcenter, hscale, hδε, hk, ?_,
    hC c e (N c e) hk2 (hδε.trans hε) hcenter' hCQ (hδ c e) hδ1 hfit₀⟩
  intro q
  apply hscalar (Opens.inclusion (neckBuffer_le_of_le (N c e).delta_pos (hδ c e)) q)
  exact ⟨by change -(δ₀ c e)⁻¹ ≤ q.val.2; linarith [q.property.1],
    by change q.val.2 ≤ (δ₀ c e)⁻¹; linarith [q.property.2]⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation
