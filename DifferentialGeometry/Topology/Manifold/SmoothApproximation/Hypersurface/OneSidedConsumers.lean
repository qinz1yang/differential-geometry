import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Hypersurface.OneSided

/-!
# Consumers of the one-sided hypersurface smoothing (W-SUB, O)

* `exists_smooth_carrier_one_sided`: the form LFR47 consumes in the one-sided case — a compact
  smooth manifold `Ŝ` (an embedded slice of `M` inside the tube) with a `C^n` diffeomorphism onto
  the `C^n` base `S`, together with the antisymmetric graph function over the double cover.
* `lifted_tube_smooth_data`: the lifted smooth structure on `Sc × (-ε, ε)` (O1) — a smooth
  manifold on which the normal exponential map is smooth, the deck involution is smooth and the
  identity tube is a `C^n` partial diffeomorphism.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold TopologicalSpace
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Manifold.SmoothHypersurface

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {ES : Type*} [NormedAddCommGroup ES] [NormedSpace ℝ ES] [CompleteSpace ES]
  {HS : Type*} [TopologicalSpace HS] {IS : ModelWithCorners ℝ ES HS} [IS.Boundaryless]
  {Sc : Type*} [TopologicalSpace Sc] [ChartedSpace HS Sc] [CompactSpace Sc] [T2Space Sc]
  {ES' : Type*} [NormedAddCommGroup ES'] [NormedSpace ℝ ES']
  {HS' : Type*} [TopologicalSpace HS'] {IS' : ModelWithCorners ℝ ES' HS'}
  {S : Type*} [TopologicalSpace S] [ChartedSpace HS' S]

/-- **The compatible smooth carrier of LFR47 (one-sided case).** -/
theorem exists_smooth_carrier_one_sided {d : ℕ} (hdim : Module.finrank ℝ E = d + 1) {n : ℕ}
    (hn : 1 ≤ n) {Φ : Sc × ℝ → M} {σ : Sc → Sc} {π : Sc → S} {ε : ℝ} (hε : 0 < ε)
    (hloc : IsLocalDiffeomorphOn (IS.prod 𝓘(ℝ, ℝ)) I n Φ (univ ×ˢ Ioo (-ε) ε))
    (hσ : Continuous σ) (hσσ : ∀ v, σ (σ v) = v) (hequiv : ∀ v t, Φ (σ v, -t) = Φ (v, t))
    (hinj : ∀ p ∈ univ ×ˢ Ioo (-ε) ε, ∀ q ∈ univ ×ˢ Ioo (-ε) ε, Φ p = Φ q →
      q = p ∨ q = (σ p.1, -p.2))
    (hπ : IsLocalDiffeomorph IS IS' n π) (hπs : Surjective π)
    (hπσ : ∀ v w, π v = π w ↔ w = v ∨ w = σ v) :
    ∃ Ŝ : Set M, ∃ hŜ : IsEmbeddedSlice I d Ŝ, Ŝ ⊆ Φ '' (univ ×ˢ Ioo (-ε) ε) ∧
      let _ := embeddedSliceChartedSpace hŜ
      IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ Ŝ ∧ CompactSpace Ŝ ∧
        Nonempty (Diffeomorph 𝓘(ℝ, Fin d → ℝ) IS' Ŝ S n) ∧
        ∃ h : Sc → ℝ, ContMDiff IS 𝓘(ℝ, ℝ) n h ∧ (∀ v, h (σ v) = -h v) ∧
          ∀ x, x ∈ Ŝ ↔ ∃ v, Φ (v, h v) = x := by
  obtain ⟨Ŝ, hŜ, hc, hsub, hrest⟩ := exists_smooth_hypersurface_one_sided hdim hn hε le_rfl hloc
    hσ hσσ hequiv hinj hπ hπs hπσ
  refine ⟨Ŝ, hŜ, hsub, ?_⟩
  intro _
  obtain ⟨β, h, hh, hanti, -, hβs, -⟩ := hrest
  refine ⟨embeddedSlice_isManifold hŜ, isCompact_iff_compactSpace.mp hc, ⟨β⟩, h, hh, hanti,
    fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨v, hv⟩ := hπs (β ⟨x, hx⟩)
    refine ⟨v, ?_⟩
    rw [← hβs v, hv, β.symm_apply_apply]
  · rintro ⟨v, rfl⟩
    rw [← hβs v]
    exact (β.symm (π v)).2

omit [FiniteDimensional ℝ E] [I.Boundaryless] [CompleteSpace ES] [IS.Boundaryless]
  [CompactSpace Sc] [T2Space Sc] in
/-- **The lifted smooth structure on the tube cover (O1).** For a `C^n` local diffeomorphism
`Φ : Sc × (-ε, ε) → M` commuting with the involution `(v, t) ↦ (σ v, -t)`, the open set
`W = Sc × (-ε, ε)` carries a smooth manifold structure (model of `M`) in which `Φ` is smooth, the
involution is smooth, and the identity tube is a `C^n` partial diffeomorphism. -/
theorem lifted_tube_smooth_data {n : ℕ} {Φ : Sc × ℝ → M} {σ : Sc → Sc} {ε : ℝ}
    (hloc : IsLocalDiffeomorphOn (IS.prod 𝓘(ℝ, ℝ)) I n Φ (univ ×ˢ Ioo (-ε) ε))
    (hσ : Continuous σ) (hequiv : ∀ v t, Φ (σ v, -t) = Φ (v, t)) :
    let W : Opens (Sc × ℝ) := ⟨univ ×ˢ Ioo (-ε) ε, isOpen_univ.prod isOpen_Ioo⟩
    ∃ _ : ChartedSpace H W, IsManifold I ∞ W ∧ ContMDiff I I ∞ (fun w : W => Φ w) ∧
      ∃ τ : W → W, ContMDiff I I ∞ τ ∧ (∀ w, (τ w : Sc × ℝ) = (σ (w : Sc × ℝ).1, -(w : Sc × ℝ).2)) ∧
        (Nonempty W → ∃ Ψ : PartialDiffeomorph (IS.prod 𝓘(ℝ, ℝ)) I (Sc × ℝ) W n,
          Ψ.source = univ ×ˢ Ioo (-ε) ε ∧ ∀ p ∈ Ψ.source, (Ψ p : Sc × ℝ) = p) := by
  intro W
  have hF : IsLocalDiffeomorphOn (IS.prod 𝓘(ℝ, ℝ)) I n Φ W := hloc
  let _ : ChartedSpace H W := liftedChartedSpace hF
  have hWmem : ∀ w : W, ((σ (w : Sc × ℝ).1, -(w : Sc × ℝ).2) : Sc × ℝ) ∈ W := fun w =>
    ⟨mem_univ _, by linarith [w.2.2.2], by linarith [w.2.2.1]⟩
  let τ : W → W := fun w => ⟨(σ w.1.1, -w.1.2), hWmem w⟩
  have hτc : Continuous τ :=
    ((hσ.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val).neg).subtype_mk _
  refine ⟨liftedChartedSpace hF, lifted_isManifold hF, contMDiff_lifted_proj hF, τ,
    contMDiff_lifted_deck hF hτc (fun w => hequiv _ _), fun w => rfl, fun ⟨p₀⟩ =>
    ⟨liftedTube hF p₀, liftedTube_source hF p₀, fun p hp => liftedTube_apply hF p₀ hp⟩⟩

end DifferentialGeometry.Topology.Manifold.SmoothHypersurface
