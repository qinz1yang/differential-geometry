import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05WithCarrier

/-!
# The selected sublevels are compact (consumer of the carrier export)

* `isCompact_of_core_cases`: if an ambient partial diffeomorphism carries a set `A` onto a core
  `{u ≤ T}` of a model `Ns` whose core coordinate `u` has one of the four types of the carrier
  export (zero on a compact model, or the fibre radius of a soul bundle over `Fin 0 → ℝ`,
  `AddCircle 1` or a compact `𝓡 2`-surface), then `A` is compact (the core is the whole compact
  model, resp. a disc core `D_T` of a bundle over a compact base, `isCompact_discCore`).
* `lpa05_selected_sublevels_compact_withCarrier`: in LPA05's selection
  (`lpa05_selected_zero_packets_with_witnesses_withCarrier`), every actual sublevel
  `{η_c ≤ ρ}`, `ρ ∈ [1/5, 2]`, of the radial function of every selected zero-model ball is compact
  (item (2) of review 43's checklist, compactness).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric Function
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.VectorBundle

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- **Sets carried onto a core of the carrier export are compact.** -/
theorem isCompact_of_core_cases {Y : Type*} [TopologicalSpace Y] [ChartedSpace E3 Y]
    {Ns : Type} [TopologicalSpace Ns] [ChartedSpace E3 Ns] (u : Ns → ℝ)
    (hcases : ((CompactSpace Ns ∧ ∀ y, u y = 0) ∨
       (∃ (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
          (_ : FiniteDimensional ℝ F) (V : (Fin 0 → ℝ) → Type)
          (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
          (_ : TopologicalSpace (TotalSpace F V)) (_ : FiberBundle F V)
          (_ : VectorBundle ℝ F V) (_ : ContMDiffVectorBundle ∞ F V 𝓘(ℝ, Fin 0 → ℝ))
          (_ : IsContMDiffRiemannianBundle 𝓘(ℝ, Fin 0 → ℝ) ∞ F V)
          (D : Diffeomorph (𝓘(ℝ, Fin 0 → ℝ).prod 𝓘(ℝ, F)) I3 (TotalSpace F V) Ns ∞),
          Module.finrank ℝ F = 3 ∧ ∀ x, u x = ‖(D.symm x).2‖) ∨
       (∃ (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
          (_ : FiniteDimensional ℝ F) (V : AddCircle (1 : ℝ) → Type)
          (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
          (_ : TopologicalSpace (TotalSpace F V)) (_ : FiberBundle F V)
          (_ : VectorBundle ℝ F V) (_ : ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ))
          (_ : IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V)
          (D : Diffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) I3 (TotalSpace F V) Ns ∞),
          Module.finrank ℝ F = 2 ∧ ∀ x, u x = ‖(D.symm x).2‖) ∨
       ∃ (B : Type) (_ : TopologicalSpace B) (_ : ChartedSpace E2 B)
          (_ : IsManifold (𝓡 2) ∞ B) (_ : CompactSpace B) (_ : T2Space B)
          (_ : ConnectedSpace B)
          (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
          (_ : FiniteDimensional ℝ F) (V : B → Type)
          (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
          (_ : TopologicalSpace (TotalSpace F V)) (_ : FiberBundle F V)
          (_ : VectorBundle ℝ F V) (_ : ContMDiffVectorBundle ∞ F V (𝓡 2))
          (_ : IsContMDiffRiemannianBundle (𝓡 2) ∞ F V)
          (D : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, F)) I3 (TotalSpace F V) Ns ∞),
          Module.finrank ℝ F = 1 ∧ (∀ x, u x = ‖(D.symm x).2‖) ∧
          ∃ nB : ℕ∞ω, 2 ≤ nB ∧
            ∃ kB : ContMDiffRiemannianMetric (𝓡 2) nB E2 (TangentSpace (𝓡 2) : B → Type _),
              ∀ (x : B) (u₁ u₂ : TangentSpace (𝓡 2) x), 0 ≤ kB.sectionalCurvature x u₁ u₂))
    {A : Set Y} {T : ℝ} (Ψ : PartialDiffeomorph I3 I3 Y Ns ∞) (hA : A ⊆ Ψ.source)
    (hΨA : Ψ '' A = {y | u y ≤ T}) : IsCompact A := by
  have hcore : IsCompact {y | u y ≤ T} := by
    rcases hcases with ⟨hc, hu⟩ | ⟨F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, -, hu⟩ |
        ⟨F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, -, hu⟩ |
        ⟨B, k1, k2, k3, k4, k5, k6, F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, -, hu, -⟩
    · exact (isClosed_le (continuous_const.congr fun y => (hu y).symm) continuous_const).isCompact
    · have h : {y | u y ≤ T} = {y | ‖(D.symm y).2‖ ≤ T} := by simp only [hu]
      rw [h]
      exact isCompact_discCore D T
    · have h : {y | u y ≤ T} = {y | ‖(D.symm y).2‖ ≤ T} := by simp only [hu]
      rw [h]
      exact isCompact_discCore D T
    · have h : {y | u y ≤ T} = {y | ‖(D.symm y).2‖ ≤ T} := by simp only [hu]
      rw [h]
      exact isCompact_discCore D T
  have htgt : {y | u y ≤ T} ⊆ Ψ.target := by
    rw [← hΨA]
    exact (Ψ.toPartialEquiv.image_source_eq_target ▸ image_mono hA)
  have hsymm : Ψ.symm '' {y | u y ≤ T} = A := by
    rw [← hΨA, ← image_comp]
    exact (image_congr fun y hy => Ψ.toPartialEquiv.left_inv (hA hy)).trans (image_id _)
  rw [← hsymm]
  exact hcore.image_of_continuousOn (Ψ.symm.contMDiffOn.continuousOn.mono htgt)

/-- **The selected sublevels are compact.** In LPA05's selection with the carrier, every actual
sublevel `{η_c ≤ ρ}`, `ρ ∈ [1/5, 2]`, of the radial function of every selected zero-model ball is
compact. -/
theorem lpa05_selected_sublevels_compact_withCarrier
    {β : ℕ → ℝ} (hβ : 0 < β 1) (hβone : β 1 < 1) {ζ : ℝ} (hβζ : β 1 < ζ) (hζone : ζ < 1) :
    ∃ ε δ' Λ' : ℝ, 0 < ε ∧ ε < 1 / 4 ∧ 0 < δ' ∧ 0 < Λ' ∧
    ∀ T : ℝ, 0 < T → 20 * Λ' ≤ T → ∀ e : ℝ, 0 < e → e < 1 / 40 →
    ∀ (X : ℕ → Type) [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
      [∀ i, IsManifold I3 ∞ (X i)] [∀ i, CompactSpace (X i)]
      (g : ∀ i, SmoothRiemannianMetric I3 (X i))
      (_ : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
      (α : ℕ → ℝ), Tendsto α atTop atTop →
      (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
        curvatureRadius (g i) p) →
    ∀ (K : ℕ), 10 ≤ K → ∀ (A : ℝ → ℝ → ℝ),
      (∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) →
      (∀ i (p : X i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
        ∀ C, 0 < C → C < α i → ∀ k ≤ K,
        ∀ y ∈ riemannianBallOf (g i) p (C * firstVolumeScale (g i) p v),
          curvatureDerivativeNorm (g i) k y ≤
            A C v * (firstVolumeScale (g i) p v ^ (k + 2))⁻¹) →
    ∀ (Λ w : ℝ), 0 < Λ → 0 < w → w < 4 * Real.pi / 3 →
    ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ i in atTop,
      ∀ (ρ : X i → ℝ) (hρ : ∀ p, 0 < ρ p), Continuous ρ →
        (∀ p, ρ p ≤ 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) →
      ∃ (N C : X i → Type) (_ : ∀ b, MetricSpace (N b)) (_ : ∀ b, ChartedSpace E3 (N b))
        (_ : ∀ b, IsManifold I3 ∞ (N b)) (_ : ∀ b, MetricSpace (C b)) (o : ∀ b, C b),
        ∃ Z : ZeroModelFamily I3 (X i) (g i) ρ hρ β N C o δ ε e T V,
          ∀ c (hc : c ∈ Z.centres), ∀ ρ' ∈ Icc (1 / 5 : ℝ) 2,
            IsCompact {x | (Z.zero c hc).radial x ≤ ρ'} := by
  obtain ⟨ε, δ', Λ', hε, hε4, hδ', hΛ', h⟩ :=
    lpa05_selected_zero_packets_with_witnesses_withCarrier hβ hβone hβζ hζone
  refine ⟨ε, δ', Λ', hε, hε4, hδ', hΛ', ?_⟩
  intro T hT hTΛ e he he1 X mX _ _ _ g hmetric α hα hstand K hK A hA hder Λ w hΛ hw hwc
  obtain ⟨V, hTV, δ, hδ0, hδδ', hW⟩ := h T hT hTΛ e he he1 X g hmetric α hα hstand K hK A hA hder
    Λ w hΛ hw hwc
  refine ⟨V, hTV, δ, hδ0, hδδ', ?_⟩
  filter_upwards [hW] with i hi ρ hρ hρc hρw
  obtain ⟨N, C, mN, cN, hMN, mC, o, u, hmodels, Z, hcore, -⟩ := hi ρ hρ hρc hρw
  refine ⟨N, C, mN, cN, hMN, mC, o, Z, fun c hc ρ' hρ' => ?_⟩
  obtain ⟨T₀, -, Ψ, hΨs, hΨi⟩ := hcore c hc ρ' hρ'
  exact isCompact_of_core_cases (u (Z.zero c hc).model)
    (hmodels (Z.zero c hc).model).2.2.2.2.1 Ψ hΨs hΨi

end DifferentialGeometry.Geometry.Collapse
