import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05WithCarrierApplications
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.CoreCollar
import DifferentialGeometry.Geometry.Collapse.SublevelCore.PointNormalFlowRadius

/-!
# The boundaries of the selected closed cores (items (2), (3) of review 43's checklist)

* `core_cases_frontier`: for the core coordinate `u` of the carrier export, every core
  `{u ≤ T}`, `T > 0`, is closed and its frontier is the level `{u = T}` (empty on a compact model,
  the top level of a disc core otherwise, `frontier_discCore_eq`).
* `lpa05_selected_core_boundary_withCarrier`: in LPA05's selection with the carrier, at every
  selected centre `c` and every `ρ ∈ [1/5, 2]`, for the SAME radial function `η_c`:
  - the actual sublevel `A = {η_c ≤ ρ}` has boundary `frontier A = {η_c = ρ}` (regular level,
    `frontier_sublevel_eq_level_of_regular`);
  - the gradient of `η_c` (metric `r_c⁻² g`) is strictly transverse to it,
    `dη_c(∇η_c) > 0` (`mvfderiv_gradFun_pos`);
  - enclosure: `B(c, (ρ - e) r_c) ⊆ A ⊆ B(c, (ρ + e) r_c)`;
  - the ambient partial diffeomorphism `Ψ` of the closed LC38 carries `A` onto `{u_c ≤ T}` AND its
    boundary `{η_c = ρ}` onto the level `{u_c = T}` (`partialDiffeomorph_image_frontier_of_subset_source`).
The radial collar of `A` is `core_radial_collar` applied to the soul bundle of the model.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric Function
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Topology.VectorBundle

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- **The cores of the carrier export are closed with the level as frontier.** -/
theorem core_cases_frontier {Ns : Type} [TopologicalSpace Ns] [ChartedSpace E3 Ns] (u : Ns → ℝ)
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
    {T : ℝ} (hT : 0 < T) :
    IsClosed {y | u y ≤ T} ∧ frontier {y | u y ≤ T} = {y | u y = T} := by
  rcases hcases with ⟨-, hu⟩ | ⟨F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, -, hu⟩ |
      ⟨F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, -, hu⟩ |
      ⟨B, k1, k2, k3, k4, k5, k6, F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, -, hu, -⟩
  · have h1 : {y | u y ≤ T} = univ := eq_univ_of_forall fun y => by
      change u y ≤ T
      rw [hu y]
      exact hT.le
    have h2 : {y | u y = T} = ∅ := eq_empty_of_forall_notMem fun y hy => by
      change u y = T at hy
      rw [hu y] at hy
      exact hT.ne hy
    rw [h1, h2]
    exact ⟨isClosed_univ, frontier_univ⟩
  all_goals
    have hcont := continuous_discCoreRadius_of_isContMDiffRiemannianBundle D
    have h1 : {y | u y ≤ T} = {y | ‖(D.symm y).2‖ ≤ T} := by simp only [hu]
    have h2 : {y | u y = T} = {y | ‖(D.symm y).2‖ = T} := by simp only [hu]
    rw [h1, h2]
    exact ⟨isClosed_le hcont continuous_const,
      frontier_discCore_eq D.toHomeomorph hcont hT⟩

/-- **The boundaries of the selected closed cores.** In LPA05's selection with the carrier, at every
selected centre and every `ρ ∈ [1/5, 2]`: `frontier {η_c ≤ ρ} = {η_c = ρ}`, `dη_c(∇η_c) > 0` on
it, the enclosure `B(c, (ρ - e) r_c) ⊆ {η_c ≤ ρ} ⊆ B(c, (ρ + e) r_c)`, and an ambient partial
diffeomorphism carrying `{η_c ≤ ρ}` onto `{u_c ≤ T}` and `{η_c = ρ}` onto `{u_c = T}`. -/
theorem lpa05_selected_core_boundary_withCarrier
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
        (_ : ∀ b, IsManifold I3 ∞ (N b)) (_ : ∀ b, MetricSpace (C b)) (o : ∀ b, C b)
        (u : ∀ b, N b → ℝ),
        ∃ Z : ZeroModelFamily I3 (X i) (g i) ρ hρ β N C o δ ε e T V,
          ∀ c (hc : c ∈ Z.centres), ∀ ρ' ∈ Icc (1 / 5 : ℝ) 2,
            frontier {x | (Z.zero c hc).radial x ≤ ρ'} = {x | (Z.zero c hc).radial x = ρ'} ∧
            (∀ q, (Z.zero c hc).radial q = ρ' →
              0 < mvfderiv I3 (Z.zero c hc).radial q
                (gradFun (scaleMetric (((Z.zero c hc).radius)⁻¹ ^ 2)
                  (pow_pos (inv_pos.mpr (Z.zero c hc).radius_pos) 2) (g i))
                  (Z.zero c hc).radial q)) ∧
            (∀ x, dist x (Z.zero c hc).center < (ρ' - e) * (Z.zero c hc).radius →
              (Z.zero c hc).radial x ≤ ρ') ∧
            (∀ x, (Z.zero c hc).radial x ≤ ρ' →
              dist x (Z.zero c hc).center < (ρ' + e) * (Z.zero c hc).radius) ∧
            ∃ T₀ : ℝ, 0 < T₀ ∧ ∃ Ψ : PartialDiffeomorph I3 I3 (X i) (N (Z.zero c hc).model) ∞,
              {x | (Z.zero c hc).radial x ≤ ρ'} ⊆ Ψ.source ∧
              Ψ '' {x | (Z.zero c hc).radial x ≤ ρ'} = {y | u (Z.zero c hc).model y ≤ T₀} ∧
              Ψ '' {x | (Z.zero c hc).radial x = ρ'} = {y | u (Z.zero c hc).model y = T₀} := by
  obtain ⟨ε, δ', Λ', hε, hε4, hδ', hΛ', h⟩ :=
    lpa05_selected_zero_packets_with_witnesses_withCarrier hβ hβone hβζ hζone
  refine ⟨ε, δ', Λ', hε, hε4, hδ', hΛ', ?_⟩
  intro T hT hTΛ e he he1 X mX _ _ _ g hmetric α hα hstand K hK A hA hder Λ w hΛ hw hwc
  obtain ⟨V, hTV, δ, hδ0, hδδ', hW⟩ := h T hT hTΛ e he he1 X g hmetric α hα hstand K hK A hA hder
    Λ w hΛ hw hwc
  refine ⟨V, hTV, δ, hδ0, hδδ', ?_⟩
  filter_upwards [hW] with i hi ρ hρ hρc hρw
  obtain ⟨N, C, mN, cN, hMN, mC, o, u, hmodels, Z, hcore, -⟩ := hi ρ hρ hρc hρw
  refine ⟨N, C, mN, cN, hMN, mC, o, u, Z, fun c hc ρ' hρ' => ?_⟩
  have hR := (Z.zero c hc).radius_pos
  obtain ⟨hlip, -, hclose, -, -, -, -, -, -, -, ⟨O', hO'o, hO'sub, hO'sm, hne⟩, -⟩ :=
    (Z.zero c hc).radial_spec
  have hηc : Continuous (Z.zero c hc).radial :=
    @LipschitzWith.continuous (X i) ℝ ((mX i).rescale ((Z.zero c hc).radius)⁻¹
      (inv_pos.mpr hR)).toPseudoEMetricSpace _ _ _ hlip
  have hlevel : ∀ q, (Z.zero c hc).radial q = ρ' → q ∈ O' := fun q hq =>
    hO'sub (show (Z.zero c hc).radial q ∈ Icc (1 / 5 : ℝ) 2 by rw [hq]; exact hρ')
  have hfr : frontier {x | (Z.zero c hc).radial x ≤ ρ'} = {x | (Z.zero c hc).radial x = ρ'} :=
    frontier_sublevel_eq_level_of_regular (I := I3) hηc fun q hq =>
      ⟨((hO'sm.contMDiffAt (hO'o.mem_nhds (hlevel q hq))).of_le (by norm_num)),
        mfderiv_ne_zero_of_gradFun_ne_zero _ (hne q (hlevel q hq))⟩
  have hcl : ∀ x, |(Z.zero c hc).radial x - ((Z.zero c hc).radius)⁻¹ *
      dist x (Z.zero c hc).center| < e := by
    intro x
    have h1 := hclose x
    rw [@Metric.infDist_singleton (X i) ((mX i).rescale ((Z.zero c hc).radius)⁻¹
      (inv_pos.mpr hR)).toPseudoMetricSpace] at h1
    exact h1
  obtain ⟨T₀, hT₀, Ψ, hΨs, hΨi⟩ := hcore c hc ρ' hρ'
  obtain ⟨hclu, hfru⟩ := core_cases_frontier (u (Z.zero c hc).model)
    (hmodels (Z.zero c hc).model).2.2.2.2.1 hT₀
  have hAc : IsClosed {x | (Z.zero c hc).radial x ≤ ρ'} := isClosed_le hηc continuous_const
  refine ⟨hfr, fun q hq => mvfderiv_gradFun_pos _ (hne q (hlevel q hq)), fun x hx => ?_,
    fun x hx => ?_, T₀, hT₀, Ψ, hΨs, hΨi, ?_⟩
  · have h1 := (abs_lt.mp (hcl x)).2
    have h2 : ((Z.zero c hc).radius)⁻¹ * dist x (Z.zero c hc).center < ρ' - e := by
      rw [inv_mul_lt_iff₀ hR]
      linarith
    linarith
  · have h1 := (abs_lt.mp (hcl x)).1
    have hx' : (Z.zero c hc).radial x ≤ ρ' := hx
    have h2 : ((Z.zero c hc).radius)⁻¹ * dist x (Z.zero c hc).center < ρ' + e := by linarith
    rw [inv_mul_lt_iff₀ hR] at h2
    linarith
  · rw [← hfr, partialDiffeomorph_image_frontier_of_subset_source Ψ hAc hΨs (hΨi ▸ hclu), hΨi, hfru]

end DifferentialGeometry.Geometry.Collapse
