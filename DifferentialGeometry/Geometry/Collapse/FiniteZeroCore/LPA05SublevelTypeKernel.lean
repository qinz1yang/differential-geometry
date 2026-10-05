import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05SublevelTypeClause

/-!
# LPA05's sublevel-type clause on ONE zero-model family (kernel, lane C14-FAM-Z)

External review 53, §4.1 (A-Z): the final families must keep, for the SAME zero family, the types
of the actual radial sublevels `{η_c ≤ a}`, `a ∈ [1/5, 2]` (LFR54 on the actual selected sublevels,
blueprint 207A, LPA05 A:30548). `lpa05_selected_sublevel_types_withCarrier` proves them inside its
own existential; here the classification step is isolated as a statement about ONE zero-model
family, so that a producer which keeps the carrier data at its own joint zero selection can apply
it to the family it returns.

* `zero_sublevel_types_of_carrier_FAMZ`: for an oriented compact three-manifold `M` with an aligned
  metric, a zero-model family `Z` whose models `N b` are proper, each with a core coordinate
  `u b : N b → ℝ` and LPA02's classification (compact model with a `C^{K-1}` metric of `sec ≥ 0`
  and `u b = 0`, or `u b` the fibre radius of a soul bundle over a point, a circle or a closed
  surface with `sec ≥ 0`), and the carrier of every actual sublevel `{η_c ≤ a}` onto a core
  `{u ≤ T₀}`: every such sublevel is `CompactModelSublevel ∨ PointSoulCoreSublevel ∨
  CircleSoulCoreSublevel ∨ ProjectiveSoulCoreSublevel ∨ KleinSoulCoreSublevel`. The proof is the
  case analysis of `lpa05_selected_sublevel_types_withCarrier` (LFR53 on the compact model, LFR54
  rows on the disc cores, the source orientation pulled back to the soul bundle, LC77's one end).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric Function Manifold
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Topology.VectorBundle
open DifferentialGeometry.Topology.Manifold

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- **The sublevel types of ONE zero-model family from its carrier data.** On an oriented compact
three-manifold with an aligned metric, a zero-model family whose proper models carry LPA02's core
coordinate `u` with its classification, and whose actual sublevels `{η_c ≤ a}`, `a ∈ [1/5, 2]`,
are carried onto cores `{u ≤ T₀}`, has every such sublevel of one of LFR54's types: the whole
source with LFR53's compact type, or a disc core `ClosedCell 3`, `solidTorusCarrier`,
`ℝP³ ∖ (open ball)` or `D(o(K))`, boundary onto boundary. -/
theorem zero_sublevel_types_of_carrier_FAMZ
    {M : Type} [mM : MetricSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
    {gM : SmoothRiemannianMetric I3 M}
    (hmetric : ∀ a b : M, riemannianEDistOf gM a b = ENNReal.ofReal (dist a b))
    (oM : ManifoldOrientation (𝓡 3) M 3)
    {ρ : M → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {N C : M → Type}
    [∀ b, MetricSpace (N b)] [∀ b, ChartedSpace E3 (N b)] [∀ b, IsManifold I3 ∞ (N b)]
    [∀ b, MetricSpace (C b)] {o : ∀ b, C b} {δ ε e T V : ℝ}
    (Z : ZeroModelFamily I3 M gM ρ hρ β N C o δ ε e T V) {K : ℕ} (hK : 3 ≤ K)
    (u : ∀ b, N b → ℝ) (hprop : ∀ b, ProperSpace (N b))
    (hcases : ∀ b, (CompactSpace (N b) ∧ (∀ y, u b y = 0) ∧
          ∃ G' : ContMDiffRiemannianMetric I3 ((K - 1 : ℕ) : ℕ∞ω) E3
              (TangentSpace I3 : N b → Type _),
            ∀ (x : N b) (u₁ u₂ : TangentSpace I3 x), 0 ≤ G'.sectionalCurvature x u₁ u₂) ∨
        (∃ (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
            (_ : FiniteDimensional ℝ F) (V : (Fin 0 → ℝ) → Type)
            (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
            (_ : TopologicalSpace (TotalSpace F V)) (_ : FiberBundle F V)
            (_ : VectorBundle ℝ F V) (_ : ContMDiffVectorBundle ∞ F V 𝓘(ℝ, Fin 0 → ℝ))
            (_ : IsContMDiffRiemannianBundle 𝓘(ℝ, Fin 0 → ℝ) ∞ F V)
            (D : Diffeomorph (𝓘(ℝ, Fin 0 → ℝ).prod 𝓘(ℝ, F)) I3 (TotalSpace F V) (N b) ∞),
            Module.finrank ℝ F = 3 ∧ ∀ x, u b x = ‖(D.symm x).2‖) ∨
        (∃ (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
            (_ : FiniteDimensional ℝ F) (V : AddCircle (1 : ℝ) → Type)
            (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
            (_ : TopologicalSpace (TotalSpace F V)) (_ : FiberBundle F V)
            (_ : VectorBundle ℝ F V) (_ : ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ))
            (_ : IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V)
            (D : Diffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) I3 (TotalSpace F V) (N b) ∞),
            Module.finrank ℝ F = 2 ∧ ∀ x, u b x = ‖(D.symm x).2‖) ∨
        ∃ (B : Type) (_ : TopologicalSpace B) (_ : ChartedSpace E2 B)
            (_ : IsManifold (𝓡 2) ∞ B) (_ : CompactSpace B) (_ : T2Space B)
            (_ : ConnectedSpace B)
            (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
            (_ : FiniteDimensional ℝ F) (V : B → Type)
            (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
            (_ : TopologicalSpace (TotalSpace F V)) (_ : FiberBundle F V)
            (_ : VectorBundle ℝ F V) (_ : ContMDiffVectorBundle ∞ F V (𝓡 2))
            (_ : IsContMDiffRiemannianBundle (𝓡 2) ∞ F V)
            (D : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, F)) I3 (TotalSpace F V) (N b) ∞),
            Module.finrank ℝ F = 1 ∧ (∀ x, u b x = ‖(D.symm x).2‖) ∧
            ∃ nB : ℕ∞ω, 2 ≤ nB ∧
              ∃ kB : ContMDiffRiemannianMetric (𝓡 2) nB E2 (TangentSpace (𝓡 2) : B → Type _),
                ∀ (x : B) (u₁ u₂ : TangentSpace (𝓡 2) x), 0 ≤ kB.sectionalCurvature x u₁ u₂)
    (hcore : ∀ c (hc : c ∈ Z.centres), ∀ a ∈ Icc (1 / 5 : ℝ) 2, ∃ T₀ : ℝ, 0 < T₀ ∧
      ∃ Ψ : PartialDiffeomorph I3 I3 M (N (Z.zero c hc).model) ∞,
        {x | (Z.zero c hc).radial x ≤ a} ⊆ Ψ.source ∧
          Ψ '' {x | (Z.zero c hc).radial x ≤ a} = {y | u (Z.zero c hc).model y ≤ T₀}) :
    ∀ c (hc : c ∈ Z.centres), ∀ a ∈ Icc (1 / 5 : ℝ) 2,
      CompactModelSublevel oM (N (Z.zero c hc).model) {x | (Z.zero c hc).radial x ≤ a} ∨
      PointSoulCoreSublevel (N (Z.zero c hc).model) {x | (Z.zero c hc).radial x ≤ a} ∨
      CircleSoulCoreSublevel (N (Z.zero c hc).model) {x | (Z.zero c hc).radial x ≤ a} ∨
      ProjectiveSoulCoreSublevel (N (Z.zero c hc).model) {x | (Z.zero c hc).radial x ≤ a} ∨
      KleinSoulCoreSublevel (N (Z.zero c hc).model) {x | (Z.zero c hc).radial x ≤ a} := by
  have hLFR54 := ZeroModel.lfr54_classified_finite_zero_packet.{0, 0, 0, 0, 0, 0, 0, 0, 0}
  intro c hc ρ' hρ'
  obtain ⟨T₀, hT₀, Ψ, hΨs, hΨi⟩ := hcore c hc ρ' hρ'
  have hpN := hprop (Z.zero c hc).model
  have h1 : (1 : ℝ) ∈ Icc (1 / 5 : ℝ) 2 := ⟨by norm_num, by norm_num⟩
  have hballT := (Z.zero c hc).modelChart_target 1 h1
  rcases hcases (Z.zero c hc).model with ⟨hcpt, hu, Gc, hGc⟩ |
      ⟨F, i1, i2, i3, V', j1, j2, j3, j4, j5, j6, j7, D, hF3, hu⟩ |
      ⟨F, i1, i2, i3, V', j1, j2, j3, j4, j5, j6, j7, D, hF2, hu⟩ |
      ⟨B, k1, k2, k3, k4, k5, k6, F, i1, i2, i3, V', j1, j2, j3, j4, j5, j6, j7, D, hF1, hu, nB,
        hnB, kB, hkB⟩
  · -- compact model: the sublevel is the whole source
    left
    obtain ⟨hlip, -, -, -, -, -, hc0, -⟩ := (Z.zero c hc).radial_spec
    have hηc : Continuous (Z.zero c hc).radial :=
      @LipschitzWith.continuous M ℝ (mM.rescale ((Z.zero c hc).radius)⁻¹
        (inv_pos.mpr (Z.zero c hc).radius_pos)).toPseudoEMetricSpace _ _ _ hlip
    have hAcl : IsClosed {x | (Z.zero c hc).radial x ≤ ρ'} := isClosed_le hηc continuous_const
    have huniv : Ψ '' {x | (Z.zero c hc).radial x ≤ ρ'} = univ := by
      rw [hΨi]
      exact eq_univ_of_forall fun y => by
        change u (Z.zero c hc).model y ≤ T₀
        rw [hu y]
        exact hT₀.le
    have hsrc : Ψ.source = {x | (Z.zero c hc).radial x ≤ ρ'} := by
      refine Subset.antisymm (fun x hx => ?_) hΨs
      have hy : Ψ x ∈ Ψ '' {x | (Z.zero c hc).radial x ≤ ρ'} := by
        rw [huniv]
        exact mem_univ _
      obtain ⟨a, ha, hax⟩ := hy
      have hax' := Ψ.toPartialEquiv.injOn (hΨs ha) hx hax
      rw [← hax']
      exact ha
    have hne : ({x | (Z.zero c hc).radial x ≤ ρ'} : Set M).Nonempty :=
      ⟨(Z.zero c hc).center, by
        change (Z.zero c hc).radial (Z.zero c hc).center ≤ ρ'
        rw [hc0]
        linarith [hρ'.1]⟩
    have instConn_FAMZ : ConnectedSpace M :=
      connectedSpace_of_aligned_metric gM hmetric (Z.zero c hc).center
    have hunivA : {x | (Z.zero c hc).radial x ≤ ρ'} = univ :=
      IsClopen.eq_univ ⟨hAcl, hsrc ▸ Ψ.open_source⟩ hne
    have htgt : Ψ.target = univ := by
      rw [← Ψ.toPartialEquiv.image_source_eq_target]
      rw [hsrc, huniv]
    have instCpt_FAMZ : CompactSpace (N (Z.zero c hc).model) := hcpt
    let Φ := DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalDiffeomorphOfUniv Ψ
      (hsrc.trans hunivA) htgt
    exact ⟨hunivA, hcpt, ⟨Φ⟩, exists_compactNonnegativeType_of_diffeomorph oM Φ
      (by exact_mod_cast (show 2 ≤ K - 1 by omega)) Gc hGc⟩
  · -- point soul
    right; left
    have hd : Module.finrank ℝ ((Fin 0 → ℝ) × F) = 2 + 1 := by
      rw [Module.finrank_prod, Module.finrank_fin_fun, hF3]
    have hΨi' : Ψ '' {x | (Z.zero c hc).radial x ≤ ρ'} = {y | ‖(D.symm y).2‖ ≤ T₀} := by
      rw [hΨi]
      ext y
      simp only [mem_ofPred_eq, hu]
    obtain ⟨Φ, hΦ1, hΦ2⟩ := hLFR54.1 (B := Fin 0 → ℝ) hd (Module.finrank_fin_fun ℝ) D T₀ hT₀
    exact ⟨F, i1, i2, i3, V', j1, j2, j3, j4, j5, j6, j7, D, hd, T₀, hT₀, Ψ, hΨs, hΨi', Φ, hΦ1,
      hΦ2⟩
  · -- circle soul
    right; right; left
    have hd : Module.finrank ℝ (ℝ × F) = 2 + 1 := finrank_real_prod_eq_three hF2
    have hΨi' : Ψ '' {x | (Z.zero c hc).radial x ≤ ρ'} = {y | ‖(D.symm y).2‖ ≤ T₀} := by
      rw [hΨi]
      ext y
      simp only [mem_ofPred_eq, hu]
    obtain ⟨oV⟩ := nonempty_smoothOrientation_of_ball_chart oM
      ((Z.zero c hc).modelChart 1 h1) hballT D
    obtain ⟨Φ, hΦ⟩ := hLFR54.2.1 hF2 oV D T₀ hT₀
    exact ⟨F, i1, i2, i3, V', j1, j2, j3, j4, j5, j6, j7, D, hd, T₀, hT₀, Ψ, hΨs, hΨi', Φ, hΦ⟩
  · -- surface soul
    right; right; right
    have hd : Module.finrank ℝ (E2 × F) = 2 + 1 := by
      rw [Module.finrank_prod, finrank_euclideanSpace_fin, hF1]
    have hΨi' : Ψ '' {x | (Z.zero c hc).radial x ≤ ρ'} = {y | ‖(D.symm y).2‖ ≤ T₀} := by
      rw [hΨi]
      ext y
      simp only [mem_ofPred_eq, hu]
    obtain ⟨oN⟩ := nonempty_smoothOrientation_of_ball_chart oM
      ((Z.zero c hc).modelChart 1 h1) hballT D
    rcases hLFR54.2.2.1 hd oN hnB kB hkB D (Z.one_end c hc) T₀ hT₀ with
      ⟨cb, f, hf1, hf2, hf3⟩ | ⟨Φ, hΦ⟩
    · left
      exact ⟨B, k1, k2, k3, k4, k5, k6, F, i1, i2, i3, V', j1, j2, j3, j4, j5, j6, j7, D, hd, T₀,
        hT₀, Ψ, hΨs, hΨi', cb, f, hf1, hf2, hf3⟩
    · right
      exact ⟨B, k1, k2, k3, k4, k5, k6, F, i1, i2, i3, V', j1, j2, j3, j4, j5, j6, j7, D, hd, T₀,
        hT₀, Ψ, hΨs, hΨi', Φ, hΦ⟩

end DifferentialGeometry.Geometry.Collapse
