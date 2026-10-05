import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05SublevelTypeClause

/-!
# The sublevel-type classification from one carrier witness (lane BFAM-ZD)

The case analysis of `lpa05_selected_sublevel_types_withCarrier` (FZ/LPA05SublevelTypeClause.lean),
stated for ONE carrier witness on an arbitrary connected oriented smooth three-manifold `M` (no
compactness of `M`, so that it applies on the completed interiors of the boundary producer): a
closed nonempty `A ⊆ M` carried by an ambient partial diffeomorphism `Ψ` onto a core `{u ≤ T₀}` of
a smooth model `Ns`, where `u` is `0` on a compact model with a `C^{K-1}` metric of `sec ≥ 0` or the
fibre radius of a point / circle / surface soul bundle, and `Ns` has at most one end and an
open-ball chart `Ψb : M ⇀ Ns` onto all of `Ns` (orienting the soul bundle), has one of LFR54's
types (`CompactModelSublevel`, `PointSoulCoreSublevel`, `CircleSoulCoreSublevel`,
`ProjectiveSoulCoreSublevel`, `KleinSoulCoreSublevel`).
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

/-- **LFR54's sublevel types from one carrier witness** (lane BFAM-ZD; the case analysis of
`lpa05_selected_sublevel_types_withCarrier` for an arbitrary connected oriented `M`). A closed
nonempty `A ⊆ M` carried by `Ψ : M ⇀ Ns` onto `{u ≤ T₀}` (`T₀ > 0`), with `u = 0` on a compact
model carrying a `C^{K-1}` metric of `sec ≥ 0` or `u` the fibre radius of a point / circle /
`𝓡 2`-surface soul bundle of `Ns`, `Ns` with at most one end and an open-ball chart `Ψb` onto `Ns`:
`A` is the whole of `M` (compact model; `M` with any orientation `oM` has one of LFR53's types) or
is carried onto a disc core `D³`, `S¹ × D²`, `ℝP³ ∖ int D³` or `D(o(K))`. -/
theorem sublevel_types_of_carrier_BFZD
    {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M] [ConnectedSpace M]
    (oM : ManifoldOrientation I3 M 3)
    {Ns : Type} [MetricSpace Ns] [ProperSpace Ns] [ChartedSpace E3 Ns] [IsManifold I3 ∞ Ns]
    {K : ℕ} (hK : 10 ≤ K) {u : Ns → ℝ}
    (hcases : ((CompactSpace Ns ∧ (∀ y, u y = 0) ∧
        ∃ G' : ContMDiffRiemannianMetric I3 ((K - 1 : ℕ) : ℕ∞ω) E3 (TangentSpace I3 : Ns → Type _),
          ∀ (x : Ns) (u₁ u₂ : TangentSpace I3 x), 0 ≤ G'.sectionalCurvature x u₁ u₂) ∨
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
    (Ψb : PartialDiffeomorph I3 I3 M Ns ∞) (hΨb : Ψb.target = univ)
    (hend : ∀ Kc : Set Ns, IsCompact Kc → ∀ a₁ a₂ : Ns,
      ¬ Bornology.IsBounded (connectedComponentIn Kcᶜ a₁) →
      ¬ Bornology.IsBounded (connectedComponentIn Kcᶜ a₂) →
      connectedComponentIn Kcᶜ a₁ = connectedComponentIn Kcᶜ a₂)
    {A : Set M} (hAc : IsClosed A) (hAne : A.Nonempty) {T₀ : ℝ} (hT₀ : 0 < T₀)
    (Ψ : PartialDiffeomorph I3 I3 M Ns ∞) (hΨs : A ⊆ Ψ.source)
    (hΨi : Ψ '' A = {y | u y ≤ T₀}) :
    CompactModelSublevel oM Ns A ∨ PointSoulCoreSublevel Ns A ∨ CircleSoulCoreSublevel Ns A ∨
      ProjectiveSoulCoreSublevel Ns A ∨ KleinSoulCoreSublevel Ns A := by
  have hLFR54 := ZeroModel.lfr54_classified_finite_zero_packet.{0, 0, 0, 0, 0, 0, 0, 0, 0}
  rcases hcases with ⟨hcpt, hu, Gc, hGc⟩ | ⟨F, i1, i2, i3, V', j1, j2, j3, j4, j5, j6, j7, D, hF3, hu⟩ |
      ⟨F, i1, i2, i3, V', j1, j2, j3, j4, j5, j6, j7, D, hF2, hu⟩ |
      ⟨B, k1, k2, k3, k4, k5, k6, F, i1, i2, i3, V', j1, j2, j3, j4, j5, j6, j7, D, hF1, hu, nB,
        hnB, kB, hkB⟩
  · -- compact model: the sublevel is the whole source
    left
    have huniv : Ψ '' A = univ := by
      rw [hΨi]
      exact eq_univ_of_forall fun y => by
        change u y ≤ T₀
        rw [hu y]
        exact hT₀.le
    have hsrc : Ψ.source = A := by
      refine Subset.antisymm (fun x hx => ?_) hΨs
      have hy : Ψ x ∈ Ψ '' A := by
        rw [huniv]
        exact mem_univ _
      obtain ⟨a, ha, hax⟩ := hy
      have hax' := Ψ.toPartialEquiv.injOn (hΨs ha) hx hax
      rw [← hax']
      exact ha
    have hunivA : A = univ := IsClopen.eq_univ ⟨hAc, hsrc ▸ Ψ.open_source⟩ hAne
    have htgt : Ψ.target = univ := by
      rw [← Ψ.toPartialEquiv.image_source_eq_target]
      rw [hsrc, huniv]
    have instCpt_BFZD : CompactSpace Ns := hcpt
    let Φ := DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalDiffeomorphOfUniv Ψ
      (hsrc.trans hunivA) htgt
    exact ⟨hunivA, hcpt, ⟨Φ⟩, exists_compactNonnegativeType_of_diffeomorph oM Φ
      (by exact_mod_cast (show 2 ≤ K - 1 by omega)) Gc hGc⟩
  · -- point soul
    right; left
    have hd : Module.finrank ℝ ((Fin 0 → ℝ) × F) = 2 + 1 := by
      rw [Module.finrank_prod, Module.finrank_fin_fun, hF3]
    have hΨi' : Ψ '' A = {y | ‖(D.symm y).2‖ ≤ T₀} := by
      rw [hΨi]
      ext y
      simp only [mem_ofPred_eq, hu]
    obtain ⟨Φ, hΦ1, hΦ2⟩ := hLFR54.1 (B := Fin 0 → ℝ) hd (Module.finrank_fin_fun ℝ) D T₀ hT₀
    exact ⟨F, i1, i2, i3, V', j1, j2, j3, j4, j5, j6, j7, D, hd, T₀, hT₀, Ψ, hΨs, hΨi', Φ, hΦ1,
      hΦ2⟩
  · -- circle soul
    right; right; left
    have hd : Module.finrank ℝ (ℝ × F) = 2 + 1 := finrank_real_prod_eq_three hF2
    have hΨi' : Ψ '' A = {y | ‖(D.symm y).2‖ ≤ T₀} := by
      rw [hΨi]
      ext y
      simp only [mem_ofPred_eq, hu]
    obtain ⟨oV⟩ := nonempty_smoothOrientation_of_ball_chart oM Ψb hΨb D
    obtain ⟨Φ, hΦ⟩ := hLFR54.2.1 hF2 oV D T₀ hT₀
    exact ⟨F, i1, i2, i3, V', j1, j2, j3, j4, j5, j6, j7, D, hd, T₀, hT₀, Ψ, hΨs, hΨi', Φ, hΦ⟩
  · -- surface soul
    right; right; right
    have hd : Module.finrank ℝ (E2 × F) = 2 + 1 := by
      rw [Module.finrank_prod, finrank_euclideanSpace_fin, hF1]
    have hΨi' : Ψ '' A = {y | ‖(D.symm y).2‖ ≤ T₀} := by
      rw [hΨi]
      ext y
      simp only [mem_ofPred_eq, hu]
    obtain ⟨oN⟩ := nonempty_smoothOrientation_of_ball_chart oM Ψb hΨb D
    rcases hLFR54.2.2.1 hd oN hnB kB hkB D hend T₀ hT₀ with ⟨cb, f, hf1, hf2, hf3⟩ | ⟨Φ, hΦ⟩
    · left
      exact ⟨B, k1, k2, k3, k4, k5, k6, F, i1, i2, i3, V', j1, j2, j3, j4, j5, j6, j7, D, hd, T₀,
        hT₀, Ψ, hΨs, hΨi', cb, f, hf1, hf2, hf3⟩
    · right
      exact ⟨B, k1, k2, k3, k4, k5, k6, F, i1, i2, i3, V', j1, j2, j3, j4, j5, j6, j7, D, hd, T₀,
        hT₀, Ψ, hΨs, hΨi', Φ, hΦ⟩

end DifferentialGeometry.Geometry.Collapse
