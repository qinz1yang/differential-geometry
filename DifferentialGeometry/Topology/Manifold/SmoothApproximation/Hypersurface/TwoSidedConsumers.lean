import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Hypersurface.TwoSided
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Consumers of the two-sided hypersurface smoothing (W-SUB, T)

* `exists_smooth_carrier_two_sided`: the form LFR47 consumes — a compact smooth manifold
  `Ŝ` (an embedded slice of `M` with its charted space) together with a `C^n` diffeomorphism onto
  the `C^n` base `S`.
* `exists_smooth_hypersurface_product`: the zero section of the trivial line bundle `S × ℝ` over a
  compact smooth manifold (identity tube).
* `exists_smooth_hypersurface_sphere_product`: the concrete case of the round `2`-sphere,
  `S² × ℝ` with its product structure.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Manifold.SmoothHypersurface

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {ES : Type*} [NormedAddCommGroup ES] [NormedSpace ℝ ES] [CompleteSpace ES]
  {HS : Type*} [TopologicalSpace HS] {IS : ModelWithCorners ℝ ES HS} [IS.Boundaryless]
  {S : Type*} [TopologicalSpace S] [ChartedSpace HS S] [CompactSpace S]

/-- **The compatible smooth carrier of LFR47 (two-sided case).** A compact `C^n` manifold with a
two-sided `C^n` tube in a smooth manifold is `C^n`-diffeomorphic to a compact smooth manifold,
realized as a smooth embedded slice inside the tube. -/
theorem exists_smooth_carrier_two_sided {d : ℕ} (hdim : Module.finrank ℝ E = d + 1)
    {n : ℕ} (hn : 1 ≤ n)
    (Φ : PartialDiffeomorph (IS.prod 𝓘(ℝ, ℝ)) I (S × ℝ) M n) {ε : ℝ} (hε : 0 < ε)
    (hsrc : univ ×ˢ Ioo (-ε) ε ⊆ Φ.source) :
    ∃ Ŝ : Set M, ∃ hŜ : IsEmbeddedSlice I d Ŝ, Ŝ ⊆ Φ.target ∧
      let _ := embeddedSliceChartedSpace hŜ
      IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ Ŝ ∧ CompactSpace Ŝ ∧
        Nonempty (Diffeomorph 𝓘(ℝ, Fin d → ℝ) IS Ŝ S n) := by
  obtain ⟨Ŝ, hŜ, hc, hsub, hrest⟩ :=
    exists_smooth_hypersurface_two_sided hdim hn Φ hε le_rfl hsrc
  refine ⟨Ŝ, hŜ, fun x hx => ?_, ?_⟩
  · obtain ⟨p, hp, rfl⟩ := hsub hx
    exact Φ.map_source (hsrc hp)
  intro _
  obtain ⟨β, -⟩ := hrest
  exact ⟨embeddedSlice_isManifold hŜ, isCompact_iff_compactSpace.mp hc, ⟨β⟩⟩

/-- **The trivial line bundle.** Over a compact smooth manifold `S`, the identity tube of
`S × ℝ` yields a smooth slice `Ŝ ⊆ S × (-δ, δ)`, `C^n`-diffeomorphic to `S` by the first
projection. -/
theorem exists_smooth_hypersurface_product [FiniteDimensional ℝ ES] [IsManifold IS ∞ S]
    [T2Space S] {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Ŝ : Set (S × ℝ),
      ∃ hŜ : IsEmbeddedSlice (IS.prod 𝓘(ℝ, ℝ)) (Module.finrank ℝ ES) Ŝ,
      IsCompact Ŝ ∧ Ŝ ⊆ univ ×ˢ Ioo (-δ) δ ∧
      let _ := embeddedSliceChartedSpace hŜ
      ∃ β : Diffeomorph 𝓘(ℝ, Fin (Module.finrank ℝ ES) → ℝ) IS Ŝ S n, ∀ x, β x = x.1.1 := by
  let Φ := (Diffeomorph.refl (IS.prod 𝓘(ℝ, ℝ)) (S × ℝ) n).toPartialDiffeomorph
  have hdim : Module.finrank ℝ (ES × ℝ) = Module.finrank ℝ ES + 1 := by
    rw [Module.finrank_prod, Module.finrank_self]
  obtain ⟨Ŝ, hŜ, hc, hsub, hrest⟩ := exists_smooth_hypersurface_two_sided
    (I := IS.prod 𝓘(ℝ, ℝ)) hdim hn Φ hδ le_rfl (subset_univ _)
  refine ⟨Ŝ, hŜ, hc, fun x hx => ?_, ?_⟩
  · obtain ⟨p, hp, rfl⟩ := hsub hx
    exact hp
  intro _
  obtain ⟨β, hβ, -⟩ := hrest
  exact ⟨β, fun x => hβ x⟩

/-- **Concrete case: the round `2`-sphere.** In `S² × ℝ`, every height bound `δ > 0` admits a smooth
compact slice inside `S² × (-δ, δ)` that is `C¹`-diffeomorphic to `S²` by the projection. -/
theorem exists_smooth_hypersurface_sphere_product {δ : ℝ} (hδ : 0 < δ) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
    ∃ Ŝ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ),
      ∃ hŜ : IsEmbeddedSlice ((𝓡 2).prod 𝓘(ℝ, ℝ)) (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))) Ŝ,
      IsCompact Ŝ ∧ Ŝ ⊆ univ ×ˢ Ioo (-δ) δ ∧
      let _ := embeddedSliceChartedSpace hŜ
      ∃ β : Diffeomorph 𝓘(ℝ, Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))) → ℝ) (𝓡 2) Ŝ
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) 1, ∀ x, β x = x.1.1 := by
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  exact exists_smooth_hypersurface_product le_rfl hδ

end DifferentialGeometry.Topology.Manifold.SmoothHypersurface
