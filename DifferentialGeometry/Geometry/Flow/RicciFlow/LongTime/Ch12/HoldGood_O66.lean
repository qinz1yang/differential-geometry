import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CoresAssembly_O21
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TimeSmoothingDomain_CX5
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ForwardWindowDef_S45

set_option autoImplicit false

/-! # CH12-O66 G1: hold.GOOD (OLD-GOOD text of `[FROZEN v3] CH12-O66 hEndSfam`)

`oldGood_of_single_O66`: the OLD-GOOD premise (= the first three conjuncts of `[FROZEN] CH12-O60`
`hold`) from the per-model clauses of the hfam invariant `Single` (R3AssemblyV3_S114). This is
the hone/hfam-side adapter of hEndSfam v3. -/
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime DifferentialGeometry.CheegerGromovCompactness
open TopologicalSpace Filter
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace GC.LongTime.Ch12

/-- G1 (hold.GOOD): the OLD-GOOD text from the per-model clauses of the hfam invariant `Single`
(R3AssemblyV3_S114 l.361-368: positivity on `t ≥ s`, `α → 0`, smooth embedding on
`sourceSlice_CX5 Ω t`, `B(2α⁻¹) ⊆ sourceSlice_CX5 Ω t`, `ckErr_O21` up to `max K ⌈α⁻¹⌉`). -/
theorem oldGood_of_single_O66 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ)
    (old : ℕ) (Hold : Fin old → FiniteVolumeHyperbolicModel.{u}) (sold : Fin old → ℝ)
    (mold : ∀ i (t : ℝ), sold i ≤ t → (Hold i).Carrier → (postStage F.observation t).Carrier)
    (αo : Fin old → ℝ → ℝ) (Ωo : ∀ i, TopologicalSpace.Opens (ℝ × (Hold i).Carrier))
    (hpos : ∀ i t, sold i ≤ t → 0 < αo i t)
    (hlim : ∀ i (ε : ℝ), 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → αo i t < ε)
    (hsm : ∀ i t (ht : sold i ≤ t),
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mold i t ht) (sourceSlice_CX5 (Ωo i) t))
    (hemb : ∀ i t (ht : sold i ≤ t),
      IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : sourceSlice_CX5 (Ωo i) t => mold i t ht x))
    (hball : ∀ i t, sold i ≤ t → riemannianBallOf (Hold i).metric (Hold i).basepoint
      (2 * (αo i t)⁻¹) ⊆ sourceSlice_CX5 (Ωo i) t)
    (hck : ∀ i t (ht : sold i ≤ t), ∀ k : ℕ, k ≤ max K ⌈(αo i t)⁻¹⌉₊ →
      ∀ p ∈ riemannianBallOf (Hold i).metric (Hold i).basepoint (2 * (αo i t)⁻¹),
        ckErr_O21 (Hold i) (postMetric F.observation t) t⁻¹ (mold i t ht) k p < αo i t) :
  ∃ α : Fin old → ℝ → ℝ, (∀ i t, 0 < α i t) ∧
      (∀ i, Filter.Tendsto (α i) Filter.atTop (nhds 0)) ∧
      (∀ i t (hi : sold i ≤ t), ∃ U : TopologicalSpace.Opens (Hold i).Carrier,
        riemannianBallOf (Hold i).metric (Hold i).basepoint (2 * (α i t)⁻¹) ⊆ U ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mold i t hi) U ∧
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => mold i t hi x) ∧
        ∀ k : ℕ, k ≤ ⌈(α i t)⁻¹⌉₊ →
          ∀ p ∈ riemannianBallOf (Hold i).metric (Hold i).basepoint (2 * (α i t)⁻¹),
          ckErr_S45 (Hold i) (postMetric F.observation t) t⁻¹ (mold i t hi) k p < α i t)
    := by
  classical
  refine ⟨fun i t => if sold i ≤ t then αo i t else 1, ?_, ?_, ?_⟩
  · intro i t
    by_cases h : sold i ≤ t
    · simp only [h, ↓reduceIte]
      exact hpos i t h
    · simp only [h, ↓reduceIte]
      exact one_pos
  · intro i
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨T, hT⟩ := hlim i ε hε
    refine ⟨max T (sold i), fun t ht => ?_⟩
    have h1 : sold i ≤ t := (le_max_right _ _).trans ht
    have h2 : T ≤ t := (le_max_left _ _).trans ht
    simp only [h1, ↓reduceIte, Real.dist_eq, sub_zero]
    rw [abs_of_pos (hpos i t h1)]
    exact hT t h2
  · intro i t hi
    simp only [hi, ↓reduceIte]
    exact ⟨sourceSlice_CX5 (Ωo i) t, hball i t hi, hsm i t hi, hemb i t hi,
      fun k hk p hp => hck i t hi k (hk.trans (le_max_right _ _)) p hp⟩

end GC.LongTime.Ch12
