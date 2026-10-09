import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarHeightLevels

/-!
# Consumers of the BCP01 levels (C1/C2)

* `CuspEmbedding.bcp01_with_levels`: the BCP01 height `η` of `CuspEmbedding.bcp01` (the same `η`
  as its clauses (a), (b), (c)) has, inside the collar band, smooth torus levels for every
  `3 ≤ t ≤ 97`: the localised `η'` agrees with `η` near `e(12/5 ≤ z ≤ 488/5)`, its values in
  `[3, 97]` are taken only there, and each level `η' = t` is a smooth torus.
* `NearlyCuspidalBoundary.bcp01_with_levels`: the same in the `i`-th collar.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Geometry.Connection

namespace DifferentialGeometry.Geometry.Collapse

variable {W : CompactCarrier.{0}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
  {X : Set W.Carrier}

/-- **BCP01 with its level tori.** -/
theorem CuspEmbedding.bcp01_with_levels (e : CuspEmbedding W g K δ X) (hK : 1 ≤ K)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 1000) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 1000) :
    ∃ η η' : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η ∧ ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η' ∧
      (∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
        |η (e.toFun p) - p.2.val 0| < ε ∧
        ∀ u w : TangentSpace W.model (e.toFun p),
          |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g) η
              (e.toFun p) u w| ≤
            3 / 2 * Real.sqrt (g.inner (e.toFun p) u u) * Real.sqrt (g.inner (e.toFun p) w w)) ∧
      (∀ p ∈ cuspDomain, 12 / 5 ≤ p.2.val 0 → p.2.val 0 ≤ 488 / 5 →
        η' =ᶠ[𝓝 (e.toFun p)] η) ∧
      (∀ y, 3 ≤ η' y → η' y ≤ 97 →
        ∃ p ∈ cuspDomain, 12 / 5 < p.2.val 0 ∧ p.2.val 0 < 488 / 5 ∧ e.toFun p = y ∧
          η' y = η y) ∧
      ∀ t : ℝ, 3 ≤ t → t ≤ 97 →
        ∃ cs : ChartedSpace (Topology.Morse.MorseModel 2) {y : W.Carrier // η' y = t},
          letI := cs
          Nonempty ({y : W.Carrier // η' y = t} ≃ₘ⟮𝓘(ℝ, Topology.Morse.MorseModel 2),
            torusModel⟯ Torus) := by
  obtain ⟨η, -, -, -, hη, -, hb, -⟩ := e.bcp01 hK hδ0 hδ hε hε1
  obtain ⟨η', hη', heq, hin, hlev, -⟩ := e.levels_of_height hη
    (fun p hp h2 h98 => lt_of_lt_of_le (hb p hp h2 h98).1 (by linarith))
    (fun p hp h2 h98 => lt_trans (by norm_num) (hb p hp h2 h98).2.2.2.2.2.2.1)
  refine ⟨η, η', hη, hη', fun p hp h2 h98 => ⟨(hb p hp h2 h98).1, (hb p hp h2 h98).2.2.2.2.2.1⟩,
    heq, hin, fun t ht3 ht97 => ?_⟩
  obtain ⟨cs, -, -, hT⟩ := hlev t ht3 ht97
  exact ⟨cs, hT⟩

/-- The same in the `i`-th collar of a nearly cuspidal boundary. -/
theorem NearlyCuspidalBoundary.bcp01_with_levels (B : NearlyCuspidalBoundary W g K δ)
    (i : Fin B.count) (hK : 1 ≤ K) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 1000) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 1000) :
    ∃ η' : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η' ∧
      ∀ t : ℝ, 3 ≤ t → t ≤ 97 →
        ∃ cs : ChartedSpace (Topology.Morse.MorseModel 2) {y : W.Carrier // η' y = t},
          letI := cs
          Nonempty ({y : W.Carrier // η' y = t} ≃ₘ⟮𝓘(ℝ, Topology.Morse.MorseModel 2),
            torusModel⟯ Torus) := by
  obtain ⟨-, η', -, hη', -, -, -, hT⟩ := (B.collar i).bcp01_with_levels hK hδ0 hδ hε hε1
  exact ⟨η', hη', hT⟩

end DifferentialGeometry.Geometry.Collapse
