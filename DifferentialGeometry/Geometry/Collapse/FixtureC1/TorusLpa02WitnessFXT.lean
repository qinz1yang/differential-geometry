import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusLpa02AtScaleFXT

/-!
# LPA02 on the flat torus, part 3: the per-member joint witness `Lpa02WitnessV2` (S-LPA02-TOR, G3)

Lane S-LPA02-TOR (suffix `_FXT`). `Lpa02WitnessV2 g K Λ w ε e T V δ` asks, at every point `p` and
every radius `0 < r ≤ 2 r_p(w')`, for ONE scale `s ∈ [T, V]` carrying `Lpa02WitnessAtV2`.

On a flat torus `T³_Λ` with all periods `≥ f` and diameter `≤ D` the witness holds at `s = T`
when `T r ≤ δ f/4` (regime S, `torAtSmall_FXT`) and at `s = V` when `D ≤ δ V r` (regime B,
`torAtBig_FXT`). For every `r` one of the two applies as soon as `4 T D ≤ δ² f V`
(`torLpa02Witness_FXT`): if `T r > δ f/4` then `δ V r > δ² f V/(4 T) ≥ D`.

The numeric hypothesis `4 T D ≤ δ² f V` (a lower bound of `V/T`) is NECESSARY, not an artefact:
for `V < 10 T` the witness is false on every flat torus (take `r` with `T r` just above `f/4`;
every `s ∈ [T, V]` then has `s r ∈ (f/4, 5f/2)`, so `B(p, s r/5)` is a topological ball while
`B(p, 2 s r)` contains the essential fibre loop, and no single `Ns` is diffeomorphic to all balls
`B(p, ρ' s r)`, `ρ' ∈ [1/5, 2]`). The register only records `T₀ ≤ V` (`T₀_le_V_VAL6`); the
threshold record of the fixture must enlarge `lpa02V` (`ClosedStrategyBelowV4` has no `lpa02V`
slot).

* `torLpa02Witness_FXT`: the witness on `torMetric_FXC1 Λ` under `0 < T ≤ V`, `4 T D ≤ δ² f V`,
  `δ < radialSmoothingConeError (ε/4)`, `0 < ε < 1`, `0 < e < 1/40`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric GC.MetricGeometry
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] torMS_FXC1

/-- **LPA02's per-member joint witness on the flat torus.** -/
theorem torLpa02Witness_FXT (Λ : TorusPeriods_FXC1) {f D : ℝ} (hf0 : 0 < f)
    (hf : ∀ i, f ≤ Λ.L i) (hD : Metric.diam (univ : Set (Tor_FXC1 Λ)) ≤ D) (K : ℕ)
    {Λ' w ε e T V δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (he : 0 < e) (he1 : e < 1 / 40)
    (hδ : 0 < δ) (hδ2 : δ < radialSmoothingConeError (ε / 4)) (hT : 0 < T) (hTV : T ≤ V)
    (hV : 4 * T * D ≤ δ ^ 2 * f * V) :
    Lpa02WitnessV2 (torMetric_FXC1 Λ) K Λ' w ε e T V δ := by
  intro p r hr _
  by_cases hsmall : T * r ≤ δ * (f / 4)
  · exact ⟨T, ⟨le_rfl, hTV⟩, hT, torAtSmall_FXT Λ hf0 hf K hε hε1 he he1 hδ hδ2 p hr hT hsmall⟩
  · have hVpos : 0 < V := hT.trans_le hTV
    have hlt : δ * (f / 4) < T * r := not_le.mp hsmall
    have hDle : D ≤ δ * (V * r) := by
      have h1 : δ ^ 2 * f * V < 4 * T * (δ * (V * r)) := by
        have h2 : δ * f < 4 * (T * r) := by linarith
        have h3 : 0 < δ * V := mul_pos hδ hVpos
        nlinarith
      have h4 : 4 * T * D < 4 * T * (δ * (V * r)) := lt_of_le_of_lt hV h1
      have h5 : 0 < 4 * T := by positivity
      exact (mul_lt_mul_iff_right₀ h5 |>.mp h4).le
    exact ⟨V, ⟨hTV, le_rfl⟩, hVpos,
      torAtBig_FXT Λ K hε hε1 he he1 hδ hδ2 p hr hVpos (hD.trans hDle)⟩

end DifferentialGeometry.Geometry.Collapse
