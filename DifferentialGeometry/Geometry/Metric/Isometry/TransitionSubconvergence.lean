import DifferentialGeometry.Geometry.Metric.Isometry.FiniteJetBounds
import DifferentialGeometry.Analysis.Calculus.Compactness.FiniteOrderProof

/-!
# LFR13: uniform regularity and `C^K` subconvergence of actual transition isometries

Blueprint 207A, LFR13 (`lem:collapse-finite-transition-bounds`, A:25820–25858). Smooth chart
metrics `H i` on `U` and `G i` on `V` with uniform `C^K` bounds and uniform ellipticity, and smooth
transition maps `τ i : U → V` with `τ i ^* G i = H i`:

* derivatives of orders `1, …, K + 1` of `τ i` are uniformly bounded on `U`
  (`exists_transition_jet_bound_of_uniform_metric_bounds`; the extra derivative comes from the
  exact isometry identity, the ported
  `MetricIsometry.exists_isometry_jet_bound_of_finite_metric_bounds`);
* if the images stay in a fixed bounded chart `V`, a subsequence converges in `C^K` on every
  compact subset of `U` to a `C^K` map (`exists_transition_cK_subseq`, by the finite-order
  extraction `exists_cP_subseq_on_of_le` at order `K + 1`);
* a pointwise limit already identified is every such subsequential limit
  (`eqOn_of_mapCPConvergenceOn_of_tendsto`).

The inverse transitions are the same statement with `H` and `G` exchanged.

Deviations, recorded in `build-logs/resume/sheet-W4-F7b.md`: ellipticity is normalised to
`½‖v‖² ≤ H ≤ 2‖v‖²` (the normalisation of LFR12's charts, the only consumer of LFR13 in LFR14),
the target metric needs only the lower bound, and the bounds on the inverse matrices and on the
zeroth metric derivatives are not used (strengthening).
-/

set_option autoImplicit false

open Filter Topology Set
open scoped ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness.MetricIsometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem natCast_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by
  exact_mod_cast le_top

/-- **LFR13, derivative bounds.** Uniform `C^K` bounds (orders `1 … K`) and normalised
ellipticity of smooth chart metrics give uniform bounds for derivatives `1 … K + 1` of smooth
transition isometries. -/
theorem exists_transition_jet_bound_of_uniform_metric_bounds (K : ℕ)
    (H G : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ) (τ : ℕ → E → E) {U V : Set E}
    (hU : IsOpen U) (hV : IsOpen V)
    (hH : ∀ i, ContDiffOn ℝ ∞ (H i) U) (hG : ∀ i, ContDiffOn ℝ ∞ (G i) V)
    (hτ : ∀ i, ContDiffOn ℝ ∞ (τ i) U) (hmap : ∀ i, MapsTo (τ i) U V)
    (hiso : ∀ i, ∀ x ∈ U, ∀ u v : E,
      H i x u v = G i (τ i x) (fderiv ℝ (τ i) x u) (fderiv ℝ (τ i) x v))
    (hGsymm : ∀ i, ∀ y ∈ V, ∀ a b : E, G i y a b = G i y b a)
    (hHell : ∀ i, ∀ x ∈ U, ∀ v : E, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ H i x v v ∧ H i x v v ≤ 2 * ‖v‖ ^ 2)
    (hGell : ∀ i, ∀ y ∈ V, ∀ v : E, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ G i y v v)
    {A : ℝ} (hHb : ∀ i q, 1 ≤ q → q ≤ K → ∀ x ∈ U, ‖iteratedFDeriv ℝ q (H i) x‖ ≤ A)
    (hGb : ∀ i q, 1 ≤ q → q ≤ K → ∀ y ∈ V, ‖iteratedFDeriv ℝ q (G i) y‖ ≤ A) :
    ∃ M : ℝ, ∀ i r, 1 ≤ r → r ≤ K + 1 → ∀ x ∈ U, ‖iteratedFDeriv ℝ r (τ i) x‖ ≤ M := by
  obtain ⟨M, hM⟩ := exists_isometry_jet_bound_of_finite_metric_bounds (E0 := E) K (max 1 A)
  refine ⟨M, fun i r hr hrK x hx => ?_⟩
  have hpow : ∀ q, 1 ≤ q → A ≤ max 1 A ^ q := fun q hq =>
    (le_max_right 1 A).trans (le_self_pow₀ (le_max_left 1 A) (by omega))
  exact hM (H i) (G i) (τ i) U V hU hV ((hH i).of_le (natCast_le_infty K))
    ((hG i).of_le (natCast_le_infty K)) ((hτ i).of_le (natCast_le_infty (K + 1))) (hmap i)
    (hiso i) (hGsymm i) (hHell i) (hGell i)
    (fun q hq hqK y hy => (hHb i q hq hqK y hy).trans (hpow q hq))
    (fun q hq hqK y hy => (hGb i q hq hqK y hy).trans (hpow q hq)) r hr hrK x hx

/-- **LFR13, `C^K` subconvergence.** If moreover the images lie in a fixed bounded chart, a
subsequence of the transitions converges in `C^K` on every compact subset of `U` to a `C^K`
map. -/
theorem exists_transition_cK_subseq (K : ℕ)
    (H G : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ) (τ : ℕ → E → E) {U V : Set E}
    (hU : IsOpen U) (hV : IsOpen V) (hVb : ∃ Z : ℝ, ∀ y ∈ V, ‖y‖ ≤ Z)
    (hH : ∀ i, ContDiffOn ℝ ∞ (H i) U) (hG : ∀ i, ContDiffOn ℝ ∞ (G i) V)
    (hτ : ∀ i, ContDiffOn ℝ ∞ (τ i) U) (hmap : ∀ i, MapsTo (τ i) U V)
    (hiso : ∀ i, ∀ x ∈ U, ∀ u v : E,
      H i x u v = G i (τ i x) (fderiv ℝ (τ i) x u) (fderiv ℝ (τ i) x v))
    (hGsymm : ∀ i, ∀ y ∈ V, ∀ a b : E, G i y a b = G i y b a)
    (hHell : ∀ i, ∀ x ∈ U, ∀ v : E, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ H i x v v ∧ H i x v v ≤ 2 * ‖v‖ ^ 2)
    (hGell : ∀ i, ∀ y ∈ V, ∀ v : E, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ G i y v v)
    {A : ℝ} (hHb : ∀ i q, 1 ≤ q → q ≤ K → ∀ x ∈ U, ‖iteratedFDeriv ℝ q (H i) x‖ ≤ A)
    (hGb : ∀ i q, 1 ≤ q → q ≤ K → ∀ y ∈ V, ‖iteratedFDeriv ℝ q (G i) y‖ ≤ A) :
    ∃ (φ : ℕ → ℕ) (τinf : E → E), StrictMono φ ∧ ContDiffOn ℝ K τinf U ∧
      ∀ S : Set E, IsCompact S → S ⊆ U → MapCPConvergenceOn S K (fun k => τ (φ k)) τinf := by
  obtain ⟨M, hM⟩ := exists_transition_jet_bound_of_uniform_metric_bounds K H G τ hU hV hH hG hτ
    hmap hiso hGsymm hHell hGell hHb hGb
  obtain ⟨Z, hZ⟩ := hVb
  have hbdd : ∀ r : ℕ, r ≤ K + 1 → ∀ S : Set E, IsCompact S → S ⊆ U →
      ∃ B : ℝ, ∀ k : ℕ, ∀ x ∈ S, ‖iteratedFDeriv ℝ r (τ k) x‖ ≤ B := by
    intro r hr S _ hSU
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · exact ⟨Z, fun k x hx => by
        rw [norm_iteratedFDeriv_zero]
        exact hZ _ (hmap k (hSU hx))⟩
    · exact ⟨M, fun k x hx => hM k r hr0 hr x (hSU hx)⟩
  obtain ⟨φ, τinf, hφ, hreg, hconv⟩ := exists_cP_subseq_on_of_le (K + 1) (by omega) hU τ
    (fun k => (hτ k).of_le (natCast_le_infty (K + 1))) hbdd
  simp only [Nat.add_sub_cancel] at hreg hconv
  exact ⟨φ, τinf, hφ, hreg, hconv⟩

omit [FiniteDimensional ℝ E] in
/-- Order-zero convergence on a set containing `x` is convergence of the values at `x`. -/
theorem tendsto_of_mapCPConvergenceOn {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {p : ℕ} {Φ : ℕ → E → F} {Φinf : E → F} (h : MapCPConvergenceOn S p Φ Φinf)
    {x : E} (hx : x ∈ S) : Tendsto (fun k => Φ k x) atTop (𝓝 (Φinf x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k0, hk0⟩ := h (ε / 2) (half_pos hε)
  refine ⟨k0, fun k hk => ?_⟩
  have h0 := hk0 k hk 0 (Nat.zero_le p) x hx
  simp only [mapDerivNorm, norm_iteratedFDeriv_zero] at h0
  rw [dist_eq_norm]
  linarith

omit [FiniteDimensional ℝ E] in
/-- **LFR13, identification.** If the whole sequence converges pointwise on `U` to an already
identified map `τ₀`, every subsequential limit obtained on compact subsets of `U` (at any finite
order) equals `τ₀` on `U`. -/
theorem eqOn_of_mapCPConvergenceOn_of_tendsto {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {U : Set E} {p : ℕ} {τ : ℕ → E → F} {τ₀ τinf : E → F} {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hconv : ∀ S : Set E, IsCompact S → S ⊆ U → MapCPConvergenceOn S p (fun k => τ (φ k)) τinf)
    (hpt : ∀ x ∈ U, Tendsto (fun k => τ k x) atTop (𝓝 (τ₀ x))) : EqOn τinf τ₀ U := by
  intro x hx
  have h1 := tendsto_of_mapCPConvergenceOn
    (hconv {x} isCompact_singleton (singleton_subset_iff.2 hx)) (mem_singleton x)
  exact tendsto_nhds_unique h1 ((hpt x hx).comp hφ.tendsto_atTop)

end DifferentialGeometry.CheegerGromovCompactness.MetricIsometry
