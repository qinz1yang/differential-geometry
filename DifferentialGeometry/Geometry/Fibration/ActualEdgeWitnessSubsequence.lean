import DifferentialGeometry.Geometry.Fibration.ActualReplacementEdgeBall

/-!
# FDC02's subsequence with one witnessing edge index (the part free of the final map)

Blueprint `master207B.tex`, FDC02 (`thm:fibration-actual-compact-edge-piece`, B:7259–7263): "Let
`q_n ∈ M₂ ∩ X₂` converge in compact `M` to `q`. … After a subsequence, one selected index `i`
witnesses the base condition for every `q_n`." The witnessing itself (the base condition on
`π₂E(q_n)`) concerns the final map `E`; what is free of `E` is the pigeonhole over the FINITE set
of selected edge centres, along a convergent sequence.

* `exists_strictMono_eq_of_mem_finite_FDC1`: a sequence with values in a finite set is constant
  along a strictly increasing subsequence (value in the set).
* `fdc02_witness_subsequence_FDC1`: for `q_n → q` and witnessing edge centres `i_n` of the actual
  family, one centre `i` and a subsequence `φ` with `i_{φ n} = i` and `q_{φ n} → q`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **Pigeonhole along a sequence**: a sequence with values in a finite set `S` is constant, with
value in `S`, along a strictly increasing subsequence. -/
theorem exists_strictMono_eq_of_mem_finite_FDC1 {ι : Type*} {S : Set ι} (hS : S.Finite)
    {w : ℕ → ι} (hw : ∀ n, w n ∈ S) : ∃ i ∈ S, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, w (φ n) = i := by
  have hfreq : ∃ i ∈ S, ∃ᶠ n in atTop, w n = i := by
    by_contra hcon
    push Not at hcon
    have hev : ∀ᶠ n in atTop, ∀ i ∈ S, w n ≠ i := (eventually_all_finite hS).mpr hcon
    obtain ⟨n, hn⟩ := hev.exists
    exact hn (w n) (hw n) rfl
  obtain ⟨i, hi, hf⟩ := hfreq
  obtain ⟨φ, hφ, hφi⟩ := extraction_of_frequently_atTop hf
  exact ⟨i, hi, φ, hφ, hφi⟩

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}

/-- **FDC02's one witnessing index**: for a convergent sequence `q_n → q` with witnessing actual
edge centres `i_n`, some edge centre `i` and a subsequence `φ` have `i_{φ n} = i` for every `n`
and `q_{φ n} → q`. -/
theorem fdc02_witness_subsequence_FDC1
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    {qs : ℕ → X} {q : X} (hq : Tendsto qs atTop (𝓝 q)) {w : ℕ → X}
    (hw : ∀ n, w n ∈ L.edge.centres) :
    ∃ i ∈ L.edge.centres, ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ n, w (φ n) = i) ∧
      Tendsto (qs ∘ φ) atTop (𝓝 q) := by
  obtain ⟨i, hi, φ, hφ, hφi⟩ := exists_strictMono_eq_of_mem_finite_FDC1 L.edge.finite_centres hw
  exact ⟨i, hi, φ, hφ, hφi, hq.comp hφ.tendsto_atTop⟩

end DifferentialGeometry.Geometry.Collapse
