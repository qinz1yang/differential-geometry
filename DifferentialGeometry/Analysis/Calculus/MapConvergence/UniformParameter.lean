import DifferentialGeometry.Analysis.Calculus.MapConvergence.Composition
import Mathlib.Topology.Sequences

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.CheegerGromovCompactness
open Filter Set
open scoped _root_.Topology ContDiff
variable {E F P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem mapCInfConvergenceOnCompacts_of_uniform_spatial_jets
    {U : Set E} (hU : IsOpen U) {J : Set P}
    (f : ℕ → P → E → F) (f₀ : P → E → F)
    (hf : ∀ n t, t ∈ J → ContDiffOn ℝ ∞ (f n t) U)
    (hf₀ : ∀ t ∈ J, ContDiffOn ℝ ∞ (f₀ t) U)
    (hunif : ∀ K : Set E, IsCompact K → K ⊆ U → ∀ r : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ r (f n t) y - iteratedFDeriv ℝ r (f₀ t) y‖ ≤ ε)
    (θ : ℕ → ℕ) (hθ : Tendsto θ atTop atTop) (τ : ℕ → P) (hτ : ∀ n, τ n ∈ J)
    {t : P} (ht : t ∈ J)
    (hlim : MapCInfConvergenceOnCompacts U (fun n => f₀ (τ n)) (f₀ t)) :
    MapCInfConvergenceOnCompacts U (fun n => f (θ n) (τ n)) (f₀ t) := by
  intro K hK hKU m
  apply mapCPConvergenceOn_of_tendstoUniformlyOn hU hKU
    (fun n => (hf (θ n) (τ n) (hτ n)).of_le (by exact_mod_cast le_top))
    ((hf₀ t ht).of_le (by exact_mod_cast le_top))
  intro r _hr
  have hL := hlim.tendstoUniformlyOn_iteratedFDeriv hU hK hKU
    (fun n => hf₀ (τ n) (hτ n)) (hf₀ t ht) r
  rw [Metric.tendstoUniformlyOn_iff] at hL ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hunif K hK hKU r (ε / 2) (by positivity)
  filter_upwards [hθ.eventually_ge_atTop N, hL (ε / 2) (by positivity)] with n hn hLn
  intro y hy
  calc
    _ ≤ dist (iteratedFDeriv ℝ r (f₀ t) y) (iteratedFDeriv ℝ r (f₀ (τ n)) y) +
        dist (iteratedFDeriv ℝ r (f₀ (τ n)) y) (iteratedFDeriv ℝ r (f (θ n) (τ n)) y) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le (hLn y hy)
      (by simpa only [dist_eq_norm, norm_sub_rev] using hN (θ n) hn (τ n) (hτ n) y hy)
    _ = ε := by ring

theorem uniform_spatial_jets_of_sequential_convergence [TopologicalSpace P]
    {U : Set E} (hU : IsOpen U) {J : Set P} (hJ : IsSeqCompact J)
    (f : ℕ → P → E → F) (f₀ : P → E → F)
    (hf : ∀ n t, t ∈ J → ContDiffOn ℝ ∞ (f n t) U)
    (hf₀ : ∀ t ∈ J, ContDiffOn ℝ ∞ (f₀ t) U)
    (hsource : ∀ (θ : ℕ → ℕ), Tendsto θ atTop atTop →
      ∀ (τ : ℕ → P), (∀ n, τ n ∈ J) → ∀ t ∈ J, Tendsto τ atTop (𝓝 t) →
        MapCInfConvergenceOnCompacts U (fun n => f (θ n) (τ n)) (f₀ t))
    (hlimit : ∀ (τ : ℕ → P), (∀ n, τ n ∈ J) →
      ∀ t ∈ J, Tendsto τ atTop (𝓝 t) →
        MapCInfConvergenceOnCompacts U (fun n => f₀ (τ n)) (f₀ t))
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) (r : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ r (f n t) y - iteratedFDeriv ℝ r (f₀ t) y‖ ≤ ε := by
  classical
  intro ε hε
  by_contra hbad
  push Not at hbad
  choose k hk τ hτ y hy hbad using hbad
  have hkTop : Tendsto k atTop atTop := tendsto_atTop_mono hk tendsto_id
  obtain ⟨t, ht, σ, hσ, htime⟩ := hJ hτ
  have hindex : Tendsto (fun n => k (σ n)) atTop atTop := hkTop.comp hσ.tendsto_atTop
  have hsourceConv := hsource (fun n => k (σ n)) hindex (fun n => τ (σ n))
    (fun n => hτ (σ n)) t ht htime
  have hlimitConv := hlimit (fun n => τ (σ n)) (fun n => hτ (σ n)) t ht htime
  have hsourceJets := hsourceConv.tendstoUniformlyOn_iteratedFDeriv hU hK hKU
    (fun n => hf (k (σ n)) (τ (σ n)) (hτ (σ n))) (hf₀ t ht) r
  have hlimitJets := hlimitConv.tendstoUniformlyOn_iteratedFDeriv hU hK hKU
    (fun n => hf₀ (τ (σ n)) (hτ (σ n))) (hf₀ t ht) r
  rw [Metric.tendstoUniformlyOn_iff] at hsourceJets hlimitJets
  obtain ⟨n, hsn, hln⟩ :=
    ((hsourceJets (ε / 2) (by positivity)).and (hlimitJets (ε / 2) (by positivity))).exists
  have hsclose := hsn (y (σ n)) (hy (σ n))
  have hlclose := hln (y (σ n)) (hy (σ n))
  have hclose : ‖iteratedFDeriv ℝ r (f (k (σ n)) (τ (σ n))) (y (σ n)) -
      iteratedFDeriv ℝ r (f₀ (τ (σ n))) (y (σ n))‖ < ε := by
    calc
      _ = dist (iteratedFDeriv ℝ r (f (k (σ n)) (τ (σ n))) (y (σ n)))
          (iteratedFDeriv ℝ r (f₀ (τ (σ n))) (y (σ n))) := (dist_eq_norm _ _).symm
      _ ≤ dist (iteratedFDeriv ℝ r (f (k (σ n)) (τ (σ n))) (y (σ n)))
          (iteratedFDeriv ℝ r (f₀ t) (y (σ n))) +
          dist (iteratedFDeriv ℝ r (f₀ t) (y (σ n)))
            (iteratedFDeriv ℝ r (f₀ (τ (σ n))) (y (σ n))) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (by simpa only [dist_comm] using hsclose) hlclose
      _ = ε := by ring
  exact (not_lt_of_ge hclose.le) (hbad (σ n))

end DifferentialGeometry.CheegerGromovCompactness
