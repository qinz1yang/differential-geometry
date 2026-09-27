import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Endpoint.CoordinateJets
import Mathlib.Topology.UniformSpace.UniformApproximation


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set Topology
open DifferentialGeometry.CheegerGromovCompactness
open scoped ContDiff

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem spatial_jet_bounds_of_eventual
    {U : Set E} (hU : IsOpen U) (f : ℕ → E → F)
    (hf : ∀ i, ContDiffOn ℝ (∞ : WithTop ℕ∞) (f i) U)
    (hbdd : ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ᶠ i in atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (f i) x‖ ≤ C) :
    ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ i : ℕ, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (f i) x‖ ≤ C := by
  classical
  intro r K hK hKU
  obtain ⟨C, hC⟩ := hbdd r K hK hKU
  obtain ⟨N, hN⟩ := eventually_atTop.mp hC
  have hind : ∀ i : ℕ, ∃ b : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (f i) x‖ ≤ b := by
    intro i
    have hc : ContinuousOn (fun x => ‖iteratedFDeriv ℝ r (f i) x‖) K := by
      intro x hx
      exact (((hf i).contDiffAt (hU.mem_nhds (hKU hx))).continuousAt_iteratedFDeriv
        (by exact_mod_cast le_top)).norm.continuousWithinAt
    obtain ⟨b, hb⟩ := hK.bddAbove_image hc
    exact ⟨b, fun x hx => hb (mem_image_of_mem _ hx)⟩
  choose b hb using hind
  obtain ⟨b0, hb0⟩ := ((Set.finite_Iio N).image b).bddAbove
  refine ⟨max C b0, fun i x hx => ?_⟩
  by_cases hi : N ≤ i
  · exact (hN i hi x hx).trans (le_max_left C b0)
  · exact (hb i x hx).trans
      ((hb0 (mem_image_of_mem b (Nat.lt_of_not_ge hi))).trans (le_max_right C b0))


theorem uniform_spatial_jets_on_compact_time_of_local_bounds
    {U : Set E} (hU : IsOpen U) {J : Set ℝ} (hJ : IsCompact J)
    (f : ℕ → ℝ → E → F) (f0 : ℝ → E → F)
    (hf : ∀ i t, t ∈ J → ContDiffOn ℝ (∞ : WithTop ℕ∞) (f i t) U)
    (hf0 : ∀ t ∈ J, ContDiffOn ℝ (∞ : WithTop ℕ∞) (f0 t) U)
    (hcont : ∀ x ∈ U, ContinuousOn (fun t => f0 t x) J)
    (hbdd : ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ᶠ i in atTop, ∀ t ∈ J, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ r (f i t) x‖ ≤ C)
    (hpoint : ∀ x ∈ U,
      TendstoUniformlyOn (fun i t => f i t x) (fun t => f0 t x) atTop J)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) (r : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i ≥ N, ∀ t ∈ J, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ r (f i t) x - iteratedFDeriv ℝ r (f0 t) x‖ ≤ ε := by
  classical
  have hfixed (t : ℝ) (ht : t ∈ J) :
      ∀ q : ℕ, ∀ L : Set E, IsCompact L → L ⊆ U →
        ∃ C : ℝ, ∀ i : ℕ, ∀ x ∈ L, ‖iteratedFDeriv ℝ q (f i t) x‖ ≤ C := by
    apply spatial_jet_bounds_of_eventual hU (fun i => f i t) (fun i => hf i t ht)
    intro q L hL hLU
    obtain ⟨C, hC⟩ := hbdd q L hL hLU
    exact ⟨C, hC.mono fun i hi x hx => hi t ht x hx⟩
  have hlimit : ∀ q : ℕ, ∀ L : Set E, IsCompact L → L ⊆ U →
      ∃ C : ℝ, ∀ t ∈ J, ∀ x ∈ L, ‖iteratedFDeriv ℝ q (f0 t) x‖ ≤ C := by
    intro q L hL hLU
    obtain ⟨C, hC⟩ := hbdd q L hL hLU
    refine ⟨C, fun t ht x hx => ?_⟩
    exact iteratedFDeriv_norm_le_of_pointwise_of_local_jet_bounds
      hU (fun i => f i t) (f0 t) (fun i => hf i t ht) (hf0 t ht) (hfixed t ht)
      (fun y hy => (hpoint y hy).tendsto_at ht) q (hLU hx)
      (hC.mono fun i hi => hi t ht x hx)
  intro ε hε
  by_contra hbad
  push Not at hbad
  choose k hk t ht x hx hbad using hbad
  have hkTop : Tendsto k atTop atTop := tendsto_atTop_mono hk tendsto_id
  obtain ⟨τ, hτ, σ, hσ, htime⟩ := hJ.tendsto_subseq ht
  have htimeJ : Tendsto (fun n => t (σ n)) atTop (𝓝[J] τ) :=
    tendsto_nhdsWithin_iff.mpr ⟨htime, Eventually.of_forall (fun n => ht (σ n))⟩
  have hindex : Tendsto (fun n => k (σ n)) atTop atTop := hkTop.comp hσ.tendsto_atTop
  have hsourceBounds : ∀ q : ℕ, ∀ L : Set E, IsCompact L → L ⊆ U →
      ∃ C : ℝ, ∀ n : ℕ, ∀ y ∈ L,
        ‖iteratedFDeriv ℝ q (f (k (σ n)) (t (σ n))) y‖ ≤ C := by
    apply spatial_jet_bounds_of_eventual hU _ (fun n => hf _ _ (ht (σ n)))
    intro q L hL hLU
    obtain ⟨C, hC⟩ := hbdd q L hL hLU
    exact ⟨C, (hindex.eventually hC).mono fun n hn y hy => hn _ (ht (σ n)) y hy⟩
  have hsourcePoint : ∀ y ∈ U,
      Tendsto (fun n => f (k (σ n)) (t (σ n)) y) atTop (𝓝 (f0 τ y)) := by
    intro y hy
    have hunif : TendstoUniformlyOn (fun n s => f (k (σ n)) s y)
        (fun s => f0 s y) atTop J :=
      fun V hV => hindex.eventually (hpoint y hy V hV)
    exact hunif.tendsto_comp (hcont y hy τ hτ) htimeJ
  have hsourceConv := mapCInfConvergenceOnCompacts_of_pointwise_of_local_jet_bounds
    hU (fun n => f (k (σ n)) (t (σ n))) (f0 τ)
    (fun n => hf _ _ (ht (σ n))) hsourceBounds hsourcePoint
  have hlimitConv := mapCInfConvergenceOnCompacts_of_pointwise_of_local_jet_bounds
    hU (fun n => f0 (t (σ n))) (f0 τ) (fun n => hf0 _ (ht (σ n)))
    (by
      intro q L hL hLU
      obtain ⟨C, hC⟩ := hlimit q L hL hLU
      exact ⟨C, fun n y hy => hC _ (ht (σ n)) y hy⟩)
    (fun y hy => (hcont y hy τ hτ).tendsto.comp htimeJ)
  have hsourceJets := hsourceConv.tendstoUniformlyOn_iteratedFDeriv hU hK hKU
    (fun n => hf _ _ (ht (σ n))) (hf0 τ hτ) r
  have hlimitJets := hlimitConv.tendstoUniformlyOn_iteratedFDeriv hU hK hKU
    (fun n => hf0 _ (ht (σ n))) (hf0 τ hτ) r
  rw [Metric.tendstoUniformlyOn_iff] at hsourceJets hlimitJets
  obtain ⟨n, hsn, hln⟩ :=
    ((hsourceJets (ε / 2) (by positivity)).and (hlimitJets (ε / 2) (by positivity))).exists
  have hsourceClose := hsn (x (σ n)) (hx (σ n))
  have hlimitClose := hln (x (σ n)) (hx (σ n))
  have hclose :
      ‖iteratedFDeriv ℝ r (f (k (σ n)) (t (σ n))) (x (σ n)) -
          iteratedFDeriv ℝ r (f0 (t (σ n))) (x (σ n))‖ < ε := by
    calc
      _ = dist (iteratedFDeriv ℝ r (f (k (σ n)) (t (σ n))) (x (σ n)))
          (iteratedFDeriv ℝ r (f0 (t (σ n))) (x (σ n))) := (dist_eq_norm _ _).symm
      _ ≤ dist (iteratedFDeriv ℝ r (f (k (σ n)) (t (σ n))) (x (σ n)))
          (iteratedFDeriv ℝ r (f0 τ) (x (σ n))) +
          dist (iteratedFDeriv ℝ r (f0 τ) (x (σ n)))
            (iteratedFDeriv ℝ r (f0 (t (σ n))) (x (σ n))) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (by simpa only [dist_comm] using hsourceClose) hlimitClose
      _ = ε := by ring
  exact (not_lt_of_ge hclose.le) (hbad (σ n))

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
