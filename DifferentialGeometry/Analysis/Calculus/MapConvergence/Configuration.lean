import DifferentialGeometry.Analysis.Calculus.MapConvergence.Basic
import DifferentialGeometry.Topology.UniformConvergence

set_option autoImplicit false

noncomputable section
open Set Filter
namespace DifferentialGeometry.CheegerGromovCompactness

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem MapCInfConvergenceOnCompacts.eventually_configuration_pairs_mem
    {ι : Type*} [Fintype ι] {S : Set P}
    {configuration : ℕ → P → (ι → ℝ) × (ι → E)}
    {mu : P → ι → ℝ} {center : P → E}
    (hcfg : MapCInfConvergenceOnCompacts S configuration
      (fun p => (mu p, fun _ => center p)))
    {K : Set (P × E)} (hK : IsCompact K)
    (hfst : Set.MapsTo (fun q : P × E => q.1) K S)
    (hcenter : ContinuousOn center (Prod.fst '' K))
    {V : Set (E × E)} (hV : IsOpen V)
    (hlim : Set.MapsTo (fun q : P × E => (q.2, center q.1)) K V) :
    ∀ᶠ n in atTop, ∀ q ∈ K, ∀ gamma : ι,
      (q.2, (configuration n q.1).2 gamma) ∈ V := by
  have hKfst : IsCompact (Prod.fst '' K) :=
    hK.image_of_continuousOn continuous_fst.continuousOn
  have hKfstS : Prod.fst '' K ⊆ S := by
    rintro z ⟨q, hq, rfl⟩
    exact hfst hq
  have hKpair : IsCompact ((fun q : P × E => (q.2, center q.1)) '' K) := by
    apply hK.image_of_continuousOn
    exact continuous_snd.continuousOn.prodMk
      (hcenter.comp continuous_fst.continuousOn (fun q hq => ⟨q, hq, rfl⟩))
  have htu := uniformContinuous_snd.comp_tendstoUniformlyOn
    (tendstoUniformlyOn_of_cPConvergence (hcfg (Prod.fst '' K) hKfst hKfstS 0))
  have hpairs : TendstoUniformlyOn
      (fun n (q : P × E) (i : ι) => (q.2, (configuration n q.1).2 i))
      (fun q i => (q.2, center q.1)) atTop K := by
    rw [Metric.tendstoUniformlyOn_iff] at htu ⊢
    intro eps heps
    filter_upwards [htu eps heps] with n hn q hq
    apply (dist_pi_lt_iff heps).mpr
    intro i
    have hi := (dist_le_pi_dist (fun _ : ι => center q.1)
      (configuration n q.1).2 i).trans_lt (hn q.1 ⟨q, hq, rfl⟩)
    simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using hi
  have hmem := hpairs.eventually_forall_mapsTo_of_isCompact_image
    (fun _ => hKpair) (fun _ => hV) (fun _ => hlim)
  filter_upwards [hmem] with n hn q hq i
  exact hn i hq

end DifferentialGeometry.CheegerGromovCompactness
end
