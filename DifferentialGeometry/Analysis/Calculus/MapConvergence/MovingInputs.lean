import DifferentialGeometry.Analysis.Calculus.MapConvergence.Basic
import DifferentialGeometry.Topology.UniformConvergence

open Filter Set

namespace DifferentialGeometry.CheegerGromovCompactness

theorem MapCInfConvergenceOnCompacts.eventually_dist_comp_lt
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {U K : Set E} {V L : Set F}
    {A : ℕ → F → G} {Ainf : F → G} {B : ℕ → E → F} {Binf : E → F}
    (hA : MapCInfConvergenceOnCompacts V A Ainf)
    (hB : MapCInfConvergenceOnCompacts U B Binf)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hL : IsCompact L) (hLV : L ⊆ V)
    (hAinf : ContinuousOn Ainf L)
    (hmap : ∀ᶠ k in atTop, MapsTo (B k) K L)
    (hmapInf : MapsTo Binf K L) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x ∈ K, dist (A k (B k x)) (Ainf (Binf x)) < ε := by
  have hAu := tendstoUniformlyOn_of_cPConvergence (hA.cPConvergenceOn hL hLV 0)
  have hBu := tendstoUniformlyOn_of_cPConvergence (hB.cPConvergenceOn hK hKU 0)
  have hcomp := hAu.comp_of_eventually_mapsTo
    (hL.uniformContinuousOn_of_continuous hAinf) hBu hmap hmapInf
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hcomp) ε hε] with k hk x hx
  simpa only [dist_comm] using hk x hx

end DifferentialGeometry.CheegerGromovCompactness
