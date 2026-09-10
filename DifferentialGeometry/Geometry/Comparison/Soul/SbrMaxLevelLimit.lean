import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.Basic

set_option autoImplicit false
noncomputable section

open Filter Set
open scoped Topology

namespace DifferentialGeometry.Geometry.Topology

variable {M : Type*} [MetricSpace M]

theorem exists_level_left_limit_of_dist_antitone
    {C : Set M} (hC : IsCompact C) (F : M → ℝ) (hF : ContinuousOn F C)
    (eta : ℝ → M) {a m : ℝ} (ham : a < m)
    (hetaC : ∀ s ∈ Ico a m, eta s ∈ C)
    (hlevel : ∀ s ∈ Ico a m, F (eta s) = s)
    (hdist : ∀ q ∈ C, F q = m → AntitoneOn (fun s => dist (eta s) q) (Ico a m)) :
    ∃ q ∈ C, F q = m ∧ Tendsto eta (𝓝[<] m) (𝓝 q) := by
  obtain ⟨u, _hmono, hu, hulim⟩ := exists_seq_strictMono_tendsto' ham
  have huIco (n : ℕ) : u n ∈ Ico a m := ⟨(hu n).1.le, (hu n).2⟩
  obtain ⟨q, hqC, phi, hphi, hq⟩ :=
    hC.tendsto_subseq (fun n => hetaC (u n) (huIco n))
  have hqWithin : Tendsto (fun n => eta (u (phi n))) atTop (𝓝[C] q) :=
    tendsto_nhdsWithin_iff.mpr ⟨hq,
      Eventually.of_forall (fun n => hetaC (u (phi n)) (huIco (phi n)))⟩
  have hFq : Tendsto (fun n => F (eta (u (phi n)))) atTop (𝓝 (F q)) :=
    Filter.Tendsto.comp (hF q hqC) hqWithin
  have hFq' : Tendsto (u ∘ phi) atTop (𝓝 (F q)) := by
    have heq : (fun n => F (eta (u (phi n)))) = u ∘ phi := by
      funext n
      exact hlevel (u (phi n)) (huIco (phi n))
    rwa [heq] at hFq
  have hqm : F q = m := tendsto_nhds_unique hFq' (hulim.comp hphi.tendsto_atTop)
  refine ⟨q, hqC, hqm, ?_⟩
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  have hnear : ∀ᶠ n in atTop, dist (eta (u (phi n))) q < eps :=
    Metric.tendsto_nhds.mp hq eps heps
  obtain ⟨n, hn⟩ := hnear.exists
  filter_upwards [Ioo_mem_nhdsLT (hu (phi n)).2] with s hs
  have hsIco : s ∈ Ico a m :=
    ⟨(hu (phi n)).1.le.trans hs.1.le, hs.2⟩
  exact ((hdist q hqC hqm) (huIco (phi n)) hsIco hs.1.le).trans_lt hn

theorem exists_continuous_level_extension_of_dist_antitone
    {C : Set M} (hC : IsCompact C) (F : M → ℝ) (hF : ContinuousOn F C)
    (eta : ℝ → M) {a m : ℝ} (ham : a < m)
    (heta : ContinuousOn eta (Ico a m))
    (hetaC : ∀ s ∈ Ico a m, eta s ∈ C)
    (hlevel : ∀ s ∈ Ico a m, F (eta s) = s)
    (hdist : ∀ q ∈ C, F q = m → AntitoneOn (fun s => dist (eta s) q) (Ico a m)) :
    ∃ q ∈ C, F q = m ∧
      let etaBar := Function.update eta m q
      ContinuousOn etaBar (Icc a m) ∧
      EqOn etaBar eta (Ico a m) ∧ etaBar m = q ∧
      ∀ s ∈ Icc a m, etaBar s ∈ C ∧ F (etaBar s) = s := by
  obtain ⟨q, hqC, hqm, hlim⟩ :=
    exists_level_left_limit_of_dist_antitone hC F hF eta ham hetaC hlevel hdist
  have hcont : ContinuousOn (Function.update eta m q) (Icc a m) := by
    apply continuousOn_update_iff.mpr
    constructor
    · simpa only [Icc_sdiff_right] using heta
    · intro _hm
      rw [Icc_sdiff_right]
      exact hlim.mono_left (nhdsWithin_mono m Ico_subset_Iio_self)
  refine ⟨q, hqC, hqm, hcont, ?_, Function.update_self m q eta, ?_⟩
  · intro s hs
    exact Function.update_of_ne hs.2.ne q eta
  · intro s hs
    rcases eq_or_lt_of_le hs.2 with rfl | hsm
    · simpa only [Function.update_self] using And.intro hqC hqm
    · rw [Function.update_of_ne hsm.ne]
      exact ⟨hetaC s ⟨hs.1, hsm⟩, hlevel s ⟨hs.1, hsm⟩⟩

end DifferentialGeometry.Geometry.Topology
