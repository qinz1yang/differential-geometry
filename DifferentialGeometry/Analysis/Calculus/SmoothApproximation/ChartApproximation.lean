import DifferentialGeometry.Analysis.Calculus.SmoothApproximation.FiniteSupported
import DifferentialGeometry.Analysis.Calculus.SmoothApproximation.ChartTransport
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
noncomputable section
open Set Function Filter
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis

theorem exists_smooth_chart_approx_with_original_finite_jets
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (e : OpenPartialHomeomorph E F) (k : ℕ)
    (he : ContDiffOn ℝ k e e.source)
    {f : F → G} (hf : ContDiff ℝ k f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ e.target) :
    ∃ K : Set F, IsCompact K ∧ K ⊆ e.target ∧ tsupport f ⊆ K ∧
      ∃ g : ℕ → F → G, (∀ n, ContDiff ℝ ∞ (g n)) ∧
        (∀ n, tsupport (g n) ⊆ K) ∧
        (∀ n, ContDiff ℝ k (e.source.indicator (g n ∘ e))) ∧
        ContDiff ℝ k (e.source.indicator (f ∘ e)) ∧
        (∀ n, tsupport (e.source.indicator (g n ∘ e)) ⊆ e.symm '' K) ∧
        tsupport (e.source.indicator (f ∘ e)) ⊆ e.symm '' K ∧
        ∀ j, j ≤ k → TendstoUniformly
          (fun n => iteratedFDeriv ℝ j (e.source.indicator (g n ∘ e)))
          (iteratedFDeriv ℝ j (e.source.indicator (f ∘ e))) atTop := by
  obtain ⟨K, hK, hKt, hfK, g, hg, hgK, hconv⟩ :=
    exists_smooth_approx_supported_in_open_of_contDiff k hf hfc e.open_target hfs
  have hgk (n : ℕ) : ContDiff ℝ k (g n) := (hg n).of_le (by exact_mod_cast le_top)
  have hmapconv (S : Set F) :
      CheegerGromovCompactness.MapCPConvergenceOn S k g f :=
    CheegerGromovCompactness.mapCPConvergenceOn_of_tendstoUniformly (p := k) hgk hf
      (fun j hj => (hconv j hj).tendstoUniformlyOn)
  exact ⟨K, hK, hKt, hfK, g, hg, hgK,
    finite_jets_zero_extended_comp_converge_uniformly e k he hK hKt
      (fun n => (hgk n).contDiffOn) hf.contDiffOn hgK hfK
      (fun S _ _ => hmapconv S)⟩

theorem exists_smooth_chart_approx_with_original_pointwise_finite_jets
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (e : OpenPartialHomeomorph E F) (k : ℕ)
    (he : ContDiffOn ℝ k e e.source)
    {f : F → G} (hf : ContDiff ℝ k f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ e.target)
    {ε : E → ℝ} (hε : ContinuousOn ε e.source)
    (hεpos : ∀ x ∈ e.source, 0 < ε x) :
    ∃ g : F → G, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ e.target ∧
      ContDiff ℝ k (e.source.indicator (g ∘ e)) ∧
      HasCompactSupport (e.source.indicator (g ∘ e)) ∧
      tsupport (e.source.indicator (g ∘ e)) ⊆ e.source ∧
      ∀ j, j ≤ k → ∀ x ∈ e.source,
        ‖iteratedFDeriv ℝ j (e.source.indicator (g ∘ e)) x -
          iteratedFDeriv ℝ j (e.source.indicator (f ∘ e)) x‖ < ε x := by
  obtain ⟨K, hK, hKt, _, g, hg, hgK, hgreg, _, hgs, hfs', hconv⟩ :=
    exists_smooth_chart_approx_with_original_finite_jets e k he hf hfc hfs
  let L : Set E := e.symm '' K
  have hL : IsCompact L :=
    hK.image_of_continuousOn (e.continuousOn_invFun.mono hKt)
  have hLs : L ⊆ e.source := by
    rintro x ⟨y, hy, rfl⟩
    exact e.map_target (hKt hy)
  obtain ⟨δ, hδ, hδε⟩ :=
    hL.exists_forall_le' (hε.mono hLs) (fun x hx => hεpos x (hLs hx))
  have hall : ∀ᶠ n in atTop, ∀ j : Fin (k + 1), ∀ x : E,
      dist (iteratedFDeriv ℝ j.val (e.source.indicator (f ∘ e)) x)
        (iteratedFDeriv ℝ j.val (e.source.indicator (g n ∘ e)) x) < δ := by
    apply Filter.eventually_all.mpr
    intro j
    exact Metric.tendstoUniformly_iff.mp (hconv j.val (Nat.le_of_lt_succ j.isLt)) δ hδ
  obtain ⟨n, hn⟩ := hall.exists
  refine ⟨g n, hg n, hK.of_isClosed_subset (isClosed_tsupport _) (hgK n),
    (hgK n).trans hKt, hgreg n,
    hL.of_isClosed_subset (isClosed_tsupport _) (hgs n), (hgs n).trans hLs, ?_⟩
  intro j hj x hxs
  by_cases hx : x ∈ L
  · have hjx := hn ⟨j, Nat.lt_succ_of_le hj⟩ x
    have hlt : ‖iteratedFDeriv ℝ j (e.source.indicator (g n ∘ e)) x -
        iteratedFDeriv ℝ j (e.source.indicator (f ∘ e)) x‖ < δ := by
      rw [← dist_eq_norm_sub, dist_comm]
      exact hjx
    exact hlt.trans_le (hδε x hx)
  · have hz : iteratedFDeriv ℝ j (e.source.indicator (g n ∘ e)) x = 0 := by
      by_contra h
      exact hx (hgs n (support_iteratedFDeriv_subset j h))
    have hz₀ : iteratedFDeriv ℝ j (e.source.indicator (f ∘ e)) x = 0 := by
      by_contra h
      exact hx (hfs' (support_iteratedFDeriv_subset j h))
    simpa only [hz, hz₀, sub_self, norm_zero] using hεpos x hxs

end DifferentialGeometry.Analysis
