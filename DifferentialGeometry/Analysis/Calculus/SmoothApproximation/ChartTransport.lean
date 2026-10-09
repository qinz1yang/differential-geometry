import DifferentialGeometry.Analysis.Calculus.MapConvergence.FiniteComposition
import DifferentialGeometry.Analysis.Calculus.ContDiff.Support
import Mathlib.Topology.OpenPartialHomeomorph.Basic

set_option autoImplicit false
noncomputable section
open Set Function Filter
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis

private theorem tsupport_indicator_comp_subset_image
    {E F G : Type*} [TopologicalSpace E] [T2Space E]
    [TopologicalSpace F] [Zero G]
    (e : OpenPartialHomeomorph E F) {K : Set F}
    (hK : IsCompact K) (hKt : K ⊆ e.target)
    {f : F → G} (hfs : tsupport f ⊆ K) :
    tsupport (e.source.indicator (f ∘ e)) ⊆ e.symm '' K := by
  apply closure_minimal _
    (hK.image_of_continuousOn (e.continuousOn_invFun.mono hKt)).isClosed
  intro x hx
  by_cases hxs : x ∈ e.source
  · have hx' : f (e x) ≠ 0 := by
      simpa only [mem_support, indicator_of_mem hxs, comp_apply] using hx
    exact ⟨e x, hfs (subset_tsupport f hx'), e.left_inv hxs⟩
  · exact (hx (indicator_of_notMem hxs _)).elim

theorem finite_jets_zero_extended_comp_converge_uniformly
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (e : OpenPartialHomeomorph E F) (p : ℕ)
    (he : ContDiffOn ℝ (p : ℕ∞) e e.source)
    {K : Set F} (hK : IsCompact K) (hKt : K ⊆ e.target)
    {f : ℕ → F → G} {f₀ : F → G}
    (hf : ∀ n, ContDiffOn ℝ (p : ℕ∞) (f n) e.target)
    (hf₀ : ContDiffOn ℝ (p : ℕ∞) f₀ e.target)
    (hfs : ∀ n, tsupport (f n) ⊆ K) (hf₀s : tsupport f₀ ⊆ K)
    (hconv : ∀ S : Set F, IsCompact S → S ⊆ e.target →
      CheegerGromovCompactness.MapCPConvergenceOn S p f f₀) :
    (∀ n, ContDiff ℝ (p : ℕ∞) (e.source.indicator (f n ∘ e))) ∧
      ContDiff ℝ (p : ℕ∞) (e.source.indicator (f₀ ∘ e)) ∧
      (∀ n, tsupport (e.source.indicator (f n ∘ e)) ⊆ e.symm '' K) ∧
      tsupport (e.source.indicator (f₀ ∘ e)) ⊆ e.symm '' K ∧
      ∀ j, j ≤ p → TendstoUniformly
        (fun n => iteratedFDeriv ℝ j (e.source.indicator (f n ∘ e)))
        (iteratedFDeriv ℝ j (e.source.indicator (f₀ ∘ e))) atTop := by
  classical
  let L : Set E := e.symm '' K
  have hL : IsCompact L :=
    hK.image_of_continuousOn (e.continuousOn_invFun.mono hKt)
  have hLs : L ⊆ e.source := by
    rintro x ⟨y, hy, rfl⟩
    exact e.map_target (hKt hy)
  have hsupport (n : ℕ) : tsupport (e.source.indicator (f n ∘ e)) ⊆ L :=
    tsupport_indicator_comp_subset_image e hK hKt (hfs n)
  have hsupport₀ : tsupport (e.source.indicator (f₀ ∘ e)) ⊆ L :=
    tsupport_indicator_comp_subset_image e hK hKt hf₀s
  have hcomp (n : ℕ) : ContDiffOn ℝ (p : ℕ∞) (f n ∘ e) e.source :=
    (hf n).comp he e.mapsTo
  have hcomp₀ : ContDiffOn ℝ (p : ℕ∞) (f₀ ∘ e) e.source :=
    hf₀.comp he e.mapsTo
  have hregular {a : F → G}
      (ha : ContDiffOn ℝ (p : ℕ∞) (a ∘ e) e.source)
      (hs : tsupport (e.source.indicator (a ∘ e)) ⊆ L) :
      ContDiff ℝ (p : ℕ∞) (e.source.indicator (a ∘ e)) :=
    (ha.congr (fun x hx => indicator_of_mem hx _)).contDiff_of_tsupport_subset
      e.open_source (hs.trans hLs)
  refine ⟨fun n => hregular (hcomp n) (hsupport n),
    hregular hcomp₀ hsupport₀, hsupport, hsupport₀, ?_⟩
  have hfixed : CheegerGromovCompactness.MapCPConvergenceOn L p
      (fun _ : ℕ => (e : E → F)) e :=
    CheegerGromovCompactness.mapCInfConvergence_const (U := e.source) (e : E → F) L hL hLs p
  have hcompose := hfixed.comp_finite e.open_source e.open_target hL hLs
    hconv (fun _ => he) he hf hf₀ e.mapsTo (fun _ => e.mapsTo)
  have hjet_eq (a : F → G) (j : ℕ) {x : E} (hx : x ∈ e.source) :
      iteratedFDeriv ℝ j (e.source.indicator (a ∘ e)) x =
        iteratedFDeriv ℝ j (a ∘ e) x := by
    have hh : e.source.indicator (a ∘ e) =ᶠ[𝓝 x] a ∘ e := by
      filter_upwards [e.open_source.mem_nhds hx] with y hy
      exact indicator_of_mem hy _
    exact (hh.iteratedFDeriv ℝ j).eq_of_nhds
  intro j hj
  have hlocal := hcompose.tendstoUniformlyOn_iteratedFDeriv e.open_source hLs
    hcomp hcomp₀ hj
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlocal ε hε] with n hn x
  by_cases hx : x ∈ L
  · rw [hjet_eq f₀ j (hLs hx), hjet_eq (f n) j (hLs hx)]
    exact hn x hx
  · have hz : iteratedFDeriv ℝ j (e.source.indicator (f n ∘ e)) x = 0 := by
      by_contra h
      exact hx (hsupport n (support_iteratedFDeriv_subset j h))
    have hz₀ : iteratedFDeriv ℝ j (e.source.indicator (f₀ ∘ e)) x = 0 := by
      by_contra h
      exact hx (hsupport₀ (support_iteratedFDeriv_subset j h))
    simpa only [hz, hz₀, dist_self] using hε

end DifferentialGeometry.Analysis
