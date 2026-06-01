import DifferentialGeometry.Analysis.Laplacian.Operator.ChartLocalLaplacian
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity

/-!
# Per-chart interior `H²` regularity for chart-pulled smooth weak solutions

For a smooth Riemannian metric `g` on a closed (compact, boundaryless) smooth
manifold `M` and a chart point `α : M`, the previous layer (`ChartLocalLaplacian`)
packages the chart-pulled-back smooth function `chartPullback I α u : EuclN → ℝ`
as a smooth weak solution of a `SmoothEllipticBilinearForm` on
`Set.univ : Set EuclN` (provided the chart-pulled bilinear identity is supplied).

This file glues that packaging to the Euclidean interior `H²` regularity
theorem `h2_loc_smooth_solution` from `NirenbergH2Regularity.lean`. The
end product is a per-chart statement that, on any precompact open subdomain
`Ω''` of the chart-target image, the chart-pulled smooth function admits weak
`(i, k)`-second partials in `L²(Ω'')`, with a quantitative bound in terms of
the `H¹` data on a slightly enlarged neighborhood.

The result is stated in **hypothesis-bearing form**: the caller provides
the `IsSmoothWeakSolution` witness for `(B, chartPullback I α u, F̃)`, plus the
`L²`-locality of the right-hand side `F̃`. These hypotheses are exactly the
output of `chart_pulled_smooth_weak_solution_of_chartIdentity` (from H3) and a
local boundedness check for `F̃` on compact subsets, both of which are
discharged downstream by the manifold-side Voss-Weyl + chart-pulled volume
identity.

## Setting

Closed (compact, boundaryless) smooth Riemannian manifold setting:
`[I.Boundaryless]`, `[T2Space M]`, `[SigmaCompactSpace M]`, `[CompactSpace M]`.
The model fibre `E` is a finite-dimensional real inner-product space with
positive dimension (`[NeZero (Module.finrank ℝ E)]`).

## Main results

* `h2_loc_chart_pulled` — the per-chart interior `H²` regularity statement for
  any smooth weak solution `(B, w, F̃)` and any precompact open subdomain
  `Ω''` of the chart-target image. Provides existence, for every pair
  `(i, k) : Fin n × Fin n`, of a weak `k`-partial `g_{i,k}` of the classical
  `i`-partial `∂_i w` on `Ω''`, with `g_{i,k} ∈ L²(Ω'')` and a quantitative
  bound on `∫_{Ω''} g_{i,k}²` in terms of the `H¹` seminorm and `L²` norms on
  a slightly enlarged compact-closure neighborhood.

* `h2_loc_chart_pulled_manifold` — the manifold-level wrapper that takes the
  manifold-side smooth function `u : M → ℝ` (with chart-source-supported
  closed support), the bilinear form `B`, the `IsSmoothWeakSolution` witness,
  and a precompact open subdomain. The conclusion is the Euclidean
  `h2_loc_chart_pulled` statement applied to `chartPullback I α u`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ManifoldH2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBounds

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- **Per-chart interior `H²` regularity (Euclidean form).**

For a smooth elliptic bilinear form `B` on `Set.univ : Set EuclN`, a function
`w : EuclN → ℝ` that is a smooth weak solution of `B u = F̃` (in the sense
of `B.IsSmoothWeakSolution`), with `F̃` locally in `L²` on every
compact-closure open set, and a precompact open subdomain `Ω'' ⊆ EuclN`,
the function `w` admits, for every pair `(i, k) : Fin n × Fin n`, a weak
`k`-partial `g` of the classical `i`-partial `∂_i w` on `Ω''`. The function
`g` is in `L²(Ω'')`, and there is a slightly enlarged precompact open
neighborhood `Ω'` and a constant `C ≥ 0` such that
`∫_{Ω''} g² ≤ C · (∫_{Ω'} ∑_j (∂_j w)² + ∫_{Ω'} w² + ∫_{Ω'} F̃²)`.

This is the manifold-side packaging of `h2_loc_smooth_solution`: the only
input that is mathematically nontrivial is the smooth-weak-solution witness
`h_weak`, which in turn comes from H3. -/
theorem h2_loc_chart_pulled
    (B : SmoothEllipticBilinearForm (Module.finrank ℝ E)
      (Set.univ : Set EuclN))
    {w F : EuclN → ℝ}
    (h_weak : B.IsSmoothWeakSolution w F)
    (hF_l2_loc : ∀ {Ω' : Set EuclN}, IsCompact (closure Ω') →
      MemLp F 2 ((volume : Measure EuclN).restrict Ω'))
    {Ω'' : Set EuclN} (hΩ'' : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω'')) :
    ∀ i k : Fin (Module.finrank ℝ E), ∃ g : EuclN → ℝ,
      MemLp g 2 ((volume : Measure EuclN).restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g
        (fun y : EuclN => (fderiv ℝ w y) (EuclideanSpace.single i 1)) Ω'' ∧
      ∃ Ω' : Set EuclN, IsOpen Ω' ∧ closure Ω'' ⊆ Ω' ∧
        closure Ω' ⊆ (Set.univ : Set EuclN) ∧
        IsCompact (closure Ω') ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∫ x in Ω'', g x ^ 2 ∂(volume : Measure EuclN) ≤
            C * (∫ x in Ω',
                  ∑ j : Fin (Module.finrank ℝ E),
                    ((fderiv ℝ w x) (EuclideanSpace.single j 1))^2
                ∂(volume : Measure EuclN) +
              ∫ x in Ω', (w x)^2 ∂(volume : Measure EuclN) +
              ∫ x in Ω', (F x)^2 ∂(volume : Measure EuclN)) := by
  have h_room :
      Metric.cthickening 2 (closure Ω'') ⊆ (Set.univ : Set EuclN) := by
    intro y _; exact Set.mem_univ _
  have h_closure_in :
      closure Ω'' ⊆ (Set.univ : Set EuclN) := by
    intro y _; exact Set.mem_univ _
  obtain ⟨C, hC_nn, h_eng⟩ := h2_loc_smooth_solution
    (d := Module.finrank ℝ E)
    B hΩ'' hΩ''_compact_closure h_closure_in h_room
  intro i k
  obtain ⟨g, hg_memLp, hg_weak, Ω', hΩ'_open, hΩ''_in_Ω', hΩ'_in,
    hΩ'_compact, hbound⟩ := h_eng h_weak hF_l2_loc i k
  exact ⟨g, hg_memLp, hg_weak, Ω', hΩ'_open, hΩ''_in_Ω', hΩ'_in,
    hΩ'_compact, C, hC_nn, hbound⟩

omit [NeZero (Module.finrank ℝ E)] in
/-- A continuous function with compact support on `EuclN` is in `L²` on
every measurable subset (in particular, on any precompact open subset). -/
theorem memLp_two_continuous_compactSupport_restrict
    {f : EuclN → ℝ} (hf_cont : Continuous f) (hf_cs : HasCompactSupport f)
    (Ω' : Set EuclN) :
    MemLp f 2 ((volume : Measure EuclN).restrict Ω') := by
  have h_global : MemLp f 2 (volume : Measure EuclN) :=
    hf_cont.memLp_of_hasCompactSupport (μ := volume) (p := 2) hf_cs
  exact h_global.restrict _

/-- **Per-chart interior `H²` regularity for chart-pulled-back smooth
manifold functions.**

In the closed (compact, boundaryless) Riemannian manifold setting, the
chart-pulled-back smooth function `chartPullback I α u : EuclN → ℝ` (with
manifold-side smooth `u` and `tsupport u ⊆ chart source`) is `C^∞` on `EuclN`
by `chartPullback_contDiff` (from H3). Coupled with the smooth-weak-solution
hypothesis `B.IsSmoothWeakSolution (chartPullback I α u) F̃` produced by
`chart_pulled_smooth_weak_solution_of_chartIdentity` (from H3), and the
`L²`-locality of `F̃`, the standard Euclidean interior `H²` regularity
theorem `h2_loc_smooth_solution` gives the conclusion. -/
theorem h2_loc_chart_pulled_manifold
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {u : M → ℝ} (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (hu_cs : HasCompactSupport u)
    (hu_supp : tsupport u ⊆ (chartAt H α).source)
    (B : SmoothEllipticBilinearForm (Module.finrank ℝ E)
      (Set.univ : Set EuclN))
    {F : EuclN → ℝ}
    (h_weak : B.IsSmoothWeakSolution
      (chartPullback (I := I) α u) F)
    (hF_l2_loc : ∀ {Ω' : Set EuclN}, IsCompact (closure Ω') →
      MemLp F 2 ((volume : Measure EuclN).restrict Ω'))
    {Ω'' : Set EuclN} (hΩ'' : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω'')) :
    ∀ i k : Fin (Module.finrank ℝ E), ∃ g_ik : EuclN → ℝ,
      MemLp g_ik 2 ((volume : Measure EuclN).restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g_ik
        (fun y : EuclN => (fderiv ℝ (chartPullback (I := I) α u) y)
          (EuclideanSpace.single i 1)) Ω'' ∧
      ∃ Ω' : Set EuclN, IsOpen Ω' ∧ closure Ω'' ⊆ Ω' ∧
        closure Ω' ⊆ (Set.univ : Set EuclN) ∧
        IsCompact (closure Ω') ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∫ x in Ω'', g_ik x ^ 2 ∂(volume : Measure EuclN) ≤
            C * (∫ x in Ω',
                  ∑ j : Fin (Module.finrank ℝ E),
                    ((fderiv ℝ (chartPullback (I := I) α u) x)
                      (EuclideanSpace.single j 1))^2
                ∂(volume : Measure EuclN) +
              ∫ x in Ω', (chartPullback (I := I) α u x)^2
                ∂(volume : Measure EuclN) +
              ∫ x in Ω', (F x)^2 ∂(volume : Measure EuclN)) := by
  let _ := g
  let _ := hu_smooth
  let _ := hu_cs
  let _ := hu_supp
  exact h2_loc_chart_pulled (E := E)
    B h_weak hF_l2_loc hΩ'' hΩ''_compact_closure

end ManifoldH2
end Laplacian
end Analysis
end DifferentialGeometry
