import DifferentialGeometry.Topology.Morse.EmbeddingNaturality
import DifferentialGeometry.Topology.Morse.Naturality
import DifferentialGeometry.Topology.Morse.ConstantGerm

open Set Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Morse

variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H H' : Type} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {M N : Type} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N]
  {e f : M → N} {h : N → ℝ} {D : Set M}

theorem criticalPoints_comp_diffeomorph_replacement_eq
    [IsManifold J ∞ N]
    (he : Manifold.IsSmoothEmbedding I J ∞ e) (Φ : Diffeomorph J J N N ∞)
    (hD : IsClosed D) (hfix : EqOn f e Dᶜ)
    (himage : Φ '' range e = range e)
    (hΦfix : ∀ x, IsCriticalPointAt I (h ∘ e) x → Φ (e x) = e x)
    (hshift : ∀ x ∈ D, ∃ a : ℝ,
      (h ∘ Φ ∘ f) =ᶠ[𝓝 x] (fun y => h (f y) + a)) :
    criticalPoints I (h ∘ Φ ∘ f) = criticalPoints I (h ∘ f) := by
  have hcrit := criticalPoints_comp_diffeomorph_comp_eq_of_fixed he Φ (by simp) h
    himage hΦfix
  ext x
  change IsCriticalPointAt I (h ∘ Φ ∘ f) x ↔ IsCriticalPointAt I (h ∘ f) x
  by_cases hx : x ∈ D
  · obtain ⟨a, ha⟩ := hshift x hx
    exact (isCriticalPointAt_congr_of_eventuallyEq ha).trans
      (isCriticalPointAt_add_const_iff (h ∘ f) a x)
  · have heq : f =ᶠ[𝓝 x] e :=
      Filter.eventuallyEq_of_mem (hD.isOpen_compl.mem_nhds hx) hfix
    have hcritx : IsCriticalPointAt I (h ∘ Φ ∘ e) x ↔
        IsCriticalPointAt I (h ∘ e) x := Set.ext_iff.mp hcrit x
    exact (isCriticalPointAt_congr_of_eventuallyEq (heq.fun_comp (h ∘ Φ))).trans
      (hcritx.trans (isCriticalPointAt_congr_of_eventuallyEq (heq.fun_comp h)).symm)

theorem exists_eventuallyEq_add_const_comp_diffeomorph_replacement
    (Φ : Diffeomorph J J N N ∞) (hD : IsClosed D) (hfix : EqOn f e Dᶜ)
    (hΦnear : ∀ x, IsCriticalPointAt I (h ∘ e) x → (Φ ∘ e) =ᶠ[𝓝 x] e)
    (hshift : ∀ x ∈ D, ∃ a : ℝ,
      (h ∘ Φ ∘ f) =ᶠ[𝓝 x] (fun y => h (f y) + a))
    {x : M} (hx : IsCriticalPointAt I (h ∘ f) x) :
    ∃ a : ℝ, (h ∘ Φ ∘ f) =ᶠ[𝓝 x] (fun y => h (f y) + a) := by
  by_cases hxD : x ∈ D
  · exact hshift x hxD
  · have heq : f =ᶠ[𝓝 x] e :=
      Filter.eventuallyEq_of_mem (hD.isOpen_compl.mem_nhds hxD) hfix
    have hc := (isCriticalPointAt_congr_of_eventuallyEq (heq.fun_comp h)).mp hx
    refine ⟨0, ?_⟩
    have hh := (heq.fun_comp (h ∘ Φ)).trans
      (((hΦnear x hc).fun_comp h).trans (heq.fun_comp h).symm)
    simpa only [add_zero, Function.comp_def] using hh

theorem chartHessianAt_comp_diffeomorph_replacement_eq
    [I.Boundaryless] [IsManifold I ∞ M]
    (Φ : Diffeomorph J J N N ∞) (hD : IsClosed D) (hfix : EqOn f e Dᶜ)
    (hΦnear : ∀ x, IsCriticalPointAt I (h ∘ e) x → (Φ ∘ e) =ᶠ[𝓝 x] e)
    (hshift : ∀ x ∈ D, ∃ a : ℝ,
      (h ∘ Φ ∘ f) =ᶠ[𝓝 x] (fun y => h (f y) + a))
    {x : M} (hx : IsCriticalPointAt I (h ∘ f) x) :
    chartHessianAt (fun y => h (Φ (f ((extChartAt I x).symm y)))) (extChartAt I x x) =
      chartHessianAt (fun y => h (f ((extChartAt I x).symm y))) (extChartAt I x x) := by
  obtain ⟨a, ha⟩ := exists_eventuallyEq_add_const_comp_diffeomorph_replacement
    Φ hD hfix hΦnear hshift hx
  exact DifferentialGeometry.Morse.chartHessianAt_eq_of_eventuallyEq_add_const
    (I := I) BoundarylessManifold.isInteriorPoint ha

end DifferentialGeometry.Topology.Morse
