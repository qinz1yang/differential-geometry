import DifferentialGeometry.Geometry.Operator.TimeLaplacian
import DifferentialGeometry.Geometry.Operator.WithBoundary.VossWeyl

noncomputable section

open Filter Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Operator.WithBoundary

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

theorem hasDerivAt_Δ_g_with_boundary
    (g : SmoothRiemannianMetric I M) (f : ℝ → M → ℝ)
    (hfs : ∀ s, ContMDiff I 𝓘(ℝ, ℝ) ∞ (f s))
    (hfint : ∀ s, tsupport (f s) ⊆ I.interior M)
    {J : Set ℝ} (hJ : IsOpen J)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2) (J ×ˢ univ))
    {t : ℝ} (ht : t ∈ J) {f' : M → ℝ}
    (hf' : ContMDiff I 𝓘(ℝ, ℝ) ∞ f') (hf'int : tsupport f' ⊆ I.interior M)
    (hd : ∀ x, HasDerivAt (fun s => f s x) (f' x) t) (x : M) :
    HasDerivAt (fun s => ΔGWithBoundary (I := I) g (hfs s) (hfint s) x)
      (ΔGWithBoundary (I := I) g hf' hf'int x) t := by
  have hdeq : (fun w => deriv (fun s => f s w) t) = f' :=
    funext fun w => (hd w).deriv
  by_cases hx : x ∈ I.interior M
  · have hxi := extChartAt_mem_interior_target_of_isInteriorPoint (I := I) x
      (mem_chart_source H x) hx
    have h := hasDerivAt_chartVossWeylLaplacian g f hJ hf x ht x hxi
    rw [hdeq, ← voss_weyl_laplacian_with_boundary_formula g x hf' hf'int
      (mem_chart_source H x) hx] at h
    apply h.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun s =>
      voss_weyl_laplacian_with_boundary_formula g x (hfs s) (hfint s)
        (mem_chart_source H x) hx
  · have hz (s : ℝ) : ΔGWithBoundary (I := I) g (hfs s) (hfint s) x = 0 := by
      by_contra hne
      exact hx (hfint s (tsupport_Δ_g_with_boundary_subset g (hfs s) (hfint s)
        (subset_tsupport _ hne)))
    have hz' : ΔGWithBoundary (I := I) g hf' hf'int x = 0 := by
      by_contra hne
      exact hx (hf'int (tsupport_Δ_g_with_boundary_subset g hf' hf'int
        (subset_tsupport _ hne)))
    simpa only [hz, hz'] using (hasDerivAt_const t (0 : ℝ))

theorem continuousOn_Δ_g_with_boundary_prod
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (g : SmoothRiemannianMetric I M) (f : P → M → ℝ)
    (hfs : ∀ p, ContMDiff I 𝓘(ℝ, ℝ) ∞ (f p))
    (hfint : ∀ p, tsupport (f p) ⊆ I.interior M)
    {S : Set P} (hS : IsOpen S)
    (hf : ContMDiffOn (𝓘(ℝ, P).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : P × M => f p.1 p.2) (S ×ˢ univ))
    {K : Set M} (hK : IsClosed K) (hKi : K ⊆ I.interior M)
    (hfK : ∀ p ∈ S, tsupport (f p) ⊆ K) :
    ContinuousOn (fun p : P × M => ΔGWithBoundary (I := I) g
      (hfs p.1) (hfint p.1) p.2) (S ×ˢ univ) := by
  intro p hp
  apply ContinuousAt.continuousWithinAt
  by_cases hx : p.2 ∈ K
  · have hxi := extChartAt_mem_interior_target_of_isInteriorPoint (I := I) p.2
      (mem_chart_source H p.2) (hKi hx)
    have h := (scalarOnE_chartVossWeylLaplacian_contDiffOn_prod g f hS hf p.2).continuousOn
    have hc := h.continuousAt (x := (p.1, extChartAt I p.2 p.2)) ((hS.prod isOpen_interior).mem_nhds ⟨hp.1, hxi⟩)
    have hchart : ContinuousAt (fun r : P × M => (r.1, extChartAt I p.2 r.2)) p :=
      continuousAt_fst.prodMk ((continuousAt_extChartAt (I := I) p.2).comp continuousAt_snd)
    apply (hc.comp (f := fun r : P × M => (r.1, extChartAt I p.2 r.2))
      (x := p) hchart).congr_of_eventuallyEq
    filter_upwards [continuousAt_snd.eventually
        ((isOpen_extChartAt_source (I := I) p.2).mem_nhds (mem_extChartAt_source p.2)),
      continuousAt_snd.eventually ((I.isOpen_interior (n := ∞) (by simp)).mem_nhds (hKi hx))] with r hr hi
    simp only [Function.comp_apply]
    rw [scalarOnE_extChartAt p.2 _ hr]
    exact voss_weyl_laplacian_with_boundary_formula g p.2 (hfs r.1) (hfint r.1)
      (by rwa [extChartAt_source_eq_chartAt_source (I := I)] at hr) hi
  · apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [continuousAt_fst.eventually (hS.mem_nhds hp.1),
      continuousAt_snd.eventually (hK.isOpen_compl.mem_nhds hx)] with r hs hk
    by_contra hne
    exact hk (hfK r.1 hs (tsupport_Δ_g_with_boundary_subset g (hfs r.1) (hfint r.1)
      (subset_tsupport _ hne)))

end DifferentialGeometry.Geometry.Operator.WithBoundary
