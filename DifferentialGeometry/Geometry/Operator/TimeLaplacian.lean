import DifferentialGeometry.Analysis.Calculus.TimeJetCommute
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.TangentAction
import DifferentialGeometry.Geometry.Operator.HessianTraceChartGramRegularity

noncomputable section

open Filter Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Operator

open DifferentialGeometry.Analysis
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem hasDerivAt_chartVossWeylLaplacian
    (g : SmoothRiemannianMetric I M) (f : ℝ → M → ℝ)
    {J : Set ℝ} (hJ : IsOpen J)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2) (J ×ˢ univ))
    (α : M) {t : ℝ} (ht : t ∈ J) (x : M)
    (hxtarget : extChartAt I α x ∈ interior (extChartAt I α).target) :
    HasDerivAt (fun s : ℝ => chartVossWeylLaplacian (I := I) g α (f s) x)
      (chartVossWeylLaplacian (I := I) g α
        (fun w : M => deriv (fun s : ℝ => f s w) t) x) t := by
  classical
  have hΦ : ∀ y : E, y ∈ interior (extChartAt I α).target →
      ContDiffAt ℝ ∞
        (fun r : ℝ × E => scalarOnE (I := I) α (f r.1) r.2) (t, y) := by
    intro y hy
    exact ((scalarOnE_contDiffOn_prod α hf).mono (Set.prod_mono Subset.rfl
      interior_subset)).contDiffAt ((hJ.prod isOpen_interior).mem_nhds ⟨ht, hy⟩)
  have hpd : ∀ (j : Fin (Module.finrank ℝ E)) (y : E),
      y ∈ interior (extChartAt I α).target →
      HasDerivAt
        (fun s : ℝ => partialDeriv (E := E) j (scalarOnE (I := I) α (f s)) y)
        (partialDeriv (E := E) j (scalarOnE (I := I) α
          (fun w : M => deriv (fun s : ℝ => f s w) t)) y) t := by
    intro j y hy
    have hc := fderiv_deriv_hasDerivAt_comm
      (fun r : ℝ × E => scalarOnE (I := I) α (f r.1) r.2) t y
      (chartModelBasis E j) (hΦ y hy)
    have hc1 : HasDerivAt
        (fun s : ℝ => partialDeriv (E := E) j (scalarOnE (I := I) α (f s)) y)
        (fderiv ℝ (fun z : E => deriv (fun s : ℝ => scalarOnE (I := I) α (f s) z) t)
          y (chartModelBasis E j)) t := by
      rw [show
        (fun s : ℝ => partialDeriv (E := E) j (scalarOnE (I := I) α (f s)) y) =
          (fun s : ℝ => fderiv ℝ
            (fun z : E => f s ((extChartAt I α).symm z)) y (chartModelBasis E j)) by
              funext s
              rw [partialDeriv]
              congr 1]
      exact hc
    have hfun : (fun z : E => deriv (fun s : ℝ => scalarOnE (I := I) α (f s) z) t) =
        scalarOnE (I := I) α (fun w : M => deriv (fun s : ℝ => f s w) t) := by
      funext z
      rfl
    have hval : fderiv ℝ (fun z : E => deriv (fun s : ℝ => scalarOnE (I := I) α (f s) z) t)
          y (chartModelBasis E j) =
        partialDeriv (E := E) j (scalarOnE (I := I) α
          (fun w : M => deriv (fun s : ℝ => f s w) t)) y := by
      rw [hfun]
      rfl
    rw [hval] at hc1
    exact hc1
  have hcoeff : ∀ (i : Fin (Module.finrank ℝ E)) (y : E),
      y ∈ interior (extChartAt I α).target →
      HasDerivAt
        (fun s : ℝ => gradChartCoeffOnE (I := I) g α (f s) i y)
        (gradChartCoeffOnE (I := I) g α
          (fun w : M => deriv (fun s : ℝ => f s w) t) i y) t := by
    intro i y hy
    have hsum : ∀ j : Fin (Module.finrank ℝ E),
        HasDerivAt
          (fun s : ℝ => chartInvGramOnE (I := I) g α i j y *
            partialDeriv (E := E) j (scalarOnE (I := I) α (f s)) y)
          (chartInvGramOnE (I := I) g α i j y *
            partialDeriv (E := E) j (scalarOnE (I := I) α
              (fun w : M => deriv (fun s : ℝ => f s w) t)) y) t := by
        intro j
        exact (hpd j y hy).const_mul (chartInvGramOnE (I := I) g α i j y)
    have hsumall : HasDerivAt
        (fun s : ℝ => ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α i j y *
            partialDeriv (E := E) j (scalarOnE (I := I) α (f s)) y)
        (∑ j : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α i j y *
            partialDeriv (E := E) j (scalarOnE (I := I) α
              (fun w : M => deriv (fun s : ℝ => f s w) t)) y) t := by
      exact HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hsum j)
    simpa [gradChartCoeffOnE_def] using hsumall
  have hint : ∀ (i : Fin (Module.finrank ℝ E)) (y : E),
      y ∈ interior (extChartAt I α).target →
      HasDerivAt
        (fun s : ℝ => gradChartCoeffOnE (I := I) g α (f s) i y *
          chartDensityOnE (I := I) g α y)
        (gradChartCoeffOnE (I := I) g α
          (fun w : M => deriv (fun s : ℝ => f s w) t) i y *
          chartDensityOnE (I := I) g α y) t := by
    intro i y hy
    exact (hcoeff i y hy).mul_const (chartDensityOnE (I := I) g α y)
  have hpd_joint : ∀ (j : Fin (Module.finrank ℝ E)) (y : E),
      y ∈ interior (extChartAt I α).target →
      ContDiffAt ℝ ∞
        (fun p : ℝ × E => partialDeriv (E := E) j
          (fun z : E => scalarOnE (I := I) α (f p.1) z) p.2)
        (t, y) := by
    intro j y hy
    have hproj : ContDiffAt ℝ ∞ (fun q : (ℝ × E) × E => (q.1.1, q.2))
        ((t, y), y) := by
      exact contDiffAt_fst.fst.prodMk contDiffAt_snd
    have hf : ContDiffAt ℝ ∞ (Function.uncurry
        (fun (p : ℝ × E) => fun (z : E) => scalarOnE (I := I) α (f p.1) z))
        ((t, y), y) := by
      exact (hΦ y hy).comp ((t, y), y) hproj
    have hg : ContDiffAt ℝ ∞ (fun p : ℝ × E => p.2) (t, y) := contDiffAt_snd
    have hfd := ContDiffAt.fderiv
      (f := fun (p : ℝ × E) => fun (z : E) => scalarOnE (I := I) α (f p.1) z)
      (g := fun p : ℝ × E => p.2) hf hg (by simp)
    rw [show
      (fun p : ℝ × E => partialDeriv (E := E) j
        (fun z : E => scalarOnE (I := I) α (f p.1) z) p.2) =
        (ContinuousLinearMap.apply ℝ ℝ (chartModelBasis E j)) ∘
          (fun p : ℝ × E => fderiv ℝ
            (fun z : E => scalarOnE (I := I) α (f p.1) z) p.2) by rfl]
    exact ((ContinuousLinearMap.apply ℝ ℝ (chartModelBasis E j)).contDiff.contDiffAt.comp
      (t, y) hfd)
  have hΨ : ∀ (i : Fin (Module.finrank ℝ E)) (y : E),
      y ∈ interior (extChartAt I α).target →
      ContDiffAt ℝ ∞
        (fun p : ℝ × E => gradChartCoeffOnE (I := I) g α (f p.1) i p.2 *
          chartDensityOnE (I := I) g α p.2)
        (t, y) := by
    intro i y hy
    have hsum_cd : ∀ j : Fin (Module.finrank ℝ E),
        ContDiffAt ℝ ∞
          (fun p : ℝ × E => chartInvGramOnE (I := I) g α i j p.2 *
            partialDeriv (E := E) j (fun z : E => scalarOnE (I := I) α (f p.1) z) p.2)
          (t, y) := by
      intro j
      have hgram : ContDiffAt ℝ ∞ (fun p : ℝ × E => chartInvGramOnE (I := I) g α i j p.2)
          (t, y) := by
        change ContDiffAt ℝ ∞
          ((fun z : E => chartInvGramOnE (I := I) g α i j z) ∘
            (fun p : ℝ × E => p.2)) (t, y)
        refine ContDiffAt.comp (t, y) ?_ ?_
        · exact (chartInvGramOnE_contDiffOn (I := I) g α i j).contDiffAt
            (mem_interior_iff_mem_nhds.mp hy)
        · exact (contDiffAt_snd : ContDiffAt ℝ ∞ (fun p : ℝ × E => p.2) (t, y))
      exact hgram.mul (hpd_joint j y hy)
    have hsumall_cd : ContDiffAt ℝ ∞
        (fun p : ℝ × E => ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α i j p.2 *
            partialDeriv (E := E) j (fun z : E => scalarOnE (I := I) α (f p.1) z) p.2)
        (t, y) := by
      exact ContDiffAt.sum (s := Finset.univ) (fun j _ => hsum_cd j)
    have hρ : ContDiffAt ℝ ∞ (fun p : ℝ × E => chartDensityOnE (I := I) g α p.2)
        (t, y) := by
      change ContDiffAt ℝ ∞
        ((fun z : E => chartDensityOnE (I := I) g α z) ∘
          (fun p : ℝ × E => p.2)) (t, y)
      refine ContDiffAt.comp (t, y) ?_ ?_
      · exact (chartDensityOnE_contDiffOn (I := I) g α).contDiffAt
          (mem_interior_iff_mem_nhds.mp hy)
      · exact (contDiffAt_snd : ContDiffAt ℝ ∞ (fun p : ℝ × E => p.2) (t, y))
    have hprod_cd : ContDiffAt ℝ ∞
        (fun p : ℝ × E =>
          (∑ j : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α i j p.2 *
              partialDeriv (E := E) j (fun z : E => scalarOnE (I := I) α (f p.1) z) p.2) *
            chartDensityOnE (I := I) g α p.2)
        (t, y) := hsumall_cd.mul hρ
    rw [show
      (fun p : ℝ × E => gradChartCoeffOnE (I := I) g α (f p.1) i p.2 *
        chartDensityOnE (I := I) g α p.2) =
        (fun p : ℝ × E =>
          (∑ j : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α i j p.2 *
              partialDeriv (E := E) j
                (fun z : E => scalarOnE (I := I) α (f p.1) z) p.2) *
            chartDensityOnE (I := I) g α p.2) by
              funext p
              rw [gradChartCoeffOnE_def]]
    exact hprod_cd
  have hpartial : ∀ i : Fin (Module.finrank ℝ E),
      HasDerivAt
        (fun s : ℝ => partialDeriv (E := E) i
          (chartVossWeylIntegrand (I := I) g α (f s) i) ((extChartAt I α) x))
        (partialDeriv (E := E) i
          (chartVossWeylIntegrand (I := I) g α
            (fun w : M => deriv (fun s : ℝ => f s w) t) i) ((extChartAt I α) x)) t := by
    intro i
    have hy : (extChartAt I α) x ∈ interior (extChartAt I α).target := hxtarget
    have hc := fderiv_deriv_hasDerivAt_comm
      (fun p : ℝ × E => gradChartCoeffOnE (I := I) g α (f p.1) i p.2 *
        chartDensityOnE (I := I) g α p.2) t
      ((extChartAt I α) x) (chartModelBasis E i) (hΨ i ((extChartAt I α) x) hy)
    have hc1 : HasDerivAt
        (fun s : ℝ => partialDeriv (E := E) i
          (fun z : E => gradChartCoeffOnE (I := I) g α (f s) i z *
            chartDensityOnE (I := I) g α z) ((extChartAt I α) x))
        (fderiv ℝ (fun z : E => deriv (fun s : ℝ =>
          gradChartCoeffOnE (I := I) g α (f s) i z * chartDensityOnE (I := I) g α z) t)
          ((extChartAt I α) x) (chartModelBasis E i)) t := by
      simpa [partialDeriv] using hc
    have hfun : (fun z : E => deriv (fun s : ℝ =>
        gradChartCoeffOnE (I := I) g α (f s) i z * chartDensityOnE (I := I) g α z) t) =ᶠ[𝓝
          ((extChartAt I α) x)]
        fun z : E => gradChartCoeffOnE (I := I) g α
          (fun w : M => deriv (fun s : ℝ => f s w) t) i z * chartDensityOnE (I := I) g α z := by
      have hh : ∀ z : E, z ∈ interior (extChartAt I α).target →
          deriv (fun s : ℝ =>
            gradChartCoeffOnE (I := I) g α (f s) i z * chartDensityOnE (I := I) g α z) t =
            gradChartCoeffOnE (I := I) g α
              (fun w : M => deriv (fun s : ℝ => f s w) t) i z * chartDensityOnE (I := I) g α z := by
        intro z hz
        exact (hint i z hz).deriv
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨interior (extChartAt I α).target, ?_, ?_⟩
      · exact isOpen_interior.mem_nhds hxtarget
      · intro z hz
        exact hh z hz
    have hval2 : (fderiv ℝ (fun z : E => deriv (fun s : ℝ =>
          gradChartCoeffOnE (I := I) g α (f s) i z * chartDensityOnE (I := I) g α z) t)
          ((extChartAt I α) x)) (chartModelBasis E i) =
        partialDeriv (E := E) i
          (fun z : E => gradChartCoeffOnE (I := I) g α
            (fun w : M => deriv (fun s : ℝ => f s w) t) i z *
            chartDensityOnE (I := I) g α z) ((extChartAt I α) x) := by
      rw [Filter.EventuallyEq.fderiv_eq hfun]
      unfold partialDeriv
      rfl
    have hc1'' : HasDerivAt
        (fun s : ℝ => partialDeriv (E := E) i
          (fun z : E => gradChartCoeffOnE (I := I) g α (f s) i z *
            chartDensityOnE (I := I) g α z) ((extChartAt I α) x))
        (partialDeriv (E := E) i
          (fun z : E => gradChartCoeffOnE (I := I) g α
            (fun w : M => deriv (fun s : ℝ => f s w) t) i z *
            chartDensityOnE (I := I) g α z) ((extChartAt I α) x)) t := by
      change HasDerivAt
        (fun s : ℝ => partialDeriv (E := E) i
          (fun z : E => gradChartCoeffOnE (I := I) g α (f s) i z *
            chartDensityOnE (I := I) g α z) ((extChartAt I α) x))
        ((fderiv ℝ (fun z : E => gradChartCoeffOnE (I := I) g α
            (fun w : M => deriv (fun s : ℝ => f s w) t) i z *
            chartDensityOnE (I := I) g α z) ((extChartAt I α) x))
          (chartModelBasis E i)) t
      have hval2' : (fderiv ℝ (fun z : E => deriv (fun s : ℝ =>
            gradChartCoeffOnE (I := I) g α (f s) i z * chartDensityOnE (I := I) g α z) t)
            ((extChartAt I α) x)) (chartModelBasis E i) =
          (fderiv ℝ (fun z : E => gradChartCoeffOnE (I := I) g α
            (fun w : M => deriv (fun s : ℝ => f s w) t) i z *
            chartDensityOnE (I := I) g α z) ((extChartAt I α) x))
            (chartModelBasis E i) := by
        simpa [partialDeriv] using hval2
      rw [← hval2']
      exact hc1
    change HasDerivAt
      (fun s : ℝ => partialDeriv (E := E) i
        (fun z : E => gradChartCoeffOnE (I := I) g α (f s) i z *
          chartDensityOnE (I := I) g α z) ((extChartAt I α) x))
      (partialDeriv (E := E) i
        (fun z : E => gradChartCoeffOnE (I := I) g α
          (fun w : M => deriv (fun s : ℝ => f s w) t) i z *
          chartDensityOnE (I := I) g α z) ((extChartAt I α) x)) t
    exact hc1''
  have hsumall : HasDerivAt
      (fun s : ℝ => ∑ i : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i (chartVossWeylIntegrand (I := I) g α (f s) i)
          ((extChartAt I α) x))
      (∑ i : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i (chartVossWeylIntegrand (I := I) g α
          (fun w : M => deriv (fun s : ℝ => f s w) t) i) ((extChartAt I α) x)) t := by
    exact HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hpartial i)
  have hdiv : HasDerivAt
      (fun s : ℝ => (∑ i : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i (chartVossWeylIntegrand (I := I) g α (f s) i)
          ((extChartAt I α) x)) / chartDensity (I := I) g α x)
      ((∑ i : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i (chartVossWeylIntegrand (I := I) g α
          (fun w : M => deriv (fun s : ℝ => f s w) t) i) ((extChartAt I α) x)) /
        chartDensity (I := I) g α x) t := by
    exact hsumall.div_const (chartDensity (I := I) g α x)
  have hgoal : HasDerivAt
      (fun s : ℝ => chartVossWeylLaplacian (I := I) g α (f s) x)
      (chartVossWeylLaplacian (I := I) g α
        (fun w : M => deriv (fun s : ℝ => f s w) t) x) t := by
    simpa [chartVossWeylLaplacian_def, chartVossWeylIntegrand_def] using hdiv
  exact hgoal

end DifferentialGeometry.Geometry.Operator
