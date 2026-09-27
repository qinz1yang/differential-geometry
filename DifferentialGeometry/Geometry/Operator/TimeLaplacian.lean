import DifferentialGeometry.Analysis.Calculus.TimeJet.Commutation
import DifferentialGeometry.Geometry.Operator.DirectionalDerivative
import DifferentialGeometry.Geometry.Operator.Hessian.Trace.ChartGramRegularity

noncomputable section

open Filter Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Operator

open DifferentialGeometry.Analysis
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem chartVossWeylIntegrand_contDiffOn_prod
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (g : SmoothRiemannianMetric I M) (f : P → M → ℝ)
    {S : Set P} (hS : IsOpen S)
    (hf : ContMDiffOn (𝓘(ℝ, P).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : P × M => f p.1 p.2) (S ×ˢ univ))
    (α : M) (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun p : P × E => chartVossWeylIntegrand (I := I) g α (f p.1) i p.2)
      (S ×ˢ interior (extChartAt I α).target) := by
  rintro ⟨p₀, y₀⟩ ⟨hp₀, hy₀⟩
  classical
  have hΦ : ∀ y : E, y ∈ interior (extChartAt I α).target →
      ContDiffAt ℝ ∞
        (fun p : P × E => scalarOnE (I := I) α (f p.1) p.2) (p₀, y) := by
    intro y hy
    exact ((scalarOnE_contDiffOn_prod α hf).mono (Set.prod_mono Subset.rfl
      interior_subset)).contDiffAt ((hS.prod isOpen_interior).mem_nhds ⟨hp₀, hy⟩)
  have hpd : ∀ (i : Fin (Module.finrank ℝ E)) (y : E),
      y ∈ interior (extChartAt I α).target →
      ContDiffAt ℝ ∞
        (fun p : P × E => partialDeriv (E := E) i
          (fun z : E => scalarOnE (I := I) α (f p.1) z) p.2)
        (p₀, y) := by
    intro i y hy
    have hproj : ContDiffAt ℝ ∞ (fun q : (P × E) × E => (q.1.1, q.2)) ((p₀, y), y) := by
      exact contDiffAt_fst.fst.prodMk contDiffAt_snd
    have hf' : ContDiffAt ℝ ∞ (Function.uncurry
        (fun (p : P × E) => fun (z : E) => scalarOnE (I := I) α (f p.1) z))
        ((p₀, y), y) := by
      exact (hΦ y hy).comp ((p₀, y), y) hproj
    have hg : ContDiffAt ℝ ∞ (fun p : P × E => p.2) (p₀, y) := contDiffAt_snd
    have hfd := ContDiffAt.fderiv
      (f := fun (p : P × E) => fun (z : E) => scalarOnE (I := I) α (f p.1) z)
      (g := fun p : P × E => p.2) hf' hg (by simp)
    have hcomp :=
      (ContinuousLinearMap.apply ℝ ℝ (chartModelBasis E i)).contDiff.contDiffAt.comp
        (p₀, y) hfd
    unfold partialDeriv
    refine hcomp.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun _ => rfl
  have hgram : ∀ (i j : Fin (Module.finrank ℝ E)) (y : E),
      y ∈ interior (extChartAt I α).target →
      ContDiffAt ℝ ∞ (fun p : P × E => chartInvGramOnE (I := I) g α i j p.2) (p₀, y) := by
    intro i j y hy
    change ContDiffAt ℝ ∞
      ((fun z : E => chartInvGramOnE (I := I) g α i j z) ∘ (fun p : P × E => p.2)) (p₀, y)
    refine ContDiffAt.comp (p₀, y) ?_ ?_
    · exact (chartInvGramOnE_contDiffOn (I := I) g α i j).contDiffAt
        (mem_interior_iff_mem_nhds.mp hy)
    · exact (contDiffAt_snd : ContDiffAt ℝ ∞ (fun p : P × E => p.2) (p₀, y))
  have hgradCoeff : ∀ (i : Fin (Module.finrank ℝ E)) (y : E),
      y ∈ interior (extChartAt I α).target →
      ContDiffAt ℝ ∞
        (fun p : P × E => gradChartCoeffOnE (I := I) g α (f p.1) i p.2) (p₀, y) := by
    intro i y hy
    have hsum_cd : ContDiffAt ℝ ∞
        (fun p : P × E => ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α i j p.2 *
            partialDeriv (E := E) j (fun z : E => scalarOnE (I := I) α (f p.1) z) p.2)
        (p₀, y) := by
      exact ContDiffAt.sum (s := Finset.univ) (fun j _ => (hgram i j y hy).mul (hpd j y hy))
    refine hsum_cd.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun p => by
      change gradChartCoeffOnE (I := I) g α (f p.1) i p.2 =
        ∑ j, chartInvGramOnE (I := I) g α i j p.2 *
          partialDeriv (E := E) j (scalarOnE (I := I) α (f p.1)) p.2
      exact gradChartCoeffOnE_def (I := I) g α (f p.1) i p.2
  have hρ : ∀ y : E, y ∈ interior (extChartAt I α).target →
      ContDiffAt ℝ ∞ (fun p : P × E => chartDensityOnE (I := I) g α p.2) (p₀, y) := by
    intro y hy
    change ContDiffAt ℝ ∞
      ((fun z : E => chartDensityOnE (I := I) g α z) ∘ (fun p : P × E => p.2)) (p₀, y)
    refine ContDiffAt.comp (p₀, y) ?_ ?_
    · exact (chartDensityOnE_contDiffOn (I := I) g α).contDiffAt
        (mem_interior_iff_mem_nhds.mp hy)
    · exact (contDiffAt_snd : ContDiffAt ℝ ∞ (fun p : P × E => p.2) (p₀, y))
  have hintegrand : ∀ (i : Fin (Module.finrank ℝ E)) (y : E),
      y ∈ interior (extChartAt I α).target →
      ContDiffAt ℝ ∞
        (fun p : P × E => chartVossWeylIntegrand (I := I) g α (f p.1) i p.2) (p₀, y) := by
    intro i y hy
    simpa [chartVossWeylIntegrand_def] using (hgradCoeff i y hy).mul (hρ y hy)
  exact (hintegrand i y₀ hy₀).contDiffWithinAt

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
  have hΨ (i : Fin (Module.finrank ℝ E)) (y : E)
      (hy : y ∈ interior (extChartAt I α).target) :
      ContDiffAt ℝ ∞
        (fun p : ℝ × E => gradChartCoeffOnE (I := I) g α (f p.1) i p.2 *
          chartDensityOnE (I := I) g α p.2) (t, y) :=
    (chartVossWeylIntegrand_contDiffOn_prod g f hJ hf α i).contDiffAt
      ((hJ.prod isOpen_interior).mem_nhds ⟨ht, hy⟩)
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

private theorem chartLaplacian_contDiffAt_prod
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (g : SmoothRiemannianMetric I M) (f : P → M → ℝ)
    {S : Set P} (hS : IsOpen S)
    (hf : ContMDiffOn (𝓘(ℝ, P).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : P × M => f p.1 p.2) (S ×ˢ univ))
    (α : M) {p₀ : P} (hp₀ : p₀ ∈ S) {y₀ : E}
    (hxtarget : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞ (fun p : P × E =>
      (∑ i : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i (chartVossWeylIntegrand (I := I) g α (f p.1) i) p.2) /
        chartDensityOnE (I := I) g α p.2) (p₀, y₀) := by
  classical
  have hintegrand (i : Fin (Module.finrank ℝ E)) (y : E)
      (hy : y ∈ interior (extChartAt I α).target) :
      ContDiffAt ℝ ∞
        (fun p : P × E => chartVossWeylIntegrand (I := I) g α (f p.1) i p.2) (p₀, y) :=
    (chartVossWeylIntegrand_contDiffOn_prod g f hS hf α i).contDiffAt
      ((hS.prod isOpen_interior).mem_nhds ⟨hp₀, hy⟩)
  have hρ : ∀ y : E, y ∈ interior (extChartAt I α).target →
      ContDiffAt ℝ ∞ (fun p : P × E => chartDensityOnE (I := I) g α p.2) (p₀, y) := by
    intro y hy
    change ContDiffAt ℝ ∞
      ((fun z : E => chartDensityOnE (I := I) g α z) ∘ (fun p : P × E => p.2)) (p₀, y)
    refine ContDiffAt.comp (p₀, y) ?_ ?_
    · exact (chartDensityOnE_contDiffOn (I := I) g α).contDiffAt
        (mem_interior_iff_mem_nhds.mp hy)
    · exact (contDiffAt_snd : ContDiffAt ℝ ∞ (fun p : P × E => p.2) (p₀, y))
  have hpdI : ∀ (i : Fin (Module.finrank ℝ E)) (y : E),
      y ∈ interior (extChartAt I α).target →
      ContDiffAt ℝ ∞
        (fun p : P × E => partialDeriv (E := E) i
          (fun z : E => chartVossWeylIntegrand (I := I) g α (f p.1) i z) p.2) (p₀, y) := by
    intro i y hy
    have hproj : ContDiffAt ℝ ∞ (fun q : (P × E) × E => (q.1.1, q.2)) ((p₀, y), y) := by
      exact contDiffAt_fst.fst.prodMk contDiffAt_snd
    have hf' : ContDiffAt ℝ ∞ (Function.uncurry
        (fun (p : P × E) => fun (z : E) => chartVossWeylIntegrand (I := I) g α (f p.1) i z))
        ((p₀, y), y) := by
      exact (hintegrand i y hy).comp ((p₀, y), y) hproj
    have hg : ContDiffAt ℝ ∞ (fun p : P × E => p.2) (p₀, y) := contDiffAt_snd
    have hfd := ContDiffAt.fderiv
      (f := fun (p : P × E) => fun (z : E) => chartVossWeylIntegrand (I := I) g α (f p.1) i z)
      (g := fun p : P × E => p.2) hf' hg (by simp)
    have hcomp :=
      (ContinuousLinearMap.apply ℝ ℝ (chartModelBasis E i)).contDiff.contDiffAt.comp
        (p₀, y) hfd
    unfold partialDeriv
    refine hcomp.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun _ => rfl
  have hsum : ContDiffAt ℝ ∞
      (fun p : P × E =>
        (∑ i : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i (chartVossWeylIntegrand (I := I) g α (f p.1) i) p.2) /
          chartDensityOnE (I := I) g α p.2)
      (p₀, y₀) := by
    have hsum0 : ContDiffAt ℝ ∞
        (fun p : P × E =>
          ∑ i : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) i (chartVossWeylIntegrand (I := I) g α (f p.1) i) p.2)
        (p₀, y₀) := by
      exact ContDiffAt.sum (s := Finset.univ) (fun i _ => hpdI i y₀ hxtarget)
    have hdens : ContDiffAt ℝ ∞
        (fun p : P × E => chartDensityOnE (I := I) g α p.2) (p₀, y₀) :=
      hρ y₀ hxtarget
    have hbase : (extChartAt I α).symm y₀ ∈
        (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source,
        ← extChartAt_source_eq_chartAt_source (I := I)]
      exact (extChartAt I α).map_target (interior_subset hxtarget)
    have hdens_ne : chartDensityOnE (I := I) g α y₀ ≠ 0 :=
      ne_of_gt (chartDensity_pos (I := I) g α hbase)
    exact hsum0.div hdens hdens_ne
  exact hsum

theorem scalarOnE_chartVossWeylLaplacian_contDiffOn_prod
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (g : SmoothRiemannianMetric I M) (f : P → M → ℝ)
    {S : Set P} (hS : IsOpen S)
    (hf : ContMDiffOn (𝓘(ℝ, P).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : P × M => f p.1 p.2) (S ×ˢ univ)) (α : M) :
    ContDiffOn ℝ ∞
      (fun p : P × E => scalarOnE (I := I) α
        (chartVossWeylLaplacian (I := I) g α (f p.1)) p.2)
      (S ×ˢ interior (extChartAt I α).target) := by
  intro p hp
  apply (chartLaplacian_contDiffAt_prod g f hS hf α hp.1 hp.2).contDiffWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with r hr
    simp only [scalarOnE_def, chartVossWeylLaplacian_def, chartDensityOnE,
      (extChartAt I α).right_inv (interior_subset hr.2)]
  · simp only [scalarOnE_def, chartVossWeylLaplacian_def, chartDensityOnE,
      (extChartAt I α).right_inv (interior_subset hp.2)]

end DifferentialGeometry.Geometry.Operator
