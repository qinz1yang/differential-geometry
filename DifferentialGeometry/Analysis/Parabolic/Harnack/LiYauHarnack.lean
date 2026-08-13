import DifferentialGeometry.Analysis.Parabolic.Harnack.LiYau
import DifferentialGeometry.Analysis.Parabolic.Harnack.PathIntegration
import DifferentialGeometry.Analysis.Calculus.CurveDerivative
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Comparison.HopfRinowProper

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology Bundle

namespace DifferentialGeometry.Analysis.Parabolic.Harnack

open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M]

omit [T2Space M] in
private theorem chartLaplacianValue_jointContDiffAt
    [SigmaCompactSpace M]
    {D : RealTimeInterval}
    (g : SmoothRiemannianMetric I M)
    (f : ℝ → M → ℝ)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => f p.1 p.2)
      (D.regular ×ˢ univ))
    {t₀ : ℝ} (ht₀ : t₀ ∈ D.regular) (x₀ : M) :
    ∀ α : M, x₀ ∈ (chartAt H α).source →
      ContDiffAt ℝ ∞ (fun p : ℝ × E =>
        (∑ i : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i (chartVossWeylIntegrand (I := I) g α (f p.1) i) p.2) /
          chartDensityOnE (I := I) g α p.2)
        (t₀, (extChartAt I α) x₀) := by
  classical
  intro α hxsrc
  have hxextsrc : x₀ ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I) α]
    exact hxsrc
  have hxtarget : (extChartAt I α) x₀ ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxextsrc
  have hΦ : ∀ y : E, y ∈ (extChartAt I α).target →
      ContDiffAt ℝ ∞
        (fun r : ℝ × E => scalarOnE (I := I) α (f r.1) r.2) (t₀, y) :=
    fun y hy => scalarOnE_jointContDiffAt (I := I) (M := M) (D := D) f hf α ht₀ hy
  have hpd : ∀ (i : Fin (Module.finrank ℝ E)) (y : E),
      y ∈ (extChartAt I α).target →
      ContDiffAt ℝ ∞
        (fun p : ℝ × E => partialDeriv (E := E) i
          (fun z : E => scalarOnE (I := I) α (f p.1) z) p.2)
        (t₀, y) := by
    intro i y hy
    have hproj : ContDiffAt ℝ ∞ (fun q : (ℝ × E) × E => (q.1.1, q.2)) ((t₀, y), y) := by
      exact contDiffAt_fst.fst.prodMk contDiffAt_snd
    have hf' : ContDiffAt ℝ ∞ (Function.uncurry
        (fun (p : ℝ × E) => fun (z : E) => scalarOnE (I := I) α (f p.1) z))
        ((t₀, y), y) := by
      exact (hΦ y hy).comp ((t₀, y), y) hproj
    have hg : ContDiffAt ℝ ∞ (fun p : ℝ × E => p.2) (t₀, y) := contDiffAt_snd
    have hfd := ContDiffAt.fderiv
      (f := fun (p : ℝ × E) => fun (z : E) => scalarOnE (I := I) α (f p.1) z)
      (g := fun p : ℝ × E => p.2) hf' hg (by simp)
    simpa [partialDeriv] using
      ((ContinuousLinearMap.apply ℝ ℝ (chartModelBasis E i)).contDiff.contDiffAt.comp
        (t₀, y) hfd)
  have hgram : ∀ (i j : Fin (Module.finrank ℝ E)) (y : E),
      y ∈ (extChartAt I α).target →
      ContDiffAt ℝ ∞ (fun p : ℝ × E => chartInvGramOnE (I := I) g α i j p.2) (t₀, y) := by
    intro i j y hy
    change ContDiffAt ℝ ∞
      ((fun z : E => chartInvGramOnE (I := I) g α i j z) ∘ (fun p : ℝ × E => p.2)) (t₀, y)
    refine ContDiffAt.comp (t₀, y) ?_ ?_
    · exact (chartInvGramOnE_contDiffOn (I := I) g α i j).contDiffAt
        ((isOpen_extChartAt_target (I := I) α).mem_nhds hy)
    · exact (contDiffAt_snd : ContDiffAt ℝ ∞ (fun p : ℝ × E => p.2) (t₀, y))
  have hgradCoeff : ∀ (i : Fin (Module.finrank ℝ E)) (y : E),
      y ∈ (extChartAt I α).target →
      ContDiffAt ℝ ∞
        (fun p : ℝ × E => gradChartCoeffOnE (I := I) g α (f p.1) i p.2) (t₀, y) := by
    intro i y hy
    have hsum_cd : ContDiffAt ℝ ∞
        (fun p : ℝ × E => ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α i j p.2 *
            partialDeriv (E := E) j (fun z : E => scalarOnE (I := I) α (f p.1) z) p.2)
        (t₀, y) := by
      exact ContDiffAt.sum (s := Finset.univ) (fun j _ => (hgram i j y hy).mul (hpd j y hy))
    simpa [gradChartCoeffOnE_def] using hsum_cd
  have hρ : ∀ y : E, y ∈ (extChartAt I α).target →
      ContDiffAt ℝ ∞ (fun p : ℝ × E => chartDensityOnE (I := I) g α p.2) (t₀, y) := by
    intro y hy
    change ContDiffAt ℝ ∞
      ((fun z : E => chartDensityOnE (I := I) g α z) ∘ (fun p : ℝ × E => p.2)) (t₀, y)
    refine ContDiffAt.comp (t₀, y) ?_ ?_
    · exact (chartDensityOnE_contDiffOn (I := I) g α).contDiffAt
        ((isOpen_extChartAt_target (I := I) α).mem_nhds hy)
    · exact (contDiffAt_snd : ContDiffAt ℝ ∞ (fun p : ℝ × E => p.2) (t₀, y))
  have hintegrand : ∀ (i : Fin (Module.finrank ℝ E)) (y : E),
      y ∈ (extChartAt I α).target →
      ContDiffAt ℝ ∞
        (fun p : ℝ × E => chartVossWeylIntegrand (I := I) g α (f p.1) i p.2) (t₀, y) := by
    intro i y hy
    simpa [chartVossWeylIntegrand_def] using (hgradCoeff i y hy).mul (hρ y hy)
  have hpdI : ∀ (i : Fin (Module.finrank ℝ E)) (y : E),
      y ∈ (extChartAt I α).target →
      ContDiffAt ℝ ∞
        (fun p : ℝ × E => partialDeriv (E := E) i
          (fun z : E => chartVossWeylIntegrand (I := I) g α (f p.1) i z) p.2) (t₀, y) := by
    intro i y hy
    have hproj : ContDiffAt ℝ ∞ (fun q : (ℝ × E) × E => (q.1.1, q.2)) ((t₀, y), y) := by
      exact contDiffAt_fst.fst.prodMk contDiffAt_snd
    have hf' : ContDiffAt ℝ ∞ (Function.uncurry
        (fun (p : ℝ × E) => fun (z : E) => chartVossWeylIntegrand (I := I) g α (f p.1) i z))
        ((t₀, y), y) := by
      exact (hintegrand i y hy).comp ((t₀, y), y) hproj
    have hg : ContDiffAt ℝ ∞ (fun p : ℝ × E => p.2) (t₀, y) := contDiffAt_snd
    have hfd := ContDiffAt.fderiv
      (f := fun (p : ℝ × E) => fun (z : E) => chartVossWeylIntegrand (I := I) g α (f p.1) i z)
      (g := fun p : ℝ × E => p.2) hf' hg (by simp)
    simpa [partialDeriv] using
      ((ContinuousLinearMap.apply ℝ ℝ (chartModelBasis E i)).contDiff.contDiffAt.comp
        (t₀, y) hfd)
  have hsum : ContDiffAt ℝ ∞
      (fun p : ℝ × E =>
        (∑ i : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i (chartVossWeylIntegrand (I := I) g α (f p.1) i) p.2) /
          chartDensityOnE (I := I) g α p.2)
      (t₀, (extChartAt I α) x₀) := by
    have hsum0 : ContDiffAt ℝ ∞
        (fun p : ℝ × E =>
          ∑ i : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) i (chartVossWeylIntegrand (I := I) g α (f p.1) i) p.2)
        (t₀, (extChartAt I α) x₀) := by
      exact ContDiffAt.sum (s := Finset.univ) (fun i _ => hpdI i ((extChartAt I α) x₀) hxtarget)
    have hdens : ContDiffAt ℝ ∞
        (fun p : ℝ × E => chartDensityOnE (I := I) g α p.2) (t₀, (extChartAt I α) x₀) :=
      hρ ((extChartAt I α) x₀) hxtarget
    have hxbase : x₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source (I := I) α]
      exact hxsrc
    have hpos : 0 < chartDensity (I := I) g α x₀ := chartDensity_pos (I := I) g α hxbase
    have hdens_ne : chartDensityOnE (I := I) g α ((extChartAt I α) x₀) ≠ 0 := by
      rw [chartDensityOnE]
      rw [(extChartAt I α).left_inv hxextsrc]
      exact ne_of_gt hpos
    exact hsum0.div hdens hdens_ne
  exact hsum

private theorem laplacianAt_time_contDiffAt_on
    [SigmaCompactSpace M]
    {D : RealTimeInterval}
    (g : SmoothRiemannianMetric I M)
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (hGmetric : ∀ t : ℝ, t ∈ D.carrier → G.metric t = g)
    (hGconn : ∀ t : ℝ, t ∈ D.carrier → G.connection t = LeviCivita (G.metric t))
    (u : ℝ → M → ℝ)
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => u p.1 p.2)
      (D.regular ×ˢ univ))
    (hslice : ∀ t : ℝ, t ∈ D.carrier → ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t))
    {t₀ : ℝ} (ht₀ : t₀ ∈ D.regular) (x : M) :
    ContDiffAt ℝ ∞ (fun t : ℝ => laplacianAt (I := I) G t (u t) x) t₀ := by
  classical
  set α : M := x with hα
  have hxsrc : x ∈ (chartAt H α).source := mem_chart_source H α
  have hxextsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I) α]
    exact hxsrc
  have hxtarget : (extChartAt I α) x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxextsrc
  have hcd : ContDiffAt ℝ ∞
      (fun p : ℝ × E =>
        (∑ i : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i (chartVossWeylIntegrand (I := I) g α (u p.1) i) p.2) /
          chartDensityOnE (I := I) g α p.2)
      (t₀, (extChartAt I α) x) :=
    chartLaplacianValue_jointContDiffAt (I := I) (M := M) (D := D) g u hu ht₀ x α hxsrc
  have hsliceAt : ContDiffAt ℝ ∞
      (fun t : ℝ =>
        (∑ i : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i (chartVossWeylIntegrand (I := I) g α (u t) i)
            ((extChartAt I α) x)) /
          chartDensityOnE (I := I) g α ((extChartAt I α) x)) t₀ := by
    exact hcd.comp (x := t₀) (contDiffAt_id.prodMk contDiffAt_const)
  have hbridge : ∀ᶠ t in 𝓝 t₀,
      laplacianAt (I := I) G t (u t) x =
        (∑ i : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i (chartVossWeylIntegrand (I := I) g α (u t) i)
            ((extChartAt I α) x)) /
          chartDensityOnE (I := I) g α ((extChartAt I α) x) := by
    filter_upwards [IsOpen.mem_nhds D.regular_isOpen ht₀] with t ht
    have hconn : G.connection t = LeviCivita (G.metric t) := hGconn t (D.regular_subset ht)
    have hlap : laplacianAt (I := I) G t (u t) x =
        Δ_g (I := I) g ⟨u t, hslice t (D.regular_subset ht)⟩ x := by
      rw [laplacianAt_eq_delta (I := I) G t (hslice t (D.regular_subset ht)) hconn x]
      rw [hGmetric t (D.regular_subset ht)]
    have hvw : Δ_g (I := I) g ⟨u t, hslice t (D.regular_subset ht)⟩ x =
        (∑ i : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i (chartVossWeylIntegrand (I := I) g α (u t) i)
            ((extChartAt I α) x)) /
          chartDensityOnE (I := I) g α ((extChartAt I α) x) := by
      have hvw0 : Δ_g (I := I) g ⟨u t, hslice t (D.regular_subset ht)⟩ x =
          chartVossWeylLaplacian (I := I) g α (u t) x :=
        voss_weyl_laplacian_formula_pointwise (I := I) g α
          (hslice t (D.regular_subset ht)) hxsrc
      rw [hvw0]
      simp only [chartVossWeylLaplacian, chartDensityOnE, chartDensity]
      rw [(extChartAt I α).left_inv hxextsrc]
    exact hlap.trans hvw
  exact hsliceAt.congr_of_eventuallyEq hbridge

theorem heat_solution_one_point_harnack_of_nonnegative_ricci_on
    [CompactSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M)
    (hRic : ∀ x v, 0 ≤ ricciTensor (I := I) g x v v)
    (D : RealTimeInterval)
    (u : ℝ → M → ℝ)
    (hu : IsHeatOnStationary D g u)
    (huClosed : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2) (D.carrier ×ˢ univ))
    (hpos : ∀ t : ℝ, t ∈ D.carrier → ∀ x : M, 0 < u t x)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hreg : Icc a b ⊆ D.regular)
    (hcarrier : Icc 0 b ⊆ D.carrier)
    (hslabRegular : Ioo 0 b ⊆ D.regular)
    (x : M) :
    u a x ≤ (b / a) ^ ((Module.finrank ℝ E : ℝ) / 2) * u b x := by
  classical
  let G : MetricConnectionFamily (I := I) (M := M) ℝ :=
    stationaryMetricFamily (I := I) (M := M) g
  let n : ℝ := (Module.finrank ℝ E : ℝ)
  have hly_all : ∀ t : ℝ, t ∈ Set.Icc a b → 0 < t →
      liYauQuantity g (fun τ y => Real.log (u τ y)) t x ≤ n / (2 * t) :=
    fun t ht htpos => by
      have htreg : t ∈ D.regular := hreg ht
      have hcar_t : Icc 0 t ⊆ D.carrier := by
        intro s hs
        exact hcarrier ⟨hs.1, hs.2.trans ht.2⟩
      have hreg_t : Ioo 0 t ⊆ D.regular := by
        intro s hs
        exact hslabRegular ⟨hs.1, hs.2.trans_le ht.2⟩
      simpa [n] using liYau_estimate_of_nonnegative_ricci_on_of_metric_family
        (I := I) (M := M) g hRic D (stationaryMetricFamily (I := I) (M := M) g)
        (by intro τ hτ; rfl) (by intro τ hτ; rfl)
        u hu huClosed hpos htreg htpos hcar_t hreg_t x
  have hliYau_bound : ∀ t ∈ Set.Icc a b,
      -(n / 2 / t) ≤ deriv (fun s => u s x) t / u t x := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le ha ht.1
    have hly := hly_all t ht htpos
    have hlogderiv : deriv (fun s => Real.log (u s x)) t = deriv (fun s => u s x) t / u t x := by
      have hder : HasDerivAt (fun s => u s x) (deriv (fun s => u s x) t) t := by
        exact (hu.equation t (hreg ht) x).congr_deriv (hu.equation t (hreg ht) x).deriv.symm
      exact (hder.log (hpos t (D.regular_subset (hreg ht)) x).ne').deriv
    have hq_nonneg_grad : 0 ≤ g.inner x
        (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
        (gradientFun (I := I) g (fun y => Real.log (u t y)) x) := by
      let v : TangentSpace I x := gradientFun (I := I) g (fun y => Real.log (u t y)) x
      have hvnonneg : 0 ≤ g.inner x v v := by
        by_cases hv : v = 0
        · rw [hv]
          simp
        · exact le_of_lt (g.pos x v hv)
      simpa [v] using hvnonneg
    have hq : liYauQuantity g (fun τ y => Real.log (u τ y)) t x =
        g.inner x (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
          (gradientFun (I := I) g (fun y => Real.log (u t y)) x) -
          deriv (fun s => Real.log (u s x)) t := rfl
    have hstep : -(n / (2 * t)) ≤ deriv (fun s => Real.log (u s x)) t := by
      rw [hq] at hly
      have hgrad_le : 0 ≤ g.inner x
          (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
          (gradientFun (I := I) g (fun y => Real.log (u t y)) x) := hq_nonneg_grad
      linarith
    rw [hlogderiv] at hstep
    have hrewrite : n / (2 * t) = n / 2 / t := by
      field_simp [htpos.ne']
    rw [hrewrite] at hstep
    simpa using hstep
  have hu_path_pos : ∀ t ∈ Set.Icc a b,
    0 < u t x := fun t ht => hpos t (D.regular_subset (hreg ht)) x
  have hcdAt : ∀ t : ℝ, t ∈ D.regular → ContDiffAt ℝ ∞ (fun s : ℝ => u s x) t := by
    intro t ht
    have hnh : D.regular ×ˢ univ ∈ 𝓝 (t, x) :=
      (IsOpen.prod D.regular_isOpen isOpen_univ).mem_nhds ⟨ht, trivial⟩
    have huat : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => u p.1 p.2) (t, x) := hu.jointSmooth.contMDiffAt hnh
    have hsliceAt : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => u s x) t :=
      huat.comp (x := t) (contMDiffAt_id.prodMk contMDiffAt_const)
    exact contMDiffAt_iff_contDiffAt.mp hsliceAt
  have hderivative_cont : ContinuousOn (fun t : ℝ => deriv (fun s => u s x) t) (Set.Icc a b) := by
    have hlapCont : ∀ t : ℝ, t ∈ D.regular →
        ContinuousAt (fun s : ℝ => laplacianAt (I := I) G s (u s) x) t := by
      intro t ht
      exact (laplacianAt_time_contDiffAt_on (I := I) (M := M) (D := D) g
        (stationaryMetricFamily (I := I) (M := M) g)
        (by intro τ hτ; rfl) (by intro τ hτ; rfl) u
        hu.jointSmooth hu.sliceSmooth ht x).continuousAt
    have hderiv_eq : ∀ t : ℝ, t ∈ D.regular →
        deriv (fun s : ℝ => u s x) t = laplacianAt (I := I) G t (u t) x := by
      intro t ht
      simpa using (hu.equation t ht x).deriv
    have hderiv_contAt : ∀ t : ℝ, t ∈ Set.Icc a b →
        ContinuousAt (fun s : ℝ => deriv (fun s : ℝ => u s x) s) t := by
      intro t ht
      have htreg : t ∈ D.regular := hreg ht
      have hcont := hlapCont t htreg
      refine hcont.congr_of_eventuallyEq ?_
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨D.regular, IsOpen.mem_nhds D.regular_isOpen htreg, ?_⟩
      intro s hs
      exact hderiv_eq s hs
    intro t ht
    exact (hderiv_contAt t ht).continuousWithinAt
  have hu_path_deriv : ∀ t ∈ Set.Icc a b,
      HasDerivAt (fun s : ℝ => u s x) (deriv (fun s : ℝ => u s x) t) t := by
    intro t ht
    have htreg : t ∈ D.regular := hreg ht
    have hcdat : ContDiffAt ℝ ∞ (fun s : ℝ => u s x) t := hcdAt t htreg
    exact (hcdat.differentiableAt (by norm_num)).hasDerivAt
  have hbridge := harnack_endpoint_of_li_yau_bound
    (V := ℝ) (u := fun t : ℝ => u t x)
    (derivative := fun t : ℝ => deriv (fun s => u s x) t)
    (timePart := fun t : ℝ => deriv (fun s => u s x) t / u t x)
    (gradient := fun _ : ℝ => (0 : ℝ))
    (velocity := fun _ : ℝ => (0 : ℝ))
    (a := a) (b := b) (c := n / 2) (alpha := (1 : ℝ))
    (by norm_num) ha hab hu_path_pos hderivative_cont continuousOn_const
    hu_path_deriv (by intro t ht; simp) (by
      intro t ht
      simpa using hliYau_bound t ht)
  simpa [n] using hbridge

theorem heat_solution_one_point_harnack_of_nonnegative_ricci
    [CompactSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M)
    (hRic : ∀ x v, 0 ≤ ricciTensor (I := I) g x v v)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (hpde : ∀ t x, deriv (fun s => u s x) t =
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (x : M) :
    u a x ≤ (b / a) ^ ((Module.finrank ℝ E : ℝ) / 2) * u b x := by
  classical
  let D : RealTimeInterval := RealTimeInterval.univ 0
  let G : MetricConnectionFamily (I := I) (M := M) ℝ :=
    stationaryMetricFamily (I := I) (M := M) g
  have huOn : IsHeatOn D G u := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [D] using hu.contMDiffOn
    · exact hu.continuous.continuousOn
    · intro τ hτ
      exact hu.comp (contMDiff_const.prodMk contMDiff_id)
    · intro τ hτ x
      have hslice_cd : ContDiff ℝ ∞ (fun s => u s x) :=
        contMDiff_iff_contDiff.mp (hu.comp (contMDiff_id.prodMk contMDiff_const))
      have hder : HasDerivAt (fun s => u s x) (deriv (fun s => u s x) τ) τ :=
        (ContDiff.differentiable hslice_cd (by norm_num) τ).hasDerivAt
      have hlap : laplacianAt (I := I) G τ (u τ) x =
          Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu τ).toContMDiffMap x := by
        change laplacianAt (I := I) G τ (smoothScalarSlice (I := I) g u hu τ).toFun x =
          Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu τ).toContMDiffMap x
        rw [laplacianAt_eq_delta (I := I) G τ (smoothScalarSlice (I := I) g u hu τ).smooth
          (by rfl) x]
        rfl
      have hderiv : deriv (fun s => u s x) τ = laplacianAt (I := I) G τ (u τ) x := by
        rw [hpde τ x, ← hlap]
      convert hder.congr_deriv hderiv using 1
      simp
  simpa [D] using heat_solution_one_point_harnack_of_nonnegative_ricci_on
    (I := I) (M := M) g hRic D u huOn (by simpa [D] using hu.contMDiffOn)
    (fun τ hτ x => hpos τ x)
    ha hab (by intro τ hτ; trivial) (by intro τ hτ; trivial) (by intro τ hτ; trivial) x

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
theorem metric_inner_nonneg
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · rw [hv]
    simp
  · exact le_of_lt (g.pos x v hv)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
theorem metric_inner_add_inner_ge_neg_quarter
    (g : SmoothRiemannianMetric I M) (x : M) (p v : TangentSpace I x) :
    -(1 / 4) * g.inner x v v ≤ g.inner x p p + g.inner x p v := by
  let w : TangentSpace I x := p + ((1 / 2 : ℝ)) • v
  have hnonneg : 0 ≤ g.inner x w w := metric_inner_nonneg g x w
  have hsq : g.inner x w w = g.inner x p p + g.inner x p v + (1 / 4) * g.inner x v v := by
    have hlin1 : g.inner x (p + ((1 / 2 : ℝ)) • v) = g.inner x p + ((1 / 2 : ℝ)) • g.inner x v := by
      rw [(g.inner x).map_add]
      congr 1
      exact (g.inner x).map_smul (1 / 2 : ℝ) v
    have ha : (g.inner x p) (p + ((1 / 2 : ℝ)) • v) =
        g.inner x p p + (1 / 2) * g.inner x p v := by
      rw [(g.inner x p).map_add]
      congr 1
      exact ((g.inner x) p).map_smul (1 / 2 : ℝ) v
    have hb : (((1 / 2 : ℝ)) • g.inner x v) (p + ((1 / 2 : ℝ)) • v) =
        (1 / 2) * g.inner x v p + (1 / 4) * g.inner x v v := by
      rw [ContinuousLinearMap.smul_apply]
      rw [(g.inner x v).map_add]
      rw [smul_eq_mul, mul_add]
      congr 1
      have hms := ((g.inner x) v).map_smul (1 / 2 : ℝ) v
      rw [hms]
      simp [smul_eq_mul]
      ring
    calc
      g.inner x w w = (g.inner x p + ((1 / 2 : ℝ)) • g.inner x v) (p + ((1 / 2 : ℝ)) • v) := by
        rw [← hlin1]
      _ = (g.inner x p) (p + ((1 / 2 : ℝ)) • v) +
          (((1 / 2 : ℝ)) • g.inner x v) (p + ((1 / 2 : ℝ)) • v) := by
        rfl
      _ = (g.inner x p p + (1 / 2) * g.inner x p v) +
          ((1 / 2) * g.inner x v p + (1 / 4) * g.inner x v v) := by
        rw [ha, hb]
      _ = g.inner x p p + g.inner x p v + (1 / 4) * g.inner x v v := by
        rw [g.symm x p v]
        ring
  nlinarith

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem heat_solution_harnack_of_nonnegative_ricci_on
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    [CompactSpace M] [ConnectedSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hRic : ∀ x v, 0 ≤ ricciTensor (I := I) g x v v)
    (D : RealTimeInterval)
    (u : ℝ → M → ℝ)
    (hu : IsHeatOnStationary D g u)
    (huClosed : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2) (D.carrier ×ˢ univ))
    (hpos : ∀ t : ℝ, t ∈ D.carrier → ∀ x : M, 0 < u t x)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hreg : Icc a b ⊆ D.regular)
    (hcarrier : Icc 0 b ⊆ D.carrier)
    (hslabRegular : Ioo 0 b ⊆ D.regular)
    (x y : M) :
    u a x ≤ (b / a) ^ ((Module.finrank ℝ E : ℝ) / 2) *
      Real.exp ((riemannianEDist I x y).toReal ^ 2 / (4 * (b - a))) * u b y := by
  classical
  let G : MetricConnectionFamily (I := I) (M := M) ℝ :=
    stationaryMetricFamily (I := I) (M := M) g
  let n : ℝ := (Module.finrank ℝ E : ℝ)
  let d : ℝ := (riemannianEDist I x y).toReal
  have hne_top : riemannianEDist I x y ≠ ⊤ := riemannianEDist_ne_top (I := I) x y
  have hd_nn : 0 ≤ d := ENNReal.toReal_nonneg
  by_cases hd0 : d = 0
  · have hx_eq_y : x = y := by
      have hd0' : riemannianEDist I x y = 0 := by
        have hreal : riemannianEDist I x y = ENNReal.ofReal d := by
          rw [← ENNReal.ofReal_toReal hne_top]
        rw [hreal, hd0, ENNReal.ofReal_zero]
      exact riemannianEDist_eq_zero_imp_eq (I := I) x y hd0'
    subst hx_eq_y
    simpa [n, riemannianEDist_self] using heat_solution_one_point_harnack_of_nonnegative_ricci_on
      (I := I) (M := M) g hRic D u hu huClosed hpos ha (le_of_lt hab)
      hreg hcarrier hslabRegular x
  · have hd_pos : 0 < d := lt_of_le_of_ne hd_nn (Ne.symm hd0)
    obtain ⟨v, hv_exp, hv_len⟩ :=
      hopf_rinow_expMapIntrinsic_surjective_minimizing (I := I) g hEnorm x y
    let uvec : TangentSpace I x := d⁻¹ • v
    have hvv_nn : 0 ≤ g.inner x v v := metric_inner_nonneg g x v
    have hvv_sq : g.inner x v v = d ^ 2 := by
      have := congrArg (· ^ 2) hv_len
      simpa [Real.sq_sqrt hvv_nn] using this
    have huu : g.inner x uvec uvec = 1 := by
      have hbil : g.inner x uvec uvec = d⁻¹ * (d⁻¹ * g.inner x v v) := by
        dsimp [uvec]
        simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [hbil, hvv_sq]
      field_simp [hd0]
    have hdu : d • uvec = v := by
      dsimp [uvec]
      rw [smul_smul, mul_inv_cancel₀ hd0, one_smul]
    let γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm x uvec
    have hγ0 : γ 0 = x := intrinsicGeodesic_zero (I := I) g hEnorm x uvec
    have hγd : γ d = y := by
      have hsmul : intrinsicGeodesic (I := I) g hEnorm x (d • uvec) 1 = γ d :=
        intrinsicGeodesic_smul (I := I) g hEnorm x uvec d
      rw [← hsmul, hdu]
      have hexp : expMapIntrinsic (I := I) g hEnorm x v = y := hv_exp
      rw [expMapIntrinsic_def] at hexp
      exact hexp
    have hγ_cont : Continuous γ := intrinsicGeodesic_continuous (I := I) g hEnorm x uvec
    have hγ_smooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ :=
      isGeodesic_contMDiff (I := I) g
        (intrinsicGeodesic_isGeodesic (I := I) g hEnorm x uvec) hγ_cont
    have hγ_speed : ∀ s : ℝ,
        g.inner (γ s) (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ)) = 1 := by
      intro s
      have hsp := intrinsicGeodesic_speedSq_eq (I := I) g hEnorm x uvec s
      simpa [γ] using hsp.trans huu
    let τ : ℝ → M := fun t => γ ((t - a) / (b - a) * d)
    have hba_pos : 0 < b - a := sub_pos.mpr hab
    have hs_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
        (fun t : ℝ => (t - a) / (b - a) * d) := by
      have hs1 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
          (fun t : ℝ => (t - a) * (1 / (b - a)) * d) := by
        simpa [mul_assoc] using
          ((contMDiff_id.sub contMDiff_const).mul (contMDiff_const (c := 1 / (b - a)))).mul
            (contMDiff_const (c := d))
      refine ContMDiff.congr hs1 ?_
      intro t
      simp [div_eq_mul_inv]
    have hτ_smooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ τ := by
      simpa [τ] using hγ_smooth.comp hs_smooth
    have hτa : τ a = x := by
      simp [τ, hγ0]
    have hτb : τ b = y := by
      have hval : (b - a) / (b - a) * d = d := by
        field_simp [ne_of_gt hba_pos]
      simpa [τ, hval] using hγd
    have hτ_speed : ∀ t : ℝ,
        g.inner (τ t) (mfderiv 𝓘(ℝ, ℝ) I τ t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I τ t (1 : ℝ)) = (d / (b - a)) ^ 2 := by
      intro t
      have hsderiv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
          (fun t : ℝ => (t - a) / (b - a) * d) t (1 : ℝ) = d / (b - a) := by
        rw [mfderiv_eq_fderiv]
        have hd : deriv (fun t : ℝ => (t - a) / (b - a) * d) t = d / (b - a) := by
          have h1 : HasDerivAt (fun t : ℝ => t - a) 1 t := by
            simpa using (hasDerivAt_id t).sub_const a
          have h2 : HasDerivAt (fun t : ℝ => (t - a) * (1 / (b - a)))
              (1 * (1 / (b - a))) t := by
            simpa using (h1.mul (hasDerivAt_const t (1 / (b - a))))
          have h3 : HasDerivAt (fun t : ℝ => (t - a) * (1 / (b - a)) * d)
              ((1 * (1 / (b - a))) * d) t := by
            simpa using h2.mul (hasDerivAt_const t d)
          have h4 : HasDerivAt (fun t : ℝ => (t - a) / (b - a) * d) (d / (b - a)) t := by
            simpa [div_eq_mul_inv, mul_assoc, mul_comm] using h3
          exact h4.deriv
        have hf : (fderiv ℝ (fun t : ℝ => (t - a) / (b - a) * d) t) (1 : ℝ) =
            deriv (fun t : ℝ => (t - a) / (b - a) * d) t :=
          fderiv_apply_one_eq_deriv (f := fun t : ℝ => (t - a) / (b - a) * d) (x := t)
        calc
          (fderiv ℝ (fun t : ℝ => (t - a) / (b - a) * d) t) (1 : ℝ)
              = deriv (fun t : ℝ => (t - a) / (b - a) * d) t := hf
          _ = d / (b - a) := hd
      have hcomp := mfderiv_comp_apply
        (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := I)
        (g := γ) (f := fun t : ℝ => (t - a) / (b - a) * d)
        (x := t)
        (hγ_smooth.mdifferentiableAt (x := (t - a) / (b - a) * d) (by norm_num))
        (hs_smooth.mdifferentiableAt (x := t) (by norm_num))
        (1 : ℝ)
      have hc := congrArg (fun c : TangentSpace 𝓘(ℝ, ℝ) ((t - a) / (b - a) * d) =>
          mfderiv 𝓘(ℝ, ℝ) I γ ((t - a) / (b - a) * d) c) hsderiv
      have hct : mfderiv 𝓘(ℝ, ℝ) I (γ ∘ (fun t : ℝ => (t - a) / (b - a) * d)) t (1 : ℝ) =
          mfderiv 𝓘(ℝ, ℝ) I γ ((t - a) / (b - a) * d) (d / (b - a)) := hcomp.trans hc
      have hchain : mfderiv 𝓘(ℝ, ℝ) I τ t (1 : ℝ) =
          (d / (b - a)) • mfderiv 𝓘(ℝ, ℝ) I γ ((t - a) / (b - a) * d) (1 : ℝ) := by
        have hτe : mfderiv 𝓘(ℝ, ℝ) I τ t (1 : ℝ) =
            mfderiv 𝓘(ℝ, ℝ) I (γ ∘ (fun t : ℝ => (t - a) / (b - a) * d)) t (1 : ℝ) := by
          rfl
        rw [hτe, hct]
        have harg : mfderiv 𝓘(ℝ, ℝ) I γ ((t - a) / (b - a) * d) (d / (b - a)) =
            (d / (b - a)) • mfderiv 𝓘(ℝ, ℝ) I γ ((t - a) / (b - a) * d) (1 : ℝ) := by
          have hc1 : (d / (b - a)) = (d / (b - a)) • (1 : ℝ) := by simp
          have hms := (mfderiv 𝓘(ℝ, ℝ) I γ ((t - a) / (b - a) * d)).map_smul
            (d / (b - a)) (1 : ℝ)
          conv_lhs =>
            arg 2
            rw [hc1]
          exact hms
        exact harg
      rw [hchain]
      have hlin2 : g.inner (τ t)
          ((d / (b - a)) • mfderiv 𝓘(ℝ, ℝ) I γ ((t - a) / (b - a) * d) (1 : ℝ))
          ((d / (b - a)) • mfderiv 𝓘(ℝ, ℝ) I γ ((t - a) / (b - a) * d) (1 : ℝ)) =
          (d / (b - a)) ^ 2 * g.inner (τ t)
            (mfderiv 𝓘(ℝ, ℝ) I γ ((t - a) / (b - a) * d) (1 : ℝ))
            (mfderiv 𝓘(ℝ, ℝ) I γ ((t - a) / (b - a) * d) (1 : ℝ)) := by
        let c : ℝ := d / (b - a)
        let w : TangentSpace I (τ t) :=
          mfderiv 𝓘(ℝ, ℝ) I γ ((t - a) / (b - a) * d) (1 : ℝ)
        have hms1 : g.inner (τ t) (c • w) (c • w) =
            c • g.inner (τ t) w (c • w) := by
          have hms := (g.inner (τ t)).map_smul c w
          have happ := congrArg (fun L : TangentSpace I (τ t) →L[ℝ] ℝ => L (c • w)) hms
          simp [ContinuousLinearMap.smul_apply, smul_eq_mul]
        have hms2 : g.inner (τ t) w (c • w) = c • g.inner (τ t) w w := by
          have hms := ((g.inner (τ t)) w).map_smul c w
          simp [smul_eq_mul]
        calc
          g.inner (τ t) (c • w) (c • w)
              = c • g.inner (τ t) w (c • w) := hms1
          _ = c • (c • g.inner (τ t) w w) := by rw [hms2]
          _ = c ^ 2 * g.inner (τ t) w w := by
            simp [smul_eq_mul]
            ring
      rw [hlin2]
      have hτγ : τ t = γ ((t - a) / (b - a) * d) := rfl
      rw [hτγ]
      have hsp := hγ_speed ((t - a) / (b - a) * d)
      rw [hsp]
      ring
    let f : ℝ → M → ℝ := fun s y => Real.log (u s y)
    have hf_log : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => f p.1 p.2) (D.regular ×ˢ univ) := by
      intro p hp
      have hnh : D.regular ×ˢ univ ∈ 𝓝 p :=
        (IsOpen.prod D.regular_isOpen isOpen_univ).mem_nhds ⟨hp.1, trivial⟩
      have hlogAt : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => Real.log (u p.1 p.2)) p :=
        (Real.contDiffAt_log.2 (hpos p.1 (D.regular_subset hp.1) p.2).ne').comp_contMDiffAt
          (x := p) (hu.jointSmooth.contMDiffAt hnh)
      simpa [f] using hlogAt.contMDiffWithinAt
    have hly_all : ∀ (t : ℝ) (z : M), t ∈ Set.Icc a b → 0 < t →
        liYauQuantity g (fun τ y => Real.log (u τ y)) t z ≤ n / (2 * t) := by
      intro t z ht htpos
      have htreg : t ∈ D.regular := hreg ht
      have hcar_t : Icc 0 t ⊆ D.carrier := by
        intro s hs
        exact hcarrier ⟨hs.1, hs.2.trans ht.2⟩
      have hreg_t : Ioo 0 t ⊆ D.regular := by
        intro s hs
        exact hslabRegular ⟨hs.1, hs.2.trans_le ht.2⟩
      simpa [n] using liYau_estimate_of_nonnegative_ricci_on_of_metric_family
        (I := I) (M := M) g hRic D (stationaryMetricFamily (I := I) (M := M) g)
        (by intro τ hτ; rfl) (by intro τ hτ; rfl)
        u hu huClosed hpos htreg htpos hcar_t hreg_t z
    let τ' : ℝ → (p : M) → TangentSpace I p :=
      fun t _ => mfderiv 𝓘(ℝ, ℝ) I τ t (1 : ℝ)
    have hτ'_def : ∀ t : ℝ, τ' t (τ t) = mfderiv 𝓘(ℝ, ℝ) I τ t (1 : ℝ) := by
      intro t
      rfl
    let timePart : ℝ → ℝ := fun t => deriv (fun s : ℝ => Real.log (u s (τ t))) t
    let gradSq : ℝ → ℝ := fun t =>
      g.inner (τ t) (gradientFun (I := I) g (f t) (τ t))
        (gradientFun (I := I) g (f t) (τ t))
    let innerGV : ℝ → ℝ := fun t =>
      g.inner (τ t) (gradientFun (I := I) g (f t) (τ t))
        (τ' t (τ t))
    let speedSq : ℝ → ℝ := fun _ => (d / (b - a)) ^ 2
    let derivative : ℝ → ℝ := fun t => deriv (fun s => u s (τ s)) t
    have hhu : ∀ t ∈ Icc a b, 0 < u t (τ t) := fun t ht => hpos t (D.regular_subset (hreg ht)) (τ t)
    have huc_reg : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => u s (τ s)) D.regular := by
      have hJ : ContMDiffOn 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I) ∞
          (fun s : ℝ => (s, τ s)) D.regular := by
        have hJ0 : ContMDiffOn 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I) ∞
            (fun s : ℝ => (s, τ s)) univ := by
          exact (contMDiffOn_id : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ id univ).prodMk
            hτ_smooth.contMDiffOn
        exact hJ0.mono (by intro s hs; trivial)
      exact hu.jointSmooth.comp hJ (by intro s hs; exact ⟨hs, trivial⟩)
    have huc_cd : ContDiffOn ℝ ∞ (fun s : ℝ => u s (τ s)) D.regular :=
      contMDiffOn_iff_contDiffOn.mp huc_reg
    have hderiv_cont : ContinuousOn derivative (Icc a b) := by
      have hcont_reg : ContinuousOn
          (iteratedDerivWithin 1 (fun s : ℝ => u s (τ s)) D.regular) D.regular :=
        huc_cd.continuousOn_iteratedDerivWithin (by norm_num) (D.regular_isOpen.uniqueDiffOn)
      refine (hcont_reg.mono (by intro t ht; exact hreg ht)).congr ?_
      intro t ht
      rw [iteratedDerivWithin_one]
      simpa [derivative] using (derivWithin_of_mem_nhds (D.regular_isOpen.mem_nhds (hreg ht))).symm
    have hderiv : ∀ t ∈ Icc a b,
        HasDerivAt (fun s => u s (τ s)) (derivative t) t := by
      intro t ht
      have hcdt : ContDiffAt ℝ ∞ (fun s => u s (τ s)) t :=
        huc_cd.contDiffAt (D.regular_isOpen.mem_nhds (hreg ht))
      exact (hcdt.differentiableAt (by norm_num)).hasDerivAt
    have hpath : ∀ t ∈ Icc a b,
        derivative t / u t (τ t) = timePart t + innerGV t := by
      intro t ht
      have ht_pos : 0 < t := lt_of_lt_of_le ha ht.1
      have hlog_curve := deriv_along_curve_eq_on (I := I) (M := M) (D := D) g
        (F := f) hf_log hτ_smooth (hreg ⟨ht.1, ht.2⟩)
      have hlog_deriv_curve : deriv (fun s => Real.log (u s (τ s))) t =
          deriv (fun s => Real.log (u s (τ t))) t +
            g.inner (τ t) (gradientFun (I := I) g (f t) (τ t))
              (mfderiv 𝓘(ℝ, ℝ) I τ t (1 : ℝ)) := by
        simpa [f] using hlog_curve
      have hlog_ratio : deriv (fun s => Real.log (u s (τ s))) t =
          derivative t / u t (τ t) := by
        have hd : HasDerivAt (fun s => u s (τ s)) (derivative t) t := hderiv t ht
        exact (hd.log (hpos t (D.regular_subset (hreg ht)) (τ t)).ne').deriv
      rw [← hlog_ratio]
      rw [hlog_deriv_curve]
    have hliYau : ∀ t ∈ Icc a b,
        -(n / 2 / t) + gradSq t ≤ timePart t := by
      intro t ht
      have ht_pos : 0 < t := lt_of_lt_of_le ha ht.1
      have hly := hly_all t (τ t) ht ht_pos
      have hq_id : liYauQuantity g f t (τ t) = gradSq t - timePart t := rfl
      have hly' : gradSq t - timePart t ≤ n / (2 * t) := by
        rw [hq_id] at hly
        exact hly
      have hn : n / (2 * t) = n / 2 / t := by
        field_simp [ht_pos.ne']
      rw [hn] at hly'
      linarith
    have hquad : ∀ t ∈ Icc a b,
        -(1 / 4) * speedSq t ≤ gradSq t + innerGV t := by
      intro t ht
      have hq := metric_inner_add_inner_ge_neg_quarter g (τ t)
        (gradientFun (I := I) g (f t) (τ t))
        (mfderiv 𝓘(ℝ, ℝ) I τ t (1 : ℝ))
      have hsp := hτ_speed t
      simp [speedSq, gradSq, innerGV, τ', hτ'_def] at hq ⊢
      nlinarith [hq, hsp]
    have hbridge := harnack_endpoint_of_li_yau_bound_abstract
      (u := fun t => u t (τ t))
      (derivative := derivative)
      (timePart := timePart)
      (gradSq := gradSq)
      (innerGV := innerGV)
      (speedSq := speedSq)
      (a := a) (b := b) (c := n / 2) (alpha := (1 : ℝ))
      ha (le_of_lt hab) hhu hderiv_cont (by
        simpa [speedSq] using continuousOn_const) hderiv hpath
      (fun t ht => by simpa using hliYau t ht)
      (fun t ht => by simpa using hquad t ht)
    have hfinal : u a (τ a) ≤ (b / a) ^ (n / 2) *
        Real.exp ((d ^ 2) / (4 * (b - a))) * u b (τ b) := by
      have hintegral : 4⁻¹ * (∫ t in a..b, speedSq t) = d ^ 2 / (4 * (b - a)) := by
        have hc : (∫ t in a..b, (d / (b - a)) ^ 2) = (d / (b - a)) ^ 2 * (b - a) := by
          simp [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
        have hpc : (fun t : ℝ => speedSq t) = fun _ : ℝ => (d / (b - a)) ^ 2 := by
          funext t
          rfl
        rw [hpc, hc]
        norm_num
        field_simp [ne_of_gt hba_pos]
      simpa [hintegral, hτa, hτb] using hbridge
    rw [hτa, hτb] at hfinal
    simpa [n] using hfinal

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem heat_solution_harnack_of_nonnegative_ricci
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    [CompactSpace M] [ConnectedSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hRic : ∀ x v, 0 ≤ ricciTensor (I := I) g x v v)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (hpde : ∀ t x, deriv (fun s => u s x) t =
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (x y : M) :
    u a x ≤ (b / a) ^ ((Module.finrank ℝ E : ℝ) / 2) *
      Real.exp ((riemannianEDist I x y).toReal ^ 2 / (4 * (b - a))) * u b y := by
  classical
  let D : RealTimeInterval := RealTimeInterval.univ 0
  let G : MetricConnectionFamily (I := I) (M := M) ℝ :=
    stationaryMetricFamily (I := I) (M := M) g
  have huOn : IsHeatOn D G u := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [D] using hu.contMDiffOn
    · exact hu.continuous.continuousOn
    · intro τ hτ
      exact hu.comp (contMDiff_const.prodMk contMDiff_id)
    · intro τ hτ x
      have hslice_cd : ContDiff ℝ ∞ (fun s => u s x) :=
        contMDiff_iff_contDiff.mp (hu.comp (contMDiff_id.prodMk contMDiff_const))
      have hder : HasDerivAt (fun s => u s x) (deriv (fun s => u s x) τ) τ :=
        (ContDiff.differentiable hslice_cd (by norm_num) τ).hasDerivAt
      have hlap : laplacianAt (I := I) G τ (u τ) x =
          Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu τ).toContMDiffMap x := by
        change laplacianAt (I := I) G τ (smoothScalarSlice (I := I) g u hu τ).toFun x =
          Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu τ).toContMDiffMap x
        rw [laplacianAt_eq_delta (I := I) G τ (smoothScalarSlice (I := I) g u hu τ).smooth
          (by rfl) x]
        rfl
      have hderiv : deriv (fun s => u s x) τ = laplacianAt (I := I) G τ (u τ) x := by
        rw [hpde τ x, ← hlap]
      convert hder.congr_deriv hderiv using 1
      simp
  simpa [D] using heat_solution_harnack_of_nonnegative_ricci_on
    (I := I) (M := M) g hEnorm hRic D u huOn (by simpa [D] using hu.contMDiffOn)
    (fun τ hτ x => hpos τ x)
    ha hab (by intro τ hτ; trivial) (by intro τ hτ; trivial) (by intro τ hτ; trivial) x y

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem heat_solution_harnack_uniform_upper_bound_of_nonnegative_ricci_on
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    [CompactSpace M] [ConnectedSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hRic : ∀ x v, 0 ≤ ricciTensor (I := I) g x v v)
    (D : RealTimeInterval)
    (u : ℝ → M → ℝ)
    (hu : IsHeatOnStationary D g u)
    (huClosed : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2) (D.carrier ×ˢ univ))
    (hpos : ∀ t : ℝ, t ∈ D.carrier → ∀ x : M, 0 < u t x)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hreg : Icc a b ⊆ D.regular)
    (hcarrier : Icc 0 b ⊆ D.carrier)
    (hslabRegular : Ioo 0 b ⊆ D.regular)
    (y₀ : M) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : M, u a x ≤ C * u b y₀ := by
  classical
  have hfcont : Continuous (fun x : M => riemannianEDist I x y₀) :=
    continuous_riemannianEDist_to (I := I) y₀
  obtain ⟨xmax, _hxm, hmax⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set M)).exists_isMaxOn
      Set.univ_nonempty hfcont.continuousOn
  let Dv : ℝ := (riemannianEDist I xmax y₀).toReal
  have hDnonneg : 0 ≤ Dv := ENNReal.toReal_nonneg
  have hbound : ∀ x : M, (riemannianEDist I x y₀).toReal ≤ Dv := by
    intro x
    have hle : riemannianEDist I x y₀ ≤ riemannianEDist I xmax y₀ :=
      hmax (Set.mem_univ x)
    have hne1 : riemannianEDist I x y₀ ≠ ⊤ := riemannianEDist_ne_top (I := I) x y₀
    have hne2 : riemannianEDist I xmax y₀ ≠ ⊤ := riemannianEDist_ne_top (I := I) xmax y₀
    exact (ENNReal.toReal_le_toReal hne1 hne2).mpr hle
  let C : ℝ := (b / a) ^ ((Module.finrank ℝ E : ℝ) / 2) *
    Real.exp (Dv ^ 2 / (4 * (b - a)))
  have hbpos : 0 < b := lt_trans ha hab
  have hba_pos : 0 < b / a := div_pos hbpos ha
  have hA_nonneg : 0 ≤ (b / a) ^ ((Module.finrank ℝ E : ℝ) / 2) := by
    exact Real.rpow_nonneg (le_of_lt hba_pos) _
  have hC_pos : 0 < C := by
    dsimp [C]
    exact mul_pos (Real.rpow_pos_of_pos hba_pos _) (Real.exp_pos _)
  refine ⟨C, hC_pos, ?_⟩
  intro x
  have hxy := heat_solution_harnack_of_nonnegative_ricci_on
    (I := I) (M := M) g hEnorm hRic D u hu huClosed hpos ha hab
    hreg hcarrier hslabRegular x y₀
  have hdD : (riemannianEDist I x y₀).toReal ^ 2 ≤ Dv ^ 2 := by
    have hd : 0 ≤ (riemannianEDist I x y₀).toReal := ENNReal.toReal_nonneg
    have hmul := mul_self_le_mul_self hd (hbound x)
    simpa [pow_two] using hmul
  have hexp_le : Real.exp ((riemannianEDist I x y₀).toReal ^ 2 / (4 * (b - a))) ≤
      Real.exp (Dv ^ 2 / (4 * (b - a))) := by
    have hba : 0 < b - a := sub_pos.mpr hab
    exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hdD (by positivity))
  have hprod_le : (b / a) ^ ((Module.finrank ℝ E : ℝ) / 2) *
        Real.exp ((riemannianEDist I x y₀).toReal ^ 2 / (4 * (b - a))) * u b y₀ ≤
      C * u b y₀ := by
    have h1 : (b / a) ^ ((Module.finrank ℝ E : ℝ) / 2) *
          Real.exp ((riemannianEDist I x y₀).toReal ^ 2 / (4 * (b - a))) ≤
        (b / a) ^ ((Module.finrank ℝ E : ℝ) / 2) *
          Real.exp (Dv ^ 2 / (4 * (b - a))) := by
      exact mul_le_mul_of_nonneg_left hexp_le hA_nonneg
    have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt (hpos b (D.regular_subset
      (hreg ⟨le_of_lt hab, le_rfl⟩)) y₀))
    simpa [C] using h2
  linarith

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem heat_solution_harnack_uniform_upper_bound_of_nonnegative_ricci
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    [CompactSpace M] [ConnectedSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hRic : ∀ x v, 0 ≤ ricciTensor (I := I) g x v v)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (hpde : ∀ t x, deriv (fun s => u s x) t =
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (y₀ : M) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : M, u a x ≤ C * u b y₀ := by
  classical
  have hfcont : Continuous (fun x : M => riemannianEDist I x y₀) :=
    continuous_riemannianEDist_to (I := I) y₀
  obtain ⟨xmax, _hxm, hmax⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set M)).exists_isMaxOn
      Set.univ_nonempty hfcont.continuousOn
  let D : ℝ := (riemannianEDist I xmax y₀).toReal
  have hDnonneg : 0 ≤ D := ENNReal.toReal_nonneg
  have hbound : ∀ x : M, (riemannianEDist I x y₀).toReal ≤ D := by
    intro x
    have hle : riemannianEDist I x y₀ ≤ riemannianEDist I xmax y₀ :=
      hmax (Set.mem_univ x)
    have hne1 : riemannianEDist I x y₀ ≠ ⊤ := riemannianEDist_ne_top (I := I) x y₀
    have hne2 : riemannianEDist I xmax y₀ ≠ ⊤ := riemannianEDist_ne_top (I := I) xmax y₀
    exact (ENNReal.toReal_le_toReal hne1 hne2).mpr hle
  let C : ℝ := (b / a) ^ ((Module.finrank ℝ E : ℝ) / 2) *
    Real.exp (D ^ 2 / (4 * (b - a)))
  have hbpos : 0 < b := lt_trans ha hab
  have hba_pos : 0 < b / a := div_pos hbpos ha
  have hA_nonneg : 0 ≤ (b / a) ^ ((Module.finrank ℝ E : ℝ) / 2) := by
    exact Real.rpow_nonneg (le_of_lt hba_pos) _
  have hC_pos : 0 < C := by
    dsimp [C]
    exact mul_pos (Real.rpow_pos_of_pos hba_pos _) (Real.exp_pos _)
  refine ⟨C, hC_pos, ?_⟩
  intro x
  have hxy := heat_solution_harnack_of_nonnegative_ricci
    (I := I) (M := M) g hEnorm hRic u hu hpos hpde ha hab x y₀
  have hdD : (riemannianEDist I x y₀).toReal ^ 2 ≤ D ^ 2 := by
    have hd : 0 ≤ (riemannianEDist I x y₀).toReal := ENNReal.toReal_nonneg
    have hmul := mul_self_le_mul_self hd (hbound x)
    simpa [pow_two] using hmul
  have hexp_le : Real.exp ((riemannianEDist I x y₀).toReal ^ 2 / (4 * (b - a))) ≤
      Real.exp (D ^ 2 / (4 * (b - a))) := by
    have hba : 0 < b - a := sub_pos.mpr hab
    exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hdD (by positivity))
  have hprod_le : (b / a) ^ ((Module.finrank ℝ E : ℝ) / 2) *
        Real.exp ((riemannianEDist I x y₀).toReal ^ 2 / (4 * (b - a))) * u b y₀ ≤
      C * u b y₀ := by
    have h1 : (b / a) ^ ((Module.finrank ℝ E : ℝ) / 2) *
          Real.exp ((riemannianEDist I x y₀).toReal ^ 2 / (4 * (b - a))) ≤
        (b / a) ^ ((Module.finrank ℝ E : ℝ) / 2) *
          Real.exp (D ^ 2 / (4 * (b - a))) := by
      exact mul_le_mul_of_nonneg_left hexp_le hA_nonneg
    have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt (hpos b y₀))
    simpa [C] using h2
  linarith

end DifferentialGeometry.Analysis.Parabolic.Harnack

end
