import DifferentialGeometry.Analysis.Parabolic.Moser.LogEnergy
import DifferentialGeometry.Analysis.Calculus.TimeJetCommute
import DifferentialGeometry.Geometry.Operator.Gradient
import DifferentialGeometry.Geometry.Operator.Operators
import DifferentialGeometry.Geometry.Operator.VossWeyl
import DifferentialGeometry.Geometry.Operator.LaplacianBridge
import DifferentialGeometry.Geometry.Operator.NormGradSq
import DifferentialGeometry.Geometry.Operator.HessianTraceInequality
import DifferentialGeometry.Geometry.Curvature.Bochner.BochnerConcrete
import DifferentialGeometry.Analysis.Calculus.Extrema
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Weak
import DifferentialGeometry.Geometry.Curvature.Realized.Operators
import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamily
import DifferentialGeometry.Geometry.Connection.LeviCivita.KoszulFormula
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.TangentAction
import DifferentialGeometry.Analysis.Integration.Measure.Invariance
import DifferentialGeometry.Analysis.Parabolic.ScalarTimeDependent

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Harnack

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless] [T2Space M]

private abbrev deltaLegacy
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ f) : M → ℝ :=
  Δ_g (I := I) g ⟨f, hf⟩

private theorem deltaLegacy_contMDiff
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ f) :
    ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ (deltaLegacy (I := I) g hf) :=
  Δ_g_contMDiff (I := I) g ⟨f, hf⟩

def liYauQuantity (g : SmoothRiemannianMetric I M) (f : ℝ → M → ℝ) (t : ℝ) (x : M) : ℝ :=
  g.inner x (gradientFun (I := I) g (f t) x) (gradientFun (I := I) g (f t) x) -
    deriv (fun s : ℝ => f s x) t

def smoothScalarSliceOn
    {D : RealTimeInterval}
    (g : SmoothRiemannianMetric I M)
    (u : ℝ → M → ℝ)
    (hu : ∀ t : ℝ, t ∈ D.carrier → ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t))
    (t : ℝ) (ht : t ∈ D.carrier) : SmoothScalar g where
  toFun := fun x => u t x
  smooth := hu t ht

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
@[simp] lemma smoothScalarSliceOn_toFun
    {D : RealTimeInterval}
    (g : SmoothRiemannianMetric I M)
    (u : ℝ → M → ℝ)
    (hu : ∀ t : ℝ, t ∈ D.carrier → ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t))
    (t : ℝ) (ht : t ∈ D.carrier) (x : M) :
    (smoothScalarSliceOn (I := I) g u hu t ht).toFun x = u t x := rfl

theorem heatSolution_log_evolution
    {D : RealTimeInterval}
    (g : SmoothRiemannianMetric I M)
    (u : ℝ → M → ℝ)
    (hslice : ∀ t : ℝ, t ∈ D.carrier → ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t))
    (hlogslice : ∀ t : ℝ, t ∈ D.carrier → ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y : M => Real.log (u t y)))
    (hpos : ∀ t : ℝ, t ∈ D.carrier → ∀ x : M, 0 < u t x)
    {t : ℝ} (ht : t ∈ D.regular) {x : M}
    (hpde : HasDerivAt (fun s => u s x)
      (deltaLegacy (I := I) g (hslice t (D.regular_subset ht)) x) t) :
    deriv (fun s => Real.log (u s x)) t =
      deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht)) x +
      g.inner x
        (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
        (gradientFun (I := I) g (fun y => Real.log (u t y)) x) := by
  classical
  let ut : SmoothScalar g :=
    smoothScalarSliceOn (I := I) g u hslice t (D.regular_subset ht)
  let logut : SmoothScalar g :=
    smoothScalarSliceOn (I := I) g (fun s y => Real.log (u s y)) hlogslice
      t (D.regular_subset ht)
  have htime_deriv :
      deriv (fun s => Real.log (u s x)) t =
        (u t x)⁻¹ * deriv (fun s => u s x) t := by
    have hpde' : HasDerivAt (fun s => u s x) (deriv (fun s => u s x) t) t :=
      hpde.congr_deriv hpde.deriv.symm
    exact ((Real.hasDerivAt_log (hpos t (D.regular_subset ht) x).ne').comp t hpde').deriv
  have hgrad : MDiffAt
      (T% fun y : M => gradientFun (I := I) g ut.toFun y) x :=
    (grad_g (I := I) g ut.toContMDiffMap).mdifferentiable x
  have hlap_raw := laplacian_log (I := I)
    (LeviCivita (I := I) g) g
    (fun y => ut.smooth.mdifferentiable (by simp) y)
    (fun y => hpos t (D.regular_subset ht) y) hgrad
  have hlap :
      Δ_g (I := I) g logut.toContMDiffMap x =
        (u t x)⁻¹ * Δ_g (I := I) g ut.toContMDiffMap x -
          (u t x ^ 2)⁻¹ *
            g.inner x (gradientFun (I := I) g ut.toFun x)
              (gradientFun (I := I) g ut.toFun x) := by
    unfold SmoothScalar.toContMDiffMap
    rw [← laplacian_levi_eq (I := I) g logut.smooth x,
      ← laplacian_levi_eq (I := I) g ut.smooth x]
    simpa only [ut, logut, smoothScalarSliceOn_toFun] using hlap_raw
  have hloggrad := Moser.inner_gradientFun_log_self (I := I) g
    (ut.smooth.mdifferentiable (by simp) x) (hpos t (D.regular_subset ht) x)
  have hloggrad' :
      g.inner x
          (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
          (gradientFun (I := I) g (fun y => Real.log (u t y)) x) =
        (u t x ^ 2)⁻¹ *
          g.inner x (gradientFun (I := I) g ut.toFun x)
            (gradientFun (I := I) g ut.toFun x) := by
    simpa only [ut, smoothScalarSliceOn_toFun] using hloggrad
  calc
    deriv (fun s => Real.log (u s x)) t
        = (u t x)⁻¹ * deriv (fun s => u s x) t := htime_deriv
    _ = (u t x)⁻¹ * Δ_g (I := I) g ut.toContMDiffMap x := by
      rw [hpde.deriv]
      rfl
    _ = Δ_g (I := I) g logut.toContMDiffMap x +
        g.inner x
          (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
          (gradientFun (I := I) g (fun y => Real.log (u t y)) x) := by
      rw [hlap, hloggrad']
      ring

theorem liYauQuantity_eq_neg_laplacian_log
    {D : RealTimeInterval}
    (g : SmoothRiemannianMetric I M)
    (u : ℝ → M → ℝ)
    (hslice : ∀ t : ℝ, t ∈ D.carrier → ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t))
    (hlogslice : ∀ t : ℝ, t ∈ D.carrier → ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y : M => Real.log (u t y)))
    (hpos : ∀ t : ℝ, t ∈ D.carrier → ∀ x : M, 0 < u t x)
    {t : ℝ} (ht : t ∈ D.regular) {x : M}
    (hpde : HasDerivAt (fun s => u s x)
      (deltaLegacy (I := I) g (hslice t (D.regular_subset ht)) x) t) :
    g.inner x
          (gradientFun (I := I) g (fun y : M => Real.log (u t y)) x)
          (gradientFun (I := I) g (fun y : M => Real.log (u t y)) x) -
        deriv (fun s : ℝ => Real.log (u s x)) t =
      -deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht)) x := by
  have h := heatSolution_log_evolution (I := I) (M := M) (D := D) g u hslice hlogslice hpos ht hpde
  rw [h]
  ring

theorem liYauQuantity_eq_neg_laplacian
    {D : RealTimeInterval}
    (g : SmoothRiemannianMetric I M)
    (u : ℝ → M → ℝ)
    (hslice : ∀ t : ℝ, t ∈ D.carrier → ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t))
    (hlogslice : ∀ t : ℝ, t ∈ D.carrier → ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y : M => Real.log (u t y)))
    (hpos : ∀ t : ℝ, t ∈ D.carrier → ∀ x : M, 0 < u t x)
    {t : ℝ} (ht : t ∈ D.regular) {x : M}
    (hpde : HasDerivAt (fun s => u s x)
      (deltaLegacy (I := I) g (hslice t (D.regular_subset ht)) x) t) :
    liYauQuantity g (fun τ y => Real.log (u τ y)) t x =
      -deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht)) x := by
  simpa [liYauQuantity] using
    liYauQuantity_eq_neg_laplacian_log (I := I) (M := M) (D := D) g u hslice hlogslice hpos ht hpde

omit [T2Space M] in
theorem gradientFun_time_deriv
    {D : RealTimeInterval}
    (g : SmoothRiemannianMetric I M)
    (u : ℝ → M → ℝ)
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2) (D.regular ×ˢ univ))
    {t : ℝ} (ht : t ∈ D.regular) {x : M} :
    HasDerivAt (fun s : ℝ => gradientFun (I := I) g (u s) x)
      (gradientFun (I := I) g (fun y : M => deriv (fun s : ℝ => u s y) t) x) t := by
  classical
  set α : M := x with hα
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I) α]
    exact mem_chart_source H α
  have hxsrc : x ∈ (chartAt H α).source := by
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I) α] at hxbase
    exact hxbase
  have hxextsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I) α]
    exact hxsrc
  have hxtarget : (extChartAt I α) x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxextsrc
  have hxint : (extChartAt I α) x ∈ interior (extChartAt I α).target := by
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
    exact hxtarget
  have hΦ : ContDiffAt ℝ ∞
      (fun r : ℝ × E => scalarOnE (I := I) α (u r.1) r.2) (t, (extChartAt I α) x) := by
    have hua : ContMDiffAt ((𝓘(ℝ, ℝ).prod I)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => u p.1 p.2) (t, x) := by
      exact hu.contMDiffAt ((IsOpen.prod D.regular_isOpen isOpen_univ).mem_nhds ⟨ht, trivial⟩)
    have hiff := contMDiffAt_iff (I := (𝓘(ℝ, ℝ).prod I)) (I' := 𝓘(ℝ, ℝ))
      (n := ∞) (f := fun p : ℝ × M => u p.1 p.2) (x := (t, x))
    rcases hiff.mp hua with ⟨_, hcd⟩
    have hcd' : ContDiffWithinAt ℝ ∞
        (fun r : ℝ × E => u r.1 ((extChartAt I α).symm r.2))
        Set.univ (t, (extChartAt I α) x) := by
      have hprod : extChartAt ((𝓘(ℝ, ℝ).prod I)) (t, x) =
          (extChartAt 𝓘(ℝ, ℝ) t).prod (extChartAt I x) :=
        extChartAt_prod (x := (t, x))
      have hself : extChartAt 𝓘(ℝ, ℝ) (u t x) = PartialEquiv.refl ℝ := by
        simp [extChartAt]
      have hcomp_eq : (extChartAt 𝓘(ℝ, ℝ) (u t x) ∘ (fun p : ℝ × M => u p.1 p.2) ∘
          (extChartAt ((𝓘(ℝ, ℝ).prod I)) (t, x)).symm) =
          (fun r : ℝ × E => u r.1 ((extChartAt I α).symm r.2)) := by
        funext r
        simp only [hself, hprod, Function.comp_def, α,
          PartialEquiv.prod_coe_symm, extChartAt_coe_symm,
          modelWithCornersSelf_coe_symm]
        change u r.1 ((extChartAt I α).symm r.2) = u r.1 ((extChartAt I α).symm r.2)
        rfl
      have hrange : range ((𝓘(ℝ, ℝ).prod I)) = Set.univ := by
        have hI : range I = Set.univ := ModelWithCorners.range_eq_univ I
        apply Set.Subset.antisymm
        · intro y hy
          trivial
        · intro y hy
          have hy2 : y.2 ∈ range I := by
            rw [hI]
            trivial
          rcases hy2 with ⟨x₂, hx₂⟩
          exact ⟨(y.1, x₂), by simp [hx₂]⟩
      rw [hcomp_eq] at hcd
      have hbase : (extChartAt ((𝓘(ℝ, ℝ).prod I)) (t, x)) (t, x) =
          (t, (extChartAt I α) x) := by
        simp [α]
      rw [hrange, hbase] at hcd
      exact hcd
    exact (contDiffWithinAt_univ.mp hcd')
  have hpd : ∀ j : Fin (Module.finrank ℝ E),
      HasDerivAt
        (fun s : ℝ => partialDeriv (E := E) j (scalarOnE (I := I) α (u s))
          ((extChartAt I α) x))
        (partialDeriv (E := E) j (scalarOnE (I := I) α
          (fun y : M => deriv (fun s : ℝ => u s y) t)) ((extChartAt I α) x)) t := by
    intro j
    have hc := fderiv_deriv_hasDerivAt_comm
      (fun r : ℝ × E => scalarOnE (I := I) α (u r.1) r.2) t
      ((extChartAt I α) x) (chartModelBasis E j) hΦ
    have hc1 : HasDerivAt
        (fun s : ℝ => partialDeriv (E := E) j (scalarOnE (I := I) α (u s))
          ((extChartAt I α) x))
        (fderiv ℝ (fun y : E => deriv (fun s : ℝ => scalarOnE (I := I) α (u s) y) t)
          ((extChartAt I α) x) (chartModelBasis E j)) t := by
      simpa [partialDeriv] using hc
    have hfun : (fun y : E => deriv (fun s : ℝ => scalarOnE (I := I) α (u s) y) t) =
        scalarOnE (I := I) α (fun z : M => deriv (fun s : ℝ => u s z) t) := by
      funext y
      rfl
    have hval : fderiv ℝ (fun y : E => deriv (fun s : ℝ => scalarOnE (I := I) α (u s) y) t)
          ((extChartAt I α) x) (chartModelBasis E j) =
        partialDeriv (E := E) j (scalarOnE (I := I) α
          (fun y : M => deriv (fun s : ℝ => u s y) t)) ((extChartAt I α) x) := by
      rw [hfun]
      rfl
    simpa [hval, partialDeriv] using hc1
  have hcoeff : ∀ i : Fin (Module.finrank ℝ E),
      HasDerivAt
        (fun s : ℝ => gradChartCoeff (I := I) g α (u s) i x)
        (gradChartCoeff (I := I) g α
          (fun y : M => deriv (fun s : ℝ => u s y) t) i x) t := by
    intro i
    have hsum : ∀ j : Fin (Module.finrank ℝ E),
        HasDerivAt
          (fun s : ℝ => chartInvGramMatrix (I := I) g α x i j *
            partialDeriv (E := E) j (scalarOnE (I := I) α (u s))
              ((extChartAt I α) x))
          (chartInvGramMatrix (I := I) g α x i j *
            partialDeriv (E := E) j (scalarOnE (I := I) α
              (fun y : M => deriv (fun s : ℝ => u s y) t)) ((extChartAt I α) x)) t := by
        intro j
        exact (hpd j).const_mul (chartInvGramMatrix (I := I) g α x i j)
    have hsumall : HasDerivAt
        (fun s : ℝ => ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α x i j *
            partialDeriv (E := E) j (scalarOnE (I := I) α (u s)) ((extChartAt I α) x))
        (∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α x i j *
            partialDeriv (E := E) j (scalarOnE (I := I) α
              (fun y : M => deriv (fun s : ℝ => u s y) t)) ((extChartAt I α) x)) t := by
      exact HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hsum j)
    simpa [gradChartCoeff_def] using hsumall
  have hsum2 : HasDerivAt
      (fun s : ℝ => ∑ i : Fin (Module.finrank ℝ E),
        gradChartCoeff (I := I) g α (u s) i x • chartBasisVecFiber (I := I) α i x)
      (∑ i : Fin (Module.finrank ℝ E),
        gradChartCoeff (I := I) g α (fun y : M => deriv (fun s : ℝ => u s y) t) i x •
          chartBasisVecFiber (I := I) α i x) t := by
    exact HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      (hcoeff i).smul_const (chartBasisVecFiber (I := I) α i x))
  have hcore : HasDerivAt (fun s : ℝ => gradChartLocal (I := I) g α (u s) x)
      (gradChartLocal (I := I) g α
        (fun y : M => deriv (fun s : ℝ => u s y) t) x) t := by
    simpa [gradChartLocal] using hsum2
  have hslice_mdiff_near : ∀ᶠ s in 𝓝 t, MDifferentiableAt I 𝓘(ℝ, ℝ) (u s) x := by
    filter_upwards [IsOpen.mem_nhds D.regular_isOpen ht] with s hs
    have hnhs : D.regular ×ˢ univ ∈ 𝓝 (s, x) :=
      (IsOpen.prod D.regular_isOpen isOpen_univ).mem_nhds ⟨hs, trivial⟩
    have huat : ContMDiffAt ((𝓘(ℝ, ℝ).prod I)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => u p.1 p.2) (s, x) := hu.contMDiffAt hnhs
    have hsliceAt : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (u s) x :=
      huat.comp (x := x) (contMDiffAt_const.prodMk contMDiffAt_id)
    exact ContMDiffAt.mdifferentiableAt hsliceAt (by norm_num)
  have hloc_l_near : ∀ᶠ s in 𝓝 t,
      gradientFun (I := I) g (u s) x = gradChartLocal (I := I) g α (u s) x := by
    filter_upwards [hslice_mdiff_near] with s hs
    exact (gradChartLocal_eq_gradFun (I := I) g α
      (hf := hs) hxbase hxint).symm
  have htarget_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => deriv (fun s : ℝ => u s y) t) x := by
    have hcd_slice : ContDiffAt ℝ ∞
        (fun y : E => deriv (fun s : ℝ => scalarOnE (I := I) α (u s) y) t)
        ((extChartAt I α) x) := by
      have hswap : ContDiffAt ℝ ∞ (fun p : E × ℝ => (p.2, p.1))
          ((extChartAt I α) x, t) :=
        contDiffAt_snd.prodMk contDiffAt_fst
      have hf : ContDiffAt ℝ ∞ (Function.uncurry
          (fun (y : E) => fun (s : ℝ) => scalarOnE (I := I) α (u s) y))
          ((extChartAt I α) x, t) := by
        exact hΦ.comp ((extChartAt I α) x, t) hswap
      have hg : ContDiffAt ℝ ∞ (fun _ : E => (t : ℝ)) ((extChartAt I α) x) := contDiffAt_const
      have hfd := ContDiffAt.fderiv
        (f := fun (y : E) => fun (s : ℝ) => scalarOnE (I := I) α (u s) y)
        (g := fun _ : E => (t : ℝ)) hf hg (by simp)
      have hcd0 : ContDiffAt ℝ ∞
          (fun y : E => (fderiv ℝ (fun s : ℝ => scalarOnE (I := I) α (u s) y) t) (1 : ℝ))
          ((extChartAt I α) x) := by
        simpa using
          ((ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).contDiff.contDiffAt.comp
            ((extChartAt I α) x) hfd)
      change ContDiffAt ℝ ∞
          (fun y : E => deriv (fun s : ℝ => scalarOnE (I := I) α (u s) y) t)
          ((extChartAt I α) x)
      exact hcd0
    have hpull : ContDiffAt ℝ ∞
        (scalarOnE (I := I) α (fun y : M => deriv (fun s : ℝ => u s y) t))
        ((extChartAt I α) x) := by
      simpa [scalarOnE_def] using hcd_slice
    have hua_mdiff : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun y : M => deriv (fun s : ℝ => u s y) t) x := by
      rw [contMDiffAt_iff]
      constructor
      · have hcont_pull : ContinuousAt
            (scalarOnE (I := I) α (fun y : M => deriv (fun s : ℝ => u s y) t))
            ((extChartAt I α) x) := hpull.continuousAt
        have hw_eq : (fun y : M => deriv (fun s : ℝ => u s y) t) =ᶠ[𝓝 x]
            (scalarOnE (I := I) α (fun y : M => deriv (fun s : ℝ => u s y) t)) ∘
              (extChartAt I α) := by
          rw [Filter.eventuallyEq_iff_exists_mem]
          refine ⟨(extChartAt I α).source,
            (isOpen_extChartAt_source (I := I) α).mem_nhds hxextsrc, ?_⟩
          intro y hy
          have hlinv : (extChartAt I α).symm ((extChartAt I α) y) = y :=
            (extChartAt I α).left_inv hy
          change deriv (fun s : ℝ => u s y) t =
            deriv (fun s : ℝ => u s ((extChartAt I α).symm ((extChartAt I α) y))) t
          rw [hlinv]
        exact (hcont_pull.comp (continuousAt_extChartAt α)).congr_of_eventuallyEq hw_eq
      · have hcd_w : ContDiffWithinAt ℝ ∞
            (scalarOnE (I := I) α (fun y : M => deriv (fun s : ℝ => u s y) t))
            Set.univ ((extChartAt I α) x) := hpull.contDiffWithinAt
        have hcomp_eq : (extChartAt 𝓘(ℝ, ℝ) (deriv (fun s : ℝ => u s x) t) ∘
            (fun y : M => deriv (fun s : ℝ => u s y) t) ∘
              (extChartAt I α).symm) =
            scalarOnE (I := I) α (fun y : M => deriv (fun s : ℝ => u s y) t) := by
          funext z
          simp only [Function.comp_def, extChartAt_coe_symm, α]
          change scalarOnE (I := I) α (fun y : M => deriv (fun s : ℝ => u s y) t) z =
            scalarOnE (I := I) α (fun y : M => deriv (fun s : ℝ => u s y) t) z
          rfl
        rw [hcomp_eq]
        simpa [ModelWithCorners.range_eq_univ I, α] using hcd_w
    exact hua_mdiff.mdifferentiableAt (by simp)
  have hloc_r : gradientFun (I := I) g
      (fun y : M => deriv (fun s : ℝ => u s y) t) x =
      gradChartLocal (I := I) g α (fun y : M => deriv (fun s : ℝ => u s y) t) x :=
    (gradChartLocal_eq_gradFun (I := I) g α
      (hf := htarget_mdiff) hxbase hxint).symm
  have hgoal : HasDerivAt (fun s : ℝ => gradChartLocal (I := I) g α (u s) x)
      (gradientFun (I := I) g (fun y : M => deriv (fun s : ℝ => u s y) t) x) t := by
    rw [hloc_r]
    exact hcore
  have hgoal' : HasDerivAt (fun s : ℝ => gradientFun (I := I) g (u s) x)
      (gradientFun (I := I) g (fun y : M => deriv (fun s : ℝ => u s y) t) x) t := by
    exact hgoal.congr_of_eventuallyEq hloc_l_near
  exact hgoal'

variable [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
theorem scalarOnE_jointContDiffAt
    {D : RealTimeInterval}
    (f : ℝ → M → ℝ)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2) (D.regular ×ˢ univ))
    (α : M) {t : ℝ} (ht : t ∈ D.regular) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => scalarOnE (I := I) α (f r.1) r.2) (t, y) := by
  have hU : ContMDiffOn ((𝓘(ℝ, ℝ).prod I)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2) (D.regular ×ˢ univ) := hf
  have hids : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (fun r : ℝ × E => r.1) (Set.univ ×ˢ (extChartAt I α).target) :=
    contMDiffOn_fst
  have hsym : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) I ∞
      (fun r : ℝ × E => (extChartAt I α).symm r.2)
      (Set.univ ×ˢ (extChartAt I α).target) := by
    refine (contMDiffOn_extChartAt_symm (I := I) α).comp ?_ ?_
    · exact contMDiffOn_snd
    · intro r hr
      exact hr.2
  have hsymm : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ((𝓘(ℝ, ℝ).prod I)) ∞
      (fun r : ℝ × E => (r.1, (extChartAt I α).symm r.2))
      (D.regular ×ˢ (extChartAt I α).target) := by
    refine (hids.prodMk hsym).mono ?_
    intro r hr
    exact ⟨Set.mem_univ r.1, hr.2⟩
  have hcomp : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (fun r : ℝ × E => f r.1 ((extChartAt I α).symm r.2))
      (D.regular ×ˢ (extChartAt I α).target) :=
    hU.comp hsymm (fun r hr => ⟨hr.1, trivial⟩)
  have hcd : ContDiffOn ℝ ∞
      (fun r : ℝ × E => f r.1 ((extChartAt I α).symm r.2))
      (D.regular ×ˢ (extChartAt I α).target) := by
    rw [← contMDiffOn_iff_contDiffOn, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hcomp
  have hpt : (t, y) ∈ D.regular ×ˢ (extChartAt I α).target := ⟨ht, hy⟩
  have hopen : IsOpen (D.regular ×ˢ (extChartAt I α).target) :=
    D.regular_isOpen.prod (isOpen_extChartAt_target (I := I) α)
  have hat := hcd.contDiffAt
    (hopen.mem_nhds hpt)
  simpa [scalarOnE_def] using hat

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
theorem time_deriv_slice_contMDiff
    {D : RealTimeInterval}
    (f : ℝ → M → ℝ)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2) (D.regular ×ˢ univ))
    {t : ℝ} (ht : t ∈ D.regular) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M => deriv (fun s : ℝ => f s x) t) := by
  classical
  intro x₀
  rw [contMDiffAt_iff]
  set α : M := x₀ with hα
  have hx₀target : (extChartAt I α) x₀ ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source (mem_extChartAt_source (I := I) α)
  have hΦ : ContDiffAt ℝ ∞
      (fun r : ℝ × E => scalarOnE (I := I) α (f r.1) r.2) (t, (extChartAt I α) x₀) :=
    scalarOnE_jointContDiffAt (I := I) (M := M) (D := D) f hf α ht hx₀target
  have hcd_slice : ContDiffAt ℝ ∞
      (fun y : E => deriv (fun s : ℝ => scalarOnE (I := I) α (f s) y) t)
      ((extChartAt I α) x₀) := by
    have hswap : ContDiffAt ℝ ∞ (fun p : E × ℝ => (p.2, p.1))
        ((extChartAt I α) x₀, t) :=
      contDiffAt_snd.prodMk contDiffAt_fst
    have hf' : ContDiffAt ℝ ∞ (Function.uncurry
        (fun (y : E) => fun (s : ℝ) => scalarOnE (I := I) α (f s) y))
        ((extChartAt I α) x₀, t) := by
      exact hΦ.comp ((extChartAt I α) x₀, t) hswap
    have hg : ContDiffAt ℝ ∞ (fun _ : E => (t : ℝ)) ((extChartAt I α) x₀) := contDiffAt_const
    have hfd := ContDiffAt.fderiv
      (f := fun (y : E) => fun (s : ℝ) => scalarOnE (I := I) α (f s) y)
      (g := fun _ : E => (t : ℝ)) hf' hg (by simp)
    have hcd0 : ContDiffAt ℝ ∞
        (fun y : E => (fderiv ℝ (fun s : ℝ => scalarOnE (I := I) α (f s) y) t) (1 : ℝ))
        ((extChartAt I α) x₀) := by
      simpa using
        ((ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).contDiff.contDiffAt.comp
          ((extChartAt I α) x₀) hfd)
    change ContDiffAt ℝ ∞
        (fun y : E => deriv (fun s : ℝ => scalarOnE (I := I) α (f s) y) t)
        ((extChartAt I α) x₀)
    exact hcd0
  have hpull : ContDiffAt ℝ ∞
      (scalarOnE (I := I) α (fun x : M => deriv (fun s : ℝ => f s x) t))
      ((extChartAt I α) x₀) := by
    simpa [scalarOnE_def] using hcd_slice
  constructor
  · have hcont_pull : ContinuousAt
        (scalarOnE (I := I) α (fun x : M => deriv (fun s : ℝ => f s x) t))
        ((extChartAt I α) x₀) := hpull.continuousAt
    have hw_eq : (fun x : M => deriv (fun s : ℝ => f s x) t) =ᶠ[𝓝 x₀]
        (scalarOnE (I := I) α (fun x : M => deriv (fun s : ℝ => f s x) t)) ∘
          (extChartAt I α) := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨(extChartAt I α).source,
        (isOpen_extChartAt_source (I := I) α).mem_nhds (mem_extChartAt_source (I := I) α), ?_⟩
      intro y hy
      have hlinv : (extChartAt I α).symm ((extChartAt I α) y) = y :=
        (extChartAt I α).left_inv hy
      change deriv (fun s : ℝ => f s y) t =
        deriv (fun s : ℝ => f s ((extChartAt I α).symm ((extChartAt I α) y))) t
      rw [hlinv]
    exact (hcont_pull.comp (continuousAt_extChartAt α)).congr_of_eventuallyEq hw_eq
  · have hcd_w : ContDiffWithinAt ℝ ∞
        (scalarOnE (I := I) α (fun x : M => deriv (fun s : ℝ => f s x) t))
        Set.univ ((extChartAt I α) x₀) := hpull.contDiffWithinAt
    have hcomp_eq : (extChartAt 𝓘(ℝ, ℝ) (deriv (fun s : ℝ => f s x₀) t) ∘
        (fun x : M => deriv (fun s : ℝ => f s x) t) ∘
          (extChartAt I α).symm) =
        scalarOnE (I := I) α (fun x : M => deriv (fun s : ℝ => f s x) t) := by
      funext z
      simp only [Function.comp_def, extChartAt_coe_symm, α]
      change scalarOnE (I := I) α (fun x : M => deriv (fun s : ℝ => f s x) t) z =
        scalarOnE (I := I) α (fun x : M => deriv (fun s : ℝ => f s x) t) z
      rfl
    rw [hcomp_eq]
    simpa [ModelWithCorners.range_eq_univ I, α] using hcd_w

omit [T2Space M] [SigmaCompactSpace M] in
private theorem chartLaplacianTimeDerivOn
    {D : RealTimeInterval}
    (g : SmoothRiemannianMetric I M)
    (f : ℝ → M → ℝ)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2) (D.regular ×ˢ univ))
    {t : ℝ} (ht : t ∈ D.regular) (x : M) :
    ∀ α : M, x ∈ (chartAt H α).source →
      HasDerivAt (fun s : ℝ => chartVossWeylLaplacian (I := I) g α (f s) x)
        (chartVossWeylLaplacian (I := I) g α
          (fun w : M => deriv (fun s : ℝ => f s w) t) x) t := by
  classical
  intro α hxsrc
  have hxextsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I) α]
    exact hxsrc
  have hxtarget : (extChartAt I α) x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxextsrc
  have hΦ : ∀ y : E, y ∈ (extChartAt I α).target →
      ContDiffAt ℝ ∞
        (fun r : ℝ × E => scalarOnE (I := I) α (f r.1) r.2) (t, y) :=
    fun y hy => scalarOnE_jointContDiffAt (I := I) (M := M) (D := D) f hf α ht hy
  have hpd : ∀ (j : Fin (Module.finrank ℝ E)) (y : E),
      y ∈ (extChartAt I α).target →
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
      simpa [partialDeriv] using hc
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
    simpa [hval, partialDeriv] using hc1
  have hcoeff : ∀ (i : Fin (Module.finrank ℝ E)) (y : E),
      y ∈ (extChartAt I α).target →
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
      y ∈ (extChartAt I α).target →
      HasDerivAt
        (fun s : ℝ => gradChartCoeffOnE (I := I) g α (f s) i y *
          chartDensityOnE (I := I) g α y)
        (gradChartCoeffOnE (I := I) g α
          (fun w : M => deriv (fun s : ℝ => f s w) t) i y *
          chartDensityOnE (I := I) g α y) t := by
    intro i y hy
    exact (hcoeff i y hy).mul_const (chartDensityOnE (I := I) g α y)
  have hpd_joint : ∀ (j : Fin (Module.finrank ℝ E)) (y : E),
      y ∈ (extChartAt I α).target →
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
    simpa [partialDeriv] using
      ((ContinuousLinearMap.apply ℝ ℝ (chartModelBasis E j)).contDiff.contDiffAt.comp
        (t, y) hfd)
  have hΨ : ∀ (i : Fin (Module.finrank ℝ E)) (y : E),
      y ∈ (extChartAt I α).target →
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
            ((isOpen_extChartAt_target (I := I) α).mem_nhds hy)
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
          ((isOpen_extChartAt_target (I := I) α).mem_nhds hy)
      · exact (contDiffAt_snd : ContDiffAt ℝ ∞ (fun p : ℝ × E => p.2) (t, y))
    have hprod_cd : ContDiffAt ℝ ∞
        (fun p : ℝ × E =>
          (∑ j : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α i j p.2 *
              partialDeriv (E := E) j (fun z : E => scalarOnE (I := I) α (f p.1) z) p.2) *
            chartDensityOnE (I := I) g α p.2)
        (t, y) := hsumall_cd.mul hρ
    simpa [gradChartCoeffOnE_def] using hprod_cd
  have hpartial : ∀ i : Fin (Module.finrank ℝ E),
      HasDerivAt
        (fun s : ℝ => partialDeriv (E := E) i
          (chartVossWeylIntegrand (I := I) g α (f s) i) ((extChartAt I α) x))
        (partialDeriv (E := E) i
          (chartVossWeylIntegrand (I := I) g α
            (fun w : M => deriv (fun s : ℝ => f s w) t) i) ((extChartAt I α) x)) t := by
    intro i
    have hy : (extChartAt I α) x ∈ (extChartAt I α).target := hxtarget
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
      have hh : ∀ z : E, z ∈ (extChartAt I α).target →
          deriv (fun s : ℝ =>
            gradChartCoeffOnE (I := I) g α (f s) i z * chartDensityOnE (I := I) g α z) t =
            gradChartCoeffOnE (I := I) g α
              (fun w : M => deriv (fun s : ℝ => f s w) t) i z * chartDensityOnE (I := I) g α z := by
        intro z hz
        exact (hint i z hz).deriv
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨(extChartAt I α).target, ?_, ?_⟩
      · exact (isOpen_extChartAt_target (I := I) α).mem_nhds hxtarget
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

theorem liYauQuantity_evolution_identity
    [NeZero (Module.finrank ℝ E)]
    {D : RealTimeInterval}
    (g : SmoothRiemannianMetric I M)
    (u : ℝ → M → ℝ)
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2) (D.regular ×ˢ univ))
    (hslice : ∀ t : ℝ, t ∈ D.carrier → ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t))
    (hlogslice : ∀ t : ℝ, t ∈ D.carrier → ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y : M => Real.log (u t y)))
    (hpos : ∀ t : ℝ, t ∈ D.carrier → ∀ x : M, 0 < u t x)
    (hpde : ∀ t : ℝ, (ht : t ∈ D.regular) → ∀ x : M,
      HasDerivAt (fun s => u s x)
        (deltaLegacy (I := I) g (hslice t (D.regular_subset ht)) x) t)
    (hqslice : ∀ t : ℝ, t ∈ D.regular → ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y : M => liYauQuantity g (fun σ z => Real.log (u σ z)) t y))
    {t : ℝ} (ht : t ∈ D.regular) (x : M) :
    deriv (fun s => liYauQuantity g (fun τ y => Real.log (u τ y)) s x) t -
        deltaLegacy (I := I) g (hqslice t ht) x =
      2 * g.inner x
            (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
            (gradientFun (I := I) g (fun y => liYauQuantity g (fun σ z => Real.log
              (u σ z)) t y) x) -
        2 * chartHessFrobeniusSq (I := I) g (fun y => Real.log (u t y)) x -
        2 * ricciTensor (I := I) g x
            (gradFun (I := I) g (fun y => Real.log (u t y)) x)
            (gradFun (I := I) g (fun y => Real.log (u t y)) x) := by
  classical
  let f : ℝ → M → ℝ := fun τ y => Real.log (u τ y)
  have hlog' : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2) (D.regular ×ˢ univ) := by
    intro p hp
    have hnh : D.regular ×ˢ univ ∈ 𝓝 p :=
      (IsOpen.prod D.regular_isOpen isOpen_univ).mem_nhds ⟨hp.1, trivial⟩
    have hlogAt : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => Real.log (u p.1 p.2)) p :=
      (Real.contDiffAt_log.2 (hpos p.1 (D.regular_subset hp.1) p.2).ne').comp_contMDiffAt
        (x := p) (hu.contMDiffAt hnh)
    simpa [f] using hlogAt.contMDiffWithinAt
  let q : ℝ → M → ℝ := fun τ y => liYauQuantity g f τ y
  have hqid : ∀ (τ : ℝ) (hτ : τ ∈ D.regular) (y : M),
      q τ y = -deltaLegacy (I := I) g (hlogslice τ (D.regular_subset hτ)) y :=
    fun τ hτ y => liYauQuantity_eq_neg_laplacian (I := I) (M := M)
      (D := D) g u hslice hlogslice hpos hτ (hpde τ hτ y)
  have hftslice : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => deriv (fun s : ℝ => f s y) t) :=
    time_deriv_slice_contMDiff (I := I) (M := M) (D := D) f hlog' ht
  set α : M := x with hα
  have hxsrc : x ∈ (chartAt H α).source := mem_chart_source H α
  have hxextsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I) α]
    exact hxsrc
  have hxtarget : (extChartAt I α) x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxextsrc
  have hΦ : ∀ y : E, y ∈ (extChartAt I α).target →
      ContDiffAt ℝ ∞
        (fun r : ℝ × E => scalarOnE (I := I) α (f r.1) r.2) (t, y) :=
    fun y hy => scalarOnE_jointContDiffAt (I := I) (M := M) (D := D) f hlog' α ht hy
  have hgoal_chart : HasDerivAt
      (fun s : ℝ => chartVossWeylLaplacian (I := I) g α (f s) x)
      (chartVossWeylLaplacian (I := I) g α
        (fun w : M => deriv (fun s : ℝ => f s w) t) x) t :=
    chartLaplacianTimeDerivOn (I := I) (M := M) (D := D) g f hlog' ht x α hxsrc
  have hq_chart_eq : (fun s : ℝ => q s x) =ᶠ[𝓝 t]
      fun s : ℝ => -chartVossWeylLaplacian (I := I) g α (f s) x := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨D.regular, IsOpen.mem_nhds D.regular_isOpen ht, ?_⟩
    intro s hs
    have hqid_s := hqid s hs x
    have hvw : deltaLegacy (I := I) g (hlogslice s (D.regular_subset hs)) x =
        chartVossWeylLaplacian (I := I) g α (f s) x :=
      voss_weyl_laplacian_formula_pointwise (I := I) g α
        (hlogslice s (D.regular_subset hs)) hxsrc
    change q s x = -chartVossWeylLaplacian (I := I) g α (f s) x
    rw [← hvw]
    exact hqid_s
  have hdq_has : HasDerivAt (fun s : ℝ => q s x)
      (-(chartVossWeylLaplacian (I := I) g α (fun w : M => deriv (fun s : ℝ => f s w) t) x)) t := by
    exact hgoal_chart.neg.congr_of_eventuallyEq hq_chart_eq
  have hdq : deriv (fun s : ℝ => q s x) t =
      -chartVossWeylLaplacian (I := I) g α (fun w : M => deriv (fun s : ℝ => f s w) t) x :=
    hdq_has.deriv
  have hdq' : deriv (fun s : ℝ => q s x) t = -deltaLegacy (I := I) g hftslice x := by
    have hchart_eq : chartVossWeylLaplacian (I := I) g α
        (fun w : M => deriv (fun s : ℝ => f s w) t) x = deltaLegacy (I := I) g hftslice x := by
      exact (voss_weyl_laplacian_formula_pointwise (I := I) g α hftslice hxsrc).symm
    exact hdq.trans (congrArg Neg.neg hchart_eq)
  have hdq_laplacian : deltaLegacy (I := I) g (hqslice t ht) x =
      -deltaLegacy (I := I) g (deltaLegacy_contMDiff (I := I) g (hlogslice t
        (D.regular_subset ht))) x := by
    have heq : (fun y : M => liYauQuantity g f t y) =ᶠ[𝓝 x]
        (fun y : M => -deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht)) y) := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨Set.univ, Filter.univ_mem, ?_⟩
      intro y hy
      exact hqid t ht y
    have hneg : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun y : M => -deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht)) y) :=
      ContMDiff.neg (deltaLegacy_contMDiff (I := I) g (hlogslice t (D.regular_subset ht)))
    have hcongr := Δ_g_congr_of_eventuallyEq (I := I) g
      (hqslice t ht) hneg heq
    unfold deltaLegacy
    rw [hcongr]
    exact Δ_g_neg (I := I) g (deltaLegacy_contMDiff (I := I) g (hlogslice t
      (D.regular_subset ht))) (x := x)
  have hheq : ∀ y, deriv (fun s : ℝ => f s y) t -
      deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht)) y =
      normGradSqFun (I := I) g (fun z : M => Real.log (u t z)) y := by
    intro y
    have hle := heatSolution_log_evolution (I := I) (M := M)
      (D := D) g u hslice hlogslice hpos ht (hpde t ht y)
    have hle' : deriv (fun s : ℝ => f s y) t =
        deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht)) y +
          g.inner y (gradientFun (I := I) g (f t) y) (gradientFun (I := I) g (f t) y) := by
      simpa [f] using hle
    have hnorm : g.inner y (gradientFun (I := I) g (f t) y) (gradientFun (I := I) g (f t) y) =
        normGradSqFun (I := I) g (fun z : M => Real.log (u t z)) y := by
      have hvec : ∀ h : M → ℝ, gradientFun (I := I) g h y = gradFun (I := I) g h y := by
        intro h
        apply (metricFlatEquiv (I := I) g y).injective
        ext w
        change g.inner y (gradientFun (I := I) g h y) w = g.inner y (gradFun (I := I) g h y) w
        rw [inner_gradientFun (I := I) g h y w]
        rw [inner_gradFun (I := I) g h y w]
      have hlogeq : (fun z : M => Real.log (u t z)) = f t := rfl
      rw [normGradSqFun, hlogeq, hvec (f t)]
    have hle'' : deriv (fun s : ℝ => f s y) t =
        deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht)) y +
          normGradSqFun (I := I) g (fun z : M => Real.log (u t z)) y := by
      rw [← hnorm]
      exact hle'
    linarith
  have hmain : deriv (fun s : ℝ => q s x) t -
      deltaLegacy (I := I) g (hqslice t ht) x =
      -deltaLegacy (I := I) g (normGradSqFun_contMDiff (I := I) g
        (hlogslice t (D.regular_subset ht))) x := by
    rw [hdq', hdq_laplacian]
    have hsub_fun : (fun y : M => deriv (fun s : ℝ => f s y) t -
          deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht)) y) =ᶠ[𝓝 x]
        (fun y : M => normGradSqFun (I := I) g (fun z : M => Real.log (u t z)) y) := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨Set.univ, Filter.univ_mem, ?_⟩
      intro y hy
      exact hheq y
    have hΔsub : deltaLegacy (I := I) g
        (hftslice.sub (deltaLegacy_contMDiff (I := I) g (hlogslice t (D.regular_subset ht)))) x =
        deltaLegacy (I := I) g hftslice x -
          deltaLegacy (I := I) g (deltaLegacy_contMDiff (I := I) g (hlogslice t
            (D.regular_subset ht))) x := by
      have h1 := Δ_g_add (I := I) g ⟨_, hftslice⟩
        ⟨_, ContMDiff.neg
          (deltaLegacy_contMDiff (I := I) g (hlogslice t (D.regular_subset ht)))⟩ x
      have h2 := Δ_g_neg (I := I) g (deltaLegacy_contMDiff (I := I) g (hlogslice t
        (D.regular_subset ht))) (x := x)
      have hsub_eq : (fun y : M => deriv (fun s : ℝ => f s y) t -
            deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht)) y) =ᶠ[𝓝 x]
          (fun y : M => deriv (fun s : ℝ => f s y) t +
            -(deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht)) y)) := by
        rw [Filter.eventuallyEq_iff_exists_mem]
        refine ⟨Set.univ, Filter.univ_mem, ?_⟩
        intro y hy
        ring
      have hbridge := Δ_g_congr_of_eventuallyEq (I := I) g
        (hftslice.sub (deltaLegacy_contMDiff (I := I) g (hlogslice t (D.regular_subset ht))))
        (hftslice.add (ContMDiff.neg (deltaLegacy_contMDiff (I := I) g (hlogslice t
          (D.regular_subset ht)))))
        hsub_eq
      unfold deltaLegacy
      rw [hbridge]
      change Δ_g (I := I) g
          (⟨_, hftslice⟩ + ⟨_, ContMDiff.neg
            (deltaLegacy_contMDiff (I := I) g (hlogslice t (D.regular_subset ht)))⟩) x = _
      rw [h1, h2]
      ring
    have hΔnorm : deltaLegacy (I := I) g
        (hftslice.sub (deltaLegacy_contMDiff (I := I) g (hlogslice t (D.regular_subset ht)))) x =
        deltaLegacy (I := I) g (normGradSqFun_contMDiff (I := I) g
          (hlogslice t (D.regular_subset ht))) x :=
      Δ_g_congr_of_eventuallyEq (I := I) g
        (hftslice.sub (deltaLegacy_contMDiff (I := I) g (hlogslice t (D.regular_subset ht))))
        (normGradSqFun_contMDiff (I := I) g (hlogslice t (D.regular_subset ht))) hsub_fun
    have hstep : deltaLegacy (I := I) g hftslice x -
        deltaLegacy (I := I) g (deltaLegacy_contMDiff (I := I) g (hlogslice t
          (D.regular_subset ht))) x =
        deltaLegacy (I := I) g (normGradSqFun_contMDiff (I := I) g
          (hlogslice t (D.regular_subset ht))) x :=
      hΔsub.symm.trans hΔnorm
    linarith
  have hbochner := bochner_pointwise_concrete_metric_unconditional (I := I) g
    (hlogslice t (D.regular_subset ht)) x
  have hvecg : ∀ h : M → ℝ, gradientFun (I := I) g h x = gradFun (I := I) g h x := by
    intro h
    apply (metricFlatEquiv (I := I) g x).injective
    ext w
    change g.inner x (gradientFun (I := I) g h x) w = g.inner x (gradFun (I := I) g h x) w
    rw [inner_gradientFun (I := I) g h x w]
    rw [inner_gradFun (I := I) g h x w]
  have hgrad : 2 * g.inner x
        (gradFun (I := I) g (fun y => Real.log (u t y)) x)
        (gradFun (I := I) g (fun y => liYauQuantity g (fun σ z => Real.log (u σ z)) t y) x) =
      2 * g.inner x (gradFun (I := I) g (f t) x)
         (gradFun (I := I) g (fun y => -deltaLegacy (I := I) g (hlogslice t
           (D.regular_subset ht)) y) x) := by
    simp [f, q, hqid t ht]
  have hmain' : deriv (fun s : ℝ => q s x) t -
      deltaLegacy (I := I) g (hqslice t ht) x =
      -2 * chartHessFrobeniusSq (I := I) g (fun y : M => Real.log (u t y)) x -
        2 * ricciTensor (I := I) g x
          (gradFun (I := I) g (fun y : M => Real.log (u t y)) x)
          (gradFun (I := I) g (fun y : M => Real.log (u t y)) x) -
        2 * g.inner x (gradFun (I := I) g (fun y : M => Real.log (u t y)) x)
          (gradFun (I := I) g (deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht))) x) := by
    unfold deltaLegacy at hmain ⊢
    rw [hmain, hbochner]
    ring
  rw [hvecg (fun y : M => Real.log (u t y))]
  rw [hvecg (fun y : M => liYauQuantity g (fun σ z => Real.log (u σ z)) t y)]
  rw [hgrad]
  rw [hmain']
  have hinner_eq : 2 * g.inner x (gradFun (I := I) g (f t) x)
        (gradFun (I := I) g (fun y : M => -deltaLegacy (I := I) g (hlogslice t
          (D.regular_subset ht)) y) x) =
      -2 * g.inner x (gradFun (I := I) g (fun y : M => Real.log (u t y)) x)
        (gradFun (I := I) g (deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht))) x) := by
    have hfun : (f t) = (fun y : M => Real.log (u t y)) := by
      funext y
      rfl
    have hgradneg : gradFun (I := I) g
        (fun y : M => -deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht)) y) x =
        -gradFun (I := I) g (deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht))) x := by
      have hneg : gradientFun (I := I) g
          (fun y : M => -deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht)) y) x =
          -gradientFun (I := I) g (deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht))) x :=
        gradientFun_neg g
          ((deltaLegacy_contMDiff (I := I) g (hlogslice t
            (D.regular_subset ht))).mdifferentiableAt (by simp))
      calc
        gradFun (I := I) g
            (fun y : M => -deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht)) y) x
            = gradientFun (I := I) g
                (fun y : M => -deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht)) y) x :=
              (hvecg (fun y : M => -deltaLegacy (I := I) g (hlogslice t
                (D.regular_subset ht)) y)).symm
        _ = -gradientFun (I := I) g (deltaLegacy (I := I) g (hlogslice t
          (D.regular_subset ht))) x := hneg
        _ = -gradFun (I := I) g (deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht))) x := by
              rw [hvecg (deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht)))]
    rw [hfun, hgradneg]
    rw [map_neg]
    ring
  rw [hinner_eq]
  ring

theorem liYauQuantity_evolution_inequality
    [NeZero (Module.finrank ℝ E)]
    {D : RealTimeInterval}
    (g : SmoothRiemannianMetric I M) {K : ℝ}
    (hK : 0 ≤ K)
    (hRic : ∀ x v, -K * g.inner x v v ≤ ricciTensor (I := I) g x v v)
    (u : ℝ → M → ℝ)
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2) (D.regular ×ˢ univ))
    (hslice : ∀ t : ℝ, t ∈ D.carrier → ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t))
    (hlogslice : ∀ t : ℝ, t ∈ D.carrier → ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y : M => Real.log (u t y)))
    (hpos : ∀ t : ℝ, t ∈ D.carrier → ∀ x : M, 0 < u t x)
    (hpde : ∀ t : ℝ, (ht : t ∈ D.regular) → ∀ x : M,
      HasDerivAt (fun s => u s x)
        (deltaLegacy (I := I) g (hslice t (D.regular_subset ht)) x) t)
    (hqslice : ∀ t : ℝ, t ∈ D.regular → ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y : M => liYauQuantity g (fun σ z => Real.log (u σ z)) t y))
    {t : ℝ} (ht : t ∈ D.regular) (x : M) :
    deriv (fun s => liYauQuantity g (fun τ y => Real.log (u τ y)) s x) t -
        deltaLegacy (I := I) g (hqslice t ht) x ≤
      2 * g.inner x
            (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
            (gradientFun (I := I) g (fun y => liYauQuantity g (fun σ z => Real.log
              (u σ z)) t y) x) -
        (2 / (Module.finrank ℝ E : ℝ)) *
          (liYauQuantity g (fun σ z => Real.log (u σ z)) t x)^2 +
        2 * K * g.inner x
            (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
            (gradientFun (I := I) g (fun y => Real.log (u t y)) x) := by
  classical
  let logut : M → ℝ := fun y => Real.log (u t y)
  have hvecg : ∀ h : M → ℝ, gradientFun (I := I) g h x = gradFun (I := I) g h x := by
    intro h
    apply (metricFlatEquiv (I := I) g x).injective
    ext w
    change g.inner x (gradientFun (I := I) g h x) w = g.inner x (gradFun (I := I) g h x) w
    rw [inner_gradientFun (I := I) g h x w]
    rw [inner_gradFun (I := I) g h x w]
  have hid := liYauQuantity_evolution_identity (I := I) (M := M)
    (D := D) g u hu hslice hlogslice hpos hpde hqslice ht x
  have htrace0 := laplacian_sq_le_dim_mul_hessianFrobeniusSq_of_boundaryless (I := I) g
    (hlogslice t (D.regular_subset ht)) x
  have hn : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  have hle0 : (deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht)) x)^2 ≤
      chartHessFrobeniusSq (I := I) g logut x *
        (Module.finrank ℝ E : ℝ) := by
    rw [mul_comm] at htrace0
    exact htrace0
  have hdiv : (deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht)) x)^2 /
        (Module.finrank ℝ E : ℝ) ≤ chartHessFrobeniusSq (I := I) g logut x := by
    exact (div_le_iff₀ hn).2 hle0
  have htrace' : -2 * chartHessFrobeniusSq (I := I) g logut x ≤
      -(2 / (Module.finrank ℝ E : ℝ)) *
        (deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht)) x)^2 := by
    have hstep : -2 * chartHessFrobeniusSq (I := I) g logut x ≤
        -2 * ((deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht)) x)^2 /
          (Module.finrank ℝ E : ℝ)) := by
      nlinarith [hdiv]
    have hring : -2 * ((deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht)) x)^2 /
          (Module.finrank ℝ E : ℝ)) =
        -(2 / (Module.finrank ℝ E : ℝ)) *
          (deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht)) x)^2 := by
      ring_nf
    rwa [← hring]
  have hRic' : -2 * ricciTensor (I := I) g x (gradFun (I := I) g logut x) (gradFun
    (I := I) g logut x) ≤
      2 * K * g.inner x (gradientFun (I := I) g logut x) (gradientFun (I := I) g logut x) := by
    have hr := hRic x (gradFun (I := I) g logut x)
    have hin : g.inner x (gradientFun (I := I) g logut x) (gradientFun (I := I) g logut x) =
        g.inner x (gradFun (I := I) g logut x) (gradFun (I := I) g logut x) := by
      rw [hvecg logut]
    nlinarith [hr, hin]
  have hqsq : (liYauQuantity g (fun σ z => Real.log (u σ z)) t x)^2 =
      (deltaLegacy (I := I) g (hlogslice t (D.regular_subset ht)) x)^2 := by
    have hqid := liYauQuantity_eq_neg_laplacian (I := I) (M := M)
      (D := D) g u hslice hlogslice hpos ht (hpde t ht x)
    rw [hqid]
    ring
  rw [hid]
  rw [hqsq]
  nlinarith [htrace', hRic']

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem partialDeriv_joint_contDiffAt
    (Φ : ℝ → E → ℝ)
    {t₀ : ℝ} {y₀ : E}
    (hΦ : ContDiffAt ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2) (t₀, y₀))
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ ∞
      (fun p : ℝ × E => partialDeriv (E := E) i (fun z : E => Φ p.1 z) p.2)
      (t₀, y₀) := by
  classical
  have hfd := ContDiffAt.fderiv
    (m := (⊤ : ℕ∞))
    (f := fun p : ℝ × E => fun z : E => Φ p.1 z)
    (g := fun p : ℝ × E => p.2) (by
      change ContDiffAt ℝ ∞ (fun q : (ℝ × E) × E => Φ q.1.1 q.2) ((t₀, y₀), y₀)
      exact hΦ.comp ((t₀, y₀), y₀) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    ) contDiffAt_snd (by simp)
  have happly : ContDiffAt ℝ ∞
      (fun p : ℝ × E => (fderiv ℝ (fun z : E => Φ p.1 z) p.2) (chartModelBasis E i))
      (t₀, y₀) := by
    let evalMap : (E →L[ℝ] ℝ) →L[ℝ] ℝ :=
      { toFun := fun L => L (chartModelBasis E i)
        map_add' := by intro L M; rfl
        map_smul' := by intro a L; rfl }
    have hev : ContDiffAt ℝ ∞
        (fun p : ℝ × E => evalMap (fderiv ℝ (fun z : E => Φ p.1 z) p.2)) (t₀, y₀) :=
      evalMap.contDiff.contDiffAt.comp (t₀, y₀) hfd
    change ContDiffAt ℝ ∞
        (fun p : ℝ × E => evalMap (fderiv ℝ (fun z : E => Φ p.1 z) p.2)) (t₀, y₀)
    exact hev
  simpa [partialDeriv] using happly

omit [T2Space M] [SigmaCompactSpace M] in
theorem normGradSqFun_eq_chartInvGram_sum
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (x : M) (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    normGradSqFun (I := I) g f x =
      ∑ k : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α x k i *
          partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) *
          partialDeriv (E := E) k (scalarOnE (I := I) α f) (extChartAt I α x) := by
  classical
  have hxsrc : x ∈ (chartAt H α).source := by
    simpa [trivializationAt_baseSet_eq_chartAt_source (I := I) α] using hx
  have hx_int : (extChartAt I α) x ∈ interior (extChartAt I α).target := by
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
    exact (extChartAt I α).map_source
      (by rw [extChartAt_source_eq_chartAt_source (I := I) α]; exact hxsrc)
  have hg : gradChartLocal (I := I) g α f x = gradFun (I := I) g f x :=
    gradChartLocal_eq_gradFun (I := I) g α (hf.mdifferentiableAt (x := x) (by simp)) hx hx_int
  have hinner : g.inner x (gradChartLocal (I := I) g α f x) (gradChartLocal (I := I) g α f x) =
      ∑ k : Fin (Module.finrank ℝ E),
        gradChartCoeff (I := I) g α f k x *
          partialDeriv (E := E) k (scalarOnE (I := I) α f) (extChartAt I α x) := by
    nth_rewrite 2 [show gradChartLocal (I := I) g α f x =
        ∑ k : Fin (Module.finrank ℝ E),
          gradChartCoeff (I := I) g α f k x • chartBasisVecFiber (I := I) α k x by
        rfl]
    have hlin : (g.inner x (gradChartLocal (I := I) g α f x))
        (∑ k : Fin (Module.finrank ℝ E),
          gradChartCoeff (I := I) g α f k x • chartBasisVecFiber (I := I) α k x) =
        ∑ k : Fin (Module.finrank ℝ E),
          gradChartCoeff (I := I) g α f k x *
            (g.inner x (gradChartLocal (I := I) g α f x)) (chartBasisVecFiber (I := I) α k x) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [map_smul, smul_eq_mul]
    rw [hlin]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [inner_gradChartLocal_chartBasis (I := I) g α f hx k]
  have hcoeff : ∀ k : Fin (Module.finrank ℝ E),
      gradChartCoeff (I := I) g α f k x =
        ∑ i : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α x k i *
            partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) :=
    fun k => rfl
  calc
    normGradSqFun (I := I) g f x
        = g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x) := by
            rw [normGradSqFun]
    _ = g.inner x (gradChartLocal (I := I) g α f x) (gradChartLocal (I := I) g α f x) := by
            rw [hg]
    _ = ∑ k : Fin (Module.finrank ℝ E),
          gradChartCoeff (I := I) g α f k x *
            partialDeriv (E := E) k (scalarOnE (I := I) α f) (extChartAt I α x) := hinner
    _ = ∑ k : Fin (Module.finrank ℝ E),
          ∑ i : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g α x k i *
              partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) *
              partialDeriv (E := E) k (scalarOnE (I := I) α f) (extChartAt I α x) := by
            refine Finset.sum_congr rfl ?_
            intro k _
            rw [hcoeff k]
            rw [Finset.sum_mul]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem timeDeriv_joint_contDiffAt
    (Φ : ℝ → E → ℝ)
    {t₀ : ℝ} {y₀ : E}
    (hΦ : ContDiffAt ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2) (t₀, y₀)) :
    ContDiffAt ℝ ∞ (fun p : ℝ × E => deriv (fun s : ℝ => Φ s p.2) p.1) (t₀, y₀) := by
  classical
  have hfd := ContDiffAt.fderiv
    (m := (⊤ : ℕ∞))
    (f := fun p : ℝ × E => fun s : ℝ => Φ s p.2)
    (g := fun p : ℝ × E => p.1) (by
      change ContDiffAt ℝ ∞ (fun q : (ℝ × E) × ℝ => Φ q.2 q.1.2) ((t₀, y₀), t₀)
      exact hΦ.comp ((t₀, y₀), t₀) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
    ) (contDiffAt_fst : ContDiffAt ℝ ∞ (fun p : ℝ × E => p.1) (t₀, y₀)) (by simp)
  have happly : ContDiffAt ℝ ∞
      (fun p : ℝ × E => (fderiv ℝ (fun s : ℝ => Φ s p.2) p.1) (1 : ℝ)) (t₀, y₀) := by
    let evalMap : (ℝ →L[ℝ] ℝ) →L[ℝ] ℝ :=
      { toFun := fun L => L (1 : ℝ)
        map_add' := by intro L M; rfl
        map_smul' := by intro a L; rfl }
    have hev : ContDiffAt ℝ ∞
        (fun p : ℝ × E => evalMap (fderiv ℝ (fun s : ℝ => Φ s p.2) p.1)) (t₀, y₀) :=
      evalMap.contDiff.contDiffAt.comp (t₀, y₀) hfd
    change ContDiffAt ℝ ∞
        (fun p : ℝ × E => evalMap (fderiv ℝ (fun s : ℝ => Φ s p.2) p.1)) (t₀, y₀)
    exact hev
  change ContDiffAt ℝ ∞
      (fun p : ℝ × E => (fderiv ℝ (fun s : ℝ => Φ s p.2) p.1) (1 : ℝ)) (t₀, y₀)
  exact happly

omit [T2Space M] [SigmaCompactSpace M] in
theorem liYauQuantity_contMDiff
    {D : RealTimeInterval}
    (g : SmoothRiemannianMetric I M)
    (u : ℝ → M → ℝ)
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2) (D.regular ×ˢ univ))
    (hslice : ∀ t : ℝ, t ∈ D.carrier → ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t))
    (hpos : ∀ t : ℝ, t ∈ D.carrier → ∀ x : M, 0 < u t x) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => liYauQuantity g (fun τ y => Real.log (u τ y)) p.1 p.2)
      (D.regular ×ˢ univ) := by
  classical
  let f : ℝ → M → ℝ := fun τ y => Real.log (u τ y)
  have hlog' : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2) (D.regular ×ˢ univ) := by
    intro p hp
    have hnh : D.regular ×ˢ univ ∈ 𝓝 p :=
      (IsOpen.prod D.regular_isOpen isOpen_univ).mem_nhds ⟨hp.1, trivial⟩
    have hlogAt : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => Real.log (u p.1 p.2)) p :=
      (Real.contDiffAt_log.2 (hpos p.1 (D.regular_subset hp.1) p.2).ne').comp_contMDiffAt
        (x := p) (hu.contMDiffAt hnh)
    simpa [f] using hlogAt.contMDiffWithinAt
  have hlogslice : ∀ t : ℝ, t ∈ D.carrier → ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y : M => Real.log (u t y)) :=
    fun t ht => Moser.contMDiff_log_of_pos_slice (hslice t ht) (hpos t ht)
  have hly_def : ∀ (t : ℝ) (y : M), liYauQuantity g f t y =
      normGradSqFun (I := I) g (f t) y - deriv (fun s : ℝ => f s y) t := by
    intro t y
    unfold liYauQuantity
    have hvec : gradientFun (I := I) g (f t) y = gradFun (I := I) g (f t) y := by
      apply (metricFlatEquiv (I := I) g y).injective
      ext w
      change g.inner y (gradientFun (I := I) g (f t) y) w = g.inner y (gradFun (I := I) g (f t) y) w
      rw [inner_gradientFun (I := I) g (f t) y w]
      rw [inner_gradFun (I := I) g (f t) y w]
    rw [hvec]
    rw [normGradSqFun]
  intro p₀ hp₀
  rcases p₀ with ⟨t₀, x₀⟩
  have ht₀ : t₀ ∈ D.regular := hp₀.1
  have hqAt : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => liYauQuantity g f p.1 p.2) (t₀, x₀) := by
    rw [contMDiffAt_iff]
    set α : M := x₀ with hα
    have hy₀ : (extChartAt I α) x₀ ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source (mem_extChartAt_source (I := I) α)
    have hΦ : ContDiffAt ℝ ∞
        (fun r : ℝ × E => scalarOnE (I := I) α (f r.1) r.2) (t₀, (extChartAt I α) x₀) :=
      scalarOnE_jointContDiffAt (I := I) (M := M) (D := D) f hlog' α ht₀ hy₀
    have hpd : ∀ i : Fin (Module.finrank ℝ E), ContDiffAt ℝ ∞
        (fun p : ℝ × E => partialDeriv (E := E) i (fun z : E => scalarOnE (I := I) α (f p.1) z) p.2)
        (t₀, (extChartAt I α) x₀) :=
      fun i => partialDeriv_joint_contDiffAt (fun t z => scalarOnE (I := I) α (f t) z) hΦ i
    have hgram : ∀ (i j : Fin (Module.finrank ℝ E)), ContDiffAt ℝ ∞
        (fun p : ℝ × E => chartInvGramOnE (I := I) g α i j p.2) (t₀, (extChartAt I α) x₀) := by
      intro i j
      change ContDiffAt ℝ ∞
          ((fun z : E => chartInvGramOnE (I := I) g α i j z) ∘
            (fun p : ℝ × E => p.2)) (t₀, (extChartAt I α) x₀)
      refine ContDiffAt.comp (t₀, (extChartAt I α) x₀) ?_ contDiffAt_snd
      exact (chartInvGramOnE_contDiffOn (I := I) g α i j).contDiffAt
        ((isOpen_extChartAt_target (I := I) α).mem_nhds hy₀)
    have hdt : ContDiffAt ℝ ∞
        (fun p : ℝ × E => deriv (fun s : ℝ => f s ((extChartAt I α).symm p.2)) p.1)
        (t₀, (extChartAt I α) x₀) := by
      have htd := timeDeriv_joint_contDiffAt
        (fun t z => scalarOnE (I := I) α (f t) z) hΦ
      change ContDiffAt ℝ ∞
          (fun p : ℝ × E => deriv (fun s : ℝ => scalarOnE (I := I) α (f s) p.2) p.1)
          (t₀, (extChartAt I α) x₀)
      exact htd
    have hnorm_pull : ∀ (t : ℝ) (ht : t ∈ D.regular) (y : E), y ∈ (extChartAt I α).target →
        normGradSqFun (I := I) g (f t) ((extChartAt I α).symm y) =
          ∑ k : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α k i y *
              partialDeriv (E := E) i (scalarOnE (I := I) α (f t)) y *
              partialDeriv (E := E) k (scalarOnE (I := I) α (f t)) y := by
      intro t ht y hy
      have hx : (extChartAt I α).symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
        simpa [trivializationAt_baseSet_eq_chartAt_source (I := I) α] using
          (extChartAt I α).map_target hy
      have hformula := normGradSqFun_eq_chartInvGram_sum (I := I) g α
        (hf := hlogslice t (D.regular_subset ht))
        ((extChartAt I α).symm y) hx
      rw [show (fun z : M => Real.log (u t z)) = f t by
        funext z
        rfl] at hformula
      rw [hformula]
      refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun i _ => ?_))
      rw [← (chartInvGramOnE_def (I := I) g α k i y)]
      rw [(extChartAt I α).right_inv hy]
    have hqformula : ∀ (t : ℝ) (ht : t ∈ D.regular) (y : E), y ∈ (extChartAt I α).target →
        liYauQuantity g f t ((extChartAt I α).symm y) =
          (∑ k : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α k i y *
              partialDeriv (E := E) i (fun z : E => scalarOnE (I := I) α (f t) z) y *
              partialDeriv (E := E) k (fun z : E => scalarOnE (I := I) α (f t) z) y) -
            deriv (fun s : ℝ => f s ((extChartAt I α).symm y)) t := by
      intro t ht y hy
      rw [hly_def t ((extChartAt I α).symm y)]
      rw [hnorm_pull t ht y hy]
    have hqpull : ContDiffAt ℝ ∞
        (fun p : ℝ × E => liYauQuantity g f p.1 ((extChartAt I α).symm p.2))
        (t₀, (extChartAt I α) x₀) := by
      have hsum : ContDiffAt ℝ ∞
          (fun p : ℝ × E =>
            (∑ k : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α k i p.2 *
                partialDeriv (E := E) i (fun z : E => scalarOnE (I := I) α (f p.1) z) p.2 *
                partialDeriv (E := E) k (fun z : E => scalarOnE (I := I) α (f p.1) z) p.2) -
              deriv (fun s : ℝ => f s ((extChartAt I α).symm p.2)) p.1)
          (t₀, (extChartAt I α) x₀) := by
        refine (ContDiffAt.sum (s := Finset.univ) (fun k _ => ?_)).sub hdt
        refine ContDiffAt.sum (s := Finset.univ) (fun i _ => ?_)
        exact ((hgram k i).mul (hpd i)).mul (hpd k)
      exact hsum.congr_of_eventuallyEq (by
        rw [Filter.eventuallyEq_iff_exists_mem]
        refine ⟨D.regular ×ˢ (extChartAt I α).target,
          (IsOpen.prod D.regular_isOpen (isOpen_extChartAt_target (I := I) α)).mem_nhds ⟨ht₀,
            hy₀⟩, ?_⟩
        intro z hz
        exact hqformula z.1 hz.1 z.2 hz.2)
    constructor
    · have hcont_pull : ContinuousAt
          (fun p : ℝ × E => liYauQuantity g f p.1 ((extChartAt I α).symm p.2))
          (t₀, (extChartAt I α) x₀) := hqpull.continuousAt
      have hw_eq : (fun p : ℝ × M => liYauQuantity g f p.1 p.2) =ᶠ[𝓝 (t₀, x₀)]
          (fun p : ℝ × E => liYauQuantity g f p.1 ((extChartAt I α).symm p.2)) ∘
            (fun p : ℝ × M => (p.1, (extChartAt I α) p.2)) := by
        rw [Filter.eventuallyEq_iff_exists_mem]
        refine ⟨Set.univ ×ˢ (extChartAt I α).source,
          (isOpen_univ.prod (isOpen_extChartAt_source (I := I) α)).mem_nhds
            ⟨Set.mem_univ _, mem_extChartAt_source (I := I) α⟩, ?_⟩
        intro y hy
        change liYauQuantity g f y.1 y.2 =
          liYauQuantity g f y.1 ((extChartAt I α).symm ((extChartAt I α) y.2))
        rw [(extChartAt I α).left_inv hy.2]
      have hcomp : ContinuousAt
          ((fun p : ℝ × E => liYauQuantity g f p.1 ((extChartAt I α).symm p.2)) ∘
            (fun p : ℝ × M => (p.1, (extChartAt I α) p.2))) (t₀, x₀) :=
        ContinuousAt.comp
          (f := fun p : ℝ × M => (p.1, (extChartAt I α) p.2))
          (x := (t₀, x₀)) hcont_pull (by
          refine (continuousAt_fst : ContinuousAt (fun p : ℝ × M => p.1) (t₀, x₀)).prodMk ?_
          show ContinuousAt (fun p : ℝ × M => (extChartAt I α) p.2) (t₀, x₀)
          exact ContinuousAt.comp
            (f := fun p : ℝ × M => p.2) (x := (t₀, x₀))
            (continuousAt_extChartAt x₀) continuousAt_snd)
      have hc := hcomp.congr_of_eventuallyEq hw_eq
      simpa [f] using hc
    · have hcd_pull : ContDiffWithinAt ℝ ∞
          (fun p : ℝ × E => liYauQuantity g f p.1 ((extChartAt I α).symm p.2))
          Set.univ (t₀, (extChartAt I α) x₀) := hqpull.contDiffWithinAt
      have hcomp_eq : (extChartAt 𝓘(ℝ, ℝ) (liYauQuantity g f t₀ x₀) ∘
          (fun p : ℝ × M => liYauQuantity g f p.1 p.2) ∘
            (extChartAt (𝓘(ℝ, ℝ).prod I) (t₀, x₀)).symm) =
          (fun p : ℝ × E => liYauQuantity g f p.1 ((extChartAt I α).symm p.2)) := by
        funext z
        simp only [Function.comp_def, extChartAt_prod, extChartAt_coe_symm, α]
        change liYauQuantity g f z.1 ((extChartAt I x₀).symm z.2) =
          liYauQuantity g f z.1 ((extChartAt I x₀).symm z.2)
        rfl
      have hbase : (extChartAt (𝓘(ℝ, ℝ).prod I) (t₀, x₀)) (t₀, x₀) =
          (t₀, (extChartAt I α) x₀) := by
        rw [extChartAt_prod (x := (t₀, x₀))]
        simp [α]
      have hrange : range (𝓘(ℝ, ℝ).prod I) = Set.univ := by
        apply Set.Subset.antisymm
        · intro y hy
          trivial
        · intro y hy
          have hy2 : y.2 ∈ range I := by
            rw [ModelWithCorners.range_eq_univ I]
            trivial
          rcases hy2 with ⟨x₂, hx₂⟩
          exact ⟨(y.1, x₂), by simp [hx₂]⟩
      rw [hcomp_eq, hbase, hrange]
      exact hcd_pull
  exact hqAt.contMDiffWithinAt

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem scalarOnE_jointContDiffWithinAt
    (S : Set ℝ)
    (f : ℝ → M → ℝ)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2) (S ×ˢ univ))
    (α : M) {t : ℝ} (ht : t ∈ S) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    ContDiffWithinAt ℝ ∞
      (fun r : ℝ × E => scalarOnE (I := I) α (f r.1) r.2)
      (S ×ˢ (extChartAt I α).target) (t, y) := by
  have hU : ContMDiffOn ((𝓘(ℝ, ℝ).prod I)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2) (S ×ˢ univ) := hf
  have hids : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (fun r : ℝ × E => r.1) (Set.univ ×ˢ (extChartAt I α).target) :=
    contMDiffOn_fst
  have hsym : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) I ∞
      (fun r : ℝ × E => (extChartAt I α).symm r.2)
      (Set.univ ×ˢ (extChartAt I α).target) := by
    refine (contMDiffOn_extChartAt_symm (I := I) α).comp ?_ ?_
    · exact contMDiffOn_snd
    · intro r hr
      exact hr.2
  have hsymm : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ((𝓘(ℝ, ℝ).prod I)) ∞
      (fun r : ℝ × E => (r.1, (extChartAt I α).symm r.2))
      (S ×ˢ (extChartAt I α).target) := by
    refine (hids.prodMk hsym).mono ?_
    intro r hr
    exact ⟨Set.mem_univ r.1, hr.2⟩
  have hcomp : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (fun r : ℝ × E => f r.1 ((extChartAt I α).symm r.2))
      (S ×ˢ (extChartAt I α).target) :=
    hU.comp hsymm (fun r hr => ⟨hr.1, trivial⟩)
  have hcd : ContDiffOn ℝ ∞
      (fun r : ℝ × E => f r.1 ((extChartAt I α).symm r.2))
      (S ×ˢ (extChartAt I α).target) := by
    rw [← contMDiffOn_iff_contDiffOn, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hcomp
  have hpt : (t, y) ∈ S ×ˢ (extChartAt I α).target := ⟨ht, hy⟩
  have hat := hcd.contDiffWithinAt hpt
  simpa [scalarOnE_def] using hat

theorem partialDeriv_joint_contDiffWithinAt
    (S : Set ℝ) (Φ : ℝ → E → ℝ)
    {t₀ : ℝ} (ht₀ : t₀ ∈ S) {y₀ : E}
    (hΦ : ContDiffWithinAt ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2)
      (S ×ˢ Set.univ) (t₀, y₀))
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffWithinAt ℝ ∞
      (fun p : ℝ × E => partialDeriv (E := E) i (fun z : E => Φ p.1 z) p.2)
      (S ×ˢ Set.univ) (t₀, y₀) := by
  classical
  have hfd := ContDiffWithinAt.fderivWithin
    (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞))
    (f := fun p : ℝ × E => fun z : E => Φ p.1 z)
    (g := fun p : ℝ × E => p.2)
    (t := (Set.univ : Set E)) (s := S ×ˢ Set.univ) (x₀ := (t₀, y₀))
    (by
      change ContDiffWithinAt ℝ ∞
        (fun q : (ℝ × E) × E => Φ q.1.1 q.2)
        ((S ×ˢ Set.univ) ×ˢ Set.univ) ((t₀, y₀), y₀)
      have hswap : ContDiffWithinAt ℝ ∞
          (fun q : (ℝ × E) × E => (q.1.1, q.2))
          ((S ×ˢ Set.univ) ×ˢ Set.univ) ((t₀, y₀), y₀) := by
        exact (contDiff_fst.comp contDiff_fst).prodMk contDiff_snd |>.contDiffWithinAt
      exact hΦ.comp ((t₀, y₀), y₀) hswap (by
        intro q hq
        exact ⟨hq.1.1, Set.mem_univ q.2⟩))
    (by
      exact (contDiffWithinAt_snd : ContDiffWithinAt ℝ ∞
        (fun p : ℝ × E => p.2) (S ×ˢ Set.univ) (t₀, y₀)))
    (by exact (uniqueDiffOn_univ : UniqueDiffOn ℝ (Set.univ : Set E)))
    (by norm_num) (by simp [ht₀]) (by intro p hp; exact Set.mem_univ p.2)
  have happly : ContDiffWithinAt ℝ ∞
      (fun p : ℝ × E => (fderiv ℝ (fun z : E => Φ p.1 z) p.2) (chartModelBasis E i))
      (S ×ˢ Set.univ) (t₀, y₀) := by
    let evalMap : (E →L[ℝ] ℝ) →L[ℝ] ℝ :=
      { toFun := fun L => L (chartModelBasis E i)
        map_add' := by intro L M; rfl
        map_smul' := by intro a L; rfl }
    have hfderiv : ContDiffWithinAt ℝ ∞
        (fun p : ℝ × E => fderivWithin ℝ (fun z : E => Φ p.1 z) Set.univ p.2)
        (S ×ˢ Set.univ) (t₀, y₀) := hfd
    have hev : ContDiffWithinAt ℝ ∞
        (fun p : ℝ × E => evalMap (fderivWithin ℝ (fun z : E => Φ p.1 z) Set.univ p.2))
        (S ×ˢ Set.univ) (t₀, y₀) :=
      (evalMap.contDiff.contDiffWithinAt : ContDiffWithinAt ℝ ∞
        (fun L : E →L[ℝ] ℝ => evalMap L) Set.univ (fderivWithin ℝ
          (fun z : E => Φ t₀ z) Set.univ y₀)).comp (t₀, y₀) hfderiv (by
        intro p hp
        exact Set.mem_univ _)
    have heq : (fun p : ℝ × E => evalMap (fderivWithin ℝ
          (fun z : E => Φ p.1 z) Set.univ p.2)) =ᶠ[𝓝[S ×ˢ Set.univ] (t₀, y₀)]
        (fun p : ℝ × E => (fderiv ℝ (fun z : E => Φ p.1 z) p.2) (chartModelBasis E i)) := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨S ×ˢ Set.univ, self_mem_nhdsWithin, ?_⟩
      intro p hp
      simp only [evalMap]
      rw [fderivWithin_of_mem_nhds (Filter.univ_mem : (Set.univ : Set E) ∈ 𝓝 p.2)]
      rfl
    exact hev.congr_of_eventuallyEq heq.symm (by
      dsimp [evalMap]
      rw [fderivWithin_of_mem_nhds (Filter.univ_mem : (Set.univ : Set E) ∈ 𝓝 y₀)])
  simpa [partialDeriv] using happly

omit [FiniteDimensional ℝ E] in
theorem timeDeriv_joint_contDiffWithinAt
    (S : Set ℝ) (Φ : ℝ → E → ℝ)
    {t₀ : ℝ} (ht₀ : t₀ ∈ S) {y₀ : E}
    (hΦ : ContDiffWithinAt ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2)
      (S ×ˢ Set.univ) (t₀, y₀))
    (hS : UniqueDiffOn ℝ S) :
    ContDiffWithinAt ℝ ∞
      (fun p : ℝ × E => fderivWithin ℝ (fun s : ℝ => Φ s p.2) S p.1)
      (S ×ˢ Set.univ) (t₀, y₀) := by
  classical
  have hfd := ContDiffWithinAt.fderivWithin
    (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞))
    (f := fun p : ℝ × E => fun s : ℝ => Φ s p.2)
    (g := fun p : ℝ × E => p.1)
    (t := S) (s := S ×ˢ Set.univ) (x₀ := (t₀, y₀))
    (by
      change ContDiffWithinAt ℝ ∞
        (fun q : (ℝ × E) × ℝ => Φ q.2 q.1.2)
        ((S ×ˢ Set.univ) ×ˢ S) ((t₀, y₀), t₀)
      have hswap : ContDiffWithinAt ℝ ∞
          (fun q : (ℝ × E) × ℝ => (q.2, q.1.2))
          ((S ×ˢ Set.univ) ×ˢ S) ((t₀, y₀), t₀) := by
        exact (contDiff_snd.prodMk contDiff_fst.snd).contDiffWithinAt
      exact hΦ.comp ((t₀, y₀), t₀) hswap (by
        intro q hq
        exact ⟨hq.2, hq.1.2⟩))
    (by
      exact (contDiffWithinAt_fst : ContDiffWithinAt ℝ ∞
        (fun p : ℝ × E => p.1) (S ×ˢ Set.univ) (t₀, y₀)))
    (by exact hS)
    (by norm_num) (by simp [ht₀]) (by intro p hp; exact hp.1)
  exact hfd

omit [T2Space M] [SigmaCompactSpace M] in
theorem normGradSqFun_contMDiffOn
    {D : RealTimeInterval}
    (g : SmoothRiemannianMetric I M)
    (f : ℝ → M → ℝ)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2) (D.regular ×ˢ univ))
    (hslice : ∀ t : ℝ, t ∈ D.regular → ContMDiff I 𝓘(ℝ, ℝ) ∞ (f t)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => normGradSqFun (I := I) g (f p.1) p.2)
      (D.regular ×ˢ univ) := by
  classical
  intro p₀ hp₀
  rcases p₀ with ⟨t₀, x₀⟩
  have ht₀ : t₀ ∈ D.regular := hp₀.1
  have hNAt : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => normGradSqFun (I := I) g (f p.1) p.2) (t₀, x₀) := by
    rw [contMDiffAt_iff]
    set α : M := x₀ with hα
    have hy₀ : (extChartAt I α) x₀ ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source (mem_extChartAt_source (I := I) α)
    have hΦ : ContDiffAt ℝ ∞
        (fun r : ℝ × E => scalarOnE (I := I) α (f r.1) r.2) (t₀, (extChartAt I α) x₀) :=
      scalarOnE_jointContDiffAt (I := I) (M := M) (D := D) f hf α ht₀ hy₀
    have hpd : ∀ i : Fin (Module.finrank ℝ E), ContDiffAt ℝ ∞
        (fun p : ℝ × E => partialDeriv (E := E) i
          (fun z : E => scalarOnE (I := I) α (f p.1) z) p.2)
        (t₀, (extChartAt I α) x₀) :=
      fun i => partialDeriv_joint_contDiffAt (fun t z => scalarOnE (I := I) α (f t) z) hΦ i
    have hgram : ∀ (i j : Fin (Module.finrank ℝ E)), ContDiffAt ℝ ∞
        (fun p : ℝ × E => chartInvGramOnE (I := I) g α i j p.2)
        (t₀, (extChartAt I α) x₀) := by
      intro i j
      change ContDiffAt ℝ ∞
          ((fun z : E => chartInvGramOnE (I := I) g α i j z) ∘
            (fun p : ℝ × E => p.2)) (t₀, (extChartAt I α) x₀)
      refine ContDiffAt.comp (t₀, (extChartAt I α) x₀) ?_ contDiffAt_snd
      exact (chartInvGramOnE_contDiffOn (I := I) g α i j).contDiffAt
        ((isOpen_extChartAt_target (I := I) α).mem_nhds hy₀)
    have hNpull : ContDiffAt ℝ ∞
        (fun p : ℝ × E =>
          normGradSqFun (I := I) g (f p.1) ((extChartAt I α).symm p.2))
        (t₀, (extChartAt I α) x₀) := by
      have hsum : ContDiffAt ℝ ∞
          (fun p : ℝ × E =>
            ∑ k : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α k i p.2 *
                partialDeriv (E := E) i (fun z : E => scalarOnE (I := I) α (f p.1) z) p.2 *
                partialDeriv (E := E) k (fun z : E => scalarOnE (I := I) α (f p.1) z) p.2)
          (t₀, (extChartAt I α) x₀) := by
        refine (ContDiffAt.sum (s := Finset.univ) (fun k _ => ?_))
        refine ContDiffAt.sum (s := Finset.univ) (fun i _ => ?_)
        exact ((hgram k i).mul (hpd i)).mul (hpd k)
      exact hsum.congr_of_eventuallyEq (by
        rw [Filter.eventuallyEq_iff_exists_mem]
        refine ⟨D.regular ×ˢ (extChartAt I α).target,
          (IsOpen.prod D.regular_isOpen (isOpen_extChartAt_target (I := I) α)).mem_nhds
            ⟨ht₀, hy₀⟩, ?_⟩
        intro z hz
        have hx : (extChartAt I α).symm z.2 ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
          simpa [trivializationAt_baseSet_eq_chartAt_source (I := I) α] using
            (extChartAt I α).map_target hz.2
        have hformula := normGradSqFun_eq_chartInvGram_sum (I := I) g α
          (hf := hslice z.1 hz.1)
          ((extChartAt I α).symm z.2) hx
        change normGradSqFun (I := I) g (f z.1) ((extChartAt I α).symm z.2) =
          (∑ k : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α k i z.2 *
              partialDeriv (E := E) i (fun w : E => scalarOnE (I := I) α (f z.1) w) z.2 *
              partialDeriv (E := E) k (fun w : E => scalarOnE (I := I) α (f z.1) w) z.2)
        rw [hformula]
        refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun i _ => ?_))
        rw [← (chartInvGramOnE_def (I := I) g α k i z.2)]
        rw [(extChartAt I α).right_inv hz.2])
    constructor
    · have hcont_pull : ContinuousAt
          (fun p : ℝ × E => normGradSqFun (I := I) g (f p.1) ((extChartAt I α).symm p.2))
          (t₀, (extChartAt I α) x₀) := hNpull.continuousAt
      have hw_eq : (fun p : ℝ × M => normGradSqFun (I := I) g (f p.1) p.2) =ᶠ[𝓝 (t₀, x₀)]
          (fun p : ℝ × E => normGradSqFun (I := I) g (f p.1) ((extChartAt I α).symm p.2)) ∘
            (fun p : ℝ × M => (p.1, (extChartAt I α) p.2)) := by
        rw [Filter.eventuallyEq_iff_exists_mem]
        refine ⟨Set.univ ×ˢ (extChartAt I α).source,
          (isOpen_univ.prod (isOpen_extChartAt_source (I := I) α)).mem_nhds
            ⟨Set.mem_univ _, mem_extChartAt_source (I := I) α⟩, ?_⟩
        intro y hy
        change normGradSqFun (I := I) g (f y.1) y.2 =
          normGradSqFun (I := I) g (f y.1) ((extChartAt I α).symm ((extChartAt I α) y.2))
        rw [(extChartAt I α).left_inv hy.2]
      have hcomp : ContinuousAt
          ((fun p : ℝ × E => normGradSqFun (I := I) g (f p.1) ((extChartAt I α).symm p.2)) ∘
            (fun p : ℝ × M => (p.1, (extChartAt I α) p.2))) (t₀, x₀) :=
        ContinuousAt.comp
          (f := fun p : ℝ × M => (p.1, (extChartAt I α) p.2))
          (x := (t₀, x₀)) hcont_pull (by
          refine (continuousAt_fst : ContinuousAt (fun p : ℝ × M => p.1) (t₀, x₀)).prodMk ?_
          show ContinuousAt (fun p : ℝ × M => (extChartAt I α) p.2) (t₀, x₀)
          exact ContinuousAt.comp
            (f := fun p : ℝ × M => p.2) (x := (t₀, x₀))
            (continuousAt_extChartAt x₀) continuousAt_snd)
      exact hcomp.congr_of_eventuallyEq hw_eq
    · have hcd_pull : ContDiffWithinAt ℝ ∞
          (fun p : ℝ × E => normGradSqFun (I := I) g (f p.1) ((extChartAt I α).symm p.2))
          Set.univ (t₀, (extChartAt I α) x₀) := hNpull.contDiffWithinAt
      have hcomp_eq : (extChartAt 𝓘(ℝ, ℝ) (normGradSqFun (I := I) g (f t₀) x₀) ∘
          (fun p : ℝ × M => normGradSqFun (I := I) g (f p.1) p.2) ∘
            (extChartAt (𝓘(ℝ, ℝ).prod I) (t₀, x₀)).symm) =
          (fun p : ℝ × E => normGradSqFun (I := I) g (f p.1) ((extChartAt I α).symm p.2)) := by
        funext z
        simp only [Function.comp_def, extChartAt_prod, extChartAt_coe_symm, α]
        change normGradSqFun (I := I) g (f z.1) ((extChartAt I x₀).symm z.2) =
          normGradSqFun (I := I) g (f z.1) ((extChartAt I x₀).symm z.2)
        rfl
      have hbase : (extChartAt (𝓘(ℝ, ℝ).prod I) (t₀, x₀)) (t₀, x₀) =
          (t₀, (extChartAt I α) x₀) := by
        rw [extChartAt_prod (x := (t₀, x₀))]
        simp [α]
      have hrange : range (𝓘(ℝ, ℝ).prod I) = Set.univ := by
        apply Set.Subset.antisymm
        · intro y hy
          trivial
        · intro y hy
          have hy2 : y.2 ∈ range I := by
            rw [ModelWithCorners.range_eq_univ I]
            trivial
          rcases hy2 with ⟨x₂, hx₂⟩
          exact ⟨(y.1, x₂), by simp [hx₂]⟩
      rw [hcomp_eq, hbase, hrange]
      exact hcd_pull
  exact hNAt.contMDiffWithinAt

omit [T2Space M] [SigmaCompactSpace M] in
theorem normGradSqFun_contMDiffWithinAt
    (S : Set ℝ)
    (g : SmoothRiemannianMetric I M)
    (f : ℝ → M → ℝ)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2) (S ×ˢ univ))
    (hslice : ∀ t : ℝ, t ∈ S → ContMDiff I 𝓘(ℝ, ℝ) ∞ (f t))
    {t₀ : ℝ} (ht₀ : t₀ ∈ S) (x₀ : M) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => normGradSqFun (I := I) g (f p.1) p.2)
      (S ×ˢ univ) (t₀, x₀) := by
  classical
  rw [contMDiffWithinAt_iff]
  set α : M := x₀ with hα
  have hy₀ : (extChartAt I α) x₀ ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source (mem_extChartAt_source (I := I) α)
  have htarget_nhd : S ×ˢ (extChartAt I α).target ∈ 𝓝[S ×ˢ Set.univ]
      (t₀, (extChartAt I α) x₀) := by
    simpa [Set.prod_inter_prod] using
      Filter.inter_mem
        (self_mem_nhdsWithin : S ×ˢ Set.univ ∈ 𝓝[S ×ˢ Set.univ]
          (t₀, (extChartAt I α) x₀))
        (nhdsWithin_le_nhds
          ((isOpen_univ.prod (isOpen_extChartAt_target (I := I) α)).mem_nhds
            (show (t₀, (extChartAt I α) x₀) ∈ univ ×ˢ (extChartAt I α).target from
              ⟨Set.mem_univ t₀, hy₀⟩)))
  have huniv_nhd : S ×ˢ Set.univ ∈ 𝓝[S ×ˢ (extChartAt I α).target]
      (t₀, (extChartAt I α) x₀) := by
    refine Filter.mem_of_superset (self_mem_nhdsWithin : S ×ˢ (extChartAt I α).target ∈
      𝓝[S ×ˢ (extChartAt I α).target] (t₀, (extChartAt I α) x₀)) ?_
    show S ×ˢ (extChartAt I α).target ⊆ S ×ˢ Set.univ
    intro z hz
    exact ⟨hz.1, Set.mem_univ z.2⟩
  have hΦ : ContDiffWithinAt ℝ ∞
      (fun r : ℝ × E => scalarOnE (I := I) α (f r.1) r.2)
      (S ×ˢ (extChartAt I α).target) (t₀, (extChartAt I α) x₀) :=
    scalarOnE_jointContDiffWithinAt (I := I) (M := M) S f hf α ht₀ hy₀
  have hΦ_univ : ContDiffWithinAt ℝ ∞
      (fun r : ℝ × E => scalarOnE (I := I) α (f r.1) r.2)
      (S ×ˢ Set.univ) (t₀, (extChartAt I α) x₀) := by
    exact hΦ.mono_of_mem_nhdsWithin htarget_nhd
  have hpd : ∀ i : Fin (Module.finrank ℝ E), ContDiffWithinAt ℝ ∞
      (fun p : ℝ × E => partialDeriv (E := E) i
        (fun z : E => scalarOnE (I := I) α (f p.1) z) p.2)
      (S ×ˢ Set.univ) (t₀, (extChartAt I α) x₀) :=
    fun i => partialDeriv_joint_contDiffWithinAt S
      (fun t z => scalarOnE (I := I) α (f t) z) ht₀ hΦ_univ i
  have hgram : ∀ (i j : Fin (Module.finrank ℝ E)), ContDiffWithinAt ℝ ∞
      (fun p : ℝ × E => chartInvGramOnE (I := I) g α i j p.2)
      (S ×ˢ Set.univ) (t₀, (extChartAt I α) x₀) := by
    intro i j
    change ContDiffWithinAt ℝ ∞
        ((fun z : E => chartInvGramOnE (I := I) g α i j z) ∘
          (fun p : ℝ × E => p.2))
        (S ×ˢ Set.univ) (t₀, (extChartAt I α) x₀)
    have hg0 : ContDiffWithinAt ℝ ∞
        (fun z : E => chartInvGramOnE (I := I) g α i j z)
        (Set.univ : Set E) ((extChartAt I α) x₀) := by
      exact (chartInvGramOnE_contDiffOn
        (I := I) g α i j).contDiffWithinAt hy₀ |>.mono_of_mem_nhdsWithin (by
        exact nhdsWithin_le_nhds ((isOpen_extChartAt_target (I := I) α).mem_nhds hy₀))
    refine ContDiffWithinAt.comp (t₀, (extChartAt I α) x₀) hg0 (by
      exact (contDiffWithinAt_snd : ContDiffWithinAt ℝ ∞
        (fun p : ℝ × E => p.2) Set.univ (t₀, (extChartAt I α) x₀)).mono (by
          intro p hp
          exact Set.mem_univ p.2)) (by
      intro p hp
      exact Set.mem_univ p.2)
  have hNpull : ContDiffWithinAt ℝ ∞
      (fun p : ℝ × E =>
        normGradSqFun (I := I) g (f p.1) ((extChartAt I α).symm p.2))
      (S ×ˢ (extChartAt I α).target) (t₀, (extChartAt I α) x₀) := by
    have hsum : ContDiffWithinAt ℝ ∞
        (fun p : ℝ × E =>
          ∑ k : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α k i p.2 *
              partialDeriv (E := E) i (fun z : E => scalarOnE (I := I) α (f p.1) z) p.2 *
              partialDeriv (E := E) k (fun z : E => scalarOnE (I := I) α (f p.1) z) p.2)
        (S ×ˢ Set.univ) (t₀, (extChartAt I α) x₀) := by
      refine ContDiffWithinAt.sum (s := Finset.univ) (fun k _ => ?_)
      refine ContDiffWithinAt.sum (s := Finset.univ) (fun i _ => ?_)
      exact ((hgram k i).mul (hpd i)).mul (hpd k)
    refine (hsum.mono_of_mem_nhdsWithin huniv_nhd).congr_of_eventuallyEq (by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨S ×ˢ (extChartAt I α).target, self_mem_nhdsWithin, ?_⟩
      intro z hz
      have hx : (extChartAt I α).symm z.2 ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
        simpa [trivializationAt_baseSet_eq_chartAt_source (I := I) α] using
          (extChartAt I α).map_target hz.2
      have hformula := normGradSqFun_eq_chartInvGram_sum (I := I) g α
        (hf := hslice z.1 hz.1)
        ((extChartAt I α).symm z.2) hx
      change normGradSqFun (I := I) g (f z.1) ((extChartAt I α).symm z.2) =
        (∑ k : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k i z.2 *
            partialDeriv (E := E) i (fun w : E => scalarOnE (I := I) α (f z.1) w) z.2 *
            partialDeriv (E := E) k (fun w : E => scalarOnE (I := I) α (f z.1) w) z.2)
      rw [hformula]
      refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun i _ => ?_))
      rw [← (chartInvGramOnE_def (I := I) g α k i z.2)]
      rw [(extChartAt I α).right_inv hz.2]) (by
      change normGradSqFun (I := I) g (f t₀) ((extChartAt I α).symm ((extChartAt I α) x₀)) =
        (∑ k : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k i ((extChartAt I α) x₀) *
            partialDeriv (E := E) i (fun z : E => scalarOnE (I := I) α (f t₀) z)
              ((extChartAt I α) x₀) *
            partialDeriv (E := E) k (fun z : E => scalarOnE (I := I) α (f t₀) z)
              ((extChartAt I α) x₀))
      simpa [α, chartInvGramOnE_def,
        (extChartAt I α).left_inv (mem_extChartAt_source (I := I) α)] using
        normGradSqFun_eq_chartInvGram_sum (I := I) g α (hf := hslice t₀ ht₀) x₀ (by
          rw [trivializationAt_baseSet_eq_chartAt_source (I := I) α]
          exact mem_chart_source H α))
  have hNpull_univ : ContDiffWithinAt ℝ ∞
      (fun p : ℝ × E =>
        normGradSqFun (I := I) g (f p.1) ((extChartAt I α).symm p.2))
      (S ×ˢ Set.univ) (t₀, (extChartAt I α) x₀) := by
    exact hNpull.mono_of_mem_nhdsWithin htarget_nhd
  constructor
  · have hcont_pull : ContinuousWithinAt
        (fun p : ℝ × E =>
          normGradSqFun (I := I) g (f p.1) ((extChartAt I α).symm p.2))
        (S ×ˢ Set.univ) (t₀, (extChartAt I α) x₀) := hNpull_univ.continuousWithinAt
    have hw_eq : (fun p : ℝ × M => normGradSqFun (I := I) g (f p.1) p.2) =ᶠ[𝓝[(S ×ˢ Set.univ)]
      (t₀, x₀)]
        (fun p : ℝ × E =>
          normGradSqFun (I := I) g (f p.1) ((extChartAt I α).symm p.2)) ∘
            (fun p : ℝ × M => (p.1, (extChartAt I α) p.2)) := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨(S ×ˢ Set.univ) ∩ (Set.univ ×ˢ (extChartAt I α).source), ?_, ?_⟩
      · exact Filter.inter_mem self_mem_nhdsWithin
          (nhdsWithin_le_nhds ((isOpen_univ.prod (isOpen_extChartAt_source (I := I) α)).mem_nhds
            ⟨Set.mem_univ t₀, mem_extChartAt_source (I := I) α⟩))
      · intro y hy
        change normGradSqFun (I := I) g (f y.1) y.2 =
          normGradSqFun (I := I) g (f y.1)
            ((extChartAt I α).symm ((extChartAt I α) y.2))
        rw [(extChartAt I α).left_inv hy.2.2]
    have hcomp : ContinuousWithinAt
        ((fun p : ℝ × E =>
          normGradSqFun (I := I) g (f p.1) ((extChartAt I α).symm p.2)) ∘
            (fun p : ℝ × M => (p.1, (extChartAt I α) p.2)))
        (S ×ˢ Set.univ) (t₀, x₀) :=
      ContinuousWithinAt.comp hcont_pull (by
        refine (continuousWithinAt_fst : ContinuousWithinAt
          (fun p : ℝ × M => p.1) (S ×ˢ Set.univ) (t₀, x₀)).prodMk ?_
        show ContinuousWithinAt (fun p : ℝ × M => (extChartAt I α) p.2)
          (S ×ˢ Set.univ) (t₀, x₀)
        exact ContinuousWithinAt.comp
          (show ContinuousWithinAt (extChartAt I α) univ x₀ from
            (continuousAt_extChartAt x₀).continuousWithinAt)
          (continuousWithinAt_snd : ContinuousWithinAt
            (fun p : ℝ × M => p.2) (S ×ˢ Set.univ) (t₀, x₀))
          (by intro p hp; trivial)) (by
        intro p hp
        exact ⟨hp.1, Set.mem_univ ((extChartAt I α) p.2)⟩)
    exact hcomp.congr_of_eventuallyEq hw_eq (by
      change normGradSqFun (I := I) g (f t₀) x₀ =
        normGradSqFun (I := I) g (f t₀) ((extChartAt I α).symm ((extChartAt I α) x₀))
      rw [(extChartAt I α).left_inv (mem_extChartAt_source (I := I) α)])
  · have hcd_pull : ContDiffWithinAt ℝ ∞
        (fun p : ℝ × E =>
          normGradSqFun (I := I) g (f p.1) ((extChartAt I α).symm p.2))
        (S ×ˢ Set.univ) (t₀, (extChartAt I α) x₀) := hNpull_univ
    have hcomp_eq : (extChartAt 𝓘(ℝ, ℝ) (normGradSqFun (I := I) g (f t₀) x₀) ∘
        (fun p : ℝ × M => normGradSqFun (I := I) g (f p.1) p.2) ∘
          (extChartAt (𝓘(ℝ, ℝ).prod I) (t₀, x₀)).symm) =
        (fun p : ℝ × E => normGradSqFun (I := I) g (f p.1) ((extChartAt I α).symm p.2)) := by
      funext z
      simp only [Function.comp_def, extChartAt_prod, extChartAt_coe_symm, α]
      change normGradSqFun (I := I) g (f z.1) ((extChartAt I x₀).symm z.2) =
        normGradSqFun (I := I) g (f z.1) ((extChartAt I x₀).symm z.2)
      rfl
    have hbase : (extChartAt (𝓘(ℝ, ℝ).prod I) (t₀, x₀)) (t₀, x₀) =
        (t₀, (extChartAt I α) x₀) := by
      rw [extChartAt_prod (x := (t₀, x₀))]
      simp [α]
    have hpre : (extChartAt (𝓘(ℝ, ℝ).prod I) (t₀, x₀)).symm ⁻¹'
        (S ×ˢ Set.univ) ∩ range (𝓘(ℝ, ℝ).prod I) ⊆ S ×ˢ Set.univ := by
      intro z hz
      exact ⟨hz.1.1, Set.mem_univ z.2⟩
    have hrange : range (𝓘(ℝ, ℝ).prod I) = Set.univ := by
      apply Set.Subset.antisymm
      · intro y hy
        trivial
      · intro y hy
        have hy2 : y.2 ∈ range I := by
          rw [ModelWithCorners.range_eq_univ I]
          trivial
        rcases hy2 with ⟨x₂, hx₂⟩
        exact ⟨(y.1, x₂), by simp [hx₂]⟩
    have hpost : S ×ˢ Set.univ ⊆ (extChartAt (𝓘(ℝ, ℝ).prod I) (t₀, x₀)).symm ⁻¹'
        (S ×ˢ Set.univ) ∩ range (𝓘(ℝ, ℝ).prod I) := by
      intro z hz
      constructor
      · constructor
        · exact hz.1
        · trivial
      · rw [hrange]
        trivial
    have hdom : (extChartAt (𝓘(ℝ, ℝ).prod I) (t₀, x₀)).symm ⁻¹'
        (S ×ˢ Set.univ) ∩ range (𝓘(ℝ, ℝ).prod I) = S ×ˢ Set.univ :=
      le_antisymm hpre hpost
    rw [hcomp_eq, hbase, hdom]
    exact hcd_pull

omit [T2Space M] [SigmaCompactSpace M] in
theorem timeMulLogDeriv_continuousOn
    {D : RealTimeInterval}
    (g : SmoothRiemannianMetric I M)
    (u : ℝ → M → ℝ)
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2) (D.carrier ×ˢ univ))
    (hslice : ∀ t : ℝ, t ∈ D.carrier → ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t))
    (hpos : ∀ t : ℝ, t ∈ D.carrier → ∀ x : M, 0 < u t x)
    {t : ℝ} (ht : t ∈ D.regular) (ht0 : 0 < t)
    (hslabCarrier : Icc 0 t ⊆ D.carrier)
    (hslabRegular : Ioo 0 t ⊆ D.regular) :
    ContinuousOn (fun p : ℝ × M =>
      p.1 * deriv (fun s : ℝ => Real.log (u s p.2)) p.1)
      (Icc 0 t ×ˢ univ) := by
  classical
  let f : ℝ → M → ℝ := fun s y => Real.log (u s y)
  intro p₀ hp₀
  rcases p₀ with ⟨t₀, y₀⟩
  by_cases ht₀₀ : t₀ = 0
  · subst t₀
    have hfClosed : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => f p.1 p.2) (D.carrier ×ˢ univ) := by
      intro p hp
      have hlogAt : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Real.log (u p.1 p.2) :=
        (Real.contDiffAt_log.2 (hpos p.1 hp.1 p.2).ne').contMDiffAt
      have huAt : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun q : ℝ × M => u q.1 q.2) (D.carrier ×ˢ univ) p := hu p hp
      simpa [f] using (hlogAt.comp_contMDiffWithinAt p huAt : ContMDiffWithinAt
        (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => Real.log (u q.1 q.2))
        (D.carrier ×ˢ univ) p)
    set α : M := y₀ with hα
    have hy₀ : (extChartAt I α) y₀ ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source (mem_extChartAt_source (I := I) α)
    have hΦ : ContDiffWithinAt ℝ ∞
        (fun r : ℝ × E => scalarOnE (I := I) α (f r.1) r.2)
        (D.carrier ×ˢ (extChartAt I α).target) (0, (extChartAt I α) y₀) :=
      scalarOnE_jointContDiffWithinAt (I := I) (M := M) D.carrier f hfClosed α
        (hslabCarrier ⟨le_rfl, ht0.le⟩) hy₀
    have hΦ2 : ContDiffWithinAt ℝ 2
        (fun r : ℝ × E => scalarOnE (I := I) α (f r.1) r.2)
        (D.carrier ×ˢ (extChartAt I α).target) (0, (extChartAt I α) y₀) :=
      hΦ.of_le (by
        exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
    rcases (contDiffWithinAt_succ_iff_hasFDerivWithinAt (n := 1) (by norm_num)).1 hΦ2 with
      ⟨u, hu, h_an, F, hFder, hFcd⟩
    have hFbd0 : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r : ℝ × E in 𝓝[u] (0, (extChartAt I α) y₀),
        ‖F r‖ ≤ C := by
      have hFcont : ContinuousWithinAt F u (0, (extChartAt I α) y₀) :=
        hFcd.continuousWithinAt
      refine ⟨‖F (0, (extChartAt I α) y₀)‖ + 1, ?_, ?_⟩
      · exact add_nonneg (norm_nonneg _) zero_le_one
      · rw [Filter.eventually_iff_exists_mem]
        rcases (Filter.eventually_iff_exists_mem.mp
          ((Metric.continuousWithinAt_iff'.mp hFcont) 1 zero_lt_one)) with ⟨w, hw, hwbd⟩
        refine ⟨w, hw, ?_⟩
        · intro r hr
          calc
            ‖F r‖ = ‖(F r - F (0, (extChartAt I α) y₀)) + F (0, (extChartAt I α) y₀)‖ := by
              congr 1; abel
            _ ≤ ‖F r - F (0, (extChartAt I α) y₀)‖ + ‖F (0, (extChartAt I α) y₀)‖ :=
              norm_add_le _ _
            _ ≤ ‖F (0, (extChartAt I α) y₀)‖ + 1 := by
              have hd : dist (F r) (F (0, (extChartAt I α) y₀)) < 1 := hwbd r hr
              have hd' : ‖F r - F (0, (extChartAt I α) y₀)‖ < 1 := by
                simpa [dist_eq_norm] using hd
              linarith
    rcases hFbd0 with ⟨C₀, hC₀, hC₀bd⟩
    rw [Filter.eventually_iff_exists_mem] at hC₀bd
    rcases hC₀bd with ⟨w, hw, hwbd⟩
    rcases mem_nhdsWithin.1 hu with ⟨ou, hou, hxou, housub⟩
    rcases mem_nhdsWithin.1 hw with ⟨ow, how, hxow, howsub⟩
    let C : ℝ := C₀ * ‖((1 : ℝ), (0 : E))‖
    have hC0 : 0 ≤ C := by
      dsimp [C]
      exact mul_nonneg hC₀ (norm_nonneg ((1 : ℝ), (0 : E)))
    have hbd_pos : ∀ᶠ p : ℝ × M in
        𝓝[(Icc 0 t ×ˢ univ) ∩ {p : ℝ × M | 0 < p.1}] (0, y₀),
        ‖deriv (fun s : ℝ => f s p.2) p.1‖ ≤ C := by
      rw [Filter.eventually_iff_exists_mem]
      refine ⟨(Icc 0 t ×ˢ univ) ∩ {p : ℝ × M | 0 < p.1} ∩
        (Set.univ ×ˢ (extChartAt I α).source) ∩
        (fun p : ℝ × M => (p.1, (extChartAt I α) p.2)) ⁻¹' (ou ∩ ow), ?_, ?_⟩
      · have hsrc : Set.univ ×ˢ (extChartAt I α).source ∈
            𝓝[(Icc 0 t ×ˢ univ) ∩ {p : ℝ × M | 0 < p.1}] (0, y₀) := by
          exact nhdsWithin_le_nhds ((isOpen_univ.prod (isOpen_extChartAt_source
            (I := I) α)).mem_nhds
            ⟨Set.mem_univ 0, mem_extChartAt_source (I := I) α⟩)
        have hchart : ContinuousAt (fun p : ℝ × M => (p.1, (extChartAt I α) p.2)) (0, y₀) := by
          refine continuousAt_fst.prodMk ?_
          exact ContinuousAt.comp
            (f := fun p : ℝ × M => p.2) (x := (0, y₀))
            (continuousAt_extChartAt y₀) continuousAt_snd
        have hpre : (fun p : ℝ × M => (p.1, (extChartAt I α) p.2)) ⁻¹' (ou ∩ ow) ∈
            𝓝[(Icc 0 t ×ˢ univ) ∩ {p : ℝ × M | 0 < p.1}] (0, y₀) :=
          nhdsWithin_le_nhds (hchart (Filter.inter_mem (hou.mem_nhds hxou) (how.mem_nhds hxow)))
        simpa [Set.inter_assoc] using
          Filter.inter_mem (Filter.inter_mem self_mem_nhdsWithin hsrc) hpre
      · intro p hp
        have hp0 : 0 < p.1 := hp.1.1.2
        have hpcar : p.1 ∈ Icc 0 t := hp.1.1.1.1
        have hpreg : p.1 ∈ D.regular := by
          by_cases hpt : p.1 = t
          · rw [hpt]
            exact ht
          · exact hslabRegular ⟨hp0, lt_of_le_of_ne hpcar.2 hpt⟩
        have hpchart : (extChartAt I α) p.2 ∈ (extChartAt I α).target :=
          (extChartAt I α).map_source hp.1.2.2
        let c : ℝ × E := (p.1, (extChartAt I α) p.2)
        have hcou : c ∈ ou := hp.2.1
        have hcow : c ∈ ow := hp.2.2
        have hcu : c ∈ u := by
          exact housub ⟨hcou, Or.inr ⟨hslabCarrier hpcar, hpchart⟩⟩
        have hcw : c ∈ w := howsub ⟨hcow, hcu⟩
        have hun : u ∈ 𝓝 c := by
          refine Filter.mem_of_superset
            (((D.regular_isOpen.prod (isOpen_extChartAt_target (I := I) α)).inter hou).mem_nhds
              (show c ∈ (D.regular ×ˢ (extChartAt I α).target) ∩ ou from
                ⟨⟨hpreg, hpchart⟩, hcou⟩)) ?_
          intro q hq
          exact housub ⟨hq.2, Or.inr ⟨D.regular_subset hq.1.1, hq.1.2⟩⟩
        have hslice_eq : deriv (fun τ : ℝ => f τ p.2) p.1 =
            (F (p.1, (extChartAt I α) p.2)) (1, 0) := by
          have hΦd : HasFDerivAt (fun r : ℝ × E => scalarOnE (I := I) α (f r.1) r.2)
              (F (p.1, (extChartAt I α) p.2)) (p.1, (extChartAt I α) p.2) := by
            exact (hasFDerivWithinAt_of_mem_nhds hun).1 (hFder _ hcu)
          have hfun : (fun τ : ℝ => f τ p.2) =ᶠ[𝓝 p.1]
              (fun τ : ℝ => scalarOnE (I := I) α (f τ) (extChartAt I α p.2)) := by
            rw [Filter.eventuallyEq_iff_exists_mem]
            refine ⟨Set.univ, Filter.univ_mem, ?_⟩
            intro τ hτ
            simp only [scalarOnE_def]
            rw [(extChartAt I α).left_inv hp.1.2.2]
          have hder1 : deriv (fun τ : ℝ => f τ p.2) p.1 =
              deriv (fun τ : ℝ => scalarOnE (I := I) α (f τ) (extChartAt I α p.2)) p.1 :=
            hfun.deriv_eq
          let L : ℝ →L[ℝ] ℝ × E :=
            { toFun := fun a => (a, 0)
              map_add' := by intro a b; ext <;> simp
              map_smul' := by intro a b; ext <;> simp }
          have hg : HasFDerivAt (fun τ : ℝ => (τ, (extChartAt I α) p.2)) L p.1 := by
            have hg' : HasFDerivAt (fun τ : ℝ => (τ, (extChartAt I α) p.2))
                ((1 : ℝ →L[ℝ] ℝ).prod (0 : ℝ →L[ℝ] E)) p.1 := by
              exact (hasFDerivAt_id p.1).prodMk
                (hasFDerivAt_const ((extChartAt I α) p.2) p.1)
            have hL : (1 : ℝ →L[ℝ] ℝ).prod (0 : ℝ →L[ℝ] E) = L := by
              apply ContinuousLinearMap.ext
              intro a
              simp [L, ContinuousLinearMap.prod_apply]
            exact hg'.congr_fderiv hL
          have hcomp := hΦd.comp p.1 hg
          have hder2 : deriv (fun τ : ℝ => scalarOnE (I := I) α (f τ) (extChartAt I α p.2)) p.1 =
              (F (p.1, (extChartAt I α) p.2)) (1, 0) := by
            have hfv : fderiv ℝ (fun τ : ℝ => scalarOnE (I := I) α (f τ) (extChartAt I α p.2)) p.1 =
                (F (p.1, (extChartAt I α) p.2)).comp L := hcomp.fderiv
            rw [deriv]
            rw [hfv]
            simp [L]
          calc
            deriv (fun τ : ℝ => f τ p.2) p.1
                = deriv (fun τ : ℝ => scalarOnE (I := I) α (f τ) (extChartAt I α p.2)) p.1 :=
                  hder1
            _ = (F (p.1, (extChartAt I α) p.2)) (1, 0) := hder2
        have hbdd : ‖deriv (fun s : ℝ => f s p.2) p.1‖ ≤ C := by
          rw [hslice_eq]
          have hle : ‖(F (p.1, (extChartAt I α) p.2)) ((1 : ℝ), (0 : E))‖ ≤
              ‖F (p.1, (extChartAt I α) p.2)‖ * ‖((1 : ℝ), (0 : E))‖ :=
            ContinuousLinearMap.le_opNorm _ _
          have hbd1 : ‖F (p.1, (extChartAt I α) p.2)‖ ≤ C₀ := hwbd _ hcw
          have hbd2 : ‖F (p.1, (extChartAt I α) p.2)‖ * ‖((1 : ℝ), (0 : E))‖ ≤
              C₀ * ‖((1 : ℝ), (0 : E))‖ :=
            mul_le_mul_of_nonneg_right hbd1 (norm_nonneg _)
          exact le_trans hle (by simpa [C] using hbd2)
        exact hbdd
    have hmain : Tendsto (fun p : ℝ × M =>
        p.1 * deriv (fun s : ℝ => f s p.2) p.1)
        (𝓝[Icc 0 t ×ˢ univ] (0, y₀)) (𝓝 0) := by
      have hbd' : ∀ᶠ p : ℝ × M in 𝓝[Icc 0 t ×ˢ univ] (0, y₀),
          ‖p.1 * deriv (fun s : ℝ => f s p.2) p.1‖ ≤ ‖p.1‖ * C := by
        rw [Filter.eventually_iff_exists_mem] at hbd_pos
        rcases hbd_pos with ⟨w, hw, hwbd⟩
        rw [Filter.eventually_iff_exists_mem]
        refine ⟨w ∪ {p : ℝ × M | p.1 = 0}, ?_, ?_⟩
        · rcases mem_nhdsWithin.1 hw with ⟨u, hu_open, hx, husub⟩
          refine mem_nhdsWithin.2 ⟨u, hu_open, hx, ?_⟩
          intro p hp
          by_cases hp0 : 0 < p.1
          · left
            exact husub ⟨hp.1, ⟨hp.2, hp0⟩⟩
          · right
            exact le_antisymm (not_lt.mp hp0) hp.2.1.1
        · intro p hp
          rcases hp with hp | hp0
          · have hd : ‖deriv (fun s : ℝ => f s p.2) p.1‖ ≤ C := hwbd p hp
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left hd (norm_nonneg _)
          · rw [hp0]
            simp
      have hfst : Tendsto (fun p : ℝ × M => ‖p.1‖) (𝓝[Icc 0 t ×ˢ univ] (0, y₀)) (𝓝 0) := by
        have hc : ContinuousWithinAt (fun p : ℝ × M => ‖p.1‖) (Icc 0 t ×ˢ univ) (0, y₀) :=
          continuousWithinAt_fst.norm
        simpa using hc.tendsto
      rw [tendsto_zero_iff_norm_tendsto_zero]
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds
        (by simpa using hfst.mul_const C)
        (by filter_upwards with p; exact norm_nonneg _)
        hbd'
    simpa [ContinuousWithinAt] using hmain
  · have ht₀pos : 0 < t₀ := lt_of_le_of_ne hp₀.1.1 (Ne.symm ht₀₀)
    have ht₀reg : t₀ ∈ D.regular := by
      by_cases ht₀t : t₀ = t
      · subst t₀
        exact ht
      · exact hslabRegular ⟨ht₀pos, lt_of_le_of_ne hp₀.1.2 ht₀t⟩
    have hfReg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => f p.1 p.2) (D.regular ×ˢ univ) := by
      intro p hp
      have hlogAt : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Real.log (u p.1 p.2) :=
        (Real.contDiffAt_log.2 (hpos p.1 (D.regular_subset hp.1) p.2).ne').contMDiffAt
      have huAt : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun q : ℝ × M => u q.1 q.2) (D.regular ×ˢ univ) p :=
        hu.mono (by intro q hq; exact ⟨D.regular_subset hq.1, hq.2⟩) p hp
      simpa [f] using (hlogAt.comp_contMDiffWithinAt p huAt : ContMDiffWithinAt
        (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => Real.log (u q.1 q.2))
        (D.regular ×ˢ univ) p)
    have hDOn : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1)
        (D.regular ×ˢ univ) := by
      have hqOn : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => liYauQuantity g (fun τ y => Real.log (u τ y)) p.1 p.2)
          (D.regular ×ˢ univ) :=
        liYauQuantity_contMDiff (I := I) (M := M) (D := D) g u
          (hu.mono (by intro q hq; exact ⟨D.regular_subset hq.1, hq.2⟩))
          hslice hpos
      have hNOn : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => normGradSqFun (I := I) g (f p.1) p.2)
          (D.regular ×ˢ univ) :=
        normGradSqFun_contMDiffOn (I := I) (M := M) (D := D) g f hfReg
          (fun τ hτ => Moser.contMDiff_log_of_pos_slice
            (hslice τ (D.regular_subset hτ)) (hpos τ (D.regular_subset hτ)))
      have hly_def : ∀ (τ : ℝ) (y : M), liYauQuantity g f τ y =
          normGradSqFun (I := I) g (f τ) y - deriv (fun s : ℝ => f s y) τ := by
        intro τ y
        unfold liYauQuantity
        have hvec : gradientFun (I := I) g (f τ) y = gradFun (I := I) g (f τ) y := by
          apply (metricFlatEquiv (I := I) g y).injective
          ext w
          change g.inner y (gradientFun (I := I) g (f τ) y) w =
            g.inner y (gradFun (I := I) g (f τ) y) w
          rw [inner_gradientFun (I := I) g (f τ) y w]
          rw [inner_gradFun (I := I) g (f τ) y w]
        rw [hvec]
        rw [normGradSqFun]
      exact (hNOn.sub hqOn).congr (by intro p hp; rw [hly_def p.1 p.2]; ring)
    have hcontAt : ContinuousAt (fun p : ℝ × M =>
        p.1 * deriv (fun s : ℝ => f s p.2) p.1) (t₀, y₀) := by
      have hc : ContinuousAt (fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1) (t₀, y₀) :=
        hDOn.continuousOn.continuousAt
          ((IsOpen.prod D.regular_isOpen isOpen_univ).mem_nhds ⟨ht₀reg, trivial⟩)
      exact continuousAt_fst.mul hc
    exact hcontAt.continuousWithinAt

omit [T2Space M] [SigmaCompactSpace M] in
theorem liYauQuantity_mul_time_continuousOn
    {D : RealTimeInterval}
    (g : SmoothRiemannianMetric I M)
    (u : ℝ → M → ℝ)
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2) (D.carrier ×ˢ univ))
    (hslice : ∀ t : ℝ, t ∈ D.carrier → ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t))
    (hpos : ∀ t : ℝ, t ∈ D.carrier → ∀ x : M, 0 < u t x)
    {t : ℝ} (ht : t ∈ D.regular) (ht0 : 0 < t)
    (hslabCarrier : Icc 0 t ⊆ D.carrier)
    (hslabRegular : Ioo 0 t ⊆ D.regular) :
    ContinuousOn (fun p : ℝ × M =>
      p.1 * liYauQuantity g (fun τ y => Real.log (u τ y)) p.1 p.2)
      (Icc 0 t ×ˢ univ) := by
  classical
  let f : ℝ → M → ℝ := fun τ y => Real.log (u τ y)
  have hNcont : ContinuousOn (fun p : ℝ × M =>
      p.1 * normGradSqFun (I := I) g (f p.1) p.2) (Icc 0 t ×ˢ univ) := by
    have hlogClosed : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => f p.1 p.2) (D.carrier ×ˢ univ) := by
      intro p hp
      have hlogAt : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Real.log (u p.1 p.2) :=
        (Real.contDiffAt_log.2 (hpos p.1 hp.1 p.2).ne').contMDiffAt
      have huAt : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun q : ℝ × M => u q.1 q.2) (D.carrier ×ˢ univ) p := hu p hp
      simpa [f] using (hlogAt.comp_contMDiffWithinAt p huAt : ContMDiffWithinAt
        (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => Real.log (u q.1 q.2))
        (D.carrier ×ˢ univ) p)
    have hlogslice : ∀ τ : ℝ, τ ∈ D.carrier → ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => f τ y) :=
      fun τ hτ => Moser.contMDiff_log_of_pos_slice (hslice τ hτ) (hpos τ hτ)
    have hN : ContinuousOn (fun p : ℝ × M =>
        normGradSqFun (I := I) g (f p.1) p.2) (D.carrier ×ˢ univ) := by
      intro p hp
      exact (normGradSqFun_contMDiffWithinAt (I := I) (M := M) D.carrier g f
        hlogClosed hlogslice hp.1 p.2).continuousWithinAt
    have hNslab : ContinuousOn (fun p : ℝ × M =>
        normGradSqFun (I := I) g (f p.1) p.2) (Icc 0 t ×ˢ univ) :=
      hN.mono (by intro p hp; exact ⟨hslabCarrier hp.1, hp.2⟩)
    exact continuousOn_fst.mul hNslab
  have hDcont : ContinuousOn (fun p : ℝ × M =>
      p.1 * deriv (fun s : ℝ => f s p.2) p.1) (Icc 0 t ×ˢ univ) :=
    timeMulLogDeriv_continuousOn (I := I) (M := M) (D := D) g u hu hslice hpos ht ht0
      hslabCarrier hslabRegular
  have hly_def : ∀ (τ : ℝ) (y : M), liYauQuantity g f τ y =
      normGradSqFun (I := I) g (f τ) y - deriv (fun s : ℝ => f s y) τ := by
    intro τ y
    unfold liYauQuantity
    have hvec : gradientFun (I := I) g (f τ) y = gradFun (I := I) g (f τ) y := by
      apply (metricFlatEquiv (I := I) g y).injective
      ext w
      change g.inner y (gradientFun (I := I) g (f τ) y) w =
        g.inner y (gradFun (I := I) g (f τ) y) w
      rw [inner_gradientFun (I := I) g (f τ) y w]
      rw [inner_gradFun (I := I) g (f τ) y w]
    rw [hvec]
    rw [normGradSqFun]
  exact hNcont.sub hDcont |>.congr (by
    intro p hp
    change p.1 * liYauQuantity g f p.1 p.2 =
      p.1 * normGradSqFun (I := I) g (f p.1) p.2 -
        p.1 * deriv (fun s : ℝ => f s p.2) p.1
    rw [hly_def p.1 p.2]
    ring)

theorem liYau_estimate_of_nonnegative_ricci_on_of_metric_family
    [CompactSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M)
    (hRic : ∀ x v, 0 ≤ ricciTensor (I := I) g x v v)
    (D : RealTimeInterval)
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (hGmetric : ∀ t : ℝ, t ∈ D.carrier → G.metric t = g)
    (hGconn : ∀ t : ℝ, t ∈ D.carrier → G.connection t = LeviCivita (G.metric t))
    (u : ℝ → M → ℝ)
    (hu : IsHeatOn D G u)
    (huClosed : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2) (D.carrier ×ˢ univ))
    (hpos : ∀ t : ℝ, t ∈ D.carrier → ∀ x : M, 0 < u t x)
    {t : ℝ} (ht : t ∈ D.regular) (ht0 : 0 < t)
    (hslabCarrier : Icc 0 t ⊆ D.carrier)
    (hslabRegular : Ioo 0 t ⊆ D.regular)
    (x : M) :
    liYauQuantity g (fun τ y => Real.log (u τ y)) t x ≤
      (Module.finrank ℝ E : ℝ) / (2 * t) := by
  classical
  let f : ℝ → M → ℝ := fun τ y => Real.log (u τ y)
  have hlogslice : ∀ τ : ℝ, τ ∈ D.carrier → ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y : M => f τ y) :=
    fun τ hτ => Moser.contMDiff_log_of_pos_slice (hu.sliceSmooth τ hτ) (hpos τ hτ)
  let q : ℝ → M → ℝ := fun τ y => liYauQuantity g f τ y
  have hqOn : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => q p.1 p.2) (D.regular ×ˢ univ) := by
    simpa [f, q] using liYauQuantity_contMDiff (I := I) (M := M) (D := D) g u
      hu.jointSmooth hu.sliceSmooth hpos
  have hqslice : ∀ τ : ℝ, τ ∈ D.regular → ContMDiff I 𝓘(ℝ, ℝ) ∞ (q τ) := by
    intro τ hτ x
    have hnh : D.regular ×ˢ univ ∈ 𝓝 (τ,
      x) := (IsOpen.prod D.regular_isOpen isOpen_univ).mem_nhds ⟨hτ, trivial⟩
    have hqat : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => q p.1 p.2) (τ, x) := hqOn.contMDiffAt hnh
    exact (hqat.comp (x := x) (contMDiffAt_const.prodMk contMDiffAt_id))
  have hpd_all : ∀ (τ : ℝ) (hτ : τ ∈ D.regular) (x : M),
      HasDerivAt (fun s => u s x)
        (deltaLegacy (I := I) g (hu.sliceSmooth τ (D.regular_subset hτ)) x) τ := by
    intro τ hτ x
    have heq := hu.equation τ hτ x
    have hbridge : laplacianAt (I := I) G τ (u τ) x =
        deltaLegacy (I := I) g (hu.sliceSmooth τ (D.regular_subset hτ)) x := by
      have hconn : G.connection τ = LeviCivita (G.metric τ) :=
        hGconn τ (D.regular_subset hτ)
      rw [laplacianAt_eq_delta (I := I) G τ (hu.sliceSmooth τ (D.regular_subset hτ)) hconn x]
      rw [hGmetric τ (D.regular_subset hτ)]
    have heq0 : HasDerivAt (fun s => u s x)
        (laplacianAt (I := I) G τ (u τ) x) τ := by
      simpa using heq
    exact heq0.congr_deriv hbridge
  let n : ℝ := (Module.finrank ℝ E : ℝ)
  have hevol : ∀ (τ : ℝ) (hτ : τ ∈ D.regular) (y : M),
      deriv (fun s => q s y) τ - deltaLegacy (I := I) g (hqslice τ hτ) y ≤
        2 * g.inner y (gradientFun (I := I) g (f τ) y) (gradientFun (I := I) g (q τ) y) -
          (2 / n) * (q τ y)^2 := by
    intro τ hτ y
    have hric0 : ∀ (x : M) (v : TangentSpace I x),
        -(0 : ℝ) * g.inner x v v ≤ ricciTensor (I := I) g x v v := by
      intro x v
      simpa using hRic x v
    simpa [f, q, n] using liYauQuantity_evolution_inequality (I := I) (M := M) (D := D) g
      (K := 0) le_rfl hric0 u hu.jointSmooth hu.sliceSmooth hlogslice hpos hpd_all hqslice hτ y
  let H : ℝ → ℝ → M → ℝ := fun eps τ y => τ * q τ y - n / 2 - eps * τ
  have hH_nonpos : ∀ eps : ℝ, 0 < eps → H eps t x ≤ 0 := by
    intro eps heps
    by_contra hH
    have hHpos : 0 < H eps t x := lt_of_not_ge hH
    have hslab : IsCompact (Set.Icc 0 t ×ˢ (Set.univ : Set M)) :=
      (isCompact_Icc : IsCompact (Set.Icc 0 t)).prod isCompact_univ
    have hcont : ContinuousOn (fun p : ℝ × M => H eps p.1 p.2)
        (Set.Icc 0 t ×ˢ (Set.univ : Set M)) := by
      have hsq : ContinuousOn (fun p : ℝ × M => p.1 * q p.1 p.2)
          (Set.Icc 0 t ×ˢ (Set.univ : Set M)) := by
        simpa [q] using liYauQuantity_mul_time_continuousOn (I := I) (M := M) (D := D) g u
          huClosed hu.sliceSmooth hpos ht ht0 hslabCarrier hslabRegular
      have hfst : ContinuousOn (fun p : ℝ × M => p.1)
          (Set.Icc 0 t ×ˢ (Set.univ : Set M)) := continuousOn_fst
      have hmult : ContinuousOn (fun p : ℝ × M => p.1 * q p.1 p.2)
          (Set.Icc 0 t ×ˢ (Set.univ : Set M)) := hsq
      have hconst : ContinuousOn (fun p : ℝ × M => n / 2)
          (Set.Icc 0 t ×ˢ (Set.univ : Set M)) := continuousOn_const
      have hsub1 : ContinuousOn (fun p : ℝ × M => p.1 * q p.1 p.2 - n / 2)
          (Set.Icc 0 t ×ˢ (Set.univ : Set M)) := hmult.sub hconst
      have heps : ContinuousOn (fun p : ℝ × M => eps * p.1)
          (Set.Icc 0 t ×ˢ (Set.univ : Set M)) := continuousOn_const.mul hfst
      have hsub : ContinuousOn (fun p : ℝ × M => p.1 * q p.1 p.2 - n / 2 - eps * p.1)
          (Set.Icc 0 t ×ˢ (Set.univ : Set M)) := hsub1.sub heps
      exact hsub.congr (by intro p hp; rfl)
    have hnonempty : (Set.Icc 0 t ×ˢ (Set.univ : Set M)).Nonempty :=
      ⟨(t, x), ⟨⟨le_of_lt ht0, le_rfl⟩, trivial⟩⟩
    obtain ⟨sx, hsx, hmax⟩ := hslab.exists_isMaxOn hnonempty hcont
    rcases sx with ⟨s, x₀⟩
    have hmax' : ∀ z : ℝ × M, z ∈ Set.Icc 0 t ×ˢ Set.univ → H eps z.1 z.2 ≤ H eps s x₀ :=
      hmax
    have hmpos : 0 < H eps s x₀ := lt_of_lt_of_le hHpos (hmax' (t, x) ⟨⟨le_of_lt ht0, le_rfl⟩,
      trivial⟩)
    have hsx0 : 0 ≤ s := hsx.1.1
    have hspos : 0 < s := by
      have hs_ne0 : s ≠ 0 := by
        intro hs0
        have hnnonneg : 0 ≤ n := by
          dsimp [n]
          exact_mod_cast Nat.zero_le _
        have h0 : H eps 0 x₀ ≤ 0 := by
          simp [H]
          linarith
        have : H eps s x₀ ≤ 0 := by
          simpa [hs0] using h0
        exact (not_lt_of_ge this) hmpos
      exact lt_of_le_of_ne hsx0 (Ne.symm hs_ne0)
    have hzmax : IsMaxOn (fun τ' : ℝ => H eps τ' x₀) (Set.Icc 0 s) s := by
      intro τ' hτ'
      exact hmax' (τ', x₀) ⟨⟨hτ'.1, hτ'.2.trans hsx.1.2⟩, trivial⟩
    have hsreg : s ∈ D.regular := by
      by_cases hst : s = t
      · subst s
        exact ht
      · exact hslabRegular ⟨hspos, lt_of_le_of_ne hsx.1.2 hst⟩
    have hqTimeDiff : DifferentiableAt ℝ (fun τ' : ℝ => q τ' x₀) s := by
      have hnh : D.regular ×ˢ univ ∈ 𝓝 (s, x₀) :=
        (IsOpen.prod D.regular_isOpen isOpen_univ).mem_nhds ⟨hsreg, trivial⟩
      have hqat : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => q p.1 p.2) (s, x₀) := hqOn.contMDiffAt hnh
      have hsliceAt : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
          (fun τ' : ℝ => q τ' x₀) s :=
        hqat.comp (x := s) (contMDiffAt_id.prodMk contMDiffAt_const)
      exact MDifferentiableAt.differentiableAt
        (ContMDiffAt.mdifferentiableAt (n := ∞) hsliceAt (by norm_num))
    have hval : deriv (fun τ' : ℝ => H eps τ' x₀) s =
        q s x₀ + s * deriv (fun τ' : ℝ => q τ' x₀) s - eps := by
      have hqτdiff : DifferentiableAt ℝ (fun τ' : ℝ => q τ' x₀) s := hqTimeDiff
      have hlin : HasDerivAt (fun τ' : ℝ => τ' * q τ' x₀)
          (q s x₀ + s * deriv (fun τ' : ℝ => q τ' x₀) s) s := by
        simpa using (hasDerivAt_id s).mul hqτdiff.hasDerivAt
      have hconst : HasDerivAt (fun _ : ℝ => n / 2) 0 s := hasDerivAt_const s (n / 2)
      have heps : HasDerivAt (fun τ' : ℝ => eps * τ') eps s := by
        simpa using (hasDerivAt_id s).const_mul eps
      have hmain : HasDerivAt (fun τ' : ℝ => τ' * q τ' x₀ - n / 2 - eps * τ')
          (q s x₀ + s * deriv (fun τ' : ℝ => q τ' x₀) s - eps) s := by
        simpa using (hlin.sub hconst).sub heps
      simpa [H] using hmain.deriv
    have hder : HasDerivAt (fun τ' : ℝ => H eps τ' x₀)
        (deriv (fun τ' : ℝ => H eps τ' x₀) s) s := by
      have hqτdiff : DifferentiableAt ℝ (fun τ' : ℝ => q τ' x₀) s := hqTimeDiff
      have hlin : HasDerivAt (fun τ' : ℝ => τ' * q τ' x₀)
          (q s x₀ + s * deriv (fun τ' : ℝ => q τ' x₀) s) s := by
        simpa using (hasDerivAt_id s).mul hqτdiff.hasDerivAt
      have hconst : HasDerivAt (fun _ : ℝ => n / 2) 0 s := hasDerivAt_const s (n / 2)
      have heps : HasDerivAt (fun τ' : ℝ => eps * τ') eps s := by
        simpa using (hasDerivAt_id s).const_mul eps
      have hmain : HasDerivAt (fun τ' : ℝ => τ' * q τ' x₀ - n / 2 - eps * τ')
          (q s x₀ + s * deriv (fun τ' : ℝ => q τ' x₀) s - eps) s := by
        simpa using (hlin.sub hconst).sub heps
      simpa [H, hval] using hmain
    have htime : 0 ≤ deriv (fun τ' : ℝ => H eps τ' x₀) s :=
      deriv_nonneg_at_right_endpoint_of_isMaxOn_Icc hspos hzmax hder
    have hxmax : IsLocalMax (H eps s) x₀ := by
      exact Filter.Eventually.of_forall (fun y => hmax' (s, y) ⟨⟨hsx.1.1, hsx.1.2⟩, trivial⟩)
    have hslice_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (H eps s) := by
      have hmain : ContMDiff I 𝓘(ℝ, ℝ) ∞
          (fun y : M => s * q s y - n / 2 - eps * s) := by
        exact ((contMDiff_const.mul (hqslice s hsreg)).sub contMDiff_const).sub
          (contMDiff_const.mul contMDiff_const)
      simpa [H] using hmain
    have hlap : laplacianAt (I := I) G s (H eps s) x₀ ≤ 0 :=
      laplacianAt_nonpos_at_spatial_max (I := I) G s hxmax hslice_smooth
    have hgrad : gradientFun (I := I) g (H eps s) x₀ = 0 := by
      exact gradientFun_eq_zero_of_isLocalMax (I := I) g hxmax
        (hslice_smooth.mdifferentiableAt (x := x₀) (by simp))
    have hgradq : gradientFun (I := I) g (q s) x₀ = 0 := by
      have hgradH : gradientFun (I := I) g (H eps s) x₀ = 0 := hgrad
      have hqs_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) (q s) x₀ :=
        (hqslice s hsreg).mdifferentiableAt (x := x₀) (by simp)
      have h1 : gradientFun (I := I) g (fun y : M => s * q s y) x₀ =
          s • gradientFun (I := I) g (q s) x₀ := by
        have hsmul : (fun y : M => s * q s y) = s • q s := rfl
        rw [hsmul]
        exact gradientFun_const_smul (I := I) g s hqs_mdiff
      have h2 : gradientFun (I := I) g (fun _ : M => n / 2 + eps * s) x₀ = 0 := by
        exact gradientFun_const (I := I) g (n / 2 + eps * s) x₀
      have hsub : gradientFun (I := I) g (fun y : M => s * q s y - (n / 2 + eps * s)) x₀ =
          gradientFun (I := I) g (fun y : M => s * q s y) x₀ -
            gradientFun (I := I) g (fun _ : M => n / 2 + eps * s) x₀ :=
          gradientFun_sub (I := I) g
            ((contMDiff_const.mul (hqslice s hsreg)).mdifferentiableAt (x := x₀) (by simp))
            ((contMDiff_const : ContMDiff I 𝓘(ℝ,
              ℝ) ∞ (fun _ : M => n / 2 + eps * s)).mdifferentiableAt
              (x := x₀) (by norm_num))
      have hHdef : (H eps s) = fun y : M => s * q s y - (n / 2 + eps * s) := by
        funext y
        simp [H]
        ring
      rw [hHdef] at hgradH
      rw [hsub, h1, h2] at hgradH
      have hgradH' : s • gradientFun (I := I) g (q s) x₀ = 0 := by
        exact sub_eq_zero.mp hgradH
      exact (smul_eq_zero.mp hgradH').resolve_left (ne_of_gt hspos)
    have hgradq' : g.inner x₀ (gradientFun (I := I) g (f s) x₀) (gradientFun (I := I) g
      (q s) x₀) = 0 := by
      rw [hgradq]
      simp
    have hconn : G.connection s = LeviCivita (G.metric s) :=
      hGconn s (D.regular_subset hsreg)
    have hev0 := hevol s hsreg x₀
    have hdq_Δq : deriv (fun τ' : ℝ => q τ' x₀) s - laplacianAt (I := I) G s (q s) x₀ ≤
        -(2 / n) * (q s x₀)^2 := by
      have hlapeq : laplacianAt (I := I) G s (q s) x₀ = deltaLegacy (I := I) g
        (hqslice s hsreg) x₀ := by
        rw [laplacianAt_eq_delta (I := I) G s (hqslice s hsreg) hconn]
        rw [hGmetric s (D.regular_subset hsreg)]
      have hcanc : 2 * g.inner x₀ (gradientFun (I := I) g (f s) x₀) (gradientFun (I := I) g
        (q s) x₀) = 0 := by
        rw [hgradq']
        ring
      have hev0' : deriv (fun τ' : ℝ => q τ' x₀) s - deltaLegacy (I := I) g (hqslice s hsreg) x₀ ≤
          -(2 / n) * (q s x₀)^2 := by
        nlinarith [hev0, hcanc]
      rw [hlapeq]
      exact hev0'
    have hlapH : laplacianAt (I := I) G s (H eps s) x₀ =
        s * laplacianAt (I := I) G s (q s) x₀ := by
      have hHdef : (H eps s) = fun y : M => s • q s y - (n / 2 + eps * s) := by
        funext y
        simp [H]
        ring
      have hcq : laplacianAt (I := I) G s (fun _ : M => n / 2 + eps * s) x₀ = 0 := by
        rw [laplacianAt_eq_delta (I := I) G s contMDiff_const hconn]
        rw [hGmetric s (D.regular_subset hsreg)]
        exact Δ_g_const (I := I) g (n / 2 + eps * s) x₀
      have hsub_cd : ContMDiff I 𝓘(ℝ, ℝ) ∞
          (fun y : M => s • q s y - (n / 2 + eps * s)) := by
        have hscd : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => s • q s y) := by
          simpa [Pi.smul_apply] using contMDiff_const.mul (hqslice s hsreg)
        exact hscd.sub contMDiff_const
      have hdiff : laplacianAt (I := I) G s
          (fun y : M => s • q s y - (n / 2 + eps * s)) x₀ =
          laplacianAt (I := I) G s (s • q s) x₀ - laplacianAt (I := I) G s
            (fun _ : M => n / 2 + eps * s) x₀ := by
        rw [laplacianAt_eq_delta (I := I) G s hsub_cd hconn]
        have hscd : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => s • q s y) := by
          simpa [Pi.smul_apply] using contMDiff_const.mul (hqslice s hsreg)
        have hc_cd : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => n / 2 + eps * s) :=
          contMDiff_const
        change deltaLegacy (I := I) (G.metric s) hsub_cd x₀ =
          laplacianAt (I := I) G s (fun y : M => s • q s y) x₀ -
            laplacianAt (I := I) G s (fun _ : M => n / 2 + eps * s) x₀
        rw [laplacianAt_eq_delta (I := I) G s hscd hconn]
        rw [laplacianAt_eq_delta (I := I) G s hc_cd hconn]
        rw [hGmetric s (D.regular_subset hsreg)]
        have hsum := Δ_g_add (I := I) g ⟨_, hscd⟩ ⟨_, ContMDiff.neg hc_cd⟩ x₀
        have hneg := Δ_g_neg (I := I) g hc_cd (x := x₀)
        have hc_eq : (fun y : M => s • q s y - (n / 2 + eps * s)) =ᶠ[𝓝 x₀]
            (fun y : M => s • q s y + -(n / 2 + eps * s)) := by
          rw [Filter.eventuallyEq_iff_exists_mem]
          refine ⟨Set.univ, Filter.univ_mem, ?_⟩
          intro y hy
          ring
        have hbridge := Δ_g_congr_of_eventuallyEq (I := I) g hsub_cd
          (hscd.add (ContMDiff.neg hc_cd)) hc_eq
        unfold deltaLegacy
        rw [hbridge]
        change Δ_g (I := I) g
            (⟨_, hscd⟩ + ⟨_, ContMDiff.neg hc_cd⟩) x₀ = _
        rw [hsum]
        rw [hneg]
        ring
      have hlapS : laplacianAt (I := I) G s (s • q s) x₀ =
          s * laplacianAt (I := I) G s (q s) x₀ := by
        exact laplacianAt_smul (I := I) G s s
          (fun y => (hqslice s hsreg).mdifferentiableAt (x := y) (by simp))
          (gradientFun_mdiffAt (I := I) (G.metric s) (hqslice s hsreg) x₀)
      rw [hHdef, hdiff, hcq, hlapS]
      ring
    have hineq : deriv (fun τ' : ℝ => H eps τ' x₀) s -
        laplacianAt (I := I) G s (H eps s) x₀ ≤
        q s x₀ - (2 * s / n) * (q s x₀)^2 - eps := by
      rw [hval, hlapH]
      have hlin2 : s * (deriv (fun τ' : ℝ => q τ' x₀) s - laplacianAt (I := I) G s (q s) x₀) ≤
          s * (-(2 / n) * (q s x₀)^2) :=
        mul_le_mul_of_nonneg_left hdq_Δq hspos.le
      have hrewrite : s * (-(2 / n) * (q s x₀)^2) = -((2 * s / n) * (q s x₀)^2) := by
        field_simp [n, hspos.ne']
      rw [hrewrite] at hlin2
      linarith
    have hnonneg : 0 ≤ deriv (fun τ' : ℝ => H eps τ' x₀) s -
        laplacianAt (I := I) G s (H eps s) x₀ := by
      linarith [htime, hlap]
    have hqbig : n / (2 * s) < q s x₀ := by
      have hHpos' : 0 < s * q s x₀ - n / 2 - eps * s := by
        simpa [H] using hmpos
      have hn : 0 < n := by
        dsimp [n]
        exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
      have hs2 : 0 < 2 * s := mul_pos zero_lt_two hspos
      have hq_gt : n / (2 * s) + eps < q s x₀ := by
        have hmain : n / 2 + eps * s < s * q s x₀ := by linarith
        have hmain' : n / 2 + eps * s < q s x₀ * s := by nlinarith [hmain]
        have hdiv : (n / 2 + eps * s) / s < q s x₀ :=
          (div_lt_iff₀ hspos).mpr hmain'
        have hrewrite : (n / 2 + eps * s) / s = n / (2 * s) + eps := by
          field_simp [hspos.ne']
        simpa [hrewrite] using hdiv
      linarith
    have hneg : q s x₀ - (2 * s / n) * (q s x₀)^2 - eps < 0 := by
      have hn : 0 < n := by
        dsimp [n]
        exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
      have hqpos : 0 < q s x₀ := lt_trans
        (div_pos hn (mul_pos zero_lt_two hspos)) hqbig
      have h1 : 1 - (2 * s / n) * q s x₀ < 0 := by
        have hmul : (2 * s / n) * q s x₀ > (2 * s / n) * (n / (2 * s)) :=
          mul_lt_mul_of_pos_left hqbig
            (div_pos (mul_pos zero_lt_two hspos) hn)
        have hcancel : (2 * s / n) * (n / (2 * s)) = 1 := by
          field_simp [hspos.ne', hn.ne']
        have hmul' : 1 < (2 * s / n) * q s x₀ := by
          simpa [hcancel] using hmul
        linarith
      have hq_main : q s x₀ - (2 * s / n) * (q s x₀)^2 < 0 := by
        have hfactor : q s x₀ - (2 * s / n) * (q s x₀)^2 =
            q s x₀ * (1 - (2 * s / n) * q s x₀) := by ring
        rw [hfactor]
        exact mul_neg_of_pos_of_neg hqpos h1
      linarith
    exact (lt_irrefl (0 : ℝ))
      (lt_of_le_of_lt (le_trans hnonneg hineq) hneg)
  have hfin : ∀ eps : ℝ, 0 < eps → H eps t x ≤ 0 :=
    fun eps heps => hH_nonpos eps heps
  have hqt : liYauQuantity g f t x ≤ n / (2 * t) := by
    have htq_le : t * liYauQuantity g f t x - n / 2 ≤ 0 := by
      by_contra hnot
      have hpos : 0 < t * liYauQuantity g f t x - n / 2 := lt_of_not_ge hnot
      let eps : ℝ := (t * liYauQuantity g f t x - n / 2) / (2 * t)
      have heps_pos : 0 < eps := div_pos hpos (mul_pos zero_lt_two ht0)
      have hfin_eps : H eps t x ≤ 0 := hfin eps heps_pos
      have hle : t * liYauQuantity g f t x - n / 2 ≤ eps * t := by
        simpa [H, eps] using hfin_eps
      have hrewrite : eps * t = (t * liYauQuantity g f t x - n / 2) / 2 := by
        dsimp [eps]
        field_simp [ht0.ne']
      have heps_lt : eps * t < t * liYauQuantity g f t x - n / 2 := by
        rw [hrewrite]
        linarith
      exact (not_le_of_gt heps_lt) hle
    have htle : t * liYauQuantity g f t x ≤ n / 2 := by linarith
    have hq2 : liYauQuantity g f t x * (2 * t) ≤ n := by
      have h2tq : 2 * (t * liYauQuantity g f t x) ≤ n := by nlinarith [htle]
      have hring : liYauQuantity g f t x * (2 * t) = 2 * (t * liYauQuantity g f t x) := by ring
      rwa [hring]
    exact (le_div_iff₀ (mul_pos zero_lt_two ht0)).mpr hq2
  simpa [f, q, n] using hqt

theorem liYau_estimate_of_nonnegative_ricci_on
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
    {t : ℝ} (ht : t ∈ D.regular) (ht0 : 0 < t)
    (hslabCarrier : Icc 0 t ⊆ D.carrier)
    (hslabRegular : Ioo 0 t ⊆ D.regular)
    (x : M) :
    liYauQuantity g (fun τ y => Real.log (u τ y)) t x ≤
      (Module.finrank ℝ E : ℝ) / (2 * t) := by
  exact liYau_estimate_of_nonnegative_ricci_on_of_metric_family
    (I := I) (M := M) g hRic D (stationaryMetricFamily (I := I) (M := M) g)
    (by intro τ hτ; rfl) (by intro τ hτ; rfl)
    u hu huClosed hpos ht ht0 hslabCarrier hslabRegular x

theorem liYau_estimate_of_nonnegative_ricci
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
    {t : ℝ} (ht : 0 < t) (x : M) :
    liYauQuantity g (fun τ y => Real.log (u τ y)) t x ≤
      (Module.finrank ℝ E : ℝ) / (2 * t) := by
  classical
  let D : RealTimeInterval := RealTimeInterval.univ 0
  let G : MetricConnectionFamily (I := I) (M := M) ℝ :=
    stationaryMetricFamily (I := I) (M := M) g
  have hGmetric : ∀ τ : ℝ, G.metric τ = g := by
    intro τ
    dsimp [G]
    rfl
  have hGconn : ∀ τ : ℝ, G.connection τ = LeviCivita (G.metric τ) := by
    intro τ
    dsimp [G]
    rfl
  have huOn : IsHeatOnStationary D g u := by
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
          Δ_g (I := I) g
            ⟨(smoothScalarSlice (I := I) g u hu τ).toFun,
              (smoothScalarSlice (I := I) g u hu τ).smooth⟩ x
        rw [laplacianAt_eq_delta (I := I) G τ (smoothScalarSlice (I := I) g u hu τ).smooth
          (hGconn τ) x]
        rw [hGmetric τ]
      have hderiv : deriv (fun s => u s x) τ = laplacianAt (I := I) G τ (u τ) x := by
        rw [hpde τ x, ← hlap]
      convert hder.congr_deriv hderiv using 1
      simp [G]
  simpa [D, G] using liYau_estimate_of_nonnegative_ricci_on (I := I) (M := M) g hRic D
    u huOn (by simpa [D] using hu.contMDiffOn) (fun τ hτ x => hpos τ x) (t := t)
    (by change t ∈ (Set.univ : Set ℝ); trivial)
    ht (by intro τ hτ; trivial) (by intro τ hτ; trivial) x

theorem heat_solution_differential_harnack_of_nonnegative_ricci_on_of_metric_family
    [CompactSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M)
    (hRic : ∀ x v, 0 ≤ ricciTensor (I := I) g x v v)
    (D : RealTimeInterval)
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (hGmetric : ∀ t : ℝ, t ∈ D.carrier → G.metric t = g)
    (hGconn : ∀ t : ℝ, t ∈ D.carrier → G.connection t = LeviCivita (G.metric t))
    (u : ℝ → M → ℝ)
    (hu : IsHeatOn D G u)
    (huClosed : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2) (D.carrier ×ˢ univ))
    (hpos : ∀ t : ℝ, t ∈ D.carrier → ∀ x : M, 0 < u t x)
    {t : ℝ} (ht : t ∈ D.regular) (ht0 : 0 < t)
    (hslabCarrier : Icc 0 t ⊆ D.carrier)
    (hslabRegular : Ioo 0 t ⊆ D.regular)
    (x : M) :
    -(Module.finrank ℝ E : ℝ) / (2 * t) ≤
      deriv (fun s => u s x) t / u t x -
        g.inner x (gradientFun (I := I) g (u t) x)
          (gradientFun (I := I) g (u t) x) / (u t x ^ 2) := by
  classical
  have hly := liYau_estimate_of_nonnegative_ricci_on_of_metric_family
    (I := I) (M :=
      M) g hRic D G hGmetric hGconn u hu huClosed hpos ht ht0 hslabCarrier hslabRegular x
  have hlogderiv : deriv (fun s => Real.log (u s x)) t = deriv (fun s => u s x) t / u t x := by
    have hder : HasDerivAt (fun s => u s x) (deriv (fun s => u s x) t) t := by
      exact (hu.equation t ht x).congr_deriv (hu.equation t ht x).deriv.symm
    exact (hder.log (hpos t (D.regular_subset ht) x).ne').deriv
  have hloggrad : g.inner x
        (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
        (gradientFun (I := I) g (fun y => Real.log (u t y)) x) =
      (u t x ^ 2)⁻¹ *
        g.inner x (gradientFun (I := I) g (u t) x)
          (gradientFun (I := I) g (u t) x) := by
    have hu_slice_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) x :=
      (hu.sliceSmooth t (D.regular_subset ht)).mdifferentiableAt (x := x) (by simp)
    exact Moser.inner_gradientFun_log_self (I := I) g hu_slice_mdiff
      (hpos t (D.regular_subset ht) x)
  unfold liYauQuantity at hly
  rw [hloggrad, hlogderiv] at hly
  have hrewrite : (u t x ^ 2)⁻¹ * g.inner x
        (gradientFun (I := I) g (u t) x)
        (gradientFun (I := I) g (u t) x) =
      g.inner x (gradientFun (I := I) g (u t) x)
          (gradientFun (I := I) g (u t) x) / (u t x ^ 2) := by
    field_simp [ne_of_gt (hpos t (D.regular_subset ht) x)]
  rw [hrewrite] at hly
  have h1 : -(Module.finrank ℝ E : ℝ) / (2 * t) = -((Module.finrank ℝ E : ℝ) / (2 * t)) := by ring
  rw [h1]
  linarith

theorem heat_solution_differential_harnack_of_nonnegative_ricci_on
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
    {t : ℝ} (ht : t ∈ D.regular) (ht0 : 0 < t)
    (hslabCarrier : Icc 0 t ⊆ D.carrier)
    (hslabRegular : Ioo 0 t ⊆ D.regular)
    (x : M) :
    -(Module.finrank ℝ E : ℝ) / (2 * t) ≤
      deriv (fun s => u s x) t / u t x -
        g.inner x (gradientFun (I := I) g (u t) x)
          (gradientFun (I := I) g (u t) x) / (u t x ^ 2) := by
  exact heat_solution_differential_harnack_of_nonnegative_ricci_on_of_metric_family
    (I := I) (M := M) g hRic D (stationaryMetricFamily (I := I) (M := M) g)
    (by intro τ hτ; rfl) (by intro τ hτ; rfl)
    u hu huClosed hpos ht ht0 hslabCarrier hslabRegular x

theorem heat_solution_differential_harnack_of_nonnegative_ricci
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
    {t : ℝ} (ht : 0 < t) (x : M) :
    -(Module.finrank ℝ E : ℝ) / (2 * t) ≤
      deriv (fun s => u s x) t / u t x -
        g.inner x (gradientFun (I := I) g (u t) x)
          (gradientFun (I := I) g (u t) x) / (u t x ^ 2) := by
  classical
  have hly := liYau_estimate_of_nonnegative_ricci (I := I) (M := M) g hRic u hu hpos hpde ht x
  have hlogderiv : deriv (fun s => Real.log (u s x)) t = deriv (fun s => u s x) t / u t x := by
    have hu_slice : ContDiff ℝ ∞ (fun s => u s x) := by
      have hc : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) ∞ (fun s : ℝ => (s, x)) :=
        contMDiff_id.prodMk contMDiff_const
      exact contMDiff_iff_contDiff.mp (hu.comp hc)
    have hder : HasDerivAt (fun s => u s x) (deriv (fun s => u s x) t) t :=
      (ContDiff.differentiable hu_slice (by norm_num) t).hasDerivAt
    exact (hder.log (hpos t x).ne').deriv
  have hloggrad : g.inner x
        (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
        (gradientFun (I := I) g (fun y => Real.log (u t y)) x) =
      (u t x ^ 2)⁻¹ *
        g.inner x (gradientFun (I := I) g (u t) x)
          (gradientFun (I := I) g (u t) x) := by
    have hu_slice_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) x :=
      (hu.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiableAt (x := x) (by simp)
    exact Moser.inner_gradientFun_log_self (I := I) g hu_slice_mdiff (hpos t x)
  unfold liYauQuantity at hly
  rw [hloggrad, hlogderiv] at hly
  have hrewrite : (u t x ^ 2)⁻¹ * g.inner x
        (gradientFun (I := I) g (u t) x)
        (gradientFun (I := I) g (u t) x) =
      g.inner x (gradientFun (I := I) g (u t) x)
          (gradientFun (I := I) g (u t) x) / (u t x ^ 2) := by
    field_simp [ne_of_gt (hpos t x)]
  rw [hrewrite] at hly
  have h1 : -(Module.finrank ℝ E : ℝ) / (2 * t) = -((Module.finrank ℝ E : ℝ) / (2 * t)) := by ring
  rw [h1]
  linarith

end DifferentialGeometry.Analysis.Parabolic.Harnack
