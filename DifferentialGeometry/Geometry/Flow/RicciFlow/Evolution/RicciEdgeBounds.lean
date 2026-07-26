import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamilyContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ChartRicciJetIdentity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ExtendedSolutionRegularity

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Initial-edge bounds for a smooth Ricci-flow family

This file starts the regularizing-edge package needed by forward uniqueness.
The first producer below extracts the purely topological part: joint chart-Gram
continuity up to the initial time gives uniform two-sided metric equivalence on
every compact initial time slab.  The later producers expose the exact weak
chart equation and the interior/improper time-integral identities supplied by
the Ricci PDE.  Spatial derivative bounds remain a separate parabolic-regularity
frontier.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter MeasureTheory Set
open scoped Manifold ContDiff Interval Topology
open DifferentialGeometry
open DifferentialGeometry.Analysis
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- Joint chart-Gram regularity up to the initial time gives one metric
equivalence constant on every compact initial subinterval.  This is the
zeroth-order component of the regularizing-edge estimates used in smooth
forward uniqueness. -/
theorem ricciEdgeMetric
    (g : Real → SmoothRiemannianMetric I M) {a b c : Real}
    (hab : a < b) (hcb : c < b)
    (hcont : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun p : Real × M =>
          Integral.Measure.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∃ Λ : Real, 1 ≤ Λ ∧
      ∀ t ∈ Set.Icc a c, ∀ x : M, ∀ v : TangentSpace I x,
        Λ⁻¹ * (g a).inner x v v ≤ (g t).inner x v v ∧
          (g t).inner x v v ≤ Λ * (g a).inner x v v := by
  have hG : Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2
      (Set.Ico a b)
      (fun t x => Tensor0SBundle.metricTensorField (I := I) (g t) x) := by
    apply metricTensorCont_of_chartGram (K := Set.Ico a b) g
    intro x₀ i j
    have hincl : Continuous
        (fun q : {t : Real // t ∈ Set.Ico a b} × M => ((q.1 : Real), q.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    have hcomp : ContinuousOn
        ((fun p : Real × M =>
            Integral.Measure.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j) ∘
          (fun q : {t : Real // t ∈ Set.Ico a b} × M => ((q.1 : Real), q.2)))
        {q : {t : Real // t ∈ Set.Ico a b} × M |
          q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet} :=
      (hcont x₀ i j).comp hincl.continuousOn (fun q hq => ⟨q.1.2, hq⟩)
    simpa only [Function.comp_apply] using hcomp
  have hK : Set.Icc a c ⊆ Set.Ico a b := by
    intro t ht
    exact ⟨ht.1, lt_of_le_of_lt ht.2 hcb⟩
  have hGt : Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2
      (Set.Icc a c)
      (fun t x => Tensor0SBundle.metricTensorField (I := I) (g t) x) := by
    exact Tensor0SFamilyContinuousOnSet.mono (I := I) (M := M) hG hK
  have haD : a ∈ Set.Ico a b := ⟨le_rfl, hab⟩
  have hGa : Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2
      (Set.Icc a c)
      (fun _ x => Tensor0SBundle.metricTensorField (I := I) (g a) x) := by
    exact Tensor0SFamilyContinuousOnSet.comp_time (I := I) (M := M)
      (K := Set.Icc a c) (L := Set.Ico a b) hG
      (continuous_const : Continuous (fun _ : Real => a))
      (fun _ _ => haD)
  have hquadT : Continuous
      (metricTimeBundleQuad (I := I) (M := M) g (Set.Icc a c)) := by
    have hq := tensor0SFamily_quadCont (I := I) (M := M) hGt
    simpa [metricTimeBundleQuad, quad02,
      Tensor0SBundle.metricTensorField_apply] using hq
  have hquadA : Continuous
      (metricTimeBundleQuad (I := I) (M := M) (fun _ => g a) (Set.Icc a c)) := by
    have hq := tensor0SFamily_quadCont (I := I) (M := M) hGa
    simpa [metricTimeBundleQuad, quad02,
      Tensor0SBundle.metricTensorField_apply] using hq
  have hcompactT := metricUnitTimeSlab_icc_compact_of_bundle
    (I := I) (M := M) g a c (g a) hquadT
  have hcompactA := metricUnitTimeSlab_icc_compact_of_bundle
    (I := I) (M := M) (fun _ => g a) a c (g a) hquadA
  have htotalT := Tensor0SFamilyContinuousOnSet.tangentBundle
    (I := I) (M := M) hGt
  have htotalA := Tensor0SFamilyContinuousOnSet.tangentBundle
    (I := I) (M := M) hGa
  have habsT := timeSlabAbsQuadCont (I := I) (M := M)
    (G := fun _ => g a)
    (A := fun t x => Tensor0SBundle.metricTensorField (I := I) (g t) x)
    (Set.Icc a c) htotalT
  have habsA := timeSlabAbsQuadCont (I := I) (M := M)
    (G := g)
    (A := fun _ x => Tensor0SBundle.metricTensorField (I := I) (g a) x)
    (Set.Icc a c) htotalA
  obtain ⟨C₁, hC₁, hupper⟩ := compactUnitTimeSlab_absBound
    (I := I) (M := M) (fun _ => g a)
    (fun t x => Tensor0SBundle.metricTensorField (I := I) (g t) x)
    (Set.Icc a c) hcompactA habsT
  obtain ⟨C₂, hC₂, hlower⟩ := compactUnitTimeSlab_absBound
    (I := I) (M := M) g
    (fun _ x => Tensor0SBundle.metricTensorField (I := I) (g a) x)
    (Set.Icc a c) hcompactT habsA
  let Λ : Real := max 1 (max C₁ C₂)
  have hΛ : 1 ≤ Λ := le_max_left _ _
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  refine ⟨Λ, hΛ, ?_⟩
  intro t ht x v
  have hq₀ : 0 ≤ (g a).inner x v v := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact ((g a).pos x v hv).le
  have hqt : 0 ≤ (g t).inner x v v := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact ((g t).pos x v hv).le
  have huAbs := hupper t ht x v
  have hlAbs := hlower t ht x v
  simp only [quad02, Tensor0SBundle.metricTensorField_apply] at huAbs hlAbs
  have hu : (g t).inner x v v ≤ C₁ * (g a).inner x v v :=
    (le_abs_self _).trans huAbs
  have hl : (g a).inner x v v ≤ C₂ * (g t).inner x v v :=
    (le_abs_self _).trans hlAbs
  have hC₁Λ : C₁ ≤ Λ := le_trans (le_max_left C₁ C₂) (le_max_right 1 _)
  have hC₂Λ : C₂ ≤ Λ := le_trans (le_max_right C₁ C₂) (le_max_right 1 _)
  have hlΛ : (g a).inner x v v ≤ Λ * (g t).inner x v v :=
    hl.trans (mul_le_mul_of_nonneg_right hC₂Λ hqt)
  constructor
  · calc
      Λ⁻¹ * (g a).inner x v v ≤ Λ⁻¹ * (Λ * (g t).inner x v v) :=
        mul_le_mul_of_nonneg_left hlΛ (inv_nonneg.mpr hΛpos.le)
      _ = (g t).inner x v v := by simp [hΛpos.ne']
  · exact hu.trans (mul_le_mul_of_nonneg_right hC₁Λ hq₀)

/-- On the regular interior, the geometric Ricci-flow equation is exactly the
weakly parabolic chart-Gram `2`-jet equation.  This is the coordinate PDE that
an initial-edge gauge or boundary-regularity argument must improve to a
strictly parabolic system; no such improvement is asserted here. -/
theorem ricciEdgeChartPDE
    (g : ℝ → SmoothRiemannianMetric I M) {a b t : ℝ}
    (hpde : ∀ r ∈ Set.Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g r) x v w) (Set.Ici a) r)
    (α : M) {y : E} (ht : t ∈ Set.Ioo a b)
    (hy : y ∈ interior (extChartAt I α).target)
    (hgood : (extChartAt I α).symm y ∈ chartLeviCivitaGoodSet (I := I) α) :
    derivWithin (fun s => chartGramPi (I := I) (g s) α y) (Set.Ioo a b) t =
      jetRicciFlow (chartModelBasis E) (jet2 (chartGramPi (I := I) (g t) α) y) := by
  have hStatic : ContDiffOn ℝ ∞ (chartGramPi (I := I) (g t) α)
      (interior (extChartAt I α).target) := by
    refine contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => ?_
    exact (chartGramOnE_contDiffOn (I := I) (g t) α i j).mono interior_subset
  have hAt : ContDiffAt ℝ ∞ (chartGramPi (I := I) (g t) α) y :=
    hStatic.contDiffAt (isOpen_interior.mem_nhds hy)
  have hG : DifferentiableAt ℝ (chartGramPi (I := I) (g t) α) y :=
    hAt.differentiableAt (by simp)
  have hG1 : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ (chartGramPi (I := I) (g t) α) z := by
    filter_upwards [isOpen_interior.mem_nhds hy] with z hz
    exact (hStatic.contDiffAt (isOpen_interior.mem_nhds hz)).differentiableAt (by simp)
  have hG2 : DifferentiableAt ℝ
      (fun z => fderiv ℝ (chartGramPi (I := I) (g t) α) z) y :=
    (hAt.fderiv_right (m := ∞) le_rfl).differentiableAt (by simp)
  apply chartGramEvolution_of_pde g α (isOpen_Ioo.uniqueDiffWithinAt ht) hy hG hG1 hG2
  intro i k
  apply chartGramEntryPDE_of_metricPDE g α hgood
    ((extChartAt I α).right_inv (interior_subset hy)) i k
  exact (hpde t (Set.Ioo_subset_Ico_self ht) ((extChartAt I α).symm y)
    (chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y))
    (chartBasisVecFiber (I := I) α k ((extChartAt I α).symm y))).mono
      (fun r hr => hr.1.le)

/-- On every compact time interval strictly inside the regular slab, the
metric variation is the time integral of `-2 Ric`.  Joint interior
chart-Gram smoothness supplies continuity (hence integrability) of the Ricci
integrand; the raw metric PDE supplies the derivative. -/
theorem ricciEdgeIntegral
    (g : ℝ → SmoothRiemannianMetric I M) {a b s t : ℝ}
    (hsmooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hpde : ∀ r ∈ Set.Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun u : ℝ => (g u).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g r) x v w) (Set.Ici a) r)
    (hs : a < s) (hst : s ≤ t) (ht : t < b)
    (x : M) (v w : TangentSpace I x) :
    (∫ r in s..t, (-2 : ℝ) * ricciTensor (I := I) (g r) x v w) =
      (g t).inner x v w - (g s).inner x v w := by
  have hRicFam := ricciCont_interior_of_chartGram (I := I) g a b hsmooth
  have hRicEval : ContinuousOn
      (fun r : ℝ => metricRicciAt (I := I) (g r) x
        (DifferentialGeometry.Integral.Connection.vec2 v w)) (Set.Ioo a b) := by
    rw [continuousOn_iff_continuous_restrict]
    exact hRicFam.eval_continuous (P := {r : ℝ // r ∈ Set.Ioo a b})
      (τ := Subtype.val) (b := fun _ => x) continuous_subtype_val
      (fun r => r.2) continuous_const
      (v := fun i _ => DifferentialGeometry.Integral.Connection.vec2 v w i)
      (fun _ => continuous_const)
  have hRic : ContinuousOn
      (fun r : ℝ => ricciTensor (I := I) (g r) x v w) (Set.Ioo a b) := by
    refine hRicEval.congr (fun r _ => ?_)
    exact (metricRicciAt_apply_eq_ricciTensor (I := I) (g r) x v w).symm
  have hseg : Set.Icc s t ⊆ Set.Ioo a b := by
    intro r hr
    exact ⟨lt_of_lt_of_le hs hr.1, lt_of_le_of_lt hr.2 ht⟩
  have hint : IntervalIntegrable
      (fun r : ℝ => (-2 : ℝ) * ricciTensor (I := I) (g r) x v w)
      volume s t :=
    ContinuousOn.intervalIntegrable_of_Icc hst ((hRic.const_mul (-2)).mono hseg)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hint
  intro r hr
  rw [Set.uIcc_of_le hst] at hr
  have har : a < r := lt_of_lt_of_le hs hr.1
  have hrmem : r ∈ Set.Ico a b := ⟨har.le, lt_of_le_of_lt hr.2 ht⟩
  exact (hpde r hrmem x v w).hasDerivAt (Ici_mem_nhds har)

/-- The interior Ricci integrals have the correct improper limit at the
initial edge.  This is deliberately an improper-limit statement: the exact
endpoint hypotheses do not yet imply Lebesgue integrability of `Ric` on the
closed interval starting at `a`. -/
theorem ricciEdgeImproper
    (g : ℝ → SmoothRiemannianMetric I M) {a b t : ℝ}
    (hsmooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hpde : ∀ r ∈ Set.Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun u : ℝ => (g u).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g r) x v w) (Set.Ici a) r)
    (ht : t ∈ Set.Ioo a b) (x : M) (v w : TangentSpace I x) :
    Tendsto
      (fun s : ℝ => ∫ r in s..t, (-2 : ℝ) * ricciTensor (I := I) (g r) x v w)
      (𝓝[>] a) (𝓝 ((g t).inner x v w - (g a).inner x v w)) := by
  let f : ℝ → ℝ := fun r => (g r).inner x v w
  have hf : Tendsto f (𝓝[>] a) (𝓝 (f a)) :=
    ((hpde a ⟨le_rfl, ht.1.trans ht.2⟩ x v w).continuousWithinAt.tendsto).mono_left
      (nhdsWithin_mono a Set.Ioi_subset_Ici_self)
  have hdiff : Tendsto (fun s : ℝ => f t - f s) (𝓝[>] a) (𝓝 (f t - f a)) :=
    tendsto_const_nhds.sub hf
  have heq :
      (fun s : ℝ => ∫ r in s..t, (-2 : ℝ) * ricciTensor (I := I) (g r) x v w)
        =ᶠ[𝓝[>] a] fun s => f t - f s := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht.1)] with s hsa hst
    exact ricciEdgeIntegral (I := I) g hsmooth hpde hsa hst.le ht.2 x v w
  exact Filter.Tendsto.congr' heq.symm hdiff

end DifferentialGeometry.PDE.RicciFlow
