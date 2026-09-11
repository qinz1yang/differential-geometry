import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.RicciFamilyRegularity
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.ContractedBianchi
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology ENNReal BigOperators Matrix
namespace DifferentialGeometry.PDE.RicciFlow

private theorem matrixDet_contDiffOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : V → Matrix ι ι ℝ) (K : Set V)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun p => A p i j) K) :
    ContDiffOn ℝ ∞ (fun p => (A p).det) K := by
  have he : (fun p => (A p).det) =
      (fun p => ∑ σ : Equiv.Perm ι, (Equiv.Perm.sign σ : ℝ) * ∏ i, A p (σ i) i) := by
    funext p
    simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  rw [he]
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul
    (contDiffOn_prod fun i _ => hA (σ i) i)

private theorem matrixInverseEntry_contDiffOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : V → Matrix ι ι ℝ) (K : Set V)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun p => A p i j) K)
    (hdet : ∀ p ∈ K, (A p).det ≠ 0) (i j : ι) :
    ContDiffOn ℝ ∞ (fun p => (A p)⁻¹ i j) K := by
  have hadj : ContDiffOn ℝ ∞ (fun p => (A p).adjugate i j) K := by
    have he : (fun p => (A p).adjugate i j) =
        fun p => ((A p).updateRow j (Pi.single i (1 : ℝ))).det := by
      funext p
      exact Matrix.adjugate_apply _ _ _
    rw [he]
    apply matrixDet_contDiffOn
    intro a b
    by_cases hab : a = j
    · subst a
      simpa only [Matrix.updateRow_self] using
        (contDiffOn_const (c := (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ)) b) (s := K))
    · simpa only [Matrix.updateRow_ne hab] using hA a b
  have hs := ((matrixDet_contDiffOn A K hA).inv hdet).mul hadj
  apply hs.congr
  intro p _
  simp only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem cartesianInverseMetric_contDiffOn
    (g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) E) (K : Set ℝ)
    (hg : ContDiffOn ℝ ∞ (cartesianMetricFamily g) (K ×ˢ (univ : Set E)))
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => chartInvGramMatrix (g p.1) p.2 p.2 i j)
      (K ×ˢ (univ : Set E)) := by
  apply matrixInverseEntry_contDiffOn
  · intro a b
    have hpair := (hg.clm_apply (contDiffOn_const (c := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E a))).clm_apply
      (contDiffOn_const (c := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E b))
    apply hpair.congr
    intro p _
    simp only [DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply, DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber, TangentBundle.symmL_model_space]
    rfl
  · intro p _
    exact ne_of_gt (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_det_pos (g p.1) p.2
      (FiberBundle.mem_baseSet_trivializationAt' p.2))

theorem scalarFamily_contDiffOn
    (g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) E) (K : Set ℝ)
    (hg : ContDiffOn ℝ ∞ (cartesianMetricFamily g) (K ×ˢ (univ : Set E)))
    (hRic : ContDiffOn ℝ ∞ (cartesianRicciFamily g) (K ×ˢ (univ : Set E))) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => metricScalarAt (g p.1) p.2)
      (K ×ˢ (univ : Set E)) := by
  have hsum : ContDiffOn ℝ ∞ (fun p : ℝ × E =>
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (g p.1) p.2 p.2 i j *
          cartesianRicciFamily g p (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i) (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E j))
      (K ×ˢ (univ : Set E)) := by
    refine ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => ?_
    exact (cartesianInverseMetric_contDiffOn g K hg i j).mul
      ((hRic.clm_apply (contDiffOn_const (c := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i))).clm_apply
        (contDiffOn_const (c := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E j)))
  apply hsum.congr
  intro p _
  rw [metric_scalar_at_eq_chart_ricci_sum]
  simp only [DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis_apply,
    DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_symm_apply]
  rfl

theorem PartialStandardSolution.scalar_contDiffOn (S : PartialStandardSolution) :
    ContDiffOn ℝ ∞ (fun p : ℝ × EuclideanSpace ℝ (Fin 3) =>
      metricScalarAt (S.metric p.1) p.2) (S.domain ×ˢ univ) :=
  scalarFamily_contDiffOn S.metric S.domain S.smooth S.ricci_contDiffOn

private theorem timeSlice_differentiableWithinAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : ℝ × V → ℝ) (D : Set ℝ)
    (hf : ContDiffOn ℝ ∞ f (D ×ˢ univ))
    {K : Set ℝ} {t : ℝ} (ht : t ∈ K) (hK : K ⊆ D) (x : V) :
    DifferentiableWithinAt ℝ (fun s => f (s, x)) K t := by
  have hcurve : ContDiffOn ℝ ∞ (fun s : ℝ => (s, x)) D :=
    contDiffOn_id.prodMk contDiffOn_const
  have hcomp : ContDiffOn ℝ ∞ (fun s => f (s, x)) D :=
    hf.comp hcurve (fun _ hs => ⟨hs, mem_univ x⟩)
  exact ((hcomp.differentiableOn (by simp)) t (hK ht)).mono hK

theorem PartialStandardSolution.scalarTime (S : PartialStandardSolution)
    {K : Set ℝ} {t : ℝ} (ht : t ∈ K) (hK : K ⊆ S.domain)
    (x : EuclideanSpace ℝ (Fin 3)) :
    DifferentiableWithinAt ℝ (fun s => metricScalarAt (S.metric s) x) K t :=
  timeSlice_differentiableWithinAt (fun p => metricScalarAt (S.metric p.1) p.2)
    S.domain S.scalar_contDiffOn ht hK x
end DifferentialGeometry.PDE.RicciFlow
