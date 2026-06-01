import DifferentialGeometry.PDE.RicciFlow.HamiltonDeTurckPullbackFlat
import DifferentialGeometry.PDE.RicciFlow.Pullback.EvaluationFormChainRule
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckRemainderStrongExists
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.EigenCombination
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.TensorHsRealize
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ChartLocalPicard
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ChartOverlapUniqueness
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.BareFlowFromJointC1
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalLiftFlatIdentity
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold
import DifferentialGeometry.PDE.DeTurck.DeTurckVFChartCoord

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.ODE
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## Joint-smoothness keystone

The three smoothness targets below all reduce, via the chart-coordinate bridge
`deTurckVF_apply_eq_chartDeTurckVFComp_sum` and the bundle-section characterisation
`Bundle.contMDiffWithinAt_totalSpace`, to a single joint-`(s, y)` smoothness fact for
the *scalar* chart component `chartDeTurckVFComp (g_DT s) g_bg α p (extChartAt I α ·)`.

This section builds that keystone (`chartDeTurckVFComp_joint_contMDiffOn`) from the
node's own joint chart-Gram hypothesis, by assembling the joint Cramer inverse, the
joint chart-Christoffel symbol, and joint spatial partial derivatives. Each step is
the joint-`(s, y)` analogue of the on-disk single-metric facts in
`Geometry/HessianTrace.lean` and `PDE/DeTurck/DeTurckLinearization/ChartVectorField.lean`. -/

namespace DeTurckVFSmoothnessKeystone

open Set Function
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization

private abbrev Idx (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] := Fin (Module.finrank ℝ E)

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Joint smoothness of the determinant of a matrix family with jointly-`C^∞`
entries. -/
private lemma contDiffOn_jointDet {s : Set (ℝ × E)}
    {A : ℝ × E → Matrix n n ℝ}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun p : ℝ × E => A p i j) s) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => (A p).det) s := by
  classical
  have heq : (fun p : ℝ × E => (A p).det)
      = fun p : ℝ × E =>
        ∑ σ : Equiv.Perm n, (Equiv.Perm.sign σ : ℝ) * ∏ i, A p (σ i) i := by
    funext p; rw [Matrix.det_apply']
  rw [heq]
  refine ContDiffOn.sum (fun σ _ => ?_)
  refine (contDiffOn_const).mul ?_
  exact contDiffOn_prod (fun i _ => hA (σ i) i)

/-- Joint smoothness of an adjugate entry of a matrix family with jointly-`C^∞`
entries. -/
private lemma contDiffOn_jointAdjugate {s : Set (ℝ × E)}
    {A : ℝ × E → Matrix n n ℝ}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun p : ℝ × E => A p i j) s) (a b : n) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => (A p).adjugate a b) s := by
  classical
  have heq : (fun p : ℝ × E => (A p).adjugate a b)
      = fun p : ℝ × E => ((A p).updateRow b (Pi.single a 1)).det := by
    funext p; rw [Matrix.adjugate_apply]
  rw [heq]
  refine contDiffOn_jointDet (A := fun p => (A p).updateRow b (Pi.single a 1)) ?_
  intro i j
  by_cases hij : i = b
  · have hcongr : (fun p : ℝ × E =>
          ((A p).updateRow b (Pi.single a 1)) i j)
        = fun _ : ℝ × E => (Pi.single a 1 : n → ℝ) j := by
      funext p; rw [hij, Matrix.updateRow_self]
    rw [hcongr]; exact contDiffOn_const
  · have hcongr : (fun p : ℝ × E =>
          ((A p).updateRow b (Pi.single a 1)) i j)
        = fun p : ℝ × E => A p i j := by
      funext p; rw [Matrix.updateRow_ne hij]
    rw [hcongr]; exact hA i j

/-- Joint smoothness of an inverse entry of a matrix family with jointly-`C^∞`
entries and nowhere-vanishing determinant. -/
private lemma contDiffOn_jointMatrixInv_entry {s : Set (ℝ × E)}
    {A : ℝ × E → Matrix n n ℝ}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun p : ℝ × E => A p i j) s)
    (hdet : ∀ p ∈ s, (A p).det ≠ 0) (a b : n) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => (A p)⁻¹ a b) s := by
  classical
  have hexp : (fun p : ℝ × E => (A p)⁻¹ a b)
      = fun p : ℝ × E => (A p).det⁻¹ * (A p).adjugate a b := by
    funext p
    rw [Matrix.inv_def]
    simp [Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [hexp]
  have hdet_sm : ContDiffOn ℝ ∞ (fun p : ℝ × E => (A p).det) s :=
    contDiffOn_jointDet hA
  have hinv_sm : ContDiffOn ℝ ∞ (fun p : ℝ × E => (A p).det⁻¹) s :=
    hdet_sm.inv hdet
  exact hinv_sm.mul (contDiffOn_jointAdjugate hA a b)

private lemma contDiffOn_jointPartialDeriv {sI : Set ℝ} {U : Set E}
    (hsI : IsOpen sI) (hU : IsOpen U)
    {F : ℝ × E → ℝ} (hF : ContDiffOn ℝ ∞ F (sI ×ˢ U))
    (l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E => partialDeriv (E := E) l (fun y : E => F (p.1, y)) p.2)
      (sI ×ˢ U) := by
  classical
  have hprod_open : IsOpen (sI ×ˢ U) := hsI.prod hU
  have hF' : ContDiffOn ℝ ∞ (fun p : ℝ × E => fderiv ℝ F p) (sI ×ˢ U) :=
    hF.fderiv_of_isOpen hprod_open (by rw [ENat.coe_top_add_one])
  have hcomp : ContDiffOn ℝ ∞
      (fun p : ℝ × E =>
        (fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ ℝ E)) (sI ×ˢ U) := by
    have hL : ContDiff ℝ ∞
        (fun M : (ℝ × E) →L[ℝ] ℝ => M.comp (ContinuousLinearMap.inr ℝ ℝ E)) :=
      (ContinuousLinearMap.compL ℝ E (ℝ × E) ℝ).flip
        (ContinuousLinearMap.inr ℝ ℝ E) |>.contDiff
    exact hL.comp_contDiffOn hF'
  have hcomp_apply : ContDiffOn ℝ ∞
      (fun p : ℝ × E =>
        ((fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ ℝ E))
          ((chartModelBasis E) l)) (sI ×ˢ U) :=
    hcomp.clm_apply contDiffOn_const
  refine hcomp_apply.congr ?_
  intro p hp
  have hp_open : (sI ×ˢ U) ∈ 𝓝 p := hprod_open.mem_nhds hp
  have hdiff_joint : DifferentiableAt ℝ F p :=
    (hF.contDiffAt hp_open).differentiableAt (by simp)
  have hcurry : fderiv ℝ (fun y : E => F (p.1, y)) p.2
      = (fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
    have hg : HasFDerivAt (fun y : E => ((p.1 : ℝ), y))
        (ContinuousLinearMap.inr ℝ ℝ E) p.2 := by
      have h1 : HasFDerivAt (fun _ : E => (p.1 : ℝ)) (0 : E →L[ℝ] ℝ) p.2 :=
        hasFDerivAt_const _ _
      have h2 : HasFDerivAt (fun y : E => y) (ContinuousLinearMap.id ℝ E) p.2 :=
        hasFDerivAt_id _
      have h3 := h1.prodMk h2
      have hcl : (0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)
          = ContinuousLinearMap.inr ℝ ℝ E := by ext y <;> simp
      rw [hcl] at h3; exact h3
    have hp_eq : ((p.1 : ℝ), p.2) = p := by ext <;> rfl
    have hfd_joint' : HasFDerivAt F (fderiv ℝ F p)
        ((fun y : E => ((p.1 : ℝ), y)) p.2) := by
      change HasFDerivAt F (fderiv ℝ F p) ((p.1, p.2))
      rw [hp_eq]; exact hdiff_joint.hasFDerivAt
    have hcomp_raw : HasFDerivAt ((F) ∘ (fun y : E => ((p.1 : ℝ), y)))
        ((fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ ℝ E)) p.2 :=
      HasFDerivAt.comp p.2 hfd_joint' hg
    have huncurry_eq : (F) ∘ (fun y : E => ((p.1 : ℝ), y))
        = fun y : E => F (p.1, y) := by funext y; rfl
    rw [huncurry_eq] at hcomp_raw
    exact hcomp_raw.fderiv
  rw [partialDeriv, hcurry]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- On `interior (extChartAt I α).target`, the inverse-image manifold point lies in
the trivialization base set, so the chart Gram matrix is positive-definite there. -/
private lemma symm_mem_baseSet_of_mem_interior {α : M} {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    (extChartAt I α).symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
  have hy_tgt : y ∈ (extChartAt I α).target := interior_subset hy
  have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hy_tgt
  rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
  rw [trivializationAt_baseSet_eq_chartAt_source]
  exact hsource

/-- The matrix `Matrix.of (fun i j => chartGramOnE g α i j y)` equals
`chartGramMatrix g α ((extChartAt I α).symm y)`; in particular its inverse entries
are the `chartInvGramOnE` values. -/
private lemma gramOnE_matrix_eq (g : SmoothRiemannianMetric I M) (α : M) (y : E) :
    (Matrix.of fun i j => chartGramOnE (I := I) g α i j y)
      = chartGramMatrix (I := I) g α ((extChartAt I α).symm y) := by
  ext i j; rfl

/-- The inverse chart Gram entry equals the matrix inverse entry of the joint
`chartGramOnE` matrix. -/
private lemma chartInvGramOnE_eq_matrixInv
    (g : SmoothRiemannianMetric I M) (α : M) (a b : Fin (Module.finrank ℝ E)) (y : E) :
    chartInvGramOnE (I := I) g α a b y
      = (Matrix.of fun i j => chartGramOnE (I := I) g α i j y)⁻¹ a b := by
  rw [chartInvGramOnE_def, gramOnE_matrix_eq (I := I) g α y]
  rfl

/-- **Joint smoothness of the inverse chart Gram entry.** From the joint chart-Gram
smoothness on the chart-target interior, the inverse Gram entry of `g_DT s` is jointly
`C^∞`. -/
private lemma chartInvGramOnE_joint_contDiffOn
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) (T : ℝ)
    (h_gram_E : ∀ i j : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (fun p : ℝ × E => chartGramOnE (I := I) (g_DT p.1) α i j p.2)
        (Set.Ioo (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (a b : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E => chartInvGramOnE (I := I) (g_DT p.1) α a b p.2)
      (Set.Ioo (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
  classical
  let A : ℝ × E → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun p => Matrix.of fun i j => chartGramOnE (I := I) (g_DT p.1) α i j p.2
  have hcongr : (fun p : ℝ × E => chartInvGramOnE (I := I) (g_DT p.1) α a b p.2)
      = fun p : ℝ × E => (A p)⁻¹ a b := by
    funext p
    exact chartInvGramOnE_eq_matrixInv (I := I) (g_DT p.1) α a b p.2
  rw [hcongr]
  refine contDiffOn_jointMatrixInv_entry (A := A) (fun i j => ?_) ?_ a b
  · exact h_gram_E i j
  · intro p hp
    have hy_int : p.2 ∈ interior (extChartAt I α).target := hp.2
    have hbase := symm_mem_baseSet_of_mem_interior (I := I) (α := α) hy_int
    have hpos : 0 < (A p).det := by
      have : (A p) = chartGramMatrix (I := I) (g_DT p.1) α ((extChartAt I α).symm p.2) :=
        gramOnE_matrix_eq (I := I) (g_DT p.1) α p.2
      rw [this]
      exact chartGramMatrix_det_pos (I := I) (g_DT p.1) α hbase
    exact ne_of_gt hpos

/-- **Joint smoothness of the chart-Christoffel symbol of `g_DT s`.** Assembled from
the joint inverse Gram entry and joint spatial partial derivatives of the chart-Gram
entries, exactly as in `chartChristoffel_contDiffOn_interior`. -/
private lemma chartChristoffel_joint_contDiffOn
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) (T : ℝ)
    (h_gram_E : ∀ i j : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (fun p : ℝ × E => chartGramOnE (I := I) (g_DT p.1) α i j p.2)
        (Set.Ioo (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (i j k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E =>
        chartChristoffel (I := I) (g_DT p.1) α i j k p.2)
      (Set.Ioo (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
  classical
  have hrewrite : (fun p : ℝ × E =>
        chartChristoffel (I := I) (g_DT p.1) α i j k p.2)
      = fun p : ℝ × E =>
          (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) (g_DT p.1) α k l p.2 *
              (partialDeriv (E := E) i (chartGramOnE (I := I) (g_DT p.1) α l j) p.2 +
               partialDeriv (E := E) j (chartGramOnE (I := I) (g_DT p.1) α l i) p.2 -
               partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT p.1) α i j) p.2) := by
    funext p
    rw [chartChristoffel_def]
    refine congrArg (fun t => (1 / 2 : ℝ) * t) ?_
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rfl
  rw [hrewrite]
  have hsI : IsOpen (Set.Ioo (0 : ℝ) T) := isOpen_Ioo
  have hU : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hpd : ∀ a b c : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (fun p : ℝ × E =>
          partialDeriv (E := E) a (chartGramOnE (I := I) (g_DT p.1) α b c) p.2)
        (Set.Ioo (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
    intro a b c
    have := contDiffOn_jointPartialDeriv (E := E) hsI hU (h_gram_E b c) a
    exact this
  refine (contDiffOn_const).mul ?_
  refine ContDiffOn.sum (fun l _ => ?_)
  refine ContDiffOn.mul (chartInvGramOnE_joint_contDiffOn (I := I) g_DT α T h_gram_E k l) ?_
  exact ((hpd i l j).add (hpd j l i)).sub (hpd l i j)

/-- A `y`-only chart field that is `C^∞` on `interior (target)` is jointly `C^∞`
on the product with any time interval (it ignores the time coordinate). -/
private lemma contDiffOn_snd_of_contDiffOn_interior {α : M} (T : ℝ)
    {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F (interior (extChartAt I α).target)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => F p.2)
      (Set.Ioo (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
  have hsnd : ContDiffOn ℝ ∞ (fun p : ℝ × E => p.2)
      (Set.Ioo (0 : ℝ) T ×ˢ interior (extChartAt I α).target) :=
    contDiffOn_snd
  refine hF.comp hsnd ?_
  intro p hp; exact hp.2

/-- **Joint smoothness of the chart DeTurck-VF component (chart-target interior).**
This is the joint-`(s, y)` analogue of `chartDeTurckVFComp_contDiffOn_interior`:
assembled from the joint inverse Gram entry and joint chart-Christoffel of `g_DT s`
together with the `y`-only background Christoffel. -/
private lemma chartDeTurckVFComp_joint_contDiffOn_E
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (α : M) (T : ℝ)
    (h_gram_E : ∀ i j : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (fun p : ℝ × E => chartGramOnE (I := I) (g_DT p.1) α i j p.2)
        (Set.Ioo (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E => chartDeTurckVFComp (I := I) (g_DT p.1) g_bg α k p.2)
      (Set.Ioo (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
  classical
  have hrewrite : (fun p : ℝ × E => chartDeTurckVFComp (I := I) (g_DT p.1) g_bg α k p.2)
      = fun p : ℝ × E =>
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) (g_DT p.1) α a b p.2 *
            (chartChristoffel (I := I) (g_DT p.1) α a b k p.2 -
              chartChristoffel (I := I) g_bg α a b k p.2) := by
    funext p; rw [chartDeTurckVFComp_def]
  rw [hrewrite]
  refine ContDiffOn.sum (fun a _ => ?_)
  refine ContDiffOn.sum (fun b _ => ?_)
  refine ContDiffOn.mul (chartInvGramOnE_joint_contDiffOn (I := I) g_DT α T h_gram_E a b) ?_
  refine ContDiffOn.sub (chartChristoffel_joint_contDiffOn (I := I) g_DT α T h_gram_E a b k) ?_
  exact contDiffOn_snd_of_contDiffOn_interior (I := I) T
    (chartChristoffel_contDiffOn_interior (I := I) g_bg α a b k)

private lemma chartGramOnE_joint_contDiffOn_of_manifold
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) (T : ℝ)
    (h_gDT : ∀ (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M =>
          chartGramOnE (I := I) (g_DT q.1) α i j (extChartAt I α q.2))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E => chartGramOnE (I := I) (g_DT p.1) α i j p.2)
      (Set.Ioo (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
  classical
  set Ψ : ℝ × E → ℝ × M := fun p => (p.1, (extChartAt I α).symm p.2) with hΨ
  have hΨ_smooth : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) ((𝓘(ℝ, ℝ)).prod I) ∞ Ψ
      (Set.Ioo (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
    refine ContMDiffOn.prodMk ?_ ?_
    · exact contMDiffOn_fst
    · have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
          (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
      refine hsymm.comp contMDiffOn_snd ?_
      intro p hp; exact Set.mem_preimage.mpr (interior_subset hp.2)
  have hmaps : Set.MapsTo Ψ
      (Set.Ioo (0 : ℝ) T ×ˢ interior (extChartAt I α).target)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := by
    intro p hp
    exact ⟨hp.1, Set.mem_univ _⟩
  have hcomp : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      ((fun q : ℝ × M =>
          chartGramOnE (I := I) (g_DT q.1) α i j (extChartAt I α q.2)) ∘ Ψ)
      (Set.Ioo (0 : ℝ) T ×ˢ interior (extChartAt I α).target) :=
    (h_gDT i j).comp hΨ_smooth hmaps
  have hcongr : Set.EqOn
      (fun p : ℝ × E => chartGramOnE (I := I) (g_DT p.1) α i j p.2)
      ((fun q : ℝ × M =>
          chartGramOnE (I := I) (g_DT q.1) α i j (extChartAt I α q.2)) ∘ Ψ)
      (Set.Ioo (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
    intro p hp
    have hy_tgt : p.2 ∈ (extChartAt I α).target := interior_subset hp.2
    simp only [Function.comp_apply, hΨ]
    rw [(extChartAt I α).right_inv hy_tgt]
  have hcomp' : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × E => chartGramOnE (I := I) (g_DT p.1) α i j p.2)
      (Set.Ioo (0 : ℝ) T ×ˢ interior (extChartAt I α).target) :=
    hcomp.congr hcongr
  rw [← contMDiffOn_iff_contDiffOn, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact hcomp'

private lemma chartDeTurckVFComp_joint_contMDiffOn
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (α : M) (T : ℝ)
    (h_gDT : ∀ (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M =>
          chartGramOnE (I := I) (g_DT q.1) α i j (extChartAt I α q.2))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (p : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M =>
        chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α p (extChartAt I α q.2))
      (Set.Ioo (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α) := by
  classical
  have h_gram_E := chartGramOnE_joint_contDiffOn_of_manifold (I := I) g_DT α T h_gDT
  have hE := chartDeTurckVFComp_joint_contDiffOn_E (I := I) g_DT g_bg α T h_gram_E p
  have hE' : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × E => chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α p q.2)
      (Set.Ioo (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
    rw [← contMDiffOn_iff_contDiffOn, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod] at hE
    exact hE
  set Φ : ℝ × M → ℝ × E := fun q => (q.1, extChartAt I α q.2) with hΦ
  have hΦ_smooth : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) ∞ Φ
      (Set.Ioo (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α) := by
    refine ContMDiffOn.prodMk contMDiffOn_fst ?_
    have hext : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
      contMDiffOn_extChartAt (I := I) (x := α)
    refine hext.comp contMDiffOn_snd ?_
    intro q hq
    exact Set.mem_preimage.mpr (chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hq.2)
  have hmaps : Set.MapsTo Φ
      (Set.Ioo (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α)
      (Set.Ioo (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
    intro q hq
    exact ⟨hq.1, chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hq.2⟩
  have hcomp := hE'.comp hΦ_smooth hmaps
  exact hcomp

private lemma deTurckVF_trivSnd_eq_chartModelBasis_sum
    [I.Boundaryless]
    (g g_bg : SmoothRiemannianMetric I M) (α : M)
    {x : M} (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    (trivializationAt E (TangentSpace I) α
        ⟨x, (deTurckVF (I := I) g g_bg :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x⟩).2
      = ∑ p : Fin (Module.finrank ℝ E),
          chartDeTurckVFComp (I := I) g g_bg α p (extChartAt I α x) •
            (chartModelBasis E) p := by
  classical
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  set L : TangentSpace I x ≃L[ℝ] E :=
    (trivializationAt E (TangentSpace I) α).continuousLinearEquivAt ℝ x hbase with hL
  have hL_apply : ∀ v : TangentSpace I x,
      (trivializationAt E (TangentSpace I) α ⟨x, v⟩).2 = L v := fun _ => rfl
  rw [deTurckVF_apply_eq_chartDeTurckVFComp_sum (I := I) g g_bg α hx]
  rw [hL_apply, map_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [map_smul]
  congr 1
  rw [← hL_apply (chartBasisVecFiber (I := I) α p x)]
  exact trivializationAt_chartBasisVec_snd (I := I) α p hbase

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `C⁰` joint determinant. -/
private lemma continuousOn_jointDet {s : Set (ℝ × E)}
    {A : ℝ × E → Matrix n n ℝ}
    (hA : ∀ i j, ContinuousOn (fun p : ℝ × E => A p i j) s) :
    ContinuousOn (fun p : ℝ × E => (A p).det) s := by
  classical
  have heq : (fun p : ℝ × E => (A p).det)
      = fun p : ℝ × E =>
        ∑ σ : Equiv.Perm n, (Equiv.Perm.sign σ : ℝ) * ∏ i, A p (σ i) i := by
    funext p; rw [Matrix.det_apply']
  rw [heq]
  refine continuousOn_finset_sum _ (fun σ _ => ?_)
  refine (continuousOn_const).mul ?_
  exact continuousOn_finset_prod _ (fun i _ => hA (σ i) i)

/-- `C⁰` joint adjugate entry. -/
private lemma continuousOn_jointAdjugate {s : Set (ℝ × E)}
    {A : ℝ × E → Matrix n n ℝ}
    (hA : ∀ i j, ContinuousOn (fun p : ℝ × E => A p i j) s) (a b : n) :
    ContinuousOn (fun p : ℝ × E => (A p).adjugate a b) s := by
  classical
  have heq : (fun p : ℝ × E => (A p).adjugate a b)
      = fun p : ℝ × E => ((A p).updateRow b (Pi.single a 1)).det := by
    funext p; rw [Matrix.adjugate_apply]
  rw [heq]
  refine continuousOn_jointDet (A := fun p => (A p).updateRow b (Pi.single a 1)) ?_
  intro i j
  by_cases hij : i = b
  · have hcongr : (fun p : ℝ × E => ((A p).updateRow b (Pi.single a 1)) i j)
        = fun _ : ℝ × E => (Pi.single a 1 : n → ℝ) j := by
      funext p; rw [hij, Matrix.updateRow_self]
    rw [hcongr]; exact continuousOn_const
  · have hcongr : (fun p : ℝ × E => ((A p).updateRow b (Pi.single a 1)) i j)
        = fun p : ℝ × E => A p i j := by
      funext p; rw [Matrix.updateRow_ne hij]
    rw [hcongr]; exact hA i j

/-- `C⁰` joint inverse entry. -/
private lemma continuousOn_jointMatrixInv_entry {s : Set (ℝ × E)}
    {A : ℝ × E → Matrix n n ℝ}
    (hA : ∀ i j, ContinuousOn (fun p : ℝ × E => A p i j) s)
    (hdet : ∀ p ∈ s, (A p).det ≠ 0) (a b : n) :
    ContinuousOn (fun p : ℝ × E => (A p)⁻¹ a b) s := by
  classical
  have hexp : (fun p : ℝ × E => (A p)⁻¹ a b)
      = fun p : ℝ × E => (A p).det⁻¹ * (A p).adjugate a b := by
    funext p
    rw [Matrix.inv_def]
    simp [Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [hexp]
  exact ((continuousOn_jointDet hA).inv₀ hdet).mul (continuousOn_jointAdjugate hA a b)

/-- `C⁰` joint inverse chart Gram entry on `Icc × interior(target)`. -/
private lemma chartInvGramOnE_joint_continuousOn
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) (T : ℝ)
    (h_gram0 : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (fun p : ℝ × E => chartGramOnE (I := I) (g_DT p.1) α i j p.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (a b : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun p : ℝ × E => chartInvGramOnE (I := I) (g_DT p.1) α a b p.2)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
  classical
  let A : ℝ × E → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun p => Matrix.of fun i j => chartGramOnE (I := I) (g_DT p.1) α i j p.2
  have hcongr : (fun p : ℝ × E => chartInvGramOnE (I := I) (g_DT p.1) α a b p.2)
      = fun p : ℝ × E => (A p)⁻¹ a b := by
    funext p
    exact chartInvGramOnE_eq_matrixInv (I := I) (g_DT p.1) α a b p.2
  rw [hcongr]
  refine continuousOn_jointMatrixInv_entry (A := A) (fun i j => ?_) ?_ a b
  · exact h_gram0 i j
  · intro p hp
    have hbase := symm_mem_baseSet_of_mem_interior (I := I) (α := α) hp.2
    have hpos : 0 < (A p).det := by
      have : (A p) = chartGramMatrix (I := I) (g_DT p.1) α ((extChartAt I α).symm p.2) :=
        gramOnE_matrix_eq (I := I) (g_DT p.1) α p.2
      rw [this]
      exact chartGramMatrix_det_pos (I := I) (g_DT p.1) α hbase
    exact ne_of_gt hpos

/-- `C⁰` joint chart Christoffel symbol on `Icc × interior(target)`. -/
private lemma chartChristoffel_joint_continuousOn
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) (T : ℝ)
    (h_gram0 : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (fun p : ℝ × E => chartGramOnE (I := I) (g_DT p.1) α i j p.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (h_partial : ∀ l i j : Fin (Module.finrank ℝ E),
      ContinuousOn
        (fun p : ℝ × E =>
          partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT p.1) α i j) p.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (i j k : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun p : ℝ × E => chartChristoffel (I := I) (g_DT p.1) α i j k p.2)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
  classical
  have hrewrite : (fun p : ℝ × E =>
        chartChristoffel (I := I) (g_DT p.1) α i j k p.2)
      = fun p : ℝ × E =>
          (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) (g_DT p.1) α k l p.2 *
              (partialDeriv (E := E) i (chartGramOnE (I := I) (g_DT p.1) α l j) p.2 +
               partialDeriv (E := E) j (chartGramOnE (I := I) (g_DT p.1) α l i) p.2 -
               partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT p.1) α i j) p.2) := by
    funext p
    rw [chartChristoffel_def]
    refine congrArg (fun t => (1 / 2 : ℝ) * t) ?_
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rfl
  rw [hrewrite]
  refine (continuousOn_const).mul ?_
  refine continuousOn_finset_sum _ (fun l _ => ?_)
  refine ContinuousOn.mul (chartInvGramOnE_joint_continuousOn (I := I) g_DT α T h_gram0 k l) ?_
  exact ((h_partial i l j).add (h_partial j l i)).sub (h_partial l i j)

/-- `C⁰` joint chart DeTurck-VF component value on `Icc × interior(target)`. -/
private lemma chartDeTurckVFComp_joint_continuousOn_E
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g₀ : SmoothRiemannianMetric I M)
    (α : M) (T : ℝ)
    (h_gram0 : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (fun p : ℝ × E => chartGramOnE (I := I) (g_DT p.1) α i j p.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (h_partial : ∀ l i j : Fin (Module.finrank ℝ E),
      ContinuousOn
        (fun p : ℝ × E =>
          partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT p.1) α i j) p.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (k : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun p : ℝ × E => chartDeTurckVFComp (I := I) (g_DT p.1) g₀ α k p.2)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
  classical
  have hrewrite : (fun p : ℝ × E => chartDeTurckVFComp (I := I) (g_DT p.1) g₀ α k p.2)
      = fun p : ℝ × E =>
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) (g_DT p.1) α a b p.2 *
            (chartChristoffel (I := I) (g_DT p.1) α a b k p.2 -
              chartChristoffel (I := I) g₀ α a b k p.2) := by
    funext p; rw [chartDeTurckVFComp_def]
  rw [hrewrite]
  refine continuousOn_finset_sum _ (fun a _ => ?_)
  refine continuousOn_finset_sum _ (fun b _ => ?_)
  refine ContinuousOn.mul (chartInvGramOnE_joint_continuousOn (I := I) g_DT α T h_gram0 a b) ?_
  refine ContinuousOn.sub
    (chartChristoffel_joint_continuousOn (I := I) g_DT α T h_gram0 h_partial a b k) ?_
  have hbg : ContinuousOn (chartChristoffel (I := I) g₀ α a b k)
      (interior (extChartAt I α).target) :=
    (chartChristoffel_contDiffOn_interior (I := I) g₀ α a b k).continuousOn
  have hsnd : ContinuousOn (fun p : ℝ × E => p.2)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := continuousOn_snd
  exact hbg.comp hsnd (fun p hp => hp.2)

/-- **Manifold-level `C⁰` joint scalar producer.** Composing the `E`-level joint
continuity of the chart DeTurck-VF component with the chart map
`q ↦ (q.1, extChartAt I α q.2)` (continuous on the good set, with image in the
chart-target interior) yields the joint `(t, x)` continuity of the scalar
chart component on `Icc 0 T ×ˢ chartLeviCivitaGoodSet α`. This is the `C⁰`
analogue of `chartDeTurckVFComp_joint_contMDiffOn`. -/
private lemma chartDeTurckVFComp_joint_continuousOn_M
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g₀ : SmoothRiemannianMetric I M)
    (α : M) (T : ℝ)
    (h_gram0 : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (fun p : ℝ × E => chartGramOnE (I := I) (g_DT p.1) α i j p.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (h_partial : ∀ l i j : Fin (Module.finrank ℝ E),
      ContinuousOn
        (fun p : ℝ × E =>
          partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT p.1) α i j) p.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (k : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun q : ℝ × M =>
        chartDeTurckVFComp (I := I) (g_DT q.1) g₀ α k (extChartAt I α q.2))
      (Set.Icc (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α) := by
  classical
  have hE := chartDeTurckVFComp_joint_continuousOn_E (I := I) g_DT g₀ α T h_gram0 h_partial k
  set Φ : ℝ × M → ℝ × E := fun q => (q.1, extChartAt I α q.2) with hΦdef
  have hΦ : ContinuousOn Φ
      (Set.Icc (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α) := by
    rw [hΦdef]
    refine ContinuousOn.prodMk continuousOn_fst ?_
    have hext : ContinuousOn (extChartAt I α) (extChartAt I α).source :=
      continuousOn_extChartAt (I := I) α
    refine hext.comp continuousOn_snd ?_
    intro q hq
    have : q.2 ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]
      exact chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hq.2
    exact this
  have hmaps : Set.MapsTo Φ
      (Set.Icc (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
    intro q hq
    exact ⟨hq.1, chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hq.2⟩
  have hcomp := hE.comp hΦ hmaps
  exact hcomp

/-- Leibniz rule for the model-direction partial derivative of a product. -/
private lemma partialDeriv_mul_eq {f h : E → ℝ} {y : E}
    (l : Fin (Module.finrank ℝ E))
    (hf : DifferentiableAt ℝ f y) (hh : DifferentiableAt ℝ h y) :
    partialDeriv (E := E) l (fun x => f x * h x) y
      = partialDeriv (E := E) l f y * h y + f y * partialDeriv (E := E) l h y := by
  unfold partialDeriv
  rw [show (fun x => f x * h x) = f * h from rfl, fderiv_mul hf hh]
  simp [mul_comm, add_comm]

/-- `C⁰` joint continuity of the first spatial partial of the inverse chart Gram
entry, via the matrix-inverse derivative identity. -/
private lemma partialDeriv_chartInvGramOnE_joint_continuousOn
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) (T : ℝ)
    (h_gram0 : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (fun p : ℝ × E => chartGramOnE (I := I) (g_DT p.1) α i j p.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (h_partial : ∀ l i j : Fin (Module.finrank ℝ E),
      ContinuousOn
        (fun p : ℝ × E =>
          partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT p.1) α i j) p.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (l j' p' : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun q : ℝ × E =>
        partialDeriv (E := E) l (chartInvGramOnE (I := I) (g_DT q.1) α j' p') q.2)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
  classical
  have hrw : Set.EqOn
      (fun q : ℝ × E =>
        partialDeriv (E := E) l (chartInvGramOnE (I := I) (g_DT q.1) α j' p') q.2)
      (fun q : ℝ × E =>
        -∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) (g_DT q.1) α j' a q.2 *
              chartInvGramOnE (I := I) (g_DT q.1) α b p' q.2 *
              partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT q.1) α a b) q.2)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
    intro q hq
    exact partialDeriv_chartInvGramOnE_eq (I := I) (g_DT q.1) α q.2 l j' p' hq.2
  refine ContinuousOn.congr ?_ hrw
  refine ContinuousOn.neg ?_
  refine continuousOn_finset_sum _ (fun a _ => ?_)
  refine continuousOn_finset_sum _ (fun b _ => ?_)
  refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
  · exact chartInvGramOnE_joint_continuousOn (I := I) g_DT α T h_gram0 j' a
  · exact chartInvGramOnE_joint_continuousOn (I := I) g_DT α T h_gram0 b p'
  · exact h_partial l a b

/-- `partialDeriv` over a constant multiple. -/
private lemma partialDeriv_const_mul_eq {f : E → ℝ} {y : E} (c : ℝ)
    (l : Fin (Module.finrank ℝ E)) (hf : DifferentiableAt ℝ f y) :
    partialDeriv (E := E) l (fun x => c * f x) y = c * partialDeriv (E := E) l f y := by
  unfold partialDeriv; rw [fderiv_const_mul hf]; simp

/-- `partialDeriv` over a finite sum. -/
private lemma partialDeriv_finset_sum_eq {ι : Type*} (t : Finset ι)
    {F : ι → E → ℝ} {y : E} (l : Fin (Module.finrank ℝ E))
    (hF : ∀ i ∈ t, DifferentiableAt ℝ (F i) y) :
    partialDeriv (E := E) l (fun x => ∑ i ∈ t, F i x) y
      = ∑ i ∈ t, partialDeriv (E := E) l (F i) y := by
  unfold partialDeriv
  rw [fderiv_fun_sum hF]; simp

/-- `partialDeriv` over a sum/difference (for the Christoffel bracket). -/
private lemma partialDeriv_add_eq {f h : E → ℝ} {y : E}
    (l : Fin (Module.finrank ℝ E))
    (hf : DifferentiableAt ℝ f y) (hh : DifferentiableAt ℝ h y) :
    partialDeriv (E := E) l (fun x => f x + h x) y
      = partialDeriv (E := E) l f y + partialDeriv (E := E) l h y := by
  unfold partialDeriv; rw [fderiv_fun_add hf hh]; simp

private lemma partialDeriv_sub_eq {f h : E → ℝ} {y : E}
    (l : Fin (Module.finrank ℝ E))
    (hf : DifferentiableAt ℝ f y) (hh : DifferentiableAt ℝ h y) :
    partialDeriv (E := E) l (fun x => f x - h x) y
      = partialDeriv (E := E) l f y - partialDeriv (E := E) l h y := by
  unfold partialDeriv; rw [fderiv_fun_sub hf hh]; simp

/-- `C⁰` joint continuity of the first spatial partial of the chart Christoffel
symbol, via a Leibniz expansion through the inverse Gram and the second partials of
the chart Gram entries. -/
private lemma partialDeriv_chartChristoffel_joint_continuousOn
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) (T : ℝ)
    (h_gram0 : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (fun p : ℝ × E => chartGramOnE (I := I) (g_DT p.1) α i j p.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (h_partial : ∀ l i j : Fin (Module.finrank ℝ E),
      ContinuousOn
        (fun p : ℝ × E =>
          partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT p.1) α i j) p.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (h_partial2 : ∀ m l i j : Fin (Module.finrank ℝ E),
      ContinuousOn
        (fun p : ℝ × E =>
          partialDeriv (E := E) m
            (partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT p.1) α i j)) p.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (m i j k : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun q : ℝ × E =>
        partialDeriv (E := E) m (chartChristoffel (I := I) (g_DT q.1) α i j k) q.2)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
  classical
  have hrw : Set.EqOn
      (fun q : ℝ × E =>
        partialDeriv (E := E) m (chartChristoffel (I := I) (g_DT q.1) α i j k) q.2)
      (fun q : ℝ × E =>
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) m (chartInvGramOnE (I := I) (g_DT q.1) α k l) q.2 *
            (partialDeriv (E := E) i (chartGramOnE (I := I) (g_DT q.1) α l j) q.2 +
             partialDeriv (E := E) j (chartGramOnE (I := I) (g_DT q.1) α l i) q.2 -
             partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT q.1) α i j) q.2)
          + chartInvGramOnE (I := I) (g_DT q.1) α k l q.2 *
            (partialDeriv (E := E) m
                (partialDeriv (E := E) i (chartGramOnE (I := I) (g_DT q.1) α l j)) q.2 +
             partialDeriv (E := E) m
                (partialDeriv (E := E) j (chartGramOnE (I := I) (g_DT q.1) α l i)) q.2 -
             partialDeriv (E := E) m
                (partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT q.1) α i j)) q.2)))
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
    intro q hq
    have hy : q.2 ∈ interior (extChartAt I α).target := hq.2
    simp only []
    set g := g_DT q.1
    have hInv : ∀ a b, DifferentiableAt ℝ (chartInvGramOnE (I := I) g α a b) q.2 := by
      intro a b
      exact (((chartInvGramOnE_contDiffOn (I := I) g α a b).mono interior_subset).contDiffAt
        (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)
    have hParG : ∀ a b c, DifferentiableAt ℝ
        (partialDeriv (E := E) a (chartGramOnE (I := I) g α b c)) q.2 := by
      intro a b c
      have hG : ContDiffOn ℝ ∞ (partialDeriv (E := E) a (chartGramOnE (I := I) g α b c))
          (interior (extChartAt I α).target) := by
        unfold partialDeriv
        have hGr : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α b c)
            (interior (extChartAt I α).target) :=
          (chartGramOnE_contDiffOn (I := I) g α b c).mono interior_subset
        exact (hGr.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])).clm_apply
          contDiffOn_const
      exact (hG.contDiffAt (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)
    have hΓfun : chartChristoffel (I := I) g α i j k =
        fun z : E => (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k l z *
            (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) z +
             partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) z -
             partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) z) := by
      funext z; rw [chartChristoffel_def]
      refine congrArg (fun t => (1 / 2 : ℝ) * t) ?_
      refine Finset.sum_congr rfl (fun l _ => ?_); rfl
    rw [hΓfun]
    have hbrDiff : ∀ l, DifferentiableAt ℝ
        (fun z : E => partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) z +
          partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) z -
          partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) z) q.2 := fun l =>
      ((hParG i l j).fun_add (hParG j l i)).fun_sub (hParG l i j)
    have hsumDiff : ∀ l, DifferentiableAt ℝ
        (fun z : E => chartInvGramOnE (I := I) g α k l z *
          (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) z +
            partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) z -
            partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) z)) q.2 := fun l =>
      (hInv k l).mul (hbrDiff l)
    rw [partialDeriv_const_mul_eq
      (f := fun z : E => ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k l z *
          (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) z +
            partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) z -
            partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) z))
      (1 / 2 : ℝ) m (DifferentiableAt.fun_sum (fun l _ => hsumDiff l))]
    refine congrArg (fun t => (1 / 2 : ℝ) * t) ?_
    rw [partialDeriv_finset_sum_eq
      (F := fun (l : Fin (Module.finrank ℝ E)) (z : E) =>
        chartInvGramOnE (I := I) g α k l z *
        (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) z +
          partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) z -
          partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) z))
      Finset.univ m (fun l _ => hsumDiff l)]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [partialDeriv_mul_eq m (hInv k l) (hbrDiff l)]
    rw [partialDeriv_sub_eq m ((hParG i l j).fun_add (hParG j l i)) (hParG l i j)]
    rw [partialDeriv_add_eq m (hParG i l j) (hParG j l i)]
  refine ContinuousOn.congr ?_ hrw
  refine (continuousOn_const).mul ?_
  refine continuousOn_finset_sum _ (fun l _ => ?_)
  refine ContinuousOn.add ?_ ?_
  · refine ContinuousOn.mul
      (partialDeriv_chartInvGramOnE_joint_continuousOn (I := I) g_DT α T h_gram0 h_partial m k l)
      ?_
    exact ((h_partial i l j).add (h_partial j l i)).sub (h_partial l i j)
  · refine ContinuousOn.mul (chartInvGramOnE_joint_continuousOn (I := I) g_DT α T h_gram0 k l) ?_
    exact ((h_partial2 m i l j).add (h_partial2 m j l i)).sub (h_partial2 m l i j)

/-- `C⁰` joint continuity of the first spatial partial of the chart DeTurck-VF
component, via the Leibniz expansion `partialDeriv_chartDeTurckVFComp_eq`. -/
private lemma partialDeriv_chartDeTurckVFComp_joint_continuousOn
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g₀ : SmoothRiemannianMetric I M)
    (α : M) (T : ℝ)
    (h_gram0 : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (fun p : ℝ × E => chartGramOnE (I := I) (g_DT p.1) α i j p.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (h_partial : ∀ l i j : Fin (Module.finrank ℝ E),
      ContinuousOn
        (fun p : ℝ × E =>
          partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT p.1) α i j) p.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (h_partial2 : ∀ m l i j : Fin (Module.finrank ℝ E),
      ContinuousOn
        (fun p : ℝ × E =>
          partialDeriv (E := E) m
            (partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT p.1) α i j)) p.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (m k : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun q : ℝ × E =>
        partialDeriv (E := E) m (chartDeTurckVFComp (I := I) (g_DT q.1) g₀ α k) q.2)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
  classical
  have hrw : Set.EqOn
      (fun q : ℝ × E =>
        partialDeriv (E := E) m (chartDeTurckVFComp (I := I) (g_DT q.1) g₀ α k) q.2)
      (fun q : ℝ × E =>
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) m (chartInvGramOnE (I := I) (g_DT q.1) α a b) q.2 *
              (chartChristoffel (I := I) (g_DT q.1) α a b k q.2 -
                chartChristoffel (I := I) g₀ α a b k q.2)
            + chartInvGramOnE (I := I) (g_DT q.1) α a b q.2 *
              (partialDeriv (E := E) m (chartChristoffel (I := I) (g_DT q.1) α a b k) q.2 -
                partialDeriv (E := E) m (chartChristoffel (I := I) g₀ α a b k) q.2)))
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
    intro q hq
    have hy : q.2 ∈ interior (extChartAt I α).target := hq.2
    simp only []
    set g := g_DT q.1
    have hInv : ∀ a b, DifferentiableAt ℝ (chartInvGramOnE (I := I) g α a b) q.2 := fun a b =>
      (((chartInvGramOnE_contDiffOn (I := I) g α a b).mono interior_subset).contDiffAt
        (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)
    have hΓ : ∀ a b, DifferentiableAt ℝ (chartChristoffel (I := I) g α a b k) q.2 := fun a b =>
      ((chartChristoffel_contDiffOn_interior (I := I) g α a b k).contDiffAt
        (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)
    have hΓbg : ∀ a b, DifferentiableAt ℝ (chartChristoffel (I := I) g₀ α a b k) q.2 := fun a b =>
      ((chartChristoffel_contDiffOn_interior (I := I) g₀ α a b k).contDiffAt
        (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)
    have hcomp : chartDeTurckVFComp (I := I) g g₀ α k =
        fun z : E => ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b z *
              (chartChristoffel (I := I) g α a b k z -
                chartChristoffel (I := I) g₀ α a b k z) := by
      funext z; rw [chartDeTurckVFComp_def]
    rw [hcomp]
    have hbDiff : ∀ a b, DifferentiableAt ℝ
        (fun z : E => chartInvGramOnE (I := I) g α a b z *
          (chartChristoffel (I := I) g α a b k z -
            chartChristoffel (I := I) g₀ α a b k z)) q.2 := fun a b =>
      (hInv a b).mul ((hΓ a b).fun_sub (hΓbg a b))
    rw [partialDeriv_finset_sum_eq
      (F := fun (a : Fin (Module.finrank ℝ E)) (z : E) =>
        ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α a b z *
          (chartChristoffel (I := I) g α a b k z -
            chartChristoffel (I := I) g₀ α a b k z))
      Finset.univ m (fun a _ => DifferentiableAt.fun_sum (fun b _ => hbDiff a b))]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [partialDeriv_finset_sum_eq
      (F := fun (b : Fin (Module.finrank ℝ E)) (z : E) =>
        chartInvGramOnE (I := I) g α a b z *
        (chartChristoffel (I := I) g α a b k z -
          chartChristoffel (I := I) g₀ α a b k z))
      Finset.univ m (fun b _ => hbDiff a b)]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [partialDeriv_mul_eq m (hInv a b) ((hΓ a b).fun_sub (hΓbg a b))]
    rw [partialDeriv_sub_eq m (hΓ a b) (hΓbg a b)]
  refine ContinuousOn.congr ?_ hrw
  refine continuousOn_finset_sum _ (fun a _ => ?_)
  refine continuousOn_finset_sum _ (fun b _ => ?_)
  refine ContinuousOn.add ?_ ?_
  · refine ContinuousOn.mul
      (partialDeriv_chartInvGramOnE_joint_continuousOn (I := I) g_DT α T h_gram0 h_partial m a b)
      ?_
    refine ContinuousOn.sub
      (chartChristoffel_joint_continuousOn (I := I) g_DT α T h_gram0 h_partial a b k) ?_
    have hbg : ContinuousOn (chartChristoffel (I := I) g₀ α a b k)
        (interior (extChartAt I α).target) :=
      (chartChristoffel_contDiffOn_interior (I := I) g₀ α a b k).continuousOn
    exact hbg.comp continuousOn_snd (fun p hp => hp.2)
  · refine ContinuousOn.mul (chartInvGramOnE_joint_continuousOn (I := I) g_DT α T h_gram0 a b) ?_
    refine ContinuousOn.sub
      (partialDeriv_chartChristoffel_joint_continuousOn (I := I) g_DT α T h_gram0 h_partial
        h_partial2 m a b k) ?_
    have hbg : ContinuousOn (partialDeriv (E := E) m (chartChristoffel (I := I) g₀ α a b k))
        (interior (extChartAt I α).target) := by
      unfold partialDeriv
      have hΓ : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g₀ α a b k)
          (interior (extChartAt I α).target) :=
        chartChristoffel_contDiffOn_interior (I := I) g₀ α a b k
      exact ((hΓ.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])).clm_apply
        contDiffOn_const).continuousOn
    exact hbg.comp continuousOn_snd (fun p hp => hp.2)

/-- The Fréchet derivative of a scalar field on `E` equals the
`chartModelBasis`-coordinate sum of its model-direction partials. (This is a pure
continuous-linear-map decomposition, valid for any `fderiv`.) -/
private lemma fderiv_eq_partialDeriv_sum (F : E → ℝ) (y : E) :
    fderiv ℝ F y = ∑ m : Fin (Module.finrank ℝ E),
      (partialDeriv (E := E) m F y) •
        ((chartModelBasis E).coord m).toContinuousLinearMap := by
  classical
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    LinearMap.coe_toContinuousLinearMap', smul_eq_mul]
  conv_lhs => rw [← (chartModelBasis E).sum_repr v]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [map_smul, Module.Basis.coord_apply, smul_eq_mul, partialDeriv]
  ring

/-- **Second conjunct producer.** Joint continuity of the spatial Fréchet derivative
of the chart DeTurck-VF component on `Icc × interior(target)`. -/
private lemma fderiv_chartDeTurckVFComp_joint_continuousOn
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g₀ : SmoothRiemannianMetric I M)
    (α : M) (T : ℝ)
    (h_gram0 : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (fun p : ℝ × E => chartGramOnE (I := I) (g_DT p.1) α i j p.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (h_partial : ∀ l i j : Fin (Module.finrank ℝ E),
      ContinuousOn
        (fun p : ℝ × E =>
          partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT p.1) α i j) p.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (h_partial2 : ∀ m l i j : Fin (Module.finrank ℝ E),
      ContinuousOn
        (fun p : ℝ × E =>
          partialDeriv (E := E) m
            (partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT p.1) α i j)) p.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (k : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun q : ℝ × E =>
        fderiv ℝ (fun y : E => chartDeTurckVFComp (I := I) (g_DT q.1) g₀ α k y) q.2)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
  classical
  have hrw : Set.EqOn
      (fun q : ℝ × E =>
        fderiv ℝ (fun y : E => chartDeTurckVFComp (I := I) (g_DT q.1) g₀ α k y) q.2)
      (fun q : ℝ × E =>
        ∑ m : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) m (chartDeTurckVFComp (I := I) (g_DT q.1) g₀ α k) q.2) •
            ((chartModelBasis E).coord m).toContinuousLinearMap)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
    intro q hq
    exact fderiv_eq_partialDeriv_sum
      (fun y : E => chartDeTurckVFComp (I := I) (g_DT q.1) g₀ α k y) q.2
  refine ContinuousOn.congr ?_ hrw
  refine continuousOn_finset_sum _ (fun m _ => ?_)
  refine ContinuousOn.smul ?_ continuousOn_const
  exact partialDeriv_chartDeTurckVFComp_joint_continuousOn
    (I := I) g_DT g₀ α T h_gram0 h_partial h_partial2 m k

end DeTurckVFSmoothnessKeystone

theorem deturck_vf_joint_smoothness
    (g_bg : SmoothRiemannianMetric I M)
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ)
    (h_gDT : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M =>
          Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) x₀ i j
            (extChartAt I x₀ q.2))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
        : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := by
  classical
  intro q₀ hq₀
  set α : M := q₀.2 with hα
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_snd, ?_⟩
  simp only [← hα]
  have hgood_open : IsOpen (chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_isOpen (I := I) α
  have hα_mem : α ∈ chartLeviCivitaGoodSet (I := I) α :=
    self_mem_chartLeviCivitaGoodSet (I := I) α
  have hcoeff := fun p =>
    DeTurckVFSmoothnessKeystone.chartDeTurckVFComp_joint_contMDiffOn
      (I := I) g_DT g_bg α T (h_gDT α) p
  have hsum_within : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M =>
        ∑ p : Fin (Module.finrank ℝ E),
          chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α p (extChartAt I α q.2) •
            ((chartModelBasis E) p : E))
      (Set.Ioo (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α) q₀ := by
    refine contMDiffWithinAt_finset_sum (fun p _ => ?_)
    refine ContMDiffWithinAt.smul ?_ contMDiffWithinAt_const
    have hq₀_mem : q₀ ∈ Set.Ioo (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α :=
      ⟨hq₀.1, hα ▸ hα_mem⟩
    exact (hcoeff p) q₀ hq₀_mem
  have hnhds : Set.Ioo (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α
      ∈ nhdsWithin q₀ (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := by
    have hsub : Set.Ioo (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α
        ⊆ Set.Ioo (0 : ℝ) T ×ˢ Set.univ :=
      Set.prod_mono_right (Set.subset_univ _)
    have hopen : IsOpen (Set.Ioo (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α) :=
      isOpen_Ioo.prod hgood_open
    have hmemq₀ : q₀ ∈ Set.Ioo (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α :=
      ⟨hq₀.1, hα ▸ hα_mem⟩
    exact Filter.mem_of_superset
      (nhdsWithin_le_nhds (hopen.mem_nhds hmemq₀)) (by intro x hx; exact hx)
  have hsum_within' : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M =>
        ∑ p : Fin (Module.finrank ℝ E),
          chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α p (extChartAt I α q.2) •
            ((chartModelBasis E) p : E))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) q₀ :=
    hsum_within.mono_of_mem_nhdsWithin hnhds
  have heqOn : Set.EqOn
      (fun q : ℝ × M =>
        (trivializationAt E (TangentSpace I) α
          ⟨q.2, (deTurckVF (I := I) (g_DT q.1) g_bg) q.2⟩).2)
      (fun q : ℝ × M =>
        ∑ p : Fin (Module.finrank ℝ E),
          chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α p (extChartAt I α q.2) •
            ((chartModelBasis E) p : E))
      (Set.Ioo (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α) := by
    intro q hq
    exact DeTurckVFSmoothnessKeystone.deTurckVF_trivSnd_eq_chartModelBasis_sum
      (I := I) (g_DT q.1) g_bg α hq.2
  have hev : (fun q : ℝ × M =>
        (trivializationAt E (TangentSpace I) α
          ⟨q.2, (deTurckVF (I := I) (g_DT q.1) g_bg) q.2⟩).2)
      =ᶠ[nhdsWithin q₀ (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)]
      (fun q : ℝ × M =>
        ∑ p : Fin (Module.finrank ℝ E),
          chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α p (extChartAt I α q.2) •
            ((chartModelBasis E) p : E)) := by
    filter_upwards [hnhds] with q hq using heqOn hq
  have hxeq : (trivializationAt E (TangentSpace I) α
        ⟨q₀.2, (deTurckVF (I := I) (g_DT q₀.1) g_bg) q₀.2⟩).2
      = ∑ p : Fin (Module.finrank ℝ E),
          chartDeTurckVFComp (I := I) (g_DT q₀.1) g_bg α p (extChartAt I α q₀.2) •
            ((chartModelBasis E) p : E) :=
    heqOn (by exact ⟨hq₀.1, hα ▸ hα_mem⟩)
  exact hsum_within'.congr_of_eventuallyEq hev hxeq

theorem deturck_vf_continuous_up_to_zero
    (g₀ : SmoothRiemannianMetric I M)
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ)
    (h_gram0 : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × E =>
          Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j q.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (h_partial : ∀ (α : M) (l i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × E =>
          Integral.DivergenceTheorem.partialDeriv (E := E) l
            (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j) q.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (h_partial2 : ∀ (α : M) (m l i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × E =>
          Integral.DivergenceTheorem.partialDeriv (E := E) m
            (Integral.DivergenceTheorem.partialDeriv (E := E) l
              (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j)) q.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (h_frame : ∀ (α : M) (p : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun x : M =>
          (Integral.Measure.chartBasisVecFiber (I := I) α p x : E))
        (chartLeviCivitaGoodSet (I := I) α)) :
    (ContinuousOn (fun q : ℝ × M => (deTurckVF (I := I) (g_DT q.1) g₀ q.2 : TangentSpace I q.2))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    ∧ (∀ (α : M) (k : Fin (Module.finrank ℝ E)),
        ContinuousOn (fun q : ℝ × E =>
          fderiv ℝ (fun y : E =>
            DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT q.1) g₀ α k y) q.2)
          (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target)) := by
  refine ⟨?_, ?_⟩
  · intro q₀ hq₀
    set α : M := q₀.2 with hα
    have hgood_open : IsOpen (chartLeviCivitaGoodSet (I := I) α) :=
      chartLeviCivitaGoodSet_isOpen (I := I) α
    have hα_mem : α ∈ chartLeviCivitaGoodSet (I := I) α :=
      self_mem_chartLeviCivitaGoodSet (I := I) α
    have hscalar : ∀ p : Fin (Module.finrank ℝ E),
        ContinuousOn
          (fun q : ℝ × M =>
            chartDeTurckVFComp (I := I) (g_DT q.1) g₀ α p (extChartAt I α q.2))
          (Set.Icc (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α) := fun p =>
      DeTurckVFSmoothnessKeystone.chartDeTurckVFComp_joint_continuousOn_M
        (I := I) g_DT g₀ α T (h_gram0 α) (h_partial α) p
    have hframe_joint : ∀ p : Fin (Module.finrank ℝ E),
        ContinuousOn
          (fun q : ℝ × M =>
            (Integral.Measure.chartBasisVecFiber (I := I) α p q.2 : E))
          (Set.Icc (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α) := by
      intro p
      exact (h_frame α p).comp continuousOn_snd (fun q hq => hq.2)
    have hsum : ContinuousOn
        (fun q : ℝ × M =>
          ∑ p : Fin (Module.finrank ℝ E),
            chartDeTurckVFComp (I := I) (g_DT q.1) g₀ α p (extChartAt I α q.2) •
              (Integral.Measure.chartBasisVecFiber (I := I) α p q.2 : E))
        (Set.Icc (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α) := by
      refine continuousOn_finset_sum _ (fun p _ => ?_)
      exact (hscalar p).smul (hframe_joint p)
    have heqOn : Set.EqOn
        (fun q : ℝ × M => (deTurckVF (I := I) (g_DT q.1) g₀ q.2 : TangentSpace I q.2))
        (fun q : ℝ × M =>
          ∑ p : Fin (Module.finrank ℝ E),
            chartDeTurckVFComp (I := I) (g_DT q.1) g₀ α p (extChartAt I α q.2) •
              (Integral.Measure.chartBasisVecFiber (I := I) α p q.2 : E))
        (Set.Icc (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α) := by
      intro q hq
      exact deTurckVF_apply_eq_chartDeTurckVFComp_sum (I := I) (g_DT q.1) g₀ α hq.2
    have hraw : ContinuousOn
        (fun q : ℝ × M => (deTurckVF (I := I) (g_DT q.1) g₀ q.2 : TangentSpace I q.2))
        (Set.Icc (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α) :=
      hsum.congr heqOn
    have hmemq₀ : q₀ ∈ Set.Icc (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α :=
      ⟨hq₀.1, hα ▸ hα_mem⟩
    have hnhds : Set.Icc (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α
        ∈ nhdsWithin q₀ (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := by
      have hopen_in_dom : (Set.univ ×ˢ chartLeviCivitaGoodSet (I := I) α)
          ∈ nhdsWithin q₀ (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := by
        refine nhdsWithin_le_nhds ?_
        exact (isOpen_univ.prod hgood_open).mem_nhds ⟨Set.mem_univ _, hα ▸ hα_mem⟩
      refine Filter.mem_of_superset
        (Filter.inter_mem self_mem_nhdsWithin hopen_in_dom) ?_
      intro x hx
      exact ⟨hx.1.1, hx.2.2⟩
    exact (hraw.continuousWithinAt hmemq₀).mono_of_mem_nhdsWithin hnhds
  · intro α k
    exact DeTurckVFSmoothnessKeystone.fderiv_chartDeTurckVFComp_joint_continuousOn
      (I := I) g_DT g₀ α T (h_gram0 α) (h_partial α) (h_partial2 α) k

theorem deturck_solution_joint_smooth
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ)
    (h_smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M =>
          Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) x₀ i j
            (extChartAt I x₀ q.2))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2
        (deTurckVF (I := I) (g_DT q.1) (g_DT 0) q.2) : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) :=
  deturck_vf_joint_smoothness (I := I) (g_DT 0) g_DT T h_smooth

end DifferentialGeometry.PDE.RicciFlow
