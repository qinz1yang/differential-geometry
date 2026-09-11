import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.Curvature.Supremum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Algebra
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.CovariantTwoTensor
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Restriction
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Analysis.Laplacian

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

noncomputable section

universe u uE uH

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology ENNReal



def witnessLambda (eps : ℝ) : ℝ := (1 - eps)⁻¹

theorem one_le_witnessLambda {eps : ℝ} (h0 : 0 ≤ eps) (h1 : eps < 1) :
    1 ≤ witnessLambda eps := by
  have hpos : 0 < 1 - eps := by linarith
  rw [witnessLambda, le_inv_comm₀ zero_lt_one hpos, inv_one]
  linarith [h0]

theorem witnessLambda_le {eps : ℝ} (h1 : eps ≤ 1 / 4) :
    witnessLambda eps ≤ 4 / 3 := by
  have hpos : 0 < 1 - eps := by linarith
  rw [witnessLambda, inv_le_comm₀ hpos (by norm_num)]
  linarith

theorem one_add_le_witnessLambda {eps : ℝ} (h0 : 0 ≤ eps) (h1 : eps < 1) :
    1 + eps ≤ witnessLambda eps := by
  have hpos : 0 < 1 - eps := by linarith
  have hdiv : witnessLambda eps = 1 / (1 - eps) := by rw [witnessLambda, one_div]
  rw [hdiv, le_div_iff₀ hpos]
  nlinarith [h0]

def witnessRiemannC (eps : ℝ) : ℝ := riemannDiffC (witnessLambda eps) eps eps

theorem witnessRiemannC_nonneg {eps : ℝ} (h0 : 0 ≤ eps) (h1 : eps < 1) :
    0 ≤ witnessRiemannC eps := by
  have hL : (0 : ℝ) ≤ witnessLambda eps := le_trans zero_le_one (one_le_witnessLambda h0 h1)
  unfold witnessRiemannC riemannDiffC
  positivity

theorem witnessRiemannC_le {eps : ℝ} (h0 : 0 ≤ eps) (h1 : eps ≤ 1 / 4) :
    witnessRiemannC eps ≤ 20 * eps := by
  have hL1 : (1 : ℝ) ≤ witnessLambda eps := one_le_witnessLambda h0 (by linarith)
  have hL0 : (0 : ℝ) ≤ witnessLambda eps := le_trans zero_le_one hL1
  have hL : witnessLambda eps ≤ 4 / 3 := witnessLambda_le h1
  have h4 : witnessLambda eps ^ 4 ≤ (4 / 3 : ℝ) ^ 4 := pow_le_pow_left₀ hL0 hL 4
  have h5 : witnessLambda eps ^ 5 ≤ (4 / 3 : ℝ) ^ 5 := pow_le_pow_left₀ hL0 hL 5
  have h6 : witnessLambda eps ^ 6 ≤ (4 / 3 : ℝ) ^ 6 := pow_le_pow_left₀ hL0 hL 6
  have hsq : eps ^ 2 ≤ eps / 4 := by nlinarith
  have hexp : witnessRiemannC eps =
      3 * witnessLambda eps ^ 4 * eps + 3 * witnessLambda eps ^ 5 * eps ^ 2 +
        9 / 2 * witnessLambda eps ^ 6 * eps ^ 2 := by
    unfold witnessRiemannC riemannDiffC
    ring
  rw [hexp]
  have t1 : 3 * witnessLambda eps ^ 4 * eps ≤ 3 * (4 / 3 : ℝ) ^ 4 * eps := by nlinarith
  have t2 : 3 * witnessLambda eps ^ 5 * eps ^ 2 ≤ 3 * (4 / 3 : ℝ) ^ 5 * (eps / 4) := by
    nlinarith
  have t3 : 9 / 2 * witnessLambda eps ^ 6 * eps ^ 2 ≤ 9 / 2 * (4 / 3 : ℝ) ^ 6 * (eps / 4) := by
    nlinarith
  nlinarith [t1, t2, t3]

theorem witnessRiemannC_tendsto :
    Filter.Tendsto witnessRiemannC (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0) := by
  have hinv : ContinuousAt (fun e : ℝ => ((1 : ℝ) - e)⁻¹) 0 := by
    refine ContinuousAt.inv₀ ?_ (by norm_num)
    exact continuousAt_const.sub continuousAt_id
  have hcont : ContinuousAt witnessRiemannC 0 := by
    unfold witnessRiemannC riemannDiffC witnessLambda
    fun_prop (disch := norm_num)
  have hval : witnessRiemannC 0 = 0 := by
    unfold witnessRiemannC riemannDiffC witnessLambda
    norm_num
  have := hcont.tendsto
  rw [hval] at this
  exact this.mono_left nhdsWithin_le_nhds

section Transport

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
variable [T2Space N] [SigmaCompactSpace N] [BoundarylessManifold I N]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E




def sourceOpen (F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞)) :
    TopologicalSpace.Opens N :=
  ⟨F.source, F.open_source⟩

def openPullbackMetric
    (F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞))
    (U : TopologicalSpace.Opens N) (hU : (U : Set N) ⊆ F.source)
    (g : SmoothRiemannianMetric I M) : SmoothRiemannianMetric I U :=
  Diffeomorph.pullbackMetric (I := I)
    (g.restrictOpen (I := I)
      (⟨(F : N → M) '' (U : Set N), image_opens_isOpen F hU⟩ : TopologicalSpace.Opens M))
    (PartialDiffeomorph.toOpensDiffeo F hU)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [BoundarylessManifold I M] [SigmaCompactSpace N] [BoundarylessManifold I N] in
theorem openPullbackMetric_inner
    (F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞))
    (U : TopologicalSpace.Opens N) (hU : (U : Set N) ⊆ F.source)
    (g : SmoothRiemannianMetric I M) (y : U) (v w : TangentSpace I y) :
    (openPullbackMetric (I := I) F U hU g).inner y v w =
      g.inner ((F : N → M) (y : N))
        (mfderiv I I (F : N → M) (y : N) v)
        (mfderiv I I (F : N → M) (y : N) w) := by
  rw [openPullbackMetric, Diffeomorph.pullbackMetric_inner,
    SmoothRiemannianMetric.restrictOpen_inner,
    PartialDiffeomorph.mfderiv_toOpensDiffeo F hU y v,
    PartialDiffeomorph.mfderiv_toOpensDiffeo F hU y w]
  rfl



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace N]
  [BoundarylessManifold I N] in
theorem metricCovDeriv_self_eq_zero (g : SmoothRiemannianMetric I N) (a : ℕ) :
    metricCovDeriv (I := I) g g (a + 1) = 0 := by
  rw [metricCovDeriv_eq_covDerivOfField, covDerivOfField_eq_iterCov, iterCov_metric_zero,
    Tensor0SField.domDomCongr_zero]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace N]
  [BoundarylessManifold I N] in
theorem tensor02CovDeriv_sub_metricTensorField
    (g : SmoothRiemannianMetric I N)
    (A : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := N) (n := (∞ : WithTop ℕ∞)) 2) (a : ℕ) :
    tensor02CovDeriv (I := I) (A - Tensor0SBundle.metricTensorField (I := I) g) g (a + 1) =
      tensor02CovDeriv (I := I) A g (a + 1) := by
  rw [tensor02_cov_deriv_eq_cov_deriv_of_field, tensor02_cov_deriv_eq_cov_deriv_of_field, covDerivOfField_sub,
    ← metricCovDeriv_eq_covDerivOfField, metricCovDeriv_self_eq_zero, sub_zero]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [BoundarylessManifold I M] [SigmaCompactSpace N] [BoundarylessManifold I N] in
theorem openPullback_metricCovDerivNorm
    (F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞))
    (U : TopologicalSpace.Opens N) (hU : (U : Set N) ⊆ F.source)
    (gRef : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric I M)
    (P : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := N) (n := (∞ : WithTop ℕ∞)) 2)
    (hP : ∀ y : U, ∀ slots : Fin 2 → TangentSpace I (y : N),
      P (y : N) slots =
        g.inner ((F : N → M) (y : N))
          (mfderiv I I (F : N → M) (y : N) (slots 0))
          (mfderiv I I (F : N → M) (y : N) (slots 1)))
    (a : ℕ) (y : U) :
    metricCovDerivNorm (I := I) a (openPullbackMetric (I := I) F U hU g)
        (gRef.restrictOpen (I := I) U) y =
      tensor02CovDerivNormWith (I := I) a P gRef gRef (y : N) := by
  have hbase : ∀ (z : U) (slots : Fin 2 → TangentSpace I z),
      Tensor0SBundle.metricTensorField (I := I)
          (openPullbackMetric (I := I) F U hU g) z slots = P (z : N) slots := by
    intro z slots
    rw [Tensor0SBundle.metricTensorField_apply, openPullbackMetric_inner]
    exact (hP z slots).symm
  have htower := covDerivOfField_restrictOpen (I := I) gRef U
    (Tensor0SBundle.metricTensorField (I := I) (openPullbackMetric (I := I) F U hU g))
    P hbase a y
  have hT : metricCovDeriv (I := I) (openPullbackMetric (I := I) F U hU g)
      (gRef.restrictOpen (I := I) U) a y = covDerivOfField (I := I) gRef P a (y : N) := by
    rw [metricCovDeriv_eq_covDerivOfField]
    exact ContinuousMultilinearMap.ext htower
  unfold metricCovDerivNorm tensor02CovDerivNormWith
  rw [tensor02_cov_deriv_eq_cov_deriv_of_field, hT]
  congr 1
  exact normSq0S_restrictOpen_apply (I := I) gRef U (a + 2) y _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace N]
  [BoundarylessManifold I N] [FiniteDimensional ℝ E] in
private theorem metricSelfNonneg {M' : Type u} [TopologicalSpace M'] [ChartedSpace H M']
    [IsManifold I ∞ M'] (g : SmoothRiemannianMetric I M') (y : M') (v : TangentSpace I y) :
    0 ≤ g.inner y v v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · exact (g.pos y v hv).le

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [BoundarylessManifold I M] [SigmaCompactSpace N] [BoundarylessManifold I N]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [IsManifold I ∞ N] [T2Space N] in
theorem sourceOpen_subset (F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞)) :
    (sourceOpen (I := I) F : Set N) ⊆ F.source := subset_rfl


def witnessModelMetric (F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞))
    (h : ℝ → SmoothRiemannianMetric I N) (s : ℝ) :
    SmoothRiemannianMetric I (sourceOpen (I := I) F) :=
  (h s).restrictOpen (I := I) (sourceOpen (I := I) F)

def witnessPullbackMetric (F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞))
    (ghat : ℝ → SmoothRiemannianMetric I M) (s : ℝ) :
    SmoothRiemannianMetric I (sourceOpen (I := I) F) :=
  openPullbackMetric (I := I) F (sourceOpen (I := I) F) (sourceOpen_subset F) (ghat s)

def witnessWindow (F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞)) (eps : ℝ)
    (h : ℝ → SmoothRiemannianMetric I N) (p : N) : Set (sourceOpen (I := I) F) :=
  Subtype.val ⁻¹' riemannianClosedBallOf (I := I) (h 0) p (modelRadius eps)



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [BoundarylessManifold I M] [SigmaCompactSpace N] [BoundarylessManifold I N] in
theorem modelComparison_metricUniformEquivalentOn
    {eps : ℝ} (heps0 : 0 ≤ eps) (heps1 : eps < 1)
    {h : ℝ → SmoothRiemannianMetric I N} {ghat : ℝ → SmoothRiemannianMetric I M}
    {p : N} {x : M} {F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞)}
    (C : ModelComparison (I := I) eps h ghat p x F)
    {s : ℝ} (hs : s ∈ Set.Icc (-(modelDepth eps)) (0 : ℝ)) :
    MetricUniformEquivalentOn (I := I) (witnessWindow (I := I) F eps h p)
      (witnessModelMetric (I := I) F h s) (witnessPullbackMetric (I := I) F ghat s)
      (witnessLambda eps) := by
  refine ⟨one_le_witnessLambda heps0 heps1, ?_⟩
  intro y hy v
  have hmem : (y : N) ∈ riemannianClosedBallOf (I := I) (h 0) p (modelRadius eps) := hy
  obtain ⟨hlow, hhigh⟩ := C.metric_equivalence s hs (y : N) hmem v
  have hpb : (witnessPullbackMetric (I := I) F ghat s).inner y v v =
      C.pullback s (y : N) (fun _ => v) := by
    rw [witnessPullbackMetric, openPullbackMetric_inner]
    exact (C.pullback_apply s (y : N) y.2 (fun _ => v)).symm
  have href : (witnessModelMetric (I := I) F h s).inner y v v =
      (h s).inner (y : N) v v := rfl
  have hnn : 0 ≤ (h s).inner (y : N) v v := metricSelfNonneg (I := I) (h s) (y : N) v
  have hinv : (witnessLambda eps)⁻¹ = 1 - eps := by
    rw [witnessLambda, inv_inv]
  refine ⟨?_, ?_⟩
  · rw [hpb, href, hinv]
    exact hlow
  · rw [hpb, href]
    refine le_trans hhigh ?_
    exact mul_le_mul_of_nonneg_right (one_add_le_witnessLambda heps0 heps1) hnn

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] [SigmaCompactSpace N] [BoundarylessManifold I N] in
theorem modelComparison_jet_zero_eq
    {eps : ℝ} {h : ℝ → SmoothRiemannianMetric I N} {ghat : ℝ → SmoothRiemannianMetric I M}
    {p : N} {x : M} {F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞)}
    (C : ModelComparison (I := I) eps h ghat p x F) (s : ℝ) :
    C.jet 0 s = C.pullback s - Tensor0SBundle.metricTensorField (I := I) (h s) := by
  refine DFunLike.ext _ _ (fun z => ?_)
  have hz : (C.pullback s - Tensor0SBundle.metricTensorField (I := I) (h s)) z =
      C.pullback s z - Tensor0SBundle.metricTensorField (I := I) (h s) z := by
    simp only [ContMDiffSection.coe_sub, Pi.sub_apply]
  rw [hz]
  refine tensor0SSpace_ext 2 z (fun slots => ?_)
  rw [C.jet_zero s z slots, Tensor0SBundle.Tensor0SSpace.sub_apply,
    Tensor0SBundle.metricTensorField_apply]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [BoundarylessManifold I M] [SigmaCompactSpace N] [BoundarylessManifold I N] in
theorem modelComparison_metricCovDerivOrderBoundOn
    {eps : ℝ} {h : ℝ → SmoothRiemannianMetric I N} {ghat : ℝ → SmoothRiemannianMetric I M}
    {p : N} {x : M} {F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞)}
    (C : ModelComparison (I := I) eps h ghat p x F)
    {s : ℝ} (hs : s ∈ Set.Icc (-(modelDepth eps)) (0 : ℝ))
    {a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ modelOrder eps) :
    MetricCovDerivOrderBoundOn (I := I) (witnessWindow (I := I) F eps h p) a
      (witnessPullbackMetric (I := I) F ghat s) (witnessModelMetric (I := I) F h s) eps := by
  obtain ⟨b, rfl⟩ : ∃ b : ℕ, a = b + 1 := ⟨a - 1, by omega⟩
  intro y hy
  have hmem : (y : N) ∈ riemannianClosedBallOf (I := I) (h 0) p (modelRadius eps) := hy
  have hP : ∀ z : (sourceOpen (I := I) F), ∀ slots : Fin 2 → TangentSpace I (z : N),
      C.pullback s (z : N) slots =
        (ghat s).inner ((F : N → M) (z : N))
          (mfderiv I I (F : N → M) (z : N) (slots 0))
          (mfderiv I I (F : N → M) (z : N) (slots 1)) := fun z slots =>
    C.pullback_apply s (z : N) z.2 slots
  rw [witnessPullbackMetric, witnessModelMetric,
    openPullback_metricCovDerivNorm (I := I) F (sourceOpen (I := I) F)
      (sourceOpen_subset F) (h s) (ghat s) (C.pullback s) hP (b + 1) y]
  have hfield : tensor02CovDeriv (I := I) (C.pullback s) (h s) (b + 1) =
      tensor02CovDeriv (I := I) (C.jet 0 s) (h s) (b + 1) := by
    rw [modelComparison_jet_zero_eq C s, tensor02CovDeriv_sub_metricTensorField]
  have hclose := C.cm_close (b + 1) 0 (by simpa using ha) s hs (y : N) hmem
  unfold tensor02CovDerivNormWith
  rw [hfield]
  exact hclose



private theorem sqrt_le_of_sq_bound {A F a b c : ℝ} (hF : 0 ≤ F)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hA : A ≤ F ^ 2 * a * b * c) :
    Real.sqrt A ≤ F * Real.sqrt a * Real.sqrt b * Real.sqrt c := by
  have hprod : F ^ 2 * a * b * c = (F * Real.sqrt a * Real.sqrt b * Real.sqrt c) ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sq_sqrt hc]
  calc Real.sqrt A ≤ Real.sqrt ((F * Real.sqrt a * Real.sqrt b * Real.sqrt c) ^ 2) := by
        rw [← hprod]
        exact Real.sqrt_le_sqrt hA
    _ = F * Real.sqrt a * Real.sqrt b * Real.sqrt c := Real.sqrt_sq (by positivity)

theorem three_le_modelOrder {eps : ℝ} (h0 : 0 < eps) (h1 : eps ≤ 1 / 2) :
    3 ≤ modelOrder eps := by
  have hinv : (2 : ℝ) ≤ eps⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) h0]
    linarith
  have hceil : (2 : ℝ) ≤ (⌈eps⁻¹⌉₊ : ℝ) := le_trans hinv (Nat.le_ceil _)
  have hnat : 2 ≤ ⌈eps⁻¹⌉₊ := by exact_mod_cast hceil
  unfold modelOrder
  omega

theorem five_le_modelOrder {eps : ℝ} (h0 : 0 < eps) (h1 : eps ≤ 1 / 4) :
    5 ≤ modelOrder eps := by
  have hinv : (4 : ℝ) ≤ eps⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) h0]
    linarith
  have hceil : (4 : ℝ) ≤ (⌈eps⁻¹⌉₊ : ℝ) := le_trans hinv (Nat.le_ceil _)
  have hnat : 4 ≤ ⌈eps⁻¹⌉₊ := by exact_mod_cast hceil
  unfold modelOrder
  omega

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [BoundarylessManifold I M] [SigmaCompactSpace N] in
theorem modelComparison_riemannOp_sub_sq_le
    {eps : ℝ} (heps0 : 0 < eps) (heps1 : eps ≤ 1 / 2)
    {h : ℝ → SmoothRiemannianMetric I N} {ghat : ℝ → SmoothRiemannianMetric I M}
    {p : N} {x : M} {F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞)}
    (C : ModelComparison (I := I) eps h ghat p x F)
    {s : ℝ} (hs : s ∈ Set.Icc (-(modelDepth eps)) (0 : ℝ))
    {y : sourceOpen (I := I) F} (hy : y ∈ witnessWindow (I := I) F eps h p)
    (v w u : TangentSpace I y) :
    (witnessModelMetric (I := I) F h s).inner y
        (riemannOp (cov := LeviCivita (I := I) (witnessPullbackMetric (I := I) F ghat s))
            y v w u -
          riemannOp (cov := LeviCivita (I := I) (witnessModelMetric (I := I) F h s)) y v w u)
        (riemannOp (cov := LeviCivita (I := I) (witnessPullbackMetric (I := I) F ghat s))
            y v w u -
          riemannOp (cov := LeviCivita (I := I) (witnessModelMetric (I := I) F h s))
            y v w u) ≤
      witnessRiemannC eps ^ 2 *
        (witnessModelMetric (I := I) F h s).inner y v v *
        (witnessModelMetric (I := I) F h s).inner y w w *
        (witnessModelMetric (I := I) F h s).inner y u u := by
  have horder := three_le_modelOrder heps0 heps1
  have hEq := modelComparison_metricUniformEquivalentOn (I := I) heps0.le (by linarith) C hs
  have hJet1 := modelComparison_metricCovDerivOrderBoundOn (I := I) C hs
    (a := 1) le_rfl (by omega)
  have hJet2 := modelComparison_metricCovDerivOrderBoundOn (I := I) C hs
    (a := 2) (by omega) (by omega)
  exact riemannDiff_gJet_le (I := I) _ _ hEq hJet1 hJet2 hy v w u

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [BoundarylessManifold I M] [SigmaCompactSpace N] in
theorem modelComparison_riemannOp_sub_norm_le
    {eps : ℝ} (heps0 : 0 < eps) (heps1 : eps ≤ 1 / 2)
    {h : ℝ → SmoothRiemannianMetric I N} {ghat : ℝ → SmoothRiemannianMetric I M}
    {p : N} {x : M} {F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞)}
    (C : ModelComparison (I := I) eps h ghat p x F)
    {s : ℝ} (hs : s ∈ Set.Icc (-(modelDepth eps)) (0 : ℝ))
    {y : sourceOpen (I := I) F} (hy : y ∈ witnessWindow (I := I) F eps h p)
    (v w u : TangentSpace I y) :
    Real.sqrt ((witnessModelMetric (I := I) F h s).inner y
        (riemannOp (cov := LeviCivita (I := I) (witnessPullbackMetric (I := I) F ghat s))
            y v w u -
          riemannOp (cov := LeviCivita (I := I) (witnessModelMetric (I := I) F h s)) y v w u)
        (riemannOp (cov := LeviCivita (I := I) (witnessPullbackMetric (I := I) F ghat s))
            y v w u -
          riemannOp (cov := LeviCivita (I := I) (witnessModelMetric (I := I) F h s))
            y v w u)) ≤
      witnessRiemannC eps *
        Real.sqrt ((witnessModelMetric (I := I) F h s).inner y v v) *
        Real.sqrt ((witnessModelMetric (I := I) F h s).inner y w w) *
        Real.sqrt ((witnessModelMetric (I := I) F h s).inner y u u) :=
  sqrt_le_of_sq_bound (witnessRiemannC_nonneg heps0.le (by linarith))
    (metricSelfNonneg (I := I) _ _ _) (metricSelfNonneg (I := I) _ _ _)
    (metricSelfNonneg (I := I) _ _ _)
    (modelComparison_riemannOp_sub_sq_le (I := I) heps0 heps1 C hs hy v w u)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [BoundarylessManifold I M] [SigmaCompactSpace N] in
theorem modelComparison_riemannOp_norm_le
    {eps : ℝ} (heps0 : 0 < eps) (heps1 : eps ≤ 1 / 2)
    {h : ℝ → SmoothRiemannianMetric I N} {ghat : ℝ → SmoothRiemannianMetric I M}
    {p : N} {x : M} {F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞)}
    (C : ModelComparison (I := I) eps h ghat p x F)
    {s : ℝ} (hs : s ∈ Set.Icc (-(modelDepth eps)) (0 : ℝ))
    {y : sourceOpen (I := I) F} (hy : y ∈ witnessWindow (I := I) F eps h p)
    {Kb : ℝ} (hKb0 : 0 ≤ Kb)
    (hKb : ∀ a b c : TangentSpace I y,
      (witnessModelMetric (I := I) F h s).inner y
          (riemannOp (cov := LeviCivita (I := I) (witnessModelMetric (I := I) F h s)) y a b c)
          (riemannOp (cov := LeviCivita (I := I) (witnessModelMetric (I := I) F h s))
            y a b c) ≤
        Kb * (witnessModelMetric (I := I) F h s).inner y a a *
          (witnessModelMetric (I := I) F h s).inner y b b *
          (witnessModelMetric (I := I) F h s).inner y c c)
    (v w u : TangentSpace I y) :
    Real.sqrt ((witnessPullbackMetric (I := I) F ghat s).inner y
        (riemannOp (cov := LeviCivita (I := I) (witnessPullbackMetric (I := I) F ghat s))
          y v w u)
        (riemannOp (cov := LeviCivita (I := I) (witnessPullbackMetric (I := I) F ghat s))
          y v w u)) ≤
      witnessLambda eps ^ 2 * (witnessRiemannC eps + Real.sqrt Kb) *
        Real.sqrt ((witnessPullbackMetric (I := I) F ghat s).inner y v v) *
        Real.sqrt ((witnessPullbackMetric (I := I) F ghat s).inner y w w) *
        Real.sqrt ((witnessPullbackMetric (I := I) F ghat s).inner y u u) := by
  set hU := witnessModelMetric (I := I) F h s with hUdef
  set pb := witnessPullbackMetric (I := I) F ghat s with hpbdef
  set L := witnessLambda eps with hLdef
  have hEq := modelComparison_metricUniformEquivalentOn (I := I) heps0.le (by linarith) C hs
  have hL1 : (1 : ℝ) ≤ L := hEq.1
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL1
  have hL0 : (0 : ℝ) ≤ L := le_of_lt hLpos
  have hA : ∀ t : TangentSpace I y,
      Real.sqrt (pb.inner y t t) ≤ Real.sqrt L * Real.sqrt (hU.inner y t t) := by
    intro t
    calc Real.sqrt (pb.inner y t t) ≤ Real.sqrt (L * hU.inner y t t) :=
          Real.sqrt_le_sqrt (hEq.2 y hy t).2
      _ = Real.sqrt L * Real.sqrt (hU.inner y t t) := Real.sqrt_mul hL0 _
  have hB : ∀ t : TangentSpace I y,
      Real.sqrt (hU.inner y t t) ≤ Real.sqrt L * Real.sqrt (pb.inner y t t) := by
    intro t
    have hlow := (hEq.2 y hy t).1
    have hup : hU.inner y t t ≤ L * pb.inner y t t := by
      have hmul := mul_le_mul_of_nonneg_left hlow hL0
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hLpos), one_mul] at hmul
      exact hmul
    calc Real.sqrt (hU.inner y t t) ≤ Real.sqrt (L * pb.inner y t t) := Real.sqrt_le_sqrt hup
      _ = Real.sqrt L * Real.sqrt (pb.inner y t t) := Real.sqrt_mul hL0 _
  set R := riemannOp (cov := LeviCivita (I := I) pb) y v w u with hRdef
  set Rh := riemannOp (cov := LeviCivita (I := I) hU) y v w u with hRhdef
  have htri : Real.sqrt (hU.inner y R R) ≤
      Real.sqrt (hU.inner y (R - Rh) (R - Rh)) + Real.sqrt (hU.inner y Rh Rh) := by
    have h := Geometry.Riemannian.sqrt_inner_add_le (I := I) hU y (R - Rh) Rh
    rwa [sub_add_cancel] at h
  have hDb := modelComparison_riemannOp_sub_norm_le (I := I) heps0 heps1 C hs hy v w u
  have hRhb : Real.sqrt (hU.inner y Rh Rh) ≤
      Real.sqrt Kb * Real.sqrt (hU.inner y v v) * Real.sqrt (hU.inner y w w) *
        Real.sqrt (hU.inner y u u) := by
    refine sqrt_le_of_sq_bound (Real.sqrt_nonneg Kb) (metricSelfNonneg (I := I) _ _ _)
      (metricSelfNonneg (I := I) _ _ _) (metricSelfNonneg (I := I) _ _ _) ?_
    rw [Real.sq_sqrt hKb0]
    exact hKb v w u
  have hsum : Real.sqrt (hU.inner y R R) ≤
      (witnessRiemannC eps + Real.sqrt Kb) *
        (Real.sqrt (hU.inner y v v) * Real.sqrt (hU.inner y w w) *
          Real.sqrt (hU.inner y u u)) := by
    have := add_le_add hDb hRhb
    calc Real.sqrt (hU.inner y R R) ≤
          Real.sqrt (hU.inner y (R - Rh) (R - Rh)) + Real.sqrt (hU.inner y Rh Rh) := htri
      _ ≤ witnessRiemannC eps * Real.sqrt (hU.inner y v v) * Real.sqrt (hU.inner y w w) *
            Real.sqrt (hU.inner y u u) +
          Real.sqrt Kb * Real.sqrt (hU.inner y v v) * Real.sqrt (hU.inner y w w) *
            Real.sqrt (hU.inner y u u) := this
      _ = (witnessRiemannC eps + Real.sqrt Kb) *
            (Real.sqrt (hU.inner y v v) * Real.sqrt (hU.inner y w w) *
              Real.sqrt (hU.inner y u u)) := by ring
  have hCsum0 : 0 ≤ witnessRiemannC eps + Real.sqrt Kb :=
    add_nonneg (witnessRiemannC_nonneg heps0.le (by linarith)) (Real.sqrt_nonneg Kb)
  have hr4 : Real.sqrt L ^ 4 = L ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hL0]
  calc Real.sqrt (pb.inner y R R) ≤ Real.sqrt L * Real.sqrt (hU.inner y R R) := hA R
    _ ≤ Real.sqrt L * ((witnessRiemannC eps + Real.sqrt Kb) *
          (Real.sqrt (hU.inner y v v) * Real.sqrt (hU.inner y w w) *
            Real.sqrt (hU.inner y u u))) :=
        mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg L)
    _ ≤ Real.sqrt L * ((witnessRiemannC eps + Real.sqrt Kb) *
          ((Real.sqrt L * Real.sqrt (pb.inner y v v)) *
            (Real.sqrt L * Real.sqrt (pb.inner y w w)) *
            (Real.sqrt L * Real.sqrt (pb.inner y u u)))) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left ?_ hCsum0) (Real.sqrt_nonneg L)
        exact mul_le_mul
          (mul_le_mul (hB v) (hB w) (Real.sqrt_nonneg _) (by positivity)) (hB u)
          (Real.sqrt_nonneg _) (by positivity)
    _ = L ^ 2 * (witnessRiemannC eps + Real.sqrt Kb) *
          Real.sqrt (pb.inner y v v) * Real.sqrt (pb.inner y w w) *
          Real.sqrt (pb.inner y u u) := by
        rw [← hr4]
        ring



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace N] in
theorem openPullbackMetric_scalar
    (F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞))
    (U : TopologicalSpace.Opens N) (hU : (U : Set N) ⊆ F.source)
    (g : SmoothRiemannianMetric I M) (y : U) :
    metricScalarAt (I := I) (openPullbackMetric (I := I) F U hU g) y =
      metricScalarAt (I := I) g ((F : N → M) (y : N)) := by
  let _ : SigmaCompactSpace
      (⟨(F : N → M) '' (U : Set N), image_opens_isOpen F hU⟩ : TopologicalSpace.Opens M) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I
        (⟨(F : N → M) '' (U : Set N), image_opens_isOpen F hU⟩ :
          TopologicalSpace.Opens M).isOpen)
  rw [openPullbackMetric, metricScalarAt_pullback, metricScalarAt_restrictOpen]
  rfl

omit [I.Boundaryless] [SigmaCompactSpace M] [BoundarylessManifold I M]
  [SigmaCompactSpace N] in
theorem modelComparison_ricciTensor_sub_le
    {eps : ℝ} (heps0 : 0 < eps) (heps1 : eps ≤ 1 / 2)
    {h : ℝ → SmoothRiemannianMetric I N} {ghat : ℝ → SmoothRiemannianMetric I M}
    {p : N} {x : M} {F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞)}
    (C : ModelComparison (I := I) eps h ghat p x F)
    {s : ℝ} (hs : s ∈ Set.Icc (-(modelDepth eps)) (0 : ℝ))
    {y : sourceOpen (I := I) F} (hy : y ∈ witnessWindow (I := I) F eps h p)
    (v w : TangentSpace I y) :
    |ricciTensor (I := I) (witnessPullbackMetric (I := I) F ghat s) y v w -
        ricciTensor (I := I) (witnessModelMetric (I := I) F h s) y v w| ≤
      (Module.finrank ℝ E : ℝ) * witnessRiemannC eps *
        Real.sqrt ((witnessModelMetric (I := I) F h s).inner y v v) *
        Real.sqrt ((witnessModelMetric (I := I) F h s).inner y w w) := by
  classical
  set hU := witnessModelMetric (I := I) F h s with hUdef
  set pb := witnessPullbackMetric (I := I) F ghat s with hpbdef
  set B : Fin (Module.finrank ℝ E) → TangentSpace I y :=
    fun i => smoothOrthoFrame (I := I) hU y i y with hBdef
  have hB : ∀ i j : Fin (Module.finrank ℝ E),
      hU.inner y (B i) (B j) = if i = j then (1 : ℝ) else 0 := fun i j =>
    smoothOrthoFrame_orthonormal_at_center (I := I) hU y i j
  have hBii : ∀ i, hU.inner y (B i) (B i) = 1 := by
    intro i
    rw [hB i i]
    simp
  have hsplit : ricciTensor (I := I) pb y v w - ricciTensor (I := I) hU y v w =
      ∑ i : Fin (Module.finrank ℝ E),
        hU.inner y ((ricciEndo (I := I) pb y v w - ricciEndo (I := I) hU y v w) (B i))
          (B i) := by
    rw [ricciTensor_apply, ricciTensor_apply,
      ← map_sub (LinearMap.trace ℝ (TangentSpace I y)) (ricciEndo (I := I) pb y v w)
        (ricciEndo (I := I) hU y v w),
      trace_eq_ortho_sum (I := I) hU y
        (ricciEndo (I := I) pb y v w - ricciEndo (I := I) hU y v w) B hB]
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      |hU.inner y ((ricciEndo (I := I) pb y v w - ricciEndo (I := I) hU y v w) (B i))
        (B i)| ≤
        witnessRiemannC eps * Real.sqrt (hU.inner y v v) * Real.sqrt (hU.inner y w w) := by
    intro i
    have hval : (ricciEndo (I := I) pb y v w - ricciEndo (I := I) hU y v w) (B i) =
        riemannOp (cov := LeviCivita (I := I) pb) y (B i) v w -
          riemannOp (cov := LeviCivita (I := I) hU) y (B i) v w := rfl
    have hnorm := modelComparison_riemannOp_sub_norm_le (I := I) heps0 heps1 C hs hy (B i) v w
    rw [← hUdef, ← hpbdef] at hnorm
    rw [hBii i, Real.sqrt_one, mul_one] at hnorm
    calc |hU.inner y ((ricciEndo (I := I) pb y v w - ricciEndo (I := I) hU y v w) (B i))
            (B i)|
        ≤ Real.sqrt (hU.inner y
              ((ricciEndo (I := I) pb y v w - ricciEndo (I := I) hU y v w) (B i))
              ((ricciEndo (I := I) pb y v w - ricciEndo (I := I) hU y v w) (B i))) *
            Real.sqrt (hU.inner y (B i) (B i)) :=
          abs_metric_inner_le_sqrt_metric_quadratic (I := I) hU y _ _
      _ = Real.sqrt (hU.inner y
              ((ricciEndo (I := I) pb y v w - ricciEndo (I := I) hU y v w) (B i))
              ((ricciEndo (I := I) pb y v w - ricciEndo (I := I) hU y v w) (B i))) := by
          rw [hBii i, Real.sqrt_one, mul_one]
      _ ≤ witnessRiemannC eps * Real.sqrt (hU.inner y v v) *
            Real.sqrt (hU.inner y w w) := by rw [hval]; exact hnorm
  rw [hsplit]
  calc |∑ i : Fin (Module.finrank ℝ E),
          hU.inner y ((ricciEndo (I := I) pb y v w - ricciEndo (I := I) hU y v w) (B i))
            (B i)|
      ≤ ∑ i : Fin (Module.finrank ℝ E),
          |hU.inner y ((ricciEndo (I := I) pb y v w - ricciEndo (I := I) hU y v w) (B i))
            (B i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ E),
          witnessRiemannC eps * Real.sqrt (hU.inner y v v) *
            Real.sqrt (hU.inner y w w) := Finset.sum_le_sum (fun i _ => hterm i)
    _ = (Module.finrank ℝ E : ℝ) * witnessRiemannC eps *
          Real.sqrt (hU.inner y v v) * Real.sqrt (hU.inner y w w) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [BoundarylessManifold I M] [SigmaCompactSpace N] [BoundarylessManifold I N] in
theorem modelComparison_sqrt_model_le
    {eps : ℝ} (heps0 : 0 ≤ eps) (heps1 : eps < 1)
    {h : ℝ → SmoothRiemannianMetric I N} {ghat : ℝ → SmoothRiemannianMetric I M}
    {p : N} {x : M} {F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞)}
    (C : ModelComparison (I := I) eps h ghat p x F)
    {s : ℝ} (hs : s ∈ Set.Icc (-(modelDepth eps)) (0 : ℝ))
    {y : sourceOpen (I := I) F} (hy : y ∈ witnessWindow (I := I) F eps h p)
    (t : TangentSpace I y) :
    Real.sqrt ((witnessModelMetric (I := I) F h s).inner y t t) ≤
      Real.sqrt (witnessLambda eps) *
        Real.sqrt ((witnessPullbackMetric (I := I) F ghat s).inner y t t) := by
  have hEq := modelComparison_metricUniformEquivalentOn (I := I) heps0 heps1 C hs
  have hL1 : (1 : ℝ) ≤ witnessLambda eps := hEq.1
  have hLpos : (0 : ℝ) < witnessLambda eps := lt_of_lt_of_le zero_lt_one hL1
  have hL0 : (0 : ℝ) ≤ witnessLambda eps := le_of_lt hLpos
  have hlow := (hEq.2 y hy t).1
  have hup : (witnessModelMetric (I := I) F h s).inner y t t ≤
      witnessLambda eps * (witnessPullbackMetric (I := I) F ghat s).inner y t t := by
    have hmul := mul_le_mul_of_nonneg_left hlow hL0
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hLpos), one_mul] at hmul
    exact hmul
  calc Real.sqrt ((witnessModelMetric (I := I) F h s).inner y t t)
      ≤ Real.sqrt (witnessLambda eps *
          (witnessPullbackMetric (I := I) F ghat s).inner y t t) := Real.sqrt_le_sqrt hup
    _ = Real.sqrt (witnessLambda eps) *
          Real.sqrt ((witnessPullbackMetric (I := I) F ghat s).inner y t t) :=
        Real.sqrt_mul hL0 _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [BoundarylessManifold I M] [SigmaCompactSpace N] [BoundarylessManifold I N] in
def metricScalarDifferential {M' : Type u} [TopologicalSpace M'] [ChartedSpace H M']
    [IsManifold I ∞ M']
    (g : SmoothRiemannianMetric I M') (z : M') (v : TangentSpace I z) : ℝ :=
  mfderiv I (modelWithCornersSelf ℝ ℝ) (fun q : M' => metricScalarAt (I := I) g q) z v

def ScalarGradientComparison (I : ModelWithCorners ℝ E H) (gradC : ℝ → ℝ) : Prop :=
  ∀ (M' : Type u) [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
    [T2Space M'] [BoundarylessManifold I M'] (g₁ g₂ : SmoothRiemannianMetric I M')
    (K : Set M') (eps : ℝ), 0 < eps → eps ≤ 1 / 4 →
    MetricUniformEquivalentOn (I := I) K g₂ g₁ (witnessLambda eps) →
    (∀ a : ℕ, 1 ≤ a → a ≤ 3 → MetricCovDerivOrderBoundOn (I := I) K a g₁ g₂ eps) →
    ∀ z ∈ K, ∀ v : TangentSpace I z,
      |metricScalarDifferential (I := I) g₁ z v -
          metricScalarDifferential (I := I) g₂ z v| ≤ gradC eps * Real.sqrt (g₂.inner z v v)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [BoundarylessManifold I M] [SigmaCompactSpace N] in
theorem modelComparison_scalarDifferential_sub_le
    {gradC : ℝ → ℝ} (hGC : ScalarGradientComparison.{u, uE, uH} I gradC)
    {eps : ℝ} (heps0 : 0 < eps) (heps1 : eps ≤ 1 / 4)
    {h : ℝ → SmoothRiemannianMetric I N} {ghat : ℝ → SmoothRiemannianMetric I M}
    {p : N} {x : M} {F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞)}
    (C : ModelComparison (I := I) eps h ghat p x F)
    {s : ℝ} (hs : s ∈ Set.Icc (-(modelDepth eps)) (0 : ℝ))
    {y : sourceOpen (I := I) F} (hy : y ∈ witnessWindow (I := I) F eps h p)
    (v : TangentSpace I y) :
    |metricScalarDifferential (I := I) (witnessPullbackMetric (I := I) F ghat s) y v -
        metricScalarDifferential (I := I) (witnessModelMetric (I := I) F h s) y v| ≤
      gradC eps * Real.sqrt ((witnessModelMetric (I := I) F h s).inner y v v) := by
  have horder := five_le_modelOrder heps0 heps1
  have hEq := modelComparison_metricUniformEquivalentOn (I := I) heps0.le (by linarith) C hs
  have hJet : ∀ a : ℕ, 1 ≤ a → a ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) (witnessWindow (I := I) F eps h p) a
        (witnessPullbackMetric (I := I) F ghat s)
        (witnessModelMetric (I := I) F h s) eps := fun a ha1 ha3 =>
    modelComparison_metricCovDerivOrderBoundOn (I := I) C hs ha1 (by omega)
  exact hGC ↥(sourceOpen (I := I) F) (witnessPullbackMetric (I := I) F ghat s)
    (witnessModelMetric (I := I) F h s) (witnessWindow (I := I) F eps h p) eps
    heps0 heps1 hEq hJet y hy v

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [BoundarylessManifold I M] [SigmaCompactSpace N] in
theorem modelComparison_scalarDifferential_le
    {gradC : ℝ → ℝ} (hGC : ScalarGradientComparison.{u, uE, uH} I gradC)
    {eps : ℝ} (hgradC0 : 0 ≤ gradC eps) (heps0 : 0 < eps) (heps1 : eps ≤ 1 / 4)
    {h : ℝ → SmoothRiemannianMetric I N} {ghat : ℝ → SmoothRiemannianMetric I M}
    {p : N} {x : M} {F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞)}
    (C : ModelComparison (I := I) eps h ghat p x F)
    {s : ℝ} (hs : s ∈ Set.Icc (-(modelDepth eps)) (0 : ℝ))
    {y : sourceOpen (I := I) F} (hy : y ∈ witnessWindow (I := I) F eps h p)
    {G : ℝ} (hG0 : 0 ≤ G)
    (hG : ∀ t : TangentSpace I y,
      |metricScalarDifferential (I := I) (witnessModelMetric (I := I) F h s) y t| ≤
        G * Real.sqrt ((witnessModelMetric (I := I) F h s).inner y t t))
    (v : TangentSpace I y) :
    |metricScalarDifferential (I := I) (witnessPullbackMetric (I := I) F ghat s) y v| ≤
      Real.sqrt (witnessLambda eps) * (G + gradC eps) *
        Real.sqrt ((witnessPullbackMetric (I := I) F ghat s).inner y v v) := by
  have hsub := modelComparison_scalarDifferential_sub_le (I := I) hGC heps0 heps1 C hs hy v
  have hmod := hG v
  have hlen := modelComparison_sqrt_model_le (I := I) heps0.le (by linarith) C hs hy v
  set A := metricScalarDifferential (I := I) (witnessPullbackMetric (I := I) F ghat s) y v
    with hAdef
  set Bm := metricScalarDifferential (I := I) (witnessModelMetric (I := I) F h s) y v
    with hBmdef
  set S := Real.sqrt ((witnessModelMetric (I := I) F h s).inner y v v) with hSdef
  set Q := Real.sqrt ((witnessPullbackMetric (I := I) F ghat s).inner y v v) with hQdef
  have habs : |A| - |Bm| ≤ |A - Bm| := abs_sub_abs_le_abs_sub A Bm
  have hsplit : |A| ≤ (G + gradC eps) * S := by nlinarith [habs, hsub, hmod]
  have hfin : (G + gradC eps) * S ≤
      Real.sqrt (witnessLambda eps) * (G + gradC eps) * Q := by
    have hmul := mul_le_mul_of_nonneg_left hlen (add_nonneg hG0 hgradC0)
    nlinarith [hmul]
  linarith [hsplit, hfin]

end Transport

end

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
