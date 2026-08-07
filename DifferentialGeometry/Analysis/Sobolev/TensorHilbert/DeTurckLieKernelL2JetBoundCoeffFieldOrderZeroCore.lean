import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBoundCoeffFieldOrderZeroIdentities
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Laplacian (metric_inner_self_nonneg)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (connDiffCovDerivBiContrFib dLaBiContrFib_contMDiff deTurckLieDLbFib deTurckLieDLbFib_contMDiff
    deTurckLieFib deTurckLieCoeffField deTurckLieCoeffField_toSection
    deTurckConnDiffCovDeriv connDiff_pairing_mdiffAt connDiffCovDerivOp dLaCovKernel_apply_extend
    covGrad)
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
  (g0FlatCLM cotangentToDual_g0FlatCLM g0FlatCLM_apply)
open DifferentialGeometry.Geometry.Curvature
  (abs_tensor_one_three_flat_eval_le_fibreNorm_mul_sqrt)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
theorem abs_g1_inner_le_two_sqrt (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    {δs : ℝ} (hδs1 : δs ≤ 1)
    (hb : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δs)
    (x : M) (u w : TangentSpace I x) :
    |g₁.inner x u w| ≤
      2 * (Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x w w)) := by
  rw [htie x u w]
  refine le_trans (abs_add_le _ _) ?_
  have h1 := abs_metric_inner_le (I := I) (M := M) g₀ x u w
  have h2 := hb x u w
  have hnn : 0 ≤ Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x w w) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [h1, h2, hnn]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private theorem coframeS_one_eq_g0FlatCLM_local
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin 1 → Fin n) :
    coframeS (I := I) (M := M) g₀ x 1 e K = g0FlatCLM (I := I) g₀ x (e (K 0)) := by
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply, cotangentToDual_apply,
    cotangentToDual_apply]
  rw [show coframeS (I := I) (M := M) g₀ x 1 e K (fun _ : Fin 1 => w) =
      ∏ k : Fin 1, g₀.inner x (e (K k)) w from coframeS_apply (I := I) (M := M) g₀ x 1 e K _]
  rw [Fin.prod_univ_one]
  rw [g0FlatCLM_apply, dualToCotangent_apply]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] in
theorem toModel_coframeS_two (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin 2 → Fin n)
    (p q : TangentSpace I x) :
    Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 2 e K) ![(p : E), (q : E)] =
      g₀.inner x (e (K 0)) p * g₀.inner x (e (K 1)) q := by
  rw [show Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 2 e K) ![(p : E), (q : E)] =
      coframeS (I := I) (M := M) g₀ x 2 e K ![p, q] from rfl]
  rw [coframeS_apply (I := I) (M := M) g₀ x 2 e K ![p, q], Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private theorem abs_tensor12_flat_eval_le_fibreNorm_mul_sqrt_local
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (W : TensorRSSpace 1 2 I x) (d a b : TangentSpace I x) :
    |Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
          (g0FlatCLM (I := I) g₀ x d))
        (Fin.cons a ![b])| ≤
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x W) *
        Real.sqrt (g₀.inner x d d) *
        Real.sqrt (g₀.inner x a a) * Real.sqrt (g₀.inner x b b) := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr, _hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  set vec : Fin 2 → TangentSpace I x := ![a, b] with hvec_def
  set coef : (Fin 1 → Fin n) × (Fin 2 → Fin n) → ℝ :=
    fun p => g₀.inner x (e (p.1 0)) d * ∏ i : Fin 2, g₀.inner x (e (p.2 i)) (vec i) with hcoef_def
  set comp : (Fin 1 → Fin n) × (Fin 2 → Fin n) → ℝ :=
    fun p => fiberNormSqComponent (I := I) (M := M) g₀ x 1 2 W n e p.1 p.2 with hcomp_def
  have hcompval : ∀ (K : Fin 1 → Fin n) (J : Fin 2 → Fin n),
      fiberNormSqComponent (I := I) (M := M) g₀ x 1 2 W n e K J =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
            (g0FlatCLM (I := I) g₀ x (e (K 0))))
          (fun i : Fin 2 => e (J i)) := by
    intro K J
    rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 1 2 W n e K J =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
            (coframeS (I := I) (M := M) g₀ x 1 e K))
          (fun i : Fin 2 => e (J i)) from rfl]
    rw [coframeS_one_eq_g0FlatCLM_local (I := I) (M := M) g₀ x e K]
  have hWd : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
        (g0FlatCLM (I := I) g₀ x d) =
      ∑ k : Fin n, g₀.inner x (e k) d •
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
          (g0FlatCLM (I := I) g₀ x (e k)) := by
    have hflat : g0FlatCLM (I := I) g₀ x d =
        ∑ k : Fin n, g₀.inner x (e k) d • g0FlatCLM (I := I) g₀ x (e k) := by
      conv_lhs => rw [hrepr d]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [map_smul]
    rw [hflat, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul]
  have hexp : ∀ i : Fin 2, vec i = ∑ j : Fin n, g₀.inner x (e j) (vec i) • e j :=
    fun i => hrepr (vec i)
  have hvalue : Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
          (g0FlatCLM (I := I) g₀ x d))
        (Fin.cons a ![b]) =
      ∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), coef p * comp p := by
    change Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
          (g0FlatCLM (I := I) g₀ x d)) vec =
        ∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), coef p * comp p
    rw [hWd]
    rw [show Tensor0SSpace.toModel
          (∑ k : Fin n, g₀.inner x (e k) d •
            (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
              (g0FlatCLM (I := I) g₀ x (e k))) =
        ∑ k : Fin n, g₀.inner x (e k) d •
          Tensor0SSpace.toModel
            ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
              (g0FlatCLM (I := I) g₀ x (e k))) from by
      rw [← Tensor0SSpace.toModelL_apply, map_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [map_smul, Tensor0SSpace.toModelL_apply]]
    rw [ContinuousMultilinearMap.sum_apply]
    have hterm : ∀ k : Fin n,
        (g₀.inner x (e k) d •
          Tensor0SSpace.toModel
            ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
              (g0FlatCLM (I := I) g₀ x (e k)))) vec =
        ∑ J : Fin 2 → Fin n,
          (g₀.inner x (e k) d * ∏ i : Fin 2, g₀.inner x (e (J i)) (vec i)) *
            fiberNormSqComponent (I := I) (M := M) g₀ x 1 2 W n e (fun _ => k) J := by
      intro k
      rw [ContinuousMultilinearMap.smul_apply]
      set B2 : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ :=
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
            (g0FlatCLM (I := I) g₀ x (e k))) with hB2_def
      set coefJ : (Fin 2 → Fin n) → ℝ :=
        fun J => ∏ i : Fin 2, g₀.inner x (e (J i)) (vec i) with hcoefJ_def
      set compJ : (Fin 2 → Fin n) → ℝ :=
        fun J => B2 (fun i : Fin 2 => (show E from e (J i))) with hcompJ_def
      have hexp' : ∀ i : Fin 2, (show E from vec i) =
          ∑ j : Fin n, g₀.inner x (e j) (vec i) • (show E from e j) :=
        fun i => hexp i
      have hB2val : B2 vec = ∑ J : Fin 2 → Fin n, coefJ J * compJ J := by
        have hrw : B2 vec = B2 (fun i : Fin 2 =>
            ∑ j : Fin n, g₀.inner x (e j) (vec i) • (show E from e j)) := by
          congr 1
          funext i
          exact hexp' i
        rw [hrw, ContinuousMultilinearMap.map_sum]
        refine Finset.sum_congr rfl (fun J _ => ?_)
        rw [hcoefJ_def, hcompJ_def]
        rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]
      rw [hB2val, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun J _ => ?_)
      rw [hcompJ_def, hcompval (fun _ => k) J, ← hB2_def, hcoefJ_def]
      ring
    rw [Finset.sum_congr rfl (fun k _ => hterm k)]
    rw [show (∑ k : Fin n, ∑ J : Fin 2 → Fin n,
          (g₀.inner x (e k) d * ∏ i : Fin 2, g₀.inner x (e (J i)) (vec i)) *
            fiberNormSqComponent (I := I) (M := M) g₀ x 1 2 W n e (fun _ => k) J) =
        ∑ K : Fin 1 → Fin n, ∑ J : Fin 2 → Fin n,
          (g₀.inner x (e (K 0)) d * ∏ i : Fin 2, g₀.inner x (e (J i)) (vec i)) *
            fiberNormSqComponent (I := I) (M := M) g₀ x 1 2 W n e K J from by
      refine (Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n)).symm _ _ (fun k => ?_))
      refine Finset.sum_congr rfl (fun J _ => ?_)
      have hKeq : (Equiv.funUnique (Fin 1) (Fin n)).symm k = (fun _ : Fin 1 => k) := rfl
      rw [hKeq]]
    rw [← Fintype.sum_prod_type']
  rw [hvalue]
  have hCS : (∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), coef p * comp p) ^ 2 ≤
      (∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), coef p ^ 2) *
        ∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), comp p ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ coef comp
  have hdd_nn : 0 ≤ g₀.inner x d d := metric_inner_self_nonneg (I := I) (M := M) g₀ x d
  have haa_nn : 0 ≤ g₀.inner x a a := metric_inner_self_nonneg (I := I) (M := M) g₀ x a
  have hbb_nn : 0 ≤ g₀.inner x b b := metric_inner_self_nonneg (I := I) (M := M) g₀ x b
  have hcoefsq : (∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), coef p ^ 2) =
      g₀.inner x d d * (g₀.inner x a a * g₀.inner x b b) := by
    have hpow : ∀ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), coef p ^ 2 =
        g₀.inner x (e (p.1 0)) d ^ 2 *
          ∏ i : Fin 2, g₀.inner x (e (p.2 i)) (vec i) ^ 2 := by
      intro p
      rw [hcoef_def, mul_pow, ← Finset.prod_pow]
    rw [Finset.sum_congr rfl (fun p _ => hpow p)]
    rw [Fintype.sum_prod_type]
    rw [show (∑ K : Fin 1 → Fin n, ∑ J : Fin 2 → Fin n,
          g₀.inner x (e (K 0)) d ^ 2 * ∏ i : Fin 2, g₀.inner x (e (J i)) (vec i) ^ 2) =
        (∑ K : Fin 1 → Fin n, g₀.inner x (e (K 0)) d ^ 2) *
          ∑ J : Fin 2 → Fin n, ∏ i : Fin 2, g₀.inner x (e (J i)) (vec i) ^ 2 from by
      rw [Finset.sum_mul_sum]]
    have hKsum : (∑ K : Fin 1 → Fin n, g₀.inner x (e (K 0)) d ^ 2) = g₀.inner x d d := by
      rw [← hpars d]
      rw [show (∑ K : Fin 1 → Fin n, g₀.inner x (e (K 0)) d ^ 2) =
          ∑ k : Fin n, g₀.inner x (e k) d ^ 2 from by
        rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin n))
          (fun k : Fin n => g₀.inner x (e k) d ^ 2)]
        rfl]
    have hJsum : (∑ J : Fin 2 → Fin n, ∏ i : Fin 2, g₀.inner x (e (J i)) (vec i) ^ 2) =
        g₀.inner x a a * g₀.inner x b b := by
      rw [show (∑ J : Fin 2 → Fin n, ∏ i : Fin 2, g₀.inner x (e (J i)) (vec i) ^ 2) =
          ∑ J ∈ Fintype.piFinset (fun _ : Fin 2 => (Finset.univ : Finset (Fin n))),
            ∏ i : Fin 2, g₀.inner x (e (J i)) (vec i) ^ 2 from by
        rw [Fintype.piFinset_univ]]
      rw [← Finset.prod_univ_sum (fun _ : Fin 2 => (Finset.univ : Finset (Fin n)))
        (fun i j => g₀.inner x (e j) (vec i) ^ 2)]
      rw [Fin.prod_univ_two]
      rw [hpars (vec 0), hpars (vec 1)]
      have h0 : vec 0 = a := rfl
      have h1 : vec 1 = b := rfl
      rw [h0, h1]
    rw [hKsum, hJsum]
  have hcompsq : (∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), comp p ^ 2) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x W := by
    rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 1 2 x W e bse hnE
      hbse horth]
    rw [Fintype.sum_prod_type]
  have hnorm_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x W :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 2 x W
  have habs_sq : (∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), coef p * comp p) ^ 2 ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x W *
        (g₀.inner x d d * (g₀.inner x a a * g₀.inner x b b)) := by
    calc (∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), coef p * comp p) ^ 2
        ≤ (∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), coef p ^ 2) *
            ∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), comp p ^ 2 := hCS
      _ = (g₀.inner x d d * (g₀.inner x a a * g₀.inner x b b)) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x W := by
            rw [hcoefsq, hcompsq]
      _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x W *
            (g₀.inner x d d * (g₀.inner x a a * g₀.inner x b b)) := by ring
  rw [← Real.sqrt_sq (abs_nonneg (∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), coef p * comp p)),
    sq_abs]
  rw [show Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x W) *
        Real.sqrt (g₀.inner x d d) *
        Real.sqrt (g₀.inner x a a) * Real.sqrt (g₀.inner x b b) =
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x W *
        (g₀.inner x d d * (g₀.inner x a a * g₀.inner x b b))) from ?_]
  · exact Real.sqrt_le_sqrt habs_sq
  · rw [Real.sqrt_mul hnorm_nn]
    rw [Real.sqrt_mul hdd_nn, Real.sqrt_mul haa_nn]
    ring

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_fixed_connDiff_sqrt_bound (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : M) (v w : TangentSpace I x),
      Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g_bg g₀ x v w)
          (PDE.DeTurck.connDiff (I := I) g_bg g₀ x v w)) ≤
        C * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
  classical
  obtain ⟨K, hK0, hK⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M)
    g₀ 1 2 (connDiffSection (I := I) g_bg g₀)
  refine ⟨Real.sqrt K, Real.sqrt_nonneg _, ?_⟩
  intro x v w
  set cd : TangentSpace I x := PDE.DeTurck.connDiff (I := I) g_bg g₀ x v w with hcd_def
  set W : TensorRSSpace 1 2 I x := connDiffFib (I := I) g_bg g₀ x with hW_def
  have hval : Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
        (g0FlatCLM (I := I) g₀ x cd)) (Fin.cons (v : E) ![(w : E)]) = g₀.inner x cd cd := by
    rw [show Tensor0SSpace.toModel ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
          (g0FlatCLM (I := I) g₀ x cd)) (Fin.cons (v : E) ![(w : E)]) =
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
            connDiffFib (I := I) g_bg g₀ x)
          (g0FlatCLM (I := I) g₀ x cd)) ![v, w] from rfl]
    rw [connDiffFib_apply_eval (I := I) g_bg g₀ x (g0FlatCLM (I := I) g₀ x cd) ![v, w]]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show (g0FlatCLM (I := I) g₀ x cd)
          (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) g_bg g₀ x v w) =
        cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x cd)
          (PDE.DeTurck.connDiff (I := I) g_bg g₀ x v w) from
      (cotangentToDual_apply (I := I) (x := x) _ _).symm]
    rw [cotangentToDual_g0FlatCLM (I := I) g₀ x cd]
  have habs := abs_tensor12_flat_eval_le_fibreNorm_mul_sqrt_local (I := I) (M := M)
    g₀ x W cd v w
  rw [hval] at habs
  have hcdcd_nn : 0 ≤ g₀.inner x cd cd := metric_inner_self_nonneg (I := I) (M := M) g₀ x cd
  rw [abs_of_nonneg hcdcd_nn] at habs
  have hWnorm : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x W) ≤
      Real.sqrt K := by
    have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x W ≤ K := by
      have h := hK x
      rw [connDiffSection_toSection] at h
      rw [hW_def]
      exact h
    exact Real.sqrt_le_sqrt h2
  set NA : ℝ := Real.sqrt (g₀.inner x cd cd) with hNA_def
  have hNA_nn : 0 ≤ NA := Real.sqrt_nonneg _
  have hAA_sq : g₀.inner x cd cd = NA ^ 2 := by rw [hNA_def, Real.sq_sqrt hcdcd_nn]
  set Sv : ℝ := Real.sqrt (g₀.inner x v v) with hSv_def
  set Sw : ℝ := Real.sqrt (g₀.inner x w w) with hSw_def
  have hSv_nn : 0 ≤ Sv := Real.sqrt_nonneg _
  have hSw_nn : 0 ≤ Sw := Real.sqrt_nonneg _
  set NW : ℝ := Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x W) with hNW_def
  have hNW_nn : 0 ≤ NW := Real.sqrt_nonneg _
  have hprim' : NA ^ 2 ≤ NW * NA * Sv * Sw := by
    rw [← hAA_sq]
    exact habs
  have hNA_le : NA ≤ NW * Sv * Sw := by
    rcases eq_or_lt_of_le hNA_nn with hNA0 | hNApos
    · rw [← hNA0]
      positivity
    · have hkey : NA * NA ≤ NA * (NW * Sv * Sw) := by
        rw [show NA * NA = NA ^ 2 from by ring]
        refine le_trans hprim' ?_
        apply le_of_eq; ring
      exact le_of_mul_le_mul_left hkey hNApos
  calc NA ≤ NW * Sv * Sw := hNA_le
    _ ≤ Real.sqrt K * Sv * Sw := by
        have hprod_nn : 0 ≤ Sv * Sw := mul_nonneg hSv_nn hSw_nn
        nlinarith [hWnorm, hprod_nn, hSv_nn, hSw_nn, hNW_nn]

omit [NeZero (Module.finrank ℝ E)] in
private theorem covGrad_connDiffSection_flat_eval_eq_inner_local
    (g₀ g_c : SmoothRiemannianMetric I M) (x : M) (v w u : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g_c g₀)).toSection x)
          (g0FlatCLM (I := I) g₀ x
            (covDerivConnDiff (I := I) g₀ g_c
              (smoothExtensionTangent (I := I) x v)
              (smoothExtensionTangent (I := I) x w)
              (smoothExtensionTangent (I := I) x u) x)))
        (Fin.cons v (Fin.cons u ![w])) =
      g₀.inner x
        (covDerivConnDiff (I := I) g₀ g_c
          (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w)
          (smoothExtensionTangent (I := I) x u) x)
        (covDerivConnDiff (I := I) g₀ g_c
          (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w)
          (smoothExtensionTangent (I := I) x u) x) := by
  classical
  set A : TangentSpace I x :=
    covDerivConnDiff (I := I) g₀ g_c
      (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent (I := I) x w)
      (smoothExtensionTangent (I := I) x u) x with hA_def
  set Xsec : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent_contMDiff (I := I) x v) with hXsec_def
  set Ysec : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x u)
      (smoothExtensionTangent_contMDiff (I := I) x u) with hYsec_def
  set Zsec : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
      (smoothExtensionTangent_contMDiff (I := I) x w) with hZsec_def
  have hXx : Xsec x = v := smoothExtensionTangent_eq (I := I) x v
  have hYx : Ysec x = u := smoothExtensionTangent_eq (I := I) x u
  have hZx : Zsec x = w := smoothExtensionTangent_eq (I := I) x w
  have hA_bridge : covDerivConnDiff (I := I) g₀ g_c Xsec Zsec Ysec x = A := by
    rw [hA_def]; rfl
  obtain ⟨om, hom⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := Tensor0SModel 1 ℝ E) (V := fun y : M => Tensor0SSpace 1 I y) x
    (g0FlatCLM (I := I) g₀ x A)
  have hbridge := connDiffSection_covGrad_eq_covDerivConnDiff (I := I) g_c g₀ om Xsec Ysec Zsec x
  rw [hom, hXx, hYx, hZx, hA_bridge] at hbridge
  have hflatA : (g0FlatCLM (I := I) g₀ x A) (fun _ : Fin 1 => A) = g₀.inner x A A := by
    rw [show (g0FlatCLM (I := I) g₀ x A) (fun _ : Fin 1 => A) =
        cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x A) A from
      (cotangentToDual_apply (I := I) (x := x) _ _).symm]
    rw [cotangentToDual_g0FlatCLM (I := I) g₀ x A A]
  rw [hflatA] at hbridge
  rw [hA_def]
  exact hbridge

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_fixed_covDerivConnDiff_sqrt_bound
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : M) (v w u : TangentSpace I x),
      Real.sqrt (g₀.inner x
          (covDerivConnDiff (I := I) g₀ g_bg
            (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent (I := I) x u) x)
          (covDerivConnDiff (I := I) g₀ g_bg
            (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent (I := I) x u) x)) ≤
        C * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) *
          Real.sqrt (g₀.inner x u u) := by
  classical
  obtain ⟨K, hK0, hK⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M)
    g₀ 1 3 (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g_bg g₀))
  refine ⟨Real.sqrt K, Real.sqrt_nonneg _, ?_⟩
  intro x v w u
  letI instW : Bundle.RiemannianBundle (fun y : M => Tensor0SBundle.TensorRSSpace 1 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 1 3
  set W : Tensor0SBundle.TensorRSSpace 1 3 I x :=
    (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g_bg g₀)).toSection x
    with hW_def
  set A : TangentSpace I x :=
    covDerivConnDiff (I := I) g₀ g_bg
      (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent (I := I) x w)
      (smoothExtensionTangent (I := I) x u) x with hA_def
  have hAA_nn : 0 ≤ g₀.inner x A A := metric_inner_self_nonneg (I := I) (M := M) g₀ x A
  set NA : ℝ := Real.sqrt (g₀.inner x A A) with hNA_def
  have hNA_nn : 0 ≤ NA := Real.sqrt_nonneg _
  have hbridge := covGrad_connDiffSection_flat_eval_eq_inner_local (I := I) (M := M)
    g₀ g_bg x v w u
  rw [← hA_def, ← hW_def] at hbridge
  have hprim := abs_tensor_one_three_flat_eval_le_fibreNorm_mul_sqrt (I := I) (M := M) g₀ x W A v u
    w
  rw [hbridge] at hprim
  rw [abs_of_nonneg hAA_nn] at hprim
  have hAA_sq : g₀.inner x A A = NA ^ 2 := by rw [hNA_def, Real.sq_sqrt hAA_nn]
  set Sv : ℝ := Real.sqrt (g₀.inner x v v) with hSv_def
  set Sw : ℝ := Real.sqrt (g₀.inner x w w) with hSw_def
  set Su : ℝ := Real.sqrt (g₀.inner x u u) with hSu_def
  have hSv_nn : 0 ≤ Sv := Real.sqrt_nonneg _
  have hSw_nn : 0 ≤ Sw := Real.sqrt_nonneg _
  have hSu_nn : 0 ≤ Su := Real.sqrt_nonneg _
  set NW : ℝ := ‖(W : Tensor0SBundle.TensorRSSpace 1 3 I x)‖ with hNW_def
  have hNW_nn : 0 ≤ NW := norm_nonneg _
  have hWnorm : NW ≤ Real.sqrt K := by
    have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 3 x W ≤ K := hK x
    have h1 : NW ^ 2 ≤ K := by
      rw [hNW_def, ← riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 1 3 x W]
      exact h2
    calc NW = Real.sqrt (NW ^ 2) := (Real.sqrt_sq hNW_nn).symm
      _ ≤ Real.sqrt K := Real.sqrt_le_sqrt h1
  have hprim' : NA ^ 2 ≤ NW * NA * Sv * Su * Sw := by
    rw [← hAA_sq]
    exact hprim
  have hNA_le : NA ≤ NW * Sv * Sw * Su := by
    rcases eq_or_lt_of_le hNA_nn with hNA0 | hNApos
    · rw [← hNA0]
      positivity
    · have hkey : NA * NA ≤ NA * (NW * Sv * Su * Sw) := by
        rw [show NA * NA = NA ^ 2 from by ring]
        refine le_trans hprim' ?_
        apply le_of_eq; ring
      have hcancel := le_of_mul_le_mul_left hkey hNApos
      calc NA ≤ NW * Sv * Su * Sw := hcancel
        _ = NW * Sv * Sw * Su := by ring
  calc NA ≤ NW * Sv * Sw * Su := hNA_le
    _ ≤ Real.sqrt K * Sv * Sw * Su := by
        have hprod_nn : 0 ≤ Sv * Sw * Su := by positivity
        nlinarith [hWnorm, hprod_nn, hSv_nn, hSw_nn, hSu_nn, hNW_nn]


end DifferentialGeometry.Analysis.Sobolev

end
