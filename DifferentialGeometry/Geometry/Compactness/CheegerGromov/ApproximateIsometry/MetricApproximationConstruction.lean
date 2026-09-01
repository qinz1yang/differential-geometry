import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.PairwiseApproximateIsometry
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound
import DifferentialGeometry.Geometry.Exponential.GaussLemmaPullback
import DifferentialGeometry.Analysis.Estimates.BilinearMapPerturbation
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [MetricSpace M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
    [PseudoMetricSpace N]

section CmDiag

open DifferentialGeometry.Geometry.Riemannian

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
  [T2Space M'] [T2Space (TangentBundle I M')] [SigmaCompactSpace M']
  [ConnectedSpace M'] [T3Space M']

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] [T2Space M']
    [T2Space (TangentBundle I M')] [SigmaCompactSpace M'] [ConnectedSpace M'] [T3Space M'] in
theorem normSq0S_ortho {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M') (x : M')
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j : Idx, g.inner x (basis i) (basis j) = if i = j then (1 : ℝ) else 0)
    (A : Tensor0SBundle.Tensor0SSpace 2 I x) :
    Tensor0SBundle.normSq0S (I := I) g x 2 A
      = ∑ i : Idx, ∑ j : Idx,
          (A (fun a : Fin 2 => if a = 0 then basis i else basis j)) ^ 2 := by
  classical
  have hδ : Tensor0SBundle.MetricInverseInBasis (I := I) g x basis
      (fun i j => if i = j then (1 : ℝ) else 0) := by
    intro i j
    constructor
    · rw [Finset.sum_eq_single i]
      · simp [hON i j]
      · intro k _ hk
        simp [Ne.symm hk]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    · rw [Finset.sum_eq_single j]
      · simp [hON i j]
      · intro k _ hk
        simp [hON i k, hk]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
  rw [Tensor0SBundle.normSq0S_two_eq_coord (I := I) g x basis _ hδ]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [mul_ite, ite_mul, one_mul, zero_mul, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] [T2Space M'] [T2Space (TangentBundle I M')] [SigmaCompactSpace M'] [ConnectedSpace M'] [T3Space M'] in
theorem sqrtNormSq_le_of_comp
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M') (x : M')
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j : Idx, g.inner x (basis i) (basis j) = if i = j then (1 : ℝ) else 0)
    (A : Tensor0SBundle.Tensor0SSpace 2 I x) {c : ℝ} (hc : 0 ≤ c)
    (hcomp : ∀ i j : Idx,
      |A (fun a : Fin 2 => if a = 0 then basis i else basis j)| ≤ c) :
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 A) ≤ (Fintype.card Idx : ℝ) * c := by
  rw [normSq0S_ortho (I := I) g x basis hON A]
  have hsum : ∑ i : Idx, ∑ j : Idx,
      (A (fun a : Fin 2 => if a = 0 then basis i else basis j)) ^ 2
        ≤ ((Fintype.card Idx : ℝ) * c) ^ 2 := by
    calc ∑ i : Idx, ∑ j : Idx,
        (A (fun a : Fin 2 => if a = 0 then basis i else basis j)) ^ 2
        ≤ ∑ _i : Idx, ∑ _j : Idx, c ^ 2 := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          have h := hcomp i j
          have habs : (A (fun a : Fin 2 => if a = 0 then basis i else basis j)) ^ 2
              = |A (fun a : Fin 2 => if a = 0 then basis i else basis j)| ^ 2 := (sq_abs _).symm
          rw [habs]
          exact pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = (Fintype.card Idx : ℝ) ^ 2 * c ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ]
          ring
      _ = ((Fintype.card Idx : ℝ) * c) ^ 2 := by ring
  calc Real.sqrt (∑ i : Idx, ∑ j : Idx,
      (A (fun a : Fin 2 => if a = 0 then basis i else basis j)) ^ 2)
      ≤ Real.sqrt (((Fintype.card Idx : ℝ) * c) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = (Fintype.card Idx : ℝ) * c := by
        rw [Real.sqrt_sq (by positivity)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [Module.Finite ℝ E] [T2Space M'] [SigmaCompactSpace M'] [ConnectedSpace M'] [T3Space M'] in
omit [NeZero (Module.finrank ℝ E)] in
theorem mfderivNormalCenter
    [Module.Finite ℝ E]
    {N' : Type u} [TopologicalSpace N'] [ChartedSpace H N'] [IsManifold I ∞ N']
    [T2Space (TangentBundle I N')]
    (gk : SmoothRiemannianMetric I M') (gn : SmoothRiemannianMetric I N')
    (F : M' → N') (y : M')
    (hG : DifferentiableAt ℝ
      (fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
        (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z))) (0 : E))
    (hev : F =ᶠ[nhds y] fun q =>
      (NormalCoordinates.normalChartAt (I := I) gn (F y)).symm
        (NormalCoordinates.normalChartAt (I := I) gn (F y)
          (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm
            (NormalCoordinates.normalChartAt (I := I) gk y q))))) :
    mfderiv I I F y = fderiv ℝ
      (fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
        (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z))) (0 : E) := by
  classical
  have hcy : NormalCoordinates.normalChartAt (I := I) gk y y = 0 := by
    have h0 := (NormalCoordinates.expMapDiffeo (I := I) gk y).toPartialEquiv.left_inv
      (NormalCoordinates.zero_mem_expMapDiffeo_source (I := I) gk y)
    rw [NormalCoordinates.expMapDiffeo_zero] at h0
    exact h0
  have hdFy : NormalCoordinates.normalChartAt (I := I) gn (F y) (F y) = 0 := by
    have h0 := (NormalCoordinates.expMapDiffeo (I := I) gn (F y)).toPartialEquiv.left_inv
      (NormalCoordinates.zero_mem_expMapDiffeo_source (I := I) gn (F y))
    rw [NormalCoordinates.expMapDiffeo_zero] at h0
    exact h0
  have hcsymm0 : (NormalCoordinates.normalChartAt (I := I) gk y).symm (0 : E) = y := by
    change NormalCoordinates.expMapDiffeo (I := I) gk y (0 : E) = y
    exact NormalCoordinates.expMapDiffeo_zero (I := I) gk y
  have hysrc : y ∈ (NormalCoordinates.normalChartAt (I := I) gk y).source :=
    NormalCoordinates.p_mem_expMapDiffeo_target (I := I) gk y
  have hcm : MDifferentiableAt I 𝓘(ℝ, E)
      (NormalCoordinates.normalChartAt (I := I) gk y) y :=
    (NormalCoordinates.normalChartAt (I := I) gk y).mdifferentiableAt one_ne_zero hysrc
  have hGm : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      (fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
        (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z)))
      (NormalCoordinates.normalChartAt (I := I) gk y y) := by
    rw [hcy]
    exact hG.mdifferentiableAt
  have hGc_m : MDifferentiableAt I 𝓘(ℝ, E)
      (fun q => (fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
        (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z)))
          (NormalCoordinates.normalChartAt (I := I) gk y q)) y :=
    hGm.comp y hcm
  have h0tgt : (0 : E) ∈ (NormalCoordinates.normalChartAt (I := I) gn (F y)).symm.source := by
    change (0 : E) ∈ (NormalCoordinates.expMapDiffeo (I := I) gn (F y)).source
    exact NormalCoordinates.zero_mem_expMapDiffeo_source (I := I) gn (F y)
  have hdsymm_m : MDifferentiableAt 𝓘(ℝ, E) I
      ((NormalCoordinates.normalChartAt (I := I) gn (F y)).symm)
      ((fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
        (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z)))
          (NormalCoordinates.normalChartAt (I := I) gk y y)) := by
    have hval : (fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
        (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z)))
          (NormalCoordinates.normalChartAt (I := I) gk y y) = 0 := by
      simp only [hcy, hcsymm0, hdFy]
    rw [hval]
    exact (NormalCoordinates.normalChartAt (I := I) gn (F y)).symm.mdifferentiableAt
      one_ne_zero h0tgt
  rw [Filter.EventuallyEq.mfderiv_eq hev]
  have hsplit := mfderiv_comp (I := I) (I' := 𝓘(ℝ, E)) (I'' := I) y hdsymm_m hGc_m
  rw [show (fun q => (NormalCoordinates.normalChartAt (I := I) gn (F y)).symm
        (NormalCoordinates.normalChartAt (I := I) gn (F y)
          (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm
            (NormalCoordinates.normalChartAt (I := I) gk y q)))))
      = ((NormalCoordinates.normalChartAt (I := I) gn (F y)).symm : E → N')
        ∘ (fun q => (fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
            (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z)))
              (NormalCoordinates.normalChartAt (I := I) gk y q)) from rfl, hsplit]
  have hinner := mfderiv_comp (I := I) (I' := 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, E)) y hGm hcm
  rw [show (fun q => (fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
        (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z)))
          (NormalCoordinates.normalChartAt (I := I) gk y q))
      = ((fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
          (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z)))
        ∘ (NormalCoordinates.normalChartAt (I := I) gk y : M' → E)) from rfl] at hsplit ⊢
  rw [hinner] at hsplit ⊢
  have hd0 : (fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
      (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z)))
        (NormalCoordinates.normalChartAt (I := I) gk y y) = 0 := by
    simp only [hcy, hcsymm0, hdFy]
  rw [hd0, NormalCoordinates.mfderiv_normalChartAt_symm_zero (I := I) gn (F y),
    NormalCoordinates.mfderiv_normalChartAt_self (I := I) gk y]
  have hmodel : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
      (fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
        (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z)))
      (NormalCoordinates.normalChartAt (I := I) gk y y)
      = fderiv ℝ (fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
        (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z))) (0 : E) := by
    rw [hcy]
    exact mfderiv_eq_fderiv
  rw [hmodel]
  ext v
  rfl

omit [Module.Finite ℝ E] in
omit [T2Space M'] [SigmaCompactSpace M'] [ConnectedSpace M'] [T3Space M'] in
omit [NeZero (Module.finrank ℝ E)] in
theorem pullbackErrComp
    [Module.Finite ℝ E]
    {N' : Type u} [TopologicalSpace N'] [ChartedSpace H N'] [IsManifold I ∞ N']
    [T2Space (TangentBundle I N')]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M']
    (gk : SmoothRiemannianMetric I M') (gn : SmoothRiemannianMetric I N')
    {F : M' → N'} {y : M'}
    (hpb : PullbackMetricTensorData (I := I) F gn)
    (hG : DifferentiableAt ℝ
      (fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
        (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z))) (0 : E))
    (hev : F =ᶠ[nhds y] fun q =>
      (NormalCoordinates.normalChartAt (I := I) gn (F y)).symm
        (NormalCoordinates.normalChartAt (I := I) gn (F y)
          (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm
            (NormalCoordinates.normalChartAt (I := I) gk y q)))))
    {ε η : ℝ}
    (hA : ‖fderiv ℝ (fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
        (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z))) (0 : E)
      - ContinuousLinearMap.id ℝ E‖ ≤ ε)
    (hB : ∀ v' w' : E, |gn.inner (F y) v' w' - gk.inner y v' w'| ≤ η * (‖v'‖ * ‖w'‖))
    (v w : TangentSpace I y) :
    |(hpb.pullback y - Tensor0SBundle.metricTensorField (I := I) gk y)
        (fun a : Fin 2 => if a = 0 then v else w)|
      ≤ ((‖gn.inner (F y)‖ * ε * (2 + ε)) + η) * (‖v‖ * ‖w‖) := by
  have hsub : (hpb.pullback y - Tensor0SBundle.metricTensorField (I := I) gk y)
      (fun a : Fin 2 => if a = 0 then v else w)
      = hpb.pullback y (fun a : Fin 2 => if a = 0 then v else w)
        - Tensor0SBundle.metricTensorField (I := I) gk y
            (fun a : Fin 2 => if a = 0 then v else w) := rfl
  have hpba := hpb.pullback_apply y (fun a : Fin 2 => if a = 0 then v else w)
  norm_num at hpba
  set A := fderiv ℝ (fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
    (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z))) (0 : E) with hAdef
  have hmv : mfderiv I I F y v = A v :=
    DFunLike.congr_fun (mfderivNormalCenter (I := I) gk gn F y hG hev) v
  have hmw : mfderiv I I F y w = A w :=
    DFunLike.congr_fun (mfderivNormalCenter (I := I) gk gn F y hG hev) w
  rw [hsub, hpba, hmv, hmw, Tensor0SBundle.metricTensorField_apply]
  norm_num
  have h1 := bilinPerturb (B := gn.inner (F y)) (A := A) v w
  have h2 := hB v w
  have hAle : ‖A‖ ≤ 1 + ε := by
    calc ‖A‖ = ‖ContinuousLinearMap.id ℝ E + (A - ContinuousLinearMap.id ℝ E)‖ := by
          congr 1; abel
      _ ≤ ‖ContinuousLinearMap.id ℝ E‖ + ‖A - ContinuousLinearMap.id ℝ E‖ := norm_add_le _ _
      _ ≤ 1 + ε := add_le_add ContinuousLinearMap.norm_id_le hA
  have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) hA
  have hcoef : ‖gn.inner (F y)‖ * ‖A - ContinuousLinearMap.id ℝ E‖ * (1 + ‖A‖)
      ≤ ‖gn.inner (F y)‖ * ε * (2 + ε) := by
    have h2' : (1 : ℝ) + ‖A‖ ≤ 2 + ε := by linarith [hAle]
    gcongr
  calc |gn.inner (F y) (A v) (A w) - gk.inner y v w|
      = |(gn.inner (F y) (A v) (A w) - gn.inner (F y) v w)
          + (gn.inner (F y) v w - gk.inner y v w)| := by ring_nf
    _ ≤ |gn.inner (F y) (A v) (A w) - gn.inner (F y) v w|
        + |gn.inner (F y) v w - gk.inner y v w| := abs_add_le _ _
    _ ≤ ‖gn.inner (F y)‖ * ‖A - ContinuousLinearMap.id ℝ E‖ * (1 + ‖A‖) * (‖v‖ * ‖w‖)
        + η * (‖v‖ * ‖w‖) := add_le_add h1 h2
    _ ≤ ‖gn.inner (F y)‖ * ε * (2 + ε) * (‖v‖ * ‖w‖) + η * (‖v‖ * ‖w‖) := by
        gcongr
    _ = ((‖gn.inner (F y)‖ * ε * (2 + ε)) + η) * (‖v‖ * ‖w‖) := by ring

omit [Module.Finite ℝ E] [T2Space M'] [SigmaCompactSpace M'] [ConnectedSpace M'] [T3Space M'] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartRoundTrip_ev
    [Module.Finite ℝ E]
    {N' : Type u} [TopologicalSpace N'] [ChartedSpace H N'] [IsManifold I ∞ N']
    [T2Space (TangentBundle I N')]
    (gk : SmoothRiemannianMetric I M') (gn : SmoothRiemannianMetric I N')
    {F : M' → N'} {y : M'}
    (hsrc : ∀ᶠ q in nhds y, q ∈ (NormalCoordinates.normalChartAt (I := I) gk y).source)
    (hFsrc : ∀ᶠ q in nhds y,
      F q ∈ (NormalCoordinates.normalChartAt (I := I) gn (F y)).source) :
    F =ᶠ[nhds y] fun q =>
      (NormalCoordinates.normalChartAt (I := I) gn (F y)).symm
        (NormalCoordinates.normalChartAt (I := I) gn (F y)
          (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm
            (NormalCoordinates.normalChartAt (I := I) gk y q)))) := by
  filter_upwards [hsrc, hFsrc] with q hq hFq
  rw [show ((NormalCoordinates.normalChartAt (I := I) gk y).symm : E → M')
        ((NormalCoordinates.normalChartAt (I := I) gk y) q) = q from
      (NormalCoordinates.normalChartAt (I := I) gk y).toPartialEquiv.left_inv hq,
    show ((NormalCoordinates.normalChartAt (I := I) gn (F y)).symm : E → N')
        ((NormalCoordinates.normalChartAt (I := I) gn (F y)) (F q)) = F q from
      (NormalCoordinates.normalChartAt (I := I) gn (F y)).toPartialEquiv.left_inv hFq]

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] [T2Space M']
    [T2Space (TangentBundle I M')] [SigmaCompactSpace M'] [ConnectedSpace M'] [T3Space M'] in
theorem exists_gON_bd (g : SmoothRiemannianMetric I M') (x : M')
    {cLow : ℝ} (hc : 0 < cLow)
    (hcoer : ∀ v : TangentSpace I x, cLow * ‖v‖ ^ 2 ≤ g.inner x v v) :
    ∃ basis : Module.Basis (Fin (Module.finrank ℝ (TangentSpace I x))) ℝ (TangentSpace I x),
      (∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : ℝ) else 0) ∧
      ∀ i, ‖(basis i : TangentSpace I x)‖ ≤ (Real.sqrt cLow)⁻¹ := by
  obtain ⟨basis, hON⟩ :=
    DifferentialGeometry.Geometry.Curvature.exists_gOrthonormalBasis (I := I) g x
  refine ⟨basis, hON, fun i => ?_⟩
  have h1 : cLow * ‖(basis i : TangentSpace I x)‖ ^ 2 ≤ 1 := by
    have := hcoer (basis i)
    rw [hON i i, if_pos rfl] at this
    linarith
  have hs : Real.sqrt cLow > 0 := Real.sqrt_pos.mpr hc
  have hsq : Real.sqrt cLow * Real.sqrt cLow = cLow := Real.mul_self_sqrt (le_of_lt hc)
  rw [inv_eq_one_div, le_div_iff₀ hs]
  nlinarith [h1, hsq, norm_nonneg (basis i : TangentSpace I x),
    sq_nonneg (‖(basis i : TangentSpace I x)‖ * Real.sqrt cLow - 1)]

omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [T2Space M'] [SigmaCompactSpace M'] [ConnectedSpace M'] [T3Space M'] in
theorem pullbackErrNorm
    [Module.Finite ℝ E]
    {N' : Type u} [TopologicalSpace N'] [ChartedSpace H N'] [IsManifold I ∞ N']
    [T2Space (TangentBundle I N')] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M']
    (gk : SmoothRiemannianMetric I M') (gn : SmoothRiemannianMetric I N')
    {F : M' → N'} {y : M'}
    (hpb : PullbackMetricTensorData (I := I) F gn)
    (hG : DifferentiableAt ℝ
      (fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
        (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z))) (0 : E))
    (hev : F =ᶠ[nhds y] fun q =>
      (NormalCoordinates.normalChartAt (I := I) gn (F y)).symm
        (NormalCoordinates.normalChartAt (I := I) gn (F y)
          (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm
            (NormalCoordinates.normalChartAt (I := I) gk y q)))))
    {ε η cLow : ℝ} (hη : 0 ≤ η) (hc : 0 < cLow)
    (hcoer : ∀ v : TangentSpace I y, cLow * ‖v‖ ^ 2 ≤ gk.inner y v v)
    (hA : ‖fderiv ℝ (fun z => NormalCoordinates.normalChartAt (I := I) gn (F y)
        (F ((NormalCoordinates.normalChartAt (I := I) gk y).symm z))) (0 : E)
      - ContinuousLinearMap.id ℝ E‖ ≤ ε)
    (hB : ∀ v' w' : E, |gn.inner (F y) v' w' - gk.inner y v' w'| ≤ η * (‖v'‖ * ‖w'‖)) :
    metricTensorErrorNorm (I := I) hpb.pullback gk y
      ≤ (Module.finrank ℝ (TangentSpace I y) : ℝ)
        * (((‖gn.inner (F y)‖ * ε * (2 + ε)) + η)
            * ((Real.sqrt cLow)⁻¹ * (Real.sqrt cLow)⁻¹)) := by
  obtain ⟨basis, hON, hbd⟩ := exists_gON_bd (I := I) gk y hc hcoer
  have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) hA
  have hs0 : (0 : ℝ) ≤ (Real.sqrt cLow)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hc0 : 0 ≤ (((‖gn.inner (F y)‖ * ε * (2 + ε)) + η)
      * ((Real.sqrt cLow)⁻¹ * (Real.sqrt cLow)⁻¹)) := by positivity
  have hmain : Real.sqrt (Tensor0SBundle.normSq0S (I := I) gk y 2
      (hpb.pullback y - Tensor0SBundle.metricTensorField (I := I) gk y))
      ≤ (Fintype.card (Fin (Module.finrank ℝ (TangentSpace I y))) : ℝ)
        * (((‖gn.inner (F y)‖ * ε * (2 + ε)) + η)
            * ((Real.sqrt cLow)⁻¹ * (Real.sqrt cLow)⁻¹)) := by
    refine (sqrtNormSq_le_of_comp (I := I) gk y basis hON _ hc0 ?_)
    intro i j
    have h := pullbackErrComp (I := I) gk gn hpb hG hev hA hB (basis i) (basis j)
    refine h.trans ?_
    have hbb : ‖(basis i : TangentSpace I y)‖ * ‖(basis j : TangentSpace I y)‖
        ≤ (Real.sqrt cLow)⁻¹ * (Real.sqrt cLow)⁻¹ :=
      mul_le_mul (hbd i) (hbd j) (norm_nonneg _) hs0
    have hcoefnn : 0 ≤ (‖gn.inner (F y)‖ * ε * (2 + ε)) + η := by positivity
    exact mul_le_mul_of_nonneg_left hbb hcoefnn
  change Real.sqrt (Tensor0SBundle.normSq0S (I := I) gk y 2
      (hpb.pullback y - Tensor0SBundle.metricTensorField (I := I) gk y)) ≤ _
  simpa only [Fintype.card_fin] using hmain

def mapMetricApproximationOnOfBounds
    {N' : Type u} [TopologicalSpace N'] [ChartedSpace H N'] [IsManifold I ∞ N']
    (K : Set M') (eps : ℝ) (p : ℕ) (F : M' → N')
    (g : SmoothRiemannianMetric I M') (h : SmoothRiemannianMetric I N')
    (hpb : PullbackMetricTensorData (I := I) F h)
    (heps : 0 < eps) (heps1 : eps < 1)
    (hsmooth : ContMDiffOn I I (∞ : WithTop ℕ∞) F K)
    (hc0 : ∀ x ∈ K, metricTensorErrorNorm (I := I) hpb.pullback g x ≤ eps)
    (hcov : ∀ a : ℕ, 1 ≤ a → a ≤ p → ∀ x ∈ K,
      tensor02CovDerivNormWith (I := I) a hpb.pullback g g x ≤ eps) :
    MapMetricApproximationOn (I := I) K eps p F g h where
  eps_pos := heps
  eps_lt_one := heps1
  smoothOn := hsmooth
  pullback := hpb.pullback
  pullback_apply := fun x _ v => hpb.pullback_apply x v
  c0_small := hc0
  cov_deriv_small := hcov

def mapMetricApproximationOnOfZeroOrderBounds
    {N' : Type u} [TopologicalSpace N'] [ChartedSpace H N'] [IsManifold I ∞ N']
    (K : Set M') (eps : ℝ) (F : M' → N')
    (g : SmoothRiemannianMetric I M') (h : SmoothRiemannianMetric I N')
    (hpb : PullbackMetricTensorData (I := I) F h)
    (heps : 0 < eps) (heps1 : eps < 1)
    (hsmooth : ContMDiffOn I I (∞ : WithTop ℕ∞) F K)
    (hc0 : ∀ x ∈ K, metricTensorErrorNorm (I := I) hpb.pullback g x ≤ eps) :
    MapMetricApproximationOn (I := I) K eps 0 F g h :=
  mapMetricApproximationOnOfBounds K eps 0 F g h hpb heps heps1 hsmooth hc0
    (by intro a ha ha0 x hx; omega)

def partialDiffeomorphMetricApproximationOfBounds
    {N' : Type u} [TopologicalSpace N'] [ChartedSpace H N'] [IsManifold I ∞ N']
    [T2Space N'] (K : Set M') (eps : ℝ) (p : ℕ)
    (Φ : PartialDiffeomorph I I M' N' (∞ : WithTop ℕ∞))
    (g : SmoothRiemannianMetric I M') (h : SmoothRiemannianMetric I N')
    (hsub : K ⊆ Φ.source)
    (heps : 0 < eps) (heps1 : eps < 1)
    (hpbF : PullbackMetricTensorData (I := I) (Φ : M' → N') h)
    (hsmoothF : ContMDiffOn I I (∞ : WithTop ℕ∞) (Φ : M' → N') K)
    (hc0F : ∀ x ∈ K, metricTensorErrorNorm (I := I) hpbF.pullback g x ≤ eps)
    (hcovF : ∀ a : ℕ, 1 ≤ a → a ≤ p → ∀ x ∈ K,
      tensor02CovDerivNormWith (I := I) a hpbF.pullback g g x ≤ eps)
    (hpbR : PullbackMetricTensorData (I := I) (Φ.symm : N' → M') g)
    (hsmoothR : ContMDiffOn I I (∞ : WithTop ℕ∞) (Φ.symm : N' → M') ((Φ : M' → N') '' K))
    (hc0R : ∀ y ∈ (Φ : M' → N') '' K,
      metricTensorErrorNorm (I := I) hpbR.pullback h y ≤ eps)
    (hcovR : ∀ a : ℕ, 1 ≤ a → a ≤ p → ∀ y ∈ (Φ : M' → N') '' K,
      tensor02CovDerivNormWith (I := I) a hpbR.pullback h h y ≤ eps) :
    PartialDiffeomorphMetricApproximation (I := I) K eps p Φ g h where
  source_sub := hsub
  forward := mapMetricApproximationOnOfBounds K eps p (Φ : M' → N') g h hpbF heps heps1 hsmoothF hc0F
    hcovF
  reverse := mapMetricApproximationOnOfBounds ((Φ : M' → N') '' K) eps p (Φ.symm : N' → M') h g
    hpbR heps heps1 hsmoothR hc0R hcovR

def partialDiffeomorphMetricApproximationOfZeroOrderBounds
    {N' : Type u} [TopologicalSpace N'] [ChartedSpace H N'] [IsManifold I ∞ N']
    [T2Space N'] (K : Set M') (eps : ℝ)
    (Φ : PartialDiffeomorph I I M' N' (∞ : WithTop ℕ∞))
    (g : SmoothRiemannianMetric I M') (h : SmoothRiemannianMetric I N')
    (hsub : K ⊆ Φ.source)
    (heps : 0 < eps) (heps1 : eps < 1)
    (hpbF : PullbackMetricTensorData (I := I) (Φ : M' → N') h)
    (hsmoothF : ContMDiffOn I I (∞ : WithTop ℕ∞) (Φ : M' → N') K)
    (hc0F : ∀ x ∈ K, metricTensorErrorNorm (I := I) hpbF.pullback g x ≤ eps)
    (hpbR : PullbackMetricTensorData (I := I) (Φ.symm : N' → M') g)
    (hsmoothR : ContMDiffOn I I (∞ : WithTop ℕ∞) (Φ.symm : N' → M') ((Φ : M' → N') '' K))
    (hc0R : ∀ y ∈ (Φ : M' → N') '' K,
      metricTensorErrorNorm (I := I) hpbR.pullback h y ≤ eps) :
    PartialDiffeomorphMetricApproximation (I := I) K eps 0 Φ g h where
  source_sub := hsub
  forward := mapMetricApproximationOnOfZeroOrderBounds K eps (Φ : M' → N') g h
    hpbF heps heps1 hsmoothF hc0F
  reverse := mapMetricApproximationOnOfZeroOrderBounds ((Φ : M' → N') '' K) eps
    (Φ.symm : N' → M') h g hpbR heps heps1 hsmoothR hc0R

end CmDiag

section

open Set Manifold

variable {M'' : Type u} [TopologicalSpace M''] [ChartedSpace H M''] [IsManifold I ∞ M'']
  [T2Space M''] [T2Space (TangentBundle I M'')] [SigmaCompactSpace M'']
  [ConnectedSpace M''] [T3Space M'']
  [MetricSpace M''] [Nonempty M'']
variable {N'' : Type u} [TopologicalSpace N''] [ChartedSpace H N'']
  [nManifold : IsManifold I ∞ N'']
  [T2Space N''] [T2Space (TangentBundle I N'')] [SigmaCompactSpace N'']
  [ConnectedSpace N''] [T3Space N'']

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space (TangentBundle I M'')] [SigmaCompactSpace M''] [ConnectedSpace M''] [T3Space M'']
  [T2Space (TangentBundle I N'')] [SigmaCompactSpace N''] [ConnectedSpace N''] [T3Space N''] in
theorem exists_partial_diffeomorph_metric_approximation_of_bounds
    (g : SmoothRiemannianMetric I M'') (h : SmoothRiemannianMetric I N'')
    (Ok : M'') (Oℓ : N'') (r ε : ℝ) (p : ℕ) (U : Set M'')
    (hU : IsOpen U) (hOkU : Ok ∈ U) (hKU : Metric.closedBall Ok r ⊆ U)
    (F : M'' → N'')
    (hloc : IsLocalDiffeomorphOn I I (∞ : WithTop ℕ∞) F U)
    (hinj : Set.InjOn F U) (hbase : F Ok = Oℓ)
    (heps : 0 < ε) (heps1 : ε < 1)
    (hpbF : PullbackMetricTensorData (I := I) F h)
    (hsmoothF : ContMDiffOn I I (∞ : WithTop ℕ∞) F (Metric.closedBall Ok r))
    (hc0F : ∀ x ∈ Metric.closedBall Ok r,
      metricTensorErrorNorm (I := I) hpbF.pullback g x ≤ ε)
    (hcovF : ∀ a : ℕ, 1 ≤ a → a ≤ p → ∀ x ∈ Metric.closedBall Ok r,
      tensor02CovDerivNormWith (I := I) a hpbF.pullback g g x ≤ ε)
    (hpbR : PullbackMetricTensorData (I := I) (Function.invFunOn F U) g)
    (hsmoothR : ContMDiffOn I I (∞ : WithTop ℕ∞) (Function.invFunOn F U)
      (F '' Metric.closedBall Ok r))
    (hc0R : ∀ y ∈ F '' Metric.closedBall Ok r,
      metricTensorErrorNorm (I := I) hpbR.pullback h y ≤ ε)
    (hcovR : ∀ a : ℕ, 1 ≤ a → a ≤ p → ∀ y ∈ F '' Metric.closedBall Ok r,
      tensor02CovDerivNormWith (I := I) a hpbR.pullback h h y ≤ ε) :
    ∃ Phi : PartialDiffeomorph I I M'' N'' (∞ : WithTop ℕ∞),
      Metric.closedBall Ok r ⊆ Phi.source ∧
      Phi Ok = Oℓ ∧
      Nonempty (PartialDiffeomorphMetricApproximation (I := I) (Metric.closedBall Ok r) ε p Phi g h) := by
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) N'' := by
    change IsManifold I ∞ N''
    exact nManifold
  exact
    exists_partial_diffeomorph_metric_approximation g h Ok Oℓ r ε p U hU hOkU hKU F hloc
      hinj hbase
      (mapMetricApproximationOnOfBounds (Metric.closedBall Ok r) ε p F g h hpbF heps heps1
        hsmoothF hc0F hcovF)
      (mapMetricApproximationOnOfBounds (F '' Metric.closedBall Ok r) ε p
        (Function.invFunOn F U) h g hpbR heps heps1 hsmoothR hc0R hcovR)

omit [Module.Finite ℝ E] in
omit [T2Space (TangentBundle I M'')] [ConnectedSpace M''] [T3Space M'']
    [T2Space (TangentBundle I N'')] [ConnectedSpace N''] [T3Space N''] in
omit [FiniteDimensional ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space (TangentBundle I M'')] [SigmaCompactSpace M''] [ConnectedSpace M''] [T3Space M''] [T2Space (TangentBundle I N'')] [SigmaCompactSpace N''] [ConnectedSpace N''] [T3Space N''] in
theorem exists_partial_diffeomorph_metric_approximation_of_zero_order_bounds
    [Module.Finite ℝ E]
    (g : SmoothRiemannianMetric I M'') (h : SmoothRiemannianMetric I N'')
    (Ok : M'') (Oℓ : N'') (r ε : ℝ) (U : Set M'')
    (hU : IsOpen U) (hOkU : Ok ∈ U) (hKU : Metric.closedBall Ok r ⊆ U)
    (F : M'' → N'')
    (hloc : IsLocalDiffeomorphOn I I (∞ : WithTop ℕ∞) F U)
    (hinj : Set.InjOn F U) (hbase : F Ok = Oℓ)
    (heps : 0 < ε) (heps1 : ε < 1)
    (hpbF : PullbackMetricTensorData (I := I) F h)
    (hsmoothF : ContMDiffOn I I (∞ : WithTop ℕ∞) F (Metric.closedBall Ok r))
    (hc0F : ∀ x ∈ Metric.closedBall Ok r,
      metricTensorErrorNorm (I := I) hpbF.pullback g x ≤ ε)
    (hpbR : PullbackMetricTensorData (I := I) (Function.invFunOn F U) g)
    (hsmoothR : ContMDiffOn I I (∞ : WithTop ℕ∞) (Function.invFunOn F U)
      (F '' Metric.closedBall Ok r))
    (hc0R : ∀ y ∈ F '' Metric.closedBall Ok r,
      metricTensorErrorNorm (I := I) hpbR.pullback h y ≤ ε) :
    ∃ Phi : PartialDiffeomorph I I M'' N'' (∞ : WithTop ℕ∞),
      Metric.closedBall Ok r ⊆ Phi.source ∧
      Phi Ok = Oℓ ∧
      Nonempty (PartialDiffeomorphMetricApproximation (I := I) (Metric.closedBall Ok r) ε 0 Phi g h) :=
  exists_partial_diffeomorph_metric_approximation_of_bounds g h Ok Oℓ r ε 0 U hU hOkU hKU F hloc hinj hbase heps heps1
    hpbF hsmoothF hc0F (by intro a ha ha0 x hx; omega)
    hpbR hsmoothR hc0R (by intro a ha ha0 y hy; omega)

end

end HCGCompactness
end DifferentialGeometry
