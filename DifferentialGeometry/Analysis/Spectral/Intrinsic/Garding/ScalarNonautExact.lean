import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.MetricLapDiffSpan
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ScalarNonautCompat
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ScalarNonautHs
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ScalarNonautTime

/-!
# Exact-interval scalar nonautonomous Sobolev operators

This file packages the all-scale scalar Laplacian-difference estimates on a
caller-supplied reflected regular interval.  It does not choose or shorten a
time interval.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- On any prescribed reflected regular interval, every natural-order
Laplacian difference has an operator-norm bound uniform in time. -/
theorem lapHs_norm_on
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) {tau : ℝ}
    (hreg : ∀ s ∈ Set.Icc (0 : ℝ) tau, (T : ℝ) - s ∈ D.regular) :
    ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ s ∈ Set.Icc (0 : ℝ) tau,
        ‖lapDiffHs (I := I) (M := M) (G.metric (T : ℝ))
          (G.metric ((T : ℝ) - s)) m‖ ≤ C := by
  classical
  let q : SmoothRiemannianMetric I M := G.metric (T : ℝ)
  let K : Set ℝ := Set.Icc (0 : ℝ) tau
  let Φ₂ : ℝ → SmoothCcTensor q 2 0 := fun s =>
    scalarTraceCoeff (I := I) q (G.metric ((T : ℝ) - s))
  let Φ₁ : ℝ → SmoothCcTensor q 1 0 := fun s =>
    connTraceCoeff (I := I) q (G.metric ((T : ℝ) - s))
  have hback : K ⊆ {s : ℝ | (T : ℝ) - s ∈ D.regular} := by
    intro s hs
    exact hreg s (by simpa only [K] using hs)
  obtain ⟨B₂, hB₂, hΦ₂⟩ :=
    joint_jet_bdd (I := I) (M := M) q 2 0 Φ₂
      (S := K) (K := K) isCompact_Icc Set.Subset.rfl
      (by
        simpa only [Φ₂, K] using
          scalarTrace_rev_on (I := I) (M := M) G hG q (T : ℝ) hback)
  obtain ⟨B₁, hB₁, hΦ₁⟩ :=
    joint_jet_bdd (I := I) (M := M) q 1 0 Φ₁
      (S := K) (K := K) isCompact_Icc Set.Subset.rfl
      (by
        simpa only [Φ₁, K] using
          connTrace_rev_on (I := I) (M := M) G hG q (T : ℝ) hback)
  intro m
  obtain ⟨A₂, hA₂, hApp₂⟩ := appHs_unif (I := I) (M := M) q 2 0 m
  obtain ⟨A₁, hA₁, hApp₁⟩ := appHs_unif (I := I) (M := M) q 1 0 m
  let C₂ : ℝ := A₂ * Real.sqrt (∑ i ∈ Finset.range (m + 1), B₂ i)
  let C₁ : ℝ := A₁ * Real.sqrt (∑ i ∈ Finset.range (m + 1), B₁ i)
  let D₂ := iterCovGradHs (I := I) (M := M) q 0 2 m
  let J := tensorHsInclusion (I := I) (M := M)
    (g := q) (r := 0) (s := 0)
    (by norm_num : (m : ℝ) + ((1 : ℕ) : ℝ) ≤ (m : ℝ) + 2)
  let D₁ := (iterCovGradHs (I := I) (M := M) q 0 1 m).comp J
  let C : ℝ := C₂ * ‖D₂‖ + C₁ * ‖D₁‖
  have hC₂ : 0 ≤ C₂ := mul_nonneg hA₂ (Real.sqrt_nonneg _)
  have hC₁ : 0 ≤ C₁ := mul_nonneg hA₁ (Real.sqrt_nonneg _)
  have hC : 0 ≤ C := by
    exact add_nonneg (mul_nonneg hC₂ (norm_nonneg D₂))
      (mul_nonneg hC₁ (norm_nonneg D₁))
  refine ⟨C, hC, ?_⟩
  intro s hs
  have hsK : s ∈ K := by simpa only [K] using hs
  have h₂ : ‖appHs q 2 0 m (Φ₂ s)‖ ≤ C₂ := by
    simpa only [C₂] using hApp₂ (Φ₂ s) B₂
      (fun i _hi => hB₂ i) (fun i _hi x => hΦ₂ i s hsK x)
  have h₁ : ‖appHs q 1 0 m (Φ₁ s)‖ ≤ C₁ := by
    simpa only [C₁] using hApp₁ (Φ₁ s) B₁
      (fun i _hi => hB₁ i) (fun i _hi x => hΦ₁ i s hsK x)
  rw [lapHs_eq (I := I) (M := M)]
  calc
    ‖(appHs q 2 0 m (scalarTraceCoeff (I := I) q
          (G.metric ((T : ℝ) - s)))).comp D₂ -
        (appHs q 1 0 m (connTraceCoeff (I := I) q
          (G.metric ((T : ℝ) - s)))).comp D₁‖ ≤
        ‖(appHs q 2 0 m (Φ₂ s)).comp D₂‖ +
          ‖(appHs q 1 0 m (Φ₁ s)).comp D₁‖ := by
            simpa only [Φ₂, Φ₁] using norm_sub_le
              ((appHs q 2 0 m (Φ₂ s)).comp D₂)
              ((appHs q 1 0 m (Φ₁ s)).comp D₁)
    _ ≤ (C₂ * ‖D₂‖) + (C₁ * ‖D₁‖) := by
      apply add_le_add
      · exact ((appHs q 2 0 m (Φ₂ s)).opNorm_comp_le D₂).trans
          (mul_le_mul_of_nonneg_right h₂ (norm_nonneg D₂))
      · exact ((appHs q 1 0 m (Φ₁ s)).opNorm_comp_le D₁).trans
          (mul_le_mul_of_nonneg_right h₁ (norm_nonneg D₁))
    _ = C := rfl

/-- If the genuine `H² → H⁰` perturbation agrees with the invariant finite
spectral core on an interval, then it is the order-zero all-scale operator
throughout that interval. -/
theorem lapHs_A20_on
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (T : D.RegularTime) {tau : ℝ}
    (hcore : ∀ s ∈ Set.Icc (0 : ℝ) tau,
      ∀ v : ScalarH2Core (I := I) (M := M) (G.metric (T : ℝ)),
        tensorHsZeroEquivL2 (I := I) (M := M)
            (tensorResolventL2_isCompactOperator
              (I := I) (M := M) (G.metric (T : ℝ)) 0 0)
            (lapDiffA20 (I := I) (M := M) G T s v.1) =
          lapDiffCore (I := I) (M := M) (G.metric (T : ℝ))
            (G.metric ((T : ℝ) - s)) v) :
    ∀ s ∈ Set.Icc (0 : ℝ) tau,
      ∀ u : tensorHs (I := I) (M := M) (G.metric (T : ℝ)) 0 0 2,
        tensorHs.castEquiv (I := I) (M := M)
            (g := G.metric (T : ℝ)) (r := 0) (s := 0)
            (by norm_num : ((0 : ℕ) : ℝ) = 0)
            (lapDiffHs (I := I) (M := M) (G.metric (T : ℝ))
              (G.metric ((T : ℝ) - s)) 0
              (tensorHs.castEquiv (I := I) (M := M)
                (g := G.metric (T : ℝ)) (r := 0) (s := 0)
                (by norm_num : (2 : ℝ) = ((0 : ℕ) : ℝ) + 2) u)) =
          lapDiffA20 (I := I) (M := M) G T s u := by
  classical
  intro s hs u
  let q : SmoothRiemannianMetric I M := G.metric (T : ℝ)
  let h : SmoothRiemannianMetric I M := G.metric ((T : ℝ) - s)
  let J : tensorHs (I := I) (M := M) q 0 0 2 →L[ℝ]
      tensorHs (I := I) (M := M) q 0 0 (((0 : ℕ) : ℝ) + 2) :=
    (tensorHs.castEquiv (I := I) (M := M)
      (g := q) (r := 0) (s := 0)
      (by norm_num : (2 : ℝ) = ((0 : ℕ) : ℝ) + 2)).toContinuousLinearEquiv.toContinuousLinearMap
  let K : tensorHs (I := I) (M := M) q 0 0 ((0 : ℕ) : ℝ) →L[ℝ]
      tensorHs (I := I) (M := M) q 0 0 0 :=
    (tensorHs.castEquiv (I := I) (M := M)
      (g := q) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) = 0)).toContinuousLinearEquiv.toContinuousLinearMap
  let L := K.comp ((lapDiffHs (I := I) (M := M) q h 0).comp J)
  let R := lapDiffA20 (I := I) (M := M) G T s
  change L u = R u
  have hdense : DenseRange
      (ScalarH2Core (I := I) (M := M) q).subtype :=
    (tensorHsFiniteSupportSubmodule_dense
      (I := I) (M := M) (g := q) (r := 0) (s := 0) (σ := 2)).denseRange_val
  have heq :
      L ∘ (ScalarH2Core (I := I) (M := M) q).subtype =
        R ∘ (ScalarH2Core (I := I) (M := M) q).subtype := by
    funext v
    let U : SmoothCcTensor q 0 0 :=
      tensorHsSmoothRepr (I := I) (M := M) v.1 v.2
    have hrepr :
        ccTensorToHs (I := I) (M := M) q 0 2 U = v.1 := by
      simpa only [U, ccToHsLin_apply] using
        (ccToHsLin_repr (I := I) (M := M) q 0
          (show (0 : ℝ) ≤ 2 by norm_num) v.1 v.2)
    change L v.1 = R v.1
    rw [← hrepr]
    have hJ :
        J (ccTensorToHs (I := I) (M := M) q 0 2 U) =
          ccTensorToHs (I := I) (M := M) q 0 (((0 : ℕ) : ℝ) + 2) U := by
      apply tensorHs.ext
      funext i
      rfl
    rw [show L (ccTensorToHs (I := I) (M := M) q 0 2 U) =
        ccTensorToHs (I := I) (M := M) q 0 0
          (scalarLapDiffCc (I := I) q h U) by
      change K (lapDiffHs (I := I) (M := M) q h 0
          (J (ccTensorToHs (I := I) (M := M) q 0 2 U))) = _
      rw [hJ, lapHs_core (I := I) (M := M)]
      apply tensorHs.ext
      funext i
      rfl]
    apply tensorHs.ext
    funext i
    rw [ccTensorToHs_coeff]
    have hc := congrArg
      (fun Z : TensorL2 0 0 q =>
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator
            (I := I) (M := M) q 0 0) Z i)
      (hcore s hs v)
    simp only [tensorHsZeroEquivL2_tensorL2Coeff] at hc
    rw [lapDiffCore_eq_cc (I := I) (M := M)] at hc
    simpa only [R, q, h, U, hrepr] using hc.symm
  have hfun := hdense.equalizer L.continuous R.continuous heq
  exact congr_fun hfun u

/-- On any prescribed reflected regular interval, the completed Laplacian
difference preserves every finite time regularity order on the interior. -/
theorem lapHs_dyn_on
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) {tau : ℝ}
    (hreg : ∀ s ∈ Set.Icc (0 : ℝ) tau, (T : ℝ) - s ∈ D.regular)
    (m k : ℕ)
    (U : ℝ → tensorHs (I := I) (M := M) (G.metric (T : ℝ)) 0 0
      ((m : ℝ) + 2))
    (hU : ContDiffOn ℝ k U (Set.Ioo (0 : ℝ) tau)) :
    ContDiffOn ℝ k
      (fun s => lapDiffHs (I := I) (M := M) (G.metric (T : ℝ))
        (G.metric ((T : ℝ) - s)) m (U s))
      (Set.Ioo (0 : ℝ) tau) := by
  classical
  let q : SmoothRiemannianMetric I M := G.metric (T : ℝ)
  let J := tensorHsInclusion (I := I) (M := M)
    (g := q) (r := 0) (s := 0)
    (by norm_num : (m : ℝ) + ((1 : ℕ) : ℝ) ≤ (m : ℝ) + 2)
  let D₂ := iterCovGradHs (I := I) (M := M) q 0 2 m
  let D₁ := (iterCovGradHs (I := I) (M := M) q 0 1 m).comp J
  let V₂ : ℝ → tensorHs (I := I) (M := M) q 0 2 (m : ℝ) :=
    fun s => D₂ (U s)
  let V₁ : ℝ → tensorHs (I := I) (M := M) q 0 1 (m : ℝ) :=
    fun s => D₁ (U s)
  have hV₂ : ContDiffOn ℝ k V₂ (Set.Ioo (0 : ℝ) tau) := by
    simpa only [V₂, Function.comp_apply] using
      D₂.contDiff.comp_contDiffOn hU
  have hV₁ : ContDiffOn ℝ k V₁ (Set.Ioo (0 : ℝ) tau) := by
    simpa only [V₁, Function.comp_apply] using
      D₁.contDiff.comp_contDiffOn hU
  have hback : Set.Ioo (0 : ℝ) tau ⊆
      {s : ℝ | (T : ℝ) - s ∈ D.regular} := by
    intro s hs
    exact hreg s ⟨hs.1.le, hs.2.le⟩
  have h₂ := appHs_dyn_fin (I := I) (M := M) q 2 0 m k
    (fun s => scalarTraceCoeff (I := I) q (G.metric ((T : ℝ) - s)))
    isOpen_Ioo
    (scalarTrace_rev_on (I := I) (M := M) G hG q (T : ℝ) hback) V₂ hV₂
  have h₁ := appHs_dyn_fin (I := I) (M := M) q 1 0 m k
    (fun s => connTraceCoeff (I := I) q (G.metric ((T : ℝ) - s)))
    isOpen_Ioo
    (connTrace_rev_on (I := I) (M := M) G hG q (T : ℝ) hback) V₁ hV₁
  refine (h₂.sub h₁).congr ?_
  intro s _hs
  rw [lapHs_eq (I := I) (M := M)]
  rfl

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
