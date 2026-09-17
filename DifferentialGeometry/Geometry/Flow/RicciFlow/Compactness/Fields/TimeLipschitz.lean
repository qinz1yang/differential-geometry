import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.MetricExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Endpoint.TimeLipschitz

section

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold TopologicalSpace
open scoped Manifold Topology ContDiff BigOperators


namespace DifferentialGeometry
namespace CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

section ConvergenceField

variable {X : PointedFlowSeq (I := I)}
variable {P : PointedRiemannianManifold (I := I)}
variable {subseq : Nat -> Nat}
variable (Φ : PointedCGHMaps (I := I) X P subseq)

open DifferentialGeometry.Tensor0SBundle in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem exists_metric_extension_time_lipschitz_constant
    (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    (times : Set ℝ) (k : ℕ)
    (hlipSource : letI : TopologicalSpace P.M := P.topology;
        letI : ChartedSpace H P.M := P.charted; letI : T2Space P.M := P.t2;
        letI : IsManifold I ∞ P.M := P.smooth; letI : SigmaCompactSpace P.M := P.sigmaCompact;
        letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
        letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
        letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
        letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
        letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
          sourceDomSigmaOf (I := I) Φ k (hsrc k)
        letI : SigmaCompactSpace ↥(sourceOpen (I := I) Φ k) :=
          sourceDomSigmaOf (I := I) Φ k (hsrc k)
        letI : T2Space ↥(sourceOpen (I := I) Φ k) := sourceDomT2 (I := I) Φ k
        forall C : Set (SourceDomain (I := I) Φ k), IsCompact C -> forall p : Nat,
          exists Ls : Real, 0 <= Ls /\
            forall (s t : Real), s ∈ times -> t ∈ times ->
              forall b : Nat, b <= p -> forall y : SourceDomain (I := I) Φ k, y ∈ C ->
                metricDerivNorm (I := I) b (sourceMetric (I := I) Φ hsrc htgt k s)
                  (sourceMetric (I := I) Φ hsrc htgt k t)
                  (sourceMetricRestriction (I := I) Φ R k) y <= Ls * |s - t|) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    forall K' : Set P.M, IsCompact K' -> forall p : Nat,
      exists Lk : Real, 0 <= Lk /\
        forall s, s ∈ times -> forall t, t ∈ times ->
          forall a : Nat, a <= p -> forall x, x ∈ K' ->
            metricDerivNorm (I := I) a (gSeqExt (I := I) Φ R bf hsrc htgt k s)
              (gSeqExt (I := I) Φ R bf hsrc htgt k t) R x <= Lk * |s - t| := by
  classical
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  intro K' hK' p
  let : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  let : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  let : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  let : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  let : SigmaCompactSpace (SourceDomain (I := I) Φ k) := sourceDomSigmaOf (I := I) Φ k (hsrc k)
  let : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) <= ∞)
  let : IsManifold I 2 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
      (by decide : (2 : WithTop ℕ∞) <= ∞)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) (SourceDomain (I := I) Φ k) := by
    change IsManifold I ∞ (SourceDomain (I := I) Φ k); infer_instance
  let : SigmaCompactSpace ↥(sourceOpen (I := I) Φ k) := sourceDomSigmaOf (I := I) Φ k (hsrc k)
  let : T2Space ↥(sourceOpen (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  let : IsManifold I ∞ ↥(sourceOpen (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  let : IsManifold I 1 ↥(sourceOpen (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := ↥(sourceOpen (I := I) Φ k)) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) <= ∞)
  let : IsManifold I 2 ↥(sourceOpen (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := ↥(sourceOpen (I := I) Φ k)) (n := (∞ : WithTop ℕ∞))
      (by decide : (2 : WithTop ℕ∞) <= ∞)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) ↥(sourceOpen (I := I) Φ k) := by
    change IsManifold I ∞ (SourceDomain (I := I) Φ k); infer_instance
  have hKTc : IsCompact (K' ∩ tsupport (bf.chi k)) :=
    hK'.inter_right (isClosed_tsupport (bf.chi k))
  have hKTsub : K' ∩ tsupport (bf.chi k) ⊆ Φ.source k := fun z hz => bf.chi_support k hz.2
  have hCc : IsCompact (sourceCompactSet (I := I) Φ k (K' ∩ tsupport (bf.chi k))) :=
    sourceCompactSet_isCompact (I := I) Φ k hKTc hKTsub
  obtain ⟨Ls, hLs0, hLs⟩ :=
    hlipSource (sourceCompactSet (I := I) Φ k (K' ∩ tsupport (bf.chi k))) hCc p
  set χ' : SourceDomain (I := I) Φ k -> Real :=
    fun y => bf.chi k (y : P.M) with hχ'def
  have hχ' : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ' :=
    (bf.chi_smooth k).comp (contMDiff_subtype_val (I := I) (U := sourceOpen (I := I) Φ k))
  have hχB : forall c : Nat, exists Cc : Real, 0 <= Cc /\
      forall y, y ∈ sourceCompactSet (I := I) Φ k (K' ∩ tsupport (bf.chi k)) ->
        Real.sqrt (normSq0S (I := I)
          (sourceMetricRestriction (I := I) Φ R k) y (0 + c)
          (iterCov (I := I) (sourceMetricRestriction (I := I) Φ R k) 0
            (Tensor0SField.fromScalarField (𝕜 := Real) (E := E) (H := H) (I := I)
              (M := SourceDomain (I := I) Φ k) (∞ : WithTop ℕ∞) χ' hχ') c y)) <= Cc :=
    fun c => sqrtNormSq0S_bddOn (I := I) hCc (0 + c)
      (sourceMetricRestriction (I := I) Φ R k)
      (iterCov (I := I) (sourceMetricRestriction (I := I) Φ R k) 0
        (Tensor0SField.fromScalarField (𝕜 := Real) (E := E) (H := H) (I := I)
          (M := SourceDomain (I := I) Φ k) (∞ : WithTop ℕ∞) χ' hχ') c)
  choose Cχ hCχ0 hCχ using hχB
  have hrange : (Finset.range (p + 1)).Nonempty := ⟨0, Finset.mem_range.2 (Nat.succ_pos p)⟩
  set Cx : Real := (Finset.range (p + 1)).sup' hrange Cχ with hCxdef
  have hCx0 : 0 <= Cx :=
    le_trans (hCχ0 0) (Finset.le_sup' Cχ (Finset.mem_range.2 (Nat.succ_pos p)))
  have hCxge : forall c : Nat, c <= p -> Cχ c <= Cx := fun c hc =>
    Finset.le_sup' Cχ (Finset.mem_range.2 (Nat.lt_succ_of_le hc))
  refine ⟨2 ^ p * Cx * Ls,
    mul_nonneg (mul_nonneg (by positivity) hCx0) hLs0, fun s hs t ht a ha x hx => ?_⟩
  by_cases hxsupp : x ∈ tsupport (bf.chi k)
  · have hxU : x ∈ Φ.source k := bf.chi_support k hxsupp
    have hyC : (⟨x, hxU⟩ : SourceDomain (I := I) Φ k) ∈
        sourceCompactSet (I := I) Φ k (K' ∩ tsupport (bf.chi k)) := ⟨hx, hxsupp⟩
    obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I)
      (sourceMetricRestriction (I := I) Φ R k)
      (⟨x, hxU⟩ : SourceDomain (I := I) Φ k)
    have hinv : MetricInverseInBasis (I := I)
        (sourceMetricRestriction (I := I) Φ R k)
        (⟨x, hxU⟩ : SourceDomain (I := I) Φ k) basis
        (identityInvMetric (Idx := Fin (Module.finrank Real
          (TangentSpace I (⟨x, hxU⟩ : SourceDomain (I := I) Φ k))))) := by
      have h' := DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I)
        (sourceMetricRestriction (I := I) Φ R k) basis hON
      intro i j
      simpa [identityInvMetric, diagonalInvMetric] using h' i j
    have hsmul : metricTensorField (I := I)
          ((gSeqExt (I := I) Φ R bf hsrc htgt k s).restrictOpen (I := I)
            (sourceOpen (I := I) Φ k))
        - metricTensorField (I := I)
          ((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I)
            (sourceOpen (I := I) Φ k))
        = tensor0SFieldSmulByFun (𝕜 := Real) (E := E) (H := H) (I := I)
            (M := SourceDomain (I := I) Φ k) (∞ : WithTop ℕ∞) χ' hχ'
            (metricTensorField (I := I) (sourceMetric (I := I) Φ hsrc htgt k s)
              - metricTensorField (I := I) (sourceMetric (I := I) Φ hsrc htgt k t)) := by
      refine DFunLike.ext _ _ (fun y => ?_)
      refine ContinuousMultilinearMap.ext (fun v => ?_)
      change (metricTensorField (I := I)
            ((gSeqExt (I := I) Φ R bf hsrc htgt k s).restrictOpen (I := I)
              (sourceOpen (I := I) Φ k)) y
          - metricTensorField (I := I)
            ((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I)
              (sourceOpen (I := I) Φ k)) y) v
        = (χ' y • (metricTensorField (I := I) (sourceMetric (I := I) Φ hsrc htgt k s) y
            - metricTensorField (I := I) (sourceMetric (I := I) Φ hsrc htgt k t) y)) v
      rw [sub_apply, smul_apply,
        sub_apply]
      rw [metricTensorField_apply, metricTensorField_apply,
        metricTensorField_apply, metricTensorField_apply]
      rw [SmoothRiemannianMetric.restrictOpen_inner,
        SmoothRiemannianMetric.restrictOpen_inner]
      rw [gSeqExt_inner_of_mem (I := I) Φ R bf hsrc htgt k s (y : P.M) y.2 (v 0) (v 1),
        gSeqExt_inner_of_mem (I := I) Φ R bf hsrc htgt k t (y : P.M) y.2 (v 0) (v 1)]
      simp only [hχ'def, smul_eq_mul]
      ring
    have hres : metricDerivNorm (I := I) a
          ((gSeqExt (I := I) Φ R bf hsrc htgt k s).restrictOpen (I := I)
            (sourceOpen (I := I) Φ k))
          ((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I)
            (sourceOpen (I := I) Φ k))
          (sourceMetricRestriction (I := I) Φ R k)
          (⟨x, hxU⟩ : SourceDomain (I := I) Φ k)
        = metricDerivNorm (I := I) a (gSeqExt (I := I) Φ R bf hsrc htgt k s)
          (gSeqExt (I := I) Φ R bf hsrc htgt k t) R x :=
      metricDerivNorm_restrictOpen (I := I) _ _ _ (sourceOpen (I := I) Φ k) a ⟨x, hxU⟩
    rw [← hres,
      metricDerivNorm_eq_iterCov (I := I)
        ((gSeqExt (I := I) Φ R bf hsrc htgt k s).restrictOpen (I := I)
          (sourceOpen (I := I) Φ k))
        ((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I)
          (sourceOpen (I := I) Φ k))
        (sourceMetricRestriction (I := I) Φ R k) a basis hinv,
      hsmul]
    refine le_trans (iterCov_smulF_le (I := I)
      (sourceMetricRestriction (I := I) Φ R k)
      (⟨x, hxU⟩ : SourceDomain (I := I) Φ k) basis hinv a χ' hχ'
      (metricTensorField (I := I) (sourceMetric (I := I) Φ hsrc htgt k s)
        - metricTensorField (I := I) (sourceMetric (I := I) Φ hsrc htgt k t))) ?_
    have hterm : forall c : Nat, c ∈ Finset.range (a + 1) ->
        (a.choose c : Real) *
          Real.sqrt (normSq0S (I := I)
            (sourceMetricRestriction (I := I) Φ R k) (⟨x, hxU⟩ :
              SourceDomain (I := I) Φ k) (0 + c)
            (iterCov (I := I) (sourceMetricRestriction (I := I) Φ R k) 0
              (Tensor0SField.fromScalarField (𝕜 := Real) (E := E) (H := H) (I := I)
                (M := SourceDomain (I := I) Φ k) (∞ : WithTop ℕ∞) χ' hχ') c ⟨x, hxU⟩)) *
          Real.sqrt (normSq0S (I := I)
            (sourceMetricRestriction (I := I) Φ R k) (⟨x, hxU⟩ :
              SourceDomain (I := I) Φ k) (2 + (a - c))
            (iterCov (I := I) (sourceMetricRestriction (I := I) Φ R k) 2
              (metricTensorField (I := I) (sourceMetric (I := I) Φ hsrc htgt k s)
                - metricTensorField (I := I) (sourceMetric (I := I) Φ hsrc htgt k t))
              (a - c) ⟨x, hxU⟩))
        <= (a.choose c : Real) * Cx * (Ls * |s - t|) := by
      intro c hc
      have hcp : c <= p := le_trans (Nat.le_of_lt_succ (Finset.mem_range.1 hc)) ha
      have hχle : Real.sqrt (normSq0S (I := I)
          (sourceMetricRestriction (I := I) Φ R k) (⟨x, hxU⟩ :
            SourceDomain (I := I) Φ k) (0 + c)
          (iterCov (I := I) (sourceMetricRestriction (I := I) Φ R k) 0
            (Tensor0SField.fromScalarField (𝕜 := Real) (E := E) (H := H) (I := I)
              (M := SourceDomain (I := I) Φ k) (∞ : WithTop ℕ∞) χ' hχ') c ⟨x, hxU⟩))
          <= Cx := le_trans (hCχ c ⟨x, hxU⟩ hyC) (hCxge c hcp)
      have hsle : Real.sqrt (normSq0S (I := I)
          (sourceMetricRestriction (I := I) Φ R k) (⟨x, hxU⟩ :
            SourceDomain (I := I) Φ k) (2 + (a - c))
          (iterCov (I := I) (sourceMetricRestriction (I := I) Φ R k) 2
            (metricTensorField (I := I) (sourceMetric (I := I) Φ hsrc htgt k s)
              - metricTensorField (I := I) (sourceMetric (I := I) Φ hsrc htgt k t))
            (a - c) ⟨x, hxU⟩)) <= Ls * |s - t| := by
        rw [← metricDerivNorm_eq_iterCov (I := I) (sourceMetric (I := I) Φ hsrc htgt k s)
          (sourceMetric (I := I) Φ hsrc htgt k t)
          (sourceMetricRestriction (I := I) Φ R k) (a - c) basis hinv]
        exact hLs s t hs ht (a - c) (le_trans (Nat.sub_le a c) ha) ⟨x, hxU⟩ hyC
      calc (a.choose c : Real) *
            Real.sqrt (normSq0S (I := I)
              (sourceMetricRestriction (I := I) Φ R k) (⟨x, hxU⟩ :
                SourceDomain (I := I) Φ k) (0 + c)
              (iterCov (I := I) (sourceMetricRestriction (I := I) Φ R k) 0
                (Tensor0SField.fromScalarField (𝕜 := Real) (E := E) (H := H) (I := I)
                  (M := SourceDomain (I := I) Φ k) (∞ : WithTop ℕ∞) χ' hχ') c ⟨x, hxU⟩)) *
            Real.sqrt (normSq0S (I := I)
              (sourceMetricRestriction (I := I) Φ R k) (⟨x, hxU⟩ :
                SourceDomain (I := I) Φ k) (2 + (a - c))
              (iterCov (I := I) (sourceMetricRestriction (I := I) Φ R k) 2
                (metricTensorField (I := I) (sourceMetric (I := I) Φ hsrc htgt k s)
                  - metricTensorField (I := I) (sourceMetric (I := I) Φ hsrc htgt k t))
                (a - c) ⟨x, hxU⟩))
          <= (a.choose c : Real) * Cx *
            Real.sqrt (normSq0S (I := I)
              (sourceMetricRestriction (I := I) Φ R k) (⟨x, hxU⟩ :
                SourceDomain (I := I) Φ k) (2 + (a - c))
              (iterCov (I := I) (sourceMetricRestriction (I := I) Φ R k) 2
                (metricTensorField (I := I) (sourceMetric (I := I) Φ hsrc htgt k s)
                  - metricTensorField (I := I) (sourceMetric (I := I) Φ hsrc htgt k t))
                (a - c) ⟨x, hxU⟩)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hχle (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)
        _ <= (a.choose c : Real) * Cx * (Ls * |s - t|) :=
            mul_le_mul_of_nonneg_left hsle (mul_nonneg (Nat.cast_nonneg _) hCx0)
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have hsum : (∑ c ∈ Finset.range (a + 1), (a.choose c : Real) * Cx * (Ls * |s - t|))
        = (2 : Real) ^ a * Cx * (Ls * |s - t|) := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      push_cast
      ring
    rw [hsum]
    have h2 : (2 : Real) ^ a <= (2 : Real) ^ p := by
      exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 <= 2) ha
    have hnn : 0 <= Cx * (Ls * |s - t|) :=
      mul_nonneg hCx0 (mul_nonneg hLs0 (abs_nonneg _))
    calc (2 : Real) ^ a * Cx * (Ls * |s - t|)
        = (2 : Real) ^ a * (Cx * (Ls * |s - t|)) := by ring
      _ <= (2 : Real) ^ p * (Cx * (Ls * |s - t|)) := mul_le_mul_of_nonneg_right h2 hnn
      _ = 2 ^ p * Cx * Ls * |s - t| := by ring
  · set U₀ : TopologicalSpace.Opens P.M :=
      ⟨(tsupport (bf.chi k))ᶜ, (isClosed_tsupport (bf.chi k)).isOpen_compl⟩ with hU₀def
    let : ChartedSpace H ↥U₀ :=
      TopologicalSpace.Opens.instChartedSpace (H := H) (M := P.M) (s := U₀)
    let : IsManifold I ∞ ↥U₀ := { U₀.instHasGroupoid (contDiffGroupoid ∞ I) with }
    let : SigmaCompactSpace ↥U₀ := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U₀.isOpen)
    let : IsManifold I 1 ↥U₀ :=
      IsManifold.of_le (I := I) (M := ↥U₀) (n := (∞ : WithTop ℕ∞))
        (by decide : (1 : WithTop ℕ∞) <= ∞)
    let : IsManifold I 2 ↥U₀ :=
      IsManifold.of_le (I := I) (M := ↥U₀) (n := (∞ : WithTop ℕ∞))
        (by decide : (2 : WithTop ℕ∞) <= ∞)
    let : IsManifold I ((∞ : WithTop ℕ∞) + 1) ↥U₀ := by
      change IsManifold I ∞ ↥U₀; infer_instance
    have hx0 : x ∈ U₀ := hxsupp
    have hres : metricDerivNorm (I := I) a
          ((gSeqExt (I := I) Φ R bf hsrc htgt k s).restrictOpen (I := I) U₀)
          ((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I) U₀)
          (R.restrictOpen (I := I) U₀) (⟨x, hx0⟩ : ↥U₀)
        = metricDerivNorm (I := I) a (gSeqExt (I := I) Φ R bf hsrc htgt k s)
          (gSeqExt (I := I) Φ R bf hsrc htgt k t) R x :=
      metricDerivNorm_restrictOpen (I := I) _ _ _ U₀ a ⟨x, hx0⟩
    have hmTF : metricTensorField (I := I)
          ((gSeqExt (I := I) Φ R bf hsrc htgt k s).restrictOpen (I := I) U₀)
        = metricTensorField (I := I)
          ((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I) U₀) := by
      refine DFunLike.ext _ _ (fun y => ?_)
      refine ContinuousMultilinearMap.ext (fun v => ?_)
      calc
        metricTensorField (I := I)
            ((gSeqExt (I := I) Φ R bf hsrc htgt k s).restrictOpen (I := I) U₀) y v =
          ((gSeqExt (I := I) Φ R bf hsrc htgt k s).restrictOpen (I := I) U₀).inner
            y (v 0) (v 1) := metricTensorField_apply _ _ _
        _ = (gSeqExt (I := I) Φ R bf hsrc htgt k s).inner
            (y : P.M) (v 0) (v 1) := by
          rw [SmoothRiemannianMetric.restrictOpen_inner]
        _ = R.inner (y : P.M) (v 0) (v 1) :=
          gSeqExt_inner_of_notMem (I := I) Φ R bf hsrc htgt k s
            (y : P.M) y.2 (v 0) (v 1)
        _ = (gSeqExt (I := I) Φ R bf hsrc htgt k t).inner
            (y : P.M) (v 0) (v 1) :=
          (gSeqExt_inner_of_notMem (I := I) Φ R bf hsrc htgt k t
            (y : P.M) y.2 (v 0) (v 1)).symm
        _ = ((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I) U₀).inner
            y (v 0) (v 1) := by
          rw [SmoothRiemannianMetric.restrictOpen_inner]
        _ = metricTensorField (I := I)
            ((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I) U₀) y v :=
          (metricTensorField_apply _ _ _).symm
    have hswap : metricDerivNorm (I := I) a
          ((gSeqExt (I := I) Φ R bf hsrc htgt k s).restrictOpen (I := I) U₀)
          ((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I) U₀)
          (R.restrictOpen (I := I) U₀) (⟨x, hx0⟩ : ↥U₀)
        = metricDerivNorm (I := I) a
          ((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I) U₀)
          ((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I) U₀)
          (R.restrictOpen (I := I) U₀) (⟨x, hx0⟩ : ↥U₀) := by
      unfold metricDerivNorm metricDiffCovDerivAt
      rw [metricCovDeriv_eq_covDerivOfField (I := I)
          ((gSeqExt (I := I) Φ R bf hsrc htgt k s).restrictOpen (I := I) U₀)
          (R.restrictOpen (I := I) U₀) a,
        metricCovDeriv_eq_covDerivOfField (I := I)
          ((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I) U₀)
          (R.restrictOpen (I := I) U₀) a,
        hmTF]
    rw [← hres, hswap, metricDerivNorm_self]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hCx0) hLs0) (abs_nonneg _)


end ConvergenceField
end CheegerGromovCompactness
end DifferentialGeometry

end

end

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem exists_metric_extension_time_lipschitz_constant_on_closed_interval
    {X : PointedFlowSeq (I := I)} {P : PointedRiemannianManifold (I := I)}
    {subseq : ℕ → ℕ} (Φ : PointedCGHMaps (I := I) X P subseq)
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    {a b : ℝ} (hab : a < b) (hslab : Icc a b ⊆ X.D.carrier)
    (hregular : Ico a b ⊆ X.D.regular) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    ∀ i : ℕ, ∀ K : Set P.M, IsCompact K → ∀ p : ℕ,
      ∃ L : ℝ, 0 ≤ L ∧ ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ q ≤ p, ∀ x ∈ K,
        metricDerivNorm q (gSeqExt Φ R bf hsrc htgt i s)
          (gSeqExt Φ R bf hsrc htgt i t) R x ≤ L * |s - t| := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  intro i
  apply exists_metric_extension_time_lipschitz_constant Φ R bf hsrc htgt (Icc a b) i
  let : TopologicalSpace (SourceDomain Φ i) := sourceDomTop Φ i
  let : ChartedSpace H (SourceDomain Φ i) := sourceDomCharted Φ i
  let : T2Space (SourceDomain Φ i) := sourceDomT2 Φ i
  let : IsManifold I ∞ (SourceDomain Φ i) := sourceDomSmooth Φ i
  let : SigmaCompactSpace (SourceDomain Φ i) := sourceDomSigmaOf Φ i (hsrc i)
  let : SigmaCompactSpace ↥(sourceOpen Φ i) := sourceDomSigmaOf Φ i (hsrc i)
  let : T2Space ↥(sourceOpen Φ i) := sourceDomT2 Φ i
  let : IsManifold I 1 (SourceDomain Φ i) := IsManifold.of_le (n := ∞) (by decide)
  let : IsManifold I (∞ + 1) (SourceDomain Φ i) := by
    change IsManifold I ∞ (SourceDomain Φ i)
    infer_instance
  intro C hC p
  obtain ⟨L, hL, hlip⟩ := exists_metric_time_lipschitz_constant_on_compact_of_solution
    (sourceFlow Φ i (hsrc i) (htgt i))
    (isSolutionOn_sourceFlow Φ i (hsrc i) (htgt i))
    hab hslab hregular (sourceMetricRestriction Φ R i) hC p
  exact ⟨L, hL, fun s t hs ht q hq y hy => hlip q hq s hs t ht y hy⟩

end DifferentialGeometry.CheegerGromovCompactness

end
