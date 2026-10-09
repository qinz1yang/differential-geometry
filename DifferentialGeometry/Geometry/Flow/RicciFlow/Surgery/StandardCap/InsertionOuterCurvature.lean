import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InsertionRoundingTie
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CurvatureRounding
import DifferentialGeometry.Geometry.Curvature.Closure
import DifferentialGeometry.Geometry.Curvature.OperatorNaturality
import DifferentialGeometry.Geometry.Curvature.OpenEmbeddingPullback
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Flat
import DifferentialGeometry.Geometry.Metric.Conformal.OfContDiff
import DifferentialGeometry.Geometry.Metric.RoundCylinder

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold TopologicalSpace DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev EC := EuclideanSpace ℝ (Fin 2) × ℝ
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private abbrev cyl := roundCylinderMetric (E := E3) (n := 2)
private local instance : NeZero (Module.finrank ℝ EC) := ⟨by simp⟩
private local instance (U : Opens (S2 × ℝ)) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen IC U.isOpen)
private local instance (U : Opens (S2 × ℝ)) (W : Opens U) : SigmaCompactSpace W :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen IC W.isOpen)
private local instance (U : Opens E3) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) U.isOpen)

private theorem old_subset {A B : ℝ} (hAB : 2 * A < B) :
    insertionCylinder A B ≤ openCylinder B := by
  intro q hq
  change -2 * A < q.2 ∧ q.2 < B at hq
  change -B < q.2 ∧ q.2 < B
  exact ⟨by linarith [hq.1], hq.2⟩
private theorem round_subset {A B : ℝ} (hAB : 2 * A < B) :
    roundingCollar A ≤ insertionCylinder A B := by
  intro q hq
  change -A < q.2 ∧ q.2 < 0 at hq
  change -2 * A < q.2 ∧ q.2 < B
  constructor <;> linarith [hq.1, hq.2]

private theorem curvature_restrict_subset {U V : Opens (S2 × ℝ)} (hVU : V ≤ U)
    (g : SmoothRiemannianMetric IC U) (q : V) :
    metricScalarAt (g.restrictOpenOfSubset hVU) q = metricScalarAt g (Opens.inclusion hVU q) ∧
      leastCurvatureOperatorEigenvalueAt (g.restrictOpenOfSubset hVU) q
          (metricAlgebraicCurvatureTensorAt (g.restrictOpenOfSubset hVU) q) =
        leastCurvatureOperatorEigenvalueAt g (Opens.inclusion hVU q)
          (metricAlgebraicCurvatureTensorAt g (Opens.inclusion hVU q)) := by
  let W := nestedOpen (M := S2 × ℝ) (U := U) (V := V)
  let D := flatNestedDiffeo (I := IC) hVU
  let k := g.restrictOpen W
  have hp := restrictSubset_pull (I := IC) hVU g
  have hc : Diffeomorph.pullbackMetricCross k D = Diffeomorph.pullbackMetric k D := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [Diffeomorph.pullbackMetricCross_inner, Diffeomorph.pullbackMetric_inner]
  constructor
  · rw [hp, metricScalarAt_pullback, metricScalarAt_restrictOpen]
    rfl
  · rw [hp, ← hc, leastCurvatureOperatorEigenvalueAt_pullbackMetricCross,
      leastCurvatureOperatorEigenvalueAt_restrictOpen]
    rfl

private theorem pullback_curvature {A B η : ℝ} (hA : 0 < A)
    (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (openCylinder B)) (q : insertionCylinder A B) :
    metricScalarAt (insertedPullbackMetric hA hAB hη h) q =
        metricScalarAt (insertedMetric hA hAB hη h) (insertionMap hA hAB q) ∧
      leastCurvatureOperatorEigenvalueAt (insertedPullbackMetric hA hAB hη h) q
          (metricAlgebraicCurvatureTensorAt (insertedPullbackMetric hA hAB hη h) q) =
        leastCurvatureOperatorEigenvalueAt (insertedMetric hA hAB hη h) (insertionMap hA hAB q)
          (metricAlgebraicCurvatureTensorAt (insertedMetric hA hAB hη h) (insertionMap hA hAB q)) := by
  let out := insertedMetric hA hAB hη h
  have hone : scaleMetric 1 zero_lt_one out = out := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [scaleMetric_inner, one_mul]
  constructor
  · have hs := metricScalarAt_pullbackMetricOfInjectiveLocalDiffeomorph_scale out
      (insertionMap hA hAB) (insertionMap_isLocalDiffeomorph hA hAB)
      (injective_insertionMap hA hAB) 1 zero_lt_one q
    simpa only [hone, div_one, insertedPullbackMetric, out] using hs
  · exact leastCurvatureOperatorEigenvalueAt_pullbackMetricOfInjectiveLocalDiffeomorph out
      (insertionMap hA hAB) (insertionMap_isLocalDiffeomorph hA hAB)
      (injective_insertionMap hA hAB) q

theorem insertedMetric_retained_curvature {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (openCylinder B))
    (q : insertionCylinder A B) (hq : 0 ≤ q.val.2) :
    metricScalarAt (insertedMetric hA hAB hη h) (insertionMap hA hAB q) =
        metricScalarAt h (Opens.inclusion (old_subset hAB) q) ∧
      leastCurvatureOperatorEigenvalueAt (insertedMetric hA hAB hη h) (insertionMap hA hAB q)
          (metricAlgebraicCurvatureTensorAt (insertedMetric hA hAB hη h) (insertionMap hA hAB q)) =
        leastCurvatureOperatorEigenvalueAt h (Opens.inclusion (old_subset hAB) q)
          (metricAlgebraicCurvatureTensorAt h (Opens.inclusion (old_subset hAB) q)) := by
  let out := insertedPullbackMetric hA hAB hη h
  let old := h.restrictOpenOfSubset (old_subset hAB)
  let W : Opens (insertionCylinder A B) :=
    ⟨{x | 0 < x.val.2}, isOpen_lt continuous_const (continuous_snd.comp continuous_subtype_val)⟩
  have heq (x : insertionCylinder A B) (hx : 0 ≤ x.val.2)
      (v w : TangentSpace IC x) : out.inner x v w = old.inner x v w := by
    have ht := insertedPullbackMetric_rounded_inner hA hAB hη h x (by linarith) v w
    rw [conformalFactor_eq_zero_of_nonneg hx, mul_zero, Real.exp_zero, one_mul] at ht
    exact ht
  have hW : ∀ x : insertionCylinder A B, x ∈ W →
      ∀ v w : TangentSpace IC x, out.inner x v w = old.inner x v w :=
    fun x hx => heq x (show 0 ≤ x.val.2 from (show 0 < x.val.2 from hx).le)
  have hopen : IsOpenMap (fun x : insertionCylinder A B => x.val.2) :=
    isOpenMap_snd.comp (insertionCylinder A B).isOpen.isOpenEmbedding_subtypeVal.isOpenMap
  have hclosure : q ∈ closure (W : Set (insertionCylinder A B)) := by
    apply hopen.preimage_closure_subset_closure_preimage (s := Ioi (0 : ℝ))
    change q.val.2 ∈ closure (Ioi (0 : ℝ))
    rw [closure_Ioi]
    exact Set.mem_Ici.mpr hq
  have hR := metricScalarAt_eq_of_eqOn_closure out old W hW q hclosure
  have hRm := metricRm04StdAt_eq_of_eqOn_closure out old W hW q hclosure
  have hν := leastCurvatureOperatorEigenvalueAt_eq_of_metricRm04StdAt_equiv
    out old q q (LinearEquiv.refl ℝ (TangentSpace IC q)) (heq q hq) hRm
  obtain ⟨hRs, hνs⟩ := curvature_restrict_subset (old_subset hAB) h q
  obtain ⟨hRp, hνp⟩ := pullback_curvature hA hAB hη h q
  exact ⟨hRp.symm.trans (hR.trans hRs), hνp.symm.trans (hν.trans hνs)⟩

private theorem rounded_restriction {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (openCylinder B)) :
    (insertedPullbackMetric hA hAB hη h).restrictOpenOfSubset (round_subset hAB) =
      roundingMetric A (h.restrictOpenOfSubset ((round_subset hAB).trans (old_subset hAB))) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [SmoothRiemannianMetric.restrictSubset_inner, roundingMetric, conformalMetricOfContDiff_inner]
  have ht := insertedPullbackMetric_rounded_inner hA hAB hη h
    (Opens.inclusion (round_subset hAB) x)
    (by change -5 * A / 4 ≤ x.val.2; have hx := x.property.1; linarith) v w
  exact ht

private theorem rounding_input_error {A B : ℝ} (hAB : 2 * A < B)
    (h : SmoothRiemannianMetric IC (openCylinder B)) :
    metricDerivENormSupOn univ 2
      (h.restrictOpenOfSubset ((round_subset hAB).trans (old_subset hAB)))
      (roundingReference A) (roundingReference A) ≤
      metricDerivENormSupOn univ 2 h (cyl.restrictOpen (openCylinder B))
        (cyl.restrictOpen (openCylinder B)) := by
  apply (metricDerivENormSupOn_le_iff _ _ _ _ _ _).mpr
  intro j hj x _hx
  have hn := metricDerivNorm_flat ((round_subset hAB).trans (old_subset hAB)) h
    (cyl.restrictOpen (openCylinder B)) (cyl.restrictOpen (openCylinder B)) j x
  rw [SmoothRiemannianMetric.restrictOpen_flat] at hn
  rw [show roundingReference A = cyl.restrictOpen (roundingCollar A) from rfl, hn]
  exact ofReal_metricDerivNorm_le_sup univ 2 _ _ _ hj (mem_univ _)

theorem exists_insertedMetric_outer_curvature_gain :
    ∃ (A : ℝ) (hA : 0 < A), 2 * A < 1 / 2 ∧
      ∀ (B : ℝ) (hAB : 2 * A < B) (η : ℝ) (hη : 0 < η)
        (h : SmoothRiemannianMetric IC (openCylinder B)),
        metricDerivENormSupOn univ 2 h (cyl.restrictOpen (openCylinder B))
            (cyl.restrictOpen (openCylinder B)) < ENNReal.ofReal (1 / 100000000 : ℝ) →
        ∀ q : insertionCylinder A B, q.val.2 ∈ Ioc (-A) 0 →
          metricScalarAt h (Opens.inclusion (old_subset hAB) q) +
              (-deriv (deriv conformalFactor) q.val.2) / 2 ≤
            metricScalarAt (insertedMetric hA hAB hη h) (insertionMap hA hAB q) ∧
          2 * leastCurvatureOperatorEigenvalueAt h (Opens.inclusion (old_subset hAB) q)
                (metricAlgebraicCurvatureTensorAt h (Opens.inclusion (old_subset hAB) q)) +
              (-deriv (deriv conformalFactor) q.val.2) / 2 ≤
            2 * leastCurvatureOperatorEigenvalueAt (insertedMetric hA hAB hη h) (insertionMap hA hAB q)
              (metricAlgebraicCurvatureTensorAt (insertedMetric hA hAB hη h) (insertionMap hA hAB q)) := by
  obtain ⟨A, hA, hsmall, _hplanes, _hprofile, _hnorm, hgain⟩ :=
    exists_curvature_rounding_collar (η := (1 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  refine ⟨A, hA, hsmall, ?_⟩
  intro B hAB η hη h hclose q hq
  rcases lt_or_eq_of_le hq.2 with hz | hz
  · let x : roundingCollar A := ⟨q.val, hq.1, hz⟩
    let hsub := (round_subset hAB).trans (old_subset hAB)
    have hg := hgain (h.restrictOpenOfSubset hsub)
      ((rounding_input_error hAB h).trans_lt hclose) x
    obtain ⟨hRs, hνs⟩ := curvature_restrict_subset hsub h x
    obtain ⟨hRr, hνr⟩ := curvature_restrict_subset (round_subset hAB)
      (insertedPullbackMetric hA hAB hη h) x
    rw [rounded_restriction hA hAB hη h] at hRr hνr
    obtain ⟨hRp, hνp⟩ := pullback_curvature hA hAB hη h q
    rw [hRs, hνs, hRr, hνr] at hg
    have hxq : Opens.inclusion (round_subset hAB) x = q := by
      apply Subtype.ext
      rfl
    have hxo : Opens.inclusion hsub x = Opens.inclusion (old_subset hAB) q := by
      apply Subtype.ext
      rfl
    rw [hxq, hxo] at hg
    exact ⟨hg.1.trans_eq hRp, hg.2.trans_eq (congrArg (fun t : ℝ => 2 * t) hνp)⟩
  · obtain ⟨hR, hν⟩ := insertedMetric_retained_curvature hA hAB hη h q (le_of_eq hz.symm)
    have hD : deriv (deriv conformalFactor) 0 = 0 := by
      simpa only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
        iteratedDeriv_one, iteratedDeriv_zero] using iteratedDeriv_conformalFactor_zero 2
    rw [hz, hD, neg_zero, zero_div, add_zero, add_zero, hR, hν]
    exact ⟨le_rfl, le_rfl⟩

end DifferentialGeometry.PDE.RicciFlow.StandardCap
