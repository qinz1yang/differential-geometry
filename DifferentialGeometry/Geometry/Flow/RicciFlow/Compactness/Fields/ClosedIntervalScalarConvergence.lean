import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.ClosedIntervalDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Equation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PullbackMetricEquivalence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.Regularity
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.CompactEquivalence
import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.Scalar


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq (I := I)} {P : PointedRiemannianManifold (I := I)}
  {subseq : ℕ → ℕ}

theorem FlowMetricConvergenceData.tendstoUniformlyOn_scalar_on_closed_interval
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    {a b : ℝ} (co : FlowMetricConvergenceData Φ R bf hsrc htgt a b)
    (hslab : Icc a b ⊆ X.D.carrier) (hregular : Ico a b ⊆ X.D.regular)
    {K : Set P.M} (hK : letI : TopologicalSpace P.M := P.topology; IsCompact K) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    TendstoUniformlyOn
      (fun k (z : ℝ × P.M) =>
        letI : TopologicalSpace (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).topology
        letI : ChartedSpace H (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).charted
        letI : IsManifold I ∞ (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).smooth
        letI : SigmaCompactSpace (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).sigmaCompact
        letI : T2Space (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).t2
        (X.term ((subseq ∘ co.φ) k)).S.scalar z.1 (Φ.map (co.φ k) z.2))
      (fun z => metricScalarAt (co.gInf z.1) z.2) atTop (Icc a b ×ˢ K) := by
  classical
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨L, hL, hEqInf⟩ := exists_metric_uniform_equivalent_on_compact co.gInf R
    isCompact_Icc hK (FlowMetricConvergenceData.metric_cont Φ hslab co)
  obtain ⟨Nlow, hNlow⟩ := FlowMetricConvergenceData.exists_eventually_metricUniformEquivalentOn
    Φ R bf hsrc htgt co hK hL hEqInf
  let lam : ℝ := min L⁻¹ (2 * L)⁻¹
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hlam : 0 < lam := lt_min (inv_pos.mpr hLpos)
    (inv_pos.mpr (mul_pos (by norm_num) hLpos))
  have hRnonneg (x : P.M) (v : TangentSpace I x) : 0 ≤ R.inner x v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact (R.pos x v hv).le
  have hlowInf (t : ℝ) (ht : t ∈ Icc a b) (x : P.M) (hx : x ∈ K)
      (v : TangentSpace I x) : lam * R.inner x v v ≤ (co.gInf t).inner x v v :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (hRnonneg x v)).trans
      ((hEqInf t ht).2 x hx v).1
  have hlowSeq (k : ℕ) (hk : Nlow ≤ k) (t : ℝ) (ht : t ∈ Icc a b)
      (x : P.M) (hx : x ∈ K) (v : TangentSpace I x) :
      lam * R.inner x v v ≤ (gSeqExt Φ R bf hsrc htgt (co.φ k) t).inner x v v :=
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (hRnonneg x v)).trans
      ((hNlow k hk t ht).2 x hx v).1
  obtain ⟨Ncov, hNcov⟩ := co.convergencePt K hK 2 1 zero_lt_one
  obtain ⟨B, _, hbase⟩ := exists_metric_extension_covariant_derivative_bound_on_closed_interval
    Φ R bf hsrc htgt hslab hregular (co.φ Ncov) hK 2
  have hbddInf (t : ℝ) (ht : t ∈ Icc a b) (x : P.M) (hx : x ∈ K)
      (q : ℕ) (hq : q ≤ 2) : metricCovDerivNorm q (co.gInf t) R x ≤ B + 1 := by
    have hdiff : metricDerivNorm q (co.gInf t)
        (gSeqExt Φ R bf hsrc htgt (co.φ Ncov) t) R x < 1 := by
      rw [metricDerivNorm_symm]
      exact hNcov Ncov le_rfl t ht q hq x hx
    exact (covNorm_le_add q (co.gInf t)
      (gSeqExt Φ R bf hsrc htgt (co.φ Ncov) t) R x).trans
        (add_le_add (hbase q hq t ht x hx) hdiff.le)
  have hbddSeq (k : ℕ) (hk : Ncov ≤ k) (t : ℝ) (ht : t ∈ Icc a b)
      (x : P.M) (hx : x ∈ K) (q : ℕ) (hq : q ≤ 2) :
      metricCovDerivNorm q (gSeqExt Φ R bf hsrc htgt (co.φ k) t) R x ≤ B + 2 := by
    have htri := covNorm_le_add q (gSeqExt Φ R bf hsrc htgt (co.φ k) t)
      (co.gInf t) R x
    have hb := hbddInf t ht x hx q hq
    have hd := hNcov k hk t ht q hq x hx
    linarith
  obtain ⟨C, hC, hscalar⟩ := exists_abs_metricScalarAt_sub_le R hK lam (B + 2) hlam
  obtain ⟨Ngrow, hNgrow⟩ := bf.grow_cover K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  let delta : ℝ := epsilon / (3 * C + 1)
  have hden : 0 < 3 * C + 1 := by positivity
  have hdelta : 0 < delta := div_pos hepsilon hden
  obtain ⟨Ndelta, hNdelta⟩ := co.convergencePt K hK 2 delta hdelta
  filter_upwards [eventually_ge_atTop Nlow, eventually_ge_atTop Ncov,
    eventually_ge_atTop Ngrow, eventually_ge_atTop Ndelta] with k hklow hkcov hkgrow hkdelta
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  let u := gSeqExt Φ R bf hsrc htgt (co.φ k) t
  have hsum : (∑ q ∈ Finset.range 3, metricDerivNorm q u (co.gInf t) R x) ≤
      3 * delta := by
    calc
      (∑ q ∈ Finset.range 3, metricDerivNorm q u (co.gInf t) R x)
          ≤ ∑ _q ∈ Finset.range 3, delta := by
            exact Finset.sum_le_sum fun q hq =>
              (hNdelta k hkdelta t ht q
                (Nat.le_of_lt_succ (Finset.mem_range.mp hq)) x hx).le
      _ = 3 * delta := by norm_num
  have hlocal := hscalar u (co.gInf t)
    (fun y hy v => hlowSeq k hklow t ht y hy v)
    (fun y hy v => hlowInf t ht y hy v)
    (fun y hy q hq => hbddSeq k hkcov t ht y hy q hq)
    (fun y hy q hq => (hbddInf t ht y hy q hq).trans (by linarith)) x hx
  have hdeltaEq : delta * (3 * C + 1) = epsilon :=
    div_mul_cancel₀ epsilon (ne_of_gt hden)
  have hprod : C * (3 * delta) < epsilon := by nlinarith
  have hmetric : |metricScalarAt u x - metricScalarAt (co.gInf t) x| < epsilon :=
    (hlocal.trans (mul_le_mul_of_nonneg_left hsum hC.le)).trans_lt hprod
  have hxgrow : x ∈ bf.grow (co.φ k) :=
    hNgrow (co.φ k) (hkgrow.trans (co.strictMono.id_le k)) hx
  dsimp only [u] at hmetric
  rw [gSeqExt_scalar Φ R bf hsrc htgt (co.φ k) t x hxgrow] at hmetric
  simpa only [Function.comp_apply, Real.dist_eq, abs_sub_comm] using hmetric

end DifferentialGeometry.CheegerGromovCompactness
