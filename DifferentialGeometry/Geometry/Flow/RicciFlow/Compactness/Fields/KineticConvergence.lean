import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.GramConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Defs
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.Evaluation
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Quadratic.WeakConvergence
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Basic

noncomputable section

open Set Filter Bundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

section Curve

open PDE.RicciFlow.Perelman

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {X : PointedFlowSeq.{u, uE, uH} (I := I)}
variable {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
variable {subseq : ℕ → ℕ}
variable (Φ : PointedCGHMaps (I := I) X P subseq)

theorem FlowMetricConvergenceData.tendstoUniformlyOn_inner_lVelocity
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    (beta psi : ℝ) (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt beta psi)
    (T a b : ℝ) (alpha : ℝ → P.M)
    (halpha : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    (hback : MapsTo (fun s ↦ T - s) (Icc a b) (Icc beta psi)) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    TendstoUniformlyOn
      (fun k s ↦
        (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) (T - s)).inner (alpha s)
          (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s))
      (fun s ↦
        (co.gInf (T - s)).inner (alpha s)
          (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s))
      atTop (Icc a b) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  have hv : Continuous
      (fun s ↦ TotalSpace.mk' E (alpha s) (lVelocity (I := I) alpha s)) := by
    have hone : Continuous
        (fun s : ℝ ↦ (⟨s, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
      rw [continuous_iff_continuousAt]
      intro s
      rw [FiberBundle.continuousAt_totalSpace]
      exact ⟨continuousAt_id, by simpa using continuousAt_const⟩
    exact (halpha.continuous_tangentMap le_rfl).comp hone
  apply SmoothRiemannianMetric.tendstoUniformlyOn_inner_of_isCompact
    (fun k s => gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) (T - s))
    (fun s => co.gInf (T - s)) R alpha
    (fun s => lVelocity (I := I) alpha s) (fun s => lVelocity (I := I) alpha s)
    isCompact_Icc hv.continuousOn hv.continuousOn
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨k₀, hk₀⟩ := co.convergencePt (alpha '' Icc a b)
    (isCompact_Icc.image_of_continuousOn halpha.continuous.continuousOn) 0 ε hε
  filter_upwards [eventually_ge_atTop k₀] with k hk
  intro s hs
  have h := hk₀ k hk (T - s) (hback hs) 0 le_rfl (alpha s) ⟨s, hs, rfl⟩
  have hn : 0 ≤ metricDerivNorm 0
      (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) (T - s))
      (co.gInf (T - s)) R (alpha s) := Real.sqrt_nonneg _
  simpa only [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hn] using h

end Curve

section Energy

open Geometry.Curvature Analysis.Parabolic.TimeSobolev MeasureTheory

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {X : PointedFlowSeq.{u, uE, uH} (I := I)}
variable {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
variable {subseq : ℕ → ℕ}
variable (Φ : PointedCGHMaps (I := I) X P subseq)

theorem FlowMetricConvergenceData.integral_inner_chartGramOp_le_liminf
    (R : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      let : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    (beta psi : ℝ) (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt beta psi)
    (hcarrier : Icc beta psi ⊆ X.D.carrier)
    (alpha : P.M) {L : ℝ} (hL : 0 ≤ L) (tau : ℝ → ℝ)
    (htauCont : ContinuousOn tau (Icc (0 : ℝ) L))
    (htau : MapsTo tau (Icc (0 : ℝ) L) (Icc beta psi))
    {K : Set E} (hKc : IsCompact K)
    (hKchart : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      K ⊆ (extChartAt I alpha).target)
    (u : ℕ → timeH1 E L) (uLim : timeH1 E L)
    (huK : ∀ n (r : Icc (0 : ℝ) L), (u n).toFun r.1 ∈ K)
    (huLimK : ∀ r : Icc (0 : ℝ) L, uLim.toFun r.1 ∈ K)
    (hu : TendstoUniformly
      (fun n (r : Icc (0 : ℝ) L) ↦ (u n).toFun r.1)
      (fun r ↦ uLim.toFun r.1) atTop)
    (hdu : ∀ z : timeL2 E L,
      Tendsto (fun n ↦ inner ℝ (u n).deriv z) atTop
        (nhds (inner ℝ uLim.deriv z))) :
    let : TopologicalSpace P.M := P.topology
    let : ChartedSpace H P.M := P.charted
    let : T2Space P.M := P.t2
    let : IsManifold I ∞ P.M := P.smooth
    let : SigmaCompactSpace P.M := P.sigmaCompact
    (∫ r in (0 : ℝ)..L,
      (1 / 2 : ℝ) * inner ℝ
        (chartGramOp (I := I)
          ((lcMetricFamily (I := I) (M := P.M) co.gInf).restrict X.D)
          alpha (tau r, uLim.toFun r) (uLim.deriv r))
        (uLim.deriv r)) ≤
      liminf (fun n ↦ ∫ r in (0 : ℝ)..L,
        (1 / 2 : ℝ) * inner ℝ
          (chartGramOp (I := I)
            ((lcMetricFamily (I := I) (M := P.M)
              (fun t ↦ gSeqExt (I := I) Φ R bf hsrc htgt (co.φ n) t)).restrict X.D)
            alpha (tau r, (u n).toFun r) ((u n).deriv r))
          ((u n).deriv r)) atTop := by classical
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let GSeq : ℕ → MetricConnectionFamilyOn (I := I) (M := P.M) X.D := fun n ↦
    (lcMetricFamily (I := I) (M := P.M)
      (fun t ↦ gSeqExt (I := I) Φ R bf hsrc htgt (co.φ n) t)).restrict X.D
  let GInf : MetricConnectionFamilyOn (I := I) (M := P.M) X.D :=
    (lcMetricFamily (I := I) (M := P.M) co.gInf).restrict X.D
  let A : ℕ → ℝ → E →L[ℝ] E := fun n r ↦
    (1 / 2 : ℝ) • chartGramOp (I := I) (GSeq n) alpha
      (tau r, (u n).toFun r)
  let ALim : ℝ → E →L[ℝ] E := fun r ↦
    (1 / 2 : ℝ) • chartGramOp (I := I) GInf alpha
      (tau r, uLim.toFun r)
  have hpair (n : ℕ) : ContinuousOn
      (fun r ↦ (tau r, (u n).toFun r)) (Icc (0 : ℝ) L) :=
    htauCont.prodMk (u n).continuousOn_toFun
  have hpairLim : ContinuousOn
      (fun r ↦ (tau r, uLim.toFun r)) (Icc (0 : ℝ) L) :=
    htauCont.prodMk uLim.continuousOn_toFun
  have hAcont (n : ℕ) : ContinuousOn (A n) (Icc (0 : ℝ) L) := by
    have h := (continuousOn_chartGramOp_gSeqExt (I := I) (X := X) Φ R bf hsrc htgt
      (co.φ n) alpha hKchart).comp (hpair n) fun r hr ↦
        ⟨hcarrier (htau hr), huK n ⟨r, hr⟩⟩
    exact h.fun_const_smul (1 / 2 : ℝ)
  have hGInfCont : ContinuousOn (chartGramOp (I := I) GInf alpha) (Icc beta psi ×ˢ K) :=
    co.continuousOn_chartGramOp Φ R bf hsrc htgt beta psi alpha hKchart hKc hcarrier
  have hALimCont : ContinuousOn ALim (Icc (0 : ℝ) L) := by
    have h := hGInfCont.comp hpairLim fun r hr => ⟨htau hr, huLimK ⟨r, hr⟩⟩
    exact h.fun_const_smul (1 / 2 : ℝ)
  have hGramUnif : TendstoUniformly
      (fun n (r : Icc (0 : ℝ) L) ↦
        chartGramOp (I := I) (GSeq n) alpha
          (tau r.1, (u n).toFun r.1))
      (fun r ↦ chartGramOp (I := I) GInf alpha
        (tau r.1, uLim.toFun r.1)) atTop := by
    simpa only [GSeq, GInf] using
      (co.tendstoUniformly_chartGramOp Φ R bf hsrc htgt
        beta psi alpha hKchart hKc hGInfCont
        (tau := fun r : Icc (0 : ℝ) L ↦ tau r.1)
        (u := fun n r ↦ (u n).toFun r.1)
        (uLim := fun r ↦ uLim.toFun r.1)
        (fun r ↦ htau r.2) (Eventually.of_forall huK) huLimK hu)
  have hconv : TendstoUniformlyOn A ALim atTop (Icc (0 : ℝ) L) := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    simpa only [A, ALim, Function.comp_def] using
      (uniformContinuous_const_smul (1 / 2 : ℝ)).comp_tendstoUniformly hGramUnif
  have hself : ∀ n, ∀ᵐ r ∂timeMeasure L, IsSelfAdjoint (A n r) := fun n ↦
    Eventually.of_forall fun r ↦ by
      exact (IsSelfAdjoint.all (1 / 2 : ℝ)).smul
        (chartGramOp_self (I := I) (GSeq n) alpha (tau r, (u n).toFun r))
  have hpos : ∀ n, ∀ᵐ r ∂timeMeasure L, ∀ x,
      0 ≤ inner ℝ (A n r x) x := fun n ↦ Eventually.of_forall fun r x ↦ by
    dsimp only [A]
    rw [smul_apply, real_inner_smul_left]
    exact mul_nonneg (by norm_num)
      (chartGramOp_nonneg (I := I) (GSeq n) alpha (tau r, (u n).toFun r) x)
  have h := integral_inner_le_liminf_of_tendstoUniformlyOn A ALim hAcont hALimCont
    hconv hself hpos hL (fun n => (u n).deriv) uLim.deriv hdu
  dsimp only [A, ALim, GSeq, GInf] at h
  simpa only [smul_apply, real_inner_smul_left] using h

end Energy

end DifferentialGeometry.CheegerGromovCompactness
