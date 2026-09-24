import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Completeness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.FlowLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineConvergence

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedFlowSeq (I := I)}
variable {P : PointedRiemannianManifold (I := I)}
variable {subseq : Nat → Nat}
variable (Φ : PointedCGHMaps (I := I) X P subseq)

namespace HalfLineMetricConvergenceData

noncomputable def atWindow
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    (co : HalfLineMetricConvergenceData (I := I) Φ R bf hsrc htgt) (n : Nat) :
    FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt (-(n : Real)) 0 where
  φ := co.φ
  strictMono := co.strictMono
  gInf := co.gInf
  convergence := (co.convergenceOn n).convergence
  convergencePt := (co.convergenceOn n).convergencePt

end HalfLineMetricConvergenceData

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_halfLineMetricConvergenceData_of_bounds
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    (cLow : Nat → Real) (hcLow : ∀ n, 0 < cLow n)
    (hbound : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
      ∀ n k : Nat, ∀ t : Real, t ∈ Set.Icc (-(n : Real)) 0 →
        ∀ (y : SourceDomain (I := I) Φ k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
                sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
                sourceDomCharted (I := I) Φ k
            TangentSpace I y),
          cLow n * R.inner (y : P.M) v v ≤
            letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
              sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
              sourceDomCharted (I := I) Φ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
              sourceDomSmooth (I := I) Φ k
            (sourceMetric (I := I) Φ hsrc htgt k t).inner y v v)
    (hcovTail : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : T2Space P.M := P.t2
        letI : IsManifold I ∞ P.M := P.smooth
        letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ n q : Nat, ∃ C : Real, ∀ (k : Nat) (t : Real), t ∈ Set.Icc (-(n : Real)) 0 →
        ∀ z : P.M, z ∈ bf.grow k →
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z ≤ C)
    (hlipTail : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : T2Space P.M := P.t2
        letI : IsManifold I ∞ P.M := P.smooth
        letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ n p : Nat, ∃ Lt : Real, 0 ≤ Lt ∧
        ∀ (k : Nat) (s t : Real), s ∈ Set.Icc (-(n : Real)) 0 → t ∈ Set.Icc (-(n : Real)) 0 →
          ∀ q : Nat, q ≤ p → ∀ z : P.M, z ∈ bf.grow k →
            metricDerivNorm (I := I) q
              (gSeqExt (I := I) Φ R bf hsrc htgt k s)
              (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z ≤ Lt * |s - t|)
    (hlipSource : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : T2Space P.M := P.t2
        letI : IsManifold I ∞ P.M := P.smooth
        letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ n k : Nat,
        letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
          sourceDomTop (I := I) Φ k
        letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
          sourceDomCharted (I := I) Φ k
        letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
        letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
          sourceDomSmooth (I := I) Φ k
        letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
          sourceDomSigmaOf (I := I) Φ k (hsrc k)
        letI : SigmaCompactSpace ↥(sourceOpen (I := I) Φ k) :=
          sourceDomSigmaOf (I := I) Φ k (hsrc k)
        letI : T2Space ↥(sourceOpen (I := I) Φ k) := sourceDomT2 (I := I) Φ k
        ∀ C : Set (SourceDomain (I := I) Φ k), IsCompact C → ∀ p : Nat,
          ∃ Ls : Real, 0 ≤ Ls ∧
            ∀ (s t : Real), s ∈ Set.Icc (-(n : Real)) 0 → t ∈ Set.Icc (-(n : Real)) 0 →
              ∀ q : Nat, q ≤ p →
                ∀ y : SourceDomain (I := I) Φ k, y ∈ C →
                  metricDerivNorm (I := I) q
                    (sourceMetric (I := I) Φ hsrc htgt k s)
                    (sourceMetric (I := I) Φ hsrc htgt k t)
                    (sourceMetricRestriction (I := I) Φ R k) y ≤ Ls * |s - t|) :
    Nonempty (HalfLineMetricConvergenceData (I := I) Φ R bf hsrc htgt) := by
  classical
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  refine nonempty_halfLineMetricConvergenceData (Φ := Φ) ?_
  intro n ρ hρ
  let bfρ := BumpFamily.compSubseq (I := I) Φ bf ρ hρ
  let hsrcρ := SourceIsSigmaCompact.compSubseq (I := I) Φ hsrc ρ hρ
  let htgtρ := TargetIsSigmaCompact.compSubseq (I := I) Φ htgt ρ hρ
  have hboundρ : ∀ (k : Nat) (t : Real),
      t ∈ Set.Icc (-(n : Real)) 0 →
      ∀ (y : SourceDomain (I := I) (Φ.compSubseq ρ hρ) k)
        (v : letI : TopologicalSpace
              (SourceDomain (I := I) (Φ.compSubseq ρ hρ) k) :=
                sourceDomTop (I := I) (Φ.compSubseq ρ hρ) k
          letI : ChartedSpace H
              (SourceDomain (I := I) (Φ.compSubseq ρ hρ) k) :=
                sourceDomCharted (I := I) (Φ.compSubseq ρ hρ) k
          TangentSpace I y),
        cLow n * R.inner (y : P.M) v v ≤
          letI : TopologicalSpace
              (SourceDomain (I := I) (Φ.compSubseq ρ hρ) k) :=
                sourceDomTop (I := I) (Φ.compSubseq ρ hρ) k
          letI : ChartedSpace H
              (SourceDomain (I := I) (Φ.compSubseq ρ hρ) k) :=
                sourceDomCharted (I := I) (Φ.compSubseq ρ hρ) k
          letI : IsManifold I ∞
              (SourceDomain (I := I) (Φ.compSubseq ρ hρ) k) :=
                sourceDomSmooth (I := I) (Φ.compSubseq ρ hρ) k
          (sourceMetric (I := I) (Φ.compSubseq ρ hρ) hsrcρ htgtρ k t).inner y v v := by
    intro k t ht y v
    have hb := hbound n (ρ k) t ht y v
    rw [← sourceMetric_compSubseq (I := I) (Φ := Φ) hsrc htgt ρ hρ k] at hb
    exact hb
  have hcovTailρ : ∀ q : Nat, ∃ C : Real, ∀ (k : Nat) (t : Real),
      t ∈ Set.Icc (-(n : Real)) 0 →
      ∀ z : P.M, z ∈ bfρ.grow k →
        metricCovDerivNorm (I := I) q
          (gSeqExt (I := I) (Φ.compSubseq ρ hρ) R bfρ hsrcρ htgtρ k t) R z ≤ C := by
    intro q
    obtain ⟨C, hC⟩ := hcovTail n q
    refine ⟨C, fun k t ht z hz => ?_⟩
    dsimp only [bfρ, hsrcρ, htgtρ]
    rw [gSeqExt_compSubseq]
    exact hC (ρ k) t ht z hz
  have hlipTailρ : ∀ p : Nat, ∃ Lt : Real, 0 ≤ Lt ∧
      ∀ (k : Nat) (s t : Real),
        s ∈ Set.Icc (-(n : Real)) 0 →
        t ∈ Set.Icc (-(n : Real)) 0 →
        ∀ q : Nat, q ≤ p → ∀ z : P.M, z ∈ bfρ.grow k →
          metricDerivNorm (I := I) q
            (gSeqExt (I := I) (Φ.compSubseq ρ hρ) R bfρ hsrcρ htgtρ k s)
            (gSeqExt (I := I) (Φ.compSubseq ρ hρ) R bfρ hsrcρ htgtρ k t) R z ≤
              Lt * |s - t| := by
    intro p
    obtain ⟨Lt, hLt0, hLt⟩ := hlipTail n p
    refine ⟨Lt, hLt0, fun k s t hs ht q hq z hz => ?_⟩
    dsimp only [bfρ, hsrcρ, htgtρ]
    rw [gSeqExt_compSubseq, gSeqExt_compSubseq]
    exact hLt (ρ k) s t hs ht q hq z hz
  have hlipSourceρ : ∀ k : Nat,
      letI : TopologicalSpace (SourceDomain (I := I) (Φ.compSubseq ρ hρ) k) :=
        sourceDomTop (I := I) (Φ.compSubseq ρ hρ) k
      letI : ChartedSpace H (SourceDomain (I := I) (Φ.compSubseq ρ hρ) k) :=
        sourceDomCharted (I := I) (Φ.compSubseq ρ hρ) k
      letI : T2Space (SourceDomain (I := I) (Φ.compSubseq ρ hρ) k) :=
        sourceDomT2 (I := I) (Φ.compSubseq ρ hρ) k
      letI : IsManifold I ∞ (SourceDomain (I := I) (Φ.compSubseq ρ hρ) k) :=
        sourceDomSmooth (I := I) (Φ.compSubseq ρ hρ) k
      letI : SigmaCompactSpace (SourceDomain (I := I) (Φ.compSubseq ρ hρ) k) :=
        sourceDomSigmaOf (I := I) (Φ.compSubseq ρ hρ) k (hsrcρ k)
      letI : SigmaCompactSpace ↥(sourceOpen (I := I) (Φ.compSubseq ρ hρ) k) :=
        sourceDomSigmaOf (I := I) (Φ.compSubseq ρ hρ) k (hsrcρ k)
      letI : T2Space ↥(sourceOpen (I := I) (Φ.compSubseq ρ hρ) k) :=
        sourceDomT2 (I := I) (Φ.compSubseq ρ hρ) k
      ∀ C : Set (SourceDomain (I := I) (Φ.compSubseq ρ hρ) k), IsCompact C →
        ∀ p : Nat, ∃ Ls : Real, 0 ≤ Ls ∧
          ∀ (s t : Real),
            s ∈ Set.Icc (-(n : Real)) 0 →
            t ∈ Set.Icc (-(n : Real)) 0 →
            ∀ q : Nat, q ≤ p →
              ∀ y : SourceDomain (I := I) (Φ.compSubseq ρ hρ) k, y ∈ C →
                metricDerivNorm (I := I) q
                  (sourceMetric (I := I) (Φ.compSubseq ρ hρ) hsrcρ htgtρ k s)
                  (sourceMetric (I := I) (Φ.compSubseq ρ hρ) hsrcρ htgtρ k t)
                  (sourceMetricRestriction (I := I) (Φ.compSubseq ρ hρ) R k) y ≤
                    Ls * |s - t| := by
    intro k C hC p
    obtain ⟨Ls, hLs0, hLs⟩ := hlipSource n (ρ k) C hC p
    refine ⟨Ls, hLs0, fun s t hs ht q hq y hy => ?_⟩
    have hst := hLs s t hs ht q hq y hy
    rw [← refRes_compSubseq (I := I) (Φ := Φ) R ρ hρ k] at hst
    exact hst
  have hβψ : (-(n : Real)) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg n)
  let coρ := flowMetricConvergenceData (I := I) (Φ := Φ.compSubseq ρ hρ) R bfρ hsrcρ htgtρ
    (-(n : Real)) 0 hβψ (cLow n) (hcLow n) hboundρ hcovTailρ hlipTailρ hlipSourceρ
  refine ⟨coρ.φ, coρ.strictMono, coρ.gInf, ?_⟩
  exact BumpMetricConvergence.of_compSubseq (Φ := Φ) ρ hρ
    (FlowMetricConvergenceData.bump_convergence (Φ := Φ.compSubseq ρ hρ) coρ)

namespace HalfLineMetricConvergenceData

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem metric_convergence
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    (co : HalfLineMetricConvergenceData (I := I) Φ R bf hsrc htgt)
    (hcarrier : X.D.carrier ⊆ Set.Iic 0) :
    MetricInnerPullbackTendsto (I := I) (Φ.compSubseq co.φ co.strictMono) co.gInf := by
  intro t ht x v w
  obtain ⟨n, hn⟩ : ∃ n : Nat, t ∈ Set.Icc (-(n : Real)) 0 := by
    obtain ⟨n, hn⟩ := exists_nat_ge (-t)
    exact ⟨n, ⟨by linarith, hcarrier ht⟩⟩
  convert FlowMetricConvergenceData.metric_convergence_at (I := I) Φ R bf hsrc htgt
    (-(n : Real)) 0 (HalfLineMetricConvergenceData.atWindow Φ co n) hn x v w using 1
  · funext k
    rfl
  · simp only [HalfLineMetricConvergenceData.atWindow]

theorem scalar_convergence
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    (cLow : Nat → Real) (hcLow : ∀ n, 0 < cLow n)
    (hbound : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
      ∀ n k : Nat, ∀ t : Real, t ∈ Set.Icc (-(n : Real)) 0 →
        ∀ (y : SourceDomain (I := I) Φ k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
              sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
              sourceDomCharted (I := I) Φ k
            TangentSpace I y),
          cLow n * R.inner (y : P.M) v v ≤
            letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
              sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
              sourceDomCharted (I := I) Φ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
              sourceDomSmooth (I := I) Φ k
            (sourceMetric (I := I) Φ hsrc htgt k t).inner y v v)
    (hcovTail : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : T2Space P.M := P.t2
        letI : IsManifold I ∞ P.M := P.smooth
        letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ n q : Nat, ∃ C : Real, ∀ (k : Nat) (t : Real), t ∈ Set.Icc (-(n : Real)) 0 →
        ∀ z : P.M, z ∈ bf.grow k →
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z ≤ C)
    (co : HalfLineMetricConvergenceData (I := I) Φ R bf hsrc htgt)
    (hcarrier : X.D.carrier ⊆ Set.Iic 0) :
    FunctionPullbackTendsto (I := I) (Φ.compSubseq co.φ co.strictMono)
      (fun k t x ↦
        letI : TopologicalSpace (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).topology
        letI : ChartedSpace H (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).charted
        letI : IsManifold I ∞ (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).smooth
        letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
            (X.term ((subseq ∘ co.φ) k)).M := by
          change IsManifold I ∞ (X.term ((subseq ∘ co.φ) k)).M
          infer_instance
        letI : SigmaCompactSpace (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).sigmaCompact
        letI : T2Space (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).t2
        (X.term ((subseq ∘ co.φ) k)).S.scalar t x)
      (fun t x ↦
        letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
        letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
          change IsManifold I ∞ P.M
          infer_instance
        letI : SigmaCompactSpace P.M := P.sigmaCompact
        letI : T2Space P.M := P.t2
        metricScalarAt (I := I) (co.gInf t) x) := by
  intro t ht x
  obtain ⟨n, hn⟩ : ∃ n : Nat, t ∈ Set.Icc (-(n : Real)) 0 := by
    obtain ⟨n, hn⟩ := exists_nat_ge (-t)
    exact ⟨n, ⟨by linarith, hcarrier ht⟩⟩
  exact FlowMetricConvergenceData.scalar_convergence_at (I := I) Φ R bf hsrc htgt
      (-(n : Real)) 0 (cLow n) (hcLow n)
      (fun k t ht => hbound n k t ht)
      (fun q => hcovTail n q) (HalfLineMetricConvergenceData.atWindow Φ co n) hn x

theorem ricci_convergence
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    (cLow : Nat → Real) (hcLow : ∀ n, 0 < cLow n)
    (hbound : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
      ∀ n k : Nat, ∀ t : Real, t ∈ Set.Icc (-(n : Real)) 0 →
        ∀ (y : SourceDomain (I := I) Φ k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
              sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
              sourceDomCharted (I := I) Φ k
            TangentSpace I y),
          cLow n * R.inner (y : P.M) v v ≤
            letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
              sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
              sourceDomCharted (I := I) Φ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
              sourceDomSmooth (I := I) Φ k
            (sourceMetric (I := I) Φ hsrc htgt k t).inner y v v)
    (hcovTail : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : T2Space P.M := P.t2
        letI : IsManifold I ∞ P.M := P.smooth
        letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ n q : Nat, ∃ C : Real, ∀ (k : Nat) (t : Real), t ∈ Set.Icc (-(n : Real)) 0 →
        ∀ z : P.M, z ∈ bf.grow k →
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z ≤ C)
    (co : HalfLineMetricConvergenceData (I := I) Φ R bf hsrc htgt)
    (hcarrier : X.D.carrier ⊆ Set.Iic 0) :
    MetricRicciPullbackTendsto (I := I) (Φ.compSubseq co.φ co.strictMono) co.gInf := by
  intro t ht x v w
  obtain ⟨n, hn⟩ : ∃ n : Nat, t ∈ Set.Icc (-(n : Real)) 0 := by
    obtain ⟨n, hn⟩ := exists_nat_ge (-t)
    exact ⟨n, ⟨by linarith, hcarrier ht⟩⟩
  simp only [Function.comp_apply, PointedCGHMaps.compSubseq_map]
  exact FlowMetricConvergenceData.ricci_convergence_at (I := I) Φ R bf hsrc htgt
    (-(n : Real)) 0 (cLow n) (hcLow n) (fun k t ht => hbound n k t ht)
    (fun q => hcovTail n q) (HalfLineMetricConvergenceData.atWindow Φ co n) hn x v w

theorem ricNorm_convergence
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    (cLow : Nat → Real) (hcLow : ∀ n, 0 < cLow n)
    (hbound : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
      ∀ n k : Nat, ∀ t : Real, t ∈ Set.Icc (-(n : Real)) 0 →
        ∀ (y : SourceDomain (I := I) Φ k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
                sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
                sourceDomCharted (I := I) Φ k
            TangentSpace I y),
          cLow n * R.inner (y : P.M) v v ≤
            letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
              sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
              sourceDomCharted (I := I) Φ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
              sourceDomSmooth (I := I) Φ k
            (sourceMetric (I := I) Φ hsrc htgt k t).inner y v v)
    (hcovTail : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : T2Space P.M := P.t2
        letI : IsManifold I ∞ P.M := P.smooth
        letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ n q : Nat, ∃ C : Real, ∀ (k : Nat) (t : Real), t ∈ Set.Icc (-(n : Real)) 0 →
        ∀ z : P.M, z ∈ bf.grow k →
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z ≤ C)
    (co : HalfLineMetricConvergenceData (I := I) Φ R bf hsrc htgt)
    (hcarrier : X.D.carrier ⊆ Set.Iic 0) :
    FunctionPullbackTendsto (I := I) (Φ.compSubseq co.φ co.strictMono)
      (fun k t x ↦
        letI : TopologicalSpace (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).topology
        letI : ChartedSpace H (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).charted
        letI : IsManifold I ∞ (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).smooth
        letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
            (X.term ((subseq ∘ co.φ) k)).M := by
          change IsManifold I ∞ (X.term ((subseq ∘ co.φ) k)).M
          infer_instance
        letI : SigmaCompactSpace (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).sigmaCompact
        letI : T2Space (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).t2
        DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I)
          (X.term ((subseq ∘ co.φ) k)).S t x)
      (fun t x ↦
        letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
        letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
          change IsManifold I ∞ P.M
          infer_instance
        letI : SigmaCompactSpace P.M := P.sigmaCompact
        letI : T2Space P.M := P.t2
        normSq0S (I := I) (co.gInf t) x 2
          (metricRicci (I := I) (co.gInf t) x)) := by
  intro t ht x
  obtain ⟨n, hn⟩ : ∃ n : Nat, t ∈ Set.Icc (-(n : Real)) 0 := by
    obtain ⟨n, hn⟩ := exists_nat_ge (-t)
    exact ⟨n, ⟨by linarith, hcarrier ht⟩⟩
  exact FlowMetricConvergenceData.ricNorm_convergence_at (I := I) Φ R bf hsrc htgt
      (-(n : Real)) 0 (cLow n) (hcLow n)
      (fun k t ht => hbound n k t ht)
      (fun q => hcovTail n q) (HalfLineMetricConvergenceData.atWindow Φ co n) hn x

end HalfLineMetricConvergenceData

namespace HalfLineMetricConvergenceData

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem gInf_zero_eq
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    (co : HalfLineMetricConvergenceData (I := I) Φ R bf hsrc htgt)
    (g0 : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (hconv0 : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : T2Space P.M := P.t2
        letI : IsManifold I ∞ P.M := P.smooth
        letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ (x : P.M) (v w : TangentSpace I x) (ε : Real), 0 < ε →
        ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k → ∀ hx : x ∈ Φ.source k,
          |(letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
              sourceDomCharted (I := I) Φ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
              sourceDomSmooth (I := I) Φ k
            (sourceMetric (I := I) Φ hsrc htgt k 0).inner ⟨x, hx⟩ v w)
            - g0.inner x v w| < ε) :
    co.gInf 0 = g0 := by
  have h0 : (0 : Real) ∈ Set.Icc (-((0 : Nat) : Real)) 0 :=
    ⟨by norm_num, le_rfl⟩
  have h := DifferentialGeometry.CheegerGromovCompactness.gInf_zero_eq (I := I)
    Φ R bf hsrc htgt
    (-((0 : Nat) : Real)) 0 (HalfLineMetricConvergenceData.atWindow Φ co 0) h0 g0 hconv0
  simpa only [HalfLineMetricConvergenceData.atWindow] using h

theorem gInf_pde
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    (co : HalfLineMetricConvergenceData (I := I) Φ R bf hsrc htgt)
    (cLow : Nat → Real) (hcLow : ∀ n, 0 < cLow n)
    (hbound : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
      ∀ n k : Nat, ∀ t : Real, t ∈ Set.Icc (-(n : Real)) 0 →
        ∀ (y : SourceDomain (I := I) Φ k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
              sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
              sourceDomCharted (I := I) Φ k
            TangentSpace I y),
          cLow n * R.inner (y : P.M) v v ≤
            letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
              sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
              sourceDomCharted (I := I) Φ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
              sourceDomSmooth (I := I) Φ k
            (sourceMetric (I := I) Φ hsrc htgt k t).inner y v v)
    (hcovTail : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : T2Space P.M := P.t2
        letI : IsManifold I ∞ P.M := P.smooth
        letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ n q : Nat, ∃ C : Real, ∀ (k : Nat) (t : Real), t ∈ Set.Icc (-(n : Real)) 0 →
        ∀ z : P.M, z ∈ bf.grow k →
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z ≤ C)
    (hreg : Set.Iio 0 ⊆ X.D.regular)
    {t : Real} (_ht : t ∈ X.D.regular) (htneg : t < 0)
    (x : P.M)
    (v w : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      TangentSpace I x) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    HasDerivAt (fun s : Real => (co.gInf s).inner x v w)
      ((-2 : Real) * ricciTensor (I := I) (co.gInf t) x v w) t := by
  obtain ⟨n, hn⟩ := exists_nat_gt (-t)
  have hγ : -(n : Real) < t := by linarith
  have hmid : t < t / 2 := by linarith
  have hhalf : t / 2 < 0 := by linarith
  have hwin : Set.Icc (-(n : Real)) (t / 2) ⊆ X.D.regular := by
    intro s hs
    exact hreg (lt_of_le_of_lt hs.2 hhalf)
  have hsub : Set.Icc (-(n : Real)) (t / 2) ⊆ Set.Icc (-(n : Real)) 0 := by
    intro s hs
    exact ⟨hs.1, le_of_lt (lt_of_le_of_lt hs.2 hhalf)⟩
  have hmem : t ∈ Set.Icc (-(n : Real)) (t / 2) := ⟨hγ.le, hmid.le⟩
  have h := FlowMetricConvergenceData.gInf_pde (I := I) Φ R bf hsrc htgt
    (-(n : Real)) (t / 2) hwin (cLow n) (hcLow n)
    (fun k s hs y v => hbound n k s (hsub hs) y v)
    (fun q => by
      obtain ⟨C, hC⟩ := hcovTail n q
      exact ⟨C, fun k s hs z hz => hC k s (hsub hs) z hz⟩)
    (FlowMetricConvergenceData.restrict (Φ := Φ)
      (HalfLineMetricConvergenceData.atWindow Φ co n) hsub) x v w hmem
  have hder := h.hasDerivAt (Icc_mem_nhds hγ hmid)
  simpa only [HalfLineMetricConvergenceData.atWindow,
    FlowMetricConvergenceData.restrict] using hder

end HalfLineMetricConvergenceData

end CheegerGromovCompactness
end DifferentialGeometry
