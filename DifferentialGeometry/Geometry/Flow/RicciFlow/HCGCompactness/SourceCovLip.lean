import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConvFieldAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConvFieldInputs

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Uniform source-flow covariant and time-Lipschitz bounds

This file records the constants-first source-native analytic output used by the
open-window convergence assembly.  It deliberately mentions neither bump
functions nor the globally extended metrics: those are downstream localization
devices, while the estimates here belong to the pulled-back Ricci flows on the
varying source domains.
-/

noncomputable section

open Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {X : PointedFlowSeq (I := I)}
variable {P : PointedRiemannianManifold (I := I)}
variable {subseq : Nat → Nat}

/-- Uniform, constants-first covariant and time-Lipschitz control for the
pulled-back source flows.  Both constants are chosen before the varying source
index `k`; this is the quantifier order required by the compactness argument. -/
structure SrcCovLipData
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (β ψ : ℝ) : Prop where
  /-- Every reference-covariant metric tower is uniformly bounded on every
  source domain and throughout the closed time window. -/
  cov :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    ∀ q : Nat, ∃ Cq : ℝ, 0 ≤ Cq ∧
      ∀ k : Nat,
        letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
          sourceDomTop (I := I) Φ k
        letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
          sourceDomCharted (I := I) Φ k
        letI : T2Space (SourceDomain (I := I) Φ k) :=
          sourceDomT2 (I := I) Φ k
        letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
          sourceDomSmooth (I := I) Φ k
        letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
          sourceDomSigmaOf (I := I) Φ k (hsrc k)
        ∀ t : ℝ, t ∈ Set.Icc β ψ →
          ∀ y : SourceDomain (I := I) Φ k,
            metricCovDerivNorm (I := I) q
                (srcMetric (I := I) Φ hsrc htgt k t)
                (refRes (I := I) Φ R hsrc k) y ≤ Cq
  /-- For each finite order, one Lipschitz constant controls all lower orders,
  all source domains, and every pair of times in the window. -/
  lip :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    ∀ p : Nat, ∃ Lp : ℝ, 0 ≤ Lp ∧
      ∀ k : Nat,
        letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
          sourceDomTop (I := I) Φ k
        letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
          sourceDomCharted (I := I) Φ k
        letI : T2Space (SourceDomain (I := I) Φ k) :=
          sourceDomT2 (I := I) Φ k
        letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
          sourceDomSmooth (I := I) Φ k
        letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
          sourceDomSigmaOf (I := I) Φ k (hsrc k)
        ∀ s t : ℝ, s ∈ Set.Icc β ψ → t ∈ Set.Icc β ψ →
          ∀ q : Nat, q ≤ p →
            ∀ y : SourceDomain (I := I) Φ k,
              metricDerivNorm (I := I) q
                  (srcMetric (I := I) Φ hsrc htgt k s)
                  (srcMetric (I := I) Φ hsrc htgt k t)
                  (refRes (I := I) Φ R hsrc k) y ≤ Lp * |s - t|

/-- Joint order-zero metric and Ricci-evolution bounds in a fixed reference
norm.  Both constants are explicit, so the result can be applied uniformly on
varying source manifolds without choosing a compact spatial subcover. -/
theorem covRic0_le
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [IsManifold I ∞ M] [SigmaCompactSpace M]
    (gSeq : Nat → Real → SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    {i : Nat} {t B K : Real}
    (hB : 1 ≤ B)
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gRef (gSeq i t) B)
    (x : M)
    (hShi :
      Real.sqrt
          (Tensor0SBundle.normSq0S (I := I) (gSeq i t) x 2
            (ricCovTower (I := I) (gSeq i t) (gSeq i t) 0 x)) ≤ K) :
    metricCovDerivNorm (I := I) 0 (gSeq i t) gRef x ≤
        B * Real.sqrt (Module.finrank Real E : Real) ∧
      Real.sqrt
          (Tensor0SBundle.normSq0S (I := I) gRef x 2
            ((-2 : Real) • nablaRicReal (I := I) gSeq gRef 0 i t x)) ≤
        2 * (Real.sqrt (B ^ 2) * K) := by
  have hsymm := metricUniformEquivalentOn_symm (I := I) hEq
  constructor
  · exact covNorm0_le (I := I) (gSeq i t) gRef x hB
      (fun v => hsymm.2 x (Set.mem_univ x) v)
  · rw [sqrt_normSq0S_smul]
    have habs : |(-2 : Real)| = 2 := by norm_num
    rw [habs]
    have hcomp := Tensor0SBundle.sqrt_normSq0S_le_of_metric_equiv
      (I := I) (g := gSeq i t) (h := gRef) x 2 hB
      (fun v => hsymm.2 x (Set.mem_univ x) v)
      (ricCovTower (I := I) (gSeq i t) (gSeq i t) 0 x)
    have hnabla :
        Real.sqrt
            (Tensor0SBundle.normSq0S (I := I) gRef x (0 + 2)
              (nablaRicReal (I := I) gSeq gRef 0 i t x)) ≤
          Real.sqrt (B ^ 2) *
            Real.sqrt
              (Tensor0SBundle.normSq0S (I := I) (gSeq i t) x 2
                (ricCovTower (I := I) (gSeq i t) (gSeq i t) 0 x)) := by
      rw [nablaRicReal_normSq]
      simpa using hcomp
    exact le_trans (mul_le_mul_of_nonneg_left hnabla (by norm_num))
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hShi (Real.sqrt_nonneg _)) (by norm_num))

/-- Source-flow covariant and time-Lipschitz bounds from uniform metric
equivalence, moving Shi estimates, and one uniform initial covariant envelope.

This is the analytic owner of the varying-domain quantifier uniformity.  In
particular, it must not be replaced by applying a per-source compact estimate
after fixing `k`, since that would choose the constants in the wrong order. -/
theorem srcCovLip_of_soln
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    {β ψ t₀ : ℝ}
    (_hβψ : β ≤ ψ)
    (ht₀ : t₀ ∈ Set.Icc β ψ)
    (hwin : Set.Icc β ψ ⊆ X.D.regular)
    (Bmax : ℝ) (hBmax : 1 ≤ Bmax)
    (hequiv :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : T2Space P.M := P.t2
      letI : IsManifold I ∞ P.M := P.smooth
      letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ k : Nat,
        letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
          sourceDomTop (I := I) Φ k
        letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
          sourceDomCharted (I := I) Φ k
        letI : T2Space (SourceDomain (I := I) Φ k) :=
          sourceDomT2 (I := I) Φ k
        letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
          sourceDomSmooth (I := I) Φ k
        letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
          sourceDomSigmaOf (I := I) Φ k (hsrc k)
        ∀ t : ℝ, t ∈ Set.Icc β ψ →
          MetricUniformEquivalentOn (I := I)
            (Set.univ : Set (SourceDomain (I := I) Φ k))
            (refRes (I := I) Φ R hsrc k)
            (srcMetric (I := I) Φ hsrc htgt k t) Bmax)
    (hShi :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : T2Space P.M := P.t2
      letI : IsManifold I ∞ P.M := P.smooth
      letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ N : Nat, ∃ KShi : ℝ, 0 ≤ KShi ∧
        ∀ k : Nat,
          letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
            sourceDomTop (I := I) Φ k
          letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
            sourceDomCharted (I := I) Φ k
          letI : T2Space (SourceDomain (I := I) Φ k) :=
            sourceDomT2 (I := I) Φ k
          letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
            sourceDomSmooth (I := I) Φ k
          letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
            sourceDomSigmaOf (I := I) Φ k (hsrc k)
          MovingShiBoundOn (I := I)
            (Set.univ : Set (SourceDomain (I := I) Φ k)) β ψ
            (fun _ t ↦ srcMetric (I := I) Φ hsrc htgt k t) N KShi)
    (hinit :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : T2Space P.M := P.t2
      letI : IsManifold I ∞ P.M := P.smooth
      letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ q : Nat, ∃ Cq : ℝ, 0 ≤ Cq ∧
        ∀ k : Nat,
          letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
            sourceDomTop (I := I) Φ k
          letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
            sourceDomCharted (I := I) Φ k
          letI : T2Space (SourceDomain (I := I) Φ k) :=
            sourceDomT2 (I := I) Φ k
          letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
            sourceDomSmooth (I := I) Φ k
          letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
            sourceDomSigmaOf (I := I) Φ k (hsrc k)
          ∀ y : SourceDomain (I := I) Φ k,
            metricCovDerivNorm (I := I) q
                (srcMetric (I := I) Φ hsrc htgt k t₀)
                (refRes (I := I) Φ R hsrc k) y ≤ Cq) :
    SrcCovLipData (I := I) Φ R hsrc htgt β ψ := by
  classical
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  have hcore0 : ∃ C0 L0 : ℝ, 0 ≤ C0 ∧ 0 ≤ L0 ∧
      (∀ k : Nat,
        letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
          sourceDomTop (I := I) Φ k
        letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
          sourceDomCharted (I := I) Φ k
        letI : T2Space (SourceDomain (I := I) Φ k) :=
          sourceDomT2 (I := I) Φ k
        letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
          sourceDomSmooth (I := I) Φ k
        letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
          sourceDomSigmaOf (I := I) Φ k (hsrc k)
        ∀ t : ℝ, t ∈ Set.Icc β ψ →
          ∀ y : SourceDomain (I := I) Φ k,
            metricCovDerivNorm (I := I) 0
                (srcMetric (I := I) Φ hsrc htgt k t)
                (refRes (I := I) Φ R hsrc k) y ≤ C0) ∧
      (∀ k : Nat,
        letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
          sourceDomTop (I := I) Φ k
        letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
          sourceDomCharted (I := I) Φ k
        letI : T2Space (SourceDomain (I := I) Φ k) :=
          sourceDomT2 (I := I) Φ k
        letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
          sourceDomSmooth (I := I) Φ k
        letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
          sourceDomSigmaOf (I := I) Φ k (hsrc k)
        ∀ t : ℝ, t ∈ Set.Icc β ψ →
          ∀ y : SourceDomain (I := I) Φ k,
            Real.sqrt
                (Tensor0SBundle.normSq0S (I := I)
                  (refRes (I := I) Φ R hsrc k) y 2
                  ((-2 : ℝ) •
                    nablaRicReal (I := I)
                      (fun _ t' ↦ srcMetric (I := I) Φ hsrc htgt k t')
                      (refRes (I := I) Φ R hsrc k) 0 0 t y)) ≤ L0) := by
    obtain ⟨K0, hK0, hShi0⟩ := hShi 0
    refine ⟨Bmax * Real.sqrt (Module.finrank ℝ E : ℝ),
      2 * (Real.sqrt (Bmax ^ 2) * K0), ?_, ?_, ?_, ?_⟩
    · exact mul_nonneg (le_trans zero_le_one hBmax) (Real.sqrt_nonneg _)
    · exact mul_nonneg (by norm_num)
        (mul_nonneg (Real.sqrt_nonneg _) hK0)
    · intro k
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
        sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
        sourceDomCharted (I := I) Φ k
      letI : T2Space (SourceDomain (I := I) Φ k) :=
        sourceDomT2 (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
        sourceDomSmooth (I := I) Φ k
      letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
        sourceDomSigmaOf (I := I) Φ k (hsrc k)
      intro t ht y
      exact
        (covRic0_le (I := I)
          (fun _ t' ↦ srcMetric (I := I) Φ hsrc htgt k t')
          (refRes (I := I) Φ R hsrc k) (i := 0) (t := t)
          (B := Bmax) (K := K0) hBmax (hequiv k t ht) y
          (hShi0 k 0 le_rfl 0 t ht y (Set.mem_univ y))).1
    · intro k
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
        sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
        sourceDomCharted (I := I) Φ k
      letI : T2Space (SourceDomain (I := I) Φ k) :=
        sourceDomT2 (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
        sourceDomSmooth (I := I) Φ k
      letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
        sourceDomSigmaOf (I := I) Φ k (hsrc k)
      intro t ht y
      exact
        (covRic0_le (I := I)
          (fun _ t' ↦ srcMetric (I := I) Φ hsrc htgt k t')
          (refRes (I := I) Φ R hsrc k) (i := 0) (t := t)
          (B := Bmax) (K := K0) hBmax (hequiv k t ht) y
          (hShi0 k 0 le_rfl 0 t ht y (Set.mem_univ y))).2
  /- Strong induction chooses every numeric coefficient before the varying
  source type. At positive order, `covOrderBound_stage_on` supplies the metric
  tower bound and `ric_bound_field_on` supplies the evolution-tensor bound. -/
  have hcore : ∀ q : Nat, ∃ Cq Lq : ℝ, 0 ≤ Cq ∧ 0 ≤ Lq ∧
      (∀ k : Nat,
        letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
          sourceDomTop (I := I) Φ k
        letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
          sourceDomCharted (I := I) Φ k
        letI : T2Space (SourceDomain (I := I) Φ k) :=
          sourceDomT2 (I := I) Φ k
        letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
          sourceDomSmooth (I := I) Φ k
        letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
          sourceDomSigmaOf (I := I) Φ k (hsrc k)
        ∀ t : ℝ, t ∈ Set.Icc β ψ →
          ∀ y : SourceDomain (I := I) Φ k,
            metricCovDerivNorm (I := I) q
                (srcMetric (I := I) Φ hsrc htgt k t)
                (refRes (I := I) Φ R hsrc k) y ≤ Cq) ∧
      (∀ k : Nat,
        letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
          sourceDomTop (I := I) Φ k
        letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
          sourceDomCharted (I := I) Φ k
        letI : T2Space (SourceDomain (I := I) Φ k) :=
          sourceDomT2 (I := I) Φ k
        letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
          sourceDomSmooth (I := I) Φ k
        letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
          sourceDomSigmaOf (I := I) Φ k (hsrc k)
        ∀ t : ℝ, t ∈ Set.Icc β ψ →
          ∀ y : SourceDomain (I := I) Φ k,
            Real.sqrt
                (Tensor0SBundle.normSq0S (I := I)
                  (refRes (I := I) Φ R hsrc k) y (q + 2)
                  ((-2 : ℝ) •
                    nablaRicReal (I := I)
                      (fun _ t' ↦ srcMetric (I := I) Φ hsrc htgt k t')
                      (refRes (I := I) Φ R hsrc k) q 0 t y)) ≤ Lq) := by
    intro q
    induction q using Nat.strong_induction_on with
    | _ q ih =>
      by_cases hq : q = 0
      · subst q
        exact hcore0
      · have hq_pos : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq
        have hprev := fun r : {r : Nat // r < q} => ih r.1 r.2
        choose Cprev _Lprev _hCprev _hLprev hcovPrev _hricPrev using hprev
        let Cg : Nat → ℝ := fun r =>
          if hr : r < q then Cprev ⟨r, hr⟩ else 0
        obtain ⟨Kq, hKq0, hShiQ⟩ := hShi q
        obtain ⟨initC, hinitC0, hinitQ⟩ := hinit q
        let coeff :=
          ricTowerCoeffs (Module.finrank ℝ E) q Bmax Cg Kq
        let Cq :=
          metricCovOrderEvolutionConstant coeff.slope coeff.offset
            (ψ - β) initC
        let Lq := 2 * (coeff.slope * Cq + coeff.offset)
        have hcoeff : 0 ≤ coeff.slope ∧ 0 ≤ coeff.offset := by
          dsimp only [coeff]
          exact ricCoeffs_nonneg (Module.finrank ℝ E) q Bmax Cg Kq
            hBmax hKq0
        have hCq0 : 0 ≤ Cq := by
          dsimp only [Cq, metricCovOrderEvolutionConstant]
          exact Real.sqrt_nonneg _
        have hLq0 : 0 ≤ Lq := by
          dsimp only [Lq]
          exact mul_nonneg (by norm_num)
            (add_nonneg (mul_nonneg hcoeff.1 hCq0) hcoeff.2)
        have htime : ∀ t ∈ Set.Icc β ψ, |t - t₀| ≤ ψ - β := by
          intro t ht
          rw [abs_le]
          constructor <;> nlinarith [ht.1, ht.2, ht₀.1, ht₀.2]
        have hcovAll :
            ∀ k : Nat,
              letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
                sourceDomTop (I := I) Φ k
              letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
                sourceDomCharted (I := I) Φ k
              letI : T2Space (SourceDomain (I := I) Φ k) :=
                sourceDomT2 (I := I) Φ k
              letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
                sourceDomSmooth (I := I) Φ k
              letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
                sourceDomSigmaOf (I := I) Φ k (hsrc k)
              ∀ t : ℝ, t ∈ Set.Icc β ψ →
                ∀ y : SourceDomain (I := I) Φ k,
                  metricCovDerivNorm (I := I) q
                      (srcMetric (I := I) Φ hsrc htgt k t)
                      (refRes (I := I) Φ R hsrc k) y ≤ Cq := by
          intro k
          letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
            sourceDomTop (I := I) Φ k
          letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
            sourceDomCharted (I := I) Φ k
          letI : T2Space (SourceDomain (I := I) Φ k) :=
            sourceDomT2 (I := I) Φ k
          letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
            sourceDomSmooth (I := I) Φ k
          letI : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
            IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k)
              (n := (∞ : WithTop ℕ∞)) (by decide)
          letI : IsManifold I 2 (SourceDomain (I := I) Φ k) :=
            IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k)
              (n := (∞ : WithTop ℕ∞)) (by decide)
          letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
              (SourceDomain (I := I) Φ k) := by
            change IsManifold I ∞ (SourceDomain (I := I) Φ k)
            infer_instance
          letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
            sourceDomSigmaOf (I := I) Φ k (hsrc k)
          have hDreg : ∀ {r : ℝ}, r ∈ X.D.regular →
              X.D.regular ∈ nhds r :=
            fun {r} hr => X.D.regular_isOpen.mem_nhds hr
          have hev := hevComp_of_solutions (I := I)
            (K := (Set.univ : Set (SourceDomain (I := I) Φ k)))
            (β := β) (ψ := ψ)
            (gSeq := fun _ t' ↦ srcMetric (I := I) Φ hsrc htgt k t')
            (gRef := refRes (I := I) Φ R hsrc k) (N := q)
            (fun _ ↦ X.D)
            (fun _ ↦ sourceFlow (I := I) Φ k (hsrc k) (htgt k))
            (fun _ ↦ isSolutionOn_sourceFlow (I := I) Φ k (hsrc k) (htgt k))
            (fun _ _ ↦ rfl)
            (fun _ ↦ hwin)
            (fun _ p' hp V x₀ ↦
              solnTowerSwap_reg (I := I) (refRes (I := I) Φ R hsrc k)
                (sourceFlow (I := I) Φ k (hsrc k) (htgt k))
                (isSolutionOn_sourceFlow (I := I) Φ k (hsrc k) (htgt k))
                q hDreg p' hp V x₀)
          have hstage := covOrderBound_stage_on (I := I)
            (U := (Set.univ : Set (SourceDomain (I := I) Φ k)))
            (β := β) (ψ := ψ) (t0 := t₀)
            (gSeq := fun _ t' ↦ srcMetric (I := I) Φ hsrc htgt k t')
            (gRef := refRes (I := I) Φ R hsrc k)
            isOpen_univ q hq_pos Bmax hBmax
            (fun _ t ht ↦ hequiv k t ht) Cg
            (fun r _hr1 hrq _ t ht y _hy => by
              simpa only [Cg, dif_pos hrq] using
                hcovPrev ⟨r, hrq⟩ k t ht y)
            Kq hKq0 (hShiQ k) ht₀
            (fun i y _hy t ht v => hev i y (Set.mem_univ y) t ht v)
            initC hinitC0 (fun _ y _hy => hinitQ k y)
            (ψ - β) htime
          intro t ht y
          simpa only [Cq, coeff] using
            hstage 0 t ht y (Set.mem_univ y)
        have hricAll :
            ∀ k : Nat,
              letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
                sourceDomTop (I := I) Φ k
              letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
                sourceDomCharted (I := I) Φ k
              letI : T2Space (SourceDomain (I := I) Φ k) :=
                sourceDomT2 (I := I) Φ k
              letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
                sourceDomSmooth (I := I) Φ k
              letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
                sourceDomSigmaOf (I := I) Φ k (hsrc k)
              ∀ t : ℝ, t ∈ Set.Icc β ψ →
                ∀ y : SourceDomain (I := I) Φ k,
                  Real.sqrt
                      (Tensor0SBundle.normSq0S (I := I)
                        (refRes (I := I) Φ R hsrc k) y (q + 2)
                        ((-2 : ℝ) •
                          nablaRicReal (I := I)
                            (fun _ t' ↦ srcMetric (I := I) Φ hsrc htgt k t')
                            (refRes (I := I) Φ R hsrc k) q 0 t y)) ≤ Lq := by
          intro k
          letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
            sourceDomTop (I := I) Φ k
          letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
            sourceDomCharted (I := I) Φ k
          letI : T2Space (SourceDomain (I := I) Φ k) :=
            sourceDomT2 (I := I) Φ k
          letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
            sourceDomSmooth (I := I) Φ k
          letI : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
            IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k)
              (n := (∞ : WithTop ℕ∞)) (by decide)
          letI : IsManifold I 2 (SourceDomain (I := I) Φ k) :=
            IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k)
              (n := (∞ : WithTop ℕ∞)) (by decide)
          letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
              (SourceDomain (I := I) Φ k) := by
            change IsManifold I ∞ (SourceDomain (I := I) Φ k)
            infer_instance
          letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
            sourceDomSigmaOf (I := I) Φ k (hsrc k)
          intro t ht y
          rw [sqrt_normSq0S_smul]
          have hfield :
              Real.sqrt
                  (Tensor0SBundle.normSq0S (I := I)
                    (refRes (I := I) Φ R hsrc k) y (q + 2)
                    (nablaRicReal (I := I)
                      (fun _ t' ↦ srcMetric (I := I) Φ hsrc htgt k t')
                      (refRes (I := I) Φ R hsrc k) q 0 t y)) ≤
                coeff.slope *
                    metricCovDerivNorm (I := I) q
                      (srcMetric (I := I) Φ hsrc htgt k t)
                      (refRes (I := I) Φ R hsrc k) y +
                  coeff.offset := by
            simpa only [coeff] using
              ric_bound_field_on (I := I)
                (U := (Set.univ : Set (SourceDomain (I := I) Φ k)))
                (β := β) (ψ := ψ)
                (gSeq := fun _ t' ↦ srcMetric (I := I) Φ hsrc htgt k t')
                (gRef := refRes (I := I) Φ R hsrc k)
                isOpen_univ q hq_pos Bmax hBmax
                (fun _ t' ht' ↦ hequiv k t' ht') Cg
                (fun r _hr1 hrq _ t' ht' y' _hy' => by
                  simpa only [Cg, dif_pos hrq] using
                    hcovPrev ⟨r, hrq⟩ k t' ht' y')
                Kq hKq0 (hShiQ k) 0 t ht y (Set.mem_univ y)
          have hbase :
              Real.sqrt
                  (Tensor0SBundle.normSq0S (I := I)
                    (refRes (I := I) Φ R hsrc k) y (q + 2)
                    (nablaRicReal (I := I)
                      (fun _ t' ↦ srcMetric (I := I) Φ hsrc htgt k t')
                      (refRes (I := I) Φ R hsrc k) q 0 t y)) ≤
                coeff.slope * Cq + coeff.offset :=
            hfield.trans <|
              by
                simpa only [add_comm] using
                  add_le_add_right
                    (mul_le_mul_of_nonneg_left (hcovAll k t ht y) hcoeff.1)
                    coeff.offset
          rw [show |(-2 : ℝ)| = 2 by norm_num]
          dsimp only [Lq]
          exact mul_le_mul_of_nonneg_left hbase (by norm_num)
        exact ⟨Cq, Lq, hCq0, hLq0, hcovAll, hricAll⟩
  refine
    { cov := ?_
      lip := ?_ }
  · intro q
    obtain ⟨Cq, _Lq, hCq, _hLq, hcov, _hric⟩ := hcore q
    exact ⟨Cq, hCq, hcov⟩
  · intro p
    have hricBound : ∀ q : Nat, ∃ Lq : ℝ, 0 ≤ Lq ∧
        ∀ k : Nat,
          letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
            sourceDomTop (I := I) Φ k
          letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
            sourceDomCharted (I := I) Φ k
          letI : T2Space (SourceDomain (I := I) Φ k) :=
            sourceDomT2 (I := I) Φ k
          letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
            sourceDomSmooth (I := I) Φ k
          letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
            sourceDomSigmaOf (I := I) Φ k (hsrc k)
          ∀ t : ℝ, t ∈ Set.Icc β ψ →
            ∀ y : SourceDomain (I := I) Φ k,
              Real.sqrt
                  (Tensor0SBundle.normSq0S (I := I)
                    (refRes (I := I) Φ R hsrc k) y (q + 2)
                    ((-2 : ℝ) •
                      nablaRicReal (I := I)
                        (fun _ t' ↦ srcMetric (I := I) Φ hsrc htgt k t')
                        (refRes (I := I) Φ R hsrc k) q 0 t y)) ≤ Lq := by
      intro q
      obtain ⟨_Cq, Lq, _hCq, hLq, _hcov, hric⟩ := hcore q
      exact ⟨Lq, hLq, hric⟩
    choose Lq hLq0 hric using hricBound
    let Lp : ℝ := ∑ q ∈ Finset.range (p + 1), Lq q
    have hLp0 : 0 ≤ Lp := by
      dsimp only [Lp]
      exact Finset.sum_nonneg fun q _ => hLq0 q
    refine ⟨Lp, hLp0, ?_⟩
    intro k
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
      sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
      sourceDomCharted (I := I) Φ k
    letI : T2Space (SourceDomain (I := I) Φ k) :=
      sourceDomT2 (I := I) Φ k
    letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
      sourceDomSmooth (I := I) Φ k
    letI : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
      IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k)
        (n := (∞ : WithTop ℕ∞)) (by decide)
    letI : IsManifold I 2 (SourceDomain (I := I) Φ k) :=
      IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k)
        (n := (∞ : WithTop ℕ∞)) (by decide)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
        (SourceDomain (I := I) Φ k) := by
      change IsManifold I ∞ (SourceDomain (I := I) Φ k)
      infer_instance
    letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
      sourceDomSigmaOf (I := I) Φ k (hsrc k)
    intro s t hs ht q hqp y
    have hDreg : ∀ {r : ℝ}, r ∈ X.D.regular → X.D.regular ∈ nhds r :=
      fun {r} hr => X.D.regular_isOpen.mem_nhds hr
    have hev := hevComp_of_solutions (I := I)
      (K := (Set.univ : Set (SourceDomain (I := I) Φ k)))
      (β := β) (ψ := ψ)
      (gSeq := fun _ t' ↦ srcMetric (I := I) Φ hsrc htgt k t')
      (gRef := refRes (I := I) Φ R hsrc k) (N := q)
      (fun _ ↦ X.D)
      (fun _ ↦ sourceFlow (I := I) Φ k (hsrc k) (htgt k))
      (fun _ ↦ isSolutionOn_sourceFlow (I := I) Φ k (hsrc k) (htgt k))
      (fun _ _ ↦ rfl)
      (fun _ ↦ hwin)
      (fun _ p' hp V x₀ ↦
        solnTowerSwap_reg (I := I) (refRes (I := I) Φ R hsrc k)
          (sourceFlow (I := I) Φ k (hsrc k) (htgt k))
          (isSolutionOn_sourceFlow (I := I) Φ k (hsrc k) (htgt k))
          q hDreg p' hp V x₀)
    have hqLip : metricDerivNorm (I := I) q
          (srcMetric (I := I) Φ hsrc htgt k s)
          (srcMetric (I := I) Φ hsrc htgt k t)
          (refRes (I := I) Φ R hsrc k) y ≤ Lq q * |s - t| := by
      exact timeLipschitz_of_hasDerivAt (I := I)
        (refRes (I := I) Φ R hsrc k) q
        (fun t' ↦ srcMetric (I := I) Φ hsrc htgt k t')
        (fun t' y' ↦ (-2 : ℝ) •
          nablaRicReal (I := I)
            (fun _ r ↦ srcMetric (I := I) Φ hsrc htgt k r)
            (refRes (I := I) Φ R hsrc k) q 0 t' y')
        Set.univ β ψ (Lq q)
        (fun y' _hy' t' ht' v ↦ hev 0 y' (Set.mem_univ y') t' ht' v)
        (fun y' _hy' t' ht' ↦ hric q k t' ht' y')
        s hs t ht y (Set.mem_univ y)
    have hqmem : q ∈ Finset.range (p + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le hqp)
    have hqle : Lq q ≤ Lp := by
      dsimp only [Lp]
      exact Finset.single_le_sum
        (fun r _hr ↦ hLq0 r) hqmem
    exact hqLip.trans
      (mul_le_mul_of_nonneg_right hqle (abs_nonneg (s - t)))

end HCGCompactness
end DifferentialGeometry
