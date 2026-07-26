import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConvFieldMain
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.WindowDataPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MovingShiPullback

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-!
# Brick 7a of the P4 conv engine — producers for the carried cited inputs

Bricks 4–5 (`ConvFieldAssembly.lean`, `ConvFieldMain.lean`) carry five cited inputs at
`gSeqExt`/source-flow granularity: `hbound` (uniform source lower bound), `hcovTail`
(uniform tail covariant bound), `hlipTail`/`hlipSrc` (time-Lipschitz at the two
granularities), and `hconv0` (pointwise time-0 convergence).  This file produces each of
them, verbatim, from honest THEOREM-LEVEL inputs stated against the comparison maps `Φ`
(ruling 5b: instantiate `Φ := pointedCGHMaps_of_atZero X L subseq rmaps` at Brick 7b):

* the eq-(3.3)-side window metric equivalence of the sequence flows against per-`k`
  references on the target side (`hequivT`, uniform majorant `B`/`Bmax`), plus the
  uniform relation of the transported reference to the restricted limit reference
  (`hrel`, constant `Crel`) — producers `hbound_of_equiv` and the shared transport
  `srcEquivOn`;
* the moving-Shi bounds for the sequence flows on the target side (`hShiT`) —
  transported by `srcShi` and consumed by `lipSrc_of_soln`;
* uniform source-side covariant bounds on the bump agreement diagonal (`hcovSrc`) —
  transferred locally, with no bump-collar derivative input, by
  `covTail_of_bounds`;
* the uniform source-granularity window Lipschitz bound on the bump agreement diagonal
  (`hlipG`) — producer `lipTail_of_src`;
* the time-0 seminorm convergence in `MetricSourceCPConvOn` shape (`hcp`, discharged
  from `mc.convergence` at 7b) — producer `conv0_of_cp`.

`lipSrc_of_soln` is fully produced (no Lipschitz citation): it runs the solution-driven
producers `hgLip0Sol`/`hgLipFinSol` on the Brick-2 flow `sourceFlow Φ k`, with their
`SolLipData` packs assembled per `k` from the transported equivalence and Shi bounds,
`covOrderBound_of_soln`, and compact initial bounds (`metricCovDerivNorm_bddOn`).

The general prelims include the metric-compatibility endpoint `covNorm_self_succ`
(`|∇_g^{a+1} g|_g = 0`, from `Tensor0SBundle.nabla_metric_zero`), the reverse triangle
`covNorm_le_add`, the explicit-constant order-0 bound `covNorm0_le`, and the
difference-slot congruence `derivNorm_congr_diff`.

See `ConvFieldInputs.md` for the route, the honesty discussion of each cited input, and
the recorded gaps.
-/

noncomputable section

open Set Function Filter Bundle Manifold Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow (SolutionOn IsSolutionOn)

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-! ### General prelims on a fixed manifold -/

section Prelims

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- The pointwise covariant metric norm is local with respect to restriction to
an open subtype. -/
theorem covNorm_restrictOpen
    (h gRef : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] (a : Nat) (x : U) :
    metricCovDerivNorm (I := I) a (h.restrictOpen (I := I) U)
        (gRef.restrictOpen (I := I) U) x =
      metricCovDerivNorm (I := I) a h gRef (x : M) := by
  have hcov :
      metricCovDeriv (I := I) (h.restrictOpen (I := I) U)
          (gRef.restrictOpen (I := I) U) a x =
        metricCovDeriv (I := I) h gRef a (x : M) := by
    ext slots
    exact metricCovDeriv_restrictOpen_apply (I := I) h gRef U a x slots
  unfold metricCovDerivNorm
  rw [normSq0S_restrictOpen_apply, hcov]

/-- Uniform metric equivalence is transitive, with multiplied constants. -/
theorem equivOn_trans {K : Set M} {g h f : SmoothRiemannianMetric I M} {C₁ C₂ : Real}
    (h₁ : MetricUniformEquivalentOn (I := I) K g h C₁)
    (h₂ : MetricUniformEquivalentOn (I := I) K h f C₂) :
    MetricUniformEquivalentOn (I := I) K g f (C₁ * C₂) := by
  obtain ⟨hC₁, hb₁⟩ := h₁
  obtain ⟨hC₂, hb₂⟩ := h₂
  have hC₁0 : (0 : Real) < C₁ := lt_of_lt_of_le one_pos hC₁
  have hC₂0 : (0 : Real) < C₂ := lt_of_lt_of_le one_pos hC₂
  refine ⟨by nlinarith, fun x hx v => ?_⟩
  obtain ⟨hg₁, hg₂⟩ := hb₁ x hx v
  obtain ⟨hh₁, hh₂⟩ := hb₂ x hx v
  constructor
  · have hstep : C₂⁻¹ * (C₁⁻¹ * g.inner x v v) <= C₂⁻¹ * h.inner x v v :=
      mul_le_mul_of_nonneg_left hg₁ (inv_nonneg.2 hC₂0.le)
    calc (C₁ * C₂)⁻¹ * g.inner x v v
        = C₂⁻¹ * (C₁⁻¹ * g.inner x v v) := by rw [mul_inv]; ring
      _ <= C₂⁻¹ * h.inner x v v := hstep
      _ <= f.inner x v v := hh₁
  · calc f.inner x v v <= C₂ * h.inner x v v := hh₂
      _ <= C₂ * (C₁ * g.inner x v v) := mul_le_mul_of_nonneg_left hg₂ hC₂0.le
      _ = (C₁ * C₂) * g.inner x v v := by ring

/-- **Reverse triangle for the one-metric covariant norm**:
`|∇^a g|_gRef ≤ |∇^a h|_gRef + |∇^a(g − h)|_gRef`. -/
theorem covNorm_le_add
    (a : Nat) (g h gRef : SmoothRiemannianMetric I M) (x : M) :
    metricCovDerivNorm (I := I) a g gRef x <=
      metricCovDerivNorm (I := I) a h gRef x + metricDerivNorm (I := I) a g h gRef x := by
  simp only [metricCovDerivNorm, metricDerivNorm, metricDiffCovDerivAt]
  have htri := sqrtNormSq0S_add_le (I := I) gRef x (a + 2)
    (metricCovDeriv (I := I) g gRef a x - metricCovDeriv (I := I) h gRef a x)
    (metricCovDeriv (I := I) h gRef a x)
  have hcancel : metricCovDeriv (I := I) g gRef a x - metricCovDeriv (I := I) h gRef a x
      + metricCovDeriv (I := I) h gRef a x = metricCovDeriv (I := I) g gRef a x :=
    sub_add_cancel _ _
  rw [hcancel] at htri
  linarith [htri]

private theorem mtf_eq_mt0S (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.metricTensorField (I := I) g x = metricTensor0S (I := I) g x := by
  ext v
  rw [Tensor0SBundle.metricTensorField_apply, metricTensor0S_apply]

/-- **Explicit-constant order-0 covariant bound from a pointwise metric equivalence.**
If `C⁻¹·h ≤ gRef ≤ C·h` pointwise at `x`, then `|h|_gRef(x) ≤ C·√(dim)`.  The constant
is explicit (this is `covZeroBdd`'s body with the constant exposed), which is what makes
the bound uniform across the varying source domains. -/
theorem covNorm0_le
    (h gRef : SmoothRiemannianMetric I M) (x : M) {C : Real} (hC1 : 1 <= C)
    (hpair : forall v : TangentSpace I x,
      C⁻¹ * h.inner x v v <= gRef.inner x v v /\ gRef.inner x v v <= C * h.inner x v v) :
    metricCovDerivNorm (I := I) 0 h gRef x <=
      C * Real.sqrt (Module.finrank Real E : Real) := by
  classical
  have hcomp := sqrt_normSq0S_le_of_metric_equiv
    (I := I) (g := h) (h := gRef) x 2 hC1 hpair (metricTensor0S (I := I) h x)
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) h x
  have hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) h x basis
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h' := metricInverseInBasis_of_orthonormal (I := I) h basis hON
    intro a b
    simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric] using h' a b
  have hself :
      Tensor0SBundle.normSq0S (I := I) h x 2 (metricTensor0S (I := I) h x)
        = (Module.finrank Real E : Real) := by
    have hcard := normSq0S_metricTensor0S_eq_card (I := I) h basis
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) hinv
    simpa using hcard
  have hcov :
      metricCovDerivNorm (I := I) 0 h gRef x =
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x 2
          (metricTensor0S (I := I) h x)) := by
    simp only [metricCovDerivNorm, metricCovDeriv_eq_covDerivOfField]
    change Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x 2
        (Tensor0SBundle.metricTensorField (I := I) h x)) =
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x 2
        (metricTensor0S (I := I) h x))
    rw [mtf_eq_mt0S]
  have hC0 : (0 : Real) <= C := le_trans zero_le_one hC1
  have hsq : Real.sqrt (C ^ 2) = C := by
    rw [Real.sqrt_sq hC0]
  rw [hcov]
  calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x 2 (metricTensor0S (I := I) h x))
      <= Real.sqrt (C ^ 2) * Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x 2
          (metricTensor0S (I := I) h x)) := hcomp
    _ = C * Real.sqrt (Module.finrank Real E : Real) := by rw [hsq, hself]

/-- Metric compatibility of the Koszul connection, first covariant derivative:
`∇_g g = 0` as a `(0,3)`-tensor field. -/
private theorem covDeriv_self_one (g : SmoothRiemannianMetric I M) :
    metricCovDeriv (I := I) g g 1 = 0 := by
  refine DFunLike.ext _ _ (fun x => ?_)
  refine ContinuousMultilinearMap.ext (fun slots => ?_)
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at_gen (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (slots 0)
  have hcons : Fin.cons (X x) (Fin.tail slots) = slots := by
    rw [hX]
    exact Fin.cons_self_tail slots
  have h1 := metricCovDeriv_one_apply_section (I := I) g g X x (Fin.tail slots)
  have h0 : Tensor0SBundle.nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
      (leviCivitaConnectionOfMetric (I := I) g) X
      (metricCovDeriv (I := I) g g 0) x = 0 := by
    have hbase : metricCovDeriv (I := I) g g 0
        = Tensor0SBundle.metricTensorField (I := I) g := rfl
    rw [hbase]
    exact Tensor0SBundle.nabla_metric_zero (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) g
      (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g) X x
  calc metricCovDeriv (I := I) g g 1 x slots
      = metricCovDeriv (I := I) g g 1 x (Fin.cons (X x) (Fin.tail slots)) := by rw [hcons]
    _ = Tensor0SBundle.nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
          (leviCivitaConnectionOfMetric (I := I) g) X
          (metricCovDeriv (I := I) g g 0) x (Fin.tail slots) := h1
    _ = 0 := by rw [h0]; rfl
    _ = (0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (1 + 2)) x slots := rfl

/-- Metric compatibility, all positive orders: `∇_g^{a+1} g = 0`. -/
theorem covDeriv_self_succ (g : SmoothRiemannianMetric I M) (a : Nat) :
    metricCovDeriv (I := I) g g (a + 1) = 0 := by
  induction a with
  | zero => exact covDeriv_self_one (I := I) g
  | succ n ih =>
      rw [metricCovDeriv_succ, ih]
      have hz := metricCovDerivStep_smul (I := I) g (0 : Real) (n + 1)
        (0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (n + 1 + 2))
      rw [zero_smul, zero_smul] at hz
      exact hz

/-- **Metric compatibility at norm level**: `|∇_g^{a+1} g|_g = 0` at every point. -/
theorem covNorm_self_succ (g : SmoothRiemannianMetric I M) (a : Nat) (x : M) :
    metricCovDerivNorm (I := I) (a + 1) g g x = 0 := by
  have h := covDeriv_self_succ (I := I) g a
  simp only [metricCovDerivNorm]
  have hx0 : metricCovDeriv (I := I) g g (a + 1) x
      = (0 : Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (a + 1 + 2) x) := by
    rw [h]; rfl
  rw [hx0]
  have hzero : (0 : Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (a + 1 + 2) x)
      = (0 : Real) • (0 : Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (a + 1 + 2) x) := (zero_smul _ _).symm
  rw [hzero, sqrt_normSq0S_smul]
  simp

/-- The MSM135 seminorm depends on its two metric slots only through the DIFFERENCE of
their metric tensor fields: pairs with equal differences have equal seminorms. -/
theorem derivNorm_congr_diff
    (a : Nat) (g₁ g₂ h₁ h₂ gRef : SmoothRiemannianMetric I M) (x : M)
    (hdiff : Tensor0SBundle.metricTensorField (I := I) g₁
        - Tensor0SBundle.metricTensorField (I := I) g₂
      = Tensor0SBundle.metricTensorField (I := I) h₁
        - Tensor0SBundle.metricTensorField (I := I) h₂) :
    metricDerivNorm (I := I) a g₁ g₂ gRef x = metricDerivNorm (I := I) a h₁ h₂ gRef x := by
  have key : forall f₁ f₂ : SmoothRiemannianMetric I M,
      metricCovDeriv (I := I) f₁ gRef a x - metricCovDeriv (I := I) f₂ gRef a x
        = (covDerivOfField (I := I) gRef
            (Tensor0SBundle.metricTensorField (I := I) f₁
              - Tensor0SBundle.metricTensorField (I := I) f₂) a) x := by
    intro f₁ f₂
    rw [covDerivOfField_sub, metricCovDeriv_eq_covDerivOfField (I := I) f₁ gRef a,
      metricCovDeriv_eq_covDerivOfField (I := I) f₂ gRef a]
    rfl
  unfold metricDerivNorm metricDiffCovDerivAt
  rw [key g₁ g₂, key h₁ h₂, hdiff]

end Prelims

/-! ### Transports to the source domains -/

section ConvField

variable {X : PointedFlowSeq (I := I)}
variable {P : PointedRiemannianManifold (I := I)}
variable {subseq : Nat -> Nat}
variable (Φ : PointedCGHMaps (I := I) X P subseq)

/-- The per-`k` reference metric on the `k`th sequence manifold, transported to the
source domain: restrict to the open target, then pull back along `sourceTargetDiff`.
This mirrors the `sourceFlow` construction, so the transported window equivalence
lands on `srcMetric` definitionally. -/
noncomputable def tgtRefSrc
    (gRefT : forall k : Nat,
      letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
      letI : IsManifold I ∞ (X.term (subseq k)).M := (X.term (subseq k)).smooth
      SmoothRiemannianMetric I ((X.term (subseq k)).M))
    (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ) (k : Nat) :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
    SmoothRiemannianMetric I (SourceDomain (I := I) Φ k) := by
  letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
  letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
  letI : IsManifold I ∞ (X.term (subseq k)).M := (X.term (subseq k)).smooth
  letI : SigmaCompactSpace (X.term (subseq k)).M := (X.term (subseq k)).sigmaCompact
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) := sourceDomSigmaOf (I := I) Φ k (hsrc k)
  letI : SigmaCompactSpace ↥(targetOpen (I := I) Φ k) := targetDomSigmaOf (I := I) Φ k (htgt k)
  letI : T2Space ↥(targetOpen (I := I) Φ k) := targetDomT2 (I := I) Φ k
  letI : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
  letI : ChartedSpace H (TargetDomain (I := I) Φ k) := targetDomCharted (I := I) Φ k
  letI : IsManifold I ∞ (TargetDomain (I := I) Φ k) := targetDomSmooth (I := I) Φ k
  letI : SigmaCompactSpace (TargetDomain (I := I) Φ k) := targetDomSigmaOf (I := I) Φ k (htgt k)
  letI : T2Space (TargetDomain (I := I) Φ k) := targetDomT2 (I := I) Φ k
  exact Diffeomorph.pullbackMetric (I := I)
    ((gRefT k).restrictOpen (I := I) (targetOpen (I := I) Φ k))
    (sourceTargetDiff (I := I) Φ k)

/-- **The transported window equivalence on the source domains.**  From the cited
target-side window equivalence `hequivT` (per-`k` reference `gRefT k`, uniform majorant
`B`) and the cited uniform relation `hrel` between the transported reference and the
restricted limit reference `refRes`, the source-flow metrics are uniformly equivalent to
`refRes` on the whole source domain, with the composed constant `Crel * B t`. -/
theorem srcEquivOn
    (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (β ψ : Real)
    (gRefT : forall k : Nat,
      letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
      letI : IsManifold I ∞ (X.term (subseq k)).M := (X.term (subseq k)).smooth
      SmoothRiemannianMetric I ((X.term (subseq k)).M))
    (B : Real -> Real) (Crel : Real)
    (hequivT : forall k : Nat,
      letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
      letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
      letI : IsManifold I ∞ (X.term (subseq k)).M := (X.term (subseq k)).smooth
      letI : SigmaCompactSpace (X.term (subseq k)).M := (X.term (subseq k)).sigmaCompact
      MetricUniformEquivalentOnWindow (I := I) (Φ.target k) β ψ (gRefT k)
        (fun _ t => (X.term (subseq k)).S.family.metric t) B)
    (hrel : forall k : Nat,
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
      letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
      MetricUniformEquivalentOn (I := I)
        (Set.univ : Set (SourceDomain (I := I) Φ k))
        (refRes (I := I) Φ R hsrc k)
        (tgtRefSrc (I := I) Φ gRefT hsrc htgt k) Crel)
    (k : Nat) (t : Real) (ht : t ∈ Set.Icc β ψ) :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
    letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
    MetricUniformEquivalentOn (I := I)
      (Set.univ : Set (SourceDomain (I := I) Φ k))
      (refRes (I := I) Φ R hsrc k)
      (srcMetric (I := I) Φ hsrc htgt k t) (Crel * B t) := by
  letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
  letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
  letI : IsManifold I ∞ (X.term (subseq k)).M := (X.term (subseq k)).smooth
  letI : SigmaCompactSpace (X.term (subseq k)).M := (X.term (subseq k)).sigmaCompact
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) := sourceDomSigmaOf (I := I) Φ k (hsrc k)
  letI : SigmaCompactSpace ↥(targetOpen (I := I) Φ k) := targetDomSigmaOf (I := I) Φ k (htgt k)
  letI : T2Space ↥(targetOpen (I := I) Φ k) := targetDomT2 (I := I) Φ k
  letI : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
  letI : ChartedSpace H (TargetDomain (I := I) Φ k) := targetDomCharted (I := I) Φ k
  letI : IsManifold I ∞ (TargetDomain (I := I) Φ k) := targetDomSmooth (I := I) Φ k
  letI : SigmaCompactSpace (TargetDomain (I := I) Φ k) := targetDomSigmaOf (I := I) Φ k (htgt k)
  letI : T2Space (TargetDomain (I := I) Φ k) := targetDomT2 (I := I) Φ k
  -- restrict the target-side equivalence to the open target
  have h1 := metricUniformEquivalentOnWindow_restrictOpen (I := I)
    (K := Φ.target k) (β := β) (ψ := ψ) (gRef := gRefT k)
    (gSeq := fun _ t => (X.term (subseq k)).S.family.metric t) (B := B)
    (hequivT k) (targetOpen (I := I) Φ k)
    (V := (Set.univ : Set ↥(targetOpen (I := I) Φ k)))
    (fun x _ => x.2)
  -- pull back along the source-target diffeomorphism
  have h2 := metricUniformEquivalentOnWindow_pullback (I := I)
    (K := (Set.univ : Set ↥(targetOpen (I := I) Φ k)))
    (β := β) (ψ := ψ)
    (gRef := (gRefT k).restrictOpen (I := I) (targetOpen (I := I) Φ k))
    (gSeq := fun _ t =>
      ((X.term (subseq k)).S.family.metric t).restrictOpen (I := I) (targetOpen (I := I) Φ k))
    (B := B) h1 (sourceTargetDiff (I := I) Φ k)
    (V := (Set.univ : Set (SourceDomain (I := I) Φ k)))
    (fun _ _ => Set.mem_univ _)
  have h2t := h2 0 t ht
  exact equivOn_trans (I := I) (hrel k) h2t

/-- **The transported moving-Shi bound on the source domains.**  The cited target-side
`MovingShiBoundOn` transports to the source-flow metrics with the same constant, by
`movingShiBoundOn_restrictOpen` followed by `movingShiBoundOn_pullback`. -/
theorem srcShi
    (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (β ψ : Real) (N : Nat) (KShi : Real)
    (hShiT : forall k : Nat,
      letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
      letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
      letI : IsManifold I ∞ (X.term (subseq k)).M := (X.term (subseq k)).smooth
      letI : SigmaCompactSpace (X.term (subseq k)).M := (X.term (subseq k)).sigmaCompact
      MovingShiBoundOn (I := I) (Φ.target k) β ψ
        (fun _ t => (X.term (subseq k)).S.family.metric t) N KShi)
    (k : Nat) :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
    letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
    letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) := sourceDomSigmaOf (I := I) Φ k (hsrc k)
    MovingShiBoundOn (I := I) (Set.univ : Set (SourceDomain (I := I) Φ k)) β ψ
      (fun _ t => srcMetric (I := I) Φ hsrc htgt k t) N KShi := by
  letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
  letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
  letI : IsManifold I ∞ (X.term (subseq k)).M := (X.term (subseq k)).smooth
  letI : SigmaCompactSpace (X.term (subseq k)).M := (X.term (subseq k)).sigmaCompact
  letI : IsManifold I 1 (X.term (subseq k)).M :=
    IsManifold.of_le (I := I) (M := (X.term (subseq k)).M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) <= ∞)
  letI : IsManifold I 2 (X.term (subseq k)).M :=
    IsManifold.of_le (I := I) (M := (X.term (subseq k)).M) (n := (∞ : WithTop ℕ∞))
      (by decide : (2 : WithTop ℕ∞) <= ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term (subseq k)).M := by
    change IsManifold I ∞ (X.term (subseq k)).M
    infer_instance
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) := sourceDomSigmaOf (I := I) Φ k (hsrc k)
  letI : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) <= ∞)
  letI : IsManifold I 2 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
      (by decide : (2 : WithTop ℕ∞) <= ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (SourceDomain (I := I) Φ k) := by
    change IsManifold I ∞ (SourceDomain (I := I) Φ k)
    infer_instance
  letI : SigmaCompactSpace ↥(targetOpen (I := I) Φ k) := targetDomSigmaOf (I := I) Φ k (htgt k)
  letI : T2Space ↥(targetOpen (I := I) Φ k) := targetDomT2 (I := I) Φ k
  letI : IsManifold I 1 ↥(targetOpen (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := ↥(targetOpen (I := I) Φ k)) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) <= ∞)
  letI : IsManifold I 2 ↥(targetOpen (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := ↥(targetOpen (I := I) Φ k)) (n := (∞ : WithTop ℕ∞))
      (by decide : (2 : WithTop ℕ∞) <= ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) ↥(targetOpen (I := I) Φ k) := by
    change IsManifold I ∞ ↥(targetOpen (I := I) Φ k)
    infer_instance
  letI : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
  letI : ChartedSpace H (TargetDomain (I := I) Φ k) := targetDomCharted (I := I) Φ k
  letI : IsManifold I ∞ (TargetDomain (I := I) Φ k) := targetDomSmooth (I := I) Φ k
  letI : SigmaCompactSpace (TargetDomain (I := I) Φ k) := targetDomSigmaOf (I := I) Φ k (htgt k)
  letI : T2Space (TargetDomain (I := I) Φ k) := targetDomT2 (I := I) Φ k
  have h1 := movingShiBoundOn_restrictOpen (I := I)
    (gSeq := fun _ t => (X.term (subseq k)).S.family.metric t)
    (targetOpen (I := I) Φ k) (Φ.target k) β ψ N KShi
    (Set.univ : Set ↥(targetOpen (I := I) Φ k))
    (fun x _ => x.2) (hShiT k)
  have h2 := movingShiBoundOn_pullback (I := I)
    (gSeq := fun _ t =>
      ((X.term (subseq k)).S.family.metric t).restrictOpen (I := I) (targetOpen (I := I) Φ k))
    (sourceTargetDiff (I := I) Φ k)
    (Set.univ : Set (TargetDomain (I := I) Φ k)) β ψ N KShi
    (Set.univ : Set (SourceDomain (I := I) Φ k))
    (fun _ _ => Set.mem_univ _) h1
  exact h2

/-! ### Producer 1: `hbound` (the uniform source lower bound) -/

/-- **Producer for the `hbound` carried input of `hlow_gSeqExt`/`convOut`.**  From the
cited target-side window equivalence and the cited reference relation, the source-flow
metrics are bounded below by `(Crel * Bmax)⁻¹ · R` on the whole source domains,
uniformly in `k` and in window time.  The conclusion is verbatim the `hbound` hypothesis
with `cLow := (Crel * Bmax)⁻¹` (positive since `Crel, Bmax ≥ 1`). -/
theorem hbound_of_equiv
    (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (β ψ : Real)
    (gRefT : forall k : Nat,
      letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
      letI : IsManifold I ∞ (X.term (subseq k)).M := (X.term (subseq k)).smooth
      SmoothRiemannianMetric I ((X.term (subseq k)).M))
    (B : Real -> Real) (Crel Bmax : Real)
    (hBmax : forall t : Real, t ∈ Set.Icc β ψ -> B t <= Bmax)
    (hCrel1 : 1 <= Crel)
    (hequivT : forall k : Nat,
      letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
      letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
      letI : IsManifold I ∞ (X.term (subseq k)).M := (X.term (subseq k)).smooth
      letI : SigmaCompactSpace (X.term (subseq k)).M := (X.term (subseq k)).sigmaCompact
      MetricUniformEquivalentOnWindow (I := I) (Φ.target k) β ψ (gRefT k)
        (fun _ t => (X.term (subseq k)).S.family.metric t) B)
    (hrel : forall k : Nat,
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
      letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
      MetricUniformEquivalentOn (I := I)
        (Set.univ : Set (SourceDomain (I := I) Φ k))
        (refRes (I := I) Φ R hsrc k)
        (tgtRefSrc (I := I) Φ gRefT hsrc htgt k) Crel) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    forall (k : Nat) (t : Real), t ∈ Set.Icc β ψ ->
      forall (y : SourceDomain (I := I) Φ k)
        (v : letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k;
          letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k;
          TangentSpace I y),
        (Crel * Bmax)⁻¹ * R.inner (y : P.M) v v <=
          letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
          letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
          letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
          (srcMetric (I := I) Φ hsrc htgt k t).inner y v v := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  intro k t ht y v
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  have hEq := srcEquivOn (I := I) Φ R hsrc htgt β ψ gRefT B Crel hequivT hrel k t ht
  have hBt1 : (1 : Real) <= B t := (hequivT k 0 t ht).1
  have hlow := (hEq.2 y (Set.mem_univ y) v).1
  -- `refRes.inner y v v = R.inner (y : P.M) v v` definitionally
  have hRef : (refRes (I := I) Φ R hsrc k).inner y v v = R.inner (y : P.M) v v := rfl
  rw [hRef] at hlow
  have hRnn : 0 <= R.inner (y : P.M) v v := by
    by_cases hv : v = 0
    · subst hv; simp
    · exact (R.pos (y : P.M) v hv).le
  have hmono : (Crel * Bmax)⁻¹ * R.inner (y : P.M) v v
      <= (Crel * B t)⁻¹ * R.inner (y : P.M) v v := by
    have h1 : (0 : Real) < Crel * B t := by nlinarith
    have h2 : Crel * B t <= Crel * Bmax :=
      mul_le_mul_of_nonneg_left (hBmax t ht) (le_trans zero_le_one hCrel1)
    have hinv : (Crel * Bmax)⁻¹ <= (Crel * B t)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le h1 h2
    exact mul_le_mul_of_nonneg_right hinv hRnn
  exact le_trans hmono hlow

/-! ### Producer 5: `hconv0` (the pointwise time-0 convergence) -/

/-- **Producer for the `hconv0` hypothesis of `gInf_zero_eq`.**  From the time-0
seminorm convergence in `MetricSourceCPConvOn` shape — order-0 sup-seminorm smallness of
`(srcMetric k 0, resSrc g0, refRes)` on the part of each compact inside the `k`th source
domain, together with the eventual containment `K ⊆ Φ.source k` (7b discharger:
`mc.convergence`) — the pulled-back time-0 metrics converge pointwise to `g0` at every
`(x, v, w)`.  The conclusion is verbatim the `hconv0` hypothesis of `gInf_zero_eq`. -/
theorem conv0_of_cp
    (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (g0 : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (hcp : letI : TopologicalSpace P.M := P.topology;
        letI : ChartedSpace H P.M := P.charted; letI : T2Space P.M := P.t2;
        letI : IsManifold I ∞ P.M := P.smooth; letI : SigmaCompactSpace P.M := P.sigmaCompact;
      forall K : Set P.M, IsCompact K -> forall ε : Real, 0 < ε ->
        exists k0 : Nat, forall k : Nat, k0 <= k -> K ⊆ Φ.source k /\
          (letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
           letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
           letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
           letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
           letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
             sourceDomSigmaOf (I := I) Φ k (hsrc k)
           metricDerivNormSupOn (I := I) (sourceCompactSet (I := I) Φ k K) 0
             (srcMetric (I := I) Φ hsrc htgt k 0)
             (resSrc (I := I) Φ hsrc k g0)
             (refRes (I := I) Φ R hsrc k) < ε)) :
    letI : TopologicalSpace P.M := P.topology;
    letI : ChartedSpace H P.M := P.charted; letI : T2Space P.M := P.t2;
    letI : IsManifold I ∞ P.M := P.smooth; letI : SigmaCompactSpace P.M := P.sigmaCompact;
    forall (x : P.M) (v w : TangentSpace I x) (ε : Real), 0 < ε ->
      exists k0 : Nat, forall k : Nat, k0 <= k -> forall hx : x ∈ Φ.source k,
        |(letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
          letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
          letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
          (srcMetric (I := I) Φ hsrc htgt k 0).inner ⟨x, hx⟩ v w)
          - g0.inner x v w| < ε := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  intro x v w ε hε
  -- the fixed reference quadratic factor at `x`
  have hRnn : forall u : TangentSpace I x, 0 <= R.inner x u u := by
    intro u
    by_cases hu : u = 0
    · subst hu; simp
    · exact (R.pos x u hu).le
  set n : Real := (Module.finrank Real E : Real) with hn
  set Cx : Real := R.inner x (v + w) (v + w) + R.inner x v v + R.inner x w w with hCx
  have hn0 : 0 <= n := by rw [hn]; exact Nat.cast_nonneg _
  have hCx0 : 0 <= Cx := by
    have h1 := hRnn (v + w)
    have h2 := hRnn v
    have h3 := hRnn w
    rw [hCx]; linarith
  have hden : (0 : Real) < n * Cx + 1 := by positivity
  obtain ⟨k0, hk0⟩ := hcp {x} isCompact_singleton (ε / (n * Cx + 1)) (by positivity)
  refine ⟨k0, fun k hk hx => ?_⟩
  obtain ⟨-, hsup⟩ := hk0 k hk
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) := sourceDomSigmaOf (I := I) Φ k (hsrc k)
  letI : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) <= ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (SourceDomain (I := I) Φ k) := by
    change IsManifold I ∞ (SourceDomain (I := I) Φ k)
    infer_instance
  -- the singleton sup set is the singleton of the lifted point
  have hsing : sourceCompactSet (I := I) Φ k ({x} : Set P.M)
      = ({(⟨x, hx⟩ : SourceDomain (I := I) Φ k)} : Set (SourceDomain (I := I) Φ k)) := by
    ext z
    constructor
    · intro hz
      have hzx : (z : P.M) = x := hz
      exact Subtype.ext hzx
    · intro hz
      have hzx : z = (⟨x, hx⟩ : SourceDomain (I := I) Φ k) := hz
      change (z : P.M) ∈ ({x} : Set P.M)
      rw [hzx]
      rfl
  rw [hsing] at hsup
  -- pointwise order-0 smallness at the lifted point
  have hpt := derivNorm_le_sup_sing (I := I) 0
    (srcMetric (I := I) Φ hsrc htgt k 0)
    (resSrc (I := I) Φ hsrc k g0)
    (refRes (I := I) Φ R hsrc k)
    (⟨x, hx⟩ : SourceDomain (I := I) Φ k) 0 le_rfl
  have hlt : metricDerivNorm (I := I) 0
      (srcMetric (I := I) Φ hsrc htgt k 0)
      (resSrc (I := I) Φ hsrc k g0)
      (refRes (I := I) Φ R hsrc k)
      (⟨x, hx⟩ : SourceDomain (I := I) Φ k) < ε / (n * Cx + 1) :=
    lt_of_le_of_lt hpt hsup
  -- convert to the inner-product difference via the polarized bound
  have hbound := metricInnerApply_diff_le (I := I)
    (srcMetric (I := I) Φ hsrc htgt k 0)
    (resSrc (I := I) Φ hsrc k g0)
    (refRes (I := I) Φ R hsrc k)
    (⟨x, hx⟩ : SourceDomain (I := I) Φ k) v w
  have hres0 : (resSrc (I := I) Φ hsrc k g0).inner (⟨x, hx⟩ : SourceDomain (I := I) Φ k) v w
      = g0.inner x v w := rfl
  have hrefsum : (refRes (I := I) Φ R hsrc k).inner
        (⟨x, hx⟩ : SourceDomain (I := I) Φ k) (v + w) (v + w)
      + (refRes (I := I) Φ R hsrc k).inner (⟨x, hx⟩ : SourceDomain (I := I) Φ k) v v
      + (refRes (I := I) Φ R hsrc k).inner (⟨x, hx⟩ : SourceDomain (I := I) Φ k) w w
      = Cx := rfl
  have hnfin : (Module.finrank Real
      (TangentSpace I (⟨x, hx⟩ : SourceDomain (I := I) Φ k)) : Real) = n := by
    rw [hn]
    norm_cast
  rw [hres0, hrefsum, hnfin] at hbound
  have h1 : n * metricDerivNorm (I := I) 0
        (srcMetric (I := I) Φ hsrc htgt k 0)
        (resSrc (I := I) Φ hsrc k g0)
        (refRes (I := I) Φ R hsrc k)
        (⟨x, hx⟩ : SourceDomain (I := I) Φ k) * Cx
      <= n * (ε / (n * Cx + 1)) * Cx := by
    have hd0 : 0 <= metricDerivNorm (I := I) 0
        (srcMetric (I := I) Φ hsrc htgt k 0)
        (resSrc (I := I) Φ hsrc k g0)
        (refRes (I := I) Φ R hsrc k)
        (⟨x, hx⟩ : SourceDomain (I := I) Φ k) := Real.sqrt_nonneg _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlt.le hn0) hCx0
  have h2 : n * (ε / (n * Cx + 1)) * Cx < ε := by
    have hlt2 : n * Cx < n * Cx + 1 := by linarith
    have hεD : (0 : Real) < ε / (n * Cx + 1) := by positivity
    calc n * (ε / (n * Cx + 1)) * Cx
        = (n * Cx) * (ε / (n * Cx + 1)) := by ring
      _ < (n * Cx + 1) * (ε / (n * Cx + 1)) := mul_lt_mul_of_pos_right hlt2 hεD
      _ = ε := by
          rw [mul_comm]
          exact div_mul_cancel₀ ε hden.ne'
  exact lt_of_le_of_lt (le_trans hbound h1) h2

/-! ### Producer 3: `hlipTail` (the tail time-Lipschitz bound at `gSeqExt` granularity) -/

/-- **Producer for the `hlipTail` carried input of `hgLip_gSeqExt`/`convOut`.**  From the
cited uniform source-granularity window Lipschitz bound on the bump agreement diagonal
(`hlipG` — uniform in `k` over the points of `bf.grow k`, in-tree per-`k` realizability
demonstrated by `lipSrc_of_soln`), the same bound holds verbatim at `gSeqExt` granularity
on `bf.grow k`, with the SAME constant: on the `chi_one` open the bump is identically `1`,
so the difference tensor fields agree (`derivNorm_congr_diff`) after localizing twice by
`metricDerivNorm_restrictOpen`. -/
theorem lipTail_of_src
    (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (β ψ : Real)
    (hlipG : letI : TopologicalSpace P.M := P.topology;
        letI : ChartedSpace H P.M := P.charted; letI : T2Space P.M := P.t2;
        letI : IsManifold I ∞ P.M := P.smooth; letI : SigmaCompactSpace P.M := P.sigmaCompact;
      forall p : Nat, exists Lt : Real, 0 <= Lt /\
        forall (k : Nat) (s t : Real), s ∈ Set.Icc β ψ -> t ∈ Set.Icc β ψ ->
          forall a : Nat, a <= p ->
            forall y : SourceDomain (I := I) Φ k, (y : P.M) ∈ bf.grow k ->
              letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
              letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
              letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
              letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
              letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
                sourceDomSigmaOf (I := I) Φ k (hsrc k)
              metricDerivNorm (I := I) a (srcMetric (I := I) Φ hsrc htgt k s)
                (srcMetric (I := I) Φ hsrc htgt k t)
                (refRes (I := I) Φ R hsrc k) y <= Lt * |s - t|) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    forall p : Nat, exists Lt : Real, 0 <= Lt /\
      forall (k : Nat) (s t : Real), s ∈ Set.Icc β ψ -> t ∈ Set.Icc β ψ ->
        forall a : Nat, a <= p -> forall z : P.M, z ∈ bf.grow k ->
          metricDerivNorm (I := I) a (gSeqExt (I := I) Φ R bf hsrc htgt k s)
            (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z <= Lt * |s - t| := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  intro p
  obtain ⟨Lt, hLt0, hLt⟩ := hlipG p
  refine ⟨Lt, hLt0, fun k s t hs ht a ha z hzgrow => ?_⟩
  have hzsrc : z ∈ Φ.source k := bf.grow_subset k hzgrow
  -- source-domain instances, at both spellings
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) := sourceDomSigmaOf (I := I) Φ k (hsrc k)
  letI : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) <= ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (SourceDomain (I := I) Φ k) := by
    change IsManifold I ∞ (SourceDomain (I := I) Φ k); infer_instance
  letI : SigmaCompactSpace ↥(sourceOpen (I := I) Φ k) := sourceDomSigmaOf (I := I) Φ k (hsrc k)
  letI : T2Space ↥(sourceOpen (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  set y : SourceDomain (I := I) Φ k := ⟨z, hzsrc⟩ with hydef
  -- the open where the bump is 1, lifted into the source domain
  obtain ⟨W, hWopen, hgrowW, hW1⟩ := bf.chi_one k
  set O : TopologicalSpace.Opens (SourceDomain (I := I) Φ k) :=
    ⟨Subtype.val ⁻¹' W, hWopen.preimage continuous_subtype_val⟩ with hOdef
  letI : ChartedSpace H ↥O :=
    TopologicalSpace.Opens.instChartedSpace (H := H) (M := SourceDomain (I := I) Φ k) (s := O)
  letI : IsManifold I ∞ ↥O := { O.instHasGroupoid (contDiffGroupoid ∞ I) with }
  letI : SigmaCompactSpace ↥O := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I O.isOpen)
  letI : IsManifold I 1 ↥O :=
    IsManifold.of_le (I := I) (M := ↥O) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) <= ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) ↥O := by
    change IsManifold I ∞ ↥O; infer_instance
  have hyO : y ∈ O := hgrowW hzgrow
  -- the O-restricted difference fields agree (the bump is 1 on W)
  have hdiffO : Tensor0SBundle.metricTensorField (I := I)
        (((gSeqExt (I := I) Φ R bf hsrc htgt k s).restrictOpen (I := I)
          (sourceOpen (I := I) Φ k)).restrictOpen (I := I) O)
      - Tensor0SBundle.metricTensorField (I := I)
        (((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I)
          (sourceOpen (I := I) Φ k)).restrictOpen (I := I) O)
      = Tensor0SBundle.metricTensorField (I := I)
          ((srcMetric (I := I) Φ hsrc htgt k s).restrictOpen (I := I) O)
        - Tensor0SBundle.metricTensorField (I := I)
          ((srcMetric (I := I) Φ hsrc htgt k t).restrictOpen (I := I) O) := by
    refine DFunLike.ext _ _ (fun w => ?_)
    refine ContinuousMultilinearMap.ext (fun vs => ?_)
    have hwW : (((w : SourceDomain (I := I) Φ k)) : P.M) ∈ W := w.2
    have hwsrc : (((w : SourceDomain (I := I) Φ k)) : P.M) ∈ Φ.source k :=
      (w : SourceDomain (I := I) Φ k).2
    change (Tensor0SBundle.metricTensorField (I := I)
          (((gSeqExt (I := I) Φ R bf hsrc htgt k s).restrictOpen (I := I)
            (sourceOpen (I := I) Φ k)).restrictOpen (I := I) O) w
        - Tensor0SBundle.metricTensorField (I := I)
          (((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I)
            (sourceOpen (I := I) Φ k)).restrictOpen (I := I) O) w) vs
      = (Tensor0SBundle.metricTensorField (I := I)
            ((srcMetric (I := I) Φ hsrc htgt k s).restrictOpen (I := I) O) w
        - Tensor0SBundle.metricTensorField (I := I)
            ((srcMetric (I := I) Φ hsrc htgt k t).restrictOpen (I := I) O) w) vs
    rw [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.sub_apply]
    change
      (gSeqExt (I := I) Φ R bf hsrc htgt k s).inner
          (((w : SourceDomain (I := I) Φ k)) : P.M) (vs 0) (vs 1)
        - (gSeqExt (I := I) Φ R bf hsrc htgt k t).inner
          (((w : SourceDomain (I := I) Φ k)) : P.M) (vs 0) (vs 1)
        = (srcMetric (I := I) Φ hsrc htgt k s).inner
            (w : SourceDomain (I := I) Φ k) (vs 0) (vs 1)
          - (srcMetric (I := I) Φ hsrc htgt k t).inner
            (w : SourceDomain (I := I) Φ k) (vs 0) (vs 1)
    rw [gSeqExt_inner_of_mem (I := I) Φ R bf hsrc htgt k s
        (((w : SourceDomain (I := I) Φ k)) : P.M) hwsrc (vs 0) (vs 1),
      gSeqExt_inner_of_mem (I := I) Φ R bf hsrc htgt k t
        (((w : SourceDomain (I := I) Φ k)) : P.M) hwsrc (vs 0) (vs 1),
      hW1 _ hwW]
    simp
  -- localize, swap, and come back
  calc metricDerivNorm (I := I) a (gSeqExt (I := I) Φ R bf hsrc htgt k s)
        (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z
      = metricDerivNorm (I := I) a
          ((gSeqExt (I := I) Φ R bf hsrc htgt k s).restrictOpen (I := I)
            (sourceOpen (I := I) Φ k))
          ((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I)
            (sourceOpen (I := I) Φ k))
          (refRes (I := I) Φ R hsrc k) y :=
        (metricDerivNorm_restrictOpen (I := I) _ _ _ (sourceOpen (I := I) Φ k) a y).symm
    _ = metricDerivNorm (I := I) a
          (((gSeqExt (I := I) Φ R bf hsrc htgt k s).restrictOpen (I := I)
            (sourceOpen (I := I) Φ k)).restrictOpen (I := I) O)
          (((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I)
            (sourceOpen (I := I) Φ k)).restrictOpen (I := I) O)
          ((refRes (I := I) Φ R hsrc k).restrictOpen (I := I) O)
          (⟨y, hyO⟩ : ↥O) :=
        (metricDerivNorm_restrictOpen (I := I) _ _ _ O a (⟨y, hyO⟩ : ↥O)).symm
    _ = metricDerivNorm (I := I) a
          ((srcMetric (I := I) Φ hsrc htgt k s).restrictOpen (I := I) O)
          ((srcMetric (I := I) Φ hsrc htgt k t).restrictOpen (I := I) O)
          ((refRes (I := I) Φ R hsrc k).restrictOpen (I := I) O)
          (⟨y, hyO⟩ : ↥O) :=
        derivNorm_congr_diff (I := I) a _ _ _ _ _ (⟨y, hyO⟩ : ↥O) hdiffO
    _ = metricDerivNorm (I := I) a (srcMetric (I := I) Φ hsrc htgt k s)
          (srcMetric (I := I) Φ hsrc htgt k t)
          (refRes (I := I) Φ R hsrc k) y :=
        metricDerivNorm_restrictOpen (I := I) _ _ _ O a (⟨y, hyO⟩ : ↥O)
    _ <= Lt * |s - t| := hLt k s t hs ht a ha y hzgrow

/-! ### Producer 2: `hcovTail` (the uniform covariant bound at `gSeqExt` granularity) -/

/-- **Producer for the `hcovTail` input of `hbdd_gSeqExt`/`convOut`.**
A uniform source-flow covariant bound on the agreement region `bf.grow k`
transfers to the bump extension with the same constant.  The bump is identically
one on an open neighborhood of `bf.grow k`, so restriction locality identifies
the two covariant metric towers pointwise. -/
theorem covTail_of_bounds
    (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (β ψ : Real)
    (hcovSrc : letI : TopologicalSpace P.M := P.topology;
        letI : ChartedSpace H P.M := P.charted; letI : T2Space P.M := P.t2;
        letI : IsManifold I ∞ P.M := P.smooth; letI : SigmaCompactSpace P.M := P.sigmaCompact;
      forall q : Nat, exists C : Real, 0 <= C /\
        forall (k : Nat) (t : Real), t ∈ Set.Icc β ψ ->
          forall y : SourceDomain (I := I) Φ k, (y : P.M) ∈ bf.grow k ->
            letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
            letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
            letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
              sourceDomSigmaOf (I := I) Φ k (hsrc k)
            metricCovDerivNorm (I := I) q (srcMetric (I := I) Φ hsrc htgt k t)
              (refRes (I := I) Φ R hsrc k) y <= C) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    forall q : Nat, exists C : Real, forall (k : Nat) (t : Real), t ∈ Set.Icc β ψ ->
      forall z : P.M, z ∈ bf.grow k ->
        metricCovDerivNorm (I := I) q
          (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z <= C := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  intro q
  obtain ⟨C, _hC0, hC⟩ := hcovSrc q
  refine ⟨C, fun k t ht z hzgrow => ?_⟩
  have hzsrc : z ∈ Φ.source k := bf.grow_subset k hzgrow
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
    sourceDomSigmaOf (I := I) Φ k (hsrc k)
  letI : SigmaCompactSpace ↥(sourceOpen (I := I) Φ k) :=
    sourceDomSigmaOf (I := I) Φ k (hsrc k)
  letI : T2Space ↥(sourceOpen (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  set y : SourceDomain (I := I) Φ k := ⟨z, hzsrc⟩ with hydef
  obtain ⟨W, hWopen, hgrowW, hW1⟩ := bf.chi_one k
  set O : TopologicalSpace.Opens (SourceDomain (I := I) Φ k) :=
    ⟨Subtype.val ⁻¹' W, hWopen.preimage continuous_subtype_val⟩ with hOdef
  letI : ChartedSpace H ↥O :=
    TopologicalSpace.Opens.instChartedSpace (H := H) (M := SourceDomain (I := I) Φ k) (s := O)
  letI : IsManifold I ∞ ↥O := { O.instHasGroupoid (contDiffGroupoid ∞ I) with }
  letI : SigmaCompactSpace ↥O := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I O.isOpen)
  letI : T2Space ↥O := inferInstance
  have hyO : y ∈ O := hgrowW hzgrow
  have hfieldO : Tensor0SBundle.metricTensorField (I := I)
        (((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I)
          (sourceOpen (I := I) Φ k)).restrictOpen (I := I) O) =
      Tensor0SBundle.metricTensorField (I := I)
        ((srcMetric (I := I) Φ hsrc htgt k t).restrictOpen (I := I) O) := by
    refine DFunLike.ext _ _ (fun w => ?_)
    refine ContinuousMultilinearMap.ext (fun vs => ?_)
    have hwW : (((w : SourceDomain (I := I) Φ k)) : P.M) ∈ W := w.2
    have hwsrc : (((w : SourceDomain (I := I) Φ k)) : P.M) ∈ Φ.source k :=
      (w : SourceDomain (I := I) Φ k).2
    change
      (gSeqExt (I := I) Φ R bf hsrc htgt k t).inner
          (((w : SourceDomain (I := I) Φ k)) : P.M) (vs 0) (vs 1) =
        (srcMetric (I := I) Φ hsrc htgt k t).inner
          (w : SourceDomain (I := I) Φ k) (vs 0) (vs 1)
    rw [gSeqExt_inner_of_mem (I := I) Φ R bf hsrc htgt k t
      (((w : SourceDomain (I := I) Φ k)) : P.M) hwsrc (vs 0) (vs 1), hW1 _ hwW]
    simp
  calc
    metricCovDerivNorm (I := I) q
        (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z =
      metricCovDerivNorm (I := I) q
        ((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I)
          (sourceOpen (I := I) Φ k))
        (refRes (I := I) Φ R hsrc k) y :=
      (covNorm_restrictOpen (I := I) _ _ (sourceOpen (I := I) Φ k) q y).symm
    _ = metricCovDerivNorm (I := I) q
        (((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I)
          (sourceOpen (I := I) Φ k)).restrictOpen (I := I) O)
        ((refRes (I := I) Φ R hsrc k).restrictOpen (I := I) O)
        (⟨y, hyO⟩ : ↥O) :=
      (covNorm_restrictOpen (I := I) _ _ O q (⟨y, hyO⟩ : ↥O)).symm
    _ = metricCovDerivNorm (I := I) q
        ((srcMetric (I := I) Φ hsrc htgt k t).restrictOpen (I := I) O)
        ((refRes (I := I) Φ R hsrc k).restrictOpen (I := I) O)
        (⟨y, hyO⟩ : ↥O) := by
      unfold metricCovDerivNorm
      rw [metricCovDeriv_eq_covDerivOfField, metricCovDeriv_eq_covDerivOfField, hfieldO]
    _ = metricCovDerivNorm (I := I) q
        (srcMetric (I := I) Φ hsrc htgt k t)
        (refRes (I := I) Φ R hsrc k) y :=
      covNorm_restrictOpen (I := I) _ _ O q (⟨y, hyO⟩ : ↥O)
    _ <= C := hC k t ht y hzgrow
/-! ### Producer 4: `hlipSrc` (the per-`k` source-granularity time-Lipschitz bound) -/

set_option maxHeartbeats 1600000 in
/-- **Producer for the `hlipSrc` carried input of `hgLip_gSeqExt`/`convOut`.**  This one
is fully produced (no Lipschitz citation): per `k`, the solution-driven producers
`hgLip0Sol` and `hgLipFinSol` run on the Brick-2 pulled-back flow `sourceFlow Φ k`, whose
flow equation they consume.  Their analytic inputs are assembled from: the transported
window equivalence (`srcEquivOn`), the transported moving-Shi bounds (`srcShi`, per
order budget from `hShiT`), the mixed-derivative swap from the flow's own regularity
(`solnTowerSwap_reg`), and the `SolLipData` covariant packs from `covOrderBound_of_soln`
with per-`k` compact initial bounds (`metricCovDerivNorm_bddOn` on a compact-closure
neighborhood).  The conclusion is verbatim the `hlipSrc` hypothesis. -/
theorem lipSrc_of_soln
    (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (β ψ : Real) (hβψ : β <= ψ)
    (hwin : Set.Icc β ψ ⊆ X.D.regular)
    (gRefT : forall k : Nat,
      letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
      letI : IsManifold I ∞ (X.term (subseq k)).M := (X.term (subseq k)).smooth
      SmoothRiemannianMetric I ((X.term (subseq k)).M))
    (B : Real -> Real) (Crel Bmax : Real)
    (hBmax : forall t : Real, t ∈ Set.Icc β ψ -> B t <= Bmax)
    (hCrel1 : 1 <= Crel) (hBmax1 : 1 <= Bmax)
    (hequivT : forall k : Nat,
      letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
      letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
      letI : IsManifold I ∞ (X.term (subseq k)).M := (X.term (subseq k)).smooth
      letI : SigmaCompactSpace (X.term (subseq k)).M := (X.term (subseq k)).sigmaCompact
      MetricUniformEquivalentOnWindow (I := I) (Φ.target k) β ψ (gRefT k)
        (fun _ t => (X.term (subseq k)).S.family.metric t) B)
    (hrel : forall k : Nat,
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
      letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
      MetricUniformEquivalentOn (I := I)
        (Set.univ : Set (SourceDomain (I := I) Φ k))
        (refRes (I := I) Φ R hsrc k)
        (tgtRefSrc (I := I) Φ gRefT hsrc htgt k) Crel)
    (hShiT : forall N : Nat, exists KShi : Real, 0 <= KShi /\
      forall k : Nat,
        letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
        letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
        letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
        letI : IsManifold I ∞ (X.term (subseq k)).M := (X.term (subseq k)).smooth
        letI : SigmaCompactSpace (X.term (subseq k)).M := (X.term (subseq k)).sigmaCompact
        MovingShiBoundOn (I := I) (Φ.target k) β ψ
          (fun _ t => (X.term (subseq k)).S.family.metric t) N KShi) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    forall k : Nat,
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
          forall (s t : Real), s ∈ Set.Icc β ψ -> t ∈ Set.Icc β ψ ->
            forall b : Nat, b <= p -> forall y : SourceDomain (I := I) Φ k, y ∈ C ->
              metricDerivNorm (I := I) b (srcMetric (I := I) Φ hsrc htgt k s)
                (srcMetric (I := I) Φ hsrc htgt k t)
                (refRes (I := I) Φ R hsrc k) y <= Ls * |s - t| := by
  classical
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  choose KShiF hKShiF0 hKShiF using hShiT
  intro k
  -- source-domain instances, both spellings
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) := sourceDomSigmaOf (I := I) Φ k (hsrc k)
  letI : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) <= ∞)
  letI : IsManifold I 2 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
      (by decide : (2 : WithTop ℕ∞) <= ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (SourceDomain (I := I) Φ k) := by
    change IsManifold I ∞ (SourceDomain (I := I) Φ k); infer_instance
  letI : SigmaCompactSpace ↥(sourceOpen (I := I) Φ k) := sourceDomSigmaOf (I := I) Φ k (hsrc k)
  letI : T2Space ↥(sourceOpen (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  haveI : LocallyCompactSpace E := inferInstance
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace (SourceDomain (I := I) Φ k) :=
    ChartedSpace.locallyCompactSpace H (SourceDomain (I := I) Φ k)
  intro C hC p
  -- the transported analytic inputs at this index
  have hequivU : MetricUniformEquivalentOnWindow (I := I)
      (Set.univ : Set (SourceDomain (I := I) Φ k)) β ψ
      (refRes (I := I) Φ R hsrc k)
      (fun _ t => srcMetric (I := I) Φ hsrc htgt k t) (fun t => Crel * B t) :=
    fun _ t ht => srcEquivOn (I := I) Φ R hsrc htgt β ψ gRefT B Crel hequivT hrel k t ht
  have hBmax'1 : (1 : Real) <= Crel * Bmax := by nlinarith
  have hBmax' : forall t : Real, t ∈ Set.Icc β ψ -> Crel * B t <= Crel * Bmax :=
    fun t ht => mul_le_mul_of_nonneg_left (hBmax t ht) (le_trans zero_le_one hCrel1)
  have hShiU : forall N : Nat, MovingShiBoundOn (I := I)
      (Set.univ : Set (SourceDomain (I := I) Φ k)) β ψ
      (fun _ t => srcMetric (I := I) Φ hsrc htgt k t) N (KShiF N) :=
    fun N => srcShi (I := I) Φ hsrc htgt β ψ N (KShiF N) (hKShiF N) k
  -- the flow and its regularity
  have hS : forall _i : Nat, IsSolutionOn (I := I)
      (sourceFlow (I := I) Φ k (hsrc k) (htgt k)) :=
    fun _ => isSolutionOn_sourceFlow (I := I) Φ k (hsrc k) (htgt k)
  have hmet : forall (_i : Nat) (r : Real),
      (sourceFlow (I := I) Φ k (hsrc k) (htgt k)).family.metric r
        = srcMetric (I := I) Φ hsrc htgt k r := fun _ _ => rfl
  have hreg : forall _i : Nat, Set.Icc β ψ ⊆ X.D.regular := fun _ => hwin
  have hDreg : forall {t : Real}, t ∈ X.D.regular -> X.D.regular ∈ nhds t :=
    fun {t} ht => X.D.regular_isOpen.mem_nhds ht
  -- order-0 Lipschitz from the flow equation
  have h0 := hgLip0Sol (I := I)
    (K := C) (U := (Set.univ : Set (SourceDomain (I := I) Φ k)))
    (gSeq := fun _ t => srcMetric (I := I) Φ hsrc htgt k t)
    (gRef := refRes (I := I) Φ R hsrc k)
    (Set.subset_univ C) (fun t => Crel * B t) hequivU
    (Crel * Bmax) hBmax'1 hBmax'
    (KShiF 0) (hKShiF0 0)
    (fun i t ht x hx => hShiU 0 0 le_rfl i t ht x hx)
    (fun _ => X.D) (fun _ => sourceFlow (I := I) Φ k (hsrc k) (htgt k))
    hS hmet hreg
  -- the mixed-derivative swap from the flow's own regularity
  have hswap : SolSwapData (I := I) (refRes (I := I) Φ R hsrc k)
      (fun _ => X.D) (fun _ => sourceFlow (I := I) Φ k (hsrc k) (htgt k)) :=
    fun _i N p' hp V x0 =>
      solnTowerSwap_reg (I := I) (refRes (I := I) Φ R hsrc k)
        (sourceFlow (I := I) Φ k (hsrc k) (htgt k))
        (isSolutionOn_sourceFlow (I := I) Φ k (hsrc k) (htgt k))
        N hDreg p' hp V x0
  -- the positive-order covariant packs
  have hpack : forall a : Nat, 1 <= a -> a <= p ->
      exists U : Set (SourceDomain (I := I) Φ k), IsOpen U /\ C ⊆ U /\
        exists B' : Real -> Real, exists Bmax' : Real, exists Cg : Nat -> Real,
        exists KShi : Real, exists CN : Real,
          MetricUniformEquivalentOnWindow (I := I) U β ψ
            (refRes (I := I) Φ R hsrc k)
            (fun _ t => srcMetric (I := I) Φ hsrc htgt k t) B' /\
          1 <= Bmax' /\ (forall t, t ∈ Set.Icc β ψ -> B' t <= Bmax') /\
          (forall r : Nat, 1 <= r -> r < a ->
            MetricCovDerivOrderBoundOnWindow (I := I) U β ψ
              (fun _ t => srcMetric (I := I) Φ hsrc htgt k t)
              (refRes (I := I) Φ R hsrc k) r (Cg r)) /\
          0 <= KShi /\
          (forall s : Nat, s <= a -> forall i : Nat,
            forall t : Real, t ∈ Set.Icc β ψ ->
              forall x : SourceDomain (I := I) Φ k, x ∈ U ->
                Real.sqrt
                  (Tensor0SBundle.normSq0S (I := I)
                    (srcMetric (I := I) Φ hsrc htgt k t) x (2 + s)
                    (ricCovTower (I := I) (srcMetric (I := I) Φ hsrc htgt k t)
                      (srcMetric (I := I) Φ hsrc htgt k t) s x)) <= KShi) /\
          0 <= CN /\
          MetricCovDerivOrderBoundOnWindow (I := I) C β ψ
            (fun _ t => srcMetric (I := I) Φ hsrc htgt k t)
            (refRes (I := I) Φ R hsrc k) a CN := by
    intro a ha1 hap
    -- nested compact-closure neighborhoods of `C`
    obtain ⟨U₁, hU₁o, hCU₁, hU₁c⟩ :=
      exists_isOpen_superset_and_isCompact_closure hC
    obtain ⟨U₂, hU₂o, hclU₂, hU₂c⟩ :=
      exists_isOpen_superset_and_isCompact_closure hU₁c
    -- per-`k` initial covariant bounds on the compact closure
    have hbd : forall r : Nat, exists c : Real,
        forall z : SourceDomain (I := I) Φ k, z ∈ closure U₂ ->
          metricCovDerivNorm (I := I) r (srcMetric (I := I) Φ hsrc htgt k β)
            (refRes (I := I) Φ R hsrc k) z <= c :=
      fun r => metricCovDerivNorm_bddOn (I := I) hU₂c r
        (srcMetric (I := I) Φ hsrc htgt k β) (refRes (I := I) Φ R hsrc k)
    choose cInit hcInit using hbd
    -- the order bounds from the P2 capstone on `closure U₁ ⊆ U₂`
    have horders := covOrderBound_of_soln (I := I)
      (K := closure U₁) (U := U₂) (β := β) (ψ := ψ) (t0 := β)
      (gSeq := fun _ t => srcMetric (I := I) Φ hsrc htgt k t)
      (gRef := refRes (I := I) Φ R hsrc k)
      hU₁c hU₂o hclU₂ a
      (fun _ => X.D) (fun _ => sourceFlow (I := I) Φ k (hsrc k) (htgt k))
      hS hmet hreg
      (fun t => Crel * B t)
      (metricUniformEquivalentOnWindow_mono (I := I) (Set.subset_univ U₂) hequivU)
      (Crel * Bmax) hBmax'1 hBmax'
      (KShiF a) (hKShiF0 a)
      (fun s hs i t ht x _hx => hShiU a s hs i t ht x (Set.mem_univ x))
      (Set.mem_Icc.mpr ⟨le_refl β, hβψ⟩)
      (fun _i {t} ht => hDreg ht)
      (fun r => max (cInit r) 0)
      (fun r => le_max_right _ _)
      (fun r _ _ i x hx => le_trans (hcInit r x (subset_closure hx)) (le_max_left _ _))
      (ψ - β)
      (fun t ht => by
        rw [abs_of_nonneg (sub_nonneg.2 ht.1)]
        exact sub_le_sub_right ht.2 β)
    have hCw : forall r : Nat, exists Cw : Real, 1 <= r -> r <= a ->
        MetricCovDerivOrderBoundOnWindow (I := I) (closure U₁) β ψ
          (fun _ t => srcMetric (I := I) Φ hsrc htgt k t)
          (refRes (I := I) Φ R hsrc k) r Cw := by
      intro r
      by_cases h : 1 <= r ∧ r <= a
      · obtain ⟨Cw, hCwr⟩ := horders r h.1 h.2
        exact ⟨Cw, fun _ _ => hCwr⟩
      · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
    choose Cg hCg using hCw
    refine ⟨U₁, hU₁o, hCU₁, (fun t => Crel * B t), Crel * Bmax, Cg,
      KShiF a, max (Cg a) 0, ?_, hBmax'1, hBmax', ?_, hKShiF0 a, ?_, le_max_right _ _, ?_⟩
    · exact metricUniformEquivalentOnWindow_mono (I := I) (Set.subset_univ U₁) hequivU
    · intro r hr1 hra i t ht x hx
      exact hCg r hr1 (le_of_lt hra) i t ht x (subset_closure hx)
    · exact fun s hs i t ht x _hx => hShiU a s hs i t ht x (Set.mem_univ x)
    · intro i t ht x hx
      exact le_trans (hCg a ha1 le_rfl i t ht x (subset_closure (hCU₁ hx)))
        (le_max_left _ _)
  -- run the all-orders producer and re-order binders to the carried shape
  obtain ⟨Ls, hLs0, hLs⟩ := hgLipFinSol (I := I)
    (K := C) (β := β) (ψ := ψ) (p := p)
    (gSeq := fun _ t => srcMetric (I := I) Φ hsrc htgt k t)
    (gRef := refRes (I := I) Φ R hsrc k)
    (D := fun _ => X.D)
    (S := fun _ => sourceFlow (I := I) Φ k (hsrc k) (htgt k))
    hC hS hmet hreg hswap h0 ⟨hpack⟩
  exact ⟨Ls, hLs0, fun s t hs ht b hb y hy => hLs 0 s hs t ht b hb y hy⟩


end ConvField

end HCGCompactness
end DifferentialGeometry
