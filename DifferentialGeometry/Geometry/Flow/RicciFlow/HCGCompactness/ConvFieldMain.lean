import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConvFieldAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconvWindowAllPt

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Brick 5 of the P4 conv engine — one global `gInf` and the conv-field bridge

Applies the all-compacts Arzelà–Ascoli endpoint `windowGInfAll`
(`MetricPreconvWindowAll.lean`) to the bump-extended sequence `gSeqExt`
(`ConvFieldAssembly.lean`, Brick 4), packages the output as DATA (`ConvOut`:
one subsequence `φ`, one global limit family `gInf`, the sup-level window
convergence `conv` and its pointwise companion `convPt` along the SAME `φ`),
and proves the conv-field bridge: the `SourceDomainMetricData.ofRestrictPullback`
seminorm `derivNormSupOn` of the pulled-back flows against the limit family is
eventually small on every compact of the limit manifold `P.M`
(`ofRP_supOn_conv`), via the per-index three-slot identification
`ofRP_supOn_eq`.  Time-0 identification `gInf_zero_eq` closes the Brick-7
`hL0` reduction: `gInf 0` equals any pointwise time-0 limit of the pulled-back
source metrics.

Cited inputs (threaded through at the exact Brick-4 granularity, dischargers
unchanged): the uniform source lower bound (`hbound`, for `hlow_gSeqExt`), the
uniform tail covariant bound (`hcovTail`, for `hbdd_gSeqExt`), the tail/source
time-Lipschitz bounds (`hlipTail`/`hlipSrc`, for `hgLip_gSeqExt`), and — for
the time-0 identification only — the pointwise time-0 convergence of the
pulled-back source metrics (`hconv0`, discharged at Brick 7 from
`mc.convergence`).

The slot identification never compares metrics across nested subtypes: the
pullback slot is swapped against `resSrc (gSeqExt k t)` pointwise on a sub-open
`O ⊆ SourceDomain Φ k` where the bump is identically `1` (`BumpFamily.chi_one`),
using restriction-invariance (`metricDerivNorm_restrictOpen`) twice and the
`metricTensorField`-congruence `derivNorm_congr_left`.
-/

noncomputable section

open Set Function Filter Bundle Manifold TopologicalSpace
open scoped Manifold Topology ContDiff BigOperators
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow (SolutionOn IsSolutionOn)

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H} [I.Boundaryless]

/-! ### Generic seminorm congruence lemmas

Candidates for relocation next to `metricDerivNorm`/`metricDerivNormSupOn`
(`PointedConvergence.lean`); kept here to avoid invalidating the deep import
chain mid-phase. -/

section CongrLemmas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

/-- The MSM135 seminorm depends on its first metric slot only through the
metric tensor field: metrics with equal `metricTensorField` have equal
seminorms against any second slot and any reference. -/
theorem derivNorm_congr_left
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (a : Nat) (g₁ g₂ gI gRef : SmoothRiemannianMetric I M) (x : M)
    (h : Tensor0SBundle.metricTensorField (I := I) g₁
      = Tensor0SBundle.metricTensorField (I := I) g₂) :
    metricDerivNorm (I := I) a g₁ gI gRef x = metricDerivNorm (I := I) a g₂ gI gRef x := by
  unfold metricDerivNorm metricDiffCovDerivAt
  rw [metricCovDeriv_eq_covDerivOfField (I := I) g₁ gRef a,
    metricCovDeriv_eq_covDerivOfField (I := I) g₂ gRef a, h]

/-- The raw `C^p` sup seminorm is unchanged when the first metric slot is
replaced by a metric with pointwise-equal seminorms on the sup set. -/
theorem supOn_congr_left
    (K : Set M) (p : Nat) (g₁ g₂ gI gRef : SmoothRiemannianMetric I M)
    (h : forall x, x ∈ K -> forall a : Nat, a <= p ->
      metricDerivNorm (I := I) a g₁ gI gRef x = metricDerivNorm (I := I) a g₂ gI gRef x) :
    metricDerivNormSupOn (I := I) K p g₁ gI gRef
      = metricDerivNormSupOn (I := I) K p g₂ gI gRef := by
  unfold metricDerivNormSupOn
  congr 1
  ext r
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, x, hx, rfl⟩
    exact ⟨a, ha, x, hx, (h x hx a ha).symm⟩
  · rintro ⟨a, ha, x, hx, rfl⟩
    exact ⟨a, ha, x, hx, h x hx a ha⟩

end CongrLemmas

section ConvField

variable {X : PointedFlowSeq (I := I)}
variable {P : PointedRiemannianManifold (I := I)}
variable {subseq : Nat -> Nat}
variable (Φ : PointedCGHMaps (I := I) X P subseq)

/-- The image of a limit-manifold set viewed inside a source domain is the set
itself, provided the set lies in that source.  (The inline computation of
`sourceCompactSet_isCompact`, extracted.) -/
theorem sourceCompactSet_image_eq (k : Nat) {K : Set P.M}
    (hKsrc : letI : TopologicalSpace P.M := P.topology; K ⊆ Φ.source k) :
    Subtype.val '' (sourceCompactSet (I := I) Φ k K) = K := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz
  · intro hy
    exact ⟨⟨y, hKsrc hy⟩, hy, rfl⟩

/-- Restriction of a limit-manifold metric to the `k`th source domain, with the
`restrictOpen` instances converted across the `SourceDomain Φ k` vs
`↥(sourceOpen Φ k)` spelling gap and passed explicitly (the `refRes` idiom;
`refRes Φ R hsrc k` is definitionally `resSrc Φ hsrc k R`). -/
noncomputable def resSrc (hsrc : SrcSigma Φ) (k : Nat)
    (g : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M) :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
    SmoothRiemannianMetric I (SourceDomain (I := I) Φ k) :=
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  let sourceSigma : SigmaCompactSpace ↥(sourceOpen (I := I) Φ k) := by
    change SigmaCompactSpace (SourceDomain (I := I) Φ k)
    exact sourceDomSigmaOf (I := I) Φ k (hsrc k)
  let sourceT2 : T2Space ↥(sourceOpen (I := I) Φ k) := by
    change T2Space (SourceDomain (I := I) Φ k)
    exact sourceDomT2 (I := I) Φ k
  @SmoothRiemannianMetric.restrictOpen E inferInstance inferInstance H inferInstance I
    P.M P.topology P.charted P.smooth inferInstance
    g (sourceOpen (I := I) Φ k) sourceSigma sourceT2

/-- Pointwise evaluation of `resSrc`: restriction does not change inner
products. -/
theorem resSrc_inner (hsrc : SrcSigma Φ) (k : Nat)
    (g : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (y : SourceDomain (I := I) Φ k)
    (v w : letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k;
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k;
      TangentSpace I y) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
    (resSrc (I := I) Φ hsrc k g).inner y v w = g.inner (y : P.M) v w := rfl

/-- The restricted reference metric `refRes` is the `resSrc` restriction of the
reference. -/
theorem refRes_eq_resSrc
    (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (hsrc : SrcSigma Φ) (k : Nat) :
    refRes (I := I) Φ R hsrc k = resSrc (I := I) Φ hsrc k R := rfl

/-- **Sup-level restriction invariance for `resSrc`.**  The source-domain `C^p`
seminorm of three restricted metrics over a set equals the limit-manifold
seminorm over its image. -/
theorem supOn_resSrc_eq (hsrc : SrcSigma Φ) (k : Nat)
    (g₁ g₂ g₃ : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (C : Set (SourceDomain (I := I) Φ k)) (p : Nat) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
    letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
    letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) := sourceDomSigmaOf (I := I) Φ k (hsrc k)
    metricDerivNormSupOn (I := I) C p (resSrc (I := I) Φ hsrc k g₁)
        (resSrc (I := I) Φ hsrc k g₂) (resSrc (I := I) Φ hsrc k g₃)
      = metricDerivNormSupOn (I := I) (Subtype.val '' C) p g₁ g₂ g₃ := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) := sourceDomSigmaOf (I := I) Φ k (hsrc k)
  let sourceSigma : SigmaCompactSpace ↥(sourceOpen (I := I) Φ k) := by
    change SigmaCompactSpace (SourceDomain (I := I) Φ k)
    exact sourceDomSigmaOf (I := I) Φ k (hsrc k)
  let sourceT2 : T2Space ↥(sourceOpen (I := I) Φ k) := by
    change T2Space (SourceDomain (I := I) Φ k)
    exact sourceDomT2 (I := I) Φ k
  exact @metricDerivNormSupOn_restrictOpen E _ _ _ _ _ H _ I _
    P.M P.topology P.charted P.t2 P.smooth P.sigmaCompact
    g₁ g₂ g₃ (sourceOpen (I := I) Φ k) sourceSigma sourceT2 C p

/-! ### The Brick-5 output data -/

/-- **The Brick-5 output package** (ruling 5a: data, not bare existentials).
One subsequence `φ`, one global limit family `gInf` on the limit manifold
`P.M`, the sup-level convergence `conv` of the bump-extended sequence `gSeqExt`
along `φ` toward `gInf` on the fixed window `[β, ψ]` for every spatial compact
and every order, and its pointwise companion `convPt` along the same subsequence
(the form consumed by the Brick-6 regularity/PDE layer). -/
structure ConvOut
    (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (β ψ : Real) where
  /-- The single subsequence serving all spatial compacts and orders on the
  fixed window `[β, ψ]`. -/
  φ : Nat -> Nat
  /-- Strict monotonicity of the subsequence. -/
  hφ : StrictMono φ
  /-- The single global limit metric family on the limit manifold. -/
  gInf : letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    Real -> SmoothRiemannianMetric I P.M
  /-- The `windowGInfAll` conclusion for `gSeqExt` along `φ` toward `gInf`:
  sup-level `C^p` window smallness on every compact, every order. -/
  conv : letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    forall K : Set P.M, IsCompact K -> forall p : Nat, forall ε : Real, 0 < ε ->
      exists k0 : Nat, forall k : Nat, k0 <= k ->
        forall t, t ∈ Set.Icc β ψ ->
          metricDerivNormSupOn (I := I) K p
            (gSeqExt (I := I) Φ R bf hsrc htgt (φ k) t) (gInf t) R < ε
  /-- Pointwise companion of `conv` along the SAME `φ` (each order `a ≤ p`,
  each point of the compact). -/
  convPt : letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    forall K : Set P.M, IsCompact K -> forall p : Nat, forall ε : Real, 0 < ε ->
      exists k0 : Nat, forall k : Nat, k0 <= k ->
        forall t, t ∈ Set.Icc β ψ -> forall a : Nat, a <= p -> forall x, x ∈ K ->
          metricDerivNorm (I := I) a
            (gSeqExt (I := I) Φ R bf hsrc htgt (φ k) t) (gInf t) R x < ε

namespace ConvOut

/-- Reindex a fixed-window convergence output along a further strict
subsequence, retaining its limit metric family and both convergence fields. -/
noncomputable def comp_subseq
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {β ψ : Real}
    (co : ConvOut (I := I) Φ R bf hsrc htgt β ψ)
    (η : Nat → Nat) (hη : StrictMono η) :
    ConvOut (I := I) Φ R bf hsrc htgt β ψ where
  φ := co.φ ∘ η
  hφ := co.hφ.comp hη
  gInf := co.gInf
  conv := by
    intro K hK p ε hε
    obtain ⟨k₀, hk₀⟩ := co.conv K hK p ε hε
    refine ⟨k₀, fun k hk t ht => ?_⟩
    simpa only [Function.comp_apply] using
      hk₀ (η k) (hk.trans (hη.id_le k)) t ht
  convPt := by
    intro K hK p ε hε
    obtain ⟨k₀, hk₀⟩ := co.convPt K hK p ε hε
    refine ⟨k₀, fun k hk t ht a ha x hx => ?_⟩
    simpa only [Function.comp_apply] using
      hk₀ (η k) (hk.trans (hη.id_le k)) t ht a ha x hx

end ConvOut

/-- **Brick-5 Step 1+2: the Arzelà–Ascoli extraction, packaged.**  Applies
`windowGInfAll` to the bump-extended sequence `gSeqExt` (Brick 4), with the
three raw hypotheses discharged by `hgLip_gSeqExt`/`hbdd_gSeqExt`/`hlow_gSeqExt`
from the cited inputs (threaded through verbatim at the Brick-4 granularity),
and derives the pointwise companion along the same subsequence via the
`BddAbove` pattern of `windowGInfAll_pt`. -/
noncomputable def convOut
    (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (β ψ : Real) (hβψ : β <= ψ)
    (cLow : Real) (hcLow : 0 < cLow)
    (hbound : letI : TopologicalSpace P.M := P.topology;
        letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      forall (k : Nat) (t : Real), t ∈ Set.Icc β ψ ->
        forall (y : SourceDomain (I := I) Φ k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k;
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k;
            TangentSpace I y),
          cLow * R.inner (y : P.M) v v <=
            letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
            (srcMetric (I := I) Φ hsrc htgt k t).inner y v v)
    (hcovTail : letI : TopologicalSpace P.M := P.topology;
        letI : ChartedSpace H P.M := P.charted; letI : T2Space P.M := P.t2;
        letI : IsManifold I ∞ P.M := P.smooth; letI : SigmaCompactSpace P.M := P.sigmaCompact;
      forall q : Nat, exists C : Real, forall (k : Nat) (t : Real), t ∈ Set.Icc β ψ ->
        forall z : P.M, z ∈ bf.grow k ->
          metricCovDerivNorm (I := I) q (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z <= C)
    (hlipTail : letI : TopologicalSpace P.M := P.topology;
        letI : ChartedSpace H P.M := P.charted; letI : T2Space P.M := P.t2;
        letI : IsManifold I ∞ P.M := P.smooth; letI : SigmaCompactSpace P.M := P.sigmaCompact;
      forall p : Nat, exists Lt : Real, 0 <= Lt /\
        forall (k : Nat) (s t : Real), s ∈ Set.Icc β ψ -> t ∈ Set.Icc β ψ ->
          forall a : Nat, a <= p -> forall z : P.M, z ∈ bf.grow k ->
            metricDerivNorm (I := I) a (gSeqExt (I := I) Φ R bf hsrc htgt k s)
              (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z <= Lt * |s - t|)
    (hlipSrc : letI : TopologicalSpace P.M := P.topology;
        letI : ChartedSpace H P.M := P.charted; letI : T2Space P.M := P.t2;
        letI : IsManifold I ∞ P.M := P.smooth; letI : SigmaCompactSpace P.M := P.sigmaCompact;
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
                  (refRes (I := I) Φ R hsrc k) y <= Ls * |s - t|) :
    ConvOut (I := I) Φ R bf hsrc htgt β ψ := by
  classical
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  haveI : LocallyCompactSpace E := inferInstance
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace P.M := ChartedSpace.locallyCompactSpace H P.M
  haveI : WeaklyLocallyCompactSpace P.M := inferInstance
  have hne : Nonempty P.M := ⟨P.basepoint⟩
  have hd := denseIccSeq (beta := β) (psiT := ψ) hβψ
  have hAA := windowGInfAll (I := I) hne β ψ R
    (gSeqExt (I := I) Φ R bf hsrc htgt)
    hd.choose hd.choose_spec.1 hd.choose_spec.2
    (hgLip_gSeqExt (I := I) Φ R bf hsrc htgt β ψ hlipTail hlipSrc)
    (hbdd_gSeqExt (I := I) Φ R bf hsrc htgt β ψ hcovTail)
    (hlow_gSeqExt (I := I) Φ R bf hsrc htgt cLow β ψ hcLow hbound)
  refine
    { φ := hAA.choose
      hφ := hAA.choose_spec.1
      gInf := hAA.choose_spec.2.choose
      conv := hAA.choose_spec.2.choose_spec
      convPt := ?_ }
  intro K hK p ε hε
  obtain ⟨k0, hk0⟩ := hAA.choose_spec.2.choose_spec K hK p ε hε
  refine ⟨k0, fun k hk t ht a hap x hx => ?_⟩
  -- uniform covariant bounds along the extracted subsequence at time `t`
  choose Cf hCf using fun q : Nat =>
    hbdd_gSeqExt (I := I) Φ R bf hsrc htgt β ψ hcovTail
      hAA.choose hAA.choose_spec.1 t ht q K hK
  -- `BddAbove` for the `(K, p)` sup set at `(k, t)` via a singleton-tail split
  have hbddAbove : BddAbove {r : Real | exists b : Nat, b <= p ∧ exists z : P.M, z ∈ K ∧
      metricDerivNorm (I := I) b (gSeqExt (I := I) Φ R bf hsrc htgt (hAA.choose k) t)
        (hAA.choose_spec.2.choose t) R z = r} := by
    refine ⟨(Finset.range (p + 1)).sup' ⟨0, Finset.mem_range.2 (Nat.succ_pos p)⟩
      (fun b => Cf b + Cf b + 1), ?_⟩
    rintro r ⟨b, hbp, z, hzK, rfl⟩
    obtain ⟨m0, hm0⟩ := hAA.choose_spec.2.choose_spec {z} isCompact_singleton p 1 zero_lt_one
    have hz : metricDerivNorm (I := I) b (gSeqExt (I := I) Φ R bf hsrc htgt (hAA.choose m0) t)
        (hAA.choose_spec.2.choose t) R z < 1 :=
      lt_of_le_of_lt
        (derivNorm_le_sup_sing (I := I) p
          (gSeqExt (I := I) Φ R bf hsrc htgt (hAA.choose m0) t)
          (hAA.choose_spec.2.choose t) R z b hbp)
        (hm0 m0 le_rfl t ht)
    have htri := metricDerivNorm_triangle (I := I) b
      (gSeqExt (I := I) Φ R bf hsrc htgt (hAA.choose k) t)
      (gSeqExt (I := I) Φ R bf hsrc htgt (hAA.choose m0) t)
      (hAA.choose_spec.2.choose t) R z
    have hcov : metricDerivNorm (I := I) b
        (gSeqExt (I := I) Φ R bf hsrc htgt (hAA.choose k) t)
        (gSeqExt (I := I) Φ R bf hsrc htgt (hAA.choose m0) t) R z <= Cf b + Cf b :=
      le_trans
        (derivNorm_le_cov_add (I := I) b
          (gSeqExt (I := I) Φ R bf hsrc htgt (hAA.choose k) t)
          (gSeqExt (I := I) Φ R bf hsrc htgt (hAA.choose m0) t) R z)
        (add_le_add (hCf b k z hzK) (hCf b m0 z hzK))
    have hle : metricDerivNorm (I := I) b
        (gSeqExt (I := I) Φ R bf hsrc htgt (hAA.choose k) t)
        (hAA.choose_spec.2.choose t) R z <= Cf b + Cf b + 1 := by linarith
    exact le_trans hle
      (Finset.le_sup' (fun b => Cf b + Cf b + 1) (Finset.mem_range.2 (Nat.lt_succ_of_le hbp)))
  exact lt_of_le_of_lt (le_csSup hbddAbove ⟨a, hap, x, hx, rfl⟩) (hk0 k hk t ht)

/-! ### Step 3: the conv-field bridge -/

/-- Definitional unfolding of the `ofRestrictPullback` seminorm: pullback slot
= the Brick-2 source-flow metric, limit slot = the restricted limit-flow
metric, reference slot = the restricted reference. -/
private theorem ofRP_supOn_def
    (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (gInf : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      Real -> SmoothRiemannianMetric I P.M)
    (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (k : Nat) (K : Set P.M) (p : Nat) (t : Real) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
      change IsManifold I ∞ P.M; infer_instance
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
    letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
    letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) := sourceDomSigmaOf (I := I) Φ k (hsrc k)
    (SourceDomainMetricData.ofRestrictPullback (I := I) (Φ := Φ) (k := k)
        (hsrc k) (htgt k)
        (fun _ => refRes (I := I) Φ R hsrc k) gInf).derivNormSupOn (I := I) K p t
      = metricDerivNormSupOn (I := I) (sourceCompactSet (I := I) Φ k K) p
          (srcMetric (I := I) Φ hsrc htgt k t)
          (resSrc (I := I) Φ hsrc k (gInf t))
          (refRes (I := I) Φ R hsrc k) := rfl

open Tensor0SBundle in
/-- **Brick-5 Step 3, per index: the three-slot identification.**  On a compact
`K` inside the bump agreement region `grow k`, the `ofRestrictPullback`
seminorm of the `k`th pulled-back flow against the limit metric `gIt`
(hypothesis `hmet`: the limit-flow metric at time `t` is `gIt`) and the
restricted reference `refRes` equals the fixed-manifold seminorm of the
bump-extended metric against `gIt` and `R` on `P.M`.  Pullback slot: `gSeqExt`
agrees with the source metric on the open where the bump is `1`
(`BumpFamily.chi_one` + `gSeqExt_inner_of_mem`), so the seminorms agree
pointwise over `K` by restriction-invariance and `metricTensorField`
congruence; limit and reference slots are definitionally restrictions. -/
theorem ofRP_supOn_eq
    (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (k : Nat) (K : Set P.M) (p : Nat) (t : Real)
    (gIt : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (gInf : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      Real -> SmoothRiemannianMetric I P.M)
    (hmet : letI : TopologicalSpace P.M := P.topology;
        letI : ChartedSpace H P.M := P.charted; letI : T2Space P.M := P.t2;
        letI : IsManifold I ∞ P.M := P.smooth; letI : SigmaCompactSpace P.M := P.sigmaCompact;
      gInf t = gIt)
    (hKgrow : letI : TopologicalSpace P.M := P.topology; K ⊆ bf.grow k) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    (SourceDomainMetricData.ofRestrictPullback (I := I) (Φ := Φ) (k := k)
        (hsrc k) (htgt k)
        (fun _ => refRes (I := I) Φ R hsrc k) gInf).derivNormSupOn (I := I) K p t
      = metricDerivNormSupOn (I := I) K p
          (gSeqExt (I := I) Φ R bf hsrc htgt k t) gIt R := by
  classical
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
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
  -- membership bookkeeping
  have hKsrc : K ⊆ Φ.source k := hKgrow.trans (bf.grow_subset k)
  -- the open where the bump is identically 1
  obtain ⟨W, hWopen, hgrowW, hW1⟩ := bf.chi_one k
  -- the sub-open of the source domain over that set
  let O : TopologicalSpace.Opens (SourceDomain (I := I) Φ k) :=
    ⟨Subtype.val ⁻¹' W, hWopen.preimage continuous_subtype_val⟩
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
  -- the pullback slot and the restricted bump-extension have equal tensor
  -- fields after restriction to `O` (the bump is 1 there)
  have hmTF : metricTensorField (I := I)
        ((srcMetric (I := I) Φ hsrc htgt k t).restrictOpen (I := I) O)
      = metricTensorField (I := I)
        ((resSrc (I := I) Φ hsrc k
          (gSeqExt (I := I) Φ R bf hsrc htgt k t)).restrictOpen (I := I) O) := by
    refine DFunLike.ext _ _ (fun y => ?_)
    refine ContinuousMultilinearMap.ext (fun v => ?_)
    have hyW : ((y : SourceDomain (I := I) Φ k) : P.M) ∈ W := y.2
    have hysrc : ((y : SourceDomain (I := I) Φ k) : P.M) ∈ Φ.source k :=
      (y : SourceDomain (I := I) Φ k).2
    change
      ((srcMetric (I := I) Φ hsrc htgt k t).restrictOpen (I := I) O).inner y (v 0) (v 1) =
        ((resSrc (I := I) Φ hsrc k
          (gSeqExt (I := I) Φ R bf hsrc htgt k t)).restrictOpen (I := I) O).inner
          y (v 0) (v 1)
    rw [SmoothRiemannianMetric.restrictOpen_inner,
      SmoothRiemannianMetric.restrictOpen_inner]
    rw [resSrc_inner (I := I) Φ hsrc k]
    rw [gSeqExt_inner_of_mem (I := I) Φ R bf hsrc htgt k t
      ((y : SourceDomain (I := I) Φ k) : P.M) hysrc (v 0) (v 1)]
    rw [hW1 _ hyW]
    simp
  -- pointwise slot swap over the sup set
  have hpt : forall z, z ∈ sourceCompactSet (I := I) Φ k K -> forall a : Nat, a <= p ->
      metricDerivNorm (I := I) a (srcMetric (I := I) Φ hsrc htgt k t)
        (resSrc (I := I) Φ hsrc k gIt) (refRes (I := I) Φ R hsrc k) z
      = metricDerivNorm (I := I) a
        (resSrc (I := I) Φ hsrc k (gSeqExt (I := I) Φ R bf hsrc htgt k t))
        (resSrc (I := I) Φ hsrc k gIt) (refRes (I := I) Φ R hsrc k) z := by
    intro z hz a _ha
    have hzW : z ∈ O := hgrowW (hKgrow hz)
    calc metricDerivNorm (I := I) a (srcMetric (I := I) Φ hsrc htgt k t)
          (resSrc (I := I) Φ hsrc k gIt) (refRes (I := I) Φ R hsrc k) z
        = metricDerivNorm (I := I) a
            ((srcMetric (I := I) Φ hsrc htgt k t).restrictOpen (I := I) O)
            ((resSrc (I := I) Φ hsrc k gIt).restrictOpen (I := I) O)
            ((refRes (I := I) Φ R hsrc k).restrictOpen (I := I) O)
            (⟨z, hzW⟩ : ↥O) :=
          (metricDerivNorm_restrictOpen (I := I) _ _ _ O a (⟨z, hzW⟩ : ↥O)).symm
      _ = metricDerivNorm (I := I) a
            ((resSrc (I := I) Φ hsrc k
              (gSeqExt (I := I) Φ R bf hsrc htgt k t)).restrictOpen (I := I) O)
            ((resSrc (I := I) Φ hsrc k gIt).restrictOpen (I := I) O)
            ((refRes (I := I) Φ R hsrc k).restrictOpen (I := I) O)
            (⟨z, hzW⟩ : ↥O) :=
          derivNorm_congr_left (I := I) a _ _ _ _ (⟨z, hzW⟩ : ↥O) hmTF
      _ = metricDerivNorm (I := I) a
            (resSrc (I := I) Φ hsrc k (gSeqExt (I := I) Φ R bf hsrc htgt k t))
            (resSrc (I := I) Φ hsrc k gIt) (refRes (I := I) Φ R hsrc k) z :=
          metricDerivNorm_restrictOpen (I := I) _ _ _ O a (⟨z, hzW⟩ : ↥O)
  -- assemble: definitional unfolding, limit-slot rewrite, pointwise swap,
  -- sup-level restriction invariance, image identification
  calc (SourceDomainMetricData.ofRestrictPullback (I := I) (Φ := Φ) (k := k)
        (hsrc k) (htgt k)
        (fun _ => refRes (I := I) Φ R hsrc k) gInf).derivNormSupOn (I := I) K p t
      = metricDerivNormSupOn (I := I) (sourceCompactSet (I := I) Φ k K) p
          (srcMetric (I := I) Φ hsrc htgt k t)
          (resSrc (I := I) Φ hsrc k (gInf t))
          (refRes (I := I) Φ R hsrc k) :=
        ofRP_supOn_def (I := I) Φ R gInf hsrc htgt k K p t
    _ = metricDerivNormSupOn (I := I) (sourceCompactSet (I := I) Φ k K) p
          (srcMetric (I := I) Φ hsrc htgt k t)
          (resSrc (I := I) Φ hsrc k gIt)
          (refRes (I := I) Φ R hsrc k) := by rw [hmet]
    _ = metricDerivNormSupOn (I := I) (sourceCompactSet (I := I) Φ k K) p
          (resSrc (I := I) Φ hsrc k (gSeqExt (I := I) Φ R bf hsrc htgt k t))
          (resSrc (I := I) Φ hsrc k gIt)
          (refRes (I := I) Φ R hsrc k) :=
        supOn_congr_left (I := I) (sourceCompactSet (I := I) Φ k K) p _ _ _ _ hpt
    _ = metricDerivNormSupOn (I := I) (Subtype.val '' sourceCompactSet (I := I) Φ k K) p
          (gSeqExt (I := I) Φ R bf hsrc htgt k t) gIt R := by
        rw [refRes_eq_resSrc (I := I) Φ R hsrc k]
        exact supOn_resSrc_eq (I := I) Φ hsrc k
          (gSeqExt (I := I) Φ R bf hsrc htgt k t) gIt R
          (sourceCompactSet (I := I) Φ k K) p
    _ = metricDerivNormSupOn (I := I) K p
          (gSeqExt (I := I) Φ R bf hsrc htgt k t) gIt R := by
        rw [sourceCompactSet_image_eq (I := I) Φ k hKsrc]

/-- **Brick-5 Step 3: the conv-field bridge.**  Given the Brick-5 output
`co : ConvOut` and the limit-metric identification `hmetric` (the limit-flow
metric on the window is `co.gInf` — discharged by `rfl` once the Brick-6 flow
is built with metric `gInf`), the `ofRestrictPullback` seminorm of the
`co.φ k`-th pulled-back flow, measured against the restricted reference
`refRes`, is eventually smaller than any `ε` on every compact `K ⊆ P.M`,
every order `p`, uniformly over the window — the `FlowLimitData.conv` shape at
subsequence granularity. -/
theorem ofRP_supOn_conv
    (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (β ψ : Real)
    (co : ConvOut (I := I) Φ R bf hsrc htgt β ψ)
    (gInf : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      Real -> SmoothRiemannianMetric I P.M)
    (hmetric : letI : TopologicalSpace P.M := P.topology;
        letI : ChartedSpace H P.M := P.charted; letI : T2Space P.M := P.t2;
        letI : IsManifold I ∞ P.M := P.smooth; letI : SigmaCompactSpace P.M := P.sigmaCompact;
      forall t : Real, t ∈ Set.Icc β ψ -> gInf t = co.gInf t) :
    forall K : Set P.M,
      forall _hK : (letI : TopologicalSpace P.M := P.topology; IsCompact K),
      forall p : Nat, forall ε : Real, 0 < ε ->
        exists k0 : Nat, forall k : Nat, k0 <= k ->
          forall t : Real, t ∈ Set.Icc β ψ ->
            (SourceDomainMetricData.ofRestrictPullback (I := I) (Φ := Φ) (k := co.φ k)
                (hsrc (co.φ k)) (htgt (co.φ k))
                (fun _ => refRes (I := I) Φ R hsrc (co.φ k)) gInf).derivNormSupOn (I := I) K p t
              < ε := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  intro K hK p ε hε
  obtain ⟨k0c, hk0c⟩ := co.conv K hK p ε hε
  obtain ⟨k0g, hk0g⟩ := bf.grow_cover K hK
  refine ⟨max k0c k0g, fun k hk t ht => ?_⟩
  have hkg : K ⊆ bf.grow (co.φ k) :=
    hk0g (co.φ k) (le_trans (le_trans (le_max_right _ _) hk) (co.hφ.id_le k))
  rw [ofRP_supOn_eq (I := I) Φ R bf hsrc htgt (co.φ k) K p t (co.gInf t) gInf
    (hmetric t ht) hkg]
  exact hk0c k (le_trans (le_max_left _ _) hk) t ht

/-! ### Step 4: time-0 identification of the limit -/

/-- **Brick-5 Step 4: `gInf 0` is the time-0 Cheeger–Gromov limit metric.**
From the pointwise time-0 convergence of the pulled-back source metrics toward
`g0` (hypothesis `hconv0`, in `Φ`/`rmaps` terms — its Brick-7 discharger is
`mc.convergence`) and the Brick-5 window convergence at `t = 0`, the two limits
agree pointwise (`tendsto_nhds_unique`), hence as metrics
(`metric_ext_inner`).  This is the input for the Brick-7 `hL0` reduction via
`flowOfMetric_atTime`. -/
theorem gInf_zero_eq
    (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (β ψ : Real)
    (co : ConvOut (I := I) Φ R bf hsrc htgt β ψ)
    (h0 : (0 : Real) ∈ Set.Icc β ψ)
    (g0 : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (hconv0 : letI : TopologicalSpace P.M := P.topology;
        letI : ChartedSpace H P.M := P.charted; letI : T2Space P.M := P.t2;
        letI : IsManifold I ∞ P.M := P.smooth; letI : SigmaCompactSpace P.M := P.sigmaCompact;
      forall (x : P.M) (v w : TangentSpace I x) (ε : Real), 0 < ε ->
        exists k0 : Nat, forall k : Nat, k0 <= k -> forall hx : x ∈ Φ.source k,
          |(letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
            (srcMetric (I := I) Φ hsrc htgt k 0).inner ⟨x, hx⟩ v w)
            - g0.inner x v w| < ε) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    co.gInf 0 = g0 := by
  classical
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  refine metric_ext_inner (I := I) (co.gInf 0) g0 (fun x => ?_)
  refine ContinuousLinearMap.ext (fun v => ?_)
  refine ContinuousLinearMap.ext (fun w => ?_)
  -- nonnegativity of the reference quadratic form
  have hRnn : forall u : TangentSpace I x, 0 <= R.inner x u u := by
    intro u
    by_cases hu : u = 0
    · subst hu; simp
    · exact (R.pos x u hu).le
  -- T1: the bump-extended sequence converges to `gInf 0` at `x` (from `convPt`)
  have hT1 : Tendsto
      (fun k => (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) 0).inner x v w)
      atTop (nhds ((co.gInf 0).inner x v w)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    set n : Real := (Module.finrank Real (TangentSpace I x) : Real) with hn
    set Cx : Real := R.inner x (v + w) (v + w) + R.inner x v v + R.inner x w w with hCx
    have hn0 : 0 <= n := Nat.cast_nonneg _
    have hCx0 : 0 <= Cx := by
      have h1 := hRnn (v + w)
      have h2 := hRnn v
      have h3 := hRnn w
      rw [hCx]; linarith
    have hden : (0 : Real) < n * Cx + 1 := by positivity
    obtain ⟨k0, hk0⟩ := co.convPt {x} isCompact_singleton 0 (ε / (n * Cx + 1))
      (by positivity)
    refine ⟨k0, fun k hk => ?_⟩
    have hpt := hk0 k hk 0 h0 0 le_rfl x (Set.mem_singleton x)
    have hbound := metricInnerApply_diff_le (I := I)
      (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) 0) (co.gInf 0) R x v w
    rw [Real.dist_eq]
    have h1 : n * metricDerivNorm (I := I) 0
          (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) 0) (co.gInf 0) R x * Cx
        <= n * (ε / (n * Cx + 1)) * Cx :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpt.le hn0) hCx0
    have h2 : n * (ε / (n * Cx + 1)) * Cx < ε := by
      have hlt : n * Cx < n * Cx + 1 := by linarith
      have hεD : (0 : Real) < ε / (n * Cx + 1) := by positivity
      calc n * (ε / (n * Cx + 1)) * Cx
          = (n * Cx) * (ε / (n * Cx + 1)) := by ring
        _ < (n * Cx + 1) * (ε / (n * Cx + 1)) := mul_lt_mul_of_pos_right hlt hεD
        _ = ε := by
            rw [mul_comm]
            exact div_mul_cancel₀ ε hden.ne'
    exact lt_of_le_of_lt (le_trans hbound h1) h2
  -- T2: the same sequence converges to `g0` at `x` (bump = 1 eventually +
  -- the cited time-0 convergence)
  have hT2 : Tendsto
      (fun k => (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) 0).inner x v w)
      atTop (nhds (g0.inner x v w)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨k1, hk1⟩ := hconv0 x v w ε hε
    obtain ⟨k2, hk2⟩ := bf.grow_cover {x} isCompact_singleton
    refine ⟨max k1 k2, fun k hk => ?_⟩
    have hφk1 : k1 <= co.φ k :=
      le_trans (le_trans (le_max_left _ _) hk) (co.hφ.id_le k)
    have hgrow : x ∈ bf.grow (co.φ k) :=
      hk2 (co.φ k) (le_trans (le_trans (le_max_right _ _) hk) (co.hφ.id_le k))
        (Set.mem_singleton x)
    have hxsrc : x ∈ Φ.source (co.φ k) := bf.grow_subset (co.φ k) hgrow
    obtain ⟨W, hWopen, hgrowW, hW1⟩ := bf.chi_one (co.φ k)
    have hχ : bf.chi (co.φ k) x = 1 := hW1 x (hgrowW hgrow)
    letI : TopologicalSpace (SourceDomain (I := I) Φ (co.φ k)) :=
      sourceDomTop (I := I) Φ (co.φ k)
    letI : ChartedSpace H (SourceDomain (I := I) Φ (co.φ k)) :=
      sourceDomCharted (I := I) Φ (co.φ k)
    letI : IsManifold I ∞ (SourceDomain (I := I) Φ (co.φ k)) :=
      sourceDomSmooth (I := I) Φ (co.φ k)
    have heq : (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) 0).inner x v w
        = (srcMetric (I := I) Φ hsrc htgt (co.φ k) 0).inner ⟨x, hxsrc⟩ v w := by
      rw [gSeqExt_inner_of_mem (I := I) Φ R bf hsrc htgt (co.φ k) 0 x hxsrc v w, hχ]
      simp
    rw [Real.dist_eq, heq]
    exact hk1 (co.φ k) hφk1 hxsrc
  exact tendsto_nhds_unique hT1 hT2

end ConvField

end HCGCompactness
end DifferentialGeometry
