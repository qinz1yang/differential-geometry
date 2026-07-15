import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.SourceDomainFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MovingShiRestrictOpen
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconvWindowAll
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricDerivNormRestrict
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivArityBridge
import DifferentialGeometry.Geometry.Topology.SigmaCompactOpen
import DifferentialGeometry.Geometry.Metric.BumpExtend
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconvWindowSolutions

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Brick 4 of the P4 conv engine — the bump-extended sequence on the limit manifold

For a pointed flow sequence `X`, limit data `L`, a subsequence, and comparison maps
`Φ : PointedCGHMaps X L subseq`, this file builds a single sequence of TOTAL smooth
Riemannian metrics `gSeqExt : ℕ → ℝ → SmoothRiemannianMetric I P.M` on the limit
manifold `P.M`, obtained by bump-extending the per-`k` pulled-back source flow
`sourceFlow Φ k` (Brick 2) from its open source `sourceOpen Φ k` to all of `P.M`
against the fixed reference metric `R`, with a coherent bump family that equals `1`
on a growing compact exhaustion of `P.M`.

`gSeqExt` is the legal input to the abstract Arzelà–Ascoli endpoint `windowGInfAll`
(`MetricPreconvWindowAll.lean`), which takes RAW hypotheses (`hgLip`/`hbdd`/`hlow`)
with no solution field.

This file delivers, sorry-free: the coherent `BumpFamily` (`nonempty_bumpFamily`), the
sequence `gSeqExt` with its pointwise evaluation (`gSeqExt_inner_of_mem`/`_of_notMem`), and
ALL THREE raw hypotheses of `windowGInfAll`:
**`hlow_gSeqExt`** — the uniform lower-bound (`hlow`) hypothesis, proved from a cited uniform
source lower bound via the convex-combination structure of `bumpExtendOpen`;
**`hbdd_gSeqExt`** — the uniform covariant-derivative bound (`hbdd`) hypothesis, proved from a
cited uniform source covariant bound on the tail together with the fixed-metric compact
boundedness `metricCovDerivNorm_bddOn` on the finitely many head/mid indices;
**`hgLip_gSeqExt`** — the time-Lipschitz (`hgLip`) hypothesis for all orders `a ≤ p`.  The time
difference cancels the reference summand, `gSeqExt k s − gSeqExt k t = χ_k · (src_s − src_t)`
on the source and `0` off `tsupport χ_k`, so on the tail (`K' ⊆ grow k`) a cited uniform bound
at `gSeqExt` granularity on `grow k` applies (its Brick-5 discharger: bump-locality — `χ_k = 1`
on an open neighborhood of `grow k`, recorded in `BumpFamily.chi_one` — plus the transported
source-flow Lipschitz producers), while the finitely many head/mid indices are handled HERE by
the χ-Leibniz collar estimate: the arity bridge `metricDerivNorm_eq_iterCov` + the m-fold
scaled-field tower `iterCov_smulF_le` (`ProductMFoldNorm.lean`) bound
`|∇_R^a(χ·(src_s − src_t))|` by `Σ_c binom(a,c)·|∇^c χ|·|∇^{a−c}(src_s − src_t)|`, the `∇^c χ`
factors are bounded on the compact window by `sqrtNormSq0S_bddOn`, and the source factor
carries the `|s−t|` from a cited per-`k` source-granularity Lipschitz bound (its discharger:
`hgLipFinSol`/`hgLip0Sol` on `sourceFlow Φ k`).

## Route

See `ConvFieldAssembly.md` for the full route, difficulty ranking of the three
hypotheses, and the recorded frontier.
-/

noncomputable section

open Set Function Filter Bundle Manifold TopologicalSpace
open scoped Manifold Topology ContDiff BigOperators
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow (SolutionOn IsSolutionOn)

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

section ConvField

variable {X : PointedFlowSeq (I := I)}
variable {P : PointedRiemannianManifold (I := I)}
variable {subseq : Nat -> Nat}
variable (Φ : PointedCGHMaps (I := I) X P subseq)

/-- The source-domain σ-compactness inputs, one per `k` (matching `sourceFlow`). -/
def SrcSigma : Prop :=
  forall k : Nat, letI : TopologicalSpace P.M := P.topology; IsSigmaCompact (Φ.source k)

/-- The target-domain σ-compactness inputs, one per `k` (matching `sourceFlow`). -/
def TgtSigma : Prop :=
  forall k : Nat,
    letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
    IsSigmaCompact (Φ.target k)

/-- The metric family of the `k`th pulled-back source flow (Brick 2), as a family of
smooth Riemannian metrics on the open source domain `SourceDomain Φ k`.  This is the
partial metric that gets bump-extended to all of `P.M`. -/
noncomputable def srcMetric (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ) (k : Nat) :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
    Real -> SmoothRiemannianMetric I (SourceDomain (I := I) Φ k) :=
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) := sourceDomSigmaOf (I := I) Φ k (hsrc k)
  letI : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (SourceDomain (I := I) Φ k) := by
    change IsManifold I ∞ (SourceDomain (I := I) Φ k); infer_instance
  fun t => (sourceFlow (I := I) Φ k (hsrc k) (htgt k)).family.metric t

/-- The reference metric `R` restricted to the `k`th source domain.  Implicit instance
resolution cannot cross the `SourceDomain Φ k` vs `↥(sourceOpen Φ k)` spelling gap, so the
`restrictOpen` instances are converted with `change` and passed explicitly — the same idiom
as `gSeqExt`'s `bumpExtendOpen` call and `SourceDomainMetricData.ofRestrictPullback`. -/
noncomputable def refRes (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (hsrc : SrcSigma Φ) (k : Nat) :
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
    R (sourceOpen (I := I) Φ k) sourceSigma sourceT2

/-- A coherent bump family on the limit manifold `P.M` for the comparison maps `Φ`.

It carries, per index `k`, a compact "agreement region" `grow k ⊆ Φ.source k` and a smooth
`[0,1]` bump `chi k` supported in `Φ.source k` that equals `1` on `grow k`.  The regions
`grow k` eventually contain every compact of `P.M` (`grow_cover`), which is what makes
`gSeqExt k` eventually agree with the pulled-back source metric on every compact (used
downstream in Brick 5).  For small `k` the region `grow k` may be empty (the constant-`R`
head: the bump is then supported in a possibly tiny source and `gSeqExt` there is close to
`R`). -/
structure BumpFamily where
  /-- The per-`k` compact agreement region where `chi k = 1`. -/
  grow : Nat -> Set P.M
  /-- Each agreement region is compact. -/
  grow_compact : forall k : Nat,
    letI : TopologicalSpace P.M := P.topology
    IsCompact (grow k)
  /-- Each agreement region sits inside the `k`th source. -/
  grow_subset : forall k : Nat,
    letI : TopologicalSpace P.M := P.topology
    grow k ⊆ Φ.source k
  /-- The agreement regions eventually contain every compact set. -/
  grow_cover : forall K : Set P.M,
    letI : TopologicalSpace P.M := P.topology
    IsCompact K -> exists k0 : Nat, forall k : Nat, k0 <= k -> K ⊆ grow k
  /-- The per-`k` bump function on `P.M`. -/
  chi : Nat -> P.M -> Real
  /-- Each bump is smooth. -/
  chi_smooth : forall k : Nat,
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (chi k)
  /-- Each bump is valued in `[0,1]`. -/
  chi01 : forall (k : Nat) (x : P.M), chi k x ∈ Set.Icc (0 : Real) 1
  /-- Each bump is supported in the `k`th source. -/
  chi_supp : forall k : Nat,
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    tsupport (chi k) ⊆ Φ.source k
  /-- Each bump equals `1` on an OPEN neighborhood of its agreement region.  The open
  form (rather than pointwise equality on `grow k`) is what makes germ/locality
  arguments possible downstream: on that neighborhood the bump extension literally
  agrees with the pulled-back source metric, so covariant derivatives of any order
  coincide there (the Brick-5 discharger of the tail hypotheses needs this). -/
  chi_one : forall k : Nat,
    letI : TopologicalSpace P.M := P.topology
    exists W : Set P.M, IsOpen W /\ grow k ⊆ W /\ forall x : P.M, x ∈ W -> chi k x = 1

/-- **The bump-extended sequence on the limit manifold.**  For each `k`, the pulled-back
source flow metric `srcMetric Φ k t` (defined on the open source `sourceOpen Φ k`) is
bump-extended by `bumpExtendOpen` against the fixed reference metric `R`, using the bump
`bf.chi k` (supported in `Φ.source k`).  The result is a total smooth Riemannian metric
on `P.M`, giving a single sequence `gSeqExt` feeding the Arzelà–Ascoli endpoint
`windowGInfAll`. -/
noncomputable def gSeqExt (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (k : Nat) (t : Real) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    SmoothRiemannianMetric I P.M :=
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
  @SmoothRiemannianMetric.bumpExtendOpen E _ _ _ H _ I P.M _ _ _ R
    (sourceOpen (I := I) Φ k) sourceSigma sourceT2
    (srcMetric (I := I) Φ hsrc htgt k t)
    (bf.chi k) (bf.chi_smooth k) (bf.chi01 k) (bf.chi_supp k)

/-- A coherent bump family always exists for the limit manifold `P.M`.

Route: a compact exhaustion `Kx` of `P.M`, the per-`k` agreement region
`grow k := Kx (bidx k)` (or `∅` when no exhaustion piece fits) with
`bidx k := findGreatest (Kx · ⊆ Φ.source k) k`, an intermediate open collar `V` from
normality (`grow k ⊆ V ⊆ closure V ⊆ Φ.source k`), and a smooth `[0,1]` cutoff equal to
`1` near `grow k` and supported in `V` (`exists_contMDiffMap_one_nhds_of_subset_interior`),
so `tsupport ⊆ closure V ⊆ Φ.source k`. -/
theorem nonempty_bumpFamily : Nonempty (BumpFamily (I := I) Φ) := by
  classical
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : IsManifold I ∞ P.M := P.smooth
  letI : T2Space P.M := P.t2
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  haveI : LocallyCompactSpace E := inferInstance
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace P.M := ChartedSpace.locallyCompactSpace H P.M
  haveI : WeaklyLocallyCompactSpace P.M := inferInstance
  haveI : NormalSpace P.M := inferInstance
  -- compact exhaustion
  set Kx : CompactExhaustion P.M := CompactExhaustion.choice P.M with hKxdef
  -- per-`k` predicate and index
  let Pfit : Nat -> Nat -> Prop := fun k j => (Kx j : Set P.M) ⊆ Φ.source k
  let bidx : Nat -> Nat := fun k => Nat.findGreatest (Pfit k) k
  let fits : Nat -> Prop := fun k => (Kx (bidx k) : Set P.M) ⊆ Φ.source k
  let grow : Nat -> Set P.M := fun k => if fits k then (Kx (bidx k) : Set P.M) else ∅
  have hgrow_subset : forall k, grow k ⊆ Φ.source k := by
    intro k
    simp only [grow]
    by_cases h : fits k
    · rw [if_pos h]; exact h
    · rw [if_neg h]; exact Set.empty_subset _
  have hgrow_compact : forall k, IsCompact (grow k) := by
    intro k
    simp only [grow]
    by_cases h : fits k
    · rw [if_pos h]; exact Kx.isCompact _
    · rw [if_neg h]; exact isCompact_empty
  -- eventual covering: any compact is eventually inside grow
  have hgrow_cover : forall K : Set P.M, IsCompact K ->
      exists k0 : Nat, forall k : Nat, k0 <= k -> K ⊆ grow k := by
    intro K hK
    obtain ⟨j0, hj0⟩ := Kx.exists_superset_of_isCompact hK
    obtain ⟨m0, hm0⟩ := Φ.source_subset (K := (Kx j0 : Set P.M)) (Kx.isCompact j0)
    refine ⟨max j0 m0, fun k hk => ?_⟩
    have hj0k : j0 <= k := le_trans (le_max_left j0 m0) hk
    have hm0k : m0 <= k := le_trans (le_max_right j0 m0) hk
    -- `j0` satisfies `P k` (since `k ≥ m0`), so `bidx k ≥ j0`
    have hPj0 : Pfit k j0 := hm0 k hm0k
    have hle : j0 <= bidx k := Nat.le_findGreatest hj0k hPj0
    -- and `bidx k` satisfies `P k`
    have hPbidx : Pfit k (bidx k) := Nat.findGreatest_spec hj0k hPj0
    have hfitsk : fits k := hPbidx
    have hsub : (Kx j0 : Set P.M) ⊆ grow k := by
      simp only [grow]; rw [if_pos hfitsk]; exact Kx.subset hle
    exact hj0.trans hsub
  -- for each `k`, an intermediate open collar and a cutoff supported in `Φ.source k`
  have hchoice : forall k : Nat, exists f : P.M -> Real,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ f /\ (forall x : P.M, f x ∈ Set.Icc (0 : Real) 1) /\
        tsupport f ⊆ Φ.source k /\
        (exists W : Set P.M, IsOpen W /\ grow k ⊆ W /\ forall x : P.M, x ∈ W -> f x = 1) := by
    intro k
    have hgc : IsClosed (grow k) := (hgrow_compact k).isClosed
    -- collar `V`: grow k ⊆ V open, closure V ⊆ Φ.source k
    obtain ⟨V, hVopen, hgV, hVcl⟩ :=
      normal_exists_closure_subset hgc (Φ.source_open k) (hgrow_subset k)
    -- cutoff = 1 near grow k, support ⊆ V
    obtain ⟨f, hf1, hfsupp, hf01⟩ :=
      exists_contMDiffMap_one_nhds_of_subset_interior (I := I) (M := P.M) (n := (⊤ : ℕ∞))
        hgc (s := grow k) (t := V)
        (hgV.trans hVopen.interior_eq.ge)
    refine ⟨fun x => f x, f.contMDiff, hf01, ?_, ?_⟩
    · -- tsupport f ⊆ closure V ⊆ Φ.source k
      have hsupp : Function.support (fun x => f x) ⊆ V := by
        intro x hx
        by_contra hxV
        exact hx (hfsupp x hxV)
      calc tsupport (fun x => f x) ⊆ closure V := closure_mono hsupp
        _ ⊆ Φ.source k := hVcl
    · -- extract the open `= 1` neighborhood from the `nhdsSet` eventual equality
      have hev : {x : P.M | f x = 1} ∈ nhdsSet (grow k) :=
        hf1.mono fun x hx => by simpa using hx
      obtain ⟨W, hWopen, hgrowW, hWsub⟩ := mem_nhdsSet_iff_exists.mp hev
      exact ⟨W, hWopen, hgrowW, fun x hx => hWsub hx⟩
  choose chi hchi_smooth hchi01 hchi_supp hchi_one using hchoice
  exact ⟨{
    grow := grow
    grow_compact := hgrow_compact
    grow_subset := hgrow_subset
    grow_cover := hgrow_cover
    chi := chi
    chi_smooth := hchi_smooth
    chi01 := hchi01
    chi_supp := hchi_supp
    chi_one := hchi_one }⟩

/-! ### Pointwise evaluation of `gSeqExt` -/

section Eval

variable (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
  (bf : BumpFamily (I := I) Φ) (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)

/-- On the `k`th source, `gSeqExt` evaluates to the convex combination of the pulled-back
source metric and the reference metric. -/
theorem gSeqExt_inner_of_mem (k : Nat) (t : Real)
    (x : P.M) (hx : letI : TopologicalSpace P.M := P.topology; x ∈ Φ.source k)
    (v w : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; TangentSpace I x) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
    (gSeqExt (I := I) Φ R bf hsrc htgt k t).inner x v w =
      bf.chi k x • (srcMetric (I := I) Φ hsrc htgt k t).inner ⟨x, hx⟩ v w
        + (1 - bf.chi k x) • R.inner x v w := by
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
    change SigmaCompactSpace (SourceDomain (I := I) Φ k); exact sourceDomSigmaOf (I := I) Φ k (hsrc k)
  let sourceT2 : T2Space ↥(sourceOpen (I := I) Φ k) := by
    change T2Space (SourceDomain (I := I) Φ k); exact sourceDomT2 (I := I) Φ k
  exact @bumpExtendOpen_inner_of_mem E _ _ _ H _ I P.M _ _ _ R
    (sourceOpen (I := I) Φ k) sourceSigma sourceT2
    (srcMetric (I := I) Φ hsrc htgt k t) (bf.chi k) (bf.chi_smooth k) (bf.chi01 k)
    (bf.chi_supp k) x hx v w

/-- Off the topological support of the `k`th bump, `gSeqExt` coincides with the reference
metric `R`. -/
theorem gSeqExt_inner_of_notMem (k : Nat) (t : Real)
    (x : P.M) (hx : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      x ∉ tsupport (bf.chi k))
    (v w : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; TangentSpace I x) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    (gSeqExt (I := I) Φ R bf hsrc htgt k t).inner x v w = R.inner x v w := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  let sourceSigma : SigmaCompactSpace ↥(sourceOpen (I := I) Φ k) := by
    change SigmaCompactSpace (SourceDomain (I := I) Φ k); exact sourceDomSigmaOf (I := I) Φ k (hsrc k)
  let sourceT2 : T2Space ↥(sourceOpen (I := I) Φ k) := by
    change T2Space (SourceDomain (I := I) Φ k); exact sourceDomT2 (I := I) Φ k
  exact @bumpExtendOpen_inner_of_notMem_tsupport E _ _ _ H _ I P.M _ _ _ R
    (sourceOpen (I := I) Φ k) sourceSigma sourceT2
    (srcMetric (I := I) Φ hsrc htgt k t) (bf.chi k) (bf.chi_smooth k) (bf.chi01 k)
    (bf.chi_supp k) x hx v w

end Eval

/-! ### `hlow`: uniform lower bound `c·R ≤ gSeqExt` -/

section Low

/-- **`hlow` for the bump-extended sequence.**  From the cited uniform lower bound `cLow · R ≤
srcMetric` on the sources (transported from Theorem 3.9's window metric-equivalence), the
bump-extended metrics `gSeqExt (ρ k) t` are uniformly bounded below by `min(cLow, 1) · R`: on the
support of the bump the value is a convex combination of the source metric (`≥ cLow · R`) and `R`
(`= 1 · R`), so `≥ min(cLow, 1) · R`; off the support it is exactly `R ≥ min(cLow, 1) · R`.  This
is the `hlow` hypothesis consumed by `windowGInfAll`. -/
theorem hlow_gSeqExt
    (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (cLow β ψ : Real) (hcLow : 0 < cLow)
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
            (srcMetric (I := I) Φ hsrc htgt k t).inner y v v) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    forall rho : Nat -> Nat, StrictMono rho -> forall t, t ∈ Set.Icc β ψ ->
      exists c : Real, 0 < c /\ forall (k : Nat) (x : P.M) (v : TangentSpace I x),
        c * R.inner x v v <= (gSeqExt (I := I) Φ R bf hsrc htgt (rho k) t).inner x v v := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  intro rho _hrho t ht
  refine ⟨min cLow 1, lt_min hcLow one_pos, fun k x v => ?_⟩
  set c := min cLow 1 with hc
  have hc1 : c <= 1 := min_le_right _ _
  have hccLow : c <= cLow := min_le_left _ _
  -- `R.inner x v v ≥ 0`
  have hRnn : 0 <= R.inner x v v := by
    by_cases hv : v = 0
    · subst hv; simp
    · exact (R.pos x v hv).le
  by_cases hx : x ∈ Φ.source (rho k)
  · -- on the source: convex combination
    letI : TopologicalSpace (SourceDomain (I := I) Φ (rho k)) := sourceDomTop (I := I) Φ (rho k)
    letI : ChartedSpace H (SourceDomain (I := I) Φ (rho k)) := sourceDomCharted (I := I) Φ (rho k)
    letI : IsManifold I ∞ (SourceDomain (I := I) Φ (rho k)) := sourceDomSmooth (I := I) Φ (rho k)
    rw [gSeqExt_inner_of_mem (I := I) Φ R bf hsrc htgt (rho k) t x hx v v]
    set χ := bf.chi (rho k) x with hχdef
    have hχ01 := bf.chi01 (rho k) x
    have hχ0 : 0 <= χ := hχ01.1
    have hχ1 : χ <= 1 := hχ01.2
    -- source-metric lower bound at `y := ⟨x, hx⟩`; unify the source-inner atom as `S`
    have hsrc_low := hbound (rho k) t ht ⟨x, hx⟩ v
    set S := (srcMetric (I := I) Φ hsrc htgt (rho k) t).inner ⟨x, hx⟩ v v with hSdef
    set r := R.inner x v v with hrdef
    -- `hsrc_low : cLow * R.inner ↑⟨x,hx⟩ v v ≤ S`; `↑⟨x,hx⟩ = x` reduces `R.inner` to `r`
    have hsrc_low' : cLow * r <= S := hsrc_low
    -- goal after `smul_eq_mul`: `c * r ≤ χ • S + (1 - χ) • r`
    rw [smul_eq_mul, smul_eq_mul]
    have h1 : χ * (cLow * r) <= χ * S := mul_le_mul_of_nonneg_left hsrc_low' hχ0
    have hterm2 : c * ((1 - χ) * r) <= (1 - χ) * r := by
      have h1χ : 0 <= 1 - χ := by linarith
      calc c * ((1 - χ) * r) <= 1 * ((1 - χ) * r) :=
            mul_le_mul_of_nonneg_right hc1 (mul_nonneg h1χ hRnn)
        _ = (1 - χ) * r := one_mul _
    nlinarith [h1, hterm2, mul_le_mul_of_nonneg_left hccLow hχ0, hRnn, hχ0, hRnn]
  · -- off the source ⟹ off the support ⟹ value is `R`
    have hxsupp : x ∉ tsupport (bf.chi (rho k)) := fun h => hx (bf.chi_supp (rho k) h)
    rw [gSeqExt_inner_of_notMem (I := I) Φ R bf hsrc htgt (rho k) t x hxsupp v v]
    calc c * R.inner x v v <= 1 * R.inner x v v :=
          mul_le_mul_of_nonneg_right hc1 hRnn
      _ = R.inner x v v := one_mul _

end Low

/-! ### `hbdd`: uniform covariant-derivative bounds on every compact -/

section Bdd

/-- **`hbdd` for the bump-extended sequence.**  From a cited uniform covariant-derivative
bound on the sources — for each order `q`, a single constant bounding
`metricCovDerivNorm q (gSeqExt (ρ k) t) R` on `Φ.source (ρ k)` uniformly in `k` and `t` (the
tail input, discharged in Brick 5 from Theorem 3.9's window covariant bounds transported to the
source flows via `metricCovDerivNorm_pullback`/`_restrictOpen` + bump-locality) — the
bump-extended metrics `gSeqExt (ρ k) t` satisfy a single uniform covariant bound on every
compact `K'`.  The tail indices (`k` large, `K' ⊆ grow (ρ k) ⊆ Φ.source (ρ k)`) inherit the
cited source bound; the finitely many head/mid indices are bounded wholesale by
`metricCovDerivNorm_bddOn` (each `gSeqExt (ρ k) t` is one fixed smooth metric, bounded on the
compact `K'`), and the finite maximum combines them.  This is the `hbdd` hypothesis consumed by
`windowGInfAll`. -/
theorem hbdd_gSeqExt
    (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (β ψ : Real)
    (hcovTail : letI : TopologicalSpace P.M := P.topology;
        letI : ChartedSpace H P.M := P.charted; letI : T2Space P.M := P.t2;
        letI : IsManifold I ∞ P.M := P.smooth; letI : SigmaCompactSpace P.M := P.sigmaCompact;
      forall q : Nat, exists C : Real, forall (k : Nat) (t : Real), t ∈ Set.Icc β ψ ->
        forall z : P.M, z ∈ Φ.source k ->
          metricCovDerivNorm (I := I) q (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z <= C) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    forall rho : Nat -> Nat, StrictMono rho -> forall t, t ∈ Set.Icc β ψ ->
      forall q : Nat, forall K' : Set P.M, IsCompact K' -> exists C : Real,
        forall (k : Nat) (z : P.M), z ∈ K' ->
          metricCovDerivNorm (I := I) q (gSeqExt (I := I) Φ R bf hsrc htgt (rho k) t) R z <= C := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  intro rho hrho t ht q K' hK'
  -- TAIL: the cited uniform source covariant bound.
  obtain ⟨Ctail, hCtail⟩ := hcovTail q
  -- eventual covering: `K' ⊆ grow (ρ k)` for all `k ≥ k0`.
  obtain ⟨k0, hk0⟩ := bf.grow_cover K' hK'
  -- HEAD/MID: for each index `k`, bound the single fixed metric on `K'`.
  have hhead : forall k : Nat, exists Ck : Real, forall z : P.M, z ∈ K' ->
      metricCovDerivNorm (I := I) q (gSeqExt (I := I) Φ R bf hsrc htgt (rho k) t) R z <= Ck := by
    intro k
    exact metricCovDerivNorm_bddOn (I := I) hK' q
      (gSeqExt (I := I) Φ R bf hsrc htgt (rho k) t) R
  choose Chead hChead using hhead
  -- combine: the tail constant with the finite head maximum over `k < k0`.
  have hne : (Finset.range (k0 + 1)).Nonempty := ⟨0, Finset.mem_range.2 (Nat.succ_pos k0)⟩
  refine ⟨max Ctail ((Finset.range (k0 + 1)).sup' hne Chead), fun k z hz => ?_⟩
  by_cases hk : k0 <= k
  · -- tail: `k0 ≤ k ≤ ρ k`, so `z ∈ K' ⊆ grow (ρ k) ⊆ Φ.source (ρ k)`.
    have hk' : k0 <= rho k := le_trans hk (hrho.id_le k)
    have hzsrc : z ∈ Φ.source (rho k) := bf.grow_subset (rho k) (hk0 (rho k) hk' hz)
    exact le_trans (hCtail (rho k) t ht z hzsrc) (le_max_left _ _)
  · -- head/mid: `k < k0`, use the fixed-metric bound and the finite maximum.
    have hklt : k < k0 := Nat.lt_of_not_le hk
    refine le_trans (hChead k z hz) (le_trans ?_ (le_max_right _ _))
    exact Finset.le_sup' Chead (Finset.mem_range.2 (by omega))

end Bdd

/-! ### `hgLip`: uniform time-Lipschitz bounds on every compact, all orders -/

section Lip

open Tensor0SBundle in
set_option backward.isDefEq.respectTransparency false in
/-- **`hgLip` for the bump-extended sequence.**  Two cited inputs:

* `hlipTail` — a uniform (in `k`) time-Lipschitz bound at `gSeqExt` granularity on the
  agreement regions `grow k` (its Brick-5 discharger: bump-locality — `chi k = 1` on an
  open neighborhood of `grow k` (`BumpFamily.chi_one`), where `gSeqExt` literally agrees
  with the pulled-back source metric, plus the transported source-flow Lipschitz
  producers `hgLipFinSol`/`hgLip0Sol` on `sourceFlow Φ k`);
* `hlipSrc` — a per-`k` source-granularity time-Lipschitz bound on compacts of the
  source domain, against the restricted reference `R.restrictOpen` (its discharger:
  `hgLipFinSol`/`hgLip0Sol` on `sourceFlow Φ k`).

Conclusion: the raw `hgLip` hypothesis of `windowGInfAll` for `gSeqExt` — for every
compact `K'` and order budget `p` a single `L ≥ 0`, uniform in `k`, with
`|∇_R^a(gSeqExt k s − gSeqExt k t)|_R(x) ≤ L·|s − t|` for all `k`, window times `s, t`,
orders `a ≤ p`, and `x ∈ K'`.

Route: the time difference kills the reference summand.  Tail indices (`K' ⊆ grow k`
from `grow_cover`) inherit `hlipTail`.  For each of the finitely many head/mid indices,
points of `K' ∩ tsupport (chi k)` (compact, inside the source) are handled by the
χ-Leibniz collar tower on the source domain: `metricDerivNorm_restrictOpen` localizes,
`metricDerivNorm_eq_iterCov` converts to the `iterCov` norm, the difference field is the
function-scaled field `chi k · (src_s − src_t)` (`gSeqExt_inner_of_mem`), and
`iterCov_smulF_le` bounds it by `∑_c binom(a,c)·|∇^c chi|·|∇^{a−c}(src_s − src_t)|`; the
`chi` factors are bounded on the compact by `sqrtNormSq0S_bddOn`, the source factor
carries `|s − t|` from `hlipSrc`, and `∑_c binom(a,c) = 2^a ≤ 2^p`.  Off
`tsupport (chi k)` the restricted metrics have equal metric tensor fields
(`gSeqExt_inner_of_notMem`), so the difference norm vanishes (`metricDerivNorm_self`).
The tail constant and the finitely many head constants combine by `max`/`Finset.sup'`. -/
theorem hgLip_gSeqExt
    (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (β ψ : Real)
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
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    forall K' : Set P.M, IsCompact K' -> forall p : Nat,
      exists Lp : Real, 0 <= Lp /\
        forall k : Nat, forall s, s ∈ Set.Icc β ψ -> forall t, t ∈ Set.Icc β ψ ->
          forall a : Nat, a <= p -> forall x, x ∈ K' ->
            metricDerivNorm (I := I) a (gSeqExt (I := I) Φ R bf hsrc htgt k s)
              (gSeqExt (I := I) Φ R bf hsrc htgt k t) R x <= Lp * |s - t| := by
  classical
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  intro K' hK' p
  -- TAIL: the cited gSeqExt-granularity Lipschitz bound on the agreement regions.
  obtain ⟨Lt, hLt0, hLt⟩ := hlipTail p
  obtain ⟨k0, hk0⟩ := bf.grow_cover K' hK'
  -- HEAD/MID: for each single index `k`, a Lipschitz constant valid on all of `K'`.
  have hhead : forall k : Nat, exists Lk : Real, 0 <= Lk /\
      forall s, s ∈ Set.Icc β ψ -> forall t, t ∈ Set.Icc β ψ ->
        forall a : Nat, a <= p -> forall x, x ∈ K' ->
          metricDerivNorm (I := I) a (gSeqExt (I := I) Φ R bf hsrc htgt k s)
            (gSeqExt (I := I) Φ R bf hsrc htgt k t) R x <= Lk * |s - t| := by
    intro k
    -- source-domain instances
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
    -- the same instances at the `↥(sourceOpen Φ k)` spelling (for `restrictOpen`)
    letI : SigmaCompactSpace ↥(sourceOpen (I := I) Φ k) := sourceDomSigmaOf (I := I) Φ k (hsrc k)
    letI : T2Space ↥(sourceOpen (I := I) Φ k) := sourceDomT2 (I := I) Φ k
    letI : IsManifold I ∞ ↥(sourceOpen (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
    letI : IsManifold I 1 ↥(sourceOpen (I := I) Φ k) :=
      IsManifold.of_le (I := I) (M := ↥(sourceOpen (I := I) Φ k)) (n := (∞ : WithTop ℕ∞))
        (by decide : (1 : WithTop ℕ∞) <= ∞)
    letI : IsManifold I 2 ↥(sourceOpen (I := I) Φ k) :=
      IsManifold.of_le (I := I) (M := ↥(sourceOpen (I := I) Φ k)) (n := (∞ : WithTop ℕ∞))
        (by decide : (2 : WithTop ℕ∞) <= ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) ↥(sourceOpen (I := I) Φ k) := by
      change IsManifold I ∞ (SourceDomain (I := I) Φ k); infer_instance
    -- the compact collar window inside the source
    have hKTc : IsCompact (K' ∩ tsupport (bf.chi k)) :=
      hK'.inter_right (isClosed_tsupport (bf.chi k))
    have hKTsub : K' ∩ tsupport (bf.chi k) ⊆ Φ.source k := fun z hz => bf.chi_supp k hz.2
    have hCc : IsCompact (sourceCompactSet (I := I) Φ k (K' ∩ tsupport (bf.chi k))) :=
      sourceCompactSet_isCompact (I := I) Φ k hKTc hKTsub
    -- cited per-k source-granularity Lipschitz bound on that compact
    obtain ⟨Ls, hLs0, hLs⟩ :=
      hlipSrc k (sourceCompactSet (I := I) Φ k (K' ∩ tsupport (bf.chi k))) hCc p
    -- the restricted bump as a smooth function on the source domain
    set χ' : SourceDomain (I := I) Φ k -> Real :=
      fun y => bf.chi k (y : P.M) with hχ'def
    have hχ' : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ' :=
      (bf.chi_smooth k).comp (contMDiff_subtype_val (I := I) (U := sourceOpen (I := I) Φ k))
    -- χ-factor bounds on the compact, one per derivative order `c`
    have hχB : forall c : Nat, exists Cc : Real, 0 <= Cc /\
        forall y, y ∈ sourceCompactSet (I := I) Φ k (K' ∩ tsupport (bf.chi k)) ->
          Real.sqrt (normSq0S (I := I)
            (refRes (I := I) Φ R hsrc k) y (0 + c)
            (iterCov (I := I) (refRes (I := I) Φ R hsrc k) 0
              (Tensor0SField.fromScalarField (𝕜 := Real) (E := E) (H := H) (I := I)
                (M := SourceDomain (I := I) Φ k) (∞ : WithTop ℕ∞) χ' hχ') c y)) <= Cc :=
      fun c => sqrtNormSq0S_bddOn (I := I) hCc (0 + c)
        (refRes (I := I) Φ R hsrc k)
        (iterCov (I := I) (refRes (I := I) Φ R hsrc k) 0
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
    · -- collar/interior: the χ-Leibniz estimate on the source domain
      have hxU : x ∈ Φ.source k := bf.chi_supp k hxsupp
      have hyC : (⟨x, hxU⟩ : SourceDomain (I := I) Φ k) ∈
          sourceCompactSet (I := I) Φ k (K' ∩ tsupport (bf.chi k)) := ⟨hx, hxsupp⟩
      -- orthonormal basis of the restricted reference at the point
      obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I)
        (refRes (I := I) Φ R hsrc k)
        (⟨x, hxU⟩ : SourceDomain (I := I) Φ k)
      have hinv : MetricInverseInBasis_gen (I := I)
          (refRes (I := I) Φ R hsrc k)
          (⟨x, hxU⟩ : SourceDomain (I := I) Φ k) basis
          (identityInvMetric (Idx := Fin (Module.finrank Real
            (TangentSpace I (⟨x, hxU⟩ : SourceDomain (I := I) Φ k))))) := by
        have h' := metricInverseInBasis_of_orthonormal (I := I)
          (refRes (I := I) Φ R hsrc k) basis hON
        intro i j
        simpa [identityInvMetric, diagonalInvMetric] using h' i j
      -- the restricted difference field is the χ-scaled source difference field
      have hsmul : metricTensorField (I := I)
            ((gSeqExt (I := I) Φ R bf hsrc htgt k s).restrictOpen (I := I)
              (sourceOpen (I := I) Φ k))
          - metricTensorField (I := I)
            ((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I)
              (sourceOpen (I := I) Φ k))
          = tensor0SField_smulByFun (𝕜 := Real) (E := E) (H := H) (I := I)
              (M := SourceDomain (I := I) Φ k) (∞ : WithTop ℕ∞) χ' hχ'
              (metricTensorField (I := I) (srcMetric (I := I) Φ hsrc htgt k s)
                - metricTensorField (I := I) (srcMetric (I := I) Φ hsrc htgt k t)) := by
        refine DFunLike.ext _ _ (fun y => ?_)
        refine ContinuousMultilinearMap.ext (fun v => ?_)
        show (metricTensorField (I := I)
              ((gSeqExt (I := I) Φ R bf hsrc htgt k s).restrictOpen (I := I)
                (sourceOpen (I := I) Φ k)) y
            - metricTensorField (I := I)
              ((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I)
                (sourceOpen (I := I) Φ k)) y) v
          = (χ' y • (metricTensorField (I := I) (srcMetric (I := I) Φ hsrc htgt k s) y
              - metricTensorField (I := I) (srcMetric (I := I) Φ hsrc htgt k t) y)) v
        rw [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.smul_apply,
          ContinuousMultilinearMap.sub_apply]
        simp only [metricTensorField_apply, SmoothRiemannianMetric.restrictOpen_inner]
        rw [gSeqExt_inner_of_mem (I := I) Φ R bf hsrc htgt k s (y : P.M) y.2 (v 0) (v 1),
          gSeqExt_inner_of_mem (I := I) Φ R bf hsrc htgt k t (y : P.M) y.2 (v 0) (v 1)]
        simp only [hχ'def, smul_eq_mul]
        ring
      -- localize to the source domain and convert to the `iterCov` norm
      have hres : metricDerivNorm (I := I) a
            ((gSeqExt (I := I) Φ R bf hsrc htgt k s).restrictOpen (I := I)
              (sourceOpen (I := I) Φ k))
            ((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I)
              (sourceOpen (I := I) Φ k))
            (refRes (I := I) Φ R hsrc k)
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
          (refRes (I := I) Φ R hsrc k) a basis hinv,
        hsmul]
      -- the χ-Leibniz tower bound, then term-by-term estimates
      refine le_trans (iterCov_smulF_le (I := I)
        (refRes (I := I) Φ R hsrc k)
        (⟨x, hxU⟩ : SourceDomain (I := I) Φ k) basis hinv a χ' hχ'
        (metricTensorField (I := I) (srcMetric (I := I) Φ hsrc htgt k s)
          - metricTensorField (I := I) (srcMetric (I := I) Φ hsrc htgt k t))) ?_
      have hterm : forall c : Nat, c ∈ Finset.range (a + 1) ->
          (a.choose c : Real) *
            Real.sqrt (normSq0S (I := I)
              (refRes (I := I) Φ R hsrc k) (⟨x, hxU⟩ :
                SourceDomain (I := I) Φ k) (0 + c)
              (iterCov (I := I) (refRes (I := I) Φ R hsrc k) 0
                (Tensor0SField.fromScalarField (𝕜 := Real) (E := E) (H := H) (I := I)
                  (M := SourceDomain (I := I) Φ k) (∞ : WithTop ℕ∞) χ' hχ') c ⟨x, hxU⟩)) *
            Real.sqrt (normSq0S (I := I)
              (refRes (I := I) Φ R hsrc k) (⟨x, hxU⟩ :
                SourceDomain (I := I) Φ k) (2 + (a - c))
              (iterCov (I := I) (refRes (I := I) Φ R hsrc k) 2
                (metricTensorField (I := I) (srcMetric (I := I) Φ hsrc htgt k s)
                  - metricTensorField (I := I) (srcMetric (I := I) Φ hsrc htgt k t))
                (a - c) ⟨x, hxU⟩))
          <= (a.choose c : Real) * Cx * (Ls * |s - t|) := by
        intro c hc
        have hcp : c <= p := le_trans (Nat.le_of_lt_succ (Finset.mem_range.1 hc)) ha
        have hχle : Real.sqrt (normSq0S (I := I)
            (refRes (I := I) Φ R hsrc k) (⟨x, hxU⟩ :
              SourceDomain (I := I) Φ k) (0 + c)
            (iterCov (I := I) (refRes (I := I) Φ R hsrc k) 0
              (Tensor0SField.fromScalarField (𝕜 := Real) (E := E) (H := H) (I := I)
                (M := SourceDomain (I := I) Φ k) (∞ : WithTop ℕ∞) χ' hχ') c ⟨x, hxU⟩))
            <= Cx := le_trans (hCχ c ⟨x, hxU⟩ hyC) (hCxge c hcp)
        have hsle : Real.sqrt (normSq0S (I := I)
            (refRes (I := I) Φ R hsrc k) (⟨x, hxU⟩ :
              SourceDomain (I := I) Φ k) (2 + (a - c))
            (iterCov (I := I) (refRes (I := I) Φ R hsrc k) 2
              (metricTensorField (I := I) (srcMetric (I := I) Φ hsrc htgt k s)
                - metricTensorField (I := I) (srcMetric (I := I) Φ hsrc htgt k t))
              (a - c) ⟨x, hxU⟩)) <= Ls * |s - t| := by
          rw [← metricDerivNorm_eq_iterCov (I := I) (srcMetric (I := I) Φ hsrc htgt k s)
            (srcMetric (I := I) Φ hsrc htgt k t)
            (refRes (I := I) Φ R hsrc k) (a - c) basis hinv]
          exact hLs s t hs ht (a - c) (le_trans (Nat.sub_le a c) ha) ⟨x, hxU⟩ hyC
        calc (a.choose c : Real) *
              Real.sqrt (normSq0S (I := I)
                (refRes (I := I) Φ R hsrc k) (⟨x, hxU⟩ :
                  SourceDomain (I := I) Φ k) (0 + c)
                (iterCov (I := I) (refRes (I := I) Φ R hsrc k) 0
                  (Tensor0SField.fromScalarField (𝕜 := Real) (E := E) (H := H) (I := I)
                    (M := SourceDomain (I := I) Φ k) (∞ : WithTop ℕ∞) χ' hχ') c ⟨x, hxU⟩)) *
              Real.sqrt (normSq0S (I := I)
                (refRes (I := I) Φ R hsrc k) (⟨x, hxU⟩ :
                  SourceDomain (I := I) Φ k) (2 + (a - c))
                (iterCov (I := I) (refRes (I := I) Φ R hsrc k) 2
                  (metricTensorField (I := I) (srcMetric (I := I) Φ hsrc htgt k s)
                    - metricTensorField (I := I) (srcMetric (I := I) Φ hsrc htgt k t))
                  (a - c) ⟨x, hxU⟩))
            <= (a.choose c : Real) * Cx *
              Real.sqrt (normSq0S (I := I)
                (refRes (I := I) Φ R hsrc k) (⟨x, hxU⟩ :
                  SourceDomain (I := I) Φ k) (2 + (a - c))
                (iterCov (I := I) (refRes (I := I) Φ R hsrc k) 2
                  (metricTensorField (I := I) (srcMetric (I := I) Φ hsrc htgt k s)
                    - metricTensorField (I := I) (srcMetric (I := I) Φ hsrc htgt k t))
                  (a - c) ⟨x, hxU⟩)) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hχle (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)
          _ <= (a.choose c : Real) * Cx * (Ls * |s - t|) :=
              mul_le_mul_of_nonneg_left hsle (mul_nonneg (Nat.cast_nonneg _) hCx0)
      refine le_trans (Finset.sum_le_sum hterm) ?_
      -- collapse the binomial sum and compare `2^a ≤ 2^p`
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
    · -- off the bump support: both metrics restrict to `R`, the difference vanishes
      set U₀ : TopologicalSpace.Opens P.M :=
        ⟨(tsupport (bf.chi k))ᶜ, (isClosed_tsupport (bf.chi k)).isOpen_compl⟩ with hU₀def
      letI : ChartedSpace H ↥U₀ :=
        TopologicalSpace.Opens.instChartedSpace (H := H) (M := P.M) (s := U₀)
      letI : IsManifold I ∞ ↥U₀ := { U₀.instHasGroupoid (contDiffGroupoid ∞ I) with }
      letI : SigmaCompactSpace ↥U₀ := isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen I U₀.isOpen)
      letI : IsManifold I 1 ↥U₀ :=
        IsManifold.of_le (I := I) (M := ↥U₀) (n := (∞ : WithTop ℕ∞))
          (by decide : (1 : WithTop ℕ∞) <= ∞)
      letI : IsManifold I 2 ↥U₀ :=
        IsManifold.of_le (I := I) (M := ↥U₀) (n := (∞ : WithTop ℕ∞))
          (by decide : (2 : WithTop ℕ∞) <= ∞)
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) ↥U₀ := by
        change IsManifold I ∞ ↥U₀; infer_instance
      have hx0 : x ∈ U₀ := hxsupp
      have hres : metricDerivNorm (I := I) a
            ((gSeqExt (I := I) Φ R bf hsrc htgt k s).restrictOpen (I := I) U₀)
            ((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I) U₀)
            (R.restrictOpen (I := I) U₀) (⟨x, hx0⟩ : ↥U₀)
          = metricDerivNorm (I := I) a (gSeqExt (I := I) Φ R bf hsrc htgt k s)
            (gSeqExt (I := I) Φ R bf hsrc htgt k t) R x :=
        metricDerivNorm_restrictOpen (I := I) _ _ _ U₀ a ⟨x, hx0⟩
      -- equal metric tensor fields off the support
      have hmTF : metricTensorField (I := I)
            ((gSeqExt (I := I) Φ R bf hsrc htgt k s).restrictOpen (I := I) U₀)
          = metricTensorField (I := I)
            ((gSeqExt (I := I) Φ R bf hsrc htgt k t).restrictOpen (I := I) U₀) := by
        refine DFunLike.ext _ _ (fun y => ?_)
        refine ContinuousMultilinearMap.ext (fun v => ?_)
        simp only [metricTensorField_apply, SmoothRiemannianMetric.restrictOpen_inner]
        rw [gSeqExt_inner_of_notMem (I := I) Φ R bf hsrc htgt k s (y : P.M) y.2 (v 0) (v 1),
          gSeqExt_inner_of_notMem (I := I) Φ R bf hsrc htgt k t (y : P.M) y.2 (v 0) (v 1)]
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
  choose Lk hLk0 hLk using hhead
  have hne : (Finset.range (k0 + 1)).Nonempty := ⟨0, Finset.mem_range.2 (Nat.succ_pos k0)⟩
  refine ⟨max Lt ((Finset.range (k0 + 1)).sup' hne Lk),
    le_trans hLt0 (le_max_left _ _), fun k s hs t ht a ha x hx => ?_⟩
  by_cases hk : k0 <= k
  · -- tail: `K' ⊆ grow k`, the cited gSeqExt-granularity bound applies
    exact le_trans (hLt k s t hs ht a ha x (hk0 k hk hx))
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  · -- head/mid: the per-index constant, dominated by the finite maximum
    refine le_trans (hLk k s hs t ht a ha x hx)
      (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
    exact le_trans (Finset.le_sup' Lk (Finset.mem_range.2 (by omega)))
      (le_max_right _ _)

end Lip

end ConvField

end HCGCompactness
end DifferentialGeometry
