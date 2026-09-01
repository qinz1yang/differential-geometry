import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.Completeness
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphComposition

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff
open Set Topology TopologicalSpace

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable [I.Boundaryless]
variable {M : ℕ → Type u} [∀ j, MetricSpace (M j)] [∀ j, ChartedSpace H (M j)]
  [∀ j, IsManifold I ∞ (M j)] [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)]

section ApproxData

open Bundle

variable [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
variable [∀ j, IsRiemannianManifold I (M j)]
variable [NeZero (Module.finrank ℝ E)]

omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)]
  [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
omit [∀ (j : ℕ), SigmaCompactSpace (M j)] in
theorem tail_derivSup_lt
    (j₀ : ℕ)
    (U : ∀ n, Opens (M (j₀ + n)))
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hU : ∀ n k, (U n : Set (M (j₀ + n))) ⊆
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source)
    (gInf : ∀ n, SmoothRiemannianMetric I (U n))
    (hclose : ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n →
        ∀ l q : ℕ, q ≤ p → ∀ x : U n,
          metricDerivNorm (I := I) q
            (chainPullbackSeq (I := I) Ψ g (U n) (hU n) l)
            (gInf n) (gInf n) x ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n →
        ∀ l : ℕ, ∀ K : Set (U n), IsCompact K →
          metricDerivNormSupOn (I := I) K p
            (chainPullbackSeq (I := I) Ψ g (U n) (hU n) l)
            (gInf n) (gInf n) < ε := by
  intro ε hε p
  obtain ⟨n₀, hn₀⟩ := hclose (ε / 2) (by linarith) p
  refine ⟨n₀, fun n hn => ?_⟩
  intro l K _hK
  exact lt_of_le_of_lt
    (metricDerivNormSupOn_le_of_forall (I := I) K p
      (chainPullbackSeq (I := I) Ψ g (U n) (hU n) l)
      (gInf n) (gInf n) (ε / 2) (by linarith)
      (fun q hqp x _ => hn₀ n hn l q hqp x)) (by linarith)

omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
theorem tailFlatSup_lt
    (b : ∀ j, M j) (j₀ : ℕ)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hU : ∀ n k,
      (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n) : Set (M (j₀ + n))) ⊆
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source)
    (gInf : ∀ n, SmoothRiemannianMetric I
      (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)))
    (hclose : ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n →
        letI : SigmaCompactSpace
            (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)) :=
          isSigmaCompact_iff_sigmaCompactSpace.mp
            (Geometry.isSigmaCompact_of_isOpen I
              (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)).isOpen)
        ∀ l q : ℕ, q ≤ p →
          ∀ x : ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n),
            metricDerivNorm (I := I) q
              (chainPullbackSeq (I := I) Ψ g
                (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)) (hU n) l)
              (gInf n) (gInf n) x ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n →
        letI : SigmaCompactSpace
            (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)) :=
          isSigmaCompact_iff_sigmaCompactSpace.mp
            (Geometry.isSigmaCompact_of_isOpen I
              (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)).isOpen)
        letI : SigmaCompactSpace (tailBallOpen b j₀ n) :=
          isSigmaCompact_iff_sigmaCompactSpace.mp
            (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
        ∀ K : Set (tailBallOpen b j₀ n), IsCompact K →
          metricDerivNormSupOn (I := I) K p
            ((g (j₀ + n)).restrictOpen (I := I) (tailBallOpen b j₀ n))
            (tailMetric (I := I) b j₀ gInf n)
            (tailMetric (I := I) b j₀ gInf n) < ε := by
  intro ε hε p
  obtain ⟨n₀, hn₀⟩ := hclose (ε / 2) (by linarith) p
  refine ⟨n₀, fun n hn => ?_⟩
  let U := ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)
  let V := tailBallOpen b j₀ n
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let _ : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I V.isOpen)
  intro K _hK
  refine lt_of_le_of_lt
    (metricDerivNormSupOn_le_of_forall (I := I) K p
      ((g (j₀ + n)).restrictOpen (I := I) V)
      (tailMetric (I := I) b j₀ gInf n)
      (tailMetric (I := I) b j₀ gInf n) (ε / 2) (by linarith) ?_) (by linarith)
  intro q hqp x _hxK
  let inc : V → U := Opens.inclusion (tailBall_le_large b j₀ n)
  have hbig := hn₀ n hn 0 q hqp (inc x)
  rw [chainPullback_zero (I := I) Ψ g U (hU n)] at hbig
  calc
    metricDerivNorm (I := I) q
        ((g (j₀ + n)).restrictOpen (I := I) V)
        (tailMetric (I := I) b j₀ gInf n)
        (tailMetric (I := I) b j₀ gInf n) x =
      metricDerivNorm (I := I) q
        ((g (j₀ + n)).restrictOpen (I := I) U)
        (gInf n) (gInf n) (inc x) := by
          simpa only [U, V, inc, tailMetric,
            SmoothRiemannianMetric.restrictOpen_flat] using
            metricDerivNorm_flat (I := I) (tailBall_le_large b j₀ n)
              ((g (j₀ + n)).restrictOpen (I := I) U) (gInf n) (gInf n) q x
    _ ≤ ε / 2 := hbig

omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] in
def ambientCGConverges
    (j₀ : ℕ) (U : ∀ n, Opens (M (j₀ + n)))
    [∀ n, Nonempty (U n)] [∀ n, SigmaCompactSpace (U n)]
    (S : SmoothSeqSystem I (fun n => U n)) (O₀ : U 0)
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (gInf : ∀ n, SmoothRiemannianMetric I (U n))
    (hgInf : S.MetricCocycle gInf)
    (hstage : ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∀ K : Set (U k), IsCompact K →
        metricDerivNormSupOn (I := I) K p
          ((g (j₀ + k)).restrictOpen (I := I) (U k))
          (gInf k) (gInf k) < ε) :
    PointedRiemannianCGConverges (I := I)
      (chainAmbientSeq (I := I) j₀ U S O₀ g)
      (limitPointedCoc S O₀ gInf hgInf) id
      (chainAmbientMaps (I := I) j₀ U S O₀ g gInf hgInf) := by
  let Φ := chainAmbientMaps (I := I) j₀ U S O₀ g gInf hgInf
  have hσsrc : ∀ k : ℕ,
      letI : TopologicalSpace (limitPointedCoc S O₀ gInf hgInf).M :=
        (limitPointedCoc S O₀ gInf hgInf).topology
      IsSigmaCompact (Φ.source k) := by
    intro k
    let _ : TopologicalSpace (limitPointedCoc S O₀ gInf hgInf).M :=
      (limitPointedCoc S O₀ gInf hgInf).topology
    let _ : ChartedSpace H (limitPointedCoc S O₀ gInf hgInf).M :=
      (limitPointedCoc S O₀ gInf hgInf).charted
    let _ : SigmaCompactSpace (limitPointedCoc S O₀ gInf hgInf).M :=
      (limitPointedCoc S O₀ gInf hgInf).sigmaCompact
    exact Geometry.isSigmaCompact_of_isOpen I (Φ.source_open k)
  have hσtgt : ∀ k : ℕ,
      letI : TopologicalSpace
          ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).M :=
        ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).topology
      IsSigmaCompact (Φ.target k) := by
    intro k
    let _ : TopologicalSpace
        ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).M :=
      ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).topology
    let _ : ChartedSpace H
        ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).M :=
      ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).charted
    let _ : SigmaCompactSpace
        ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).M :=
      ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).sigmaCompact
    exact Geometry.isSigmaCompact_of_isOpen I (Φ.target_open k)
  let refMetric : ∀ k : ℕ,
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomTop (I := I) Φ k
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomSmooth (I := I) Φ k
      SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k) := fun k => by
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomTop (I := I) Φ k
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomCharted (I := I) Φ k
    letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomSmooth (I := I) Φ k
    letI : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomSigmaOf (I := I) Φ k (hσsrc k)
    letI : T2Space (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomT2 (I := I) Φ k
    exact (S.limitMetric gInf hgInf).restrictOpen (I := I) (metricSourceOpen (I := I) Φ k)
  refine PointedRiemannianCGConverges.ofRestrictPullback (I := I)
    Φ hσsrc refMetric ?_
  intro K hK p ε hε
  obtain ⟨kSrc, hkSrc⟩ := Φ.source_subset hK
  obtain ⟨kConv, hkConv⟩ := hstage ε hε p
  refine ⟨max kSrc kConv, fun k hk => ?_⟩
  have hkS : kSrc ≤ k := le_trans (Nat.le_max_left kSrc kConv) hk
  have hkC : kConv ≤ k := le_trans (Nat.le_max_right kSrc kConv) hk
  let _ : TopologicalSpace (limitPointedCoc S O₀ gInf hgInf).M :=
    (limitPointedCoc S O₀ gInf hgInf).topology
  let _ : ChartedSpace H (limitPointedCoc S O₀ gInf hgInf).M :=
    (limitPointedCoc S O₀ gInf hgInf).charted
  let _ : TopologicalSpace
      ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).M :=
    ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).topology
  let _ : ChartedSpace H
      ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).M :=
    ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).charted
  let _ : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomTop (I := I) Φ k
  let _ : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomCharted (I := I) Φ k
  let _ : T2Space (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomT2 (I := I) Φ k
  let _ : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomSmooth (I := I) Φ k
  let _ : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomSigmaOf (I := I) Φ k (hσsrc k)
  let _ : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomTop (I := I) Φ k
  let _ : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomCharted (I := I) Φ k
  let _ : T2Space (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomT2 (I := I) Φ k
  let _ : IsManifold I ∞ (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomSmooth (I := I) Φ k
  let _ : SigmaCompactSpace (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomSigmaOf (I := I) Φ k (hσtgt k)
  let F := metricSourceTargetDiff (I := I) Φ k
  let sourceMetric : SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k) :=
    (S.limitMetric gInf hgInf).restrictOpen (I := I) (metricSourceOpen (I := I) Φ k)
  let targetSeq : SmoothRiemannianMetric I (MetricTargetDomain (I := I) Φ k) := by
    change SmoothRiemannianMetric I (U k)
    exact (g (j₀ + k)).restrictOpen (I := I) (U k)
  let targetLim : SmoothRiemannianMetric I (MetricTargetDomain (I := I) Φ k) := by
    change SmoothRiemannianMetric I (U k)
    exact gInf k
  have hlim : sourceMetric = Diffeomorph.pullbackMetric (I := I) targetLim F := by
    have metric_ext : ∀ (g₁ g₂ : SmoothRiemannianMetric I
        (MetricSourceDomain (I := I) Φ k)),
        (∀ (x : MetricSourceDomain (I := I) Φ k) (v w : TangentSpace I x),
          g₁.inner x v w = g₂.inner x v w) → g₁ = g₂ := by
      intro g₁ g₂ h
      obtain ⟨i₁, s₁, p₁, b₁, c₁⟩ := g₁
      obtain ⟨i₂, s₂, p₂, b₂, c₂⟩ := g₂
      have hi : i₁ = i₂ :=
        funext fun x => ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => h x v w
      subst hi
      rfl
    apply metric_ext
    intro x v w
    let inclS : MetricSourceDomain (I := I) Φ k →
        (limitPointedCoc S O₀ gInf hgInf).M := Subtype.val
    have hsrc : sourceMetric.inner x v w =
        (S.limitMetric gInf hgInf).inner
          (x : (limitPointedCoc S O₀ gInf hgInf).M)
          (mfderiv I I inclS x v) (mfderiv I I inclS x w) := by
      rw [SmoothRiemannianMetric.restrictOpen_inner,
        mfderiv_subtype_val_apply, mfderiv_subtype_val_apply]
    have htgt :
        (Diffeomorph.pullbackMetric (I := I) targetLim F).inner x v w =
          (gInf k).inner (F x : U k)
            (mfderiv I I F x v) (mfderiv I I F x w) := by
      dsimp only [targetLim]
      rw [Diffeomorph.pullbackMetric_inner]
      rfl
    rw [hsrc, htgt]
    rw [S.limitMetric_of_mem gInf hgInf k x.2]
    rw [metricSourceTargetDiff_mfderiv (I := I) Φ k x v,
      metricSourceTargetDiff_mfderiv (I := I) Φ k x w]
    simp only [inclS, mfderiv_subtype_val_apply]
    let z : (limitPointedCoc S O₀ gInf hgInf).M := x
    have hxSource : z ∈ (S.inclPartialDiffeo k).source := by
      change z ∈ Set.range (S.toSeqSystem.incl k)
      exact x.2
    have hFx : (F x : U k) = Function.invFun (S.toSeqSystem.incl k) z := by
      apply Subtype.ext
      have hmapPoint : Φ.map k z =
          ((Function.invFun (S.toSeqSystem.incl k) z : U k) : M (j₀ + k)) := rfl
      exact (metricSourceTargetDiff_apply (I := I) Φ k x).trans hmapPoint
    have hmapv : mfderiv I I (Φ.map k) z v =
        mfderiv I I
          (S.inclPartialDiffeo k : (limitPointedCoc S O₀ gInf hgInf).M → U k)
          z v := by
      change mfderiv I I
        (PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo k) rfl :
          (limitPointedCoc S O₀ gInf hgInf).M → M (j₀ + k)) z v = _
      exact PartialDiffeomorph.liftOpen_mfderiv
        (S.inclPartialDiffeo k) rfl hxSource v
    have hmapw : mfderiv I I (Φ.map k) z w =
        mfderiv I I
          (S.inclPartialDiffeo k : (limitPointedCoc S O₀ gInf hgInf).M → U k)
          z w := by
      change mfderiv I I
        (PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo k) rfl :
          (limitPointedCoc S O₀ gInf hgInf).M → M (j₀ + k)) z w = _
      exact PartialDiffeomorph.liftOpen_mfderiv
        (S.inclPartialDiffeo k) rfl hxSource w
    rw [hFx, hmapv, hmapw]
    rfl
  change metricDerivNormSupOn (I := I)
      (metricSourceCompactSet (I := I) Φ k K) p
      (Diffeomorph.pullbackMetric (I := I) targetSeq F)
      sourceMetric sourceMetric < ε
  rw [hlim, metricDerivNormSupOn_pullback_image (I := I)]
  have hKsource : IsCompact (metricSourceCompactSet (I := I) Φ k K) :=
    metricSourceCompactSet_isCompact (I := I) Φ k hK (hkSrc k hkS)
  have hKtarget : IsCompact (F '' metricSourceCompactSet (I := I) Φ k K) :=
    hKsource.image F.continuous
  with_unfolding_all
    exact hkConv k hkC _ hKtarget

omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] in
def chainCGConverges
    (j₀ : ℕ) (U : ∀ n, Opens (M (j₀ + n)))
    [∀ n, Nonempty (U n)] [∀ n, SigmaCompactSpace (U n)]
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hU : ∀ n k, (U n : Set (M (j₀ + n))) ⊆
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source)
    (hmap : ∀ n,
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
        M (j₀ + n) → M (j₀ + (n + 1))) '' (U n : Set (M (j₀ + n))) ⊆
        (U (n + 1) : Set (M (j₀ + (n + 1)))))
    (gInf : ∀ n, SmoothRiemannianMetric I (U n))
    (hstep : ∀ n,
      let F : U n → U (n + 1) := PartialDiffeomorph.opensMap
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hmap n)
      ∀ (x : U n) (v w : TangentSpace I x),
        (gInf n).inner x v w =
          (gInf (n + 1)).inner (F x)
            (mfderiv I I F x v) (mfderiv I I F x w))
    (hclose : ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n →
        letI : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
          (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
        ∀ l q : ℕ, q ≤ p → ∀ x : U n,
          metricDerivNorm (I := I) q
            (chainPullbackSeq (I := I) Ψ g (U n) (hU n) l)
            (gInf n) (gInf n) x ≤ ε)
    (O₀ : U 0) :
    let S := chainBallSystem (I := I) j₀ U Ψ hU hmap
    let gSeq : ∀ n, SmoothRiemannianMetric I (U n) := fun n =>
      chainPullbackSeq (I := I) Ψ g (U n) (hU n) 0
    let hgInf : S.MetricCocycle gInf :=
      chainMetricCocycle (I := I) j₀ U Ψ hU hmap gInf hstep
    PointedRiemannianCGConverges (I := I)
      (factorSeq S O₀ gSeq) (limitPointedCoc S O₀ gInf hgInf) id
      (limitCGMapsOf S O₀ gSeq gInf hgInf) := by
  let S := chainBallSystem (I := I) j₀ U Ψ hU hmap
  let gSeq : ∀ n, SmoothRiemannianMetric I (U n) := fun n =>
    chainPullbackSeq (I := I) Ψ g (U n) (hU n) 0
  let hgInf : S.MetricCocycle gInf :=
    chainMetricCocycle (I := I) j₀ U Ψ hU hmap gInf hstep
  apply limitCGConverges (I := I) S O₀ gSeq gInf hgInf
  intro ε hε p
  obtain ⟨n₀, hn₀⟩ := tail_derivSup_lt (I := I) j₀ U Ψ g hU gInf hclose ε hε p
  refine ⟨n₀, fun n hn K hK => ?_⟩
  simpa only [gSeq] using hn₀ n hn 0 K hK

omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] in
def chainAmbientConv
    (j₀ : ℕ) (U : ∀ n, Opens (M (j₀ + n)))
    [∀ n, Nonempty (U n)] [∀ n, SigmaCompactSpace (U n)]
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hU : ∀ n k, (U n : Set (M (j₀ + n))) ⊆
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source)
    (hmap : ∀ n,
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
        M (j₀ + n) → M (j₀ + (n + 1))) '' (U n : Set (M (j₀ + n))) ⊆
        (U (n + 1) : Set (M (j₀ + (n + 1)))))
    (gInf : ∀ n, SmoothRiemannianMetric I (U n))
    (hstep : ∀ n,
      let F : U n → U (n + 1) := PartialDiffeomorph.opensMap
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hmap n)
      ∀ (x : U n) (v w : TangentSpace I x),
        (gInf n).inner x v w =
          (gInf (n + 1)).inner (F x)
            (mfderiv I I F x v) (mfderiv I I F x w))
    (hclose : ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n →
        letI : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
          (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
        ∀ l q : ℕ, q ≤ p → ∀ x : U n,
          metricDerivNorm (I := I) q
            (chainPullbackSeq (I := I) Ψ g (U n) (hU n) l)
            (gInf n) (gInf n) x ≤ ε)
    (O₀ : U 0) :
    let S := chainBallSystem (I := I) j₀ U Ψ hU hmap
    let hgInf : S.MetricCocycle gInf :=
      chainMetricCocycle (I := I) j₀ U Ψ hU hmap gInf hstep
    PointedRiemannianCGConverges (I := I)
      (chainAmbientSeq (I := I) j₀ U S O₀ g)
      (limitPointedCoc S O₀ gInf hgInf) id
      (chainAmbientMaps (I := I) j₀ U S O₀ g gInf hgInf) := by
  let S := chainBallSystem (I := I) j₀ U Ψ hU hmap
  let hgInf : S.MetricCocycle gInf :=
    chainMetricCocycle (I := I) j₀ U Ψ hU hmap gInf hstep
  apply ambientCGConverges (I := I) j₀ U S O₀ g gInf hgInf
  intro ε hε p
  obtain ⟨n₀, hn₀⟩ := tail_derivSup_lt (I := I) j₀ U Ψ g hU gInf hclose ε hε p
  refine ⟨n₀, fun n hn K hK => ?_⟩
  rw [← chainPullback_zero (I := I) Ψ g (U n) (hU n)]
  exact hn₀ n hn 0 K hK

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def tailAmbientConv
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (j₀ : ℕ)
    (D₀ : ∀ n k, PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
      (g (j₀ + n)) (g ((j₀ + n) + k)))
    (hU : ∀ n k,
      (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n) : Set (M (j₀ + n))) ⊆
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source)
    (hmap : ∀ n,
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
        M (j₀ + n) → M (j₀ + (n + 1))) ''
          (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n) : Set (M (j₀ + n))) ⊆
        (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + (n + 1)) :
          Set (M (j₀ + (n + 1)))))
    (gInf : ∀ n, SmoothRiemannianMetric I
      (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)))
    (hstep : ∀ n,
      let F : ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n) →
          ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + (n + 1)) :=
        PartialDiffeomorph.opensMap
          (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hmap n)
      ∀ (x : ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n))
        (v w : TangentSpace I x),
        (gInf n).inner x v w =
          (gInf (n + 1)).inner (F x)
            (mfderiv I I F x v) (mfderiv I I F x w))
    (hclose : ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n →
        letI : SigmaCompactSpace
            (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)) :=
          isSigmaCompact_iff_sigmaCompactSpace.mp
            (Geometry.isSigmaCompact_of_isOpen I
              (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)).isOpen)
        ∀ l q : ℕ, q ≤ p →
          ∀ x : ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n),
            metricDerivNorm (I := I) q
              (chainPullbackSeq (I := I) Ψ g
                (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)) (hU n) l)
              (gInf n) (gInf n) x ≤ ε) :
    letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tailBall_nonempty b j₀ n
    letI : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
      isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
    let S := tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀
    let gTail := tailMetric (I := I) b j₀ gInf
    let hgTail : S.MetricCocycle gTail :=
      tailMetricCocycle (I := I) b Ψ hbase g hnorm j₀ D₀ hU hmap gInf hstep
    PointedRiemannianCGConverges (I := I)
      (chainAmbientSeq (I := I) j₀ (tailBallOpen b j₀) S (tailCenter b j₀ 0) g)
      (limitPointedCoc S (tailCenter b j₀ 0) gTail hgTail) id
      (chainAmbientMaps (I := I) j₀ (tailBallOpen b j₀) S
        (tailCenter b j₀ 0) g gTail hgTail) := by
  letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tailBall_nonempty b j₀ n
  letI : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
  let S := tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀
  let gTail := tailMetric (I := I) b j₀ gInf
  let hgTail : S.MetricCocycle gTail :=
    tailMetricCocycle (I := I) b Ψ hbase g hnorm j₀ D₀ hU hmap gInf hstep
  apply ambientCGConverges (I := I) j₀ (tailBallOpen b j₀) S
    (tailCenter b j₀ 0) g gTail hgTail
  exact tailFlatSup_lt (I := I) b j₀ Ψ g hU gInf hclose

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def ballSystemOfData
    (b : ∀ j, M j) (r ε : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hε : ∀ j, 0 ≤ ε j)
    (p : ℕ → ℕ)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (D : ∀ j, PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b j) (r j)) (ε j) (p j) (Ψ j) (g j) (g (j + 1)))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (hgrow : ∀ j, Real.sqrt (1 + ε j) * r j < r (j + 1)) :
    letI : ∀ j, Nonempty (ballOpen b r j) := fun j => ballOpen_nonempty b r j (hr j)
    SmoothSeqSystem I (fun j => ballOpen b r j) := by
  letI : ∀ j, Nonempty (ballOpen b r j) := fun j => ballOpen_nonempty b r j (hr j)
  have hsrc : ∀ j, (ballOpen b r j : Set (M j)) ⊆ (Ψ j).source := by
    intro j x hx
    apply (D j).source_sub
    exact Metric.mem_closedBall.mpr (Metric.mem_ball.mp hx).le
  have hmap : ∀ j, (Ψ j : M j → M (j + 1)) '' (ballOpen b r j : Set (M j)) ⊆
      (ballOpen b r (j + 1) : Set (M (j + 1))) := by
    intro j
    have hdata : MapMetricApproximationOn (I := I)
        (Metric.closedEBall (b j) (ENNReal.ofReal (r j))) (ε j) (p j)
        (Ψ j : M j → M (j + 1)) (g j) (g (j + 1)) := by
      rw [Metric.closedEBall_ofReal (hr j).le]
      exact (D j).forward
    have hsource : Metric.closedEBall (b j) (ENNReal.ofReal (r j)) ⊆ (Ψ j).source := by
      rw [Metric.closedEBall_ofReal (hr j).le]
      exact (D j).source_sub
    simpa only [ballOpen, Opens.coe_mk, hbase j] using
      (data_image_metric_ball (I := I) (Ψ j) (hnorm j) (hnorm (j + 1))
        (hr j) le_rfl (hε j) (hgrow j) hdata hsource)
  exact ballSystem b r hr Ψ hsrc hmap

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
noncomputable def directedBallSystem
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (hdata : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ p : ℕ, ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∀ l : ℕ,
      Nonempty (PartialDiffeomorphMetricApproximation (I := I)
        (Metric.closedBall (b j) ((2 : ℝ) ^ j)) δ p
        (chainComp (I := I) (Mf := M) Ψ j l) (g j) (g (j + l)))) :
    Σ j₀ : ℕ,
      let b' : ∀ n, M (j₀ + n) := fun n => b (j₀ + n)
      let r' : ℕ → ℝ := fun n => (2 : ℝ) ^ (j₀ + n)
      letI : ∀ n, Nonempty (ballOpen b' r' n) :=
        fun n => ballOpen_nonempty b' r' n (by positivity)
      SmoothSeqSystem I (fun n => ballOpen b' r' n) := by
  classical
  let hex := hdata (1 / 2) (by norm_num) (by norm_num) 0
  let j₀ := Classical.choose hex
  have hj₀ := Classical.choose_spec hex
  refine ⟨j₀, ?_⟩
  let b' : ∀ n, M (j₀ + n) := fun n => b (j₀ + n)
  let r' : ℕ → ℝ := fun n => (2 : ℝ) ^ (j₀ + n)
  let Ψ' : ∀ n, PartialDiffeomorph I I (M (j₀ + n)) (M (j₀ + (n + 1)))
      (∞ : WithTop ℕ∞) := fun n =>
    chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1
  let g' : ∀ n, SmoothRiemannianMetric I (M (j₀ + n)) := fun n => g (j₀ + n)
  letI : ∀ n, Nonempty (ballOpen b' r' n) :=
    fun n => ballOpen_nonempty b' r' n (by dsimp [r']; positivity)
  have hD : ∀ n, Nonempty (PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b' n) (r' n)) (1 / 2) 0 (Ψ' n) (g' n) (g' (n + 1))) := by
    intro n
    exact hj₀ (j₀ + n) (Nat.le_add_right j₀ n) 1
  let D : ∀ n, PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b' n) (r' n)) (1 / 2) 0 (Ψ' n) (g' n) (g' (n + 1)) :=
    fun n => Classical.choice (hD n)
  have hbase' : ∀ n, (Ψ' n : M (j₀ + n) → M (j₀ + (n + 1))) (b' n) = b' (n + 1) := by
    intro n
    exact chainComp_base (I := I) (Mf := M) Ψ b hbase (j₀ + n) 1
  have hnorm' : ∀ n (x : M (j₀ + n)) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g' n).inner x v v)) := by
    intro n
    exact hnorm (j₀ + n)
  have hgrow : ∀ n, Real.sqrt (1 + (1 / 2 : ℝ)) * r' n < r' (n + 1) := by
    intro n
    have hsqrt : Real.sqrt (1 + (1 / 2 : ℝ)) < 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2)]
    calc
      Real.sqrt (1 + (1 / 2 : ℝ)) * r' n < 2 * r' n :=
        mul_lt_mul_of_pos_right hsqrt (by dsimp [r']; positivity)
      _ = r' (n + 1) := by
        dsimp [r']
        rw [show j₀ + (n + 1) = (j₀ + n) + 1 by omega]
        rw [pow_succ]
        ring
  exact ballSystemOfData b' r' (fun _ => 1 / 2) (fun n => by dsimp [r']; positivity)
    (fun _ => by norm_num) (fun _ => 0) Ψ' hbase' g' D hnorm' hgrow

end ApproxData

end HCGCompactness
end DifferentialGeometry
