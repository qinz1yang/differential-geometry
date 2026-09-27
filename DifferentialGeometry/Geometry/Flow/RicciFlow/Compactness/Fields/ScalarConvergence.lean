import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Equation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.MetricLowerBound
import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.Scalar
import DifferentialGeometry.Topology.UniformConvergence

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Set Bundle Manifold Filter
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]

variable {X : PointedFlowSeq (I := I)}
variable {P : PointedRiemannianManifold (I := I)}
variable {subseq : ℕ → ℕ}
variable (Φ : PointedCGHMaps (I := I) X P subseq)

theorem FlowMetricConvergenceData.tendstoUniformlyOn_scalar
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    (beta psi : ℝ) (cLow : ℝ) (hcLow : 0 < cLow)
    (hbound : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
      ∀ (k : ℕ) (t : ℝ), t ∈ Set.Icc beta psi →
        ∀ (y : SourceDomain (I := I) Φ k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
              sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
              sourceDomCharted (I := I) Φ k
            TangentSpace I y),
          cLow * R.inner (y : P.M) v v ≤
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
      ∀ q : ℕ, q ≤ 2 → ∃ C : ℝ, ∀ (k : ℕ) (t : ℝ), t ∈ Set.Icc beta psi →
        ∀ z : P.M, z ∈ bf.grow k →
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z ≤ C)
    (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt beta psi)
    (K : Set P.M)
    (hK : letI : TopologicalSpace P.M := P.topology; IsCompact K) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    TendstoUniformlyOn
      (fun k (q : ℝ × P.M) ↦
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
        (X.term ((subseq ∘ co.φ) k)).S.scalar q.1 (Φ.map (co.φ k) q.2))
      (fun q ↦ metricScalarAt (I := I) (co.gInf q.1) q.2)
      atTop (Icc beta psi ×ˢ K) := by
  classical
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let lam : ℝ := min cLow 1
  have hlam : 0 < lam := by
    simpa only [lam] using lt_min hcLow one_pos
  have hlowSeq : ∀ (k : ℕ) (t : ℝ), t ∈ Set.Icc beta psi →
      ∀ (x : P.M) (v : TangentSpace I x),
        lam * R.inner x v v ≤
          (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) t).inner x v v := by
    intro k t ht x v
    simpa only [lam] using
      gSeqExt_lower (I := I) Φ R bf hsrc htgt cLow beta psi hcLow hbound
        (co.φ k) t ht x v
  have hlowInf : ∀ (t : ℝ), t ∈ Set.Icc beta psi →
      ∀ (x : P.M) (v : TangentSpace I x),
        lam * R.inner x v v ≤ (co.gInf t).inner x v v :=
    FlowMetricConvergenceData.lower_of (I := I) (Φ := Φ) co hlowSeq
  choose C hC using hcovTail
  let Cmax : ℝ := max (C 0 (by omega)) (max (C 1 (by omega)) (C 2 le_rfl))
  let B0 : ℝ := max 0 (Cmax + 1)
  have hCmax : ∀ (a : ℕ) (ha : a ≤ 2), C a ha ≤ Cmax := by
    intro a ha
    interval_cases a <;> simp only [Cmax, le_max_iff] <;> aesop
  obtain ⟨kgrow, hkgrow⟩ := bf.grow_cover K hK
  have hbddSeqC : ∀ (k : ℕ), kgrow ≤ k → ∀ (t : ℝ),
      t ∈ Set.Icc beta psi → ∀ (x : P.M), x ∈ K →
        ∀ (a : ℕ) (ha : a ≤ 2),
          metricCovDerivNorm (I := I) a
            (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) t) R x ≤ C a ha := by
    intro k hk t ht x hx a ha
    exact hC a ha (co.φ k) t ht x
      (hkgrow (co.φ k) (hk.trans (co.strictMono.id_le k)) hx)
  have hbddSeq : ∀ (k : ℕ), kgrow ≤ k → ∀ (t : ℝ),
      t ∈ Set.Icc beta psi → ∀ (x : P.M), x ∈ K →
        ∀ a : ℕ, a ≤ 2 →
          metricCovDerivNorm (I := I) a
            (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) t) R x ≤ B0 := by
    intro k hk t ht x hx a ha
    exact (hbddSeqC k hk t ht x hx a ha).trans
      ((hCmax a ha).trans
        ((le_add_of_nonneg_right zero_le_one).trans (le_max_right _ _)))
  obtain ⟨kconv, hkconv⟩ := co.convergence K hK 2 1 one_pos
  let kbase : ℕ := max kgrow kconv
  have hkbaseGrow : kgrow ≤ kbase := le_max_left _ _
  have hkbaseConv : kconv ≤ kbase := le_max_right _ _
  have hbddInf : ∀ (t : ℝ), t ∈ Set.Icc beta psi →
      ∀ (x : P.M), x ∈ K → ∀ a : ℕ, a ≤ 2 →
        metricCovDerivNorm (I := I) a (co.gInf t) R x ≤ B0 := by
    intro t ht x hx a ha
    have hdiff : metricDerivNorm (I := I) a (co.gInf t)
        (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ kbase) t) R x < 1 := by
      rw [metricDerivNorm_symm (I := I) a (co.gInf t)
        (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ kbase) t) R x]
      exact (derivNorm_le_sup (I := I) hK ha
        (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ kbase) t) (co.gInf t) R hx).trans_lt
          (hkconv kbase hkbaseConv t ht)
    have htri := covNorm_le_add (I := I) a (co.gInf t)
      (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ kbase) t) R x
    calc
      metricCovDerivNorm (I := I) a (co.gInf t) R x
          ≤ metricCovDerivNorm (I := I) a
              (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ kbase) t) R x +
            metricDerivNorm (I := I) a (co.gInf t)
              (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ kbase) t) R x := htri
      _ ≤ Cmax + 1 := add_le_add
        ((hbddSeqC kbase hkbaseGrow t ht x hx a ha).trans (hCmax a ha)) hdiff.le
      _ ≤ B0 := le_max_right _ _
  obtain ⟨Csc, hCsc, hscalar⟩ :=
    exists_abs_metricScalarAt_sub_le (I := I) R hK lam B0 hlam
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  let den : ℝ := 3 * Csc + 1
  have hden : 0 < den := by
    dsimp only [den]
    nlinarith
  let delta : ℝ := epsilon / den
  have hdelta : 0 < delta := div_pos hepsilon hden
  obtain ⟨kdelta, hkdelta⟩ := co.convergence K hK 2 delta hdelta
  filter_upwards [eventually_ge_atTop (max kgrow kdelta)] with k hk
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  have hkGrow : kgrow ≤ k := (le_max_left _ _).trans hk
  have hkDelta : kdelta ≤ k := (le_max_right _ _).trans hk
  let u := gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) t
  let rho := metricDerivNormSupOn (I := I) K 2 u (co.gInf t) R
  have hrho : rho < delta := by
    simpa only [rho, u] using hkdelta k hkDelta t ht
  have hsum :
      (∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u (co.gInf t) R x) ≤
        3 * rho := by
    calc
      (∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u (co.gInf t) R x)
          ≤ ∑ _q ∈ Finset.range 3, rho := by
            exact Finset.sum_le_sum fun q hq ↦
              derivNorm_le_sup (I := I) hK
                (Nat.le_of_lt_succ (Finset.mem_range.1 hq)) u (co.gInf t) R hx
      _ = 3 * rho := by norm_num
  have hlocal := hscalar u (co.gInf t)
    (fun y _hy xi ↦ hlowSeq k t ht y xi)
    (fun y _hy xi ↦ hlowInf t ht y xi)
    (fun y hy a ha ↦ hbddSeq k hkGrow t ht y hy a ha)
    (fun y hy a ha ↦ hbddInf t ht y hy a ha) x hx
  have hdeltaEq : delta * den = epsilon := by
    dsimp only [delta]
    exact div_mul_cancel₀ epsilon (ne_of_gt hden)
  have hprod : Csc * (3 * rho) < epsilon := by
    have hmul : 3 * Csc * rho < 3 * Csc * delta :=
      mul_lt_mul_of_pos_left hrho (mul_pos (by norm_num) hCsc)
    dsimp only [den] at hdeltaEq
    nlinarith
  have hmetric :
      |metricScalarAt (I := I) u x - metricScalarAt (I := I) (co.gInf t) x| < epsilon :=
    (hlocal.trans (mul_le_mul_of_nonneg_left hsum hCsc.le)).trans_lt hprod
  have hxgrow : x ∈ bf.grow (co.φ k) :=
    hkgrow (co.φ k) (hkGrow.trans (co.strictMono.id_le k)) hx
  dsimp only [u] at hmetric
  rw [gSeqExt_scalar (I := I) Φ R bf hsrc htgt (co.φ k) t x hxgrow] at hmetric
  simpa only [Function.comp_apply, Real.dist_eq, abs_sub_comm] using hmetric

theorem FlowMetricConvergenceData.continuousOn_scalar
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    (beta psi : ℝ) (cLow : ℝ) (hcLow : 0 < cLow)
    (hbound : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
      ∀ (k : ℕ) (t : ℝ), t ∈ Set.Icc beta psi →
        ∀ (y : SourceDomain (I := I) Φ k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
              sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
              sourceDomCharted (I := I) Φ k
            TangentSpace I y),
          cLow * R.inner (y : P.M) v v ≤
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
      ∀ q : ℕ, q ≤ 2 → ∃ C : ℝ, ∀ (k : ℕ) (t : ℝ), t ∈ Set.Icc beta psi →
        ∀ z : P.M, z ∈ bf.grow k →
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z ≤ C)
    (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt beta psi)
    (K : Set P.M)
    (hK : letI : TopologicalSpace P.M := P.topology; IsCompact K)
    (htime : Icc beta psi ⊆ X.D.carrier) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    ContinuousOn
      (fun q : ℝ × P.M => metricScalarAt (I := I) (co.gInf q.1) q.2)
      (Icc beta psi ×ˢ K) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let scalarSeq : ℕ → ℝ × P.M → ℝ := fun k q ↦
    let : TopologicalSpace (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).topology
    let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).charted
    let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).smooth
    let : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).sigmaCompact
    let : T2Space (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).t2
    (X.term (subseq (co.φ k))).S.scalar q.1 (Φ.map (co.φ k) q.2)
  let scalarLim : ℝ × P.M → ℝ := fun q ↦
    metricScalarAt (I := I) (co.gInf q.1) q.2
  let S : Set (ℝ × P.M) := Set.Icc beta psi ×ˢ K
  have hscalar : TendstoUniformlyOn scalarSeq scalarLim atTop S :=
    co.tendstoUniformlyOn_scalar Φ R bf hsrc htgt beta psi cLow hcLow hbound hcovTail K hK
  obtain ⟨kgrow, hkgrow⟩ := bf.grow_cover K hK
  have hscalarCont : ∀ᶠ k in Filter.atTop,
      ContinuousOn (scalarSeq k) S := by
    filter_upwards [Filter.eventually_ge_atTop kgrow] with k hk
    let : TopologicalSpace (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).topology
    let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).charted
    let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).smooth
    let : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).sigmaCompact
    let : T2Space (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).t2
    have hKsrc : K ⊆ Φ.source (co.φ k) := fun x hx ↦
      bf.grow_subset (co.φ k)
        (hkgrow (co.φ k) (hk.trans (co.strictMono.id_le k)) hx)
    have hmap : ContinuousOn (fun x : P.M ↦ Φ.map (co.φ k) x) K := by
      simpa only [PointedCGHMaps.map] using
        (Φ.partialDiffeomorph (co.φ k)).contMDiffOn_toFun.continuousOn.mono hKsrc
    have hpair : ContinuousOn
        (fun q : ℝ × P.M ↦ (q.1, Φ.map (co.φ k) q.2)) S :=
      continuousOn_fst.prodMk
        (hmap.comp continuousOn_snd (fun _ hq ↦ hq.2))
    have hmaps : MapsTo
        (fun q : ℝ × P.M ↦ (q.1, Φ.map (co.φ k) q.2)) S
        (X.D.carrier ×ˢ (Set.univ : Set (X.term (subseq (co.φ k))).M)) :=
      fun _ hq ↦ ⟨htime hq.1, Set.mem_univ _⟩
    simpa only [scalarSeq, Function.comp_def] using
      (X.term (subseq (co.φ k))).isSolution.scalarCont.comp hpair hmaps
  exact hscalar.continuousOn hscalarCont.frequently

theorem FlowMetricConvergenceData.tendstoUniformly_scalar
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    (beta psi : ℝ) (cLow : ℝ) (hcLow : 0 < cLow)
    (hbound : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
      ∀ (k : ℕ) (t : ℝ), t ∈ Set.Icc beta psi →
        ∀ (y : SourceDomain (I := I) Φ k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
              sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
              sourceDomCharted (I := I) Φ k
            TangentSpace I y),
          cLow * R.inner (y : P.M) v v ≤
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
      ∀ q : ℕ, q ≤ 2 → ∃ C : ℝ, ∀ (k : ℕ) (t : ℝ), t ∈ Set.Icc beta psi →
        ∀ z : P.M, z ∈ bf.grow k →
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z ≤ C)
    (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt beta psi)
    {Q : Type*} (tau : Q → ℝ)
    (alpha : ℕ → Q → P.M)
    (alphaLim : Q → P.M)
    (uP : UniformSpace P.M)
    (htop : uP.toTopologicalSpace = P.topology)
    (halpha : letI : UniformSpace P.M := uP
      TendstoUniformly alpha alphaLim Filter.atTop)
    (K : Set P.M)
    (hK : letI : TopologicalSpace P.M := P.topology; IsCompact K)
    (hseqK : letI : TopologicalSpace P.M := P.topology
      ∀ᶠ k in Filter.atTop, ∀ s, alpha k s ∈ K)
    (hlimK : ∀ s, alphaLim s ∈ K)
    (htau : ∀ s : Q, tau s ∈ Set.Icc beta psi)
    (htime : Set.Icc beta psi ⊆ X.D.carrier) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    TendstoUniformly
      (fun k s ↦
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
        (X.term ((subseq ∘ co.φ) k)).S.scalar (tau s)
          (Φ.map (co.φ k) (alpha k s)))
      (fun s ↦ metricScalarAt (I := I) (co.gInf (tau s)) (alphaLim s))
      Filter.atTop := by
  classical
  let : TopologicalSpace P.M := P.topology
  let : UniformSpace P.M := uP.replaceTopology htop.symm
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let scalarSeq : ℕ → ℝ × P.M → ℝ := fun k q ↦
    let : TopologicalSpace (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).topology
    let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).charted
    let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).smooth
    let : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).sigmaCompact
    let : T2Space (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).t2
    (X.term (subseq (co.φ k))).S.scalar q.1 (Φ.map (co.φ k) q.2)
  let scalarLim : ℝ × P.M → ℝ := fun q ↦
    metricScalarAt (I := I) (co.gInf q.1) q.2
  let S : Set (ℝ × P.M) := Set.Icc beta psi ×ˢ K
  have hscalar : TendstoUniformlyOn scalarSeq scalarLim atTop S :=
    co.tendstoUniformlyOn_scalar Φ R bf hsrc htgt beta psi cLow hcLow hbound hcovTail K hK
  have hlimCont : ContinuousOn scalarLim S :=
    co.continuousOn_scalar Φ R bf hsrc htgt beta psi cLow hcLow hbound hcovTail K hK htime
  have hQ : IsCompact S := isCompact_Icc.prod hK
  have huc : UniformContinuousOn scalarLim S :=
    hQ.uniformContinuousOn_of_continuous hlimCont
  have htauSelf : TendstoUniformly (fun _ : ℕ ↦ tau) tau Filter.atTop := by
    rw [tendstoUniformly_iff_tendsto]
    exact tendsto_diag_uniformity (tau ∘ Prod.snd) (Filter.atTop ×ˢ ⊤)
  have halpha' : TendstoUniformly alpha alphaLim atTop := halpha
  have hpairTwo := htauSelf.prodMk halpha'
  have hpair : TendstoUniformly
      (fun k s ↦ (tau s, alpha k s)) (fun s ↦ (tau s, alphaLim s))
      Filter.atTop := by
    rw [tendstoUniformly_iff_tendsto] at hpairTwo ⊢
    have hdiag : Tendsto (fun k : ℕ ↦ (k, k)) Filter.atTop
        (Filter.atTop ×ˢ Filter.atTop) := tendsto_id.prodMk tendsto_id
    have hpull : Tendsto
        (fun q : ℕ × Q ↦ ((q.1, q.1), q.2))
        (Filter.atTop ×ˢ ⊤) ((Filter.atTop ×ˢ Filter.atTop) ×ˢ ⊤) :=
      (hdiag.comp tendsto_fst).prodMk tendsto_snd
    exact hpairTwo.comp hpull
  have h := hscalar.comp_tendstoUniformly huc hpair
    (by
      filter_upwards [hseqK] with k hk
      exact fun q => ⟨htau q, hk q⟩)
    (fun q => ⟨htau q, hlimK q⟩)
  simpa only [scalarSeq, scalarLim, Function.comp_apply] using h

end CheegerGromovCompactness
end DifferentialGeometry
