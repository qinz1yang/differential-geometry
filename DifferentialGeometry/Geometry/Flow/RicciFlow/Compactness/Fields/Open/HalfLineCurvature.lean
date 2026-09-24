import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.MetricExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.MetricLowerBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Regularity
import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.RiemannTensor

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M] [IsManifold I 1 M]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem tensor0SFamilyContinuousOnSet_of_chartRicciContOn
    {K : Set ℝ} (g : ℝ → SmoothRiemannianMetric I M)
    (hric : ∀ x₀ : M, ∃ Kc : Set M, IsCompact Kc ∧ Kc ∈ 𝓝 x₀ ∧
      Kc ⊆ chartLeviCivitaGoodSet (I := I) x₀ ∧
      ∀ i j : Fin (Module.finrank ℝ E),
        ContinuousOn
          (fun q : ℝ × M => chartRicciTensor (I := I) (g q.1) x₀ i j (extChartAt I x₀ q.2))
          (K ×ˢ Kc)) :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K
      (fun t x => metricRicciAt (I := I) (g t) x) := by
  choose Kc hKcc hKcn hKcgood hKch using hric
  apply tensor0SFamilyContinuousOnSet_of_chartBasisComp (N := Kc) (hN := hKcn)
  intro x₀ idx
  have hmap : ContinuousOn (fun q : {t : ℝ // t ∈ K} × M => ((q.1 : ℝ), q.2))
      {q : {t : ℝ // t ∈ K} × M | q.2 ∈ Kc x₀} :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousOn
  have hmaps : Set.MapsTo (fun q : {t : ℝ // t ∈ K} × M => ((q.1 : ℝ), q.2))
      {q : {t : ℝ // t ∈ K} × M | q.2 ∈ Kc x₀}
      (K ×ˢ Kc x₀) :=
    fun q hq => ⟨q.1.2, hq⟩
  refine (((hKch x₀ (idx 0) (idx 1)).comp hmap hmaps)).congr ?_
  intro q hq
  have hq' : q.2 ∈ chartLeviCivitaGoodSet (I := I) x₀ := hKcgood x₀ hq
  have hvec : (fun k : Fin 2 => chartBasisVecFiber (I := I) x₀ (idx k) q.2) =
      vec2 (chartBasisVecFiber (I := I) x₀ (idx 0) q.2)
        (chartBasisVecFiber (I := I) x₀ (idx 1) q.2) := by
    funext k
    fin_cases k <;> rfl
  change metricRicciAt (I := I) (g (q.1 : ℝ)) q.2
      (fun k : Fin 2 => chartBasisVecFiber (I := I) x₀ (idx k) q.2)
    = chartRicciTensor (I := I) (g (q.1 : ℝ)) x₀ (idx 0) (idx 1)
        (extChartAt I x₀ q.2)
  rw [hvec, metricRicciAt_apply_eq_ricciTensor]
  exact ricciTensor_chartBasisVec_alpha_eq (I := I) (g (q.1 : ℝ)) x₀ (idx 0) (idx 1) hq'

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem tensor0SFamilyContinuousOnSet_of_chartRiemannContOn
    {K : Set ℝ} (g : ℝ → SmoothRiemannianMetric I M)
    (hrm : ∀ x₀ : M, ∃ Kc : Set M, IsCompact Kc ∧ Kc ∈ 𝓝 x₀ ∧
      Kc ⊆ chartLeviCivitaGoodSet (I := I) x₀ ∧
      (∀ i j k' l : Fin (Module.finrank ℝ E),
        ContinuousOn
          (fun q : ℝ × M =>
            chartRiemannTensor (I := I) (g q.1) x₀ i j k' l (extChartAt I x₀ q.2))
          (K ×ˢ Kc)) ∧
      (∀ i j : Fin (Module.finrank ℝ E),
        ContinuousOn
          (fun q : ℝ × M => chartGramMatrix (I := I) (g q.1) x₀ q.2 i j)
          (K ×ˢ Kc))) :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) 4 K
      (fun t x => metricRm04At (I := I) (g t) x) := by
  choose Kc hKcc hKcn hKcgood hKch hKcg using hrm
  apply tensor0SFamilyContinuousOnSet_of_chartBasisComp (N := Kc) (hN := hKcn)
  intro x₀ idx
  have hsum : ContinuousOn
      (fun q : ℝ × M =>
        ∑ l : Fin (Module.finrank ℝ E),
          chartRiemannTensor (I := I) (g q.1) x₀ (idx 2) (idx 0) (idx 1) l
              (extChartAt I x₀ q.2) *
            chartGramMatrix (I := I) (g q.1) x₀ q.2 (idx 3) l)
      (K ×ˢ Kc x₀) := by
    refine continuousOn_finsetSum _ (fun l _ => ?_)
    exact (hKch x₀ (idx 2) (idx 0) (idx 1) l).mul (hKcg x₀ (idx 3) l)
  have hmap : ContinuousOn (fun q : {t : ℝ // t ∈ K} × M => ((q.1 : ℝ), q.2))
      {q : {t : ℝ // t ∈ K} × M | q.2 ∈ Kc x₀} :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousOn
  have hmaps : Set.MapsTo (fun q : {t : ℝ // t ∈ K} × M => ((q.1 : ℝ), q.2))
      {q : {t : ℝ // t ∈ K} × M | q.2 ∈ Kc x₀}
      (K ×ˢ Kc x₀) :=
    fun q hq => ⟨q.1.2, hq⟩
  refine ((hsum.comp hmap hmaps)).congr ?_
  intro q hq
  have hq' : q.2 ∈ chartLeviCivitaGoodSet (I := I) x₀ := hKcgood x₀ hq
  simp only [Function.comp_apply]
  exact rm04_coord_eq (I := I) (g (q.1 : ℝ)) x₀ idx hq'

end DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry
namespace CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedFlowSeq (I := I)}
variable {P : PointedRiemannianManifold (I := I)}
variable {subseq : Nat → Nat}
variable (Φ : PointedCGHMaps (I := I) X P subseq)

omit [NeZero (Module.finrank ℝ E)] in
theorem FlowMetricConvergenceData.ricciCont_window
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    {β ψ : Real}
    (cLow : Real) (hcLow : 0 < cLow)
    (hbound : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
      ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ →
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
      ∀ q : Nat, q ≤ 2 → ∃ C : Real, ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ →
        ∀ z : P.M, z ∈ bf.grow k →
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z ≤ C)
    (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt β ψ)
    (hkcont : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : T2Space P.M := P.t2
        letI : IsManifold I ∞ P.M := P.smooth
        letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ (k : Nat) (x₀ : P.M) (i j : Fin (Module.finrank Real E)),
        ContinuousOn
          (fun q : Real × P.M =>
            chartRicciTensor (I := I) (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) q.1)
              x₀ i j (extChartAt I x₀ q.2))
          (Set.Icc β ψ ×ˢ
            (chartLeviCivitaGoodSet (I := I) x₀ ∩ bf.grow (co.φ k)))) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    tensor0SFamilyContinuousOnSet (I := I) (M := P.M) 2 (Set.Icc β ψ)
      (fun t x => metricRicciAt (I := I) (co.gInf t) x) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : IsManifold I 1 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : LocallyCompactSpace H := I.locallyCompactSpace
  let : LocallyCompactSpace P.M := ChartedSpace.locallyCompactSpace H P.M
  let lam : Real := min cLow 1
  have hlam : 0 < lam := by
    change 0 < min cLow 1
    exact lt_min hcLow one_pos
  have hlowSeqAll : ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ →
      ∀ (x : P.M) (v : TangentSpace I x),
        lam * R.inner x v v ≤ (gSeqExt (I := I) Φ R bf hsrc htgt k t).inner x v v := by
    intro k t ht x v
    exact gSeqExt_lower (I := I) Φ R bf hsrc htgt cLow β ψ hcLow hbound k t ht x v
  have hlowInfAll : ∀ (t : Real), t ∈ Set.Icc β ψ →
      ∀ (x : P.M) (v : TangentSpace I x),
        lam * R.inner x v v ≤ (co.gInf t).inner x v v :=
    FlowMetricConvergenceData.lower_of (I := I) (Φ := Φ) co
      (fun k t ht x v => hlowSeqAll (co.φ k) t ht x v)
  choose C hC using hcovTail
  let Cmax : Real := max (C 0 (by omega)) (max (C 1 (by omega)) (C 2 le_rfl))
  let B0 : Real := max 0 (Cmax + 1)
  have hCmax : ∀ (a : Nat) (ha : a ≤ 2), C a ha ≤ Cmax := by
    intro a ha
    interval_cases a
    · exact le_max_left _ _
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
    · exact le_trans (le_max_right _ _) (le_max_right _ _)
  apply tensor0SFamilyContinuousOnSet_of_chartRicciContOn
    (g := fun t => co.gInf t)
  intro x₀
  obtain ⟨Kc, hKcc, hxKc, hKcgood⟩ :=
    exists_compact_subset (x := x₀) (chartLeviCivitaGoodSet_isOpen (I := I) x₀)
      (self_mem_chartLeviCivitaGoodSet (I := I) (α := x₀))
  obtain ⟨kgrow, hkgrow⟩ := bf.grow_cover Kc hKcc
  refine ⟨Kc, hKcc,
    Filter.mem_of_superset (isOpen_interior.mem_nhds hxKc) interior_subset,
    hKcgood, ?_⟩
  intro i j
  have hKchart : Kc ⊆ (chartAt H x₀).source := by
    intro y hy
    rw [← extChartAt_source_eq_chartAt_source (I := I)]
    exact (hKcgood hy).1.1
  have hbddSeq : ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ → ∀ y ∈ Kc, ∀ a : Nat, a ≤ 2 →
      metricCovDerivNorm (I := I) a
        (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ (k + kgrow)) t) R y ≤ B0 := by
    intro k t ht y hy a ha
    have hgrow : Kc ⊆ bf.grow (co.φ (k + kgrow)) :=
      hkgrow _ (le_trans (Nat.le_add_left kgrow k) (co.strictMono.id_le (k + kgrow)))
    exact (hC a ha (co.φ (k + kgrow)) t ht y (hgrow hy)).trans
      ((hCmax a ha).trans
        ((le_add_of_nonneg_right zero_le_one).trans (le_max_right _ _)))
  have hconv : ∀ ε : Real, 0 < ε → ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k →
      ∀ t ∈ Set.Icc β ψ,
        metricDerivNormSupOn (I := I) Kc 2
          (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ (k + kgrow)) t) (co.gInf t) R < ε := by
    intro ε hε
    obtain ⟨k0, hk0⟩ := co.convergence Kc hKcc 2 ε hε
    refine ⟨k0, fun k hk t ht => hk0 (k + kgrow) ?_ t ht⟩
    exact le_trans hk (Nat.le_add_right k kgrow)
  obtain ⟨kconv, hkconv⟩ := hconv 1 one_pos
  have hbddInf : ∀ (t : Real), t ∈ Set.Icc β ψ → ∀ y ∈ Kc, ∀ a : Nat, a ≤ 2 →
      metricCovDerivNorm (I := I) a (co.gInf t) R y ≤ B0 := by
    intro t ht y hy a ha
    have hdiff : metricDerivNorm (I := I) a (co.gInf t)
        (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ (kconv + kgrow)) t) R y < 1 := by
      rw [metricDerivNorm_symm (I := I) a (co.gInf t)
        (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ (kconv + kgrow)) t) R y]
      exact (derivNorm_le_sup (I := I) hKcc ha
        (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ (kconv + kgrow)) t) (co.gInf t) R hy).trans_lt
          (hkconv kconv le_rfl t ht)
    have htri := covNorm_le_add (I := I) a (co.gInf t)
      (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ (kconv + kgrow)) t) R y
    calc
      metricCovDerivNorm (I := I) a (co.gInf t) R y
          ≤ metricCovDerivNorm (I := I) a
              (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ (kconv + kgrow)) t) R y +
            metricDerivNorm (I := I) a (co.gInf t)
              (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ (kconv + kgrow)) t) R y := htri
      _ ≤ Cmax + 1 := add_le_add
        ((hC a ha _ t ht y (hkgrow _
          (le_trans (Nat.le_add_left kgrow kconv) (co.strictMono.id_le (kconv + kgrow))) hy)).trans
          (hCmax a ha)) hdiff.le
      _ ≤ B0 := le_max_right _ _
  have hlowSeq : ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ → ∀ y ∈ Kc, ∀ ξ : TangentSpace I y,
      lam * R.inner y ξ ξ ≤
        (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ (k + kgrow)) t).inner y ξ ξ :=
    fun k t ht y _ ξ => hlowSeqAll (co.φ (k + kgrow)) t ht y ξ
  have hlowInf : ∀ (t : Real), t ∈ Set.Icc β ψ → ∀ y ∈ Kc, ∀ ξ : TangentSpace I y,
      lam * R.inner y ξ ξ ≤ (co.gInf t).inner y ξ ξ :=
    fun t ht y _ ξ => hlowInfAll t ht y ξ
  have hkcontK : ∀ k : Nat, ContinuousOn
      (fun q : Real × P.M =>
        chartRicciTensor (I := I)
          (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ (k + kgrow)) q.1) x₀ i j
          (extChartAt I x₀ q.2))
      (Set.Icc β ψ ×ˢ Kc) := by
    intro k
    refine (hkcont (k + kgrow) x₀ i j).mono (Set.prod_mono Set.Subset.rfl ?_)
    intro y hy
    exact ⟨hKcgood hy,
      hkgrow _ (le_trans (Nat.le_add_left kgrow k) (co.strictMono.id_le (k + kgrow))) hy⟩
  exact chartRicciLim_contOn (I := I) R x₀ hKcc hKchart
    (fun k t => gSeqExt (I := I) Φ R bf hsrc htgt (co.φ (k + kgrow)) t) (co.gInf)
    β ψ lam B0 hlam hlowSeq hlowInf hbddSeq hbddInf hconv i j hkcontK


omit [NeZero (Module.finrank ℝ E)] in
theorem FlowMetricConvergenceData.rm04Cont_window
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    {β ψ : Real} (hwin : Set.Icc β ψ ⊆ X.D.carrier)
    (cLow : Real) (hcLow : 0 < cLow)
    (hbound : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
      ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ →
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
      ∀ q : Nat, q ≤ 2 → ∃ C : Real, ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ →
        ∀ z : P.M, z ∈ bf.grow k →
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z ≤ C)
    (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt β ψ)
    (hkcont : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : T2Space P.M := P.t2
        letI : IsManifold I ∞ P.M := P.smooth
        letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ (k : Nat) (x₀ : P.M) (i j k' l : Fin (Module.finrank Real E)),
        ContinuousOn
          (fun q : Real × P.M =>
            chartRiemannTensor (I := I) (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) q.1)
              x₀ i j k' l (extChartAt I x₀ q.2))
          (Set.Icc β ψ ×ˢ
            (chartLeviCivitaGoodSet (I := I) x₀ ∩ bf.grow (co.φ k)))) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    tensor0SFamilyContinuousOnSet (I := I) (M := P.M) 4 (Set.Icc β ψ)
      (fun t x => metricRm04At (I := I) (co.gInf t) x) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : IsManifold I 1 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : LocallyCompactSpace H := I.locallyCompactSpace
  let : LocallyCompactSpace P.M := ChartedSpace.locallyCompactSpace H P.M
  let lam : Real := min cLow 1
  have hlam : 0 < lam := by
    change 0 < min cLow 1
    exact lt_min hcLow one_pos
  have hlowSeqAll : ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ →
      ∀ (x : P.M) (v : TangentSpace I x),
        lam * R.inner x v v ≤ (gSeqExt (I := I) Φ R bf hsrc htgt k t).inner x v v := by
    intro k t ht x v
    exact gSeqExt_lower (I := I) Φ R bf hsrc htgt cLow β ψ hcLow hbound k t ht x v
  have hlowInfAll : ∀ (t : Real), t ∈ Set.Icc β ψ →
      ∀ (x : P.M) (v : TangentSpace I x),
        lam * R.inner x v v ≤ (co.gInf t).inner x v v :=
    FlowMetricConvergenceData.lower_of (I := I) (Φ := Φ) co
      (fun k t ht x v => hlowSeqAll (co.φ k) t ht x v)
  choose C hC using hcovTail
  let Cmax : Real := max (C 0 (by omega)) (max (C 1 (by omega)) (C 2 le_rfl))
  let B0 : Real := max 0 (Cmax + 1)
  have hCmax : ∀ (a : Nat) (ha : a ≤ 2), C a ha ≤ Cmax := by
    intro a ha
    interval_cases a
    · exact le_max_left _ _
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
    · exact le_trans (le_max_right _ _) (le_max_right _ _)
  apply tensor0SFamilyContinuousOnSet_of_chartRiemannContOn
    (g := fun t => co.gInf t)
  intro x₀
  obtain ⟨Kc, hKcc, hxKc, hKcgood⟩ :=
    exists_compact_subset (x := x₀) (chartLeviCivitaGoodSet_isOpen (I := I) x₀)
      (self_mem_chartLeviCivitaGoodSet (I := I) (α := x₀))
  obtain ⟨kgrow, hkgrow⟩ := bf.grow_cover Kc hKcc
  have hKcbase : Kc ⊆ (trivializationAt E (TangentSpace I) x₀).baseSet :=
    fun y hy => chartLeviCivitaGoodSet_mem_baseSet (I := I) (hKcgood hy)
  refine ⟨Kc, hKcc,
    Filter.mem_of_superset (isOpen_interior.mem_nhds hxKc) interior_subset,
    hKcgood, ?_, ?_⟩
  · intro i j k' l
    have hKchart : Kc ⊆ (chartAt H x₀).source := by
      intro y hy
      rw [← extChartAt_source_eq_chartAt_source (I := I)]
      exact (hKcgood hy).1.1
    have hbddSeq : ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ → ∀ y ∈ Kc, ∀ a : Nat, a ≤ 2 →
        metricCovDerivNorm (I := I) a
          (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ (k + kgrow)) t) R y ≤ B0 := by
      intro k t ht y hy a ha
      have hgrow : Kc ⊆ bf.grow (co.φ (k + kgrow)) :=
        hkgrow _ (le_trans (Nat.le_add_left kgrow k) (co.strictMono.id_le (k + kgrow)))
      exact (hC a ha (co.φ (k + kgrow)) t ht y (hgrow hy)).trans
        ((hCmax a ha).trans
          ((le_add_of_nonneg_right zero_le_one).trans (le_max_right _ _)))
    have hconv : ∀ ε : Real, 0 < ε → ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k →
        ∀ t ∈ Set.Icc β ψ,
          metricDerivNormSupOn (I := I) Kc 2
            (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ (k + kgrow)) t) (co.gInf t) R < ε := by
      intro ε hε
      obtain ⟨k0, hk0⟩ := co.convergence Kc hKcc 2 ε hε
      refine ⟨k0, fun k hk t ht => hk0 (k + kgrow) ?_ t ht⟩
      exact le_trans hk (Nat.le_add_right k kgrow)
    obtain ⟨kconv, hkconv⟩ := hconv 1 one_pos
    have hbddInf : ∀ (t : Real), t ∈ Set.Icc β ψ → ∀ y ∈ Kc, ∀ a : Nat, a ≤ 2 →
        metricCovDerivNorm (I := I) a (co.gInf t) R y ≤ B0 := by
      intro t ht y hy a ha
      have hdiff : metricDerivNorm (I := I) a (co.gInf t)
          (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ (kconv + kgrow)) t) R y < 1 := by
        rw [metricDerivNorm_symm (I := I) a (co.gInf t)
          (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ (kconv + kgrow)) t) R y]
        exact (derivNorm_le_sup (I := I) hKcc ha
          (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ (kconv + kgrow)) t) (co.gInf t) R hy).trans_lt
            (hkconv kconv le_rfl t ht)
      have htri := covNorm_le_add (I := I) a (co.gInf t)
        (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ (kconv + kgrow)) t) R y
      calc
        metricCovDerivNorm (I := I) a (co.gInf t) R y
            ≤ metricCovDerivNorm (I := I) a
                (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ (kconv + kgrow)) t) R y +
              metricDerivNorm (I := I) a (co.gInf t)
                (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ (kconv + kgrow)) t) R y := htri
        _ ≤ Cmax + 1 := add_le_add
          ((hC a ha _ t ht y (hkgrow _
            (le_trans (Nat.le_add_left kgrow kconv)
              (co.strictMono.id_le (kconv + kgrow))) hy)).trans
            (hCmax a ha)) hdiff.le
        _ ≤ B0 := le_max_right _ _
    have hlowSeq : ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ → ∀ y ∈ Kc, ∀ ξ : TangentSpace I y,
        lam * R.inner y ξ ξ ≤
          (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ (k + kgrow)) t).inner y ξ ξ :=
      fun k t ht y _ ξ => hlowSeqAll (co.φ (k + kgrow)) t ht y ξ
    have hlowInf : ∀ (t : Real), t ∈ Set.Icc β ψ → ∀ y ∈ Kc, ∀ ξ : TangentSpace I y,
        lam * R.inner y ξ ξ ≤ (co.gInf t).inner y ξ ξ :=
      fun t ht y _ ξ => hlowInfAll t ht y ξ
    have hkcontK : ∀ k : Nat, ContinuousOn
        (fun q : Real × P.M =>
          chartRiemannTensor (I := I)
            (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ (k + kgrow)) q.1) x₀ i j k' l
            (extChartAt I x₀ q.2))
        (Set.Icc β ψ ×ˢ Kc) := by
      intro k
      refine (hkcont (k + kgrow) x₀ i j k' l).mono (Set.prod_mono Set.Subset.rfl ?_)
      intro y hy
      exact ⟨hKcgood hy,
        hkgrow _ (le_trans (Nat.le_add_left kgrow k) (co.strictMono.id_le (k + kgrow))) hy⟩
    exact chartRiemannLim_contOn (I := I) R x₀ hKcc hKchart
      (fun k t => gSeqExt (I := I) Φ R bf hsrc htgt (co.φ (k + kgrow)) t) (co.gInf)
      β ψ lam B0 hlam hlowSeq hlowInf hbddSeq hbddInf hconv i j k' l hkcontK
  · intro i j
    refine (chartGramLim_contOn (I := I)
      (fun k t => gSeqExt (I := I) Φ R bf hsrc htgt (co.φ (k + kgrow)) t) (co.gInf) R β ψ
      (fun K hK ε hε => ?_) x₀ i j (fun k => ?_)).mono
      (Set.prod_mono Set.Subset.rfl hKcbase)
    · obtain ⟨k0, hk0⟩ := co.convergencePt K hK 0 ε hε
      exact ⟨k0, fun k hk t ht x hx => hk0 (k + kgrow) (le_trans hk (Nat.le_add_right k kgrow))
        t ht 0 le_rfl x hx⟩
    · exact (gSeqExt_gram_cont (I := I) Φ R bf hsrc htgt (co.φ (k + kgrow)) x₀ i j).mono
        (Set.prod_mono hwin Set.Subset.rfl)

end CheegerGromovCompactness
end DifferentialGeometry
