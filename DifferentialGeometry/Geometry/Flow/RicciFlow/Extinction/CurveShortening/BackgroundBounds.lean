import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.IteratedCovariantDerivativeFields
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Regularity.Norm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Trace


noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

private theorem larger_regular_window {D : RealTimeInterval} {a b : ℝ}
    (hab : a < b) (hreg : Icc a b ⊆ D.regular) :
    ∃ alpha omega : ℝ, alpha < a ∧ b < omega ∧ Icc alpha omega ⊆ D.regular := by
  obtain ⟨l, u, ha, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (D.regular_isOpen.mem_nhds (hreg ⟨le_rfl, hab.le⟩))
  obtain ⟨v, w, hb, hvw⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (D.regular_isOpen.mem_nhds (hreg ⟨hab.le, le_rfl⟩))
  refine ⟨(l + a) / 2, (b + w) / 2, by linarith [ha.1], by linarith [hb.2], ?_⟩
  intro t ht
  by_cases hta : t < a
  · apply hlu
    constructor <;> linarith [ht.1, ha.1, ha.2]
  by_cases hbt : b < t
  · apply hvw
    constructor <;> linarith [ht.2, hb.1, hb.2]
  exact hreg ⟨le_of_not_gt hta, le_of_not_gt hbt⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    {D : RealTimeInterval} {a b : ℝ}

omit [SigmaCompactSpace M] in
private theorem actual_curvature_tower_bound [I.Boundaryless] [CompactSpace M]
    (F : SolutionOn (I := I) (M := M) D)
    (hF : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn F)
    (hab : a < b) (hreg : Icc a b ⊆ D.regular) (k : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t ∈ Icc a b, ∀ p : M,
      normSq0S (F.base.metric t) p (4 + k) (nablaKRm04Field F t k p) ≤ L := by
  obtain ⟨alpha, omega, halpha, homega, hlarge⟩ := larger_regular_window hab hreg
  have hao : alpha < omega := halpha.trans (hab.trans homega)
  let F' := F.timeRestrict (RealTimeInterval.closedOpen alpha omega hao)
  have hF' : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn F' :=
    isSolutionOn_timeRestrict hF
      (fun t ht => D.regular_subset (hlarge ⟨ht.1, ht.2.le⟩))
      (fun t ht => hlarge ⟨ht.1.le, ht.2.le⟩)
  have hcont : ContinuousOn (fun p : ℝ × M =>
      normSq0S (F.base.metric p.1) p.2 (4 + k) (nablaKRm04Field F p.1 k p.2))
      (Icc a b ×ˢ (univ : Set M)) := by
    have hh := (towerNorm_joint hF' k).continuousOn.mono
      (show Icc a b ×ˢ (univ : Set M) ⊆ Ioo alpha omega ×ˢ univ from
        fun p hp => ⟨⟨halpha.trans_le hp.1.1, hp.1.2.trans_lt homega⟩, hp.2⟩)
    simpa only [nablaKRm04NormSqIntrinsic, nablaKRm_eq_iterCov, F', SolutionOn.timeRestrict]
      using hh
  have hcompact := (isCompact_Icc : IsCompact (Icc a b)).prod
    (isCompact_univ : IsCompact (univ : Set M))
  obtain ⟨L, hL⟩ := hcompact.exists_bound_of_continuousOn hcont
  refine ⟨max L 0, le_max_right _ _, ?_⟩
  intro t ht p
  have hh := hL (t, p) ⟨ht, mem_univ p⟩
  rw [Real.norm_eq_abs] at hh
  exact (le_abs_self _).trans (hh.trans (le_max_left _ _))

omit [SigmaCompactSpace M] in
theorem rfs_csf_background [I.Boundaryless] [CompactSpace M]
    (F : SolutionOn (I := I) (M := M) D)
    (hF : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn F)
    (hab : a < b) (hreg : Icc a b ⊆ D.regular) :
    ∃ B : RicciBackground (I := I) (M := M) D a b,
      B.family = F.base ∧
      ∀ m : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a b, ∀ p : M,
        normSq0S (F.base.metric t) p (4 + m) (nablaKRm04Field F t m p) ≤ K ^ 2 := by
  obtain ⟨L0, hL0, h0⟩ := actual_curvature_tower_bound F hF hab hreg 0
  obtain ⟨L1, hL1, h1⟩ := actual_curvature_tower_bound F hF hab hreg 1
  let n : ℝ := Module.finrank ℝ E
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hn0 : 0 ≤ n ^ 4 * L0 := mul_nonneg (pow_nonneg hn _) hL0
  have hn1 : 0 ≤ n ^ 5 * L1 := mul_nonneg (pow_nonneg hn _) hL1
  have hr0 : ∀ t ∈ Icc a b, ∀ p : M,
      normSq0S (F.base.metric t) p 2 (F.base.ricciAt t p) ≤ n ^ 4 * L0 := by
    intro t ht p
    have hh := ricTower_normSq_le F t 0 p
    change normSq0S (F.base.metric t) p 2 (F.base.ricciAt t p) ≤
      n ^ 4 * normSq0S (F.base.metric t) p 4 (nablaKRm04Field F t 0 p) at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (h0 t ht p) (pow_nonneg hn _))
  have hr1 : ∀ t ∈ Icc a b, ∀ p : M,
      normSq0S (F.base.metric t) p 3
        (totalNabla0SFun 2 (F.base.connection t) (F.base.ricci t) p) ≤ n ^ 5 * L1 := by
    intro t ht p
    have hh := ricTower_normSq_le F t 1 p
    change normSq0S (F.base.metric t) p 3
      (totalNabla0SFun 2 (F.base.connection t) (F.base.ricci t) p) ≤
        n ^ 5 * normSq0S (F.base.metric t) p 5 (nablaKRm04Field F t 1 p) at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (h1 t ht p) (pow_nonneg hn _))
  refine ⟨{
    family := F.base
    smooth := hF.smoothMetric
    lt := hab
    regular := hreg
    equation := hF
    B₀ := n ^ 4 * L0 + 1
    B₁ := L0 + 1
    B₂ := n ^ 5 * L1 + 1
    B₀_nonneg := by positivity
    B₁_nonneg := by positivity
    B₂_nonneg := by positivity
    ricci_bound := ?_
    riemann_bound := ?_
    nablaRicci_bound := ?_ }, rfl, ?_⟩
  · intro t ht p
    exact (hr0 t ht p).trans (by nlinarith [sq_nonneg (n ^ 4 * L0)])
  · intro t ht p
    have hh := h0 t ht p
    change normSq0S (F.base.metric t) p 4 (F.base.rm04At t p) ≤ L0 at hh
    exact hh.trans (by nlinarith [sq_nonneg L0])
  · intro t ht p
    exact (hr1 t ht p).trans (by nlinarith [sq_nonneg (n ^ 5 * L1)])
  · intro m
    obtain ⟨L, hL, hh⟩ := actual_curvature_tower_bound F hF hab hreg m
    refine ⟨L + 1, by positivity, ?_⟩
    intro t ht p
    exact (hh t ht p).trans (by nlinarith [sq_nonneg L])

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem tensor_abs_eval_le_of_unit_slots (g : SmoothRiemannianMetric I M)
    (p : M) (r : ℕ) (T : Tensor0SSpace r I p) (K : ℝ) (hK : 0 ≤ K)
    (hbound : normSq0S g p r T ≤ K ^ 2)
    (v : Fin r → TangentSpace I p) (hv : ∀ i, g.inner p (v i) (v i) ≤ 1) :
    |T v| ≤ K := by
  have hsqrt : Real.sqrt (normSq0S g p r T) ≤ K := Real.sqrt_le_iff.mpr ⟨hK, hbound⟩
  have hprod : (∏ i : Fin r, Real.sqrt (g.inner p (v i) (v i))) ≤ 1 := by
    apply Finset.prod_le_one
    · intro i _
      exact Real.sqrt_nonneg _
    · intro i _
      exact Real.sqrt_le_iff.mpr ⟨by norm_num, by simpa using hv i⟩
  exact (abs_apply_le_norm0S g p r T v).trans
    ((mul_le_mul_of_nonneg_left hprod (Real.sqrt_nonneg _)).trans (by simpa using hsqrt))

omit [SigmaCompactSpace M] in
theorem RicciBackground.ricci_unit_bound
    (B : RicciBackground (I := I) (M := M) D a b)
    (t : ℝ) (ht : t ∈ Icc a b) (p : M) (v : Fin 2 → TangentSpace I p)
    (hv : ∀ i, (B.family.metric t).inner p (v i) (v i) ≤ 1) :
    |B.family.ricciAt t p v| ≤ B.B₀ :=
  tensor_abs_eval_le_of_unit_slots _ _ _ _ _ B.B₀_nonneg (B.ricci_bound t ht p) v hv

omit [SigmaCompactSpace M] in
theorem RicciBackground.riemann_unit_bound
    (B : RicciBackground (I := I) (M := M) D a b)
    (t : ℝ) (ht : t ∈ Icc a b) (p : M) (v : Fin 4 → TangentSpace I p)
    (hv : ∀ i, (B.family.metric t).inner p (v i) (v i) ≤ 1) :
    |B.family.rm04At t p v| ≤ B.B₁ :=
  tensor_abs_eval_le_of_unit_slots _ _ _ _ _ B.B₁_nonneg (B.riemann_bound t ht p) v hv

omit [SigmaCompactSpace M] in
theorem RicciBackground.nablaRicci_unit_bound
    (B : RicciBackground (I := I) (M := M) D a b)
    (t : ℝ) (ht : t ∈ Icc a b) (p : M) (v : Fin 3 → TangentSpace I p)
    (hv : ∀ i, (B.family.metric t).inner p (v i) (v i) ≤ 1) :
    |totalNabla0SFun 2 (B.family.connection t) (B.family.ricci t) p v| ≤ B.B₂ :=
  tensor_abs_eval_le_of_unit_slots _ _ _ _ _ B.B₂_nonneg (B.nablaRicci_bound t ht p) v hv

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
