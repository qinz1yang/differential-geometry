import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.RefJetWindow_S81

set_option autoImplicit false

/-!
# CH12-S81 / G2b: `refJets_window_S81` (general manifold form of `hReferenceJets`)
-/

noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology
namespace GC.LongTime.Ch12

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem refJets_window_S81 (h : SmoothRiemannianMetric I M) {K V : Set M} (hKc : IsCompact K)
    (hV : IsOpen V) (hKV : K ⊆ V) (N : ℕ) {Λ : ℝ} (hΛ : 1 ≤ Λ) {KShi : ℝ} (hKShi : 0 ≤ KShi)
    (Cinit : ℕ → ℝ) (hC : ∀ q, 0 ≤ Cinit q) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D), IsSolutionOn S →
      ∀ {t u : ℝ}, 0 < t → u ≤ 2 * t → Icc t u ⊆ D.regular →
      (∀ r ∈ Icc t u, ∀ x ∈ V, ∀ v : TangentSpace I x,
        Λ⁻¹ * (r * h.inner x v v) ≤ (S.base.metric r).inner x v v ∧
          (S.base.metric r).inner x v v ≤ Λ * (r * h.inner x v v)) →
      (∀ s ≤ N, ∀ r ∈ Icc t u, ∀ x ∈ V,
        normSq0S (S.base.metric r) x (2 + s)
          (ricCovTower (I := I) (S.base.metric r) (S.base.metric r) s x) * r ^ (2 + s) ≤ KShi ^ 2) →
      (∀ q, 1 ≤ q → q ≤ N → ∀ x ∈ V,
        Real.sqrt (normSq0S h x (q + 2) (metricCovDeriv (I := I) (S.base.metric t) h q x)) ≤
          Cinit q * t) →
      ∀ j ≤ N, ∀ r ∈ Icc t u, ∀ x ∈ K,
        Real.sqrt (normSq0S h x (j + 2) (defectJet_S57 S h j r x)) ≤ B * r := by
  classical
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by decide)
  obtain ⟨L, hLc, hKL, hLV⟩ := exists_compact_between hKc hV hKV
  have hBm : 1 ≤ 2 * Λ := by linarith
  have key := fun (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ N) =>
    covOrder_tower_const (gRef := h) hLc hV hLV N (2 * Λ) hBm KShi hKShi Cinit hC 1 r h1 h2
  choose! Cw hCw using key
  let d := Module.finrank ℝ E
  let cj : ℕ → ℝ := fun j => if j = 0 then 2 * Λ * Real.sqrt (d : ℝ) else Cw j
  let rj : ℕ → ℝ := fun j => if j = 0 then 2 * Λ * KShi else
    (ricTowerCoeffs d j (2 * Λ) Cw KShi).slope * Cw j + (ricTowerCoeffs d j (2 * Λ) Cw KShi).offset
  refine ⟨∑ j ∈ Finset.range (N + 1), (|cj j| + 2 * |rj j|), ?_, ?_⟩
  · exact Finset.sum_nonneg fun j _ => by positivity
  intro D S hS t u ht hu hreg hequiv hShi hinit j hj r hr x hx
  have htu : t ≤ u := hr.1.trans hr.2
  set ψ : ℝ := u / t with hψ
  have hψ1 : 1 ≤ ψ := by rw [hψ, le_div_iff₀ ht]; linarith
  have hψ2 : ψ ≤ 2 := by rw [hψ, div_le_iff₀ ht]; linarith
  have hmem : ∀ τ ∈ Icc (1 : ℝ) ψ, t * τ ∈ Icc t u := by
    intro τ hτ
    refine ⟨by nlinarith [hτ.1], ?_⟩
    have := mul_le_mul_of_nonneg_left hτ.2 ht.le
    rwa [hψ, mul_div_cancel₀ _ ht.ne'] at this
  have hτr : r / t ∈ Icc (1 : ℝ) ψ :=
    ⟨by rw [le_div_iff₀ ht]; linarith [hr.1], div_le_div_of_nonneg_right hr.2 ht.le⟩
  have htτ : t * (r / t) = r := by field_simp
  have hequivW : MetricUniformEquivalentOnWindow (I := I) V 1 ψ h (qSeq_S81 S t ht)
      (fun _ => 2 * Λ) :=
    fun i τ hτ => qSeq_equiv_S81 S h ht hΛ hequiv hτ.1 (hτ.2.trans hψ2) (hmem τ hτ)
  have hShiW : ∀ N' ≤ N, MovingShiBoundOn (I := I) V 1 ψ (qSeq_S81 S t ht) N' KShi :=
    fun N' hN' s hs i τ hτ x hx =>
      qSeq_shi_S81 S ht hKShi N hShi hτ.1 (hmem τ hτ) (hs.trans hN') hx
  have hW : ∀ r', 1 ≤ r' → r' ≤ N →
      MetricCovDerivOrderBoundOnWindow (I := I) L 1 ψ (qSeq_S81 S t ht) h r' (Cw r') := by
    intro r' h1 h2
    refine hCw r' h1 h2 (fun _ => 2 * Λ) hequivW (fun _ _ => le_rfl) (hShiW N le_rfl)
      ⟨le_rfl, hψ1⟩ ?_ ?_ ?_
    · intro q hq1 hqN i x _ s hs v
      exact qSeq_hasDerivAt_S81 S hS h ht q i (hreg (hmem s hs)) x v
    · intro q hq1 hqN i x hx
      have := hinit q hq1 hqN x hx
      simp only [qSeq_S81, mul_one, metricCovDerivNorm_scaleMetric_left]
      change t⁻¹ * Real.sqrt (normSq0S h x (q + 2)
        (metricCovDeriv (I := I) (S.base.metric t) h q x)) ≤ _
      calc _ ≤ t⁻¹ * (Cinit q * t) := mul_le_mul_of_nonneg_left this (inv_nonneg.2 ht.le)
        _ = Cinit q := by field_simp
    · intro τ hτ
      rw [abs_le]
      constructor <;> linarith [hτ.1, hτ.2]
  have hxI : x ∈ interior L := hKL hx
  have hxL : x ∈ L := interior_subset hxI
  have hxV : x ∈ V := hLV hxL
  have hterm : |cj j| + 2 * |rj j| ≤ ∑ j ∈ Finset.range (N + 1), (|cj j| + 2 * |rj j|) :=
    Finset.single_le_sum (f := fun j => |cj j| + 2 * |rj j|) (fun j _ => by positivity)
      (Finset.mem_range.2 (by omega))
  have hr0 : 0 < r := lt_of_lt_of_le ht hr.1
  have hQeq := qSeq_equiv_S81 S h ht hΛ hequiv hτr.1 (hτr.2.trans hψ2) (hmem _ hτr)
  have hnormQ : metricCovDerivNorm (I := I) j (qSeq_S81 S t ht 0 (r / t)) h x =
      t⁻¹ * metricCovDerivNorm (I := I) j (S.base.metric r) h x := by
    simp only [qSeq_S81, metricCovDerivNorm_scaleMetric_left, htτ]
  have hQnorm : metricCovDerivNorm (I := I) j (qSeq_S81 S t ht 0 (r / t)) h x ≤ cj j := by
    by_cases hj0 : j = 0
    · subst hj0
      simp only [cj, ite_true]
      exact covOrder_zero_le (I := I) (qSeq_S81 S t ht 0 (r / t)) h hQeq x hxV
    · simp only [cj, hj0, ite_false]
      exact hW j (by omega) hj 0 (r / t) hτr x hxL
  have hA : Real.sqrt (normSq0S h x (j + 2) (metricCovDeriv (I := I) (S.base.metric r) h j x)) ≤
      r * |cj j| := by
    have e : Real.sqrt (normSq0S h x (j + 2) (metricCovDeriv (I := I) (S.base.metric r) h j x)) =
        metricCovDerivNorm (I := I) j (S.base.metric r) h x := rfl
    rw [e]
    have e2 : metricCovDerivNorm (I := I) j (S.base.metric r) h x =
        t * metricCovDerivNorm (I := I) j (qSeq_S81 S t ht 0 (r / t)) h x := by
      rw [hnormQ]; field_simp
    rw [e2]
    calc t * metricCovDerivNorm (I := I) j (qSeq_S81 S t ht 0 (r / t)) h x ≤ t * |cj j| :=
          mul_le_mul_of_nonneg_left (hQnorm.trans (le_abs_self _)) ht.le
      _ ≤ r * |cj j| := mul_le_mul_of_nonneg_right hr.1 (abs_nonneg _)
  have hric : nablaRicReal (I := I) (fun _ s => S.base.metric s) h j 0 r x =
      nablaRicReal (I := I) (qSeq_S81 S t ht) h j 0 (r / t) x := by
    have e := nablaRicReal_qSeq_S81 S h ht j 0 (r / t) x
    rw [htτ] at e
    exact e.symm
  have hB : Real.sqrt (normSq0S h x (j + 2)
      (nablaRicReal (I := I) (fun _ s => S.base.metric s) h j 0 r x)) ≤ |rj j| := by
    rw [hric]
    by_cases hj0 : j = 0
    · subst hj0
      simp only [rj, ite_true]
      rw [nablaRicReal_normSq]
      have hshi := qSeq_shi_S81 S ht hKShi N hShi hτr.1 (hmem _ hτr) (s := 0) (Nat.zero_le _) hxV
      have hsym := (metricUniformEquivalentOn_symm (I := I) hQeq).2 x hxV
      have := sqrt_normSq0S_le_of_metric_equiv (I := I) (qSeq_S81 S t ht 0 (r / t)) h x 2
        (C := 2 * Λ) hBm hsym
        (ricCovTower (I := I) (qSeq_S81 S t ht 0 (r / t)) h 0 x)
      have e3 : Real.sqrt ((2 * Λ) ^ 2) = 2 * Λ := Real.sqrt_sq (by linarith)
      rw [e3] at this
      refine (le_trans this ?_).trans (le_abs_self _)
      exact mul_le_mul_of_nonneg_left hshi (by linarith)
    · simp only [rj, hj0, ite_false]
      have hbd := ric_bound_field_on (I := I) (U := interior L) (β := 1) (ψ := ψ)
        (gSeq := qSeq_S81 S t ht) (gRef := h) isOpen_interior j (by omega) (2 * Λ) hBm
        (fun i τ hτ => ⟨hBm, fun y hy => (hequivW i τ hτ).2 y (hLV (interior_subset hy))⟩)
        Cw (fun r' h1 h2 => metricCovOrderWindow_mono (interior_subset)
          (hW r' h1 (by omega))) KShi hKShi
        (fun s hs i τ hτ y hy => hShiW j hj s hs i τ hτ y (hLV (interior_subset hy)))
        0 (r / t) hτr x hxI
      have hco := ricCoeffs_nonneg d j (2 * Λ) Cw KShi hBm hKShi
      have hc2 := hW j (by omega) hj 0 (r / t) hτr x hxL
      refine (le_trans hbd ?_).trans (le_abs_self _)
      have := mul_le_mul_of_nonneg_left hc2 hco.1
      linarith
  have hdef : defectJet_S57 S h j r x =
      metricCovDeriv (I := I) (S.base.metric r) h j x +
        (2 * r) • nablaRicReal (I := I) (fun _ s => S.base.metric s) h j 0 r x := rfl
  rw [hdef]
  refine (sqrt_normSq0S_add_le h x (j + 2) _ _).trans ?_
  rw [sqrt_normSq0S_smul, abs_of_nonneg (by positivity)]
  have h2 : 2 * r * Real.sqrt (normSq0S h x (j + 2)
      (nablaRicReal (I := I) (fun _ s => S.base.metric s) h j 0 r x)) ≤ 2 * r * |rj j| :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  calc _ ≤ r * |cj j| + 2 * r * |rj j| := add_le_add hA h2
    _ = r * (|cj j| + 2 * |rj j|) := by ring
    _ ≤ r * ∑ j ∈ Finset.range (N + 1), (|cj j| + 2 * |rj j|) :=
        mul_le_mul_of_nonneg_left hterm hr0.le
    _ = _ := by ring

end GC.LongTime.Ch12
