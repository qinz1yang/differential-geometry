import DifferentialGeometry.Topology.Morse.NormalForm.Manifold
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Order.Compact

open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Morse

open Set CellAttachment

variable {n : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (MorseModel n) H} [I.Boundaryless]
  [IsManifold I ∞ M] {f : M → ℝ} {p : M}

private theorem minimum_morse_index_eq_zero (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hnd : IsNondegenerateCriticalPointAt I f p) (hmin : ∀ x, f p ≤ f x) :
    sigNeg (chartHessianAt
      (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) = 0 := by
  classical
  let Q := chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)
  let k := sigNeg Q
  have hk : k ≤ n := by
    have hdim : Module.finrank ℝ (MorseModel n) = n := by simp [MorseModel]
    exact hdim ▸ sigPos_le_finrank (-Q)
  obtain ⟨R, hR, Φ, _, _, _, _, hnormal, _⟩ := morse_lemma I f hf p k hk hnd rfl
  by_contra hzero
  have hkpos : 0 < k := Nat.pos_of_ne_zero hzero
  let u : EuclideanSpace ℝ (Fin k) := EuclideanSpace.single ⟨0, hkpos⟩ 1
  have hu : ‖u‖ = 1 := by simp [u, EuclideanSpace.single, PiLp.norm_single]
  have hsqrt : Real.sqrt (2 * (R ^ 2 / 2)) = R := by
    rw [show 2 * (R ^ 2 / 2) = R ^ 2 by ring, Real.sqrt_sq hR.le]
  have hbound : morseNorm n (cellMap R u) ≤ R := by
    have h := norm_cellMap_le hk (R ^ 2 / 2) R (hsqrt.le) u hu.le
    rw [hsqrt] at h
    exact h
  have heq := hnormal (cellMap R u) hbound
  rw [morseNormalForm_cellMap, hu] at heq
  have hle := hmin (Φ (cellMap R u))
  nlinarith [sq_pos_of_pos hR]

private theorem exists_minimum_morse_chart (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hnd : IsNondegenerateCriticalPointAt I f p) (hmin : ∀ x, f p ≤ f x) :
    ∃ R : ℝ, 0 < R ∧
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I
          (EuclideanSpace ℝ (Fin n)) M ∞,
        Φ.source = Metric.ball 0 R ∧ Φ 0 = p ∧
          ∀ y ∈ Φ.source, f (Φ y) = f p + ‖y‖ ^ 2 / 2 := by
  obtain ⟨R, hR, Φ, _, _, hΦ0, hsource, hnormal, _, _, R', hR', hΦ, hΦinv⟩ :=
    morse_lemma I f hf p 0 (Nat.zero_le n) hnd (minimum_morse_index_eq_zero hf hnd hmin)
  let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  let e := L.toHomeomorph.toOpenPartialHomeomorph.trans Φ
  let r := min R R'
  have hr : 0 < r := lt_min hR hR'
  have hLnorm (y : EuclideanSpace ℝ (Fin n)) : morseNorm n (L y) = ‖y‖ := rfl
  have hball (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ Metric.ball 0 r) :
      morseNorm n (L y) < r := by simpa only [hLnorm, Metric.mem_ball, dist_zero_right] using hy
  have hsub : Metric.ball 0 r ⊆ e.source := by
    intro y hy
    exact ⟨mem_univ _, hsource (L y) ((hball y hy).le.trans (min_le_left _ _))⟩
  let e' := e.restrOpen (Metric.ball 0 r) Metric.isOpen_ball
  have he'S : e'.source = Metric.ball 0 r := inter_eq_right.mpr hsub
  have hLball : MapsTo L (Metric.ball 0 r) (Metric.ball 0 R') := by
    intro y hy
    rw [Metric.mem_ball, dist_zero_right]
    exact (morseNorm_piNorm_le (L y)).trans_lt ((hball y hy).trans_le (min_le_right _ _))
  have hforward : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ e' e'.source := by
    rw [he'S]
    exact hΦ.comp L.contDiff.contMDiff.contMDiffOn hLball
  have hinvsub : e'.target ⊆ Φ '' Metric.ball 0 R' := by
    intro x hx
    have hy : e'.symm x ∈ Metric.ball 0 r := he'S ▸ e'.map_target hx
    exact ⟨L (e'.symm x), hLball hy, e'.right_inv hx⟩
  have hinverse : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e'.symm e'.target := by
    exact L.symm.contDiff.contMDiff.comp_contMDiffOn (hΦinv.mono hinvsub)
  refine ⟨r, hr, ⟨e'.toPartialEquiv, e'.open_source, e'.open_target, hforward, hinverse⟩,
    he'S, ?_, ?_⟩
  · change Φ (L 0) = p
    simpa only [map_zero] using hΦ0
  · intro y hy
    change f (Φ (L y)) = f p + ‖y‖ ^ 2 / 2
    have heq := hnormal (L y) ((hball y (he'S ▸ hy)).le.trans (min_le_left _ _))
    rw [morseNormalForm] at heq
    have hsum : (∑ j : Fin (n - 0), (L y (posIdx (Nat.zero_le n) j)) ^ 2) = ‖y‖ ^ 2 := by
      simpa [posIdx, L] using (EuclideanSpace.real_norm_sq_eq y).symm
    rw [hsum] at heq
    simpa [div_eq_mul_inv, mul_comm] using heq

private theorem exists_sublevel_subset_of_unique_minimum [CompactSpace M]
    (hf : Continuous f) (hmin : ∀ x, x ≠ p → f p < f x)
    {U : Set M} (hU : IsOpen U) (hp : p ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ sublevel f (f p + ε) ⊆ U := by
  classical
  by_cases hne : Uᶜ.Nonempty
  · obtain ⟨q, hq, hqmin⟩ := hU.isClosed_compl.isCompact.exists_isMinOn hne hf.continuousOn
    have hqp : q ≠ p := fun heq => hq (heq ▸ hp)
    refine ⟨(f q - f p) / 2, by linarith [hmin q hqp], ?_⟩
    intro x hx
    by_contra hxU
    have hle : f q ≤ f x := hqmin hxU
    change f x ≤ f p + (f q - f p) / 2 at hx
    linarith [hmin q hqp]
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x _
    by_contra hx
    exact hne ⟨x, hx⟩

theorem exists_sublevel_closedBall_chart_of_unique_minimum [CompactSpace M]
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hnd : IsNondegenerateCriticalPointAt I f p)
    (hmin : ∀ x, x ≠ p → f p < f x) :
    ∃ R : ℝ, 0 < R ∧
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I
          (EuclideanSpace ℝ (Fin n)) M ∞,
        Metric.ball 0 R ⊆ Φ.source ∧ Φ 0 = p ∧
          (∀ y ∈ Φ.source, f (Φ y) = f p + ‖y‖ ^ 2 / 2) ∧
          ∀ r : ℝ, 0 ≤ r → r < R →
            Φ '' Metric.closedBall 0 r = sublevel f (f p + r ^ 2 / 2) := by
  classical
  have hle (x : M) : f p ≤ f x := by
    by_cases hx : x = p
    · exact hx ▸ le_rfl
    · exact (hmin x hx).le
  obtain ⟨R, hR, Φ, hsource, hΦ0, hnormal⟩ := exists_minimum_morse_chart hf hnd hle
  have hp : p ∈ Φ.target := hΦ0 ▸ Φ.map_source' (hsource ▸ Metric.mem_ball_self hR)
  obtain ⟨ε, hε, hlow⟩ := exists_sublevel_subset_of_unique_minimum
    hf.continuous hmin Φ.open_target hp
  refine ⟨min R (Real.sqrt (2 * ε)), lt_min hR (Real.sqrt_pos.2 (by positivity)),
    Φ, ?_, hΦ0, hnormal, ?_⟩
  · rw [hsource]
    exact Metric.ball_subset_ball (min_le_left _ _)
  · intro r hr hrR
    have hrR' : r < R := hrR.trans_le (min_le_left _ _)
    have hsq : r ^ 2 / 2 ≤ ε := by
      have hlt : r < Real.sqrt (2 * ε) := hrR.trans_le (min_le_right _ _)
      have hltSq := (sq_lt_sq₀ hr (Real.sqrt_nonneg (2 * ε))).2 hlt
      rw [Real.sq_sqrt (by positivity)] at hltSq
      linarith
    have hball : Metric.closedBall 0 r ⊆ Φ.source := by
      rw [hsource]
      exact Metric.closedBall_subset_ball hrR'
    apply Subset.antisymm
    · rintro x ⟨y, hy, rfl⟩
      change f (Φ y) ≤ f p + r ^ 2 / 2
      rw [hnormal y (hball hy)]
      have hyn : ‖y‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hy
      have hsq' := (sq_le_sq₀ (norm_nonneg y) hr).2 hyn
      linarith
    · intro x hx
      have hxt : x ∈ Φ.target := hlow (by
        change f x ≤ f p + ε
        exact hx.trans (by linarith))
      refine ⟨Φ.invFun x, ?_, Φ.right_inv' hxt⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      have heq := hnormal (Φ.invFun x) (Φ.map_target' hxt)
      rw [Φ.right_inv' hxt] at heq
      apply (sq_le_sq₀ (norm_nonneg _) hr).1
      change f x ≤ f p + r ^ 2 / 2 at hx
      linarith

end DifferentialGeometry.Topology.Morse
