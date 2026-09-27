import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.TimeComposition

noncomputable section
open scoped Manifold ContDiff NNReal ENNReal
namespace DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {ι : Type*} [Fintype ι]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold 𝓘(ℝ, ℝ) ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
  [BoundarylessManifold 𝓘(ℝ, ℝ) M]
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

theorem exists_vectorH1_time_composition_on_symmetric_time_interval
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M) (n : ℕ)
    (F : (Option ι → ℝ) → (Fin n → ℝ)) {U : Set (Option ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (t0 : ℝ) (u0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1))
    (hu0 : Set.range (scalarH1PiToContinuous g (scalarH1TimeCoordinate g (t0, u0))) ⊆ U) :
    ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ≥0,
      ∃ N : ℝ → Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) R →
        PiLp 2 (fun _ : Fin n => TensorHs g 0 0 1),
      LipschitzWith C (fun p : ℝ × Metric.closedBall
        (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) R => N p.1 p.2) ∧
      (∀ t ∈ Set.Icc (-R) R,
        ∀ u ∈ Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) R,
        Set.range (scalarH1PiToContinuous g (scalarH1TimeCoordinate g (t0 + t, u0 + u))) ⊆ U) ∧
      ∀ t ∈ Set.Icc (-R) R, ∀ u x j,
        scalarH1ToContinuous g (N t u j) x = F (fun i => match i with
          | none => t0 + t
          | some i => scalarH1ToContinuous g (u0 i + u.1 i) x) j := by
  classical
  let Fj : Option (Fin n) → (Option ι → ℝ) → ℝ := fun j => match j with
    | none => fun _ => 0
    | some k => fun z => F z k
  have hFj (j : Option (Fin n)) : ContDiffOn ℝ ∞ (Fj j) U := by
    cases j with
    | none => exact contDiffOn_const
    | some k => exact contDiffOn_pi.mp hF k
  have hs (j : Option (Fin n)) := exists_scalarH1_time_composition_on_symmetric_time_interval
    g (Fj j) (hFj j) hU t0 u0 hu0
  choose r hr C Nj hNj hRange hEval using hs
  let R := (Finset.univ : Finset (Option (Fin n))).inf' Finset.univ_nonempty r
  have hR : 0 < R := (Finset.lt_inf'_iff Finset.univ_nonempty).2 (fun j _ => hr j)
  have hRle (j : Option (Fin n)) : R ≤ r j := Finset.inf'_le r (Finset.mem_univ j)
  let S := Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) R
  let incl (j : Option (Fin n)) :
      S → Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) (r j) :=
    fun u => ⟨u.1, (Metric.closedBall_subset_closedBall (hRle j)) u.2⟩
  let K : ℝ≥0 := Finset.univ.sup C
  have hCle (j : Option (Fin n)) : C j ≤ K := Finset.le_sup (Finset.mem_univ j)
  let f : ℝ × S → Fin n → TensorHs g 0 0 1 := fun p j => Nj (some j) p.1 (incl (some j) p.2)
  have hf : LipschitzWith K f := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    rw [dist_eq_norm]
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg K.coe_nonneg dist_nonneg)).2
    intro j
    have h := (hNj (some j)).dist_le_mul (p.1, incl (some j) p.2) (q.1, incl (some j) q.2)
    change dist (f p j) (f q j) ≤ (C (some j) : ℝ) * dist p q at h
    simpa only [Pi.sub_apply, dist_eq_norm] using
      h.trans (mul_le_mul_of_nonneg_right
        (NNReal.coe_le_coe.mpr (hCle (some j))) dist_nonneg)
  let N : ℝ → S → PiLp 2 (fun _ : Fin n => TensorHs g 0 0 1) :=
    fun t u => WithLp.toLp 2 (f (t, u))
  have hN := (PiLp.lipschitzWith_toLp 2 (fun _ : Fin n => TensorHs g 0 0 1)).comp hf
  refine ⟨R, hR, _, N, hN, ?_, ?_⟩
  · intro t ht u hu
    exact hRange none t ⟨(neg_le_neg (hRle none)).trans ht.1, ht.2.trans (hRle none)⟩ u
      ((Metric.closedBall_subset_closedBall (hRle none)) hu)
  · intro t ht u x j
    exact hEval (some j) t
      ⟨(neg_le_neg (hRle (some j))).trans ht.1, ht.2.trans (hRle (some j))⟩
      (incl (some j) u) x


theorem exists_vectorH1_time_composition_on_closedBall
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M) (n : ℕ)
    (F : (Option ι → ℝ) → (Fin n → ℝ)) {U : Set (Option ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (t0 : ℝ) (u0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1))
    (hu0 : Set.range (scalarH1PiToContinuous g (scalarH1TimeCoordinate g (t0, u0))) ⊆ U) :
    ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ≥0,
      ∃ N : ℝ → Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) R →
        PiLp 2 (fun _ : Fin n => TensorHs g 0 0 1),
      LipschitzWith C (fun p : ℝ × Metric.closedBall
        (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) R => N p.1 p.2) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) R,
        ∀ u ∈ Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) R,
        Set.range (scalarH1PiToContinuous g (scalarH1TimeCoordinate g (t0 + t, u0 + u))) ⊆ U) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) R, ∀ u x j,
        scalarH1ToContinuous g (N t u j) x = F (fun i => match i with
          | none => t0 + t
          | some i => scalarH1ToContinuous g (u0 i + u.1 i) x) j := by
  classical
  let Fj : Option (Fin n) → (Option ι → ℝ) → ℝ := fun j => match j with
    | none => fun _ => 0
    | some k => fun z => F z k
  have hFj (j : Option (Fin n)) : ContDiffOn ℝ ∞ (Fj j) U := by
    cases j with
    | none => exact contDiffOn_const
    | some k => exact contDiffOn_pi.mp hF k
  have hs (j : Option (Fin n)) := exists_scalarH1_time_composition_on_closedBall
    g (Fj j) (hFj j) hU t0 u0 hu0
  choose r hr C Nj hNj hRange hEval using hs
  let R := (Finset.univ : Finset (Option (Fin n))).inf' Finset.univ_nonempty r
  have hR : 0 < R := (Finset.lt_inf'_iff Finset.univ_nonempty).2 (fun j _ => hr j)
  have hRle (j : Option (Fin n)) : R ≤ r j := Finset.inf'_le r (Finset.mem_univ j)
  let S := Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) R
  let incl (j : Option (Fin n)) : S → Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) (r j) :=
    fun u => ⟨u.1, (Metric.closedBall_subset_closedBall (hRle j)) u.2⟩
  let K : ℝ≥0 := Finset.univ.sup C
  have hCle (j : Option (Fin n)) : C j ≤ K := Finset.le_sup (Finset.mem_univ j)
  let f : ℝ × S → Fin n → TensorHs g 0 0 1 := fun p j => Nj (some j) p.1 (incl (some j) p.2)
  have hf : LipschitzWith K f := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    rw [dist_eq_norm]
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg K.coe_nonneg dist_nonneg)).2
    intro j
    have h := (hNj (some j)).dist_le_mul (p.1, incl (some j) p.2) (q.1, incl (some j) q.2)
    change dist (f p j) (f q j) ≤ (C (some j) : ℝ) * dist p q at h
    simpa only [Pi.sub_apply, dist_eq_norm] using h.trans (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr (hCle (some j))) dist_nonneg)
  let N : ℝ → S → PiLp 2 (fun _ : Fin n => TensorHs g 0 0 1) :=
    fun t u => WithLp.toLp 2 (f (t, u))
  have hN := (PiLp.lipschitzWith_toLp 2 (fun _ : Fin n => TensorHs g 0 0 1)).comp hf
  refine ⟨R, hR, _, N, hN, ?_, ?_⟩
  · intro t ht u hu
    exact hRange none t ⟨ht.1, ht.2.trans (hRle none)⟩ u
      ((Metric.closedBall_subset_closedBall (hRle none)) hu)
  · intro t ht u x j
    exact hEval (some j) t ⟨ht.1, ht.2.trans (hRle (some j))⟩ (incl (some j) u) x

end DifferentialGeometry.Analysis.Spectral
