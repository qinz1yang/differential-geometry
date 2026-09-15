import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.AddCircleLocalComposition
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.TimeComposition

noncomputable section
open scoped Manifold ContDiff NNReal ENNReal

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Integral.L2

variable {ι : Type*} [Fintype ι]
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private def timeCoordinate
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (σ : ℝ) :
    ℝ × PiLp 2 (fun _ : ι => TensorHs g 0 0 σ) →L[ℝ]
      PiLp 2 (fun _ : Option ι => TensorHs g 0 0 σ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Option ι => TensorHs g 0 0 σ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j => match j with
      | none => ((ContinuousLinearMap.id ℝ ℝ).smulRight
          (ccTensorToHs g 0 σ (scalarCc g 1))).comp (ContinuousLinearMap.fst ℝ ℝ _)
      | some i => (PiLp.proj 2 (fun _ : ι => TensorHs g 0 0 σ) i).comp
        (ContinuousLinearMap.snd ℝ ℝ _))

private theorem timeCoordinate_eval
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (σ : ℝ) (hσ : 1 ≤ σ)
    (p : ℝ × PiLp 2 (fun _ : ι => TensorHs g 0 0 σ)) (x : AddCircle (1 : ℝ)) :
    scalarH1PiToContinuous g
      (ContinuousLinearMap.piLpMap 2 (fun _ : Option ι => tensorHsInclusion (g := g) (r := 0) (s := 0) hσ)
        (timeCoordinate g σ p)) x = fun j => match j with
          | none => p.1
          | some i => scalarH1ToContinuous g (tensorHsInclusion hσ (p.2 i)) x := by
  funext j
  cases j with
  | none =>
    change scalarH1ToContinuous g (tensorHsInclusion hσ (p.1 • ccTensorToHs g 0 σ (scalarCc g 1))) x = _
    rw [map_smul, tensorHsInclusion_ccTensorToHs, map_smul, scalarH1ToContinuous_one]
    simp only [ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]
  | some i => rfl

private theorem exists_scalar_time_composition_on_ball
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (F : (Option ι → ℝ) → ℝ) {U : Set (Option ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (t0 : ℝ) (u0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1)))
    (hu0 : Set.range (fun x : AddCircle (1 : ℝ) => fun j => match j with
      | none => t0
      | some i => scalarH1ToContinuous g
        (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ (k : ℝ) + 1) (u0 i)) x) ⊆ U) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ (k : ℝ) + 1)
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ≥0,
      ∃ N : Metric.ball (t0, u0) δ → TensorHs g 0 0 ((k : ℝ) + 1),
        LipschitzWith C N ∧
        (∀ p ∈ Metric.ball (t0, u0) δ,
          Set.range (fun x : AddCircle (1 : ℝ) => fun j => match j with
            | none => p.1
            | some i => scalarH1ToContinuous g (J (p.2 i)) x) ⊆ U) ∧
        ∀ p x, scalarH1ToContinuous g (J (N p)) x =
          F (fun j => match j with
            | none => p.1.1
            | some i => scalarH1ToContinuous g (J (p.1.2 i)) x) := by
  intro J
  have hbase : Set.range (scalarH1PiToContinuous g
      (ContinuousLinearMap.piLpMap 2 (fun _ : Option ι => J)
        (timeCoordinate g ((k : ℝ) + 1) (t0, u0)))) ⊆ U := by
    rintro z ⟨x, rfl⟩
    rw [timeCoordinate_eval]
    exact hu0 (Set.mem_range_self x)
  obtain ⟨r, hr, C, N, hN, hRange, hNe, _⟩ := exists_scalarHs_composition_on_ball
    g k F hF hU (timeCoordinate g ((k : ℝ) + 1) (t0, u0)) hbase
  have hnear : ∀ᶠ p in nhds (t0, u0),
      timeCoordinate g ((k : ℝ) + 1) p ∈
        Metric.ball (timeCoordinate g ((k : ℝ) + 1) (t0, u0)) r :=
    (timeCoordinate g ((k : ℝ) + 1)).continuous.continuousAt.eventually
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
  obtain ⟨δ, hδ, hmap⟩ := Metric.eventually_nhds_iff.mp hnear
  let A : Metric.ball (t0, u0) δ →
      Metric.ball (timeCoordinate g ((k : ℝ) + 1) (t0, u0)) r :=
    fun p => ⟨timeCoordinate g ((k : ℝ) + 1) p, hmap p.2⟩
  have hA : LipschitzWith ‖timeCoordinate (ι := ι) g ((k : ℝ) + 1)‖₊ A := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    exact (timeCoordinate (ι := ι) g ((k : ℝ) + 1)).dist_le_opNorm p.1 q.1
  refine ⟨δ, hδ, C * ‖timeCoordinate (ι := ι) g ((k : ℝ) + 1)‖₊,
    fun p => N (A p), hN.comp hA, ?_, ?_⟩
  · intro p hp
    rintro z ⟨x, rfl⟩
    have h := hRange _ (hmap hp) (Set.mem_range_self x)
    simpa only [timeCoordinate_eval] using h
  · intro p x
    rw [hNe, timeCoordinate_eval]

theorem exists_scalarHs_time_composition_on_closedBall
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (F : (Option ι → ℝ) → ℝ) {U : Set (Option ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (t0 : ℝ) (u0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1)))
    (hu0 : Set.range (fun x : AddCircle (1 : ℝ) => fun j => match j with
      | none => t0
      | some i => scalarH1ToContinuous g
        (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ (k : ℝ) + 1) (u0 i)) x) ⊆ U) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ (k : ℝ) + 1)
    ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ≥0,
      ∃ N : ℝ → Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1))) R →
        TensorHs g 0 0 ((k : ℝ) + 1),
      LipschitzWith C (fun p : ℝ × Metric.closedBall
        (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1))) R => N p.1 p.2) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) R,
        ∀ u ∈ Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1))) R,
        Set.range (fun x : AddCircle (1 : ℝ) => fun j => match j with
          | none => t0 + t
          | some i => scalarH1ToContinuous g (J (u0 i + u i)) x) ⊆ U) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) R, ∀ u x,
        scalarH1ToContinuous g (J (N t u)) x = F (fun j => match j with
          | none => t0 + t
          | some i => scalarH1ToContinuous g (J (u0 i + u.1 i)) x) := by
  intro J
  obtain ⟨δ, hδ, C, N, hN, hRange, hNe⟩ := exists_scalar_time_composition_on_ball g k F hF hU t0 u0 hu0
  let R := δ / 2
  have hR : 0 < R := half_pos hδ
  let S := Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1))) R
  have hmap (p : ℝ × S) :
      (t0 + (Set.projIcc 0 R hR.le p.1 : ℝ), u0 + p.2.1) ∈ Metric.ball (t0, u0) δ := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    constructor
    · have hc := (Set.projIcc 0 R hR.le p.1).2
      simp only [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg hc.1]
      exact hc.2.trans_lt (half_lt_self hδ)
    · have hu := p.2.2
      rw [Metric.mem_closedBall, dist_zero_right] at hu
      rw [dist_eq_norm, add_sub_cancel_left]
      exact hu.trans_lt (half_lt_self hδ)
  let A : ℝ × S → Metric.ball (t0, u0) δ := fun p => ⟨_, hmap p⟩
  have hA : LipschitzWith 1 A := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    change dist (t0 + (Set.projIcc 0 R hR.le p.1 : ℝ), u0 + p.2.1)
      (t0 + (Set.projIcc 0 R hR.le q.1 : ℝ), u0 + q.2.1) ≤ (1 : ℝ) * dist p q
    rw [one_mul, Prod.dist_eq, Prod.dist_eq, dist_add_left, dist_add_left]
    apply max_le_max
    · simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq] using
        (LipschitzWith.projIcc hR.le).dist_le_mul p.1 q.1
    · exact le_rfl
  refine ⟨R, hR, C, fun t u => N (A (t,u)), ?_, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro p q
    exact (hN.dist_le_mul (A p) (A q)).trans
      (mul_le_mul_of_nonneg_left (by simpa only [NNReal.coe_one, one_mul] using hA.dist_le_mul p q) C.coe_nonneg)
  · intro t ht u hu
    have h := hRange _ (hmap (t, ⟨u, hu⟩))
    simpa only [Set.projIcc_of_mem hR.le ht, PiLp.add_apply] using h
  · intro t ht u x
    rw [hNe]
    congr 1
    funext j
    cases j with
    | none =>
        change t0 + (Set.projIcc 0 R hR.le t : ℝ) = t0 + t
        rw [Set.projIcc_of_mem hR.le ht]
    | some i => rfl


theorem exists_vectorHs_time_composition_on_closedBall
    {κ : Type*} [Fintype κ]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (F : (Option ι → ℝ) → (κ → ℝ)) {U : Set (Option ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (t0 : ℝ) (u0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1)))
    (hu0 : Set.range (fun x : AddCircle (1 : ℝ) => fun j => match j with
      | none => t0
      | some i => scalarH1ToContinuous g
        (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ (k : ℝ) + 1) (u0 i)) x) ⊆ U) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ (k : ℝ) + 1)
    ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ≥0,
      ∃ N : ℝ → Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1))) R →
        PiLp 2 (fun _ : κ => TensorHs g 0 0 ((k : ℝ) + 1)),
      LipschitzWith C (fun p : ℝ × Metric.closedBall
        (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1))) R => N p.1 p.2) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) R,
        ∀ u ∈ Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1))) R,
        Set.range (fun x : AddCircle (1 : ℝ) => fun j => match j with
          | none => t0 + t
          | some i => scalarH1ToContinuous g (J (u0 i + u i)) x) ⊆ U) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) R, ∀ u x i,
        scalarH1ToContinuous g (J (N t u i)) x = F (fun j => match j with
          | none => t0 + t
          | some i => scalarH1ToContinuous g (J (u0 i + u.1 i)) x) i := by
  intro J
  classical
  let Fj : Option (κ) → (Option ι → ℝ) → ℝ := fun j => match j with
    | none => fun _ => 0
    | some k => fun z => F z k
  have hFj (j : Option (κ)) : ContDiffOn ℝ ∞ (Fj j) U := by
    cases j with
    | none => exact contDiffOn_const
    | some k => exact contDiffOn_pi.mp hF k
  have hs (j : Option (κ)) := exists_scalarHs_time_composition_on_closedBall
    g k (Fj j) (hFj j) hU t0 u0 hu0
  choose r hr C Nj hNj hRange hEval using hs
  let R := (Finset.univ : Finset (Option (κ))).inf' Finset.univ_nonempty r
  have hR : 0 < R := (Finset.lt_inf'_iff Finset.univ_nonempty).2 (fun j _ => hr j)
  have hRle (j : Option (κ)) : R ≤ r j := Finset.inf'_le r (Finset.mem_univ j)
  let S := Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1))) R
  let incl (j : Option (κ)) : S → Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1))) (r j) :=
    fun u => ⟨u.1, (Metric.closedBall_subset_closedBall (hRle j)) u.2⟩
  let K : ℝ≥0 := Finset.univ.sup C
  have hCle (j : Option (κ)) : C j ≤ K := Finset.le_sup (Finset.mem_univ j)
  let f : ℝ × S → κ → TensorHs g 0 0 ((k : ℝ) + 1) := fun p j => Nj (some j) p.1 (incl (some j) p.2)
  have hf : LipschitzWith K f := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    rw [dist_eq_norm]
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg K.coe_nonneg dist_nonneg)).2
    intro j
    have h := (hNj (some j)).dist_le_mul (p.1, incl (some j) p.2) (q.1, incl (some j) q.2)
    change dist (f p j) (f q j) ≤ (C (some j) : ℝ) * dist p q at h
    simpa only [Pi.sub_apply, dist_eq_norm] using h.trans (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr (hCle (some j))) dist_nonneg)
  let N : ℝ → S → PiLp 2 (fun _ : κ => TensorHs g 0 0 ((k : ℝ) + 1)) :=
    fun t u => WithLp.toLp 2 (f (t, u))
  have hN := (PiLp.lipschitzWith_toLp 2 (fun _ : κ => TensorHs g 0 0 ((k : ℝ) + 1))).comp hf
  refine ⟨R, hR, _, N, hN, ?_, ?_⟩
  · intro t ht u hu
    exact hRange none t ⟨ht.1, ht.2.trans (hRle none)⟩ u
      ((Metric.closedBall_subset_closedBall (hRle none)) hu)
  · intro t ht u x j
    exact hEval (some j) t ⟨ht.1, ht.2.trans (hRle (some j))⟩ (incl (some j) u) x


theorem exists_scalar_vectorHs_time_composition_on_closedBall
    {κ : Type*} [Fintype κ]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (F : (Option ι → ℝ) → ℝ) (G : (Option ι → ℝ) → (κ → ℝ)) {U : Set (Option ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U)
    (t0 : ℝ) (u0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1)))
    (hu0 : Set.range (fun x : AddCircle (1 : ℝ) => fun j => match j with
      | none => t0
      | some i => scalarH1ToContinuous g
        (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ (k : ℝ) + 1) (u0 i)) x) ⊆ U) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ (k : ℝ) + 1)
    ∃ R : ℝ, 0 < R ∧ ∃ Cα CB : ℝ≥0,
      ∃ α : ℝ → Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1))) R →
        TensorHs g 0 0 ((k : ℝ) + 1),
      ∃ B : ℝ → Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1))) R →
        PiLp 2 (fun _ : κ => TensorHs g 0 0 ((k : ℝ) + 1)),
      LipschitzWith Cα (fun p : ℝ × Metric.closedBall
        (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1))) R => α p.1 p.2) ∧
      LipschitzWith CB (fun p : ℝ × Metric.closedBall
        (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1))) R => B p.1 p.2) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) R,
        ∀ u ∈ Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1))) R,
        Set.range (fun x : AddCircle (1 : ℝ) => fun j => match j with
          | none => t0 + t
          | some i => scalarH1ToContinuous g (J (u0 i + u i)) x) ⊆ U) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) R, ∀ u x,
        scalarH1ToContinuous g (J (α t u)) x = F (fun j => match j with
          | none => t0 + t
          | some i => scalarH1ToContinuous g (J (u0 i + u.1 i)) x)) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) R, ∀ u x j,
        scalarH1ToContinuous g (J (B t u j)) x = G (fun i => match i with
          | none => t0 + t
          | some i => scalarH1ToContinuous g (J (u0 i + u.1 i)) x) j := by
  intro J
  obtain ⟨r, hr, Cα, α, hα, hRange, hαeval⟩ :=
    exists_scalarHs_time_composition_on_closedBall g k F hF hU t0 u0 hu0
  obtain ⟨s, hs, CB, B, hB, _, hBeval⟩ :=
    exists_vectorHs_time_composition_on_closedBall g k G hG hU t0 u0 hu0
  let R := min r s
  have hR : 0 < R := lt_min hr hs
  let S := Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1))) R
  let inclα : S → Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1))) r :=
    fun u => ⟨u.1, (Metric.closedBall_subset_closedBall (min_le_left r s)) u.2⟩
  let inclB : S → Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1))) s :=
    fun u => ⟨u.1, (Metric.closedBall_subset_closedBall (min_le_right r s)) u.2⟩
  refine ⟨R, hR, Cα, CB, fun t u => α t (inclα u), fun t u => B t (inclB u), ?_, ?_, ?_, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro p q
    exact hα.dist_le_mul (p.1, inclα p.2) (q.1, inclα q.2)
  · apply LipschitzWith.of_dist_le_mul
    intro p q
    exact hB.dist_le_mul (p.1, inclB p.2) (q.1, inclB q.2)
  · intro t ht u hu
    exact hRange t ⟨ht.1, ht.2.trans (min_le_left r s)⟩ u
      ((Metric.closedBall_subset_closedBall (min_le_left r s)) hu)
  · intro t ht u x
    exact hαeval t ⟨ht.1, ht.2.trans (min_le_left r s)⟩ (inclα u) x
  · intro t ht u x j
    exact hBeval t ⟨ht.1, ht.2.trans (min_le_right r s)⟩ (inclB u) x j


end AddCircle
