import DifferentialGeometry.Geometry.Collapse.SimultaneousProductionApplications
import DifferentialGeometry.Geometry.Collapse.SimultaneousLocalCoverSkeleton
import DifferentialGeometry.Geometry.Metric.Approximation.StrongEdgeSelection
import DifferentialGeometry.Geometry.Collapse.InducedVolumeComparison
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPairData

/-!
# LC88 / BCP04, packet P4: finite selections on a compact candidate envelope (BDRY-3)

Review 45 §3.4 (P4) and sheet-BDRY-2 §P0: the circle, slim and strong-edge selections of the
closed LC87 producer use compactness of the carrier only for (a) total boundedness of the
candidate set and the two-sided bounds of the scale on it and (b) finite volume of balls. On the
completed interior `(W°, d_ĝ)` the candidates lie in the compact set `{D ≥ 10}` and the carrier is
proper. Here, for a candidate set `E` inside a compact `K`:
* `exists_finite_disjoint_lipschitz_scale_selection_of_compact_BDRY3` (LFR51's Lipschitz-scale
  selection), `exists_finite_strong_edge_selection_of_compact_BDRY3` (LFR44's edge selection),
  `exists_finite_scale_cover_with_multiplicity_of_compact_BDRY3` (selection + packing);
* on a PROPER σ-compact Riemannian carrier: `exists_finite_scale_cover_of_ricci_bound_proper_BDRY3`,
  `exists_simultaneous_support_cover_proper_BDRY3` (the circle-family cover with LC87's
  multiplicity), `ncard_supports_meeting_ball_le_of_ricci_bound_proper_BDRY3` and
  `ncard_disjoint_family_balls_le_proper_BDRY3` (the edge multiplicity);
* consumer `exists_support_cover_completion_BDRY3`: the circle-family cover on `((W)°, d_ĝ)` for a
  candidate set inside `U₁ = {D > 10}`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric MeasureTheory Bundle Manifold
open scoped ENNReal Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian GC.Endpoint
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Integral.Measure GC.MetricGeometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-! ### Metric selections with a compact candidate envelope -/

section Metric

variable {X : Type*} [MetricSpace X]

/-- **LFR51's Lipschitz-scale selection on a compact candidate envelope.** The selection of
`Metric.exists_finite_disjoint_lipschitz_scale_selection` for a candidate set `E` contained in a
compact set `K` (no compactness of the carrier). -/
theorem exists_finite_disjoint_lipschitz_scale_selection_of_compact_BDRY3
    {K : Set X} (hK : IsCompact K) (E : Set X) (hEK : E ⊆ K) {ρ : X → ℝ} {Λ : NNReal} {Δ : ℝ}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ p, 0 < ρ p)
    (hΔ : 0 < Δ) (hsmall : (Λ : ℝ) * Δ ≤ 1 / 100) :
    ∃ I : Set X, I ⊆ E ∧ I.Finite ∧ I.PairwiseDisjoint (fun i => ball i (Δ * ρ i / 3)) ∧
      ∀ p ∈ E, ∃ i ∈ I, dist p i < 7 / 10 * Δ * ρ i ∧
        ρ p < 101 / 100 * ρ i ∧ ball p (Δ * ρ p) ⊆ ball i (2 * Δ * ρ i) := by
  classical
  rcases E.eq_empty_or_nonempty with hE | hE
  · exact ⟨∅, empty_subset E, finite_empty, by simp, fun p hp => by simp [hE] at hp⟩
  have hKne : K.Nonempty := hE.mono hEK
  obtain ⟨pmin, _, hmin⟩ := hK.exists_isMinOn hKne hρ.continuous.continuousOn
  obtain ⟨pmax, _, hmax⟩ := hK.exists_isMaxOn hKne hρ.continuous.continuousOn
  obtain ⟨I, hIE, hfin, hdisj, hcover⟩ := exists_finite_disjoint_ball_selection
    (hK.totallyBounded.subset hEK) (fun p => Δ * ρ p / 3) (R := Δ * ρ pmax / 3)
    (show 0 < Δ * ρ pmin / 3 from div_pos (mul_pos hΔ (hρpos pmin)) (by norm_num))
    (fun p hp => by nlinarith only [mul_le_mul_of_nonneg_left (hmin (hEK hp)) hΔ.le])
    (fun p hp => by nlinarith only [mul_le_mul_of_nonneg_left (hmax (hEK hp)) hΔ.le])
  refine ⟨I, hIE, hfin, hdisj, ?_⟩
  intro p hp
  obtain ⟨i, hi, hinter, _⟩ := hcover p hp
  obtain ⟨hd, hr⟩ := estimates_of_intersecting_lipschitz_scale_balls hρ hΔ (hρpos i) hsmall hinter
  refine ⟨i, hi, hd, hr, ?_⟩
  intro x hx
  have htri := dist_triangle x p i
  change dist x p < Δ * ρ p at hx
  change dist x i < 2 * Δ * ρ i
  have hr' := mul_lt_mul_of_pos_left hr hΔ
  nlinarith only [htri, hx, hd, hr', mul_pos hΔ (hρpos i)]

/-- **LFR44's strong-edge selection on a compact candidate envelope** (the strong edges `E` inside
a compact `K`). -/
theorem exists_finite_strong_edge_selection_of_compact_BDRY3 {K : Set X} (hK : IsCompact K)
    {E N W : Set X} (hEK : E ⊆ K) {ρ : X → ℝ} {Λ : NNReal} {Δ : ℝ} (hρ : LipschitzWith Λ ρ)
    (hρpos : ∀ x, 0 < ρ x) (hΔ : 1 ≤ Δ) (hsmall : (Λ : ℝ) * Δ ≤ 1 / 100)
    (hN : ∀ p ∈ N, ∃ q ∈ E, dist p q < Δ * ρ q) (hW : ∀ p ∈ W, ∃ q ∈ E, dist p q < ρ q) :
    ∃ I : Set X, I ⊆ E ∧ I.Finite ∧ I.PairwiseDisjoint (fun i => ball i (Δ * ρ i / 3)) ∧
      (∀ p ∈ N ∪ W, ∃ i ∈ I, dist p i < 2 * Δ * ρ i) ∧
      ∀ q ∈ E, ∃ i ∈ I, dist q i < Δ * ρ i := by
  have hΔpos : 0 < Δ := by linarith
  obtain ⟨I, hIE, hfin, hdisj, hcov⟩ :=
    exists_finite_disjoint_lipschitz_scale_selection_of_compact_BDRY3 hK E hEK hρ hρpos hΔpos
      hsmall
  refine ⟨I, hIE, hfin, hdisj, ?_, ?_⟩
  · have hnear (p : X) (q : X) (hq : q ∈ E) (hpq : dist p q < Δ * ρ q) :
        ∃ i ∈ I, dist p i < 2 * Δ * ρ i := by
      obtain ⟨i, hi, _, _, hball⟩ := hcov q hq
      exact ⟨i, hi, hball hpq⟩
    rintro p (hp | hp)
    · obtain ⟨q, hq, hpq⟩ := hN p hp
      exact hnear p q hq hpq
    · obtain ⟨q, hq, hpq⟩ := hW p hp
      exact hnear p q hq (hpq.trans_le (le_mul_of_one_le_left (hρpos q).le hΔ))
  · intro q hq
    obtain ⟨i, hi, hd, _, _⟩ := hcov q hq
    refine ⟨i, hi, hd.trans_le ?_⟩
    have := mul_pos hΔpos (hρpos i)
    nlinarith

variable [MeasurableSpace X] [BorelSpace X]

/-- **Selection with packing on a compact candidate envelope** (the measure form of
`exists_finite_scale_cover_with_multiplicity`). -/
theorem exists_finite_scale_cover_with_multiplicity_of_compact_BDRY3
    (μ : Measure X) {K : Set X} (hK : IsCompact K) (E : Set X) (hEK : E ⊆ K) {ρ : X → ℝ}
    {Λ : NNReal} {Δ C b : ℝ} (hρ : LipschitzWith Λ ρ) (hρpos : ∀ p, 0 < ρ p)
    (hΔ : 0 < Δ) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hselection : (Λ : ℝ) * Δ ≤ 1 / 100) (hoverlap : (Λ : ℝ) * C ≤ 1 / 4)
    (hpos : ∀ i ∈ E, 0 < μ.real (ball i (Δ * ρ i / 3)))
    (hfinite : ∀ i ∈ E, μ (ball i ((3 * C + 2 * (Δ / 3)) * ρ i)) ≠ ⊤)
    (hcomparison : ∀ i ∈ E, μ.real (ball i ((3 * C + 2 * (Δ / 3)) * ρ i)) ≤
      b * μ.real (ball i (Δ * ρ i / 3))) :
    ∃ I : Set X, I ⊆ E ∧ I.Finite ∧ I.PairwiseDisjoint (fun i => ball i (Δ * ρ i / 3)) ∧
      (∀ p ∈ E, ∃ i ∈ I, ball p (Δ * ρ p) ⊆ ball i (2 * Δ * ρ i)) ∧
      ∀ x : X, ((I ∩ {i | x ∈ ball i (C * ρ i)}).ncard : ℝ) ≤ b := by
  classical
  obtain ⟨I, hIE, hfin, hdisj, hcover⟩ :=
    exists_finite_disjoint_lipschitz_scale_selection_of_compact_BDRY3 hK E hEK hρ hρpos hΔ
      hselection
  refine ⟨I, hIE, hfin, hdisj, ?_, ?_⟩
  · intro p hp
    obtain ⟨i, hi, _, _, hc⟩ := hcover p hp
    exact ⟨i, hi, hc⟩
  · intro x
    let T := I ∩ {i | x ∈ ball i (C * ρ i)}
    have hT : T.Finite := hfin.subset inter_subset_left
    have ht (i : X) : i ∈ hT.toFinset ↔ i ∈ I ∧ x ∈ ball i (C * ρ i) := by
      simp only [Set.Finite.mem_toFinset, T, mem_inter_iff, mem_ofPred_eq]
    have hid : ∀ i, (Δ / 3) * ρ i = Δ * ρ i / 3 := by intro i; ring
    have hh := card_le_of_lipschitz_scale_ball_overlap μ hT.toFinset hρ
      (fun i _ => hρpos i) (a := Δ / 3) (C := C) (b := b) (by positivity) hC hb hoverlap
      (by
        intro i hi j hj hij
        simp only [hid]
        exact hdisj (ht i |>.mp hi).1 (ht j |>.mp hj).1 hij)
      (by intro i hi; rw [hid]; exact hpos i (hIE (ht i |>.mp hi).1))
      (fun i hi => hfinite i (hIE (ht i |>.mp hi).1))
      (by intro i hi; rw [hid]; exact hcomparison i (hIE (ht i |>.mp hi).1))
      x (fun i hi => (ht i |>.mp hi).2)
    change (T.ncard : ℝ) ≤ b
    rw [Set.ncard_eq_toFinset_card T hT]
    exact hh

end Metric

/-! ### Riemannian packing on a proper carrier -/

section Proper

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space (TangentBundle I M)]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [ConnectedSpace M] [ProperSpace M] [SigmaCompactSpace M]

/-- **LC87's scale cover with Bishop–Gromov packing on a proper carrier** (candidates inside a
compact `K`; `exists_finite_scale_cover_of_ricci_bound` without `CompactSpace`). -/
theorem exists_finite_scale_cover_of_ricci_bound_proper_BDRY3
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {K : Set M} (hK : IsCompact K) (S : Set M) (hSK : S ⊆ K) {ρ : M → ℝ} {Λ : NNReal}
    {Δ C q : ℝ} (hρ : LipschitzWith Λ ρ) (hρpos : ∀ p, 0 < ρ p)
    (hΔ : 0 < Δ) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hselection : (Λ : ℝ) * Δ ≤ 1 / 100) (hoverlap : (Λ : ℝ) * C ≤ 1 / 4)
    (hRic : ∀ p ∈ S, ricciBoundedBelowOn (I := I) g
      (ball p ((3 * C + 2 * (Δ / 3)) * ρ p))
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-((q / ρ p) ^ 2)))) :
    ∃ J : Set M, J ⊆ S ∧ J.Finite ∧ J.PairwiseDisjoint (fun p => ball p (Δ * ρ p / 3)) ∧
      (∀ p ∈ S, ∃ i ∈ J, ball p (Δ * ρ p) ⊆ ball i (2 * Δ * ρ i)) ∧
      ∀ x : M, ((J ∩ {i | x ∈ ball i (C * ρ i)}).ncard : ℝ) ≤
        modelVolume (-(q ^ 2)) (Module.finrank ℝ E) (3 * C + 2 * (Δ / 3)) /
          modelVolume (-(q ^ 2)) (Module.finrank ℝ E) (Δ / 3) := by
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let : IsFiniteMeasureOnCompacts μ := riemannianVolumeMeasure_isFiniteMeasureOnCompacts g
  let : μ.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure g
  let D := 3 * C + 2 * (Δ / 3)
  have hs : 0 < Δ / 3 := by positivity
  have hsD : Δ / 3 ≤ D := by dsimp only [D]; linarith
  have hn : 1 ≤ Module.finrank ℝ E := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hm (t : ℝ) (ht : 0 < t) : 0 < modelVolume (-(q ^ 2)) (Module.finrank ℝ E) t :=
    modelVolume_pos hn ht ⟨ht.le, fun h => (not_lt_of_ge (neg_nonpos.mpr (sq_nonneg _)) h).elim⟩
  have hball (p : M) (r : ℝ) :
      {y : M | riemannianEDist I p y < ENNReal.ofReal r} = ball p r := by
    ext y
    rw [mem_ofPred_eq, ← IsRiemannianManifold.out (I := I), edist_lt_ofReal]
    exact dist_comm p y ▸ Iff.rfl
  apply exists_finite_scale_cover_with_multiplicity_of_compact_BDRY3 μ hK S hSK hρ hρpos hΔ hC
    (div_nonneg (hm D (hs.trans_le hsD)).le (hm _ hs).le) hselection hoverlap
  · intro p _
    exact ENNReal.toReal_pos (measure_ball_pos μ p
      (div_pos (mul_pos hΔ (hρpos p)) (by norm_num))).ne' (measure_ball_lt_top (μ := μ)).ne
  · intro p _
    exact (measure_ball_lt_top (μ := μ)).ne
  · intro p hp
    have hric := hRic p hp
    rw [← hball p (D * ρ p)] at hric
    have hc := ballVolume_mul_scale_le_model_ratio g hEnorm p hq (hρpos p) hs hsD hric
    have hv (r : ℝ) : VolumeComparison.ballVolume g p r = μ (ball p r) := by
      simp only [VolumeComparison.ballVolume, μ, hball]
    rw [hv, hv] at hc
    have hc' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (measure_ball_lt_top (μ := μ)).ne) hc
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (div_nonneg (hm D (hs.trans_le hsD)).le (hm _ hs).le)] at hc'
    have hid : (Δ / 3) * ρ p = Δ * ρ p / 3 := by ring
    simpa only [hid, D, Measure.real] using hc'

/-- **The circle-family cover with LC87's multiplicity on a proper carrier** (candidates inside a
compact `K`; `exists_simultaneous_support_cover` without `CompactSpace`). -/
theorem exists_simultaneous_support_cover_proper_BDRY3 (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (hdim : Module.finrank ℝ E = 3)
    {K : Set M} (hK : IsCompact K) (S : Set M) (hSK : S ⊆ K) {r : M → ℝ} {Λ : NNReal}
    (hr : LipschitzWith Λ r) (hrpos : ∀ p, 0 < r p)
    (hsmall : (Λ : ℝ) * 2000000 ≤ 1 / 100)
    (hsec : ∀ p ∈ S, ∀ y ∈ ball p ((3 * 2000000 + 2 / 3) * r p),
      SectionalBoundedBelowAt g y (-((2000000 * r p) ^ 2)⁻¹)) :
    ∃ J : Set M, J ⊆ S ∧ J.Finite ∧ J.PairwiseDisjoint (fun p => ball p (r p / 3)) ∧
      (∀ p ∈ S, ∃ i ∈ J, ball p (r p) ⊆ ball i (2 * r i)) ∧
      ∀ x : M, ((J ∩ {i | x ∈ ball i (2000000 * r i)}).ncard : ℝ) ≤
        modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (3 * 2000000 + 2 / 3) /
          modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3) := by
  have hRic : ∀ p ∈ S, ricciBoundedBelowOn g
      (ball p ((3 * 2000000 + 2 * (1 / 3)) * r p))
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-(((1 / 2000000) / r p) ^ 2))) := by
    intro p hp
    rw [hdim]
    norm_num only [Nat.reduceSub, Nat.cast_ofNat]
    apply ricciBoundedBelowOn_of_sectional_three g hdim
    intro y hy
    have h := hsec p hp y (by convert hy using 1; norm_num)
    have he : -((2000000 * r p) ^ 2)⁻¹ = -(((1 / 2000000) / r p) ^ 2) := by
      field_simp
    simpa only [hdim, Nat.reduceSub, Nat.cast_ofNat, he] using h
  have hselection : (Λ : ℝ) * 1 ≤ 1 / 100 := by
    have hn : (0 : ℝ) ≤ Λ := Λ.property
    nlinarith
  have hoverlap : (Λ : ℝ) * 2000000 ≤ 1 / 4 := by linarith
  obtain ⟨J, hJS, hfin, hdisj, hcover, hmulti⟩ :=
    exists_finite_scale_cover_of_ricci_bound_proper_BDRY3 g hEnorm hK S hSK hr hrpos
      (Δ := 1) (C := 2000000) (q := 1 / 2000000)
      zero_lt_one (by norm_num) (by norm_num) hselection hoverlap hRic
  refine ⟨J, hJS, hfin, ?_, ?_, ?_⟩
  · simpa only [one_mul] using hdisj
  · simpa only [one_mul, mul_one] using hcover
  · convert hmulti using 1; norm_num [hdim]

/-- FC08's meeting-ball count on a PROPER carrier (balls have finite volume). -/
theorem ncard_supports_meeting_ball_le_of_ricci_bound_proper_BDRY3
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {ι : Type*} (J : Finset ι) (c : ι → M) (S : ι → Set M) {ρ : M → ℝ} {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x) {R C a q : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (ha : 0 < a) (hq : 0 ≤ q) (hbudget : Λ * max R C ≤ 1 / 4)
    (hS : ∀ j ∈ J, S j ⊆ closedBall (c j) (C * ρ (c j)))
    (hdisj : (J : Set ι).PairwiseDisjoint fun j => ball (c j) (a * ρ (c j))) (p : M)
    (hRic : ∀ j ∈ J, (S j ∩ ball p (R * ρ p)).Nonempty → ricciBoundedBelowOn (I := I) g
      (ball (c j) (4 * (R + 2 * C + a) * ρ (c j)))
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-((q / ρ (c j)) ^ 2)))) :
    ({j | j ∈ J ∧ (S j ∩ ball p (R * ρ p)).Nonempty}.ncard : ℝ) ≤
      modelVolume (-(q ^ 2)) (Module.finrank ℝ E) (4 * (R + 2 * C + a)) /
        modelVolume (-(q ^ 2)) (Module.finrank ℝ E) a := by
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let : IsFiniteMeasureOnCompacts μ := riemannianVolumeMeasure_isFiniteMeasureOnCompacts g
  let : μ.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure g
  let D := 4 * (R + 2 * C + a)
  have haD : a ≤ D := by dsimp only [D]; linarith
  have hn : 1 ≤ Module.finrank ℝ E := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hm (t : ℝ) (ht : 0 < t) : 0 < modelVolume (-(q ^ 2)) (Module.finrank ℝ E) t :=
    modelVolume_pos hn ht ⟨ht.le, fun h => (not_lt_of_ge (neg_nonpos.mpr (sq_nonneg _)) h).elim⟩
  have hball (x : M) (r : ℝ) :
      {y : M | riemannianEDist I x y < ENNReal.ofReal r} = ball x r := by
    ext y
    rw [mem_ofPred_eq, ← IsRiemannianManifold.out (I := I), edist_lt_ofReal]
    exact dist_comm x y ▸ Iff.rfl
  apply GC.MetricGeometry.card_supports_meeting_ball_le μ J c S hρ hρpos hR hC ha.le
    (div_nonneg (hm D (ha.trans_le haD)).le (hm a ha).le) hbudget hS hdisj p
  · intro j _ _
    exact ENNReal.toReal_pos (measure_ball_pos μ (c j) (mul_pos ha (hρpos (c j)))).ne'
      (measure_ball_lt_top (μ := μ)).ne
  · intro j _ _
    exact (measure_ball_lt_top (μ := μ)).ne
  · intro j hj hmeet
    have hric := hRic j hj hmeet
    rw [← hball (c j) (D * ρ (c j))] at hric
    have hcmp := ballVolume_mul_scale_le_model_ratio g hEnorm (c j) hq (hρpos (c j)) ha haD hric
    have hv (r : ℝ) : VolumeComparison.ballVolume g (c j) r = μ (ball (c j) r) := by
      simp only [VolumeComparison.ballVolume, μ, hball]
    rw [hv, hv] at hcmp
    have hcmp' := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ball_lt_top (μ := μ)).ne) hcmp
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (div_nonneg (hm D (ha.trans_le haD)).le (hm a ha).le)] at hcmp'
    simpa only [D, Measure.real] using hcmp'

/-- The scaled form (radii `R Δ, C Δ, a Δ`) on a proper carrier. -/
theorem ncard_supports_meeting_ball_le_of_scaled_ricci_bound_proper_BDRY3
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {ι : Type*} (J : Finset ι) (c : ι → M) (S : ι → Set M) {ρ : M → ℝ} {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x) {Δ R C a q : ℝ} (hΔ : 0 < Δ)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (ha : 0 < a) (hq : 0 ≤ q)
    (hbudget : Λ * max (R * Δ) (C * Δ) ≤ 1 / 4)
    (hS : ∀ j ∈ J, S j ⊆ closedBall (c j) (C * Δ * ρ (c j)))
    (hdisj : (J : Set ι).PairwiseDisjoint fun j => ball (c j) (a * Δ * ρ (c j))) (p : M)
    (hRic : ∀ j ∈ J, (S j ∩ ball p (R * Δ * ρ p)).Nonempty → ricciBoundedBelowOn (I := I) g
      (ball (c j) (4 * (R + 2 * C + a) * Δ * ρ (c j)))
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-((q / (Δ * ρ (c j))) ^ 2)))) :
    ({j | j ∈ J ∧ (S j ∩ ball p (R * Δ * ρ p)).Nonempty}.ncard : ℝ) ≤
      modelVolume (-(q ^ 2)) (Module.finrank ℝ E) (4 * (R + 2 * C + a)) /
        modelVolume (-(q ^ 2)) (Module.finrank ℝ E) a := by
  have hn : 1 ≤ Module.finrank ℝ E := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have h := ncard_supports_meeting_ball_le_of_ricci_bound_proper_BDRY3 g hEnorm J c S hρ hρpos
    (R := R * Δ) (C := C * Δ) (a := a * Δ) (q := q / Δ) (by positivity) (by positivity)
    (by positivity) (div_nonneg hq hΔ.le) hbudget hS hdisj p (by
      intro j hj hmeet
      have hr := hRic j hj hmeet
      have h1 : 4 * (R * Δ + 2 * (C * Δ) + a * Δ) * ρ (c j) =
          4 * (R + 2 * C + a) * Δ * ρ (c j) := by ring
      have h2 : q / Δ / ρ (c j) = q / (Δ * ρ (c j)) := by rw [div_div]
      rw [h1, h2]
      exact hr)
  have h1 : 4 * (R * Δ + 2 * (C * Δ) + a * Δ) = Δ * (4 * (R + 2 * C + a)) := by ring
  rw [h1, mul_comm a Δ, modelVolume_neg_sq_scale q Δ _ _ hq hΔ hn,
    modelVolume_neg_sq_scale q Δ _ _ hq hΔ hn,
    mul_div_mul_left _ _ (pow_ne_zero _ hΔ.ne')] at h
  exact h

/-- **The edge multiplicity on a proper carrier** (`ncard_disjoint_family_balls_le` without
`CompactSpace`). -/
theorem ncard_disjoint_family_balls_le_proper_BDRY3 (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (hdim : Module.finrank ℝ E = 3)
    {ρ : M → ℝ} {Λ : NNReal} (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x) {Δ : ℝ}
    (hΔ : 0 < Δ) (hbudget : (Λ : ℝ) * (2000000 * Δ) ≤ 1 / 4) {Je : Set M} (hfin : Je.Finite)
    (hdisj : Je.PairwiseDisjoint fun j => ball j (Δ * ρ j / 3))
    (hsec : ∀ j ∈ Je, ∀ y ∈ ball j (4 * (1 + 2 * 2000000 + 1 / 3) * Δ * ρ j),
      SectionalBoundedBelowAt g y (-((4 * (1 + 2 * 2000000 + 1 / 3) * Δ * ρ j) ^ 2)⁻¹))
    (x : M) :
    ((Je ∩ {j | x ∈ ball j (2000000 * (Δ * ρ j))}).ncard : ℝ) ≤
      modelVolume (-((1 / (4 * (1 + 2 * 2000000 + 1 / 3)) : ℝ) ^ 2)) 3
          (4 * (1 + 2 * 2000000 + 1 / 3)) /
        modelVolume (-((1 / (4 * (1 + 2 * 2000000 + 1 / 3)) : ℝ) ^ 2)) 3 (1 / 3) := by
  have hdisj' : ((hfin.toFinset : Set M)).PairwiseDisjoint
      fun j => ball (id j) (1 / 3 * Δ * ρ (id j)) := by
    rw [Set.Finite.coe_toFinset]
    convert hdisj using 2 with j
    simp only [id]
    ring_nf
  have h := ncard_supports_meeting_ball_le_of_scaled_ricci_bound_proper_BDRY3 g hEnorm
    hfin.toFinset id
    (fun j => ball j (2000000 * (Δ * ρ j))) hρ hρpos (Δ := Δ) (R := 1) (C := 2000000)
    (a := 1 / 3) (q := 1 / (4 * (1 + 2 * 2000000 + 1 / 3))) hΔ zero_le_one (by norm_num)
    (by norm_num) (by positivity) (by
      rw [max_eq_right (by nlinarith)]
      linarith) (fun j _ y hy => by
      simp only [id, mem_closedBall, mem_ball] at hy ⊢
      linarith) hdisj' x (fun j hj _ => by
      have h2 : ((3 - 1 : ℕ) : ℝ) = 2 := by norm_num
      rw [hdim, h2]
      apply ricciBoundedBelowOn_of_sectional_three g hdim
      intro y hy
      have hj' : j ∈ Je := hfin.mem_toFinset.mp hj
      have h := hsec j hj' y (by simpa only [id] using hy)
      have hρj := hρpos j
      have he : -((4 * (1 + 2 * 2000000 + 1 / 3) * Δ * ρ j) ^ 2)⁻¹ =
          -((1 / (4 * (1 + 2 * 2000000 + 1 / 3)) / (Δ * ρ (id j))) ^ 2) := by
        simp only [id]
        field_simp
      rwa [he] at h)
  rw [hdim] at h
  refine le_trans ?_ h
  have hsub : Je ∩ {j | x ∈ ball j (2000000 * (Δ * ρ j))} ⊆
      {j | j ∈ hfin.toFinset ∧ ((fun j => ball j (2000000 * (Δ * ρ j))) j ∩
        ball x (1 * Δ * ρ x)).Nonempty} := by
    intro j hj
    exact ⟨hfin.mem_toFinset.mpr hj.1, x, hj.2, mem_ball_self (by
      have := hρpos x
      positivity)⟩
  exact_mod_cast Set.ncard_le_ncard hsub
    (hfin.toFinset.finite_toSet.subset fun j hj => hj.1)

end Proper

/-! ### Consumer: the circle-family cover on the completed interior -/

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **Consumer: LC87's circle-family cover on `(W°, d_ĝ)`.** For a complete completion `ĝ` and a
candidate set `S ⊆ U₁ = {D > 10}` with LC87's curvature buffer at its points, a Lipschitz scale `r`
on `W°` gives a finite `r/3`-disjoint selection `J ⊆ S` whose doubled balls cover the `r`-balls of
`S`, with LC87's multiplicity (no compactness of `W°`; the candidates lie in the compact
`{D ≥ 10}` and `(W°, d_ĝ)` is proper). -/
theorem exists_support_cover_completion_BDRY3 (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
    (g : SmoothRiemannianMetric W.model W.Carrier)
    (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤))
    (hcomp : RiemannianMetricComplete (I := 𝓡 3) ĝ) :
    letI := inducedMetricSpace ĝ
    ∀ (S : Set (W.pieceInterior ⊤)), S ⊆ {x | ENNReal.ofReal 10 < distanceToBoundary W g x} →
    ∀ {r : W.pieceInterior ⊤ → ℝ} {Λ : NNReal}, LipschitzWith Λ r → (∀ p, 0 < r p) →
      (Λ : ℝ) * 2000000 ≤ 1 / 100 →
      (∀ p ∈ S, ∀ y ∈ ball p ((3 * 2000000 + 2 / 3) * r p),
        SectionalBoundedBelowAt ĝ y (-((2000000 * r p) ^ 2)⁻¹)) →
    ∃ J : Set (W.pieceInterior ⊤), J ⊆ S ∧ J.Finite ∧
      J.PairwiseDisjoint (fun p => ball p (r p / 3)) ∧
      (∀ p ∈ S, ∃ i ∈ J, ball p (r p) ⊆ ball i (2 * r i)) ∧
      ∀ x : W.pieceInterior ⊤, ((J ∩ {i | x ∈ ball i (2000000 * r i)}).ncard : ℝ) ≤
        modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (3 * 2000000 + 2 / 3) /
          modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3) := by
  let instM_BDRY3 : MetricSpace (W.pieceInterior ⊤) := inducedMetricSpace ĝ
  intro S hS r Λ hr hrpos hsmall hsec
  have instNZ_BDRY3 : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :=
    ⟨by rw [finrank_euclideanSpace_fin]; norm_num⟩
  let instRB_BDRY3 : RiemannianBundle
      (fun x : W.pieceInterior ⊤ ↦ TangentSpace (𝓡 3) x) := ⟨ĝ.toRiemannianMetric⟩
  obtain ⟨hRM, hEnorm, hcont⟩ := inducedMetricSpace_riemannian ĝ
  have instP_BDRY3 : ProperSpace (W.pieceInterior ⊤) :=
    inducedMetricSpace_properSpace_of_riemannianMetricComplete hcomp
  have hK := isCompact_le_distanceToBoundary_BDRY1 W g (by norm_num : (0 : ℝ) < 10)
  exact exists_simultaneous_support_cover_proper_BDRY3 ĝ hEnorm finrank_euclideanSpace_fin hK S
    (fun x hx => show ENNReal.ofReal 10 ≤ distanceToBoundary W g x from (hS hx).le) hr hrpos
    hsmall hsec

end DifferentialGeometry.Geometry.Collapse
