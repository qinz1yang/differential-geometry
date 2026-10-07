import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HEndInitial_O32

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal

universe u

namespace GC.LongTime.Ch12

/-! CH12-O32 G2: hEnd-S (`[FROZEN] CH12-O32 hEnd-initial`) from the two parts P1 `hconvS`
(S's convergence maps are eventually GOOD at any fixed accuracy) and P2 `hstepW` (the
geometric step at the thick accuracy `βw`, which does not use `g₁`).  `β := max βw b`, where
`b` is an upper envelope of the accuracies reached by S's maps along the slice times. -/

/-- GOOD (the v5 text) is monotone in the accuracy. -/
theorem good_mono_O32 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u}) (t : ℝ)
    (q : H.Carrier → (postStage F.observation t).Carrier) {β₁ β₂ : ℝ} (h1 : 0 < β₁)
    (h12 : β₁ ≤ β₂)
    (hq : ∃ U : TopologicalSpace.Opens H.Carrier,
      riemannianBallOf H.metric H.basepoint (2 * β₁⁻¹) ⊆ U ∧ ContMDiffOn (𝓡 3) (𝓡 3) ∞ q U ∧
      IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => q x) ∧
      ∀ k : ℕ, k ≤ ⌈β₁⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * β₁⁻¹),
        ckErr_S45 H (postMetric F.observation t) t⁻¹ q k p < β₁) :
    ∃ U : TopologicalSpace.Opens H.Carrier,
      riemannianBallOf H.metric H.basepoint (2 * β₂⁻¹) ⊆ U ∧ ContMDiffOn (𝓡 3) (𝓡 3) ∞ q U ∧
      IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => q x) ∧
      ∀ k : ℕ, k ≤ ⌈β₂⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * β₂⁻¹),
        ckErr_S45 H (postMetric F.observation t) t⁻¹ q k p < β₂ := by
  obtain ⟨U, hU, hs, he, hk⟩ := hq
  have hinv : β₂⁻¹ ≤ β₁⁻¹ := inv_anti₀ h1 h12
  have hball : riemannianBallOf H.metric H.basepoint (2 * β₂⁻¹) ⊆ riemannianBallOf H.metric H.basepoint (2 * β₁⁻¹) :=
    riemannianBallOf_mono _ _ (by linarith)
  exact ⟨U, hball.trans hU, hs, he, fun k hk' p hp =>
    lt_of_lt_of_le (hk k (hk'.trans (Nat.ceil_mono hinv)) p (hball hp)) h12⟩

/-- Upper envelope: a positive null sequence `a`, read along any times `τ j`, is dominated by a
nonnegative function of time tending to `0` (`a j ≤ b (τ j)`). -/
theorem exists_envelope_O32 (τ : ℕ → ℝ) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j) (ha1 : ∀ j, a j ≤ 1)
    (ha0 : Filter.Tendsto a Filter.atTop (nhds 0)) :
    ∃ b : ℝ → ℝ, (∀ t, 0 ≤ b t) ∧ Filter.Tendsto b Filter.atTop (nhds 0) ∧
      ∀ j, a j ≤ b (τ j) := by
  have hbdd : ∀ t : ℝ, BddAbove (a '' {j | t ≤ τ j}) := fun t =>
    ⟨1, by rintro x ⟨j, -, rfl⟩; exact ha1 j⟩
  refine ⟨fun t => sSup (a '' {j | t ≤ τ j}), fun t => ?_, ?_, fun j => ?_⟩
  · exact Real.sSup_nonneg (by rintro x ⟨j, -, rfl⟩; exact (ha j).le)
  · refine Metric.tendsto_atTop.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 ha0 (ε / 2) (by linarith)
    refine ⟨∑ j ∈ Finset.range N, |τ j| + 1, fun t ht => ?_⟩
    have hle : sSup (a '' {j | t ≤ τ j}) ≤ ε / 2 := by
      refine Real.sSup_le ?_ (by linarith)
      rintro x ⟨j, hj, rfl⟩
      have hjN : N ≤ j := by
        by_contra hlt
        have hmem : j ∈ Finset.range N := Finset.mem_range.2 (not_le.1 hlt)
        have h1 : |τ j| ≤ ∑ i ∈ Finset.range N, |τ i| :=
          Finset.single_le_sum (fun i _ => abs_nonneg (τ i)) hmem
        have h2 := le_abs_self (τ j)
        have h3 : t ≤ τ j := hj
        linarith
      have := hN j hjN
      rw [Real.dist_eq, sub_zero, abs_of_pos (ha j)] at this
      linarith
    have hnn : 0 ≤ sSup (a '' {j | t ≤ τ j}) :=
      Real.sSup_nonneg (by rintro x ⟨j, -, rfl⟩; exact (ha j).le)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    linarith
  · exact le_csSup (hbdd _) ⟨j, (le_rfl : τ j ≤ τ j), rfl⟩

/-- `[FROZEN] CH12-O32` assembly: hEnd-S from P1 `hconvS` and P2 `hstepW`. -/
theorem hEnd_S_of_parts_O32 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u}) (wstar a : ℝ)
    (S : LatePointSequence_S13 F)
    (Φ : PointedRiemannianConvergenceMaps S.pointedSeq (modelPointed_S13 H) id)
    (hconvS : ∀ (δ r : ℝ) (m : ℕ), 0 < δ → 0 < r → ∃ I : ℕ, ∀ i : ℕ, I ≤ i →
      ∃ U : TopologicalSpace.Opens H.Carrier,
        riemannianBallOf H.metric H.basepoint r ⊆ U ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (sliceApprox_O32 S H Φ i) U ∧
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => sliceApprox_O32 S H Φ i x) ∧
        ∀ k : ℕ, k ≤ m → ∀ p ∈ riemannianBallOf H.metric H.basepoint r,
          ckErr_S45 H (postMetric F.observation (S.slices i).time) (S.slices i).time⁻¹
            (sliceApprox_O32 S H Φ i) k p < δ)
    (hstepW : ∃ βw : ℝ → ℝ, (∀ t, 0 < βw t) ∧ Filter.Tendsto βw Filter.atTop (nhds 0) ∧
      ∀ (ε R : ℝ) (k : ℕ), 0 < ε → 0 < R → ∃ (ε' R' : ℝ) (k' : ℕ), 0 < ε' ∧ 0 < R' ∧
        ε' ≤ ε ∧ R ≤ R' ∧ k ≤ k' ∧ ∃ Te : ℝ,
        ∀ (t t₂ : ℝ) (ht : 0 < t), Te ≤ t → t₂ = 2 * t →
        ∀ f : (s : ℝ) → s ∈ Icc t t₂ → H.Carrier → (postStage F.observation s).Carrier,
          (∀ s (hs : s ∈ Icc t t₂),
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f s hs) (riemannianBallOf H.metric H.basepoint (4 * R')) ∧
            Set.InjOn (f s hs) (riemannianBallOf H.metric H.basepoint (4 * R')) ∧
            ∀ k'' : ℕ, k'' ≤ k' → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R'),
              ckErr_S45 H (postMetric F.observation s) s⁻¹ (f s hs) k'' p < ε') →
        ∃ (E : ℝ × H.Carrier → H.Carrier)
          (g₂ : H.Carrier → (postStage F.observation t₂).Carrier),
          (∃ U : TopologicalSpace.Opens H.Carrier,
            riemannianBallOf H.metric H.basepoint (2 * (βw t₂)⁻¹) ⊆ U ∧
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ g₂ U ∧
            IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => g₂ x) ∧
            ∀ k : ℕ, k ≤ ⌈(βw t₂)⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (βw t₂)⁻¹),
              ckErr_S45 H (postMetric F.observation t₂) t₂⁻¹ g₂ k p < βw t₂) ∧
          ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ E ∧
          (∀ μ, ContMDiff (𝓡 3) (𝓡 3) ∞ (fun p => E (μ, p)) ∧
            Function.Bijective (fun p => E (μ, p))) ∧
          (∀ p, E (0, p) = p) ∧
          (∀ μ p, p ∉ riemannianBallOf H.metric H.basepoint (4 * R) → E (μ, p) = p) ∧
          (∀ μ ∈ Icc (0 : ℝ) 1, ∀ p : H.Carrier,
            let v := mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => E (r, p)) μ
              ((NormedSpace.fromTangentSpace (𝕜 := ℝ) μ).symm (1 : ℝ));
            H.metric.inner (E (μ, p)) v v ≤ ε ^ 2) ∧
          (∀ μ ∈ Icc (0 : ℝ) 1, ∀ i : ℕ, i ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R),
            ckErr_S45 H H.metric 1 (fun x => E (μ, x)) i p ≤ ε) ∧
          (∀ (h1 : t₂ ∈ Icc t t₂), ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R), f t₂ h1 (E (1, p)) = g₂ p) ∧
          (∀ s (hs : s ∈ Icc t t₂) (μ : ℝ), ∀ y ∈ riemannianBallOf H.metric H.basepoint (a), ∃ r : ℝ, 0 < r ∧
            curvatureRadius (scaleMetric s⁻¹ (inv_pos.mpr (lt_of_lt_of_le ht hs.1))
              (postMetric F.observation s)) (f s hs (E (μ, y))) = ENNReal.ofReal r ∧
            ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric s⁻¹
              (inv_pos.mpr (lt_of_lt_of_le ht hs.1)) (postMetric F.observation s))
              (f s hs (E (μ, y))) r)) :
    ∃ β : ℝ → ℝ, (∀ t, 0 < β t) ∧ Filter.Tendsto β Filter.atTop (nhds 0) ∧
      (∃ I : ℕ, ∀ i : ℕ, I ≤ i →
        ∃ U : TopologicalSpace.Opens H.Carrier,
          riemannianBallOf H.metric H.basepoint (2 * (β (S.slices i).time)⁻¹) ⊆ U ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ (sliceApprox_O32 S H Φ i) U ∧
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => sliceApprox_O32 S H Φ i x) ∧
          ∀ k : ℕ, k ≤ ⌈(β (S.slices i).time)⁻¹⌉₊ →
            ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (β (S.slices i).time)⁻¹),
            ckErr_S45 H (postMetric F.observation (S.slices i).time) (S.slices i).time⁻¹
              (sliceApprox_O32 S H Φ i) k p < β (S.slices i).time) ∧
      ∀ (ε R : ℝ) (k : ℕ), 0 < ε → 0 < R → ∃ (ε' R' : ℝ) (k' : ℕ), 0 < ε' ∧ 0 < R' ∧
        ε' ≤ ε ∧ R ≤ R' ∧ k ≤ k' ∧ ∃ Te : ℝ,
        ∀ (t t₂ : ℝ) (ht : 0 < t), Te ≤ t → t₂ = 2 * t →
        ∀ g₁ : H.Carrier → (postStage F.observation t).Carrier,
        (∃ U : TopologicalSpace.Opens H.Carrier,
          riemannianBallOf H.metric H.basepoint (2 * (β t)⁻¹) ⊆ U ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ g₁ U ∧
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => g₁ x) ∧
          ∀ k : ℕ, k ≤ ⌈(β t)⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (β t)⁻¹),
            ckErr_S45 H (postMetric F.observation t) t⁻¹ g₁ k p < β t) →
        ∀ f : (s : ℝ) → s ∈ Icc t t₂ → H.Carrier → (postStage F.observation s).Carrier,
          (∀ (h0 : t ∈ Icc t t₂), ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R'), f t h0 p = g₁ p) →
          (∀ s (hs : s ∈ Icc t t₂),
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f s hs) (riemannianBallOf H.metric H.basepoint (4 * R')) ∧
            Set.InjOn (f s hs) (riemannianBallOf H.metric H.basepoint (4 * R')) ∧
            ∀ k'' : ℕ, k'' ≤ k' → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R'),
              ckErr_S45 H (postMetric F.observation s) s⁻¹ (f s hs) k'' p < ε') →
        ∃ (E : ℝ × H.Carrier → H.Carrier)
          (g₂ : H.Carrier → (postStage F.observation t₂).Carrier),
          (∃ U : TopologicalSpace.Opens H.Carrier,
            riemannianBallOf H.metric H.basepoint (2 * (β t₂)⁻¹) ⊆ U ∧
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ g₂ U ∧
            IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => g₂ x) ∧
            ∀ k : ℕ, k ≤ ⌈(β t₂)⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (β t₂)⁻¹),
              ckErr_S45 H (postMetric F.observation t₂) t₂⁻¹ g₂ k p < β t₂) ∧
          ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ E ∧
          (∀ μ, ContMDiff (𝓡 3) (𝓡 3) ∞ (fun p => E (μ, p)) ∧
            Function.Bijective (fun p => E (μ, p))) ∧
          (∀ p, E (0, p) = p) ∧
          (∀ μ p, p ∉ riemannianBallOf H.metric H.basepoint (4 * R) → E (μ, p) = p) ∧
          (∀ μ ∈ Icc (0 : ℝ) 1, ∀ p : H.Carrier,
            let v := mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => E (r, p)) μ
              ((NormedSpace.fromTangentSpace (𝕜 := ℝ) μ).symm (1 : ℝ));
            H.metric.inner (E (μ, p)) v v ≤ ε ^ 2) ∧
          (∀ μ ∈ Icc (0 : ℝ) 1, ∀ i : ℕ, i ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R),
            ckErr_S45 H H.metric 1 (fun x => E (μ, x)) i p ≤ ε) ∧
          (∀ (h1 : t₂ ∈ Icc t t₂), ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R), f t₂ h1 (E (1, p)) = g₂ p) ∧
          (∀ s (hs : s ∈ Icc t t₂) (μ : ℝ), ∀ y ∈ riemannianBallOf H.metric H.basepoint (a), ∃ r : ℝ, 0 < r ∧
            curvatureRadius (scaleMetric s⁻¹ (inv_pos.mpr (lt_of_lt_of_le ht hs.1))
              (postMetric F.observation s)) (f s hs (E (μ, y))) = ENNReal.ofReal r ∧
            ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric s⁻¹
              (inv_pos.mpr (lt_of_lt_of_le ht hs.1)) (postMetric F.observation s))
              (f s hs (E (μ, y))) r) := by
  classical
  obtain ⟨βw, hβw, hβw0, hstep⟩ := hstepW
  choose I hI using fun n : ℕ => hconvS (1 / ((n : ℝ) + 1)) (2 * (1 / ((n : ℝ) + 1))⁻¹)
    ⌈(1 / ((n : ℝ) + 1))⁻¹⌉₊ (by positivity) (by positivity)
  let J : ℕ → ℕ := fun n => I n + n
  let nj : ℕ → ℕ := fun j => Nat.findGreatest (fun n => J n ≤ j) j
  have hnj : Filter.Tendsto nj Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop.2 fun n => Filter.eventually_atTop.2
      ⟨J n, fun j hj => Nat.le_findGreatest ((Nat.le_add_left n (I n)).trans hj) hj⟩
  let aa : ℕ → ℝ := fun j => 1 / ((nj j : ℝ) + 1)
  have haa : ∀ j, 0 < aa j := fun j => by positivity
  have haa1 : ∀ j, aa j ≤ 1 := fun j => by
    have : (1 : ℝ) ≤ (nj j : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) (nj j); linarith
    exact (div_le_one (by positivity)).2 this
  have haa0 : Filter.Tendsto aa Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hnj
  obtain ⟨b, hb, hb0, hab⟩ := exists_envelope_O32 (fun j => (S.slices j).time)
    aa haa haa1 haa0
  refine ⟨fun t => max (βw t) (b t), fun t => lt_max_of_lt_left (hβw t), ?_, ⟨J 0, fun i hi => ?_⟩,
    fun ε R k hε hR => ?_⟩
  · simpa using hβw0.max hb0
  · have hJ : J (nj i) ≤ i := Nat.findGreatest_spec (P := fun n => J n ≤ i) (Nat.zero_le i) hi
    have hIi : I (nj i) ≤ i := (Nat.le_add_right _ _).trans hJ
    exact good_mono_O32 F H (S.slices i).time (sliceApprox_O32 S H Φ i) (haa i)
      ((hab i).trans (le_max_right _ _)) (hI (nj i) i hIi)
  · obtain ⟨ε', R', k', hε', hR', hle, hRle, hkle, Te, hTe⟩ := hstep ε R k hε hR
    refine ⟨ε', R', k', hε', hR', hle, hRle, hkle, Te,
      fun t t₂ ht hT ht₂ _ _ f _ hf => ?_⟩
    obtain ⟨E, g₂, hg₂, hrest⟩ := hTe t t₂ ht hT ht₂ f hf
    exact ⟨E, g₂, good_mono_O32 F H t₂ g₂ (hβw t₂) (le_max_left _ _) hg₂, hrest⟩

end GC.LongTime.Ch12
