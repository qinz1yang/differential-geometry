import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KL70SubBinders_O38
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KcoreVolumeSmall_O38
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KcoreUnscaledVolume_O31
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84Pinch_O16
import DifferentialGeometry.Geometry.Curvature.RicciNonnegativeConvergence

/-!
# CH12-O45, group 1: the A1 sub-binder of KL70.2 (a') at sequence level (`[FROZEN] CH12-O45 G1`)

`hA1_O45`: the `hA1` binder of `hNoEscPos_of_ABC_O38`, verbatim, from `hStrong` (free neck
clause `NK`; instance `hStrong2`, NK := v2 neck clause).

* `ricci_lower_of_curvatureOperatorLowerBound_O45`: `Rm ≥ -K` (curvature operator) ⇒
  `Ric ≥ -(n K) g` (sectional curvature `≥ -K`, orthonormal trace).
* `slice_pinch_O45`: `hpinchS_O16` at the top of the slice history, read on `s.metric`.
* `A1_slice_O45`: one slice, normalized units (`λ = √R(y)`): the Ricci bound `-2 (Q₀ λ)²`, the
  centre volume `κ (h₀/λ)³` and the chain `w → x → p` of `ballVolume_small_of_centre_O38` give
  `vol B(p, ℓ/λ) ≥ v (ℓ/λ)³` for all `ℓ ∈ (0, 1]`, `v` independent of `λ`.
* `hA1_O45`: sequence layer.  The Ricci bound comes from pinching, `R ≤ C R(y)` (hbdd at
  `(N+4) h₀ < ρ`) and `Φ(s)/s` antitone: `Φ(R) ≤ Φ(C' R(y)) ≤ C' Φ(1) R(y)`; the centre `w`, its
  volume and `R(w) = 2 R(y)` from `exists_buffered_rcw_O31` + `unscaled_centre_volume_O31`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set Filter Topology
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

section RicciLower

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- Curvature operator `≥ -K` (`K ≥ 0`) gives `Ric ≥ -(n K) g`. -/
theorem ricci_lower_of_curvatureOperatorLowerBound_O45 (g : SmoothRiemannianMetric I M) (q : M)
    {K : ℝ} (hK : 0 ≤ K)
    (hRm : curvatureOperatorLowerBoundAt g q (metricAlgebraicCurvatureTensorAt g q) K)
    (v : TangentSpace I q) :
    -((Module.finrank ℝ E : ℝ) * K) * g.inner q v v ≤ ricciTensor g q v v := by
  classical
  have hsec (u w : TangentSpace I q) :
      -K * (g.inner q u u * g.inner q w w - g.inner q u w * g.inner q w u) ≤
        metricRm04StandardAt g q u w w u := by
    have h := hRm 1 (fun _ => 1) (fun _ => u) (fun _ => w)
    simp only [algebraicCurvatureOperatorQuadraticEval, algebraicCurvatureIdentityQuadraticEval,
      Fin.sum_univ_one, one_mul, metricAlgebraicCurvatureTensorAt_coe] at h
    simp only [metricRm04StandardAt]
    linarith
  obtain ⟨B, hB⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis g q
  rw [ricciTensor_eq_orthonormal_trace g q v v B hB]
  calc -((Module.finrank ℝ E : ℝ) * K) * g.inner q v v
        = ∑ _i : Fin (Module.finrank ℝ E), -K * g.inner q v v := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      rw [g.symm q _ (B i),
        ← DifferentialGeometry.CheegerGromovCompactness.metricRm04StandardAt_eq_inner_riemannOp]
      have h1 := hsec (B i) v
      have hBi : g.inner q (B i) (B i) = 1 := by rw [hB i i]; exact ite_eq_left rfl
      rw [hBi, g.symm q v (B i)] at h1
      nlinarith [mul_nonneg hK (sq_nonneg (g.inner q (B i) v))]

end RicciLower

section OneSlice

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [T2Space (TangentBundle ThreeModel M)]
  [SigmaCompactSpace M]

/-- **A1 at one slice, normalized units** (`λ = √R(y)`): `v = e^{-2Q₀h₀} c^{2(N+1)} κ h₀³/8`. -/
theorem A1_slice_O45 (g : SmoothRiemannianMetric ThreeModel M) (x w p : M)
    {Q0 h0 lam κ : ℝ} (hQ0 : 0 ≤ Q0) (hh0 : 0 < h0) (hh01 : h0 ≤ 1) (hlam : 0 < lam)
    (hκ : 0 ≤ κ) (N : ℕ)
    (hcpt : IsCompact (riemannianClosedBallOf g x ((N + 4) * (h0 / lam))))
    (hRic : ∀ z ∈ riemannianBallOf g x ((N + 4) * (h0 / lam)), ∀ v : TangentSpace ThreeModel z,
      -(2 * (Q0 * lam) ^ 2) * g.inner z v v ≤ ricciTensor (I := ThreeModel) g z v v)
    (hw : riemannianEDistOf g x w < ENNReal.ofReal ((N + 1) * (h0 / lam)))
    (hp : riemannianEDistOf g x p < ENNReal.ofReal ((N + 1) * (h0 / lam)))
    (hκ₀ : ENNReal.ofReal (κ * (h0 / lam) ^ 3) ≤
      riemannianVolumeMeasure ThreeModel M g (riemannianBallOf g w (h0 / lam)))
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) :
    ENNReal.ofReal (Real.exp (-(Q0 * 2 * h0)) * chainConst_O14 3 Q0 h0 ^ (2 * (N + 1)) * κ / 8 *
        h0 ^ 3 * (ℓ / lam) ^ 3) ≤
      riemannianVolumeMeasure ThreeModel M g (riemannianBallOf g p (ℓ / lam)) := by
  have h3 : Module.finrank ℝ ThreeSpace = 3 := finrank_euclideanSpace_fin
  have hhl : 0 < h0 / lam := div_pos hh0 hlam
  set c1 : ℝ := Real.exp (-(Q0 * 2 * h0)) * chainConst_O14 3 Q0 h0 ^ (2 * (N + 1)) * κ / 8
    with hc1
  have hc1n : 0 ≤ c1 := by
    have := chainConst_pos_O14 3 Q0 h0
    positivity
  have hRic' : ∀ z ∈ riemannianBallOf g x ((N + 4) * (h0 / lam)), ∀ v : TangentSpace ThreeModel z,
      -(((Module.finrank ℝ ThreeSpace - 1 : ℕ) : ℝ) * (Q0 * lam) ^ 2) * g.inner z v v ≤
        ricciTensor (I := ThreeModel) g z v v := by
    intro z hz v
    rw [h3]
    have := hRic z hz v
    norm_num
    linarith
  have key : ∀ ℓ' : ℝ, 0 < ℓ' → ℓ' ≤ h0 →
      ENNReal.ofReal (c1 * (ℓ' / lam) ^ 3) ≤
        riemannianVolumeMeasure ThreeModel M g (riemannianBallOf g p (ℓ' / lam)) := by
    intro ℓ' hℓ' hℓ'h
    have hs := ballVolume_small_of_centre_O38 g x (mul_nonneg hQ0 hlam.le) hhl N hcpt hRic' hw hp
      hκ₀ (div_pos hℓ' hlam) (div_le_div_of_nonneg_right hℓ'h hlam.le)
    refine le_trans (le_of_eq ?_) hs
    congr 1
    rw [h3]
    have hexp : Q0 * lam * (((3 - 1 : ℕ) : ℝ)) * (h0 / lam) = Q0 * 2 * h0 := by
      norm_num; field_simp
    have hcc : chainConst_O14 3 (Q0 * lam) (h0 / lam) = chainConst_O14 3 Q0 h0 := by
      unfold chainConst_O14
      congr 2
      field_simp
    rw [hexp, hcc, hc1]
    field_simp
    ring
  rcases le_or_gt ℓ h0 with hle | hlt
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) (key ℓ hℓ hle)
    have hh3 : h0 ^ 3 ≤ 1 := pow_le_one₀ hh0.le hh01
    have := pow_nonneg (div_pos hℓ hlam).le 3
    nlinarith [mul_nonneg hc1n this]
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) ((key h0 hh0 le_rfl).trans
      (MeasureTheory.measure_mono (riemannianBallOf_mono g p
        (div_le_div_of_nonneg_right hlt.le hlam.le))))
    have hl3 : ℓ ^ 3 ≤ 1 := pow_le_one₀ hℓ.le hℓ1
    have e1 : c1 * h0 ^ 3 * (ℓ / lam) ^ 3 = c1 * (h0 / lam) ^ 3 * ℓ ^ 3 := by
      field_simp
    rw [e1]
    have := pow_nonneg hhl.le 3
    nlinarith [mul_nonneg hc1n this]

end OneSlice

section Slice

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- `hpinchS_O16` read on the slice metric. -/
theorem slice_pinch_O45 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) :
    ∃ Phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction Phi ∧
      ∀ (s : RegularSlice F.observation) (x : s.stage.Carrier),
        curvatureOperatorLowerBoundAt s.metric x (metricAlgebraicCurvatureTensorAt s.metric x)
          (Phi (metricScalarAt s.metric x)) := by
  obtain ⟨Phi, hPhi, hpin⟩ := hpinchS_O16 Hp
  refine ⟨Phi, hPhi, fun s => ?_⟩
  have key : ∀ (j : Fin (s.history.eventCount + 1)),
      s.history.activeStage (sliceTop_S8 s) = j → ∀ x : (s.history.stage j).Carrier,
      curvatureOperatorLowerBoundAt (s.history.stageMetric j s.time) x
        (metricAlgebraicCurvatureTensorAt (s.history.stageMetric j s.time) x)
        (Phi (metricScalarAt (s.history.stageMetric j s.time) x)) := by
    intro j hj
    subst hj
    exact hpin s (sliceTop_S8 s) le_rfl
  exact key (Fin.last _) s.history.activeStage_at_horizon

/-- **hA1 of KL70.2 (a')** (`[FROZEN] CH12-O45 G1`): the `hA1` binder of
`hNoEscPos_of_ABC_O38`, verbatim, from `hStrong` with a free neck clause `NK`. -/
theorem hA1_O45 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (NK : ∀ (s : RegularSlice F.observation) (x : s.stage.Carrier),
      (Hp.parameters.neckRadius s.time ^ 2)⁻¹ < metricScalarAt s.metric x →
      SpatialCanonicalWitness s.metric Hp.epsilon Hp.C1 Hp.C2 x → Prop)
    (hStrong : ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ x : s.stage.Carrier,
      ∀ hR : (Hp.parameters.neckRadius s.time ^ 2)⁻¹ < metricScalarAt s.metric x,
      ∃ W : SpatialCanonicalWitness s.metric Hp.epsilon Hp.C1 Hp.C2 x,
        W.capTubeHasNeckChart Hp.epsilon ∧ NK s x hR W) :
    ∀ A : ℝ, 0 < A → ∀ (s : ℕ → RegularSlice F.observation)
      (y z : ∀ n, (s n).stage.Carrier) (ρ : ℝ),
      Tendsto (fun n => (s n).time) atTop atTop →
      (∀ n, (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ ≤
        metricScalarAt (s n).metric (y n)) →
      Tendsto (fun n => metricScalarAt (s n).metric (y n)) atTop atTop →
      0 ≤ ρ → ρ ≤ A →
      Tendsto (fun n => metricScalarAt (s n).metric (z n) /
        metricScalarAt (s n).metric (y n)) atTop atTop →
      (∀ r : ℝ, r < ρ → ∃ C : ℝ, ∀ᶠ n in atTop,
        ∀ w ∈ riemannianBallOf (s n).metric (y n)
          (r / Real.sqrt (metricScalarAt (s n).metric (y n))),
          metricScalarAt (s n).metric w ≤ C * metricScalarAt (s n).metric (y n)) →
      (∀ r : ℝ, ρ < r → ∀ᶠ n in atTop, z n ∈ riemannianBallOf (s n).metric (y n)
        (r / Real.sqrt (metricScalarAt (s n).metric (y n)))) →
      1 / 4 ≤ ρ →
      (∀ r : ℝ, 0 < r → r < ρ - (Real.sqrt 2)⁻¹ / 4 → ∃ v : ℝ, 0 < v ∧
        ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ min 1 (ρ - (Real.sqrt 2)⁻¹ / 4 - r) → ∀ᶠ n in atTop,
          ∀ p ∈ riemannianBallOf (s n).metric (y n) (r / Real.sqrt (metricScalarAt (s n).metric (y n))),
            ENNReal.ofReal (v * (ℓ / Real.sqrt (metricScalarAt (s n).metric (y n))) ^ 3) ≤
              riemannianVolumeMeasure ThreeModel (s n).stage.Carrier (s n).metric
                (riemannianBallOf (s n).metric p (ℓ / Real.sqrt (metricScalarAt (s n).metric (y n))))) := by
  obtain ⟨κ, hκ, hbuf⟩ := exists_buffered_rcw_O31 Hp NK hStrong
  obtain ⟨Phi, hPhi, hpin⟩ := slice_pinch_O45 Hp
  intro A _ s y z ρ htime hneck hRy _ _ hratio hbdd hesc hρ r hr hrs
  have hsq2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs2n := Real.sqrt_nonneg 2
  have hs2a : 1 < Real.sqrt 2 := by nlinarith
  have hs2b : Real.sqrt 2 ≤ 2 := by nlinarith
  have hs2 : (Real.sqrt 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hs2a
  have hs2p : 0 < (Real.sqrt 2)⁻¹ / 4 := by positivity
  have hβpos : 0 < (Real.sqrt Hp.C2)⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.mpr (lt_of_lt_of_le one_pos Hp.C2_ge_one))
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = max r (ρ - 19 / 50) := ⟨_, rfl⟩
  have hmr : r ≤ m := hm ▸ le_max_left _ _
  have hm19 : ρ - 19 / 50 ≤ m := hm ▸ le_max_right _ _
  have hmpos : 0 < m := lt_of_lt_of_le hr hmr
  have hmrs : m < ρ - (Real.sqrt 2)⁻¹ / 4 := hm ▸ max_lt hrs (by linarith)
  obtain ⟨h0, hh0⟩ : ∃ h0 : ℝ,
      h0 = min (min (1 / 4) ((Real.sqrt Hp.C2)⁻¹ / 2)) ((ρ - (Real.sqrt 2)⁻¹ / 4 - m) / 5) :=
    ⟨_, rfl⟩
  have hh0pos : 0 < h0 := hh0 ▸ lt_min (lt_min (by norm_num) (by positivity)) (by linarith)
  have hh01 : h0 ≤ 1 := hh0 ▸ (min_le_left _ _).trans ((min_le_left _ _).trans (by norm_num))
  have hh0β : h0 ≤ (Real.sqrt Hp.C2)⁻¹ / 2 := hh0 ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hh05 : 5 * h0 ≤ ρ - (Real.sqrt 2)⁻¹ / 4 - m := by
    have := min_le_right (min (1 / 4) ((Real.sqrt Hp.C2)⁻¹ / 2))
      ((ρ - (Real.sqrt 2)⁻¹ / 4 - m) / 5)
    rw [← hh0] at this; linarith
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌈m / h0⌉₊ := ⟨_, rfl⟩
  have hN1 : m ≤ N * h0 := by
    have := Nat.le_ceil (m / h0); rw [← hN, div_le_iff₀ hh0pos] at this; exact this
  have hN2 : (N : ℝ) * h0 < m + h0 := by
    have h1 := Nat.ceil_lt_add_one (div_pos hmpos hh0pos).le
    rw [← hN] at h1
    have h2 := mul_lt_mul_of_pos_right h1 hh0pos
    rw [add_mul, div_mul_cancel₀ _ hh0pos.ne', one_mul] at h2
    exact h2
  have hr'ρ : ((N : ℝ) + 4) * h0 < ρ := by linarith only [hN2, hh05, hs2p]
  obtain ⟨C, hC⟩ := hbdd (((N : ℝ) + 4) * h0) hr'ρ
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, C' = max C 1 := ⟨_, rfl⟩
  have hC'1 : 1 ≤ C' := hC' ▸ le_max_right _ _
  have hCC' : C ≤ C' := hC' ▸ le_max_left _ _
  have hPhi1 := hPhi.pos 1
  obtain ⟨Q0, hQ0⟩ : ∃ Q0 : ℝ, Q0 = Real.sqrt (3 * C' * Phi 1 / 2) := ⟨_, rfl⟩
  have hQ0n : 0 ≤ Q0 := hQ0 ▸ Real.sqrt_nonneg _
  have hQ0sq : 2 * Q0 ^ 2 = 3 * C' * Phi 1 := by
    rw [hQ0, Real.sq_sqrt (by positivity)]; ring
  refine ⟨Real.exp (-(Q0 * 2 * h0)) * chainConst_O14 3 Q0 h0 ^ (2 * (N + 1)) * κ / 8 * h0 ^ 3,
    by have := chainConst_pos_O14 3 Q0 h0; positivity, fun ℓ hℓ hℓle => ?_⟩
  have hℓ1 : ℓ ≤ 1 := hℓle.trans (min_le_left _ _)
  filter_upwards [hbuf s y z ρ htime hneck hRy hratio hesc, hC,
    hRy.eventually (eventually_ge_atTop 1)] with n hn hCn hRy1
  obtain ⟨w, hwB, -, hRw, -, W, -, -, hvolW, -⟩ := hn
  intro p hp
  have hRypos : 0 < metricScalarAt (s n).metric (y n) := lt_of_lt_of_le one_pos hRy1
  have hlam : 0 < Real.sqrt (metricScalarAt (s n).metric (y n)) := Real.sqrt_pos.mpr hRypos
  refine A1_slice_O45 (s n).metric (y n) w p (Q0 := Q0) (h0 := h0)
    (lam := Real.sqrt (metricScalarAt (s n).metric (y n))) (κ := κ) hQ0n hh0pos hh01 hlam
    hκ.le N (isCompact_univ.of_isClosed_subset (isClosed_riemannianClosedBallOf_O14 _ _ _)
      (subset_univ _)) ?_ ?_ ?_ ?_ hℓ hℓ1
  · intro x hx v
    have hx' : x ∈ riemannianBallOf (s n).metric (y n)
        (((N : ℝ) + 4) * h0 / Real.sqrt (metricScalarAt (s n).metric (y n))) := by
      rw [mul_div_assoc]; exact hx
    have hRx := hCn x hx'
    have hric := ricci_lower_of_curvatureOperatorLowerBound_O45 (s n).metric x
      (hPhi.pos _).le (hpin (s n) x) v
    rw [finrank_euclideanSpace_fin] at hric
    have hinner : 0 ≤ (s n).metric.inner x v v := by
      rcases eq_or_ne v 0 with rfl | hv
      · simp
      · exact ((s n).metric.pos x v hv).le
    have hCR : C * metricScalarAt (s n).metric (y n) ≤ C' * metricScalarAt (s n).metric (y n) :=
      mul_le_mul_of_nonneg_right hCC' hRypos.le
    have hmono : Phi (metricScalarAt (s n).metric x) ≤
        Phi (C' * metricScalarAt (s n).metric (y n)) := hPhi.mono (hRx.trans hCR)
    have h1CR : 1 ≤ C' * metricScalarAt (s n).metric (y n) := one_le_mul_of_one_le_of_one_le hC'1 hRy1
    have hanti : Phi (C' * metricScalarAt (s n).metric (y n)) /
        (C' * metricScalarAt (s n).metric (y n)) ≤ Phi 1 / 1 :=
      hPhi.quotientAntitoneOn (mem_Ioi.mpr one_pos) (mem_Ioi.mpr (by linarith)) h1CR
    rw [div_one, div_le_iff₀ (by linarith)] at hanti
    have hsq : (Q0 * Real.sqrt (metricScalarAt (s n).metric (y n))) ^ 2 =
        Q0 ^ 2 * metricScalarAt (s n).metric (y n) := by
      rw [mul_pow, Real.sq_sqrt hRypos.le]
    have hQR : 2 * Q0 ^ 2 * metricScalarAt (s n).metric (y n) =
        3 * C' * Phi 1 * metricScalarAt (s n).metric (y n) := by rw [hQ0sq]
    have h3 : 3 * Phi (metricScalarAt (s n).metric x) ≤
        2 * (Q0 * Real.sqrt (metricScalarAt (s n).metric (y n))) ^ 2 := by
      rw [hsq]; linarith only [hmono, hanti, hQR]
    have h4 := mul_le_mul_of_nonneg_right h3 hinner
    push_cast at hric
    linarith only [hric, h4]
  · have hwB' : riemannianEDistOf (s n).metric (y n) w < ENNReal.ofReal
        ((ρ - 19 / 50) / Real.sqrt (metricScalarAt (s n).metric (y n))) := hwB
    refine lt_of_lt_of_le hwB' (ENNReal.ofReal_le_ofReal ?_)
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith only [hm19, hN1, hh0pos]) hlam.le
  · have hp' : riemannianEDistOf (s n).metric (y n) p < ENNReal.ofReal
        (r / Real.sqrt (metricScalarAt (s n).metric (y n))) := hp
    refine lt_of_lt_of_le hp' (ENNReal.ofReal_le_ofReal ?_)
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith only [hmr, hN1, hh0pos]) hlam.le
  · refine unscaled_centre_volume_O31 (s n).metric w W.Q_pos hvolW
      (h0 / Real.sqrt (metricScalarAt (s n).metric (y n))) (div_pos hh0pos hlam) ?_
    rw [hRw, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have e : h0 / Real.sqrt (metricScalarAt (s n).metric (y n)) *
        (Real.sqrt 2 * Real.sqrt (metricScalarAt (s n).metric (y n))) = Real.sqrt 2 * h0 := by
      field_simp
    rw [e]
    linarith only [mul_le_mul_of_nonneg_right hs2b hh0pos.le, hh0β]

end Slice

end GC.LongTime.Ch12
