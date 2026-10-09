import DifferentialGeometry.Geometry.Collapse.FixtureC2.SphereLoopRank
import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusCircleMultiplicity

/-!
# The net of slim centres of the sphere loop (S-FIXTURE-C2b, F2, G3 file 1)

On the loop of length `ℓ = N · sp` the `N` points `j_k = π_0 (z₀, k · sp)`, `0 ≤ k < N`, form a net:

* `loopCentres_disjoint_FXC2`: distinct centres are at distance `≥ sp` (the lifts of two centres at
  the nearest heights differ by the nonzero integer multiple `(k - k' - nN) sp`);
* `loopCentres_cover_FXC2`: every point is at distance `≤ sp / 2 + D₀` from a centre (nearest
  multiple of `sp` to the height, sphere distance `≤ D₀`);
* `loopCentres_ncard_le_FXC2`: at most `4·10⁶` centres lie within `2·10⁶ sp` of a point (injection
  `k ↦ k + n_k N` into an integer interval of length `4·10⁶`), below the model-volume ratio of
  `SlimFamily.multiplicity` (`slim_multiplicity_const_ge_FXC2`).
-/

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Metric
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open GC.MetricGeometry
open scoped Manifold ContDiff

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] sphereDimension cylinderDimension sphereCompact sphereConnected
  intrinsicMetric intrinsicUniform intrinsicEMetric intrinsicPseudoMetric intrinsicBundle
  cylinderRiemannian cylinderContinuous cylinderComplete
attribute [local instance] loopMS3_FXC2

namespace DifferentialGeometry.Geometry.Collapse

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- **The model-volume ratio of the slim multiplicity is at least `4·10⁶`.** -/
theorem slim_multiplicity_const_ge_FXC2 :
    (4000000 : ℝ) ≤ modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (3 * 2000000 + 2 / 3) /
      modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3) := by
  have hq : (0 : ℝ) ≤ 1 / 2000000 := by norm_num
  have hω := euclideanUnitBallVolume_pos 3
  have hlow := euclid_le_modelVolume_neg_sq_three_FXC1 hq (R := 3 * 2000000 + 2 / 3) (by norm_num)
  have hup := modelVolume_neg_sq_three_le hq (R := 1 / 3) (by norm_num)
  have hexp : Real.exp (2 * (1 / 2000000) * (1 / 3)) < 2 :=
    lt_of_le_of_lt (Real.exp_le_exp.mpr (by norm_num)) exp_half_lt_two
  have hpos : 0 < modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3) :=
    lt_of_lt_of_le (by positivity) (euclid_le_modelVolume_neg_sq_three_FXC1 hq (R := 1 / 3)
      (by norm_num))
  rw [le_div_iff₀ hpos]
  have h1 : modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3) ≤
      euclideanUnitBallVolume 3 * (1 / 3) ^ 3 * 2 :=
    hup.trans (mul_le_mul_of_nonneg_left hexp.le (by positivity))
  calc (4000000 : ℝ) * modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3)
      ≤ 4000000 * (euclideanUnitBallVolume 3 * (1 / 3) ^ 3 * 2) :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ ≤ euclideanUnitBallVolume 3 * (3 * 2000000 + 2 / 3) ^ 3 := by
        have : (4000000 : ℝ) * ((1 / 3) ^ 3 * 2) ≤ (3 * 2000000 + 2 / 3) ^ 3 := by norm_num
        nlinarith
    _ ≤ _ := hlow

/-- The point of the loop at the height `t` above the sphere point `z`. -/
def loopPt_FXC2 (ℓ : ℝ) (z : S2) (t : ℝ) : SphereLoop_FXC2 := loopCoverS_FXC2 ℓ 0 (z, t)

theorem loopCoverS_base_FXC2 (ℓ a : ℝ) (z : S2) :
    loopCoverS_FXC2 ℓ a (z, 0) = loopPt_FXC2 ℓ z a := by
  refine Prod.ext rfl ?_
  change (((0 + a) / ℓ : ℝ) : AddCircle (1 : ℝ)) = (((a + 0) / ℓ : ℝ) : AddCircle (1 : ℝ))
  rw [zero_add, add_zero]

/-- The centre number `k` of the net of spacing `sp` over `z₀`. -/
def loopCentre_FXC2 (ℓ : LoopLen_FXC2) (z₀ : S2) (sp : ℝ) (k : ℕ) : LoopC_FXC2 ℓ :=
  loopDiffeo_FXC2 ℓ (loopPt_FXC2 ℓ.1 z₀ (k * sp))

/-- The net of the `N` centres. -/
def loopCentres_FXC2 (ℓ : LoopLen_FXC2) (z₀ : S2) (sp : ℝ) (N : ℕ) : Set (LoopC_FXC2 ℓ) :=
  range fun k : Fin N => loopCentre_FXC2 ℓ z₀ sp k

theorem loopCentres_finite_FXC2 (ℓ : LoopLen_FXC2) (z₀ : S2) (sp : ℝ) (N : ℕ) :
    (loopCentres_FXC2 ℓ z₀ sp N).Finite :=
  finite_range _

theorem dist3_loopDist_FXC2 (ℓ : LoopLen_FXC2) (a b : LoopC_FXC2 ℓ) :
    dist a b = loopDist_FXC2 ℓ.1 ℓ.2 ((loopDiffeo_FXC2 ℓ).symm a) ((loopDiffeo_FXC2 ℓ).symm b) := by
  change (riemannianEDistOf (loopMetric3_FXC2 ℓ) a b).toReal = _
  rw [loopMetric3_edist_FXC2]
  rfl

theorem dist3_pt_pt_FXC2 (ℓ : LoopLen_FXC2) (p q : SphereLoop_FXC2) :
    dist (loopDiffeo_FXC2 ℓ p) (loopDiffeo_FXC2 ℓ q) = loopDist_FXC2 ℓ.1 ℓ.2 p q := by
  rw [dist3_loopDist_FXC2, Diffeomorph.symm_apply_apply, Diffeomorph.symm_apply_apply]

/-- **Nearest lift**: the loop distance of two points at heights `t`, `s` is the cylinder
distance to the lift of the second point nearest to the first (`n = round ((t - s) / ℓ)`). -/
theorem loopDist_pt_pt_FXC2 {ℓ : ℝ} (hℓ : 0 < ℓ) (z z' : S2) (t s : ℝ) :
    |t - s - round ((t - s) / ℓ) * ℓ| ≤ ℓ / 2 ∧
      loopDist_FXC2 ℓ hℓ (loopPt_FXC2 ℓ z t) (loopPt_FXC2 ℓ z' s) =
        dist ((z, t) : sphereCylinder) (z', s + round ((t - s) / ℓ) * ℓ) := by
  have hr := abs_sub_round ((t - s) / ℓ)
  have hclose : |t - s - round ((t - s) / ℓ) * ℓ| ≤ ℓ / 2 := by
    have h1 : t - s - round ((t - s) / ℓ) * ℓ = ((t - s) / ℓ - round ((t - s) / ℓ)) * ℓ := by
      field_simp
    rw [h1, abs_mul, abs_of_pos hℓ]
    nlinarith
  refine ⟨hclose, ?_⟩
  have hcov : loopPt_FXC2 ℓ z' s = loopPt_FXC2 ℓ z' (s + round ((t - s) / ℓ) * ℓ) := by
    have := (loopCoverS_eq_iff_FXC2 (ℓ := ℓ) 0 hℓ (x := (z', s))
      (y := (z', s + round ((t - s) / ℓ) * ℓ))).mpr ⟨rfl, round ((t - s) / ℓ), rfl⟩
    exact this
  rw [hcov]
  exact loopDist_eq_cylS_of_close_FXC2 ℓ 0 hℓ (z, t) (z', s + round ((t - s) / ℓ) * ℓ)
    (by
      change |t - (s + round ((t - s) / ℓ) * ℓ)| ≤ ℓ / 2
      rw [abs_le] at hclose ⊢
      constructor <;> linarith [hclose.1, hclose.2])

section Net

variable (ℓ : LoopLen_FXC2) (z₀ : S2) {sp : ℝ} (hsp : 0 < sp) {N : ℕ} (hN : ℓ.1 = N * sp)

include hsp hN in
theorem loopCentres_far_FXC2 (k k' : Fin N) (hkk : k ≠ k') :
    sp ≤ dist (loopCentre_FXC2 ℓ z₀ sp k) (loopCentre_FXC2 ℓ z₀ sp k') := by
  have hN0 : 0 < N := by
    have := ℓ.2
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h] at hN
      simp at hN
      linarith
    · exact h
  unfold loopCentre_FXC2
  rw [dist3_pt_pt_FXC2]
  obtain ⟨-, hd⟩ := loopDist_pt_pt_FXC2 ℓ.2 z₀ z₀ ((k : ℕ) * sp) ((k' : ℕ) * sp)
  rw [hd, cyl_dist_line_FXC2]
  set n : ℤ := round ((((k : ℕ) : ℝ) * sp - ((k' : ℕ) : ℝ) * sp) / ℓ.1) with hn
  have hm : ((k : ℕ) : ℤ) - ((k' : ℕ) : ℤ) - n * N ≠ 0 := by
    intro h
    have h1 : (N : ℤ) ∣ ((k : ℕ) : ℤ) - ((k' : ℕ) : ℤ) :=
      ⟨n, by linarith⟩
    have h2 : |((k : ℕ) : ℤ) - ((k' : ℕ) : ℤ)| < N := by
      rw [abs_lt]
      have := k.2
      have := k'.2
      constructor <;> omega
    have h3 := Int.eq_zero_of_abs_lt_dvd h1 h2
    exact hkk (Fin.ext (by omega))
  have hm1 : (1 : ℝ) ≤ |((((k : ℕ) : ℤ) - ((k' : ℕ) : ℤ) - n * N : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hm
  have heq : ((k : ℕ) : ℝ) * sp - (((k' : ℕ) : ℝ) * sp + n * ℓ.1) =
      ((((k : ℕ) : ℤ) - ((k' : ℕ) : ℤ) - n * N : ℤ) : ℝ) * sp := by
    rw [hN]
    push_cast
    ring
  rw [heq, abs_mul, abs_of_pos hsp]
  nlinarith

include hN in
theorem loopNet_N_pos_FXC2 : 0 < N := by
  have := ℓ.2
  rcases Nat.eq_zero_or_pos N with h | h
  · rw [h] at hN
    simp at hN
    linarith
  · exact h

include hsp hN in
theorem loopCentres_cover_FXC2 {D0 : ℝ} (hD00 : 0 ≤ D0)
    (hD0 : ∀ s s' : S2, sphereDist_FXC2 s s' ≤ D0) (p : LoopC_FXC2 ℓ) :
    ∃ k : Fin N, dist p (loopCentre_FXC2 ℓ z₀ sp k) ≤ sp / 2 + D0 := by
  have hN0 : 0 < N := loopNet_N_pos_FXC2 ℓ hN
  obtain ⟨p0, rfl⟩ : ∃ p0, p = loopDiffeo_FXC2 ℓ p0 :=
    ⟨(loopDiffeo_FXC2 ℓ).symm p, by simp⟩
  obtain ⟨a, hbase⟩ := exists_shift_base_FXC2 ℓ.2 p0
  have hp0 : loopPt_FXC2 ℓ.1 p0.1 a = p0 := by
    rw [← loopCoverS_base_FXC2]
    exact hbase
  set k₀ : ℤ := round (a / sp) with hk₀
  have hk₀r : |a - k₀ * sp| ≤ sp / 2 := by
    have hr := abs_sub_round (a / sp)
    have h1 : a - k₀ * sp = (a / sp - round (a / sp)) * sp := by
      rw [hk₀]
      field_simp
    rw [h1, abs_mul, abs_of_pos hsp]
    nlinarith
  have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast hN0.ne'
  have hmod0 : 0 ≤ k₀ % N := Int.emod_nonneg k₀ hNz
  have hmodN : k₀ % N < N := Int.emod_lt_of_pos k₀ (by exact_mod_cast hN0)
  have hkk : (k₀ % N).toNat < N := by omega
  refine ⟨⟨(k₀ % N).toNat, hkk⟩, ?_⟩
  unfold loopCentre_FXC2
  rw [dist3_pt_pt_FXC2]
  have hcast : (((k₀ % N).toNat : ℕ) : ℤ) = k₀ % N := Int.toNat_of_nonneg hmod0
  have hfib : loopPt_FXC2 ℓ.1 z₀ (((k₀ % N).toNat : ℕ) * sp) = loopPt_FXC2 ℓ.1 z₀ (k₀ * sp) := by
    have h := (loopCoverS_eq_iff_FXC2 (ℓ := ℓ.1) 0 ℓ.2 (x := (z₀, (((k₀ % N).toNat : ℕ) : ℝ) * sp))
      (y := (z₀, (k₀ : ℝ) * sp))).mpr ⟨rfl, k₀ / N, ?_⟩
    · exact h
    · have h1 : ((k₀ : ℤ) : ℝ) = (((k₀ % N : ℤ)) : ℝ) + N * ((k₀ / N : ℤ) : ℝ) := by
        have h0 : k₀ = k₀ % N + N * (k₀ / N) := by rw [Int.emod_def]; ring
        exact_mod_cast h0
      have h2 : ((((k₀ % N).toNat : ℕ) : ℤ) : ℝ) = ((k₀ % N : ℤ) : ℝ) := by rw [hcast]
      have h3 : ((((k₀ % N).toNat : ℕ)) : ℝ) = ((k₀ % N : ℤ) : ℝ) := by exact_mod_cast h2
      change (k₀ : ℝ) * sp = (((k₀ % N).toNat : ℕ) : ℝ) * sp + ((k₀ / N : ℤ) : ℝ) * ℓ.1
      rw [hN, h3, h1]
      ring
  rw [hfib, ← hp0]
  refine le_trans (loopDist_le_cylS_FXC2 ℓ.1 0 ℓ.2 (p0.1, a) (z₀, k₀ * sp)) ?_
  have hsq := cyl_sq_dist_FXC2 ((p0.1, a) : sphereCylinder) (z₀, (k₀ : ℝ) * sp)
  have hsd := hD0 p0.1 z₀
  have hsd0 := sphereDist_nonneg_FXC2 p0.1 z₀
  refine (sq_le_sq₀ dist_nonneg (by positivity)).1 ?_
  rw [hsq]
  have h4 : (a - k₀ * sp) ^ 2 ≤ (sp / 2) ^ 2 := by
    have := sq_abs (a - k₀ * sp)
    nlinarith [abs_nonneg (a - k₀ * sp)]
  change (a - k₀ * sp) ^ 2 + sphereDist_FXC2 p0.1 z₀ ^ 2 ≤ (sp / 2 + D0) ^ 2
  nlinarith [mul_nonneg hsp.le hD00]

include hsp hN in
theorem loopCentres_ncard_le_FXC2 (x : LoopC_FXC2 ℓ) :
    ((loopCentres_FXC2 ℓ z₀ sp N ∩ {j | x ∈ ball j (2000000 * sp)}).ncard : ℝ) ≤ 4000000 := by
  have hN0 : 0 < N := loopNet_N_pos_FXC2 ℓ hN
  obtain ⟨x0, rfl⟩ : ∃ x0, x = loopDiffeo_FXC2 ℓ x0 :=
    ⟨(loopDiffeo_FXC2 ℓ).symm x, by simp⟩
  obtain ⟨a, hbase⟩ := exists_shift_base_FXC2 ℓ.2 x0
  have hx0 : loopPt_FXC2 ℓ.1 x0.1 a = x0 := by
    rw [← loopCoverS_base_FXC2]
    exact hbase
  let F : Fin N → ℤ := fun k => ((k : ℕ) : ℤ) + round ((a - ((k : ℕ) : ℝ) * sp) / ℓ.1) * N
  have hFinj : Function.Injective F := by
    intro k k' h
    have h1 : (N : ℤ) ∣ ((k : ℕ) : ℤ) - ((k' : ℕ) : ℤ) := by
      refine ⟨round ((a - ((k' : ℕ) : ℝ) * sp) / ℓ.1) - round ((a - ((k : ℕ) : ℝ) * sp) / ℓ.1),
        ?_⟩
      have : ((k : ℕ) : ℤ) + round ((a - ((k : ℕ) : ℝ) * sp) / ℓ.1) * N =
          ((k' : ℕ) : ℤ) + round ((a - ((k' : ℕ) : ℝ) * sp) / ℓ.1) * N := h
      linarith
    have h2 : |((k : ℕ) : ℤ) - ((k' : ℕ) : ℤ)| < N := by
      rw [abs_lt]
      have := k.2
      have := k'.2
      constructor <;> omega
    have h3 := Int.eq_zero_of_abs_lt_dvd h1 h2
    exact Fin.ext (by omega)
  let T : Finset ℤ := Finset.Icc (⌊a / sp⌋ - 1999999) (⌊a / sp⌋ + 2000000)
  let S' : Set (Fin N) :=
    {k | dist (loopDiffeo_FXC2 ℓ x0) (loopCentre_FXC2 ℓ z₀ sp k) < 2000000 * sp}
  have hsub : loopCentres_FXC2 ℓ z₀ sp N ∩ {j | loopDiffeo_FXC2 ℓ x0 ∈ ball j (2000000 * sp)} ⊆
      (fun k : Fin N => loopCentre_FXC2 ℓ z₀ sp k) '' S' := by
    rintro j ⟨⟨k, rfl⟩, hj⟩
    refine ⟨k, ?_, rfl⟩
    rw [mem_ofPred_eq, mem_ball] at hj
    change dist (loopDiffeo_FXC2 ℓ x0) (loopCentre_FXC2 ℓ z₀ sp k) < 2000000 * sp
    exact hj
  have h1 := Set.ncard_le_ncard hsub ((Set.toFinite S').image _)
  have h2 := Set.ncard_image_le (f := fun k : Fin N => loopCentre_FXC2 ℓ z₀ sp k)
    (Set.toFinite S')
  have hmaps : ∀ k ∈ S', F k ∈ (T : Set ℤ) := by
    intro k hk
    have hk' : dist (loopDiffeo_FXC2 ℓ x0) (loopCentre_FXC2 ℓ z₀ sp k) < 2000000 * sp := hk
    unfold loopCentre_FXC2 at hk'
    rw [dist3_pt_pt_FXC2, ← hx0] at hk'
    obtain ⟨-, hd⟩ := loopDist_pt_pt_FXC2 ℓ.2 x0.1 z₀ a (((k : ℕ) : ℝ) * sp)
    rw [hd] at hk'
    have hl := cyl_snd_le_dist_FXC2 ((x0.1, a) : sphereCylinder)
      (z₀, ((k : ℕ) : ℝ) * sp + round ((a - ((k : ℕ) : ℝ) * sp) / ℓ.1) * ℓ.1)
    have hl' : |a - (((k : ℕ) : ℝ) * sp + round ((a - ((k : ℕ) : ℝ) * sp) / ℓ.1) * ℓ.1)| <
        2000000 * sp := lt_of_le_of_lt hl hk'
    have hF : ((F k : ℤ) : ℝ) * sp =
        ((k : ℕ) : ℝ) * sp + round ((a - ((k : ℕ) : ℝ) * sp) / ℓ.1) * ℓ.1 := by
      change ((((k : ℕ) : ℤ) + round ((a - ((k : ℕ) : ℝ) * sp) / ℓ.1) * N : ℤ) : ℝ) * sp = _
      rw [hN]
      push_cast
      ring
    rw [← hF, abs_lt] at hl'
    have hlo : (a / sp - 2000000 : ℝ) < (F k : ℝ) := by
      have h : a / sp < (F k : ℝ) + 2000000 := by
        rw [div_lt_iff₀ hsp]
        linarith [hl'.2]
      linarith
    have hhi : (F k : ℝ) < a / sp + 2000000 := by
      have h : (F k : ℝ) * sp < (a / sp + 2000000) * sp := by
        rw [add_mul, div_mul_cancel₀ _ hsp.ne']
        linarith [hl'.1]
      exact lt_of_mul_lt_mul_right h hsp.le
    have hfl := Int.floor_le (a / sp)
    have hfl' := Int.lt_floor_add_one (a / sp)
    simp only [T, Finset.coe_Icc, Set.mem_Icc]
    have hz1 : (⌊a / sp⌋ - 2000000 : ℤ) < F k := by
      have : ((⌊a / sp⌋ - 2000000 : ℤ) : ℝ) < (F k : ℝ) := by
        push_cast
        linarith
      exact_mod_cast this
    have hz2 : (F k : ℤ) < ⌊a / sp⌋ + 2000001 := by
      have : (F k : ℝ) < ((⌊a / sp⌋ + 2000001 : ℤ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast this
    constructor <;> omega
  have h3 := Set.ncard_le_ncard_of_injOn F hmaps (hFinj.injOn) T.finite_toSet
  have h4 : (T : Set ℤ).ncard = 4000000 := by
    rw [Set.ncard_coe_finset, Int.card_Icc]
    omega
  have h5 : (loopCentres_FXC2 ℓ z₀ sp N ∩
      {j | loopDiffeo_FXC2 ℓ x0 ∈ ball j (2000000 * sp)}).ncard ≤ 4000000 := by omega
  exact_mod_cast h5

end Net

end DifferentialGeometry.Geometry.Collapse
