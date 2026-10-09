import DifferentialGeometry.Geometry.Collapse.FixtureC1.LatticeTorusPlaneChart

/-!
# The centre net of the circle family of the flat torus (S-FIXTURE-C1, F1, file 2)

For a torus whose two planar periods are `N R` (`N ≥ 1` a natural number), the circle centres are
the images `node(a, b) = π(R a, R b, 0)`, `0 ≤ a, b < N`: an `R`-spaced planar net (review 75,
D75-11: an `R/2` lattice does not give `R/3`-disjoint balls; an `R`-spaced one has covering radius
`< R`).

* `torCentres_FXC1`: the finite centre set;
* `torCentres_cover_FXC1`: every point is within `R` of a centre;
* `torCentres_sep_FXC1`: distinct centres are at least `R` apart (`le_edist_torPi_FXC1`);
(The count of centres within `200 R` of a point, `≤ 401²`, is NOT part of this file: see the
handover in `build-logs/resume/state-S-FIXTURE-C1.md`.)
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] torMS_FXC1

/-- The point of `ℝ³` with planar part `R (a, b)` and third coordinate `0`. -/
def torNode_FXC1 (R : ℝ) (a b : ℤ) : E3 :=
  WithLp.toLp 2 fun i : Fin 3 => if i = 0 then R * a else if i = 1 then R * b else 0

@[simp] theorem torNode_zero_FXC1 (R : ℝ) (a b : ℤ) : torNode_FXC1 R a b 0 = R * a := by
  simp [torNode_FXC1]

@[simp] theorem torNode_one_FXC1 (R : ℝ) (a b : ℤ) : torNode_FXC1 R a b 1 = R * b := by
  simp [torNode_FXC1]

@[simp] theorem torNode_two_FXC1 (R : ℝ) (a b : ℤ) : torNode_FXC1 R a b 2 = 0 := by
  simp [torNode_FXC1]

/-- The lattice element with integer coordinates `(k₀, k₁, 0)`. -/
def planarShift_FXC1 (Λ : TorusPeriods_FXC1) (k₀ k₁ : ℤ) : TorusGroup_FXC1 Λ :=
  TorusGroup_FXC1.ofInts Λ fun i : Fin 3 => if i = 0 then k₀ else if i = 1 then k₁ else 0

theorem latticeVec_planarShift_zero_FXC1 (Λ : TorusPeriods_FXC1) (k₀ k₁ : ℤ) :
    latticeVec_FXC1 Λ (planarShift_FXC1 Λ k₀ k₁) 0 = k₀ * Λ.L 0 := by
  rw [latticeVec_apply_FXC1]
  simp [planarShift_FXC1, toInts_ofInts_FXC1]

theorem latticeVec_planarShift_one_FXC1 (Λ : TorusPeriods_FXC1) (k₀ k₁ : ℤ) :
    latticeVec_FXC1 Λ (planarShift_FXC1 Λ k₀ k₁) 1 = k₁ * Λ.L 1 := by
  rw [latticeVec_apply_FXC1]
  simp [planarShift_FXC1, toInts_ofInts_FXC1]

theorem latticeVec_planarShift_two_FXC1 (Λ : TorusPeriods_FXC1) (k₀ k₁ : ℤ) :
    latticeVec_FXC1 Λ (planarShift_FXC1 Λ k₀ k₁) 2 = 0 := by
  rw [latticeVec_apply_FXC1]
  simp [planarShift_FXC1, toInts_ofInts_FXC1]

section Net

variable (Λ : TorusPeriods_FXC1) {R : ℝ} (N : ℕ)
  (hL0 : Λ.L 0 = N * R) (hL1 : Λ.L 1 = N * R)

include hL0 hL1 in
/-- Planar period shifts of a node do not change its image. -/
theorem torPi_node_shift_FXC1 (a b k₀ k₁ : ℤ) :
    torPi_FXC1 Λ (torNode_FXC1 R (a + N * k₀) (b + N * k₁)) =
      torPi_FXC1 Λ (torNode_FXC1 R a b) := by
  refine (torPi_eq_iff_FXC1.mpr ⟨planarShift_FXC1 Λ k₀ k₁, ?_⟩).symm
  ext i
  fin_cases i
  · change _ = torNode_FXC1 R a b 0 + latticeVec_FXC1 Λ (planarShift_FXC1 Λ k₀ k₁) 0
    rw [latticeVec_planarShift_zero_FXC1, hL0]
    simp
    ring
  · change _ = torNode_FXC1 R a b 1 + latticeVec_FXC1 Λ (planarShift_FXC1 Λ k₀ k₁) 1
    rw [latticeVec_planarShift_one_FXC1, hL1]
    simp
    ring
  · change _ = torNode_FXC1 R a b 2 + latticeVec_FXC1 Λ (planarShift_FXC1 Λ k₀ k₁) 2
    rw [latticeVec_planarShift_two_FXC1]
    simp

/-- The finite set of circle centres. -/
def torCentres_FXC1 (R : ℝ) (N : ℕ) : Set (Tor_FXC1 Λ) :=
  (fun m : ℤ × ℤ => torPi_FXC1 Λ (torNode_FXC1 R m.1 m.2)) '' (Ico (0 : ℤ) N ×ˢ Ico (0 : ℤ) N)

theorem torCentres_finite_FXC1 (R : ℝ) : (torCentres_FXC1 Λ R N).Finite :=
  ((Set.finite_Ico _ _).prod (Set.finite_Ico _ _)).image _

include hL0 hL1 in
/-- **Covering radius**: every point is within `R` of a centre (`L₂ ≤ R/2`). -/
theorem torCentres_cover_FXC1 (hR : 0 < R) (hN : 0 < N) (hL2 : Λ.L 2 ≤ R / 2)
    (p : Tor_FXC1 Λ) : ∃ j ∈ torCentres_FXC1 Λ R N, dist p j ≤ R := by
  obtain ⟨y, rfl⟩ := torPi_surjective_FXC1 Λ p
  let z₀ : ℤ := round (y 0 / R)
  let z₁ : ℤ := round (y 1 / R)
  have hz₀ : |y 0 / R - z₀| ≤ 1 / 2 := abs_sub_round _
  have hz₁ : |y 1 / R - z₁| ≤ 1 / 2 := abs_sub_round _
  have hNZ : (0 : ℤ) < N := by exact_mod_cast hN
  refine ⟨torPi_FXC1 Λ (torNode_FXC1 R (z₀ % N) (z₁ % N)), ⟨(z₀ % N, z₁ % N), ⟨?_, ?_⟩, rfl⟩, ?_⟩
  · exact ⟨Int.emod_nonneg _ hNZ.ne', Int.emod_lt_of_pos _ hNZ⟩
  · exact ⟨Int.emod_nonneg _ hNZ.ne', Int.emod_lt_of_pos _ hNZ⟩
  · have hshift := torPi_node_shift_FXC1 Λ N hL0 hL1 (z₀ % N) (z₁ % N) (z₀ / N) (z₁ / N)
    rw [Int.emod_add_mul_ediv, Int.emod_add_mul_ediv] at hshift
    rw [← hshift]
    refine (dist_torPi_le_FXC1 Λ y (torNode_FXC1 R z₀ z₁)).trans ?_
    have e0 : (y - torNode_FXC1 R z₀ z₁) 0 = R * (y 0 / R - z₀) := by
      simp only [PiLp.sub_apply, torNode_zero_FXC1]
      field_simp
    have e1 : (y - torNode_FXC1 R z₀ z₁) 1 = R * (y 1 / R - z₁) := by
      simp only [PiLp.sub_apply, torNode_one_FXC1]
      field_simp
    have h0 : |(y - torNode_FXC1 R z₀ z₁) 0| ≤ R / 2 := by
      rw [e0, abs_mul, abs_of_pos hR]; nlinarith
    have h1 : |(y - torNode_FXC1 R z₀ z₁) 1| ≤ R / 2 := by
      rw [e1, abs_mul, abs_of_pos hR]; nlinarith
    have hn : ‖planeL_FXC1 (y - torNode_FXC1 R z₀ z₁)‖ ≤ 3 * R / 4 := by
      refine (abs_le_of_sq_le_sq' ?_ (by positivity)).2
      rw [EuclideanSpace.norm_sq_eq]
      simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, planeL_apply_FXC1]
      have a0 := sq_le_sq' (abs_le.mp h0).1 (abs_le.mp h0).2
      have a1 := sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
      change (y - torNode_FXC1 R z₀ z₁) 0 ^ 2 + (y - torNode_FXC1 R z₀ z₁) 1 ^ 2 ≤ _
      nlinarith
    linarith

include hL0 hL1 in
/-- **Separation**: distinct centres are at least `R` apart. -/
theorem torCentres_sep_FXC1 (hR : 0 < R) {a b a' b' : ℤ} (ha : a ∈ Ico (0 : ℤ) N)
    (hb : b ∈ Ico (0 : ℤ) N) (ha' : a' ∈ Ico (0 : ℤ) N) (hb' : b' ∈ Ico (0 : ℤ) N)
    (hne : ¬ (a = a' ∧ b = b')) :
    R ≤ dist (torPi_FXC1 Λ (torNode_FXC1 R a b)) (torPi_FXC1 Λ (torNode_FXC1 R a' b')) := by
  refine le_dist_of_ofReal_le_FXC1 Λ _ _ R (le_edist_torPi_FXC1 Λ _ _ R fun n => ?_)
  have hc0 : (torNode_FXC1 R a b - (torNode_FXC1 R a' b' + latticeVec_FXC1 Λ n)) 0 =
      R * ((a - a' - N * n.toInts 0 : ℤ) : ℝ) := by
    simp only [PiLp.sub_apply, PiLp.add_apply, torNode_zero_FXC1, latticeVec_apply_FXC1, hL0]
    push_cast
    ring
  have hc1 : (torNode_FXC1 R a b - (torNode_FXC1 R a' b' + latticeVec_FXC1 Λ n)) 1 =
      R * ((b - b' - N * n.toInts 1 : ℤ) : ℝ) := by
    simp only [PiLp.sub_apply, PiLp.add_apply, torNode_one_FXC1, latticeVec_apply_FXC1, hL1]
    push_cast
    ring
  have hbig : ∀ (i : Fin 3) (k : ℤ), k ≠ 0 →
      (torNode_FXC1 R a b - (torNode_FXC1 R a' b' + latticeVec_FXC1 Λ n)) i = R * (k : ℝ) →
      R ≤ ‖torNode_FXC1 R a b - (torNode_FXC1 R a' b' + latticeVec_FXC1 Λ n)‖ := by
    intro i k hk hik
    have h1 := PiLp.norm_apply_le
      (torNode_FXC1 R a b - (torNode_FXC1 R a' b' + latticeVec_FXC1 Λ n)) i
    rw [hik, Real.norm_eq_abs, abs_mul, abs_of_pos hR] at h1
    have h2 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
    nlinarith
  have hNZ : (0 : ℤ) < N := lt_of_le_of_lt ha.1 ha.2
  by_cases hA : a - a' - N * n.toInts 0 = 0
  · by_cases hB : b - b' - N * n.toInts 1 = 0
    · exfalso
      refine hne ⟨?_, ?_⟩
      · have h := Int.eq_zero_of_abs_lt_dvd (m := N) (x := a - a')
          ⟨n.toInts 0, by linarith⟩ (by
            rw [abs_lt]
            constructor <;> linarith [ha.1, ha.2, ha'.1, ha'.2])
        linarith
      · have h := Int.eq_zero_of_abs_lt_dvd (m := N) (x := b - b')
          ⟨n.toInts 1, by linarith⟩ (by
            rw [abs_lt]
            constructor <;> linarith [hb.1, hb.2, hb'.1, hb'.2])
        linarith
    · exact hbig 1 _ hB hc1
  · exact hbig 0 _ hA hc0

end Net

end DifferentialGeometry.Geometry.Collapse
