import DifferentialGeometry.Geometry.Curvature.DimensionThree.HamiltonIvey.Reaction
import Mathlib.Analysis.Matrix.PosDef


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set DifferentialGeometry.Analysis.Convex
open DifferentialGeometry.Analysis.InnerProductSpace
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open scoped Matrix BigOperators _root_.Topology


def roundTracePinchingCone (c : ℝ) : Set (Matrix (Fin 3) (Fin 3) ℝ) :=
  {A | A.IsHermitian ∧ 0 ≤ minimumRayleighQuotient3 A ∧
    c * A.trace ≤ minimumRayleighQuotient3 A}


theorem isClosed_roundTracePinchingCone (c : ℝ) :
    IsClosed (roundTracePinchingCone c) := by
  have hHerm : IsClosed {A : Matrix (Fin 3) (Fin 3) ℝ | A.IsHermitian} := by
    have heq : {A : Matrix (Fin 3) (Fin 3) ℝ | A.IsHermitian} =
        {A : Matrix (Fin 3) (Fin 3) ℝ | A.transpose = A} := by
      ext A
      simp [Matrix.IsHermitian]
    rw [heq]
    exact isClosed_eq (by fun_prop) continuous_id
  have htrace : Continuous (fun A : Matrix (Fin 3) (Fin 3) ℝ => c * A.trace) := by
    unfold Matrix.trace
    fun_prop
  exact hHerm.inter ((isClosed_le continuous_const continuous_minimumRayleighQuotient3).inter
    (isClosed_le htrace continuous_minimumRayleighQuotient3))


theorem convex_roundTracePinchingCone (c : ℝ) :
    Convex ℝ (roundTracePinchingCone c) := by
  intro A hA B hB a b ha hb hab
  have hm := concave_minimumRayleighQuotient3.2 (mem_univ A) (mem_univ B) ha hb hab
  have htr : (a • A + b • B).trace = a * A.trace + b * B.trace := by
    simp only [Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  refine ⟨(hA.1.smul (k := a) (by rfl)).add (hB.1.smul (k := b) (by rfl)), ?_, ?_⟩
  · exact (add_nonneg (mul_nonneg ha hA.2.1) (mul_nonneg hb hB.2.1)).trans hm
  · rw [htr]
    calc
      c * (a * A.trace + b * B.trace) = a * (c * A.trace) + b * (c * B.trace) := by ring
      _ ≤ a * minimumRayleighQuotient3 A + b * minimumRayleighQuotient3 B :=
        add_le_add (mul_le_mul_of_nonneg_left hA.2.2 ha)
          (mul_le_mul_of_nonneg_left hB.2.2 hb)
      _ ≤ minimumRayleighQuotient3 (a • A + b • B) := hm


theorem roundTracePinchingCone_orthogonal_conj {c : ℝ}
    {A O : Matrix (Fin 3) (Fin 3) ℝ} (hO : O * O.transpose = 1)
    (hA : A ∈ roundTracePinchingCone c) :
    O.transpose * A * O ∈ roundTracePinchingCone c := by
  have hB : (O.transpose * A * O).IsHermitian := by
    simpa using Matrix.isHermitian_conjTranspose_mul_mul O hA.1
  have htrace : (O.transpose * A * O).trace = A.trace := by
    have h := Matrix.trace_mul_cycle O.transpose A O
    rw [hO] at h
    simpa only [Matrix.one_mul] using h
  have hmin : minimumRayleighQuotient3 (O.transpose * A * O) =
      minimumRayleighQuotient3 A := by
    rw [minimumRayleighQuotient3_eq_min_eigenvalue hB,
      minimumRayleighQuotient3_eq_min_eigenvalue hA.1,
      eigenvalues₀_eq_of_charpoly_eq_real hB hA.1 (charpoly_orthogonal_conj hO)]
  exact ⟨hB, hmin ▸ hA.2.1, by rw [htrace, hmin]; exact hA.2.2⟩


theorem diagonal_mem_roundTracePinchingCone_iff (c : ℝ) (d : Fin 3 → ℝ) :
    Matrix.diagonal d ∈ roundTracePinchingCone c ↔
      (∀ i, 0 ≤ d i) ∧ ∀ i, c * (∑ j, d j) ≤ d i := by
  constructor
  · intro h
    refine ⟨fun i => h.2.1.trans (minimumRayleighQuotient3_diagonal_le d i), ?_⟩
    intro i
    have hmin := h.2.2.trans (minimumRayleighQuotient3_diagonal_le d i)
    simpa only [Matrix.trace_diagonal] using hmin
  · rintro ⟨hpos, hpinch⟩
    exact ⟨Matrix.isHermitian_diagonal d,
      minimumRayleighQuotient3_diagonal_ge d hpos,
      by simpa only [Matrix.trace_diagonal] using
        minimumRayleighQuotient3_diagonal_ge d hpinch⟩


theorem round_pinching_boundary_reaction
    {c a b d : ℝ} (hc : 0 ≤ c) (hab : a ≤ b) (had : a ≤ d)
    (hboundary : a = c * (a + b + d)) :
    2 * c ^ 2 * (1 - 3 * c) * (a + b + d) ^ 2 ≤
      2 * (a ^ 2 + b * d) -
        c * (2 * (a ^ 2 + b * d) + 2 * (b ^ 2 + a * d) + 2 * (d ^ 2 + a * b)) := by
  let S := a + b + d
  have ha : a = c * S := hboundary
  have hsum : b + d = (1 - c) * S := by dsimp [S] at *; nlinarith [hboundary]
  have hzero : a ^ 2 - c * a * S = 0 := by rw [ha]; ring
  have hprod : c * (1 - 2 * c) * S ^ 2 ≤ b * d := by
    have hp := mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr had)
    rw [ha] at hp
    have heq : (b - c * S) * (d - c * S) = b * d - c * (1 - 2 * c) * S ^ 2 := by
      calc
        _ = b * d - c * S * (b + d) + c ^ 2 * S ^ 2 := by ring
        _ = _ := by rw [hsum]; ring
    rw [heq] at hp
    linarith
  calc
    _ = 2 * ((1 + c) * (c * (1 - 2 * c) * S ^ 2) - c * (b + d) ^ 2) := by
      change 2 * c ^ 2 * (1 - 3 * c) * S ^ 2 = _
      rw [hsum]
      ring
    _ ≤ 2 * ((1 + c) * (b * d) - c * (b + d) ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hprod (by linarith : 0 ≤ 1 + c)]
    _ = 2 * (a ^ 2 + b * d) -
        c * (2 * (a ^ 2 + b * d) + 2 * (b ^ 2 + a * d) + 2 * (d ^ 2 + a * b)) := by
      calc
        _ = 2 * (a ^ 2 - c * a * S + (1 + c) * (b * d) - c * (b + d) ^ 2) := by
          rw [hzero, zero_add]
        _ = _ := by dsimp [S]; ring

private theorem linear_gap_nonneg_small_time {a b : ℝ}
    (ha : 0 ≤ a) (hb : a = 0 → 0 ≤ b) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Icc 0 ε, 0 ≤ a + t * b := by
  rcases ha.eq_or_lt with ha | ha
  · refine ⟨1, by norm_num, fun t ht => ?_⟩
    rw [← ha, zero_add]
    exact mul_nonneg ht.1 (hb ha.symm)
  · refine ⟨a / (|b| + 1), div_pos ha (by positivity), fun t ht => ?_⟩
    have hbound := (le_div_iff₀ (by positivity : 0 < |b| + 1)).mp ht.2
    have hlow := mul_le_mul_of_nonneg_left (neg_abs_le b) ht.1
    nlinarith [ht.1]

private theorem round_pinching_boundary_nonneg
    {c a b d : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 1 / 3)
    (hab : a ≤ b) (had : a ≤ d) (hboundary : a = c * (a + b + d)) :
    0 ≤ 2 * (a ^ 2 + b * d) -
      c * (2 * (a ^ 2 + b * d) + 2 * (b ^ 2 + a * d) + 2 * (d ^ 2 + a * b)) := by
  have hcoef : 0 ≤ 1 - 3 * c := by linarith
  have hnonneg : 0 ≤ 2 * c ^ 2 * (1 - 3 * c) * (a + b + d) ^ 2 := by positivity
  exact hnonneg.trans (round_pinching_boundary_reaction hc hab had hboundary)

private theorem diagonal_roundTracePinchingCone_reaction_small_time
    {c : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 1 / 3) (a b d : ℝ)
    (hA : Matrix.diagonal ![a, b, d] ∈ roundTracePinchingCone c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Icc 0 ε,
      Matrix.diagonal ![a, b, d] +
        t • hamiltonIveyMatrixReaction (Matrix.diagonal ![a, b, d]) ∈
          roundTracePinchingCone c := by
  let v : Fin 3 → ℝ := ![a, b, d]
  let r : Fin 3 → ℝ :=
    ![2 * (a ^ 2 + b * d), 2 * (b ^ 2 + a * d), 2 * (d ^ 2 + a * b)]
  obtain ⟨hpos, hpinch⟩ := (diagonal_mem_roundTracePinchingCone_iff c v).mp hA
  have hv : (∑ j, v j) = a + b + d := by simp [v, Fin.sum_univ_succ]; ring
  have hr : (∑ j, r j) =
      2 * (a ^ 2 + b * d) + 2 * (b ^ 2 + a * d) + 2 * (d ^ 2 + a * b) := by
    simp [r, Fin.sum_univ_succ]
    ring
  have hpa := hpos (0 : Fin 3)
  have hpb := hpos (1 : Fin 3)
  have hpd := hpos (2 : Fin 3)
  change 0 ≤ a at hpa
  change 0 ≤ b at hpb
  change 0 ≤ d at hpd
  have hra : ∀ i, 0 ≤ r i := by
    intro i
    fin_cases i <;> dsimp [r] <;> positivity
  have h0 := hpinch (0 : Fin 3)
  have h1 := hpinch (1 : Fin 3)
  have h2 := hpinch (2 : Fin 3)
  change c * (∑ j, v j) ≤ a at h0
  change c * (∑ j, v j) ≤ b at h1
  change c * (∑ j, v j) ≤ d at h2
  rw [hv] at h0 h1 h2
  have hboundary (i : Fin 3) (hi : v i - c * (∑ j, v j) = 0) :
      0 ≤ r i - c * (∑ j, r j) := by
    rw [hv] at hi
    rw [hr]
    fin_cases i
    · change a - c * (a + b + d) = 0 at hi
      have hb := round_pinching_boundary_nonneg hc hc'
        (by linarith : a ≤ b) (by linarith : a ≤ d) (by linarith : a = c * (a + b + d))
      exact hb
    · change b - c * (a + b + d) = 0 at hi
      have hb := round_pinching_boundary_nonneg hc hc'
        (by linarith : b ≤ a) (by linarith : b ≤ d) (by nlinarith : b = c * (b + a + d))
      dsimp [r]
      nlinarith [hb]
    · change d - c * (a + b + d) = 0 at hi
      have hb := round_pinching_boundary_nonneg hc hc'
        (by linarith : d ≤ a) (by linarith : d ≤ b) (by nlinarith : d = c * (d + a + b))
      dsimp [r]
      nlinarith [hb]
  choose ε hε hstep using fun i : Fin 3 =>
    linear_gap_nonneg_small_time (sub_nonneg.mpr (hpinch i)) (hboundary i)
  let δ := min (ε 0) (min (ε 1) (ε 2))
  have hδ : 0 < δ := lt_min (hε 0) (lt_min (hε 1) (hε 2))
  have hδi : ∀ i : Fin 3, δ ≤ ε i := by
    intro i
    fin_cases i
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, hδ, fun t ht => ?_⟩
  rw [hamiltonIveyMatrixReaction_diagonal]
  have heq : Matrix.diagonal v + t • Matrix.diagonal r =
      Matrix.diagonal (fun i => v i + t * r i) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  rw [heq]
  apply (diagonal_mem_roundTracePinchingCone_iff c _).mpr
  refine ⟨fun i => add_nonneg (hpos i) (mul_nonneg ht.1 (hra i)), fun i => ?_⟩
  have h := hstep i t ⟨ht.1, ht.2.trans (hδi i)⟩
  have hsum : (∑ j, (v j + t * r j)) = (∑ j, v j) + t * (∑ j, r j) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsum]
  nlinarith [h]


theorem roundTracePinchingCone_reaction_small_time
    {c : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 1 / 3)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A ∈ roundTracePinchingCone c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Icc 0 ε,
      A + t • hamiltonIveyMatrixReaction A ∈ roundTracePinchingCone c := by
  obtain ⟨O, hO, hdiag⟩ := hermitian_orthogonal_diagonalization hA.1
  rw [diagonal_eigenvalues_tuple] at hdiag
  let D : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.diagonal ![hA.1.eigenvalues₀ 0, hA.1.eigenvalues₀ 1, hA.1.eigenvalues₀ 2]
  have hdiagD : O.transpose * A * O = D := hdiag
  have hD : D ∈ roundTracePinchingCone c := by
    rw [← hdiagD]
    exact roundTracePinchingCone_orthogonal_conj hO hA
  obtain ⟨ε, hε, hstep⟩ := diagonal_roundTracePinchingCone_reaction_small_time hc hc'
    (hA.1.eigenvalues₀ 0) (hA.1.eigenvalues₀ 1) (hA.1.eigenvalues₀ 2) hD
  have hO' : O.transpose * O = 1 := matrixTransposeMul_orthogonal O hO
  have hfactor : A = O * D * O.transpose := by
    calc
      A = O * (O.transpose * A * O) * O.transpose := by
        have heq : O * (O.transpose * A * O) * O.transpose =
            (O * O.transpose) * A * (O * O.transpose) := by simp only [Matrix.mul_assoc]
        rw [heq, hO, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by rw [hdiagD]
  refine ⟨ε, hε, fun t ht => ?_⟩
  have hstepD : D + t • hamiltonIveyMatrixReaction D ∈ roundTracePinchingCone c := hstep t ht
  have hconj := roundTracePinchingCone_orthogonal_conj
    (O := O.transpose) (by simpa only [Matrix.transpose_transpose] using hO') hstepD
  have hmatrix : O * (D + t • hamiltonIveyMatrixReaction D) * O.transpose =
      A + t • hamiltonIveyMatrixReaction A := by
    rw [hfactor, hamiltonIveyMatrixReaction_orthogonal_conj O D hO,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  change O * (D + t • hamiltonIveyMatrixReaction D) * O.transpose ∈ roundTracePinchingCone c at hconj
  rw [hmatrix] at hconj
  exact hconj


def roundTracePinchingConeEuclidean (c : ℝ) : Set (EuclideanSpace ℝ (Fin 3 × Fin 3)) :=
  euclideanToMatrix ⁻¹' roundTracePinchingCone c


theorem isClosed_roundTracePinchingConeEuclidean (c : ℝ) :
    IsClosed (roundTracePinchingConeEuclidean c) := by
  have hf : Continuous (euclideanToMatrix :
      EuclideanSpace ℝ (Fin 3 × Fin 3) → Matrix (Fin 3) (Fin 3) ℝ) := by
    unfold euclideanToMatrix
    fun_prop
  exact (isClosed_roundTracePinchingCone c).preimage hf


theorem convex_roundTracePinchingConeEuclidean (c : ℝ) :
    Convex ℝ (roundTracePinchingConeEuclidean c) := by
  exact (convex_roundTracePinchingCone c).linear_preimage
    (matrixEuclideanLinearEquiv (m := Fin 3) (n := Fin 3)).symm.toLinearMap


theorem roundTracePinchingConeEuclidean_reaction_mem_posTangentCone
    {c : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 1 / 3)
    (A : EuclideanSpace ℝ (Fin 3 × Fin 3)) (hA : A ∈ roundTracePinchingConeEuclidean c) :
    hamiltonIveyMatrixReactionEuclidean A ∈ posTangentConeAt (roundTracePinchingConeEuclidean c) A := by
  obtain ⟨ε, hε, hstep⟩ := roundTracePinchingCone_reaction_small_time hc hc'
    (euclideanToMatrix A) hA
  have hstepE (t : ℝ) (ht : t ∈ Icc 0 ε) :
      A + t • hamiltonIveyMatrixReactionEuclidean A ∈ roundTracePinchingConeEuclidean c := by
    change euclideanToMatrix (A + t • hamiltonIveyMatrixReactionEuclidean A) ∈ roundTracePinchingCone c
    rw [euclideanToMatrix_add, euclideanToMatrix_smul, hamiltonIveyMatrixReactionEuclidean,
      euclideanToMatrix_matrixToEuclidean]
    exact hstep t ht
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, A + t • hamiltonIveyMatrixReactionEuclidean A ∈
      roundTracePinchingConeEuclidean c := by
    rw [eventually_nhdsWithin_iff]
    apply Filter.mem_of_superset (Ioo_mem_nhds (neg_lt_zero.mpr hε) hε)
    intro t ht htpos
    exact hstepE t ⟨htpos.le, ht.2.le⟩
  exact mem_posTangentConeAt_of_frequently_mem hev.frequently


theorem roundTracePinchingCone_third_eq_scalar
    {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A ∈ roundTracePinchingCone (1 / 3)) :
    A = (A.trace / 3) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  have hshift : (-(A.trace / 3) • (1 : Matrix (Fin 3) (Fin 3) ℝ) + A).PosSemidef := by
    apply (posSemidef_shift_iff_min_eigenvalue hA.1 _).mpr
    rw [← minimumRayleighQuotient3_eq_min_eigenvalue hA.1]
    have hp := hA.2.2
    change (1 / 3 : ℝ) * A.trace ≤ minimumRayleighQuotient3 A at hp
    linarith
  have htrace : (-(A.trace / 3) • (1 : Matrix (Fin 3) (Fin 3) ℝ) + A).trace = 0 := by
    simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
      Fintype.card_fin, Nat.cast_ofNat, smul_eq_mul]
    ring
  have hzero := hshift.trace_eq_zero_iff.mp htrace
  have hcancel : (-(A.trace / 3) • (1 : Matrix (Fin 3) (Fin 3) ℝ) + A) +
      (A.trace / 3) • (1 : Matrix (Fin 3) (Fin 3) ℝ) = A := by
    rw [neg_smul]
    abel
  rw [hzero, zero_add] at hcancel
  exact hcancel.symm


theorem matrix_eq_scalar_of_roundTracePinchingCone_tendsto
    {A : Matrix (Fin 3) (Fin 3) ℝ} {c : ℕ → ℝ}
    (hc : Tendsto c atTop (𝓝 (1 / 3)))
    (hA : ∀ᶠ i in atTop, A ∈ roundTracePinchingCone (c i)) :
    A = (A.trace / 3) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  obtain ⟨i, hi⟩ := hA.exists
  apply roundTracePinchingCone_third_eq_scalar
  refine ⟨hi.1, hi.2.1, ?_⟩
  exact le_of_tendsto (hc.mul_const A.trace) (hA.mono fun _ h => h.2.2)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
