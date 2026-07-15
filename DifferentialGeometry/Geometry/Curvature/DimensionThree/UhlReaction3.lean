import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Dim-3 Hamilton reaction match (B3d algebraic core)

Self-contained `Fin 3` curvature-algebra identity underlying the Uhlenbeck base
`∂ₜRm04` (Lemma 6.1) on the **3D algebraic route**.  Everything here is a pure
`Fin 3 → ℝ` computation on a symmetric "Ricci" matrix `R`; the frame bridge
(`UhlenbeckBaseProducer` / frame-reconciliation) instantiates `R` at the
orthonormal-frame Ricci components and identifies `Bt`/`drift` with
`uhlenbeckBTensorInFrame` / `riemann04RicciDriftInFrame`.

The lowered Riemann tensor `rm` is the Kulkarni–Nomizu combination of `R`, its
trace `S`, and the Kronecker `δ`, in the project sign convention (first trace
`Σ_b rm a b c b = -R a c`).  The target identity (`reaction_match`) is

`KN(Q_Ric, Q_S, δ) + G = -2·B# - drift`,

with the **corrected** `-2(B#)` Uhlenbeck convention (see `Evolution/Uhlenbeck.lean`),
`Q_Ric = -2C - 2R²`, `Q_S = 2|R|²`, and `G` the `∂ₜg = -2Ric` cross-terms from the
KN product rule (`solution_rm04_timeDeriv_kn`).

It is proved by the GPT-Pro-validated decomposition
`reaction_match = (KN-linearity) ∘ bsharp_eq_knC ∘ driftG_eq_knRsq`:

* `driftG_eq_knRsq`  (diag2): `drift + G = 2·KN(R², 0, δ)` — cheap `Fin 3` brute force.
* `bsharp_eq_knC`    (diag1): `B# = KN(C, -|R|², δ)`.  The direct 81-case brute force is
  wall-infeasible (the double contraction `B#` costs ~200k heartbeats per component), so
  it is itself decomposed:
  - `bt_closed`: a sum-free closed form of `Bt` in the atoms
    `{R, R², δ, S, |R|²}` (per-component brute force is cheap once only ONE `Bt` is
    expanded per goal);
  - `cc_closed`: `C = 2R² − (3S/2)·R + (S²/2 − |R|²)·δ`;
  - `minor_adj3`: the 3×3 adjugate/minor identity
    `R_ac R_bd − R_ad R_bc = −KNanti(R²) + S·KNanti(R) − ((S²−|R|²)/2)·δδanti` —
    the genuine dim-3 input (the Cayley–Hamilton face);
  - assembly by `linear_combination` (formal in the atoms; no sums left).
* `reaction_match`: cheap `linear_combination` assembly from the two diagnostics.

The full identity is independently CONFIRMED CORRECT by `ring` at 7 diverse components
(0101, 0120, 1122, 0212, 0112, 0202, 1212).
-/

set_option linter.unusedSectionVars false

namespace DifferentialGeometry.Dim3Reaction

open scoped BigOperators

noncomputable section

variable (R : Fin 3 → Fin 3 → ℝ)

/-- Kronecker delta on `Fin 3`. -/
def kd (i j : Fin 3) : ℝ := if i = j then 1 else 0

/-- Scalar curvature `S = tr R`. -/
def sc : ℝ := R 0 0 + R 1 1 + R 2 2

/-- Lowered Riemann (Kulkarni–Nomizu of `R`/`S`/`δ`); first trace `Σ_b rm a b c b = -R a c`. -/
def rm (a b c d : Fin 3) : ℝ :=
  -R a c * kd b d + R b c * kd a d + R a d * kd b c - R b d * kd a c
    + (sc R / 2) * (kd a c * kd b d - kd b c * kd a d)

/-- Uhlenbeck B-tensor (orthonormal form) `B_abcd = Σ_e Σ_f rm_aebf rm_cedf`. -/
def Bt (a b c d : Fin 3) : ℝ := ∑ e, ∑ f, rm R a e b f * rm R c e d f

/-- Hamilton's `B#` combination. -/
def Bsharp (a b c d : Fin 3) : ℝ :=
  Bt R a b c d - Bt R a b d c + Bt R a c b d - Bt R a d b c

/-- Ricci-drift `Σ_p (R_ap rm_pbcd + R_bp rm_apcd + R_cp rm_abpd + R_dp rm_abcp)`. -/
def drift (a b c d : Fin 3) : ℝ :=
  ∑ p, (R a p * rm R p b c d + R b p * rm R a p c d
        + R c p * rm R a b p d + R d p * rm R a b c p)

/-- Curvature action on Ricci `C_ij = Σ_kl rm_ikjl R_kl`. -/
def Cc (i j : Fin 3) : ℝ := ∑ k, ∑ l, rm R i k j l * R k l

/-- Ricci square `(R²)_ij = Σ_p R_ip R_pj`. -/
def Rsq (i j : Fin 3) : ℝ := ∑ p, R i p * R p j

/-- `|Ric|² = Σ_ij R_ij²`. -/
def normSq : ℝ := ∑ i, ∑ j, R i j * R i j

/-- Ricci reaction `Q_Ric = -2C - 2R²`. -/
def QRic (i j : Fin 3) : ℝ := -2 * Cc R i j - 2 * Rsq R i j

/-- Scalar reaction `Q_S = 2|Ric|²`. -/
def QS : ℝ := 2 * normSq R

/-- `KN(Q_Ric, Q_S, δ)`. -/
def KNQ (a b c d : Fin 3) : ℝ :=
  -QRic R a c * kd b d + QRic R b c * kd a d + QRic R a d * kd b c - QRic R b d * kd a c
    + (QS R / 2) * (kd a c * kd b d - kd b c * kd a d)

/-- The `∂ₜg = -2Ric` cross-terms `G` from the KN product rule (B3b). -/
def Gg (a b c d : Fin 3) : ℝ :=
  4 * R a c * R b d - 4 * R a d * R b c
    + sc R * (-R a c * kd b d - kd a c * R b d + R b c * kd a d + kd b c * R a d)

/-- `KN(C, -|R|², δ)`. -/
def knC (a b c d : Fin 3) : ℝ :=
  -Cc R a c * kd b d + Cc R b c * kd a d + Cc R a d * kd b c - Cc R b d * kd a c
    + (-normSq R / 2) * (kd a c * kd b d - kd b c * kd a d)

/-- `KN(R², 0, δ)`. -/
def knRsq (a b c d : Fin 3) : ℝ :=
  -Rsq R a c * kd b d + Rsq R b c * kd a d + Rsq R a d * kd b c - Rsq R b d * kd a c

variable {R}

set_option maxHeartbeats 1000000 in
/-- **diag2** — `drift + G = 2·KN(R², 0, δ)`.  Cheap `Fin 3` brute force (single `Σ_p`,
no double contraction). -/
theorem driftG_eq_knRsq (hR : ∀ i j, R i j = R j i) (a b c d : Fin 3) :
    drift R a b c d + Gg R a b c d = 2 * knRsq R a b c d := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp only [drift, Gg, knRsq, Rsq, rm, sc, kd, Fin.sum_univ_three, Fin.isValue,
      Fin.reduceFinMk, Fin.reduceEq, reduceIte] <;>
    (try simp only [hR 1 0, hR 2 0, hR 2 1]) <;> ring

/-- `kd` is symmetric. -/
theorem kd_comm (i j : Fin 3) : kd i j = kd j i := by
  unfold kd
  rcases eq_or_ne i j with h | h
  · simp [h]
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- `R²` is symmetric when `R` is. -/
theorem rsq_comm (hR : ∀ i j, R i j = R j i) (i j : Fin 3) :
    Rsq R i j = Rsq R j i := by
  unfold Rsq
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hR i p, hR p j, mul_comm]

set_option maxHeartbeats 2000000 in
/-- Closed form of the curvature action: `C = 2R² − (3S/2)·R + (S²/2 − |R|²)·δ`. -/
theorem cc_closed (hR : ∀ i j, R i j = R j i) (i j : Fin 3) :
    Cc R i j = 2 * Rsq R i j - 3 / 2 * sc R * R i j
      + (sc R ^ 2 / 2 - normSq R) * kd i j := by
  fin_cases i <;> fin_cases j <;>
    simp only [Cc, Rsq, normSq, rm, sc, kd, Fin.sum_univ_three, Fin.isValue,
      Fin.reduceFinMk, Fin.reduceEq, reduceIte] <;>
    (try simp only [hR 1 0, hR 2 0, hR 2 1]) <;> ring

set_option maxHeartbeats 4000000 in
private theorem minor_a0 (hR : ∀ i j, R i j = R j i) (b c d : Fin 3) :
    R 0 c * R b d - R 0 d * R b c =
      -(kd 0 c * Rsq R b d + Rsq R 0 c * kd b d
          - kd 0 d * Rsq R b c - Rsq R 0 d * kd b c)
        + sc R * (kd 0 c * R b d + R 0 c * kd b d - kd 0 d * R b c - R 0 d * kd b c)
        - ((sc R ^ 2 - normSq R) / 2) * (kd 0 c * kd b d - kd 0 d * kd b c) := by
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp only [Rsq, normSq, sc, kd, Fin.sum_univ_three, Fin.isValue,
      Fin.reduceFinMk, Fin.reduceEq, reduceIte] <;>
    (try simp only [hR 1 0, hR 2 0, hR 2 1]) <;> ring

set_option maxHeartbeats 4000000 in
private theorem minor_a1 (hR : ∀ i j, R i j = R j i) (b c d : Fin 3) :
    R 1 c * R b d - R 1 d * R b c =
      -(kd 1 c * Rsq R b d + Rsq R 1 c * kd b d
          - kd 1 d * Rsq R b c - Rsq R 1 d * kd b c)
        + sc R * (kd 1 c * R b d + R 1 c * kd b d - kd 1 d * R b c - R 1 d * kd b c)
        - ((sc R ^ 2 - normSq R) / 2) * (kd 1 c * kd b d - kd 1 d * kd b c) := by
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp only [Rsq, normSq, sc, kd, Fin.sum_univ_three, Fin.isValue,
      Fin.reduceFinMk, Fin.reduceEq, reduceIte] <;>
    (try simp only [hR 1 0, hR 2 0, hR 2 1]) <;> ring

set_option maxHeartbeats 4000000 in
private theorem minor_a2 (hR : ∀ i j, R i j = R j i) (b c d : Fin 3) :
    R 2 c * R b d - R 2 d * R b c =
      -(kd 2 c * Rsq R b d + Rsq R 2 c * kd b d
          - kd 2 d * Rsq R b c - Rsq R 2 d * kd b c)
        + sc R * (kd 2 c * R b d + R 2 c * kd b d - kd 2 d * R b c - R 2 d * kd b c)
        - ((sc R ^ 2 - normSq R) / 2) * (kd 2 c * kd b d - kd 2 d * kd b c) := by
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp only [Rsq, normSq, sc, kd, Fin.sum_univ_three, Fin.isValue,
      Fin.reduceFinMk, Fin.reduceEq, reduceIte] <;>
    (try simp only [hR 1 0, hR 2 0, hR 2 1]) <;> ring

/-- **3×3 adjugate/minor identity** (the Cayley–Hamilton face) — the genuine dim-3
input behind `B# = KN(C, -|R|², δ)`:
`R_ac R_bd − R_ad R_bc = −KNanti(R²) + S·KNanti(R) − ((S²−|R|²)/2)·δδanti`. -/
theorem minor_adj3 (hR : ∀ i j, R i j = R j i) (a b c d : Fin 3) :
    R a c * R b d - R a d * R b c =
      -(kd a c * Rsq R b d + Rsq R a c * kd b d
          - kd a d * Rsq R b c - Rsq R a d * kd b c)
        + sc R * (kd a c * R b d + R a c * kd b d - kd a d * R b c - R a d * kd b c)
        - ((sc R ^ 2 - normSq R) / 2) * (kd a c * kd b d - kd a d * kd b c) := by
  fin_cases a
  · exact minor_a0 hR b c d
  · exact minor_a1 hR b c d
  · exact minor_a2 hR b c d

set_option maxHeartbeats 6000000 in
private theorem bt_a0 (hR : ∀ i j, R i j = R j i) (b c d : Fin 3) :
    Bt R 0 b c d = -(R 0 b * R c d) + 2 * R 0 c * R b d
      + kd 0 c * Rsq R b d + Rsq R 0 c * kd b d
      - 2 * kd 0 b * Rsq R c d - 2 * Rsq R 0 b * kd c d
      + 3 / 2 * sc R * (R 0 b * kd c d + kd 0 b * R c d)
      - sc R * (kd 0 c * R b d + R 0 c * kd b d)
      + (normSq R - 3 / 4 * sc R ^ 2) * (kd 0 b * kd c d)
      + sc R ^ 2 / 4 * (kd 0 c * kd b d) := by
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp only [Bt, Rsq, normSq, rm, sc, kd, Fin.sum_univ_three, Fin.isValue,
      Fin.reduceFinMk, Fin.reduceEq, reduceIte] <;>
    (try simp only [hR 1 0, hR 2 0, hR 2 1]) <;> ring

set_option maxHeartbeats 6000000 in
private theorem bt_a1 (hR : ∀ i j, R i j = R j i) (b c d : Fin 3) :
    Bt R 1 b c d = -(R 1 b * R c d) + 2 * R 1 c * R b d
      + kd 1 c * Rsq R b d + Rsq R 1 c * kd b d
      - 2 * kd 1 b * Rsq R c d - 2 * Rsq R 1 b * kd c d
      + 3 / 2 * sc R * (R 1 b * kd c d + kd 1 b * R c d)
      - sc R * (kd 1 c * R b d + R 1 c * kd b d)
      + (normSq R - 3 / 4 * sc R ^ 2) * (kd 1 b * kd c d)
      + sc R ^ 2 / 4 * (kd 1 c * kd b d) := by
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp only [Bt, Rsq, normSq, rm, sc, kd, Fin.sum_univ_three, Fin.isValue,
      Fin.reduceFinMk, Fin.reduceEq, reduceIte] <;>
    (try simp only [hR 1 0, hR 2 0, hR 2 1]) <;> ring

set_option maxHeartbeats 6000000 in
private theorem bt_a2 (hR : ∀ i j, R i j = R j i) (b c d : Fin 3) :
    Bt R 2 b c d = -(R 2 b * R c d) + 2 * R 2 c * R b d
      + kd 2 c * Rsq R b d + Rsq R 2 c * kd b d
      - 2 * kd 2 b * Rsq R c d - 2 * Rsq R 2 b * kd c d
      + 3 / 2 * sc R * (R 2 b * kd c d + kd 2 b * R c d)
      - sc R * (kd 2 c * R b d + R 2 c * kd b d)
      + (normSq R - 3 / 4 * sc R ^ 2) * (kd 2 b * kd c d)
      + sc R ^ 2 / 4 * (kd 2 c * kd b d) := by
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp only [Bt, Rsq, normSq, rm, sc, kd, Fin.sum_univ_three, Fin.isValue,
      Fin.reduceFinMk, Fin.reduceEq, reduceIte] <;>
    (try simp only [hR 1 0, hR 2 0, hR 2 1]) <;> ring

/-- **Closed form of the `B`-tensor in dim 3** (sum-free, in the atoms `R/R²/δ/S/|R|²`):
`Bt = −R_ab R_cd + 2R_ac R_bd + δ_ac(R²)_bd + (R²)_ac δ_bd − 2δ_ab(R²)_cd − 2(R²)_ab δ_cd
  + (3S/2)(R_ab δ_cd + δ_ab R_cd) − S(δ_ac R_bd + R_ac δ_bd)
  + (|R|² − ¾S²)·δ_ab δ_cd + (S²/4)·δ_ac δ_bd`. -/
theorem bt_closed (hR : ∀ i j, R i j = R j i) (a b c d : Fin 3) :
    Bt R a b c d = -(R a b * R c d) + 2 * R a c * R b d
      + kd a c * Rsq R b d + Rsq R a c * kd b d
      - 2 * kd a b * Rsq R c d - 2 * Rsq R a b * kd c d
      + 3 / 2 * sc R * (R a b * kd c d + kd a b * R c d)
      - sc R * (kd a c * R b d + R a c * kd b d)
      + (normSq R - 3 / 4 * sc R ^ 2) * (kd a b * kd c d)
      + sc R ^ 2 / 4 * (kd a c * kd b d) := by
  fin_cases a
  · exact bt_a0 hR b c d
  · exact bt_a1 hR b c d
  · exact bt_a2 hR b c d

/-- **diag1** — `B# = KN(C, -|R|², δ)`: Hamilton's `B#` combination is the
Kulkarni–Nomizu of the curvature action.  Assembled from `bt_closed` (×4 slot
permutations), `cc_closed`, and the dim-3 `minor_adj3`, by `linear_combination`
after orienting the symmetric atoms. -/
theorem bsharp_eq_knC (hR : ∀ i j, R i j = R j i) (a b c d : Fin 3) :
    Bsharp R a b c d = knC R a b c d := by
  have h1 := bt_closed hR a b c d
  have h2 := bt_closed hR a b d c
  have h3 := bt_closed hR a c b d
  have h4 := bt_closed hR a d b c
  have hc1 := cc_closed hR a c
  have hc2 := cc_closed hR b c
  have hc3 := cc_closed hR a d
  have hc4 := cc_closed hR b d
  have hm := minor_adj3 hR a b c d
  simp only [Bsharp, knC]
  simp only [hR d c, rsq_comm hR d c, kd_comm d c]
    at h1 h2 h3 h4 hc1 hc2 hc3 hc4 hm ⊢
  linear_combination h1 - h2 + h3 - h4 + kd b d * hc1 - kd a d * hc2
    - kd b c * hc3 + kd a c * hc4 + hm

set_option maxHeartbeats 1000000 in
/-- **Reaction match (B3d).**  The corrected `-2(B#)` 3D reaction identity, assembled
from `bsharp_eq_knC` + `driftG_eq_knRsq` by KN-linearity (`linear_combination`, no `Bt`). -/
theorem reaction_match (hR : ∀ i j, R i j = R j i) (a b c d : Fin 3) :
    KNQ R a b c d + Gg R a b c d = -2 * Bsharp R a b c d - drift R a b c d := by
  have hd1 := bsharp_eq_knC hR a b c d
  have hd2 := driftG_eq_knRsq hR a b c d
  simp only [KNQ, QRic, QS, knC, knRsq] at hd1 hd2 ⊢
  linear_combination 2 * hd1 + hd2

end

end DifferentialGeometry.Dim3Reaction
