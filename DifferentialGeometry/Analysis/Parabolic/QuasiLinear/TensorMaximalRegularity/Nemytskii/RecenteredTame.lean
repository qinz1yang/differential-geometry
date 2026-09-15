import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Module

noncomputable section

namespace DifferentialGeometry.Analysis.Parabolic

def recenteredRemainder
    {𝕜 T A X Y Z : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup A] [NormedSpace 𝕜 A]
    [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
    [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [SeminormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    (m : A →L[𝕜] Y →L[𝕜] Y)
    (Q : X →L[𝕜] Y) (J : X →L[𝕜] Z) (D : Z →L[𝕜] Y)
    (d : Y →L[𝕜] Y) (q : A)
    (alpha : T → Z → A) (reaction : T → Z → Y)
    (h : X) (t : T) (v : X) : Y :=
  m (alpha t (J h + J v) - q) (Q v) +
    m (alpha t (J h + J v) - q) (Q h) +
    reaction t (J h + J v) - d (D (J h + J v))

theorem recentered_tame_estimate
    {𝕜 T A X Y Z : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup A] [NormedSpace 𝕜 A]
    [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
    [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [SeminormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    (m : A →L[𝕜] Y →L[𝕜] Y)
    (Q : X →L[𝕜] Y) (J : X →L[𝕜] Z) (D : Z →L[𝕜] Y)
    (d : Y →L[𝕜] Y) (q : A)
    (alpha : T → Z → A) (reaction : T → Z → Y)
    {R K L M : ℝ} (h : X) (t : T)
    (ha_lip : ∀ z, ‖z‖ ≤ R → ∀ w, ‖w‖ ≤ R →
      ‖alpha t (J h + z) - alpha t (J h + w)‖ ≤ L * ‖z - w‖)
    (ha_close : ∀ z, ‖z‖ ≤ R →
      ‖alpha t (J h + z) - q‖ ≤ K * R)
    (hreaction_lip : ∀ z, ‖z‖ ≤ R → ∀ w, ‖w‖ ≤ R →
      ‖reaction t (J h + z) - reaction t (J h + w)‖ ≤ M * ‖z - w‖)
    {u v : X} (hu : ‖J u‖ ≤ R) (hv : ‖J v‖ ≤ R) :
    ‖recenteredRemainder m Q J D d q alpha reaction h t u -
        recenteredRemainder m Q J D d q alpha reaction h t v‖ ≤
      (‖m‖ * K * ‖Q‖) * R * ‖u - v‖ +
      (‖m‖ * L * ‖Q h‖ + M + ‖d‖ * ‖D‖) * ‖J (u - v)‖ +
      (‖m‖ * L * ‖Q‖) * (‖u‖ + ‖v‖) * ‖J (u - v)‖ := by
  dsimp only [recenteredRemainder]
  have hcoef_u := ha_close (J u) hu
  have hcoef_lip : ‖alpha t (J h + J u) - alpha t (J h + J v)‖ ≤
      L * ‖J (u - v)‖ := by
    simpa only [map_sub] using ha_lip (J u) hu (J v) hv
  have hreaction : ‖reaction t (J h + J u) - reaction t (J h + J v)‖ ≤
      M * ‖J (u - v)‖ := by
    simpa only [map_sub] using hreaction_lip (J u) hu (J v) hv
  have hprincipal :
      ‖m (alpha t (J h + J u) - q) (Q u) -
          m (alpha t (J h + J v) - q) (Q v)‖ ≤
        (‖m‖ * K * ‖Q‖) * R * ‖u - v‖ +
          (‖m‖ * L * ‖Q‖) * (‖u‖ + ‖v‖) * ‖J (u - v)‖ := by
    have heq : m (alpha t (J h + J u) - q) (Q u) -
          m (alpha t (J h + J v) - q) (Q v) =
        m (alpha t (J h + J u) - q) (Q (u - v)) +
          m (alpha t (J h + J u) - alpha t (J h + J v)) (Q v) := by
      simp only [map_sub, sub_apply]
      module
    rw [heq]
    calc
      ‖m (alpha t (J h + J u) - q) (Q (u - v)) +
          m (alpha t (J h + J u) - alpha t (J h + J v)) (Q v)‖ ≤
          ‖m (alpha t (J h + J u) - q) (Q (u - v))‖ +
            ‖m (alpha t (J h + J u) - alpha t (J h + J v)) (Q v)‖ := norm_add_le _ _
      _ ≤ ‖m‖ * (K * R) * (‖Q‖ * ‖u - v‖) +
            ‖m‖ * (L * ‖J (u - v)‖) * (‖Q‖ * (‖u‖ + ‖v‖)) := by
        apply add_le_add
        · exact m.le_of_opNorm₂_le_of_le le_rfl hcoef_u (Q.le_opNorm _)
        · exact m.le_of_opNorm₂_le_of_le le_rfl hcoef_lip
            ((Q.le_opNorm v).trans
              (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg u)) (norm_nonneg Q)))
      _ = _ := by ring
  have hshift :
      ‖m (alpha t (J h + J u) - q) (Q h) -
          m (alpha t (J h + J v) - q) (Q h)‖ ≤
        (‖m‖ * L * ‖Q h‖) * ‖J (u - v)‖ := by
    have heq : m (alpha t (J h + J u) - q) (Q h) -
          m (alpha t (J h + J v) - q) (Q h) =
        m (alpha t (J h + J u) - alpha t (J h + J v)) (Q h) := by
      simp only [map_sub, sub_apply]
      module
    rw [heq]
    calc
      ‖m (alpha t (J h + J u) - alpha t (J h + J v)) (Q h)‖ ≤
          ‖m‖ * ‖alpha t (J h + J u) - alpha t (J h + J v)‖ * ‖Q h‖ :=
            m.le_opNorm₂ _ _
      _ ≤ ‖m‖ * (L * ‖J (u - v)‖) * ‖Q h‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcoef_lip (norm_nonneg m)) (norm_nonneg (Q h))
      _ = _ := by ring
  have hcorrection :
      ‖d (D (J h + J u)) - d (D (J h + J v))‖ ≤
        (‖d‖ * ‖D‖) * ‖J (u - v)‖ := by
    rw [← d.map_sub, ← D.map_sub, add_sub_add_left_eq_sub, ← J.map_sub]
    calc
      ‖d (D (J (u - v)))‖ ≤ ‖d‖ * ‖D (J (u - v))‖ := d.le_opNorm _
      _ ≤ ‖d‖ * (‖D‖ * ‖J (u - v)‖) :=
        mul_le_mul_of_nonneg_left (D.le_opNorm _) (norm_nonneg d)
      _ = _ := by ring
  calc
    ‖(m (alpha t (J h + J u) - q) (Q u) +
          m (alpha t (J h + J u) - q) (Q h) + reaction t (J h + J u) -
            d (D (J h + J u))) -
        (m (alpha t (J h + J v) - q) (Q v) +
          m (alpha t (J h + J v) - q) (Q h) + reaction t (J h + J v) -
            d (D (J h + J v)))‖ =
      ‖(m (alpha t (J h + J u) - q) (Q u) -
          m (alpha t (J h + J v) - q) (Q v)) +
        (m (alpha t (J h + J u) - q) (Q h) -
          m (alpha t (J h + J v) - q) (Q h)) +
        (reaction t (J h + J u) - reaction t (J h + J v)) +
        -(d (D (J h + J u)) - d (D (J h + J v)))‖ := by congr 1; module
    _ ≤ ‖m (alpha t (J h + J u) - q) (Q u) -
          m (alpha t (J h + J v) - q) (Q v)‖ +
        ‖m (alpha t (J h + J u) - q) (Q h) -
          m (alpha t (J h + J v) - q) (Q h)‖ +
        ‖reaction t (J h + J u) - reaction t (J h + J v)‖ +
        ‖d (D (J h + J u)) - d (D (J h + J v))‖ := by
      simpa only [norm_neg] using (norm_add₄_le :
        ‖(m (alpha t (J h + J u) - q) (Q u) -
            m (alpha t (J h + J v) - q) (Q v)) +
            (m (alpha t (J h + J u) - q) (Q h) -
              m (alpha t (J h + J v) - q) (Q h)) +
            (reaction t (J h + J u) - reaction t (J h + J v)) +
            (-(d (D (J h + J u)) - d (D (J h + J v))))‖ ≤ _)
    _ ≤ _ := by linarith only [hprincipal, hshift, hreaction, hcorrection]


variable {𝕜 T A X Y Z : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup A] [NormedSpace 𝕜 A]
  [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
  [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [SeminormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem recentered_remainder_zero_norm_le
    (m : A →L[𝕜] Y →L[𝕜] Y)
    (Q : X →L[𝕜] Y) (J : X →L[𝕜] Z) (D : Z →L[𝕜] Y)
    (d : Y →L[𝕜] Y) (q : A)
    (alpha : T → Z → A) (reaction : T → Z → Y)
    {R K : ℝ} (h : X) (t : T)
    (ha_close : ‖alpha t (J h) - q‖ ≤ K * R) :
    ‖recenteredRemainder m Q J D d q alpha reaction h t 0‖ ≤
      ‖m‖ * (K * R) * ‖Q h‖ + ‖reaction t (J h)‖ +
        ‖d‖ * ‖D‖ * ‖J h‖ := by
  simp only [recenteredRemainder, map_zero, add_zero, zero_add]
  calc
    ‖m (alpha t (J h) - q) (Q h) + reaction t (J h) - d (D (J h))‖ ≤
        ‖m (alpha t (J h) - q) (Q h) + reaction t (J h)‖ + ‖d (D (J h))‖ :=
      norm_sub_le _ _
    _ ≤ (‖m (alpha t (J h) - q) (Q h)‖ + ‖reaction t (J h)‖) +
        ‖d (D (J h))‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ (‖m‖ * (K * R) * ‖Q h‖ + ‖reaction t (J h)‖) +
        ‖d‖ * (‖D‖ * ‖J h‖) := by
      apply add_le_add
      · exact add_le_add
          (m.le_of_opNorm₂_le_of_le le_rfl ha_close le_rfl) le_rfl
      · exact (d.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (D.le_opNorm _) (norm_nonneg d))
    _ = _ := by ring

theorem recentered_remainder_operator_identity
    (m : A →L[𝕜] Y →L[𝕜] Y)
    (Q : X →L[𝕜] Y) (J : X →L[𝕜] Z) (D : Z →L[𝕜] Y)
    (d : Y →L[𝕜] Y) (q : A)
    (alpha : T → Z → A) (reaction : T → Z → Y)
    (h : X) (t : T) (v : X) :
    ((m q).comp Q + d.comp (D.comp J)) (h + v) +
        recenteredRemainder m Q J D d q alpha reaction h t v =
      m (alpha t (J h + J v)) (Q (h + v)) + reaction t (J h + J v) := by
  simp only [recenteredRemainder, add_apply,
    ContinuousLinearMap.comp_apply, map_add, map_sub, sub_apply]
  module

end DifferentialGeometry.Analysis.Parabolic
