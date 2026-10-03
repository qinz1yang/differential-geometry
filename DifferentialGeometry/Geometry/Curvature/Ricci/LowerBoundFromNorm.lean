import DifferentialGeometry.Geometry.Comparison.BonnetMyers.LengthBound

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Riemannian.BonnetMyers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
theorem exists_ricciBoundedBelow_of_normSqRm_le
    (g : SmoothRiemannianMetric I M) {R : ℝ}
    (hRm : ∀ x : M,
      Tensor0SBundle.normSq0S (I := I) g x 4
        (metricRm04At (I := I) (M := M) g x) ≤ R) :
    ∃ q : ℝ, 0 ≤ q ∧
      RicciBoundedBelow (I := I) g
        (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2)) := by
  classical
  by_cases hdim : Module.finrank ℝ E = 1
  · refine ⟨0, le_rfl, ?_⟩
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, neg_zero] using ricciLower_dim1 g hdim
  · have hn0 : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero (NeZero.ne _)
    have hn2 : 2 ≤ Module.finrank ℝ E := by omega
    let q : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt R + 1
    have hq0 : 0 ≤ q := by
      dsimp [q]
      positivity
    have hsqrt : ∀ x : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 4
          (metricRm04At (I := I) (M := M) g x)) ≤ Real.sqrt R := by
      intro x
      exact Real.sqrt_le_sqrt (hRm x)
    have hric := ricciLower_of_rm g hsqrt
    refine ⟨q, hq0, ?_⟩
    intro x v
    have hbase := hric x v
    have hcoef :
        -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) *
            (g.inner x v v) ≤
          -((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt R) *
            (g.inner x v v) := by
      have hsq : (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt R ≤ q ^ 2 := by
        dsimp [q]
        have hbaseq : (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt R ≤
            (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt R + 1 := le_add_of_nonneg_right (by norm_num)
        have hnonneg : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt R + 1 := by positivity
        nlinarith
      have hcoef0 : (Module.finrank ℝ E - 1 : ℕ) ≥ 1 := by omega
      have hcoef1 : (1 : ℝ) ≤ ((Module.finrank ℝ E - 1 : ℕ) : ℝ) := by exact_mod_cast hcoef0
      have hmul : (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt R ≤
          ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2 :=
        le_trans hsq (by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hcoef1 (sq_nonneg q))
      have hinner : 0 ≤ g.inner x v v := by
        rcases eq_or_ne v 0 with hv | hv
        · subst v
          simp
        · exact (g.pos x v hv).le
      exact mul_le_mul_of_nonneg_right (neg_le_neg hmul) hinner
    exact le_trans hcoef hbase

end DifferentialGeometry.Geometry.Riemannian.BonnetMyers
