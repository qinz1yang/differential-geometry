import DifferentialGeometry.External.DeGiorgi.FiniteCover

/-!
# Quantitative ball covers in a finite-dimensional inner-product space

The De Giorgi library already proves the needed sharp-enough packing estimate
for the standard Euclidean model.  This file transports it through the
canonical orthonormal-coordinate isometry, so the parabolic heat-potential
argument can stay polymorphic in its finite-dimensional chart model.
-/

noncomputable section

open Set
open scoped RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [Nontrivial V]

/-- A metric ball of radius `r` admits a cover by radius-`rho` balls with a
coarse cardinality bounded only by `r / rho` and the dimension. -/
theorem exists_ball_cover {x : V} {r rho : ℝ} (hr : 0 < r)
    (hrho : 0 < rho) :
    ∃ s : Finset V,
      s.card ≤ Nat.ceil ((4 * r / rho + 1) ^ Module.finrank ℝ V) ∧
      Metric.closedBall x r ⊆ ⋃ c ∈ s, Metric.ball c rho := by
  classical
  let e := (stdOrthonormalBasis ℝ V).repr
  obtain ⟨t, htcard, _, htcover, _⟩ :=
    DeGiorgi.exists_finite_inner_ball_cover_with_card
      (d := Module.finrank ℝ V) (x₀ := e x)
      (r := r) (rho := rho) (R := r + 3 * rho)
      hr hrho (by linarith)
  let s : Finset V := t.image (fun c ↦ e.symm c)
  refine ⟨s, Finset.card_image_le.trans htcard, ?_⟩
  intro y hy
  have hey : e y ∈ Metric.closedBall (e x) r := by
    rw [Metric.mem_closedBall] at hy ⊢
    rw [e.isometry.dist_eq]
    exact hy
  have heycov := htcover hey
  rw [Set.mem_iUnion] at heycov
  obtain ⟨c, heycov⟩ := heycov
  rw [Set.mem_iUnion] at heycov
  obtain ⟨hc, hyc⟩ := heycov
  refine Set.mem_iUnion.2 ⟨e.symm c, Set.mem_iUnion.2 ⟨?_, ?_⟩⟩
  · exact Finset.mem_image.2 ⟨c, hc, rfl⟩
  · rw [Metric.mem_ball] at hyc ⊢
    have hdist := e.isometry.dist_eq y (e.symm c)
    rw [e.apply_symm_apply] at hdist
    rwa [← hdist]

/-- Integer-radius specialization used for unit-width heat annuli.  The
coarse constant `5` turns the ceiling expression into a literal natural
power, which is convenient for the Gaussian series. -/
theorem exists_shell_cover (x : V) {rho : ℝ} (hrho : 0 < rho) (k : ℕ) :
    ∃ s : Finset V,
      s.card ≤ (5 * (k + 1)) ^ Module.finrank ℝ V ∧
      Metric.closedBall x (((k + 1 : ℕ) : ℝ) * rho) ⊆
        ⋃ c ∈ s, Metric.ball c rho := by
  have hr : 0 < ((k + 1 : ℕ) : ℝ) * rho := by positivity
  obtain ⟨s, hcard, hcover⟩ :=
    exists_ball_cover (V := V) (x := x) hr hrho
  refine ⟨s, hcard.trans ?_, hcover⟩
  have hratio :
      4 * (((k + 1 : ℕ) : ℝ) * rho) / rho + 1 =
        4 * ((k + 1 : ℕ) : ℝ) + 1 := by
    field_simp [hrho.ne']
  have hbase :
      4 * (((k + 1 : ℕ) : ℝ) * rho) / rho + 1 ≤
        5 * ((k + 1 : ℕ) : ℝ) := by
    rw [hratio]
    have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    linarith
  have hpow :
      (4 * (((k + 1 : ℕ) : ℝ) * rho) / rho + 1) ^
          Module.finrank ℝ V ≤
        (5 * ((k + 1 : ℕ) : ℝ)) ^ Module.finrank ℝ V :=
    pow_le_pow_left₀ (by positivity) hbase _
  rw [Nat.ceil_le]
  norm_num only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_add, Nat.cast_one]
  exact hpow

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
