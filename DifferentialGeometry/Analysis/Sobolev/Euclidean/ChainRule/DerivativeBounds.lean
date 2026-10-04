import DifferentialGeometry.Analysis.Sobolev.Euclidean.ChainRule.Defs
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.CompositionBounds
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.Multiply

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

namespace SmoothDiffeoBoundedAtOrder

variable {d : ℕ} {kmax : ℕ} {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (Φ : SmoothDiffeoBoundedAtOrder d Ω Ω' kmax)

lemma comp_toFun_contDiff {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => u (Φ.toFun x)) :=
  hu.comp Φ.toFun_smooth

def derivBoundMaxOne : ℝ := max Φ.derivBound 1

lemma derivBoundMaxOne_pos : 0 < Φ.derivBoundMaxOne := by
  unfold derivBoundMaxOne
  have h1 : (0 : ℝ) < 1 := by norm_num
  exact lt_of_lt_of_le h1 (le_max_right _ _)

lemma derivBoundMaxOne_ge_one : 1 ≤ Φ.derivBoundMaxOne :=
  le_max_right _ _

lemma deriv_bound_le_derivBoundMaxOne : Φ.derivBound ≤ Φ.derivBoundMaxOne :=
  le_max_left _ _

end SmoothDiffeoBoundedAtOrder

lemma SmoothDiffeoBoundedAtOrder.norm_iteratedFDeriv_comp_toFun_le
    {d kmax : ℕ} {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (Φ : SmoothDiffeoBoundedAtOrder d Ω Ω' kmax)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {n : ℕ} (hn : n ≤ kmax) (x : EuclideanSpace ℝ (Fin d)) {C : ℝ}
    (hC : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i u (Φ.toFun x)‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (fun y => u (Φ.toFun y)) x‖ ≤
      n.factorial * C * Φ.derivBoundMaxOne ^ n := by
  have hΦ_smooth_top : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ.toFun := by
    simpa using Φ.toFun_smooth
  have hu_smooth_top : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u := by
    simpa using hu
  have hn_le : (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    have h1 : (n : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
    exact_mod_cast h1
  exact DifferentialGeometry.Analysis.Calculus.norm_iteratedFDeriv_comp_le_max_pow
    (g := Φ.toFun) (f := u) (n := n)
    (N := ((⊤ : ℕ∞) : WithTop ℕ∞)) hu_smooth_top hΦ_smooth_top hn_le x
    hC (fun i _ hi => Φ.iter_deriv_bounded_at i (hi.trans hn) x)

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

namespace SmoothDiffeoBounded

def derivBoundMaxOne {Ω Ω' : Set E} (Φ : SmoothDiffeoBounded d Ω Ω') : ℝ := by
  exact (Φ.toAtOrder (kmax := 0)).derivBoundMaxOne

lemma derivBoundMaxOne_pos {Ω Ω' : Set E} (Φ : SmoothDiffeoBounded d Ω Ω') :
    0 < Φ.derivBoundMaxOne := by
  exact (Φ.toAtOrder (kmax := 0)).derivBoundMaxOne_pos

lemma derivBoundMaxOne_ge_one {Ω Ω' : Set E}
    (Φ : SmoothDiffeoBounded d Ω Ω') :
    1 ≤ Φ.derivBoundMaxOne := by
  exact (Φ.toAtOrder (kmax := 0)).derivBoundMaxOne_ge_one

lemma deriv_bound_le_derivBoundMaxOne {Ω Ω' : Set E}
    (Φ : SmoothDiffeoBounded d Ω Ω') :
    Φ.derivBound ≤ Φ.derivBoundMaxOne := by
  exact (Φ.toAtOrder (kmax := 0)).deriv_bound_le_derivBoundMaxOne

lemma norm_iteratedFDeriv_comp_toFun_le
    {Ω Ω' : Set E} (Φ : SmoothDiffeoBounded d Ω Ω')
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (n : ℕ) (x : E) {C : ℝ}
    (hC : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i u (Φ.toFun x)‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (fun y => u (Φ.toFun y)) x‖ ≤
      n.factorial * C * Φ.derivBoundMaxOne ^ n := by
  exact (Φ.toAtOrder (kmax := n)).norm_iteratedFDeriv_comp_toFun_le
    hu (le_refl n) x hC

lemma comp_toFun_contDiff
    {Ω Ω' : Set E} (Φ : SmoothDiffeoBounded d Ω Ω')
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => u (Φ.toFun x)) := by
  exact (Φ.toAtOrder (kmax := 0)).comp_toFun_contDiff hu

end SmoothDiffeoBounded

variable [NeZero d]

omit [NeZero d] in
theorem norm_iterClassicalPartial_le_iteratedFDeriv :
    ∀ (j : ℕ) (β : Fin j → Fin d) {f : E → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) f → ∀ x : E,
        ‖iterClassicalPartial (d := d) j β f x‖ ≤ ‖iteratedFDeriv ℝ j f x‖ := by
  intro j
  induction j with
  | zero =>
      intro β f _ x
      simp [iterClassicalPartial_zero, norm_iteratedFDeriv_zero]
  | succ j ih =>
      intro β f hf x
      rw [iterClassicalPartial_succ]
      set g : E → ℝ :=
        fun y => (fderiv ℝ f y) (EuclideanSpace.single (β 0) 1) with hg_def
      have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g := by
        have hf_top : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f := by simpa using hf
        have hfd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ f) := by
          refine hf_top.fderiv_right (m := (⊤ : ℕ∞)) ?_
          simp
        have hfd' : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := by simpa using hfd
        exact hfd'.clm_apply contDiff_const
      have h_ih :=
        ih (fun i : Fin j => β i.succ) (f := g) hg_smooth x
      have h_step :=
        norm_iteratedFDeriv_partial_le (d := d) (η := f) hf (β 0) j x
      exact h_ih.trans h_step


omit [NeZero d] in
lemma exists_iter_deriv_bound_of_smooth_compactSupport
    {η : E → ℝ} (hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (k : ℕ) :
    ∃ Mη : ℝ, 0 ≤ Mη ∧ ∀ i, i ≤ k → ∀ y : E, ‖iteratedFDeriv ℝ i η y‖ ≤ Mη := by
  exact hη_compact.exists_bound_iteratedFDeriv (𝕜 := ℝ) hη_smooth k

omit [NeZero d] in
theorem exists_iter_deriv_bound_of_smooth_compactSupport_atOrder
    {f : E → E} (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_compact : HasCompactSupport f) (kmax : ℕ) :
    ∃ Mf : ℝ, 0 < Mf ∧ ∀ i, i ≤ kmax → ∀ y : E, ‖iteratedFDeriv ℝ i f y‖ ≤ Mf := by
  obtain ⟨C, hC, hbound⟩ :=
    hf_compact.exists_bound_iteratedFDeriv (𝕜 := ℝ) hf_smooth kmax
  refine ⟨C + 1, add_pos_of_nonneg_of_pos hC zero_lt_one, ?_⟩
  intro i hi y
  exact (hbound i hi y).trans (le_add_of_nonneg_right zero_le_one)

omit [NeZero d] in
theorem iter_deriv_bound_of_eq_const_offCompactSupport_atOrder
    {T : E → E} (hT_smooth : ContDiff ℝ (⊤ : ℕ∞) T)
    {y₀ : E} (hT_diff_compact : HasCompactSupport (fun y => T y - y₀))
    (kmax : ℕ) :
    ∃ M : ℝ, 0 < M ∧
      ∀ i, i ≤ kmax → ∀ x, ‖iteratedFDeriv ℝ i T x‖ ≤ M := by
  classical
  have hT_diff_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun y => T y - y₀) :=
    hT_smooth.sub contDiff_const
  obtain ⟨M0, hM0_pos, hM0_bound⟩ :=
    exists_iter_deriv_bound_of_smooth_compactSupport_atOrder
      (d := d) hT_diff_smooth hT_diff_compact kmax
  refine ⟨M0 + ‖y₀‖ + 1, by positivity, ?_⟩
  intro i hi x
  rcases i with _ | i
  · rw [norm_iteratedFDeriv_zero]
    have h1 : ‖T x‖ ≤ ‖T x - y₀‖ + ‖y₀‖ := by
      calc ‖T x‖ = ‖(T x - y₀) + y₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖T x - y₀‖ + ‖y₀‖ := norm_add_le _ _
    have h2 : ‖T x - y₀‖ ≤ M0 := by
      have := hM0_bound 0 (Nat.zero_le _) x
      rwa [norm_iteratedFDeriv_zero] at this
    linarith
  · have h_eq : iteratedFDeriv ℝ (i + 1) T x =
        iteratedFDeriv ℝ (i + 1) (fun y => T y - y₀) x := by
      have h_decomp : T = (fun y => T y - y₀) + (fun _ : E => y₀) := by
        funext y; simp
      have hT_diff_smooth_at :
          ContDiffAt ℝ ((i + 1 : ℕ) : WithTop ℕ∞) (fun y => T y - y₀) x :=
        (hT_diff_smooth.of_le (by exact_mod_cast (le_top : ((i + 1 : ℕ) : ℕ∞) ≤ ⊤))
          ).contDiffAt
      have hconst_smooth_at :
          ContDiffAt ℝ ((i + 1 : ℕ) : WithTop ℕ∞) (fun _ : E => y₀) x :=
        contDiff_const.contDiffAt
      rw [h_decomp, iteratedFDeriv_add_apply hT_diff_smooth_at hconst_smooth_at]
      rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero _)]
      simp
    rw [h_eq]
    have h1 := hM0_bound (i + 1) hi x
    have hy0_nn : (0 : ℝ) ≤ ‖y₀‖ := norm_nonneg _
    linarith

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
