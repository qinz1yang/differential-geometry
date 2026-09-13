import DifferentialGeometry.Analysis.Elliptic.Euclidean.HarmonicComparison
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.HalfDiskBarrier

open Set Filter InnerProductSpace Metric
open scoped Topology

namespace DifferentialGeometry.Analysis

private theorem norm_le_halfDiskBarrier_of_norm_laplacian_le
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f : ℂ → F} {R β δ : ℝ} (hR : 0 < R)
    (hf : ContinuousOn f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hd : ∀ z : ℂ, ‖z‖ < R → 0 < z.im → ContDiffAt ℝ 2 f z)
    (hβ : 0 ≤ β) (hsmall : β * δ < 1)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ R → 0 ≤ z.im → ‖f z‖ ≤ δ)
    (hΔ : ∀ z : ℂ, ‖z‖ < R → 0 < z.im → ‖Laplacian.laplacian f z‖ ≤
      β * (fderiv ℝ f z).hilbertSchmidtInner (fderiv ℝ f z))
    (hzero : ∀ z : ℂ, ‖z‖ ≤ R → z.im = 0 → f z = 0) :
    ∀ z : ℂ, ‖z‖ ≤ R → 0 ≤ z.im →
      ‖f z‖ ≤ (δ + β / (2 * (1 - β * δ)) * δ ^ 2) * halfDiskBarrier R z := by
  let s : Set ℂ := {z | ‖z‖ < R ∧ 0 < z.im}
  let K : Set ℂ := {z | ‖z‖ ≤ R ∧ 0 ≤ z.im}
  let c := β / (2 * (1 - β * δ))
  let A := δ + c * δ ^ 2
  have hδ : 0 ≤ δ := (norm_nonneg (f 0)).trans (hbound 0 (by simpa using hR.le) (by simp))
  have hc : 0 ≤ c := div_nonneg hβ (by linarith)
  have hA : 0 ≤ A := add_nonneg hδ (mul_nonneg hc (sq_nonneg δ))
  have hs : IsOpen s :=
    (isOpen_lt continuous_norm continuous_const).inter (isOpen_lt continuous_const Complex.continuous_im)
  have hK : IsClosed K :=
    (isClosed_le continuous_norm continuous_const).inter (isClosed_le continuous_const Complex.continuous_im)
  have hcl : closure s ⊆ K := closure_minimal (fun _ hz => ⟨hz.1.le, hz.2.le⟩) hK
  have hcompact : IsCompact (closure s) :=
    (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset isClosed_closure (by
      intro z hz
      simpa only [mem_closedBall, dist_zero_right] using (hcl hz).1)
  have hbar (z : ℂ) (hz : z ∈ s) : HarmonicAt (halfDiskBarrier R) z := by
    have hm : (R : ℂ) - z ≠ 0 := by
      intro h
      have hh := congrArg Complex.im h
      simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, zero_sub, neg_eq_zero] at hh
      exact hz.2.ne' hh
    have hp : (R : ℂ) + z ≠ 0 := by
      intro h
      have hh := congrArg Complex.im h
      simp only [Complex.add_im, Complex.ofReal_im, Complex.zero_im, zero_add] at hh
      exact hz.2.ne' hh
    exact harmonicAt_halfDiskBarrier hm hp
  have hb (z : ℂ) (hz : z ∈ K) (he : ‖z‖ = R ∨ z.im = 0) :
      ‖f z‖ + c * ‖f z‖ ^ 2 ≤ A * halfDiskBarrier R z := by
    by_cases hi : z.im = 0
    · rw [hzero z hz.1 hi, norm_zero, halfDiskBarrier_eq_zero_of_im_eq_zero hi]
      simp
    have hip : 0 < z.im := lt_of_le_of_ne hz.2 (Ne.symm hi)
    have hzR : ‖z‖ = R := he.resolve_right hi
    have hpsi : 1 ≤ halfDiskBarrier R z := by
      rw [halfDiskBarrier_eq_div_im_of_norm_eq hzR hip]
      exact (one_le_div hip).2 ((Complex.im_le_norm z).trans hz.1)
    have hn := hbound z hz.1 hz.2
    have hns : ‖f z‖ ^ 2 ≤ δ ^ 2 := (sq_le_sq₀ (norm_nonneg _) hδ).2 hn
    have hsq := mul_le_mul_of_nonneg_left hns hc
    have hmul := mul_le_mul_of_nonneg_left hpsi hA
    dsimp [A] at hmul ⊢
    nlinarith
  have hcmp : ∀ z ∈ closure s, ‖f z‖ + c * ‖f z‖ ^ 2 ≤ A * halfDiskBarrier R z := by
    have hh : HarmonicContOnCl (fun _ : ℂ => (0 : F)) s := harmonicContOnCl_const
    have hB : LowerSemicontinuousOn (fun z => A * halfDiskBarrier R z) (closure s) :=
      (continuous_const.mul continuous_id).comp_lowerSemicontinuousOn
        ((lowerSemicontinuousOn_halfDiskBarrier hR.le).mono (fun _ hz => (hcl hz).2))
        (fun _ _ h => mul_le_mul_of_nonneg_left h hA)
    have hhcmp := norm_sub_le_superharmonic_of_norm_laplacian_le
      (h := fun _ : ℂ => (0 : F)) (B := fun z => A * halfDiskBarrier R z)
      hs hcompact (hf.mono hcl) (fun z hz => hd z hz.1 hz.2) hh hB
      (fun z hz => contDiffAt_const.mul (hbar z hz).1) ?_ hβ hsmall
      (fun z hz => hbound z hz.1.le hz.2.le) (fun z hz => hΔ z hz.1 hz.2) ?_
    · simpa only [sub_zero] using hhcmp
    · intro z hz
      change Laplacian.laplacian (A • halfDiskBarrier R) z ≤ 0
      rw [laplacian_smul A (hbar z hz).1, (hbar z hz).2.self_of_nhds]
      simp
    · intro z hz
      simp only [sub_zero]
      apply hb z (hcl hz.1)
      have hn : z ∉ s := by simpa only [hs.interior_eq] using hz.2
      by_cases he : z.im = 0
      · exact Or.inr he
      · left
        apply le_antisymm (hcl hz.1).1
        by_contra h
        have hm : ‖z‖ < R := lt_of_not_ge h
        exact hn ⟨hm, lt_of_le_of_ne (hcl hz.1).2 (Ne.symm he)⟩
  intro z hz hi
  have hmain : ‖f z‖ + c * ‖f z‖ ^ 2 ≤ A * halfDiskBarrier R z := by
    by_cases hzs : z ∈ s
    · exact hcmp z (subset_closure hzs)
    · apply hb z ⟨hz, hi⟩
      by_cases he : z.im = 0
      · exact Or.inr he
      · left
        apply le_antisymm hz
        by_contra h
        exact hzs ⟨lt_of_not_ge h, lt_of_le_of_ne hi (Ne.symm he)⟩
  have hnon := mul_nonneg hc (sq_nonneg ‖f z‖)
  change ‖f z‖ ≤ A * halfDiskBarrier R z
  linarith

theorem norm_le_mul_im_of_norm_laplacian_le
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f : ℂ → F} {R r β δ : ℝ} (hR : 0 < R) (hr : r < R)
    (hf : ContinuousOn f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hd : ∀ z : ℂ, ‖z‖ < R → 0 < z.im → ContDiffAt ℝ 2 f z)
    (hβ : 0 ≤ β) (hsmall : β * δ < 1)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ R → 0 ≤ z.im → ‖f z‖ ≤ δ)
    (hΔ : ∀ z : ℂ, ‖z‖ < R → 0 < z.im → ‖Laplacian.laplacian f z‖ ≤
      β * (fderiv ℝ f z).hilbertSchmidtInner (fderiv ℝ f z))
    (hzero : ∀ z : ℂ, ‖z‖ ≤ R → z.im = 0 → f z = 0) :
    ∀ z : ℂ, ‖z‖ ≤ r → 0 ≤ z.im →
      ‖f z‖ ≤ (2 * R * (δ + β / (2 * (1 - β * δ)) * δ ^ 2) / (R - r) ^ 2) * z.im := by
  have hδ : 0 ≤ δ := (norm_nonneg (f 0)).trans (hbound 0 (by simpa using hR.le) (by simp))
  have hc : 0 ≤ β / (2 * (1 - β * δ)) := div_nonneg hβ (by linarith)
  have hA : 0 ≤ δ + β / (2 * (1 - β * δ)) * δ ^ 2 :=
    add_nonneg hδ (mul_nonneg hc (sq_nonneg δ))
  intro z hz hi
  calc
    ‖f z‖ ≤ (δ + β / (2 * (1 - β * δ)) * δ ^ 2) * halfDiskBarrier R z :=
      norm_le_halfDiskBarrier_of_norm_laplacian_le hR hf hd hβ hsmall hbound hΔ hzero
        z (hz.trans hr.le) hi
    _ ≤ (δ + β / (2 * (1 - β * δ)) * δ ^ 2) * ((2 * R / (R - r) ^ 2) * z.im) :=
      mul_le_mul_of_nonneg_left (halfDiskBarrier_le hr hz hi) hA
    _ = (2 * R * (δ + β / (2 * (1 - β * δ)) * δ ^ 2) / (R - r) ^ 2) * z.im := by ring

end DifferentialGeometry.Analysis
