import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Local surjectivity of boundary-preserving `C¹` maps between half-spaces

`image_mem_nhdsWithin_halfSpace`: let `S = {ℓ ≥ 0}` and `T = {μ ≥ 0}` be closed half-spaces of
Banach spaces (`ℓ n = 1`, `μ ≠ 0`). If `f` maps `S ∩ O` into `T`, maps the boundary hyperplane
`{ℓ = 0} ∩ O` into `{μ = 0}`, is differentiable within `S` with derivative `f'` continuous within
`S` at a boundary point `x₀`, and `f' x₀` is a linear equivalence, then `f '' (S ∩ O)` is a
neighbourhood of `f x₀` within `T`.

Finite order only (no `C^∞` extension across the boundary is used). Proof: `μ ∘ f` has a local
minimum on `S` at `x₀`, so `μ ∘ f' x₀` vanishes on `ker ℓ` and is positive on the inward normal `n`.
The Lipschitz extension `F x = f (π x) + min (ℓ x) 0 • f' x₀ n`, with `π x = x - min (ℓ x) 0 • n`,
approximates `f' x₀` on a ball (mean value inequality on the convex set `S ∩ ball`), hence is onto
a ball around `f x₀` (`surjOn_closedBall_of_nonlinearRightInverse`); the points with `ℓ x < 0`
are sent to `{μ < 0}`, so every point of that ball in `T` is a value of `f` on `S ∩ O`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology NNReal

namespace DifferentialGeometry.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [CompleteSpace E] in
/-- The inward normal derivative of a boundary-preserving map of half-spaces is positive:
`μ ∘ A` vanishes on `ker ℓ` and `0 < μ (A n)`. -/
theorem halfSpace_normal_derivative_pos {ℓ : E →L[ℝ] ℝ} {μ : F →L[ℝ] ℝ} {n : E} (hn : ℓ n = 1)
    (hμ : μ ≠ 0) {f : E → F} {A : E ≃L[ℝ] F} {O : Set E} {x₀ : E} (hO : O ∈ 𝓝 x₀)
    (hx₀ : ℓ x₀ = 0) (hA : HasFDerivWithinAt f (A : E →L[ℝ] F) {x | 0 ≤ ℓ x} x₀)
    (hpos : ∀ x ∈ O, 0 ≤ ℓ x → 0 ≤ μ (f x))
    (hbdry : ∀ x ∈ O, ℓ x = 0 → μ (f x) = 0) :
    (∀ v, ℓ v = 0 → μ (A v) = 0) ∧ 0 < μ (A n) := by
  set S : Set E := {x | 0 ≤ ℓ x} with hS
  have hSc : Convex ℝ S := convex_halfSpace_ge (ℓ : E →ₗ[ℝ] ℝ).isLinear 0
  have hx₀S : x₀ ∈ S := by simp [hS, hx₀]
  have hmin : IsLocalMinOn (fun x => μ (f x)) S x₀ := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds hO, self_mem_nhdsWithin] with x hxO hxS
    rw [hbdry x₀ (mem_of_mem_nhds hO) hx₀]
    exact hpos x hxO hxS
  have hd : HasFDerivWithinAt (fun x => μ (f x)) (μ.comp (A : E →L[ℝ] F)) S x₀ :=
    μ.hasFDerivAt.comp_hasFDerivWithinAt x₀ hA
  have hcone : ∀ v, 0 ≤ ℓ v → 0 ≤ μ (A v) := by
    intro v hv
    have hvS : x₀ + v ∈ S := by simp [hS, hx₀, hv]
    exact hmin.hasFDerivWithinAt_nonneg hd
      (mem_posTangentConeAt_of_segment_subset (hSc.segment_subset hx₀S hvS))
  have hker : ∀ v, ℓ v = 0 → μ (A v) = 0 := by
    intro v hv
    have h1 := hcone v hv.ge
    have h2 := hcone (-v) (by simp [hv])
    rw [map_neg, map_neg] at h2
    linarith
  refine ⟨hker, lt_of_le_of_ne (hcone n (by rw [hn]; exact zero_le_one)) fun h0 => hμ ?_⟩
  have hall : ∀ w, μ (A w) = 0 := by
    intro w
    have hw : ℓ (w - ℓ w • n) = 0 := by simp [hn]
    have hsplit : w = (w - ℓ w • n) + ℓ w • n := by abel
    rw [hsplit, map_add, map_add, hker _ hw, map_smul, map_smul, ← h0, smul_eq_mul, mul_zero,
      add_zero]
  ext y
  simpa using hall (A.symm y)

/-- **Half-space local onto theorem (finite order).** A map of closed half-spaces that is
differentiable within the source half-space, with derivative continuous at a boundary point `x₀`
and invertible there, which maps the source half-space into the target half-space and the
boundary hyperplane into the boundary hyperplane, maps every neighbourhood of `x₀` in the source
half-space onto a neighbourhood of `f x₀` in the target half-space. -/
theorem image_mem_nhdsWithin_halfSpace {ℓ : E →L[ℝ] ℝ} {μ : F →L[ℝ] ℝ} {n : E} (hn : ℓ n = 1)
    (hμ : μ ≠ 0) {f : E → F} {f' : E → E →L[ℝ] F} {A : E ≃L[ℝ] F} {O : Set E} {x₀ : E}
    (hO : IsOpen O) (hx₀O : x₀ ∈ O) (hx₀ : ℓ x₀ = 0)
    (hf : ∀ x ∈ O, 0 ≤ ℓ x → HasFDerivWithinAt f (f' x) {x | 0 ≤ ℓ x} x)
    (hf' : ContinuousWithinAt f' {x | 0 ≤ ℓ x} x₀) (hA : f' x₀ = A)
    (hpos : ∀ x ∈ O, 0 ≤ ℓ x → 0 ≤ μ (f x))
    (hbdry : ∀ x ∈ O, ℓ x = 0 → μ (f x) = 0) :
    f '' ({x | 0 ≤ ℓ x} ∩ O) ∈ 𝓝[{y | 0 ≤ μ y}] (f x₀) := by
  set S : Set E := {x | 0 ≤ ℓ x} with hS
  have hSc : Convex ℝ S := convex_halfSpace_ge (ℓ : E →ₗ[ℝ] ℝ).isLinear 0
  have hx₀S : x₀ ∈ S := by simp [hS, hx₀]
  have hAd : HasFDerivWithinAt f (A : E →L[ℝ] F) S x₀ := hA ▸ hf x₀ hx₀O hx₀S
  obtain ⟨-, hAn⟩ := halfSpace_normal_derivative_pos hn hμ (hO.mem_nhds hx₀O) hx₀ hAd hpos hbdry
  -- constants
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  set N : ℝ := ‖(A.symm : F →L[ℝ] E)‖ with hN
  have hNpos : 0 < N := by
    refine norm_pos_iff.mpr fun h => hn0 ?_
    have := congrArg (fun L : F →L[ℝ] E => L (A n)) h
    simpa using this
  set L : ℝ := 1 + ‖ℓ‖ * ‖n‖ with hL
  have hL1 : 1 ≤ L := by have := mul_nonneg (norm_nonneg ℓ) (norm_nonneg n); linarith
  have hLpos : 0 < L := by linarith
  set c : ℝ := N⁻¹ / 2 with hc
  have hcpos : 0 < c := by positivity
  set ε : ℝ := c / L with hε
  have hεpos : 0 < ε := by positivity
  -- a radius on which the derivative is `ε`-close to `A` and which lies in `O`
  obtain ⟨r₀, hr₀, hr₀O⟩ := Metric.isOpen_iff.mp hO x₀ hx₀O
  obtain ⟨r₁, hr₁, hr₁d⟩ := Metric.continuousWithinAt_iff.mp hf' ε hεpos
  set r' : ℝ := min r₀ r₁ with hr'
  have hr'pos : 0 < r' := lt_min hr₀ hr₁
  have hballO : ball x₀ r' ⊆ O := (ball_subset_ball (min_le_left _ _)).trans hr₀O
  -- the mean value inequality on the convex set `S ∩ ball x₀ r'`
  have hmv : ∀ x ∈ S ∩ ball x₀ r', ∀ y ∈ S ∩ ball x₀ r',
      ‖f y - f x - (A : E →L[ℝ] F) (y - x)‖ ≤ ε * ‖y - x‖ := by
    intro x hx y hy
    refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (f' := f') (φ := (A : E →L[ℝ] F))
      (fun z hz => (hf z (hballO hz.2) hz.1).mono inter_subset_left) (fun z hz => ?_)
      (hSc.inter (convex_ball x₀ r')) hx hy
    rw [← hA, ← dist_eq_norm]
    exact (hr₁d hz.1 (lt_of_lt_of_le (mem_ball.mp hz.2) (min_le_right _ _))).le
  -- the projection onto `S` and the extension
  let π : E → E := fun x => x - min (ℓ x) 0 • n
  have hπℓ : ∀ x, ℓ (π x) = max (ℓ x) 0 := by
    intro x
    simp only [π, map_sub, map_smul, hn, smul_eq_mul, mul_one]
    rcases le_total (ℓ x) 0 with h | h
    · rw [min_eq_left h, max_eq_right h, sub_self]
    · rw [min_eq_right h, max_eq_left h, sub_zero]
  have hπS : ∀ x, π x ∈ S := fun x => by
    change 0 ≤ ℓ (π x)
    rw [hπℓ]
    exact le_max_right _ _
  have hπlip : ∀ x y, ‖π x - π y‖ ≤ L * ‖x - y‖ := by
    intro x y
    have hmin : |min (ℓ x) 0 - min (ℓ y) 0| ≤ ‖ℓ‖ * ‖x - y‖ := by
      refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
      rw [sub_self, abs_zero, max_eq_left (abs_nonneg _), ← map_sub]
      exact (Real.norm_eq_abs _).symm.le.trans (ℓ.le_opNorm _)
    have heq : π x - π y = (x - y) - (min (ℓ x) 0 - min (ℓ y) 0) • n := by
      simp only [π, sub_smul]
      abel
    rw [heq]
    calc ‖(x - y) - (min (ℓ x) 0 - min (ℓ y) 0) • n‖
        ≤ ‖x - y‖ + |min (ℓ x) 0 - min (ℓ y) 0| * ‖n‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖x - y‖ + ‖ℓ‖ * ‖x - y‖ * ‖n‖ := by gcongr
      _ = L * ‖x - y‖ := by rw [hL]; ring
  have hπx₀ : π x₀ = x₀ := by simp [π, hx₀]
  set r : ℝ := r' / L with hr
  have hrpos : 0 < r := by positivity
  have hπball : ∀ x ∈ ball x₀ r, π x ∈ ball x₀ r' := by
    intro x hx
    rw [mem_ball, dist_eq_norm, ← hπx₀]
    calc ‖π x - π x₀‖ ≤ L * ‖x - x₀‖ := hπlip x x₀
      _ < L * r := by
          gcongr
          rw [← dist_eq_norm]
          exact mem_ball.mp hx
      _ = r' := by rw [hr]; field_simp
  have hrr' : r ≤ r' := by
    rw [hr, div_le_iff₀ hLpos]
    nlinarith
  let G : E → F := fun x => f (π x) + min (ℓ x) 0 • (A : E →L[ℝ] F) n
  have hGx₀ : G x₀ = f x₀ := by simp [G, hπx₀, hx₀]
  have happrox : ApproximatesLinearOn G (A : E →L[ℝ] F) (ball x₀ r) ⟨c, hcpos.le⟩ := by
    intro x hx y hy
    have hAxy : (A : E →L[ℝ] F) (x - y) = (A : E →L[ℝ] F) (π x - π y) +
        (min (ℓ x) 0 - min (ℓ y) 0) • (A : E →L[ℝ] F) n := by
      rw [← map_smul, ← map_add]
      congr 1
      simp only [π, sub_smul]
      abel
    have hkey : G x - G y - (A : E →L[ℝ] F) (x - y) =
        f (π x) - f (π y) - (A : E →L[ℝ] F) (π x - π y) := by
      rw [hAxy]
      simp only [G, sub_smul]
      abel
    rw [hkey]
    change _ ≤ c * ‖x - y‖
    calc ‖f (π x) - f (π y) - (A : E →L[ℝ] F) (π x - π y)‖ ≤ ε * ‖π x - π y‖ :=
          hmv _ ⟨hπS y, hπball y hy⟩ _ ⟨hπS x, hπball x hx⟩
      _ ≤ ε * (L * ‖x - y‖) := by gcongr; exact hπlip x y
      _ = c * ‖x - y‖ := by rw [hε]; field_simp
  set ρ : ℝ := r / 2 with hρ
  have hρpos : 0 < ρ := by positivity
  have hsub : closedBall x₀ ρ ⊆ ball x₀ r := closedBall_subset_ball (by linarith)
  have hsurj := happrox.surjOn_closedBall_of_nonlinearRightInverse A.toNonlinearRightInverse
    hρpos.le hsub
  change SurjOn G (closedBall x₀ ρ) (closedBall (G x₀) ((N⁻¹ - c) * ρ)) at hsurj
  rw [hGx₀] at hsurj
  have hκ : 0 < (N⁻¹ - c) * ρ := by
    have : 0 < N⁻¹ - c := by rw [hc]; linarith [inv_pos.mpr hNpos]
    positivity
  rw [mem_nhdsWithin]
  refine ⟨ball (f x₀) ((N⁻¹ - c) * ρ), isOpen_ball, mem_ball_self hκ, ?_⟩
  rintro y ⟨hyb, hyT⟩
  obtain ⟨x, hx, rfl⟩ := hsurj (ball_subset_closedBall hyb)
  have hxr : x ∈ ball x₀ r := hsub hx
  have hxO : x ∈ O := hballO (ball_subset_ball hrr' hxr)
  rcases lt_or_ge (ℓ x) 0 with hneg | hnn
  · exfalso
    have hπO : π x ∈ O := hballO (hπball x hxr)
    have hπ0 : ℓ (π x) = 0 := by rw [hπℓ, max_eq_right hneg.le]
    have hμG : μ (G x) = ℓ x * μ ((A : E →L[ℝ] F) n) := by
      simp only [G, map_add, map_smul, hbdry _ hπO hπ0, min_eq_left hneg.le, smul_eq_mul,
        zero_add]
    have : μ (G x) < 0 := by rw [hμG]; exact mul_neg_of_neg_of_pos hneg hAn
    exact absurd hyT (not_le.mpr this)
  · refine ⟨x, ⟨hnn, hxO⟩, ?_⟩
    simp [G, π, min_eq_right hnn]

end DifferentialGeometry.Analysis
