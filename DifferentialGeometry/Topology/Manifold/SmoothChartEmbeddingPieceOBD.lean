import DifferentialGeometry.Topology.Manifold.SmoothChartSubmanifoldOBD
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.ContinuousInverse

/-!
# A smooth embedded parametrization gives an affine chart piece (lane S-BD2, suffix `_OBD`)

Kernel for the stage bases of the boundary landing. A smooth topological embedding `σ : E → H`
(finite-dimensional spaces) with injective differential at `0` and image `B ∩ O` (`O` open) has,
near `σ 0`, a chart piece of `B` in the form of `SmoothChartSubmanifoldOBD`: a smooth chart map
`κ : H → E` (affine, `κ y = r⁻¹ • (L y - L (σ 0))`), a parametrization `φ : E → H` smooth on the
unit ball, and an open `O' ∋ σ 0` with `κ (φ b) = b` on the ball and `φ (κ y) = y`, `κ y ∈ ball`
on `B ∩ O'`.

* `exists_ball_injective_fderiv_OBD`: an endomorphism field with derivative `id` at `0` has
  injective derivative near `0`;
* **`exists_chartPiece_of_embedding_OBD`**: the chart piece.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Function Topology
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Manifold

variable {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- A smooth endomorphism field with derivative `id` at `0` has injective derivative near `0`. -/
theorem exists_ball_injective_fderiv_OBD {g : E → E} (hg : ContDiff ℝ ∞ g)
    (h0 : fderiv ℝ g 0 = ContinuousLinearMap.id ℝ E) :
    ∃ δ > 0, ∀ x ∈ ball (0 : E) δ, Injective (fderiv ℝ g x) := by
  have hc : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by simp)
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 hc.continuousAt (1 / 2) (by norm_num)
  refine ⟨δ, hδ, fun x hx v w hvw => ?_⟩
  have hT : ‖fderiv ℝ g x - ContinuousLinearMap.id ℝ E‖ < 1 / 2 := by
    have h1 := h (mem_ball.1 hx)
    rwa [dist_eq_norm, h0] at h1
  by_contra hne
  have hpos : 0 < ‖v - w‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have hu : fderiv ℝ g x (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  have h1 : (fderiv ℝ g x - ContinuousLinearMap.id ℝ E) (v - w) = -(v - w) := by simp [hu]
  have h2 := (fderiv ℝ g x - ContinuousLinearMap.id ℝ E).le_opNorm (v - w)
  rw [h1, norm_neg] at h2
  nlinarith

/-- **The chart piece of an embedded parametrization.** -/
theorem exists_chartPiece_of_embedding_OBD {B O : Set H} {σ : E → H}
    (hσ : ContDiff ℝ ∞ σ) (hemb : IsEmbedding σ) (hinj : Injective (fderiv ℝ σ 0))
    (hO : IsOpen O) (hr : range σ = B ∩ O) :
    ∃ (κ : H → E) (φ : E → H) (O' : Set H), ContDiff ℝ ∞ κ ∧ IsOpen O' ∧ σ 0 ∈ O' ∧
      ContDiffOn ℝ ∞ φ (ball 0 1) ∧
      (∀ b ∈ ball (0 : E) 1, φ b ∈ B ∩ O' ∧ κ (φ b) = b) ∧
      ∀ y ∈ B ∩ O', κ y ∈ ball (0 : E) 1 ∧ φ (κ y) = y := by
  classical
  have hL := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hinj
  set L : H →L[ℝ] E := hL.leftInverse with hLdef
  have hLA : ∀ v, L (fderiv ℝ σ 0 v) = v := hL.leftInverse_leftInverse
  set g : E → E := fun x => L (σ x) with hg
  have hgs : ContDiff ℝ ∞ g := L.contDiff.comp hσ
  have hσd : DifferentiableAt ℝ σ 0 := (hσ.differentiable (by simp)) 0
  have hgd : HasFDerivAt g (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) 0 := by
    have h1 : HasFDerivAt g (L.comp (fderiv ℝ σ 0)) 0 :=
      L.hasFDerivAt.comp (0 : E) hσd.hasFDerivAt
    have h2 : L.comp (fderiv ℝ σ 0) = (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) := by
      ext v
      exact hLA v
    rwa [h2] at h1
  have h0 : fderiv ℝ g 0 = ContinuousLinearMap.id ℝ E := by
    rw [hgd.fderiv]
    rfl
  obtain ⟨δ, hδ, hinjδ⟩ := exists_ball_injective_fderiv_OBD hgs h0
  let P : OpenPartialHomeomorph E E := hgs.contDiffAt.toOpenPartialHomeomorph g hgd (by simp)
  have hPc : (P : E → E) = g := rfl
  have h0src : (0 : E) ∈ P.source := hgs.contDiffAt.mem_toOpenPartialHomeomorph_source hgd (by simp)
  set b₀ : E := g 0 with hb₀
  have hb₀t : b₀ ∈ P.target := hgs.contDiffAt.image_mem_toOpenPartialHomeomorph_target hgd (by simp)
  have hPsymm0 : P.symm b₀ = 0 := by
    have := P.left_inv h0src
    rwa [hPc] at this
  have hUopen : IsOpen (P.target ∩ P.symm ⁻¹' ball (0 : E) δ) :=
    P.continuousOn_symm.isOpen_inter_preimage P.open_target isOpen_ball
  have hb₀U : b₀ ∈ P.target ∩ P.symm ⁻¹' ball (0 : E) δ :=
    ⟨hb₀t, by rw [mem_preimage, hPsymm0]; exact mem_ball_self hδ⟩
  obtain ⟨r₀, hr₀, hr₀U⟩ := Metric.isOpen_iff.1 hUopen b₀ hb₀U
  have hr₀ne : r₀ ≠ 0 := hr₀.ne'
  have hball : ∀ b ∈ ball (0 : E) 1, b₀ + r₀ • b ∈ ball b₀ r₀ := by
    intro b hb
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr₀.le]
    have := mem_ball_zero_iff.1 hb
    nlinarith
  have hsymm : ∀ b ∈ ball (0 : E) 1, ContDiffAt ℝ ∞ P.symm (b₀ + r₀ • b) := by
    intro b hb
    have hy := hr₀U (hball b hb)
    have hx : P.symm (b₀ + r₀ • b) ∈ ball (0 : E) δ := hy.2
    have hinj' := hinjδ _ hx
    have hker : LinearMap.ker (fderiv ℝ g (P.symm (b₀ + r₀ • b))).toLinearMap = ⊥ :=
      LinearMap.ker_eq_bot.2 hinj'
    have hrange : LinearMap.range (fderiv ℝ g (P.symm (b₀ + r₀ • b))).toLinearMap = ⊤ :=
      LinearMap.range_eq_top.2 ((LinearMap.injective_iff_surjective).1 hinj')
    let f₀' : E ≃L[ℝ] E :=
      ContinuousLinearEquiv.ofBijective (fderiv ℝ g (P.symm (b₀ + r₀ • b))) hker hrange
    have hf₀' : HasFDerivAt P (f₀' : E →L[ℝ] E) (P.symm (b₀ + r₀ • b)) := by
      have := ((hgs.differentiable (by simp)) (P.symm (b₀ + r₀ • b))).hasFDerivAt
      exact this
    exact P.contDiffAt_symm hy.1 hf₀' hgs.contDiffAt
  have hφs : ContDiffOn ℝ ∞ (fun b : E => σ (P.symm (b₀ + r₀ • b))) (ball 0 1) := by
    intro b hb
    have h1 : ContDiffAt ℝ ∞ (fun b : E => b₀ + r₀ • b) b :=
      (contDiff_const.add (contDiff_const.smul contDiff_id)).contDiffAt
    exact ((hσ.contDiffAt).comp b ((hsymm b hb).comp b h1)).contDiffWithinAt
  have hU₀open : IsOpen (P.source ∩ P ⁻¹' ball b₀ r₀) :=
    P.continuousOn.isOpen_inter_preimage P.open_source isOpen_ball
  obtain ⟨O'', hO'', hO''U⟩ := hemb.isInducing.isOpen_iff.1 hU₀open
  have hU₀ : ∀ x, σ x ∈ O'' ↔ x ∈ P.source ∩ P ⁻¹' ball b₀ r₀ := fun x => by
    rw [← hO''U]
    rfl
  refine ⟨fun y => r₀⁻¹ • (L y - b₀), fun b => σ (P.symm (b₀ + r₀ • b)), O ∩ O'',
    (contDiff_const.smul (L.contDiff.sub contDiff_const)), hO.inter hO'', ?_, hφs, ?_, ?_⟩
  · refine ⟨?_, (hU₀ 0).2 ⟨h0src, ?_⟩⟩
    · have : σ 0 ∈ range σ := mem_range_self 0
      rw [hr] at this
      exact this.2
    · rw [mem_preimage, hPc]
      exact mem_ball_self hr₀
  · intro b hb
    have hy : b₀ + r₀ • b ∈ ball b₀ r₀ := hball b hb
    have hyt : b₀ + r₀ • b ∈ P.target := (hr₀U hy).1
    have hxs : P.symm (b₀ + r₀ • b) ∈ P.source := P.map_target hyt
    have hPx : g (P.symm (b₀ + r₀ • b)) = b₀ + r₀ • b := by
      have := P.right_inv hyt
      rwa [hPc] at this
    have hσr : σ (P.symm (b₀ + r₀ • b)) ∈ range σ := mem_range_self _
    rw [hr] at hσr
    refine ⟨⟨hσr.1, hσr.2, (hU₀ _).2 ⟨hxs, ?_⟩⟩, ?_⟩
    · rw [mem_preimage, hPc, hPx]
      exact hy
    · change r₀⁻¹ • (g (P.symm (b₀ + r₀ • b)) - b₀) = b
      rw [hPx, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr₀ne, one_smul]
  · intro y hy
    have hyr : y ∈ range σ := by rw [hr]; exact ⟨hy.1, hy.2.1⟩
    obtain ⟨x, rfl⟩ := hyr
    obtain ⟨hxs, hxb⟩ := (hU₀ x).1 hy.2.2
    rw [mem_preimage, hPc] at hxb
    have hxb' : ‖g x - b₀‖ < r₀ := by rwa [mem_ball, dist_eq_norm] at hxb
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hr₀.le]
      rw [inv_mul_lt_iff₀ hr₀, mul_one]
      exact hxb'
    · change σ (P.symm (b₀ + r₀ • (r₀⁻¹ • (g x - b₀)))) = σ x
      rw [smul_smul, mul_inv_cancel₀ hr₀ne, one_smul, add_sub_cancel]
      have := P.left_inv hxs
      rw [hPc] at this
      rw [this]

end DifferentialGeometry.Topology.Manifold
