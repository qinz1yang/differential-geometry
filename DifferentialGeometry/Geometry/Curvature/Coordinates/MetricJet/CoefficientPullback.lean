import DifferentialGeometry.Geometry.Metric.FiniteLedger.Coefficient

set_option autoImplicit false

noncomputable section

open Set
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

def coefficientPullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : E → E →L[ℝ] E →L[ℝ] ℝ) (Φ : E → E) (y : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (c (Φ y)).bilinearComp (fderiv ℝ Φ y) (fderiv ℝ Φ y)

theorem coefficientPullback_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : E → E →L[ℝ] E →L[ℝ] ℝ) (Φ : E → E) (y u v : E) :
    coefficientPullback c Φ y u v = c (Φ y) (fderiv ℝ Φ y u) (fderiv ℝ Φ y v) :=
  rfl

theorem symm_of_pullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U V : Set E} {b c : E → E →L[ℝ] E →L[ℝ] ℝ} {Φ : E → E}
    (hcsymm : ∀ z ∈ V, ∀ u v : E, c z u v = c z v u) (hΦUV : MapsTo Φ U V)
    (hpull : ∀ y ∈ U, ∀ u v : E, b y u v = c (Φ y) (fderiv ℝ Φ y u) (fderiv ℝ Φ y v)) :
    ∀ y ∈ U, ∀ u v : E, b y u v = b y v u := fun y hy u v =>
  (hpull y hy u v).trans ((hcsymm (Φ y) (hΦUV hy) _ _).trans (hpull y hy v u).symm)

theorem isCoercive_of_pullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U V : Set E} {b c : E → E →L[ℝ] E →L[ℝ] ℝ} {Φ : E → E}
    (hcco : ∀ z ∈ V, IsCoercive (c z)) (hΦUV : MapsTo Φ U V)
    (hΦinv : ∀ y ∈ U, (fderiv ℝ Φ y).IsInvertible)
    (hpull : ∀ y ∈ U, ∀ u v : E, b y u v = c (Φ y) (fderiv ℝ Φ y u) (fderiv ℝ Φ y v)) :
    ∀ y ∈ U, IsCoercive (b y) := by
  intro y hy
  obtain ⟨C, hC, hCu⟩ := hcco (Φ y) (hΦUV hy)
  obtain ⟨M, hM, hle⟩ : ∃ M : ℝ, 0 < M ∧ ∀ u : E, ‖u‖ ≤ M * ‖fderiv ℝ Φ y u‖ := by
    obtain ⟨e, he⟩ := hΦinv y hy
    refine ⟨‖(e.symm : E →L[ℝ] E)‖ + 1, by positivity, fun u => ?_⟩
    have h1 := (e.symm : E →L[ℝ] E).le_opNorm (e u)
    rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] at h1
    rw [← he, ContinuousLinearEquiv.coe_coe]
    exact h1.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
      (norm_nonneg _))
  refine ⟨C * (M⁻¹ * M⁻¹), mul_pos hC (mul_pos (inv_pos.mpr hM) (inv_pos.mpr hM)),
    fun u => ?_⟩
  have hlow : M⁻¹ * ‖u‖ ≤ ‖fderiv ℝ Φ y u‖ :=
    (mul_le_mul_of_nonneg_left (hle u) (inv_nonneg.mpr hM.le)).trans_eq
      (inv_mul_cancel_left₀ hM.ne' _)
  rw [hpull y hy u u]
  calc C * (M⁻¹ * M⁻¹) * ‖u‖ * ‖u‖ = C * (M⁻¹ * ‖u‖) * (M⁻¹ * ‖u‖) := by ring
    _ ≤ C * ‖fderiv ℝ Φ y u‖ * ‖fderiv ℝ Φ y u‖ :=
      mul_le_mul (mul_le_mul_of_nonneg_left hlow hC.le) hlow
        (mul_nonneg (inv_nonneg.mpr hM.le) (norm_nonneg u)) (mul_nonneg hC.le (norm_nonneg _))
    _ ≤ c (Φ y) (fderiv ℝ Φ y u) (fderiv ℝ Φ y u) := hCu _

theorem contDiffOn_of_pullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U V : Set E} (hU : IsOpen U) {b c : E → E →L[ℝ] E →L[ℝ] ℝ} {Φ : E → E} {k : ℕ}
    (hc : ContDiffOn ℝ k c V) (hΦ : ContDiffOn ℝ (k + 1 : ℕ) Φ U) (hΦUV : MapsTo Φ U V)
    (hpull : ∀ y ∈ U, ∀ u v : E, b y u v = c (Φ y) (fderiv ℝ Φ y u) (fderiv ℝ Φ y v)) :
    ContDiffOn ℝ k b U := by
  have h := DifferentialGeometry.Geometry.bilinearComp_fderiv_contDiffOn hU hc hΦ hΦUV
    (Nat.le_add_left 1 k)
  refine (h.of_le (Nat.cast_le.mpr (by omega))).congr fun y hy => ?_
  ext u v
  exact hpull y hy u v

theorem contDiffOn_coefficientPullback_homeomorph_symm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {U V : Set E} (hU : IsOpen U) {c : E → E →L[ℝ] E →L[ℝ] ℝ}
    {κ : E ≃ₜ E} {K : ℕ} (hK : 1 ≤ K) (hc : ContDiffOn ℝ (K - 1 : ℕ) c V)
    (hκ : ContDiff ℝ K κ.symm) (hmaps : MapsTo κ.symm U V) :
    ContDiffOn ℝ (K - 1 : ℕ) (coefficientPullback c κ.symm) U :=
  (DifferentialGeometry.Geometry.bilinearComp_fderiv_contDiffOn hU hc hκ.contDiffOn hmaps
    hK).of_le (Nat.cast_le.mpr (by omega))

theorem coefficientPullback_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U V : Set E} {c : E → E →L[ℝ] E →L[ℝ] ℝ} {Φ : E → E}
    (hcsymm : ∀ z ∈ V, ∀ u v : E, c z u v = c z v u) (hΦUV : MapsTo Φ U V) :
    ∀ y ∈ U, ∀ u v : E, coefficientPullback c Φ y u v = coefficientPullback c Φ y v u :=
  symm_of_pullback hcsymm hΦUV fun _ _ u v => coefficientPullback_apply c Φ _ u v

theorem isCoercive_coefficientPullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U V : Set E} {c : E → E →L[ℝ] E →L[ℝ] ℝ} {Φ : E → E}
    (hcco : ∀ z ∈ V, IsCoercive (c z)) (hΦUV : MapsTo Φ U V)
    (hΦinv : ∀ y ∈ U, (fderiv ℝ Φ y).IsInvertible) :
    ∀ y ∈ U, IsCoercive (coefficientPullback c Φ y) :=
  isCoercive_of_pullback hcco hΦUV hΦinv fun _ _ u v => coefficientPullback_apply c Φ _ u v

theorem isCoercive_of_half_sq_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : E →L[ℝ] E →L[ℝ] ℝ} (h : ∀ v : E, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ B v v) : IsCoercive B :=
  ⟨1 / 2, by norm_num, fun v => by rw [mul_assoc, ← pow_two]; exact h v⟩

theorem eventually_isCoercive_of_continuousAt {Z E : Type*} [TopologicalSpace Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {b : Z → E →L[ℝ] E →L[ℝ] ℝ} {x : Z}
    (hb : ContinuousAt b x) (hco : IsCoercive (b x)) : ∀ᶠ y in 𝓝 x, IsCoercive (b y) := by
  obtain ⟨C, hC, hCu⟩ := hco
  have hev := Filter.Tendsto.eventually (p := fun z => dist z (b x) < C / 2) hb
    (Metric.ball_mem_nhds (b x) (half_pos hC))
  filter_upwards [hev] with y hy
  refine ⟨C / 2, half_pos hC, fun u => ?_⟩
  have h1 : |(b y - b x) u u| ≤ ‖b y - b x‖ * ‖u‖ * ‖u‖ := by
    rw [← Real.norm_eq_abs]
    exact (b y - b x).le_opNorm₂ u u
  have h2 : ‖b y - b x‖ < C / 2 := by
    rw [← dist_eq_norm]
    exact hy
  have h3 : (b y - b x) u u = b y u u - b x u u := rfl
  have h4 := mul_le_mul_of_nonneg_right h2.le (mul_nonneg (norm_nonneg u) (norm_nonneg u))
  linarith [hCu u, neg_abs_le ((b y - b x) u u)]

theorem isInvertible_fderiv_homeomorph_symm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {κ : E ≃ₜ E} {n : ℕ∞ω} (hn : n ≠ 0) (hκ : ContDiff ℝ n κ)
    (hκs : ContDiff ℝ n κ.symm) (y : E) : (fderiv ℝ κ.symm y).IsInvertible := by
  have hd := hκ.differentiable hn
  have hds := hκs.differentiable hn
  have h1 : (fderiv ℝ κ.symm y).comp (fderiv ℝ κ (κ.symm y)) = ContinuousLinearMap.id ℝ E := by
    have h := fderiv_comp (κ.symm y) (hds (κ (κ.symm y))) (hd (κ.symm y))
    rw [Homeomorph.symm_comp_self, fderiv_id, Homeomorph.apply_symm_apply] at h
    exact h.symm
  have h2 : (fderiv ℝ κ (κ.symm y)).comp (fderiv ℝ κ.symm y) = ContinuousLinearMap.id ℝ E := by
    rw [← fderiv_comp y (hd (κ.symm y)) (hds y), Homeomorph.self_comp_symm, fderiv_id]
  exact ⟨ContinuousLinearEquiv.equivOfInverse' (fderiv ℝ κ.symm y) (fderiv ℝ κ (κ.symm y))
    h1 h2, rfl⟩

theorem isInvertible_fderiv_of_contDiffOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (T : OpenPartialHomeomorph E E) {n : ℕ∞ω} (hn : n ≠ 0)
    (hT : ContDiffOn ℝ n T T.source) (hTs : ContDiffOn ℝ n T.symm T.target) {u : E}
    (hu : u ∈ T.source) : (fderiv ℝ T u).IsInvertible := by
  have hTu : T u ∈ T.target := T.map_source hu
  have hd : DifferentiableAt ℝ T u :=
    (hT.contDiffAt (T.open_source.mem_nhds hu)).differentiableAt hn
  have hds : DifferentiableAt ℝ T.symm (T u) :=
    (hTs.contDiffAt (T.open_target.mem_nhds hTu)).differentiableAt hn
  have hd' : DifferentiableAt ℝ T (T.symm (T u)) := by
    rw [T.left_inv hu]
    exact hd
  have h1 : (fderiv ℝ T u).comp (fderiv ℝ T.symm (T u)) = ContinuousLinearMap.id ℝ E := by
    have heq : (⇑T ∘ ⇑T.symm) =ᶠ[𝓝 (T u)] id :=
      Filter.eventually_of_mem (T.open_target.mem_nhds hTu) fun z hz => T.right_inv hz
    have h := fderiv_comp (T u) hd' hds
    rw [heq.fderiv_eq, fderiv_id, T.left_inv hu] at h
    exact h.symm
  have h2 : (fderiv ℝ T.symm (T u)).comp (fderiv ℝ T u) = ContinuousLinearMap.id ℝ E := by
    have heq : (⇑T.symm ∘ ⇑T) =ᶠ[𝓝 u] id :=
      Filter.eventually_of_mem (T.open_source.mem_nhds hu) fun z hz => T.left_inv hz
    rw [← fderiv_comp u hds hd, heq.fderiv_eq, fderiv_id]
  exact ⟨ContinuousLinearEquiv.equivOfInverse' (fderiv ℝ T u) (fderiv ℝ T.symm (T u)) h1 h2,
    rfl⟩

theorem linearIndependent_pair_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : E → E} {x : E} (hinv : (fderiv ℝ Φ x).IsInvertible) {v u : E}
    (hvu : LinearIndependent ℝ ![v, u]) :
    LinearIndependent ℝ ![fderiv ℝ Φ x v, fderiv ℝ Φ x u] := by
  refine LinearIndependent.pair_iff.mpr fun s t hst => LinearIndependent.pair_iff.mp hvu s t ?_
  apply hinv.injective
  rw [map_add, map_smul, map_smul, map_zero]
  exact hst

end DifferentialGeometry.Analysis
