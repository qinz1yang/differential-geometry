import DifferentialGeometry.Analysis.ODE.Flow.Planar.CompactFlowGerm
import DifferentialGeometry.Analysis.ODE.Flow.Planar.IdentityTangentGerm
import DifferentialGeometry.Topology.Manifold.EuclideanBoundaryCoordinates
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

noncomputable section
open Set Filter Topology Metric
open scoped ContDiff Manifold

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_compact_diffeomorph_realizing_germ_up_to_derivative
    {f : E → E} {U : Set E} (hU : IsOpen U) (h0U : (0 : E) ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (A : E ≃L[ℝ] E)
    (hA : HasFDerivAt f (A : E →L[ℝ] E) 0)
    {V : Set E} (hV : IsOpen V) (h0V : f 0 ∈ V) :
    ∃ J : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      (∀ᶠ x in 𝓝 (0 : E), J (A x + f 0) = f x) ∧
      ∃ K : Set E, IsCompact K ∧ K ⊆ V ∧
        ∀ y, y ∉ K → J y = y ∧ J.symm y = y := by
  let W : Set E := A.symm ⁻¹' U ∩ (fun y ↦ y + f 0) ⁻¹' V
  have hW : IsOpen W := (hU.preimage A.symm.continuous).inter
    (hV.preimage (continuous_id.add continuous_const))
  have h0W : (0 : E) ∈ W := by simp [W, h0U, h0V]
  let g : E → E := fun y ↦ f (A.symm y) - f 0
  have hg : ContDiffOn ℝ ∞ g W :=
    (hf.comp A.symm.contDiff.contDiffOn (fun _ hy ↦ hy.1)).sub contDiffOn_const
  have hg0 : g 0 = 0 := by simp [g]
  have hd : HasFDerivAt g (ContinuousLinearMap.id ℝ E) 0 := by
    have hA' : HasFDerivAt f (A : E →L[ℝ] E) (A.symm 0) := by simpa using hA
    have hd' := (hA'.comp 0 A.symm.hasFDerivAt).sub_const (f 0)
    simpa only [ContinuousLinearEquiv.coe_comp_coe_symm, Function.comp_def] using hd'
  obtain ⟨D, _, _, _, hgerm, _, K, hK, hKW, hfix⟩ :=
    exists_compact_isotopy_realizing_identity_tangent_germ hW h0W hg hg0 hd
  let T := DifferentialGeometry.Topology.translateDiffeomorph (f 0)
  let J := (T.symm.trans (D 1)).trans T
  have hJ (x : E) : J x = D 1 (x - f 0) + f 0 := by
    change D 1 (x + -(f 0)) + f 0 = _
    rw [← sub_eq_add_neg]
  have hJfix (y : E) (hy : y ∉ (fun x ↦ x + f 0) '' K) : J y = y := by
    have hyK : y - f 0 ∉ K := fun h ↦ hy ⟨y - f 0, h, sub_add_cancel _ _⟩
    rw [hJ, (hfix 1 (y - f 0) hyK).1, sub_add_cancel]
  refine ⟨J, ?_, (fun x ↦ x + f 0) '' K,
    hK.image (continuous_id.add continuous_const), ?_, ?_⟩
  · have ht : Tendsto A (𝓝 (0 : E)) (𝓝 0) := by simpa using A.continuous.tendsto 0
    filter_upwards [hgerm.comp_tendsto ht] with x hx
    change D 1 (A x) = g (A x) at hx
    rw [hJ, add_sub_cancel_right, hx]
    simp only [g, A.symm_apply_apply, sub_add_cancel]
  · rintro y ⟨x, hx, rfl⟩
    exact (hKW hx).2
  · intro y hy
    refine ⟨hJfix y hy, ?_⟩
    apply J.injective
    exact (J.apply_symm_apply y).trans (hJfix y hy).symm

theorem exists_compact_diffeomorph_straightening_partialDiffeomorph
    (φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (h0 : (0 : E) ∈ φ.source)
    {V : Set E} (hV : IsOpen V) (h0V : φ 0 ∈ V) :
    ∃ A : E ≃L[ℝ] E, (A : E →L[ℝ] E) = fderiv ℝ φ 0 ∧
      ∃ J : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
        (∀ᶠ x in 𝓝 (0 : E), J (A x + φ 0) = φ x) ∧
        ∃ K : Set E, IsCompact K ∧ K ⊆ V ∧
          ∀ y, y ∉ K → J y = y ∧ J.symm y = y := by
  let A : E ≃L[ℝ] E :=
    (φ.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ h0).mfderivToContinuousLinearEquiv (by simp)
  have hAe : (A : E →L[ℝ] E) = fderiv ℝ φ 0 := by
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ 0 = _
    exact mfderiv_eq_fderiv
  have hA : HasFDerivAt φ (A : E →L[ℝ] E) 0 := by
    rw [hAe]
    exact ((φ.contMDiffOn.contDiffOn.contDiffAt (φ.open_source.mem_nhds h0)).differentiableAt
      (by simp)).hasFDerivAt
  exact ⟨A, hAe, exists_compact_diffeomorph_realizing_germ_up_to_derivative
    φ.open_source h0 φ.contMDiffOn.contDiffOn A hA hV h0V⟩

private theorem exists_compact_diffeomorph_realizing_positive_mul
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∃ D : ℝ ≃ₘ[ℝ] ℝ, (D : ℝ → ℝ) =ᶠ[𝓝 0] (fun x => a * x) ∧
      ∀ x, x ∉ closedBall 0 (2 * r) → D x = x := by
  let v : ℝ → ℝ := fun x => Real.log a * x
  let Γ : ℝ × ℝ → ℝ := fun q => Real.exp (q.2 * Real.log a) * q.1
  have hv : ContDiff ℝ ∞ v := contDiff_const.mul contDiff_id
  have hΓ : Continuous Γ := by fun_prop
  have hzero (x : ℝ) : Γ (x, 0) = x := by simp [Γ]
  have hfixed (t : ℝ) (_ : t ∈ Icc (0 : ℝ) 1) : Γ (0, t) = 0 := by simp [Γ]
  have hderiv (x t : ℝ) (_ : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s => Γ (x, s)) (v (Γ (x, t))) t := by
    have hd := (((hasDerivAt_id t).mul_const (Real.log a)).exp).mul_const x
    convert hd using 1 <;> first | rfl | dsimp [Γ, v]; ring
  obtain ⟨D, _, _, _, hgerm, hfix⟩ :=
    exists_compact_isotopy_realizing_flow_germ hv Γ hΓ hzero hfixed hderiv r hr
  refine ⟨D 1, ?_, fun x hx => (hfix 1 x hx).1⟩
  simpa only [Γ, one_mul, Real.exp_log ha] using hgerm

private theorem exists_diffeomorph_eq_germ_of_deriv_pos
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (h0U : (0 : ℝ) ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (hf0 : f 0 = 0) (hd : 0 < deriv f 0)
    {r : ℝ} (hr : 0 < r) :
    ∃ D : ℝ ≃ₘ[ℝ] ℝ, StrictMono D ∧ (D : ℝ → ℝ) =ᶠ[𝓝 0] f ∧
      ∀ x, x ∉ ball 0 r → D x = x := by
  let A := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (deriv f 0) hd.ne')
  have hA : HasFDerivAt f (A : ℝ →L[ℝ] ℝ) 0 := by
    have he : (A : ℝ →L[ℝ] ℝ) = ContinuousLinearMap.toSpanSingleton ℝ (deriv f 0) := rfl
    rw [he]
    exact ((hf.contDiffAt (hU.mem_nhds h0U)).differentiableAt (by simp)).hasDerivAt.hasFDerivAt
  obtain ⟨J, hJ, K, _, hKV, hJfix⟩ :=
    exists_compact_diffeomorph_realizing_germ_up_to_derivative hU h0U hf A hA isOpen_ball
      (by simpa only [hf0, mem_ball, dist_self] using hr : f 0 ∈ ball 0 r)
  obtain ⟨L, hL, hLfix⟩ := exists_compact_diffeomorph_realizing_positive_mul hd
    (show 0 < r / 4 by positivity)
  let D := L.trans J
  have hD : (D : ℝ → ℝ) =ᶠ[𝓝 0] f := by
    filter_upwards [hJ, hL] with x hxJ hxL
    change J (L x) = f x
    rw [hxL]
    simpa only [hf0, add_zero, A, ContinuousLinearEquiv.unitsEquivAut_apply,
      Units.val_mk0, mul_comm] using hxJ
  have hmono : StrictMono D := by
    rcases D.continuous.strictMono_of_inj D.injective with hm | hm
    · exact hm
    · have hn := hm.antitone.deriv_nonpos (x := (0 : ℝ))
      rw [hD.deriv_eq] at hn
      exact (hd.not_ge hn).elim
  refine ⟨D, hmono, hD, ?_⟩
  intro x hx
  have hxK : x ∉ K := fun h => hx (hKV h)
  have hxL : x ∉ closedBall 0 (2 * (r / 4)) := by
    intro h
    apply hx
    exact (closedBall_subset_ball (by linarith only [hr])) h
  change J (L x) = x
  rw [hLfix x hxL, (hJfix x hxK).1]

private theorem exists_diffeomorph_eq_germ_of_deriv_pos_at
    {f : ℝ → ℝ} {U : Set ℝ} {a r : ℝ}
    (hU : IsOpen U) (haU : a ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (hfa : f a = a) (hd : 0 < deriv f a) (hr : 0 < r) :
    ∃ D : ℝ ≃ₘ[ℝ] ℝ, StrictMono D ∧ (D : ℝ → ℝ) =ᶠ[𝓝 a] f ∧
      ∀ x, x ∉ ball a r → D x = x := by
  let g : ℝ → ℝ := fun x => f (x + a) - a
  let V := (fun x : ℝ => x + a) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_id.add continuous_const)
  have h0V : (0 : ℝ) ∈ V := by simpa only [V, mem_preimage, zero_add] using haU
  have hg : ContDiffOn ℝ ∞ g V :=
    (hf.comp (contDiff_id.add contDiff_const).contDiffOn (fun _ hx => hx)).sub contDiffOn_const
  have hg0 : g 0 = 0 := by simp only [g, zero_add, hfa, sub_self]
  have hdg : deriv g 0 = deriv f a := by
    have hfder : HasDerivAt f (deriv f a) ((0 : ℝ) + a) := by
      simpa only [zero_add] using
        ((hf.contDiffAt (hU.mem_nhds haU)).differentiableAt (by simp)).hasDerivAt
    have hh := (hfder.comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).add_const a)).sub_const a
    simpa only [g, Function.comp_def, id_eq, zero_add, mul_one] using hh.deriv
  obtain ⟨D, hm, hD, hfix⟩ := exists_diffeomorph_eq_germ_of_deriv_pos hV h0V hg hg0
    (hdg ▸ hd) hr
  let E := ((DifferentialGeometry.Topology.translateDiffeomorph (-a)).trans D).trans
    (DifferentialGeometry.Topology.translateDiffeomorph a)
  have hE (x : ℝ) : E x = D (x - a) + a := rfl
  have he0 : (E : ℝ → ℝ) =ᶠ[𝓝 a] f := by
    have ht : Tendsto (fun x : ℝ => x - a) (𝓝 a) (𝓝 0) := by
      simpa only [sub_self] using (show Continuous (fun x : ℝ => x - a) by fun_prop).tendsto a
    filter_upwards [hD.comp_tendsto ht] with x hx
    rw [hE]
    change D (x - a) = f (x - a + a) - a at hx
    rw [hx, sub_add_cancel, sub_add_cancel]
  refine ⟨E, fun x y hxy => by
    rw [hE, hE]; have he := hm (sub_lt_sub_right hxy a); linarith only [he],
    he0, ?_⟩
  intro x hx
  have hx' : x - a ∉ ball 0 r := by
    simpa only [mem_ball, Real.dist_eq, sub_zero] using hx
  rw [hE, hfix _ hx', sub_add_cancel]

theorem exists_diffeomorph_eq_endpoint_germs
    {f₀ f₁ : ℝ → ℝ} {U₀ U₁ : Set ℝ} {a b : ℝ} (hab : a < b)
    (hU₀ : IsOpen U₀) (haU : a ∈ U₀) (hf₀ : ContDiffOn ℝ ∞ f₀ U₀)
    (hU₁ : IsOpen U₁) (hbU : b ∈ U₁) (hf₁ : ContDiffOn ℝ ∞ f₁ U₁)
    (hfa : f₀ a = a) (hfb : f₁ b = b)
    (hd₀ : 0 < deriv f₀ a) (hd₁ : 0 < deriv f₁ b) :
    ∃ D : ℝ ≃ₘ[ℝ] ℝ, StrictMono D ∧ (D : ℝ → ℝ) =ᶠ[𝓝 a] f₀ ∧
      (D : ℝ → ℝ) =ᶠ[𝓝 b] f₁ ∧ D '' Icc a b = Icc a b := by
  let r := (b - a) / 4
  have hr : 0 < r := div_pos (sub_pos.mpr hab) (by norm_num)
  obtain ⟨D₀, hm₀, hD₀, hfix₀⟩ := exists_diffeomorph_eq_germ_of_deriv_pos_at hU₀ haU hf₀ hfa hd₀ hr
  obtain ⟨D₁, hm₁, hD₁, hfix₁⟩ := exists_diffeomorph_eq_germ_of_deriv_pos_at hU₁ hbU hf₁ hfb hd₁ hr
  have hD₀a : D₀ a = a := hD₀.self_of_nhds.trans hfa
  have hD₁b : D₁ b = b := hD₁.self_of_nhds.trans hfb
  have ha : a ∉ closedBall b r := by
    rw [mem_closedBall, Real.dist_eq, abs_of_neg (sub_neg.mpr hab), not_le]
    dsimp only [r]
    linarith only [hab]
  have hb : b ∉ closedBall a r := by
    rw [mem_closedBall, Real.dist_eq, abs_of_pos (sub_pos.mpr hab), not_le]
    dsimp only [r]
    linarith only [hab]
  let D := D₀.trans D₁
  have hg₀ : (D : ℝ → ℝ) =ᶠ[𝓝 a] f₀ := by
    have hn : ∀ᶠ x in 𝓝 a, D₀ x ∉ closedBall b r :=
      D₀.continuous.continuousAt.preimage_mem_nhds
        (isClosed_closedBall.isOpen_compl.mem_nhds (hD₀a.symm ▸ ha))
    filter_upwards [hn, hD₀] with x hx he
    change D₁ (D₀ x) = f₀ x
    rw [hfix₁ _ (fun h => hx (ball_subset_closedBall h)), he]
  have hg₁ : (D : ℝ → ℝ) =ᶠ[𝓝 b] f₁ := by
    filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hb, hD₁] with x hx he
    change D₁ (D₀ x) = f₁ x
    rw [hfix₀ _ (fun h => hx (ball_subset_closedBall h)), he]
  have hm : StrictMono D := hm₁.comp hm₀
  refine ⟨D, hm, hg₀, hg₁, ?_⟩
  rw [D.continuous.continuousOn.image_Icc_of_monotoneOn hab.le (hm.monotone.monotoneOn _),
    hg₀.self_of_nhds.trans hfa, hg₁.self_of_nhds.trans hfb]


end DifferentialGeometry.Analysis
