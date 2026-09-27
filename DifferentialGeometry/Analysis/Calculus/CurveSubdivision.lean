import DifferentialGeometry.Topology.FiniteSubdivision
import DifferentialGeometry.Topology.Compactness.Nonvanishing
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.Calculus.Deriv.Mul

open Set

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_uniform_positive_functionals {a b : ℝ} {v : ℝ → E}
    (hv : ContinuousOn v (Icc a b)) (hne : ∀ x ∈ Icc a b, v x ≠ 0) :
    ∃ c > 0, ∃ δ > 0, ∀ x ∈ Icc a b, ∃ L : E →L[ℝ] ℝ,
      ‖L‖ = 1 ∧ ∀ y ∈ Icc a b, dist x y < δ → c < L (v y) := by
  obtain ⟨c, hc, hcv⟩ :=
    DifferentialGeometry.Topology.exists_pos_lt_norm_of_isCompact isCompact_Icc hv hne
  obtain ⟨δ, hδ, hunif⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hv) (c / 2) (half_pos hc)
  refine ⟨c / 2, half_pos hc, δ, hδ, ?_⟩
  intro x hx
  obtain ⟨L, hL, hLx⟩ := exists_dual_vector ℝ (v x) (norm_ne_zero_iff.mpr (hne x hx))
  have hLx' : L (v x) = ‖v x‖ := by simpa only [RCLike.ofReal_real_eq_id, id_eq] using hLx
  refine ⟨L, hL, ?_⟩
  intro y hy hxy
  have hclose : ‖v x - v y‖ < c / 2 := by simpa only [dist_eq_norm] using hunif x hx y hy hxy
  have hbound := L.le_opNorm (v x - v y)
  rw [hL, one_mul, map_sub, Real.norm_eq_abs] at hbound
  have hl := (le_abs_self (L (v x) - L (v y))).trans hbound
  rw [hLx'] at hl
  linarith [hcv x hx]

theorem exists_strict_subdivision_positive_functionals
    {a b : ℝ} (hab : a < b) {v : ℝ → E}
    (hv : ContinuousOn v (Icc a b)) (hvne : ∀ x ∈ Icc a b, v x ≠ 0) :
    ∃ (n : ℕ) (t : Fin (n + 1) → ℝ) (U : Fin n → Set ℝ)
      (L : Fin n → E →L[ℝ] ℝ),
      0 < n ∧ StrictMono t ∧ t 0 = a ∧ t (Fin.last n) = b ∧
      ∀ i, IsOpen (U i) ∧ Icc (t i.castSucc) (t i.succ) ⊆ U i ∧
        ‖L i‖ = 1 ∧ ∀ x ∈ U i ∩ Icc a b, 0 < L i (v x) := by
  classical
  have hdual (x : Icc a b) : ∃ f : E →L[ℝ] ℝ, ‖f‖ = 1 ∧ 0 < f (v x) := by
    obtain ⟨f, hf, hfv⟩ := exists_dual_vector ℝ (v x) (norm_ne_zero_iff.mpr (hvne x x.property))
    exact ⟨f, hf, hfv ▸ norm_pos_iff.mpr (hvne x x.property)⟩
  choose f hf hfv using hdual
  let c (x : Icc a b) : Set (Icc a b) := {y | 0 < f x (v y)}
  have hc (x : Icc a b) : IsOpen (c x) :=
    isOpen_lt continuous_const ((f x).continuous.comp hv.domRestrict)
  have hcover : (univ : Set (Icc a b)) ⊆ ⋃ x, c x := by
    intro x _
    exact mem_iUnion.mpr ⟨x, hfv x⟩
  obtain ⟨r, hr0, hrmono, ⟨m, hm⟩, hrcover⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc hab.le hc hcover
  let r' : Fin (m + 1) → ℝ := fun i => r i
  have hr'mono : Monotone r' := fun i j hij => hrmono hij
  obtain ⟨n, t, q, ht, _, ht0, htlast, hseg⟩ :=
    DifferentialGeometry.Geometry.exists_strict_subdiv r' hr'mono
  have hta : t 0 = a := ht0.trans hr0
  have htb : t (Fin.last n) = b := htlast.trans (hm m le_rfl)
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    have heq : (0 : Fin (n + 1)) = Fin.last n := Fin.ext (by simp [hn0])
    have := congrArg t heq
    rw [hta, htb] at this
    exact hab.ne this
  have hlocal (i : Fin n) : ∃ (U : Set ℝ) (L : E →L[ℝ] ℝ),
      IsOpen U ∧ Icc (t i.castSucc) (t i.succ) ⊆ U ∧
        ‖L‖ = 1 ∧ ∀ x ∈ U ∩ Icc a b, 0 < L (v x) := by
    obtain ⟨x, hx⟩ := hrcover (q i).val
    obtain ⟨U, hU, heq⟩ := isOpen_induced_iff.mp (hc x)
    refine ⟨U, f x, hU, ?_, hf x, ?_⟩
    · intro y hy
      rw [(hseg i).1, (hseg i).2] at hy
      have hyab : y ∈ Icc a b :=
        ⟨(r (q i).val).property.1.trans hy.1, hy.2.trans (r ((q i).val + 1)).property.2⟩
      have hyc : (⟨y, hyab⟩ : Icc a b) ∈ c x := hx hy
      rw [← heq] at hyc
      exact hyc
    · intro y hy
      have hyc : (⟨y, hy.2⟩ : Icc a b) ∈ c x := by
        rw [← heq]
        exact hy.1
      exact hyc
  choose U L hU using hlocal
  exact ⟨n, t, U, L, hn, ht, hta, htb, hU⟩

theorem strictMonoOn_chord_interpolation
    {a b : ℝ} (hab : a < b) {γ v : ℝ → E} (L : E →L[ℝ] ℝ)
    (hγ : ContinuousOn γ (Icc a b))
    (hdγ : ∀ x ∈ Ioo a b, HasDerivAt γ (v x) x)
    (hpos : ∀ x ∈ Ioo a b, 0 < L (v x))
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    StrictMonoOn (fun x => L (AffineMap.lineMap (γ x)
      (AffineMap.lineMap (γ a) (γ b) ((x - a) / (b - a))) τ)) (Icc a b) := by
  have hmono : StrictMonoOn (fun x => L (γ x)) (Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b) (L.continuous.comp_continuousOn hγ)
    intro x hx
    rw [interior_Icc] at hx
    rw [(L.hasFDerivAt.comp_hasDerivAt x (hdγ x hx)).deriv]
    exact hpos x hx
  have hends : L (γ a) < L (γ b) := hmono ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab
  rcases eq_or_lt_of_le hτ.1 with hzero | hτpos
  · subst τ
    simpa only [AffineMap.lineMap_apply_zero] using hmono
  intro x hx y hy hxy
  have hcurve := hmono hx hy hxy
  have hratio : (x - a) / (b - a) < (y - a) / (b - a) :=
    div_lt_div_of_pos_right (sub_lt_sub_right hxy a) (sub_pos.mpr hab)
  have hchord : (x - a) / (b - a) * (L (γ b) - L (γ a)) + L (γ a) <
      (y - a) / (b - a) * (L (γ b) - L (γ a)) + L (γ a) :=
    by linarith only [mul_lt_mul_of_pos_right hratio (sub_pos.mpr hends)]
  simp only [AffineMap.lineMap_apply_module, map_add, map_smul, smul_eq_mul]
  have hweighted := add_lt_add_of_le_of_lt
    (mul_le_mul_of_nonneg_left hcurve.le (sub_nonneg.mpr hτ.2))
    (mul_lt_mul_of_pos_left hchord hτpos)
  nlinarith

theorem injOn_chord_interpolation
    {a b : ℝ} (hab : a < b) {γ v : ℝ → E} (L : E →L[ℝ] ℝ)
    (hγ : ContinuousOn γ (Icc a b))
    (hdγ : ∀ x ∈ Ioo a b, HasDerivAt γ (v x) x)
    (hpos : ∀ x ∈ Ioo a b, 0 < L (v x))
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    InjOn (fun x => AffineMap.lineMap (γ x)
      (AffineMap.lineMap (γ a) (γ b) ((x - a) / (b - a))) τ) (Icc a b) := by
  intro x hx y hy heq
  exact (strictMonoOn_chord_interpolation hab L hγ hdγ hpos hτ).injOn hx hy (congrArg L heq)

theorem deriv_chord_interpolation_ne_zero
    {a b : ℝ} (hab : a < b) {γ v : ℝ → E} (L : E →L[ℝ] ℝ)
    (hγ : ContinuousOn γ (Icc a b))
    (hdγ : ∀ x ∈ Ioo a b, HasDerivAt γ (v x) x)
    (hpos : ∀ x ∈ Ioo a b, 0 < L (v x))
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) {x : ℝ} (hx : x ∈ Ioo a b) :
    deriv (fun y => AffineMap.lineMap (γ y)
      (AffineMap.lineMap (γ a) (γ b) ((y - a) / (b - a))) τ) x ≠ 0 := by
  have hmono : StrictMonoOn (fun y => L (γ y)) (Icc a b) := by
    simpa only [AffineMap.lineMap_apply_zero] using
      strictMonoOn_chord_interpolation hab L hγ hdγ hpos (left_mem_Icc.mpr zero_le_one)
  have hends : 0 < L (γ b) - L (γ a) :=
    sub_pos.mpr (hmono ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab)
  have hchord : HasDerivAt
      (fun y => AffineMap.lineMap (γ a) (γ b) ((y - a) / (b - a)))
      ((b - a)⁻¹ • (γ b - γ a)) x := by
    simpa only [Function.comp_def, one_div, id_eq] using
      (AffineMap.hasDerivAt_lineMap (a := γ a) (b := γ b)).scomp x
        (((hasDerivAt_id x).sub_const a).div_const (b - a))
  have hd : HasDerivAt (fun y => AffineMap.lineMap (γ y)
      (AffineMap.lineMap (γ a) (γ b) ((y - a) / (b - a))) τ)
      ((1 - τ) • v x + τ • ((b - a)⁻¹ • (γ b - γ a))) x := by
    convert ((hdγ x hx).const_smul (1 - τ)).add (hchord.const_smul τ) using 1
    ext y
    simp only [AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply]
  rw [hd.deriv]
  have hchordpos : 0 < (b - a)⁻¹ * (L (γ b) - L (γ a)) :=
    mul_pos (inv_pos.mpr (sub_pos.mpr hab)) hends
  have hproject : 0 < L ((1 - τ) • v x + τ • ((b - a)⁻¹ • (γ b - γ a))) := by
    simp only [map_add, map_smul, map_sub, smul_eq_mul]
    rcases lt_or_eq_of_le hτ.2 with hlt | rfl
    · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hlt) (hpos x hx))
        (mul_nonneg hτ.1 hchordpos.le)
    · simpa only [sub_self, zero_mul, one_mul, zero_add] using hchordpos
  intro hzero
  rw [hzero, map_zero] at hproject
  exact lt_irrefl 0 hproject

theorem exists_strict_subdivision_chord_interpolation
    {a b : ℝ} (hab : a < b) {γ v : ℝ → E}
    (hγ : ContinuousOn γ (Icc a b))
    (hdγ : ∀ x ∈ Ioo a b, HasDerivAt γ (v x) x)
    (hv : ContinuousOn v (Icc a b)) (hvne : ∀ x ∈ Icc a b, v x ≠ 0) :
    ∃ (n : ℕ) (t : Fin (n + 1) → ℝ) (U : Fin n → Set ℝ)
      (L : Fin n → E →L[ℝ] ℝ),
      0 < n ∧ StrictMono t ∧ t 0 = a ∧ t (Fin.last n) = b ∧
      ∀ i, IsOpen (U i) ∧ Icc (t i.castSucc) (t i.succ) ⊆ U i ∧
        ‖L i‖ = 1 ∧ (∀ x ∈ U i ∩ Icc a b, 0 < L i (v x)) ∧
        ∀ τ ∈ Icc (0 : ℝ) 1,
          let H := fun x => AffineMap.lineMap (γ x)
            (AffineMap.lineMap (γ (t i.castSucc)) (γ (t i.succ))
              ((x - t i.castSucc) / (t i.succ - t i.castSucc))) τ
          InjOn H (Icc (t i.castSucc) (t i.succ)) ∧
            ∀ x ∈ Ioo (t i.castSucc) (t i.succ), deriv H x ≠ 0 := by
  obtain ⟨n, t, U, L, hn, ht, hta, htb, hlocal⟩ :=
    exists_strict_subdivision_positive_functionals hab hv hvne
  refine ⟨n, t, U, L, hn, ht, hta, htb, ?_⟩
  intro i
  obtain ⟨hU, hcover, hnorm, hpositive⟩ := hlocal i
  refine ⟨hU, hcover, hnorm, hpositive, ?_⟩
  intro τ hτ
  have hai : a ≤ t i.castSucc := by
    rw [← hta]
    exact ht.monotone (Fin.zero_le _)
  have hib : t i.succ ≤ b := by
    rw [← htb]
    exact ht.monotone (Fin.le_last _)
  have hsub : Icc (t i.castSucc) (t i.succ) ⊆ Icc a b := Icc_subset_Icc hai hib
  have hder : ∀ x ∈ Ioo (t i.castSucc) (t i.succ), HasDerivAt γ (v x) x :=
    fun x hx => hdγ x (Ioo_subset_Ioo hai hib hx)
  have hpos : ∀ x ∈ Ioo (t i.castSucc) (t i.succ), 0 < L i (v x) :=
    fun x hx => hpositive x
      ⟨hcover (Ioo_subset_Icc_self hx), hsub (Ioo_subset_Icc_self hx)⟩
  have hti : t i.castSucc < t i.succ := ht Fin.castSucc_lt_succ
  exact ⟨injOn_chord_interpolation hti (L i) (hγ.mono hsub) hder hpos hτ,
    fun x hx => deriv_chord_interpolation_ne_zero hti (L i) (hγ.mono hsub) hder hpos hτ hx⟩

theorem norm_slope_sub_le_of_hasDerivWithinAt
    {a b ε : ℝ} (hab : a < b) {γ v : ℝ → E} {w : E}
    (hγ : ∀ x ∈ Icc a b, HasDerivWithinAt γ (v x) (Icc a b) x)
    (hv : ∀ x ∈ Icc a b, ‖v x - w‖ ≤ ε) :
    ‖slope γ a b - w‖ ≤ ε := by
  have hd (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivWithinAt (fun y => γ y - y • w) (v x - w) (Icc a b) x := by
    convert (hγ x hx).sub ((hasDerivAt_id x).smul_const w).hasDerivWithinAt using 1
    · funext y
      rfl
    · simp only [one_smul]
  have hbound := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    hd hv (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le)
  have halgebra : slope γ a b - w =
      (b - a)⁻¹ • ((γ b - b • w) - (γ a - a • w)) := by
    rw [slope_def_module]
    rw [show (γ b - b • w) - (γ a - a • w) =
      (γ b - γ a) - (b - a) • w by rw [sub_smul]; abel]
    simp only [smul_sub, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hab.ne'), one_smul]
  rw [halgebra, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (sub_pos.mpr hab))]
  calc
    (b - a)⁻¹ * ‖γ b - b • w - (γ a - a • w)‖ ≤
        (b - a)⁻¹ * (ε * ‖b - a‖) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (sub_nonneg.mpr hab.le))
    _ = ε := by
      rw [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hab)]
      field_simp [sub_ne_zero.mpr hab.ne']

theorem exists_uniform_slope_approximation
    {a b : ℝ} {γ v : ℝ → E}
    (hγ : ∀ x ∈ Icc a b, HasDerivWithinAt γ (v x) (Icc a b) x)
    (hv : ContinuousOn v (Icc a b)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ u ∈ Icc a b, ∀ w ∈ Icc a b,
      u < w → w - u < δ → ∀ x ∈ Icc u w, ‖slope γ u w - v x‖ ≤ ε := by
  obtain ⟨δ, hδ, hunif⟩ :=
    Metric.uniformContinuousOn_iff.mp (isCompact_Icc.uniformContinuousOn_of_continuous hv) ε hε
  refine ⟨δ, hδ, fun u hu w hw huw hmesh x hx => ?_⟩
  have hsub : Icc u w ⊆ Icc a b := Icc_subset_Icc hu.1 hw.2
  apply norm_slope_sub_le_of_hasDerivWithinAt huw
    (fun y hy => (hγ y (hsub hy)).mono hsub)
  intro y hy
  have h := hunif y (hsub hy) x (hsub hx) ((Real.dist_le_of_mem_Icc hy hx).trans_lt hmesh)
  simpa only [dist_eq_norm] using h.le

end DifferentialGeometry.Analysis
