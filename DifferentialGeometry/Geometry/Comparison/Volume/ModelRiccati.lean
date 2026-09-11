import DifferentialGeometry.Geometry.Comparison.Volume.Model

noncomputable section

open Filter Set
open scoped Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

theorem weightedModelMean_anti
    {m m' : ℝ → ℝ} {K b : ℝ} {d : ℕ}
    (hd : 0 < d)
    (hadm : ∀ r ∈ Ioo (0 : ℝ) b, modelRadiusAdmissible K r)
    (hm : ∀ r ∈ Ioo (0 : ℝ) b, HasDerivAt m (m' r) r)
    (hmle : ∀ r ∈ Ioo (0 : ℝ) b,
      m' r ≤ -((d : ℝ) * K) - m r ^ 2 / (d : ℝ)) :
    AntitoneOn
      (fun r => modelRadius K r ^ 2 * (m r - modelMeanCurv K d r))
      (Ioo (0 : ℝ) b) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  let F : ℝ → ℝ := fun r =>
    modelRadius K r ^ 2 * (m r - modelMeanCurv K d r)
  let F' : ℝ → ℝ := fun r =>
    2 * modelRadius K r * modelRadiusDeriv K r *
        (m r - modelMeanCurv K d r) +
      modelRadius K r ^ 2 *
        (m' r - (-((d : ℝ) * K) - modelMeanCurv K d r ^ 2 / (d : ℝ)))
  have hF (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) b) : HasDerivAt F (F' r) r := by
    have hs := (hasDerivAt_modelRadius K r).pow 2
    have hz := (hm r hr).sub (hasDerivAt_modelMeanCurv (hadm r hr) hd)
    refine (hs.mul hz).congr_deriv ?_
    simp only [F', Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.sub_apply, Pi.pow_apply]
  have hFle (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) b) : F' r ≤ 0 := by
    let D : ℝ := d
    let S : ℝ := modelRadius K r
    let SD : ℝ := modelRadiusDeriv K r
    let mm : ℝ := m r
    let hh : ℝ := modelMeanCurv K d r
    let mp : ℝ := m' r
    let hp : ℝ := -(D * K) - hh ^ 2 / D
    have hD : 0 < D := by simpa only [D] using hdR
    have hS : 0 < S := by simpa only [S] using modelRadius_pos (hadm r hr)
    have hweight : D * (2 * S * SD) = 2 * S ^ 2 * hh := by
      dsimp only [D, S, SD, hh]
      rw [modelMeanCurv]
      field_simp [ne_of_gt hS]
    have hmp : mp ≤ -(D * K) - mm ^ 2 / D := by
      simpa only [mp, D, mm] using hmle r hr
    have hmpD : D * mp ≤ -(D ^ 2 * K) - mm ^ 2 := by
      calc
        D * mp ≤ D * (-(D * K) - mm ^ 2 / D) :=
          mul_le_mul_of_nonneg_left hmp hD.le
        _ = -(D ^ 2 * K) - mm ^ 2 := by
          field_simp [ne_of_gt hD]
    have hdiffD : D * (mp - hp) ≤ hh ^ 2 - mm ^ 2 := by
      calc
        D * (mp - hp) = D * mp - (-(D ^ 2 * K) - hh ^ 2) := by
          dsimp only [hp]
          field_simp [ne_of_gt hD]
        _ ≤ (-(D ^ 2 * K) - mm ^ 2) - (-(D ^ 2 * K) - hh ^ 2) :=
          sub_le_sub_right hmpD _
        _ = hh ^ 2 - mm ^ 2 := by ring
    have hscaled : S ^ 2 * (D * (mp - hp)) ≤ S ^ 2 * (hh ^ 2 - mm ^ 2) :=
      mul_le_mul_of_nonneg_left hdiffD (sq_nonneg S)
    have hDderiv :
        D * (2 * S * SD * (mm - hh) + S ^ 2 * (mp - hp)) ≤ 0 := by
      calc
        D * (2 * S * SD * (mm - hh) + S ^ 2 * (mp - hp)) =
            (D * (2 * S * SD)) * (mm - hh) + S ^ 2 * (D * (mp - hp)) := by
          ring
        _ = 2 * S ^ 2 * hh * (mm - hh) + S ^ 2 * (D * (mp - hp)) := by
          rw [hweight]
        _ ≤ 2 * S ^ 2 * hh * (mm - hh) + S ^ 2 * (hh ^ 2 - mm ^ 2) := by
          linarith
        _ = -(S ^ 2 * (mm - hh) ^ 2) := by ring
        _ ≤ 0 := neg_nonpos.mpr (mul_nonneg (sq_nonneg S) (sq_nonneg (mm - hh)))
    change 2 * S * SD * (mm - hh) + S ^ 2 * (mp - hp) ≤ 0
    by_contra hpos
    have hprod := mul_pos hD (lt_of_not_ge hpos)
    linarith
  have hdiff : DifferentiableOn ℝ F (Ioo (0 : ℝ) b) := by
    intro r hr
    exact (hF r hr).differentiableAt.differentiableWithinAt
  have hanti : AntitoneOn F (Ioo (0 : ℝ) b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioo 0 b) hdiff.continuousOn ?_ ?_
    · simpa using hdiff
    · intro r hr
      have hr' : r ∈ Ioo (0 : ℝ) b := by simpa using hr
      rw [(hF r hr').deriv]
      exact hFle r hr'
  simpa only [F] using hanti

theorem mean_le_model_of_ratio
    {m m' R : ℝ → ℝ} {K b : ℝ} {d : ℕ}
    (hd : 0 < d)
    (hadm : ∀ r ∈ Ioo (0 : ℝ) b, modelRadiusAdmissible K r)
    (hm : ∀ r ∈ Ioo (0 : ℝ) b, HasDerivAt m (m' r) r)
    (hmle : ∀ r ∈ Ioo (0 : ℝ) b,
      m' r ≤ -((d : ℝ) * K) - m r ^ 2 / (d : ℝ))
    (hR : ∀ r ∈ Ioo (0 : ℝ) b,
      HasDerivAt R (R r * (m r - modelMeanCurv K d r)) r)
    (hRpos : ∀ r ∈ Ioo (0 : ℝ) b, 0 < R r)
    (hRlower : ∃ C : ℝ, 0 < C ∧
      ∀ᶠ r in 𝓝[>] (0 : ℝ), C ≤ R r) :
    ∀ r ∈ Ioo (0 : ℝ) b, m r ≤ modelMeanCurv K d r := by
  have hanti := weightedModelMean_anti hd hadm hm hmle
  intro r hr
  by_contra hle
  have hdiff : 0 < m r - modelMeanCurv K d r := sub_pos.mpr (lt_of_not_ge hle)
  let c : ℝ := modelRadius K r ^ 2 * (m r - modelMeanCurv K d r)
  have hc : 0 < c := mul_pos
    (sq_pos_of_pos (modelRadius_pos (hadm r hr))) hdiff
  have hweighted (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) r) :
      c ≤ modelRadius K x ^ 2 * (m x - modelMeanCurv K d x) := by
    dsimp only [c]
    have hxb : x ∈ Ioo (0 : ℝ) b := ⟨hx.1, hx.2.trans hr.2⟩
    exact hanti hxb hr hx.2.le
  let W : ℝ → ℝ := fun x => modelRadiusDeriv K x / modelRadius K x
  let G : ℝ → ℝ := fun x => R x * Real.exp (c * W x)
  let G' : ℝ → ℝ := fun x =>
    R x * (m x - modelMeanCurv K d x) * Real.exp (c * W x) +
      R x * (Real.exp (c * W x) * (c * (-1 / modelRadius K x ^ 2)))
  have hG (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) r) : HasDerivAt G (G' x) x := by
    have hxb : x ∈ Ioo (0 : ℝ) b := ⟨hx.1, hx.2.trans hr.2⟩
    have hW := hasDerivAt_modelLog (hadm x hxb)
    have hExp := (hW.const_mul c).exp
    refine ((hR x hxb).mul hExp).congr_deriv ?_
    simp only [G', W]
  have hGnonneg (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) r) : 0 ≤ G' x := by
    have hxb : x ∈ Ioo (0 : ℝ) b := ⟨hx.1, hx.2.trans hr.2⟩
    have hS : 0 < modelRadius K x ^ 2 :=
      sq_pos_of_pos (modelRadius_pos (hadm x hxb))
    have hquot : c / modelRadius K x ^ 2 ≤ m x - modelMeanCurv K d x := by
      rw [div_le_iff₀ hS]
      simpa only [mul_comm] using hweighted x hx
    have heq : G' x =
        R x * Real.exp (c * W x) *
          ((m x - modelMeanCurv K d x) - c / modelRadius K x ^ 2) := by
      dsimp only [G']
      ring
    rw [heq]
    exact mul_nonneg
      (mul_nonneg (hRpos x hxb).le (Real.exp_pos _).le)
      (sub_nonneg.mpr hquot)
  have hGdiff : DifferentiableOn ℝ G (Ioo (0 : ℝ) r) := by
    intro x hx
    exact (hG x hx).differentiableAt.differentiableWithinAt
  have hGmono : MonotoneOn G (Ioo (0 : ℝ) r) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioo 0 r) hGdiff.continuousOn ?_ ?_
    · simpa using hGdiff
    · intro x hx
      have hx' : x ∈ Ioo (0 : ℝ) r := by simpa using hx
      rw [(hG x hx').deriv]
      exact hGnonneg x hx'
  let y : ℝ := r / 2
  have hy : y ∈ Ioo (0 : ℝ) r := by
    dsimp only [y]
    constructor <;> linarith [hr.1]
  have hGbound : ∀ᶠ x in 𝓝[>] (0 : ℝ), G x ≤ G y := by
    filter_upwards [Ioo_mem_nhdsGT hy.1] with x hx
    have hxr : x ∈ Ioo (0 : ℝ) r := ⟨hx.1, hx.2.trans hy.2⟩
    exact hGmono hxr hy hx.2.le
  obtain ⟨C, hC, hClower⟩ := hRlower
  have hWtop : Tendsto W (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [W] using modelLog_tendsto K
  have hExpTop : Tendsto (fun x => Real.exp (c * W x))
      (𝓝[>] (0 : ℝ)) atTop :=
    Real.tendsto_exp_atTop.comp (hWtop.const_mul_atTop hc)
  have hGtop : Tendsto G (𝓝[>] (0 : ℝ)) atTop := by
    rw [tendsto_atTop]
    intro A
    filter_upwards [hClower, hExpTop.eventually_ge_atTop (A / C)] with x hxR hxE
    dsimp only [G]
    calc
      A = C * (A / C) := by field_simp [ne_of_gt hC]
      _ ≤ C * Real.exp (c * W x) := mul_le_mul_of_nonneg_left hxE hC.le
      _ ≤ R x * Real.exp (c * W x) :=
        mul_le_mul_of_nonneg_right hxR (Real.exp_pos _).le
  have hlarge := tendsto_atTop.1 hGtop (G y + 1)
  have hfalse : ∀ᶠ x in 𝓝[>] (0 : ℝ), False := by
    filter_upwards [hGbound, hlarge] with x hxBound hxLarge
    linarith
  exact hfalse.exists.elim fun _ hx => hx

theorem density_le_model_of_ratio_anti
    {j : ℝ → ℝ} {K b : ℝ} {d : ℕ}
    (hadm : ∀ t ∈ Ioo (0 : ℝ) b, modelRadiusAdmissible K t)
    (hanti : AntitoneOn (fun t => j t / modelDensity K d t) (Ioo (0 : ℝ) b))
    (hlim : Tendsto (fun t => j t / modelDensity K d t)
      (𝓝[>] (0 : ℝ)) (𝓝 1)) :
    ∀ t ∈ Ioo (0 : ℝ) b, j t ≤ modelDensity K d t := by
  intro t ht
  have hpos : 0 < modelDensity K d t := modelDensity_pos (hadm t ht)
  have hRatioLE : j t / modelDensity K d t ≤ 1 := by
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ),
        j t / modelDensity K d t ≤ j s / modelDensity K d s := by
      filter_upwards [Ioo_mem_nhdsGT ht.1] with s hs
      have hsb : s ∈ Ioo (0 : ℝ) b := ⟨hs.1, hs.2.trans ht.2⟩
      exact hanti hsb ht hs.2.le
    exact ge_of_tendsto hlim hev
  rwa [div_le_one hpos] at hRatioLE

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
