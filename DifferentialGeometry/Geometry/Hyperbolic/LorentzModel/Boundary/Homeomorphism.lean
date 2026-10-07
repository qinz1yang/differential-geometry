/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.CoarseGeometry.CocompactActions
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Geodesic.QuasigeodesicDivergence

open DifferentialGeometry.ProjectiveOrthogonalGroup Filter

namespace DifferentialGeometry.BoundaryHomeomorph

open DifferentialGeometry.Hyperbolic DifferentialGeometry.HyperbolicFaithful DifferentialGeometry.HyperbolicBoundary
open DifferentialGeometry.BoundaryTopology DifferentialGeometry.HyperbolicConvexity DifferentialGeometry.GromovBoundary
open DifferentialGeometry.AsymptoticRays DifferentialGeometry.GeodesicProjection DifferentialGeometry.BoundaryExtension
open DifferentialGeometry.MorseStability DifferentialGeometry.HyperbolicAction DifferentialGeometry.MorseDivergence

variable {n : ℕ}

theorem gromovCauchy_image_ray {K C : ℝ} {Φ : HUpper n → HUpper n}
    (hΦ : PseudoIsometry.IsPseudoIsometry K C Φ) (hn : 1 ≤ n) (o : HUpper n)
    (ξ : BoundaryH n) :
    GromovCauchy o (fun m : ℕ => Φ (rayTo o ξ (m : ℝ))) :=
  gromovCauchy_image_ray_of_onSegment_tendsto hΦ
    (onSegment_tendsto_of_isPseudoIsometry hΦ hn o ξ)

theorem gromovProduct_image_ge {K C : ℝ} {Φ : HUpper n → HUpper n}
    (hΦ : PseudoIsometry.IsPseudoIsometry K C Φ) (hn : 1 ≤ n) (o x y : HUpper n) :
    K⁻¹ * gromovProduct o x y - (C + morseDist K C + Real.log 2)
      ≤ gromovProduct (Φ o) (Φ x) (Φ y) := by
  have hK : (1:ℝ) ≤ K := hΦ.hK
  have hK0 : (0:ℝ) < K := one_pos.trans_le hK
  have hC0 : (0:ℝ) ≤ C := hΦ.hC
  have hMD0 : (0:ℝ) ≤ morseDist K C := morseDist_nonneg hK hC0
  have hlog : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg one_le_two
  by_cases hΦxy : Φ x = Φ y
  · have e : gromovProduct (Φ o) (Φ x) (Φ y) = dist (Φ o) (Φ x) := by
      rw [hΦxy]; unfold gromovProduct; rw [dist_self]; ring
    rw [e]
    have h1 := hΦ.lower o x
    have h2 : gromovProduct o x y ≤ dist o x := gromovProduct_le_dist_left o x y
    have h3 : K⁻¹ * gromovProduct o x y ≤ K⁻¹ * dist o x :=
      mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hK0.le)
    linarith [h1, h3, hMD0, hlog]
  · by_cases hxy : x = y
    · subst hxy; exact absurd rfl hΦxy
    · set M : ℝ := K⁻¹ * gromovProduct o x y - (C + morseDist K C) with hMdef
      have hseg : ∀ t : ℝ, 0 ≤ t → t ≤ dist (Φ x) (Φ y) →
          M ≤ dist (Φ o) (geodFromTo (Φ x) (Φ y) hΦxy t) := by
        intro t ht0 htT
        have hw : OnSegment (Φ x) (Φ y) (geodFromTo (Φ x) (Φ y) hΦxy t) :=
          onSegment_geodFromTo hΦxy ht0 htT
        have hw' : OnSegment (Φ (geodFromTo x y hxy 0))
            (Φ (geodFromTo x y hxy (dist x y))) (geodFromTo (Φ x) (Φ y) hΦxy t) := by
          rw [geodFromTo_zero hxy, geodFromTo_dist hxy]
          exact hw
        obtain ⟨r, hrP, hrd⟩ := exists_netPoint_le_morseDist (q := geodFromTo x y hxy)
          hΦ hn (fun s t => dist_geodFromTo hxy s t) dist_nonneg hw'
        have hrb := mem_paramNet_bound dist_nonneg hrP
        have h1 : gromovProduct o x y ≤ dist o (geodFromTo x y hxy r) :=
          gromovProduct_le_dist_geodFromTo o x y hxy hrb.1 hrb.2
        have h2 := hΦ.lower o (geodFromTo x y hxy r)
        have h3 := dist_triangle (Φ o) (geodFromTo (Φ x) (Φ y) hΦxy t)
          (Φ (geodFromTo x y hxy r))
        have h4 : K⁻¹ * gromovProduct o x y ≤ K⁻¹ * dist o (geodFromTo x y hxy r) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hK0.le)
        linarith [h2, h3, h4, hrd]
      have h := gromovProduct_ge_of_forall_dist_ge (Φ o) (Φ x) (Φ y) hΦxy hseg
      linarith [h, hMdef, hlog]

noncomputable def bratio (x y : HUpper n) : ℝ := Real.cosh (dist x y) / (tc x.val * tc y.val)

theorem bratio_nonneg (x y : HUpper n) : 0 ≤ bratio x y :=
  div_nonneg (Real.cosh_pos _).le (mul_pos x.future y.future).le

theorem lorB_radial_eq_neg_bratio (x y : HUpper n) :
    lorB (radial x) (radial y) = - bratio x y := by
  rw [lorB_radial_radial,
    show bratio x y = Real.cosh (dist x y) / (tc x.val * tc y.val) from rfl]

theorem bratio_le (x y : HUpper n) :
    bratio x y ≤ 4 * Real.exp (-(2 * gromovProduct basepointH x y)) := by
  have htc_x : tc x.val = Real.cosh (dist basepointH x) := (cosh_dist_basepoint x).symm
  have htc_y : tc y.val = Real.cosh (dist basepointH y) := (cosh_dist_basepoint y).symm
  have hnum : Real.cosh (dist x y) ≤ Real.exp (dist x y) := cosh_le_exp dist_nonneg
  have hdx : Real.exp (dist basepointH x) / 2 ≤ tc x.val := by
    rw [htc_x]; exact exp_div_two_le_cosh _
  have hdy : Real.exp (dist basepointH y) / 2 ≤ tc y.val := by
    rw [htc_y]; exact exp_div_two_le_cosh _
  have hden : (Real.exp (dist basepointH x) / 2) * (Real.exp (dist basepointH y) / 2)
      ≤ tc x.val * tc y.val :=
    mul_le_mul hdx hdy (by positivity) x.future.le
  rw [bratio, div_le_iff₀ (mul_pos x.future y.future)]
  have h1 : Real.exp (dist x y)
      = Real.exp (dist basepointH x) * Real.exp (dist basepointH y)
        * Real.exp (-(2 * gromovProduct basepointH x y)) := by
    rw [show dist x y = dist basepointH x + dist basepointH y
        + (-(2 * gromovProduct basepointH x y)) from by unfold gromovProduct; ring]
    rw [Real.exp_add, Real.exp_add]
  calc Real.cosh (dist x y)
      ≤ Real.exp (dist x y) := hnum
    _ = 4 * Real.exp (-(2 * gromovProduct basepointH x y))
          * ((Real.exp (dist basepointH x) / 2) * (Real.exp (dist basepointH y) / 2)) := by
        rw [h1]; ring
    _ ≤ 4 * Real.exp (-(2 * gromovProduct basepointH x y)) * (tc x.val * tc y.val) :=
        mul_le_mul_of_nonneg_left hden (by positivity)

theorem half_exp_le_bratio (x y : HUpper n) :
    Real.exp (-(2 * gromovProduct basepointH x y)) / 2 ≤ bratio x y := by
  have htc_x : tc x.val = Real.cosh (dist basepointH x) := (cosh_dist_basepoint x).symm
  have htc_y : tc y.val = Real.cosh (dist basepointH y) := (cosh_dist_basepoint y).symm
  have hnum : Real.exp (dist x y) / 2 ≤ Real.cosh (dist x y) := exp_div_two_le_cosh _
  have hdx : tc x.val ≤ Real.exp (dist basepointH x) := by
    rw [htc_x]; exact cosh_le_exp dist_nonneg
  have hdy : tc y.val ≤ Real.exp (dist basepointH y) := by
    rw [htc_y]; exact cosh_le_exp dist_nonneg
  have hden : tc x.val * tc y.val
      ≤ Real.exp (dist basepointH x) * Real.exp (dist basepointH y) :=
    mul_le_mul hdx hdy y.future.le (by positivity)
  rw [bratio, le_div_iff₀ (mul_pos x.future y.future)]
  have h1 : Real.exp (-(2 * gromovProduct basepointH x y))
      * (Real.exp (dist basepointH x) * Real.exp (dist basepointH y))
      = Real.exp (dist x y) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    unfold gromovProduct
    ring
  calc Real.exp (-(2 * gromovProduct basepointH x y)) / 2 * (tc x.val * tc y.val)
      ≤ Real.exp (-(2 * gromovProduct basepointH x y)) / 2
        * (Real.exp (dist basepointH x) * Real.exp (dist basepointH y)) :=
        mul_le_mul_of_nonneg_left hden (by positivity)
    _ = Real.exp (dist x y) / 2 := by rw [div_mul_eq_mul_div, h1]
    _ ≤ Real.cosh (dist x y) := hnum

noncomputable def bratioB (ξ η : BoundaryH n) : ℝ := - lorB ξ.val η.val

theorem sdot_sub_self_eq_two_bratioB (ξ η : BoundaryH n) :
    sdot (ξ.val - η.val) (ξ.val - η.val) = 2 * bratioB ξ η := by
  have h1 : sdot (ξ.val - η.val) (ξ.val - η.val)
      = sdot ξ.val ξ.val - 2 * sdot ξ.val η.val + sdot η.val η.val := by
    rw [sdot_sub_left, sdot_sub_right, sdot_sub_right, sdot_comm η.val ξ.val]; ring
  rw [h1, sdot_self_of_boundary ξ, sdot_self_of_boundary η]
  change 1 - 2 * sdot ξ.val η.val + 1 = 2 * bratioB ξ η
  unfold bratioB lorB
  rw [ξ.tc_eq, η.tc_eq]
  ring

theorem bratioB_nonneg (ξ η : BoundaryH n) : 0 ≤ bratioB ξ η := by
  have h := sdot_self_nonneg (ξ.val - η.val)
  have h2 := sdot_sub_self_eq_two_bratioB ξ η
  linarith [h, h2]

theorem boundary_eq_of_bratioB_eq_zero {ξ η : BoundaryH n} (h : bratioB ξ η = 0) : ξ = η := by
  have h1 : sdot (ξ.val - η.val) (ξ.val - η.val) = 0 := by
    have h2 := sdot_sub_self_eq_two_bratioB ξ η
    linarith [h, h2]
  apply BoundaryH.ext
  funext a
  rcases a with i | k
  · have hi := HUpper.inl_eq_zero_of_sdot_self_eq_zero h1 i
    rw [Pi.sub_apply] at hi
    exact sub_eq_zero.mp hi
  · have hk0 : k = 0 := Subsingleton.elim k 0
    subst hk0
    change tc ξ.val = tc η.val
    rw [ξ.tc_eq, η.tc_eq]

theorem continuous_lorB_pair :
    Continuous (fun p : LorVec n × LorVec n => lorB p.1 p.2) := by
  have heq : (fun p : LorVec n × LorVec n => lorB p.1 p.2)
      = fun p => (∑ i : Fin n, p.1 (Sum.inl i) * p.2 (Sum.inl i))
        - p.1 (Sum.inr 0) * p.2 (Sum.inr 0) := rfl
  rw [heq]
  fun_prop

theorem gromovProduct_cross_tendsto_atTop {x y : ℕ → HUpper n} {ξ : BoundaryH n}
    (hx : ConvergesToBoundary x ξ) (hy : ConvergesToBoundary y ξ) :
    ∀ R : ℝ, ∃ N : ℕ, ∀ m ≥ N, ∀ k ≥ N, R ≤ gromovProduct basepointH (x m) (y k) := by
  have hxr : Tendsto (fun m => radial (x m)) atTop (nhds ξ.val) := hx
  have hyr : Tendsto (fun m => radial (y m)) atTop (nhds ξ.val) := hy
  have hprod : Tendsto (fun p : ℕ × ℕ => (radial (x p.1), radial (y p.2)))
      (atTop ×ˢ atTop) (nhds (ξ.val, ξ.val)) := by
    rw [nhds_prod_eq]
    exact hxr.prodMap hyr
  have hL : Tendsto (fun p : ℕ × ℕ => lorB (radial (x p.1)) (radial (y p.2)))
      (atTop ×ˢ atTop) (nhds (lorB ξ.val ξ.val)) :=
    (continuous_lorB_pair.tendsto _).comp hprod
  rw [ξ.is_null] at hL
  have hρ0 : Tendsto (fun p : ℕ × ℕ => bratio (x p.1) (y p.2)) (atTop ×ˢ atTop) (nhds 0) := by
    have heq : (fun p : ℕ × ℕ => bratio (x p.1) (y p.2))
        = fun p => - lorB (radial (x p.1)) (radial (y p.2)) :=
      funext fun p => by rw [lorB_radial_eq_neg_bratio, neg_neg]
    rw [heq]
    have h2 := hL.neg
    rwa [neg_zero] at h2
  intro R
  set M := max R 0 with hMdef
  have hε : (0:ℝ) < Real.exp (-(2 * M)) / 2 := by positivity
  have hev : ∀ᶠ p in atTop ×ˢ atTop, bratio (x p.1) (y p.2) < Real.exp (-(2 * M)) / 2 :=
    hρ0.eventually (Iio_mem_nhds hε)
  rw [Filter.prod_atTop_atTop_eq] at hev
  obtain ⟨⟨N₁, N₂⟩, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max N₁ N₂, fun m hm k hk => ?_⟩
  have hge : (N₁, N₂) ≤ (m, k) :=
    Prod.le_def.mpr ⟨le_trans (le_max_left _ _) hm, le_trans (le_max_right _ _) hk⟩
  have hbr : bratio (x m) (y k) < Real.exp (-(2 * M)) / 2 := hN (m, k) hge
  have h1 := half_exp_le_bratio (x m) (y k)
  have h2 : Real.exp (-(2 * gromovProduct basepointH (x m) (y k))) < Real.exp (-(2 * M)) := by
    linarith [h1, hbr]
  rw [Real.exp_lt_exp] at h2
  have h3 : M < gromovProduct basepointH (x m) (y k) := by linarith [h2]
  exact le_of_lt (lt_of_le_of_lt (le_max_left R 0) h3)

theorem eq_of_gromovProduct_cross_tendsto {x y : ℕ → HUpper n} {ξ η : BoundaryH n}
    (hx : ConvergesToBoundary x ξ) (hy : ConvergesToBoundary y η)
    (hcross : ∀ R : ℝ, ∃ N : ℕ, ∀ m ≥ N, ∀ k ≥ N,
      R ≤ gromovProduct basepointH (x m) (y k)) :
    ξ = η := by
  have hxr : Tendsto (fun m => radial (x m)) atTop (nhds ξ.val) := hx
  have hyr : Tendsto (fun m => radial (y m)) atTop (nhds η.val) := hy
  have hprod : Tendsto (fun p : ℕ × ℕ => (radial (x p.1), radial (y p.2)))
      (atTop ×ˢ atTop) (nhds (ξ.val, η.val)) := by
    rw [nhds_prod_eq]
    exact hxr.prodMap hyr
  have hconv : Tendsto (fun p : ℕ × ℕ => lorB (radial (x p.1)) (radial (y p.2)))
      (atTop ×ˢ atTop) (nhds (lorB ξ.val η.val)) :=
    (continuous_lorB_pair.tendsto _).comp hprod
  have hzero : Tendsto (fun p : ℕ × ℕ => lorB (radial (x p.1)) (radial (y p.2)))
      (atTop ×ˢ atTop) (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set R := Real.log (4 / ε) / 2 + 1 with hRdef
    obtain ⟨N, hN⟩ := hcross R
    have hbig : 4 * Real.exp (-(2 * R)) < ε := by
      have hε0 : (0:ℝ) < 4 / ε := by positivity
      have h1 : Real.exp (-(2 * R)) = Real.exp (-2) * (ε / 4) := by
        have e1 : -(2 * R) = (-2) + (- Real.log (4 / ε)) := by rw [hRdef]; ring
        rw [e1, Real.exp_add, Real.exp_neg (Real.log (4 / ε)), Real.exp_log hε0, inv_div]
      rw [h1]
      have h4 : Real.exp (-2 : ℝ) < 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_strictMono (by norm_num)
      calc 4 * (Real.exp (-2) * (ε / 4)) = Real.exp (-2) * ε := by ring
        _ = ε * Real.exp (-2) := by ring
        _ < ε * 1 := mul_lt_mul_of_pos_left h4 hε
        _ = ε := mul_one ε
    rw [Filter.prod_atTop_atTop_eq]
    refine Filter.eventually_atTop.mpr ⟨(N, N), fun p hp => ?_⟩
    obtain ⟨hp1, hp2⟩ := Prod.le_def.mp hp
    have hR := hN p.1 hp1 p.2 hp2
    have hbr := bratio_le (x p.1) (y p.2)
    have hnn := bratio_nonneg (x p.1) (y p.2)
    have hle : 4 * Real.exp (-(2 * gromovProduct basepointH (x p.1) (y p.2)))
        ≤ 4 * Real.exp (-(2 * R)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hR])) (by norm_num)
    rw [Real.dist_eq, sub_zero]
    have heq2 : lorB (radial (x p.1)) (radial (y p.2)) = - bratio (x p.1) (y p.2) :=
      lorB_radial_eq_neg_bratio _ _
    rw [heq2, abs_neg, abs_of_nonneg hnn]
    linarith [hbr, hle, hbig]
  have h0 : lorB ξ.val η.val = 0 := tendsto_nhds_unique hconv hzero
  exact boundary_eq_of_bratioB_eq_zero (by change - lorB ξ.val η.val = 0; rw [h0, neg_zero])

theorem bExt_comp {K₂ C₂ : ℝ} {Φ Ψ : HUpper n → HUpper n}
    (hΨ : PseudoIsometry.IsPseudoIsometry K₂ C₂ Ψ)
    (hGCΦ : ∀ (o : HUpper n) (ξ : BoundaryH n),
      GromovCauchy o (fun m : ℕ => Φ (rayTo o ξ (m : ℝ))))
    (hGCΨ : ∀ (o : HUpper n) (ξ : BoundaryH n),
      GromovCauchy o (fun m : ℕ => Ψ (rayTo o ξ (m : ℝ))))
    (hGCΦΨ : ∀ (o : HUpper n) (ξ : BoundaryH n),
      GromovCauchy o (fun m : ℕ => (Ψ ∘ Φ) (rayTo o ξ (m : ℝ))))
    (hn : 1 ≤ n) :
    bExt hGCΦΨ = bExt hGCΨ ∘ bExt hGCΦ := by
  funext ξ
  set η := bExt hGCΦ ξ with hηdef
  have hx : ConvergesToBoundary (fun m : ℕ => Φ (rayTo basepointH ξ (m : ℝ))) η :=
    bExt_spec hGCΦ ξ
  have hy : ConvergesToBoundary (fun m : ℕ => rayTo basepointH η (m : ℝ)) η := tendsto_rayTo _ _
  have hx' : ConvergesToBoundary (fun m : ℕ => (Ψ ∘ Φ) (rayTo basepointH ξ (m : ℝ)))
      (bExt hGCΦΨ ξ) := bExt_spec hGCΦΨ ξ
  have hy' : ConvergesToBoundary (fun m : ℕ => Ψ (rayTo basepointH η (m : ℝ)))
      (bExt hGCΨ η) := bExt_spec hGCΨ η
  have hK0 : (0:ℝ) < K₂ := one_pos.trans_le hΨ.hK
  have hcross : ∀ R : ℝ, ∃ N : ℕ, ∀ m ≥ N, ∀ k ≥ N,
      R ≤ gromovProduct basepointH ((Ψ ∘ Φ) (rayTo basepointH ξ (m : ℝ)))
        (Ψ (rayTo basepointH η (k : ℝ))) := by
    intro R
    set C₁' : ℝ := C₂ + morseDist K₂ C₂ + Real.log 2 + dist basepointH (Ψ basepointH)
      with hC₁'
    obtain ⟨N, hN⟩ := gromovProduct_cross_tendsto_atTop hx hy (K₂ * (R + C₁'))
    refine ⟨N, fun m hm k hk => ?_⟩
    have h1 := hN m hm k hk
    have h2 := gromovProduct_image_ge hΨ hn basepointH (Φ (rayTo basepointH ξ (m : ℝ)))
      (rayTo basepointH η (k : ℝ))
    have h3 := abs_gromovProduct_sub_le basepointH (Ψ basepointH)
      ((Ψ ∘ Φ) (rayTo basepointH ξ (m : ℝ))) (Ψ (rayTo basepointH η (k : ℝ)))
    rw [abs_le] at h3
    have h4 : (K₂:ℝ)⁻¹ * (K₂ * (R + C₁')) ≤ K₂⁻¹ * gromovProduct basepointH
        (Φ (rayTo basepointH ξ (m : ℝ))) (rayTo basepointH η (k : ℝ)) :=
      mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hK0.le)
    rw [← mul_assoc, inv_mul_cancel₀ hK0.ne', one_mul] at h4
    have h5 : gromovProduct (Ψ basepointH) ((Ψ ∘ Φ) (rayTo basepointH ξ (m : ℝ)))
        (Ψ (rayTo basepointH η (k : ℝ)))
        ≤ gromovProduct basepointH ((Ψ ∘ Φ) (rayTo basepointH ξ (m : ℝ)))
          (Ψ (rayTo basepointH η (k : ℝ))) + dist basepointH (Ψ basepointH) := by
      linarith [h3.1, h3.2]
    have h2' : K₂⁻¹ * gromovProduct basepointH (Φ (rayTo basepointH ξ (m : ℝ)))
        (rayTo basepointH η (k : ℝ)) - (C₂ + morseDist K₂ C₂ + Real.log 2)
        ≤ gromovProduct (Ψ basepointH) ((Ψ ∘ Φ) (rayTo basepointH ξ (m : ℝ)))
          (Ψ (rayTo basepointH η (k : ℝ))) := h2
    linarith [h4, h5, h2', hC₁']
  exact eq_of_gromovProduct_cross_tendsto hx' hy' hcross

theorem bExt_eq_of_bounded {Φ₁ Φ₂ : HUpper n → HUpper n}
    (hGC₁ : ∀ (o : HUpper n) (ξ : BoundaryH n),
      GromovCauchy o (fun m : ℕ => Φ₁ (rayTo o ξ (m : ℝ))))
    (hGC₂ : ∀ (o : HUpper n) (ξ : BoundaryH n),
      GromovCauchy o (fun m : ℕ => Φ₂ (rayTo o ξ (m : ℝ))))
    {B : ℝ} (hB : ∀ x, dist (Φ₁ x) (Φ₂ x) ≤ B) :
    bExt hGC₁ = bExt hGC₂ := by
  funext ξ
  have hx : ConvergesToBoundary (fun m : ℕ => Φ₁ (rayTo basepointH ξ (m : ℝ)))
      (bExt hGC₁ ξ) := bExt_spec hGC₁ ξ
  have hy : ConvergesToBoundary (fun m : ℕ => Φ₂ (rayTo basepointH ξ (m : ℝ)))
      (bExt hGC₂ ξ) := bExt_spec hGC₂ ξ
  have hesc : Tendsto (fun m : ℕ => dist basepointH (Φ₂ (rayTo basepointH ξ (m : ℝ))))
      atTop atTop := (hGC₂ basepointH ξ).1
  have hyx : ConvergesToBoundary (fun m : ℕ => Φ₂ (rayTo basepointH ξ (m : ℝ)))
      (bExt hGC₁ ξ) := ConvergesToBoundary.of_bounded_dist hx (fun m => hB _) hesc
  exact convergesToBoundary_unique hyx hy

theorem gromovCauchy_rayTo (o : HUpper n) (ξ : BoundaryH n) :
    GromovCauchy o (fun m : ℕ => rayTo o ξ (m : ℝ)) := by
  constructor
  · have heq : (fun m : ℕ => dist o (rayTo o ξ (m : ℝ))) = fun m : ℕ => (m : ℝ) := by
      funext m
      rw [dist_rayTo_self, abs_of_nonneg (Nat.cast_nonneg m)]
    rw [heq]
    exact tendsto_natCast_atTop_atTop
  · intro R
    refine ⟨Nat.ceil R, fun m hm k hk => ?_⟩
    have hmR : R ≤ (m : ℝ) := (Nat.le_ceil R).trans (Nat.cast_le.mpr hm)
    have hkR : R ≤ (k : ℝ) := (Nat.le_ceil R).trans (Nat.cast_le.mpr hk)
    unfold gromovProduct
    rw [dist_rayTo_self, dist_rayTo_self, dist_rayTo, abs_of_nonneg (Nat.cast_nonneg m),
      abs_of_nonneg (Nat.cast_nonneg k)]
    rcases le_total (m : ℝ) (k : ℝ) with hmk | hmk
    · rw [abs_of_nonpos (by linarith : (m : ℝ) - (k : ℝ) ≤ 0)]
      have h : ((m : ℝ) + (k : ℝ) - -((m : ℝ) - (k : ℝ))) / 2 = (m : ℝ) := by ring
      rw [h]
      exact hmR
    · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (m : ℝ) - (k : ℝ))]
      have h : ((m : ℝ) + (k : ℝ) - ((m : ℝ) - (k : ℝ))) / 2 = (k : ℝ) := by ring
      rw [h]
      exact hkR

theorem bExt_id (hGC : ∀ (o : HUpper n) (ξ : BoundaryH n),
    GromovCauchy o (fun m : ℕ => id (rayTo o ξ (m : ℝ)))) :
    bExt hGC = id := by
  funext ξ
  have h1 : ConvergesToBoundary (fun m : ℕ => id (rayTo basepointH ξ (m : ℝ)))
      (bExt hGC ξ) := bExt_spec _ ξ
  have h2 : ConvergesToBoundary (fun m : ℕ => id (rayTo basepointH ξ (m : ℝ))) ξ :=
    tendsto_rayTo _ _
  exact convergesToBoundary_unique h1 h2

theorem lorB_eTime_spatialEmbed (u : EuclideanSpace ℝ (Fin n)) :
    lorB (eTime : LorVec n) (spatialEmbed u) = 0 := by
  change sdot (eTime : LorVec n) (spatialEmbed u) - tc (eTime : LorVec n) * tc (spatialEmbed u) = 0
  rw [sdot_eTime_spatialEmbed, tc_eTime, tc_spatialEmbed]
  norm_num

theorem lorB_spatialEmbed_spatialEmbed (u v : EuclideanSpace ℝ (Fin n)) :
    lorB (spatialEmbed u) (spatialEmbed v) = sdot (spatialEmbed u) (spatialEmbed v) := by
  change sdot (spatialEmbed u) (spatialEmbed v) - tc (spatialEmbed u) * tc (spatialEmbed v) = _
  rw [tc_spatialEmbed]
  norm_num

theorem sdot_spatialEmbed_spatial (ξ η : BoundaryH n) :
    sdot (spatialEmbed (spatial ξ)) (spatialEmbed (spatial η)) = sdot ξ.val η.val := by
  rw [sdot_spatialEmbed]
  show (∑ i : Fin n, (spatial ξ) i * (spatial η) i) = sdot ξ.val η.val
  rw [Finset.sum_congr rfl (fun i _ => by rw [spatial_apply, spatial_apply])]
  rfl

theorem cosh_dist_geodesicRay_geodesicRay (ξ η : BoundaryH n) (s t : ℝ) :
    Real.cosh (dist (geodesicRay ξ s) (geodesicRay η t))
      = Real.cosh s * Real.cosh t - Real.sinh s * Real.sinh t * sdot ξ.val η.val := by
  have h := cosh_dist (geodesicRay ξ s) (geodesicRay η t)
  rw [h]
  change - lorB (Real.cosh s • (eTime : LorVec n) + Real.sinh s • spatialEmbed (spatial ξ))
      (Real.cosh t • (eTime : LorVec n) + Real.sinh t • spatialEmbed (spatial η)) = _
  have e1 : lorB (Real.cosh s • (eTime : LorVec n) + Real.sinh s • spatialEmbed (spatial ξ))
      (Real.cosh t • (eTime : LorVec n) + Real.sinh t • spatialEmbed (spatial η))
      = Real.cosh s * Real.cosh t * lorB (eTime : LorVec n) eTime
        + Real.cosh s * Real.sinh t * lorB (eTime : LorVec n) (spatialEmbed (spatial η))
        + Real.sinh s * Real.cosh t * lorB (spatialEmbed (spatial ξ)) (eTime : LorVec n)
        + Real.sinh s * Real.sinh t * lorB (spatialEmbed (spatial ξ)) (spatialEmbed (spatial η)) := by
    simp only [lorB_add_left, lorB_add_right, lorB_smul_left, lorB_smul_right]
    ring
  rw [e1, lorB_eTime, lorB_eTime_spatialEmbed, lorB_spatialEmbed_spatialEmbed,
    sdot_spatialEmbed_spatial, lorB_comm (spatialEmbed (spatial ξ)) (eTime : LorVec n),
    lorB_eTime_spatialEmbed]
  ring

theorem sinh_le_exp_div_two (t : ℝ) : Real.sinh t ≤ Real.exp t / 2 := by
  rw [Real.sinh_eq]
  have h := Real.exp_pos (-t)
  linarith [h]

theorem exp_neg_gromov_geodesicRay_le (ξ η : BoundaryH n) (m : ℕ) :
    Real.exp (-(2 * gromovProduct basepointH (geodesicRay ξ (m : ℝ)) (geodesicRay η (m : ℝ))))
      ≤ 2 * Real.exp (-(2 * (m : ℝ))) + bratioB ξ η / 2 := by
  have hm0 : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  set am := geodesicRay ξ (m : ℝ) with hamdef
  set bm := geodesicRay η (m : ℝ) with hbmdef
  have hρ0 : 0 ≤ bratioB ξ η := bratioB_nonneg ξ η
  have hdam : dist basepointH am = (m : ℝ) := by
    rw [hamdef, HyperbolicGeometry.dist_basepoint_geodesicRay, abs_of_nonneg hm0]
  have hdbm : dist basepointH bm = (m : ℝ) := by
    rw [hbmdef, HyperbolicGeometry.dist_basepoint_geodesicRay, abs_of_nonneg hm0]
  have hgrom : -(2 * gromovProduct basepointH am bm) = dist am bm + (-(2 * (m : ℝ))) := by
    unfold gromovProduct
    rw [hdam, hdbm]
    ring
  rw [hgrom, Real.exp_add]
  have hexp : Real.exp (dist am bm) ≤ 2 * Real.cosh (dist am bm) := by
    have h := exp_div_two_le_cosh (dist am bm)
    rw [div_le_iff₀ (two_pos : (0:ℝ) < 2)] at h
    linarith [h]
  have hcosh : Real.cosh (dist am bm) = 1 + Real.sinh (m : ℝ) ^ 2 * bratioB ξ η := by
    rw [hamdef, hbmdef, cosh_dist_geodesicRay_geodesicRay]
    have hb : bratioB ξ η = 1 - sdot ξ.val η.val := by
      change - lorB ξ.val η.val = 1 - sdot ξ.val η.val
      change -(sdot ξ.val η.val - tc ξ.val * tc η.val) = 1 - sdot ξ.val η.val
      rw [ξ.tc_eq, η.tc_eq]
      ring
    rw [hb]
    have hc := Real.cosh_sq_sub_sinh_sq (m : ℝ)
    nlinarith [hc]
  have hsinh : Real.sinh (m : ℝ) ^ 2 ≤ Real.exp (2 * (m : ℝ)) / 4 := by
    have h1 := sinh_le_exp_div_two (m : ℝ)
    have h2 := sinh_nonneg_of_nonneg hm0
    have h3 : Real.sinh (m : ℝ) ^ 2 ≤ (Real.exp (m : ℝ) / 2) ^ 2 :=
      pow_le_pow_left₀ h2 h1 2
    have h4 : (Real.exp (m : ℝ) / 2) ^ 2 = Real.exp (2 * (m : ℝ)) / 4 := by
      rw [div_pow]
      have e1 : (Real.exp (m : ℝ)) ^ 2 = Real.exp (2 * (m : ℝ)) := by
        rw [← Real.exp_nat_mul]
        norm_num
      rw [e1]
      norm_num
    linarith [h3, h4]
  have hE : Real.exp (2 * (m : ℝ)) * Real.exp (-(2 * (m : ℝ))) = 1 := by
    rw [← Real.exp_add]
    have : (2:ℝ) * (m : ℝ) + -(2 * (m : ℝ)) = 0 := by ring
    rw [this, Real.exp_zero]
  have hkey : 2 * (Real.sinh (m : ℝ) ^ 2 * Real.exp (-(2 * (m : ℝ)))) ≤ 1 / 2 := by
    calc 2 * (Real.sinh (m : ℝ) ^ 2 * Real.exp (-(2 * (m : ℝ))))
        ≤ 2 * ((Real.exp (2 * (m : ℝ)) / 4) * Real.exp (-(2 * (m : ℝ)))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
          exact mul_le_mul_of_nonneg_right hsinh (Real.exp_pos _).le
      _ = (1 / 2) * (Real.exp (2 * (m : ℝ)) * Real.exp (-(2 * (m : ℝ)))) := by ring
      _ = 1 / 2 := by rw [hE]; ring
  calc Real.exp (dist am bm) * Real.exp (-(2 * (m : ℝ)))
      ≤ (2 * Real.cosh (dist am bm)) * Real.exp (-(2 * (m : ℝ))) :=
        mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
    _ = 2 * Real.exp (-(2 * (m : ℝ)))
        + (2 * (Real.sinh (m : ℝ) ^ 2 * Real.exp (-(2 * (m : ℝ))))) * bratioB ξ η := by
        rw [hcosh]; ring
    _ ≤ 2 * Real.exp (-(2 * (m : ℝ))) + (1 / 2) * bratioB ξ η := by
        have h1 := mul_le_mul_of_nonneg_right hkey hρ0
        linarith [h1]
    _ = 2 * Real.exp (-(2 * (m : ℝ))) + bratioB ξ η / 2 := by ring

theorem bratioB_bExt_le {K C : ℝ} {Φ : HUpper n → HUpper n}
    (hΦ : PseudoIsometry.IsPseudoIsometry K C Φ) (hn : 1 ≤ n) (ξ η : BoundaryH n) :
    bratioB (bExt (gromovCauchy_image_ray hΦ hn) ξ)
        (bExt (gromovCauchy_image_ray hΦ hn) η)
      ≤ 4 * Real.exp (2 * (C + morseDist K C + Real.log 2 + dist basepointH (Φ basepointH)))
        * (bratioB ξ η / 2) ^ (K : ℝ)⁻¹ := by
  have hK : (1:ℝ) ≤ K := hΦ.hK
  have hK0 : (0:ℝ) < K := one_pos.trans_le hK
  have hKinv0 : (0:ℝ) ≤ (K : ℝ)⁻¹ := inv_nonneg.mpr hK0.le
  set φ := bExt (gromovCauchy_image_ray hΦ hn) with hφdef
  set C₁' : ℝ := C + morseDist K C + Real.log 2 + dist basepointH (Φ basepointH) with hC₁'
  have hper : ∀ m : ℕ, bratio (Φ (geodesicRay ξ (m : ℝ))) (Φ (geodesicRay η (m : ℝ)))
      ≤ 4 * Real.exp (2 * C₁')
        * (2 * Real.exp (-(2 * (m : ℝ))) + bratioB ξ η / 2) ^ (K : ℝ)⁻¹ := by
    intro m
    set am := geodesicRay ξ (m : ℝ) with hamdef
    set bm := geodesicRay η (m : ℝ) with hbmdef
    have h1 := bratio_le (Φ am) (Φ bm)
    have h2 := gromovProduct_image_ge hΦ hn basepointH am bm
    have h3 := abs_gromovProduct_sub_le basepointH (Φ basepointH) (Φ am) (Φ bm)
    rw [abs_le] at h3
    have h4 : (K:ℝ)⁻¹ * gromovProduct basepointH am bm - C₁'
        ≤ gromovProduct basepointH (Φ am) (Φ bm) := by
      linarith [h2, h3.1, hC₁']
    have h5 : Real.exp (-(2 * gromovProduct basepointH (Φ am) (Φ bm)))
        ≤ Real.exp (2 * C₁') * (Real.exp (-(2 * gromovProduct basepointH am bm))) ^ (K : ℝ)⁻¹ := by
      have he1 : -(2 * gromovProduct basepointH (Φ am) (Φ bm))
          ≤ -(2 * ((K:ℝ)⁻¹ * gromovProduct basepointH am bm - C₁')) := by linarith [h4]
      have he2 := Real.exp_le_exp.mpr he1
      have he3 : -(2 * ((K:ℝ)⁻¹ * gromovProduct basepointH am bm - C₁'))
          = 2 * C₁' + (K:ℝ)⁻¹ * (-(2 * gromovProduct basepointH am bm)) := by ring
      rw [he3, Real.exp_add] at he2
      have he4 : (Real.exp (-(2 * gromovProduct basepointH am bm))) ^ (K : ℝ)⁻¹
          = Real.exp ((K:ℝ)⁻¹ * (-(2 * gromovProduct basepointH am bm))) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm]
      rw [he4]
      exact he2
    have h6 := exp_neg_gromov_geodesicRay_le ξ η m
    have h7 : (Real.exp (-(2 * gromovProduct basepointH am bm))) ^ (K : ℝ)⁻¹
        ≤ (2 * Real.exp (-(2 * (m : ℝ))) + bratioB ξ η / 2) ^ (K : ℝ)⁻¹ :=
      Real.rpow_le_rpow (Real.exp_pos _).le h6 hKinv0
    calc bratio (Φ am) (Φ bm)
        ≤ 4 * Real.exp (-(2 * gromovProduct basepointH (Φ am) (Φ bm))) := h1
      _ ≤ 4 * (Real.exp (2 * C₁')
            * (Real.exp (-(2 * gromovProduct basepointH am bm))) ^ (K : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_left h5 (by norm_num)
      _ ≤ 4 * (Real.exp (2 * C₁')
            * (2 * Real.exp (-(2 * (m : ℝ))) + bratioB ξ η / 2) ^ (K : ℝ)⁻¹) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 4)
          exact mul_le_mul_of_nonneg_left h7 (Real.exp_pos _).le
      _ = 4 * Real.exp (2 * C₁')
            * (2 * Real.exp (-(2 * (m : ℝ))) + bratioB ξ η / 2) ^ (K : ℝ)⁻¹ := by ring
  have hconv : Tendsto (fun m : ℕ => bratio (Φ (geodesicRay ξ (m : ℝ))) (Φ (geodesicRay η (m : ℝ))))
      atTop (nhds (bratioB (φ ξ) (φ η))) := by
    have hξ : ConvergesToBoundary (fun m : ℕ => Φ (geodesicRay ξ (m : ℝ))) (φ ξ) := by
      have h := bExt_spec (gromovCauchy_image_ray hΦ hn) ξ
      have h2 : (fun m : ℕ => Φ (rayTo basepointH ξ (m : ℝ)))
          = (fun m : ℕ => Φ (geodesicRay ξ (m : ℝ))) := by
        funext m
        rw [rayTo_basepointH_eq_geodesicRay]
      rwa [h2] at h
    have hη : ConvergesToBoundary (fun m : ℕ => Φ (geodesicRay η (m : ℝ))) (φ η) := by
      have h := bExt_spec (gromovCauchy_image_ray hΦ hn) η
      have h2 : (fun m : ℕ => Φ (rayTo basepointH η (m : ℝ)))
          = (fun m : ℕ => Φ (geodesicRay η (m : ℝ))) := by
        funext m
        rw [rayTo_basepointH_eq_geodesicRay]
      rwa [h2] at h
    have heq : (fun m : ℕ => bratio (Φ (geodesicRay ξ (m : ℝ))) (Φ (geodesicRay η (m : ℝ))))
        = fun m : ℕ => - lorB (radial (Φ (geodesicRay ξ (m : ℝ))))
            (radial (Φ (geodesicRay η (m : ℝ)))) :=
      funext fun m => by rw [lorB_radial_eq_neg_bratio, neg_neg]
    rw [heq]
    have hL : Tendsto (fun m : ℕ => lorB (radial (Φ (geodesicRay ξ (m : ℝ))))
        (radial (Φ (geodesicRay η (m : ℝ))))) atTop (nhds (lorB (φ ξ).val (φ η).val)) := by
      have hprod : Tendsto (fun m : ℕ => (radial (Φ (geodesicRay ξ (m : ℝ))),
          radial (Φ (geodesicRay η (m : ℝ))))) atTop (nhds ((φ ξ).val, (φ η).val)) := by
        rw [nhds_prod_eq]
        exact hξ.prodMk hη
      exact (continuous_lorB_pair.tendsto _).comp hprod
    have hneg := hL.neg
    change Tendsto (fun m : ℕ => - lorB (radial (Φ (geodesicRay ξ (m : ℝ))))
        (radial (Φ (geodesicRay η (m : ℝ))))) atTop (nhds (bratioB (φ ξ) (φ η)))
    exact hneg
  have hRHS : Tendsto (fun m : ℕ => 4 * Real.exp (2 * C₁')
      * (2 * Real.exp (-(2 * (m : ℝ))) + bratioB ξ η / 2) ^ (K : ℝ)⁻¹)
      atTop (nhds (4 * Real.exp (2 * C₁') * (bratioB ξ η / 2) ^ (K : ℝ)⁻¹)) := by
    have hexp : Tendsto (fun m : ℕ => Real.exp (-(2 * (m : ℝ)))) atTop (nhds 0) := by
      have h1 : (fun m : ℕ => Real.exp (-(2 * (m : ℝ))))
          = fun m : ℕ => (Real.exp (-2)) ^ m := by
        funext m
        rw [show -(2 * (m : ℝ)) = (m : ℝ) * (-2) by ring, Real.exp_nat_mul]
      rw [h1]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le (by
        rw [← Real.exp_zero]
        exact Real.exp_strictMono (by norm_num))
    have hbase : Tendsto (fun m : ℕ => 2 * Real.exp (-(2 * (m : ℝ))) + bratioB ξ η / 2)
        atTop (nhds (2 * 0 + bratioB ξ η / 2)) :=
      (hexp.const_mul 2).add tendsto_const_nhds
    rw [show (2:ℝ) * 0 + bratioB ξ η / 2 = bratioB ξ η / 2 by ring] at hbase
    have hrpow : Tendsto (fun m : ℕ => (2 * Real.exp (-(2 * (m : ℝ))) + bratioB ξ η / 2) ^ (K : ℝ)⁻¹)
        atTop (nhds ((bratioB ξ η / 2) ^ (K : ℝ)⁻¹)) :=
      (Real.continuousAt_rpow_const _ _ (Or.inr hKinv0)).tendsto.comp hbase
    exact hrpow.const_mul _
  exact le_of_tendsto_of_tendsto hconv hRHS (Filter.Eventually.of_forall hper)

theorem bExt_continuous {K C : ℝ} {Φ : HUpper n → HUpper n}
    (hΦ : PseudoIsometry.IsPseudoIsometry K C Φ) (hn : 1 ≤ n) :
    Continuous (bExt (gromovCauchy_image_ray hΦ hn)) := by
  have hK : (1:ℝ) ≤ K := hΦ.hK
  have hK0 : (0:ℝ) < K := one_pos.trans_le hK
  have hKinv0 : (0:ℝ) < (K : ℝ)⁻¹ := inv_pos.mpr hK0
  set φ := bExt (gromovCauchy_image_ray hΦ hn) with hφdef
  set C₁' : ℝ := C + morseDist K C + Real.log 2 + dist basepointH (Φ basepointH) with hC₁'
  have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  rw [continuous_iff_continuousAt]
  intro ξ
  rw [ContinuousAt, isEmbedding_val.isInducing.nhds_eq_comap ξ,
    isEmbedding_val.isInducing.nhds_eq_comap (φ ξ), tendsto_comap_iff]
  rw [tendsto_pi_nhds]
  intro a
  rcases a with i | k
  · rw [Metric.tendsto_nhds]
    intro ε hε
    have hbig0 : (0:ℝ) < 8 * Real.exp (2 * C₁') := by positivity
    set ε₁ := ε ^ 2 / (8 * Real.exp (2 * C₁')) with hε₁def
    have hε₁0 : (0:ℝ) < ε₁ := by positivity
    set δ₁ := ε₁ ^ (K : ℝ) with hδ₁def
    have hδ₁0 : (0:ℝ) < δ₁ := Real.rpow_pos_of_pos hε₁0 K
    set δ := Real.sqrt (4 * δ₁ / n) with hδdef
    have hδ0 : (0:ℝ) < δ := Real.sqrt_pos.mpr (by positivity)
    refine eventually_comap.mpr (Filter.eventually_of_mem (Metric.ball_mem_nhds ξ.val hδ0)
      (fun v hv u hu => ?_))
    have hud : dist (BoundaryH.val u) ξ.val < δ := by rw [hu]; exact Metric.mem_ball.mp hv
    have hcoord : ∀ j : Fin n, |u.val (Sum.inl j) - ξ.val (Sum.inl j)| < δ := by
      intro j
      calc |u.val (Sum.inl j) - ξ.val (Sum.inl j)|
          = dist (u.val (Sum.inl j)) (ξ.val (Sum.inl j)) := (Real.dist_eq _ _).symm
        _ ≤ dist u.val ξ.val := dist_le_pi_dist _ _ _
        _ < δ := hud
    have hsd : sdot (u.val - ξ.val) (u.val - ξ.val) < n * δ ^ 2 := by
      have hterm : ∀ j : Fin n, (u.val - ξ.val) (Sum.inl j) * (u.val - ξ.val) (Sum.inl j)
          < δ ^ 2 := by
        intro j
        have h1 : |(u.val - ξ.val) (Sum.inl j)| < δ := by
          rw [Pi.sub_apply]; exact hcoord j
        have h2 : (u.val - ξ.val) (Sum.inl j) * (u.val - ξ.val) (Sum.inl j)
            = |(u.val - ξ.val) (Sum.inl j)| ^ 2 := by rw [sq_abs, sq]
        rw [h2]
        exact pow_lt_pow_left₀ h1 (abs_nonneg _) (by norm_num : 2 ≠ 0)
      have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
        have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
        exact Finset.univ_nonempty
      calc sdot (u.val - ξ.val) (u.val - ξ.val)
          = ∑ j : Fin n, (u.val - ξ.val) (Sum.inl j) * (u.val - ξ.val) (Sum.inl j) := rfl
        _ < ∑ _j : Fin n, δ ^ 2 := Finset.sum_lt_sum_of_nonempty hne (fun j _ => hterm j)
        _ = n * δ ^ 2 := by rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    have hbr : bratioB u ξ < n * δ ^ 2 / 2 := by
      have h1 := sdot_sub_self_eq_two_bratioB u ξ
      linarith [hsd, h1]
    change dist ((BoundaryH.val ∘ φ) u (Sum.inl i)) ((BoundaryH.val ∘ φ) ξ (Sum.inl i)) < ε
    rw [Function.comp_apply, Function.comp_apply, Real.dist_eq]
    have hc1 : ((φ u).val (Sum.inl i) - (φ ξ).val (Sum.inl i)) ^ 2 ≤ 2 * bratioB (φ u) (φ ξ) := by
      have h1 := sdot_sub_self_eq_two_bratioB (φ u) (φ ξ)
      have h2 : ((φ u).val (Sum.inl i) - (φ ξ).val (Sum.inl i)) ^ 2
          ≤ sdot ((φ u).val - (φ ξ).val) ((φ u).val - (φ ξ).val) := by
        change ((φ u).val (Sum.inl i) - (φ ξ).val (Sum.inl i)) ^ 2
            ≤ ∑ j : Fin n, ((φ u).val - (φ ξ).val) (Sum.inl j)
              * ((φ u).val - (φ ξ).val) (Sum.inl j)
        have hterm : ((φ u).val (Sum.inl i) - (φ ξ).val (Sum.inl i)) ^ 2
            = ((φ u).val - (φ ξ).val) (Sum.inl i) * ((φ u).val - (φ ξ).val) (Sum.inl i) := by
          rw [Pi.sub_apply]; ring
        rw [hterm]
        exact Finset.single_le_sum
          (f := fun j : Fin n => ((φ u).val - (φ ξ).val) (Sum.inl j)
            * ((φ u).val - (φ ξ).val) (Sum.inl j))
          (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
      linarith [h1, h2]
    have hc2 := bratioB_bExt_le hΦ hn u ξ
    have hc3 : 2 * bratioB (φ u) (φ ξ) < ε ^ 2 := by
      have h1 : (bratioB u ξ / 2) ^ (K : ℝ)⁻¹ < (n * δ ^ 2 / 4) ^ (K : ℝ)⁻¹ :=
        Real.rpow_lt_rpow (div_nonneg (bratioB_nonneg u ξ) (by norm_num)) (by linarith [hbr])
          hKinv0
      have h2 : n * δ ^ 2 / 4 = δ₁ := by
        rw [hδdef, Real.sq_sqrt (by positivity)]
        field_simp
      rw [h2] at h1
      have h3 : (δ₁ : ℝ) ^ (K : ℝ)⁻¹ = ε₁ := by
        rw [hδ₁def, ← Real.rpow_mul hε₁0.le, mul_inv_cancel₀ hK0.ne', Real.rpow_one]
      rw [h3] at h1
      have h4 : 2 * (4 * Real.exp (2 * C₁') * (bratioB u ξ / 2) ^ (K:ℝ)⁻¹)
          < 2 * (4 * Real.exp (2 * C₁') * ε₁) :=
        mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left h1 (by positivity)) (by norm_num)
      have h5 : 2 * (4 * Real.exp (2 * C₁') * ε₁) = ε ^ 2 := by
        rw [hε₁def]
        field_simp
        ring
      linarith [hc2, h4, h5]
    exact abs_lt_of_sq_lt_sq (lt_of_le_of_lt hc1 hc3) hε.le
  · have hk0 : k = 0 := Subsingleton.elim k 0
    subst hk0
    have hconst : (fun u : BoundaryH n => (BoundaryH.val ∘ φ) u (Sum.inr 0)) = fun _ => (1 : ℝ) := by
      funext u
      change (φ u).val (Sum.inr 0) = 1
      exact (φ u).tc_eq
    have hval : (φ ξ).val (Sum.inr 0) = 1 := (φ ξ).tc_eq
    rw [hconst, hval]
    exact tendsto_const_nhds

noncomputable def bExtHomeomorph {K C K' C' E E' : ℝ} {Φ Ψ : HUpper n → HUpper n}
    (hΦ : PseudoIsometry.IsPseudoIsometry K C Φ)
    (hΨ : PseudoIsometry.IsPseudoIsometry K' C' Ψ)
    (hdispl : ∀ x : HUpper n, dist (Ψ (Φ x)) x ≤ E)
    (hdispl' : ∀ y : HUpper n, dist (Φ (Ψ y)) y ≤ E')
    (hn : 1 ≤ n) : BoundaryH n ≃ₜ BoundaryH n where
  toFun := bExt (gromovCauchy_image_ray hΦ hn)
  invFun := bExt (gromovCauchy_image_ray hΨ hn)
  left_inv ξ := by
    have hGCΨΦ : ∀ (o : HUpper n) (ξ : BoundaryH n),
        GromovCauchy o (fun m : ℕ => (Ψ ∘ Φ) (rayTo o ξ (m : ℝ))) :=
      gromovCauchy_image_ray (hΨ.comp hΦ) hn
    have hGCid : ∀ (o : HUpper n) (ξ : BoundaryH n),
        GromovCauchy o (fun m : ℕ => id (rayTo o ξ (m : ℝ))) := gromovCauchy_rayTo
    have e1 : bExt hGCΨΦ
        = bExt (gromovCauchy_image_ray hΨ hn) ∘ bExt (gromovCauchy_image_ray hΦ hn) :=
      bExt_comp hΨ (gromovCauchy_image_ray hΦ hn) (gromovCauchy_image_ray hΨ hn) hGCΨΦ hn
    have e2 : bExt hGCΨΦ = bExt hGCid :=
      bExt_eq_of_bounded hGCΨΦ hGCid
        (fun x => hdispl x)
    have e3 : bExt hGCid = id := bExt_id hGCid
    have h : (bExt (gromovCauchy_image_ray hΨ hn) ∘ bExt (gromovCauchy_image_ray hΦ hn)) ξ
        = id ξ := by rw [← e1, e2, e3]
    exact h
  right_inv η := by
    have hGCΦΨ : ∀ (o : HUpper n) (ξ : BoundaryH n),
        GromovCauchy o (fun m : ℕ => (Φ ∘ Ψ) (rayTo o ξ (m : ℝ))) :=
      gromovCauchy_image_ray (hΦ.comp hΨ) hn
    have hGCid : ∀ (o : HUpper n) (ξ : BoundaryH n),
        GromovCauchy o (fun m : ℕ => id (rayTo o ξ (m : ℝ))) := gromovCauchy_rayTo
    have e1 : bExt hGCΦΨ
        = bExt (gromovCauchy_image_ray hΦ hn) ∘ bExt (gromovCauchy_image_ray hΨ hn) :=
      bExt_comp hΦ (gromovCauchy_image_ray hΨ hn) (gromovCauchy_image_ray hΦ hn) hGCΦΨ hn
    have e2 : bExt hGCΦΨ = bExt hGCid :=
      bExt_eq_of_bounded hGCΦΨ hGCid
        (fun y => hdispl' y)
    have e3 : bExt hGCid = id := bExt_id hGCid
    have h : (bExt (gromovCauchy_image_ray hΦ hn) ∘ bExt (gromovCauchy_image_ray hΨ hn)) η
        = id η := by rw [← e1, e2, e3]
    exact h
  continuous_toFun := bExt_continuous hΦ hn
  continuous_invFun := bExt_continuous hΨ hn

theorem bExtHomeomorph_apply {K C K' C' E E' : ℝ} {Φ Ψ : HUpper n → HUpper n}
    (hΦ : PseudoIsometry.IsPseudoIsometry K C Φ)
    (hΨ : PseudoIsometry.IsPseudoIsometry K' C' Ψ)
    (hdispl : ∀ x : HUpper n, dist (Ψ (Φ x)) x ≤ E)
    (hdispl' : ∀ y : HUpper n, dist (Φ (Ψ y)) y ≤ E')
    (hn : 1 ≤ n) (ξ : BoundaryH n) :
    bExtHomeomorph hΦ hΨ hdispl hdispl' hn ξ
      = bExt (gromovCauchy_image_ray hΦ hn) ξ := rfl

theorem bratioB_bExtHomeomorph_symm_le {K C K' C' E E' : ℝ} {Φ Ψ : HUpper n → HUpper n}
    (hΦ : PseudoIsometry.IsPseudoIsometry K C Φ)
    (hΨ : PseudoIsometry.IsPseudoIsometry K' C' Ψ)
    (hdispl : ∀ x : HUpper n, dist (Ψ (Φ x)) x ≤ E)
    (hdispl' : ∀ y : HUpper n, dist (Φ (Ψ y)) y ≤ E')
    (hn : 1 ≤ n) (ξ η : BoundaryH n) :
    bratioB ξ η
      ≤ 4 * Real.exp (2 * (C' + morseDist K' C' + Real.log 2
          + dist basepointH (Ψ basepointH)))
        * (bratioB (bExtHomeomorph hΦ hΨ hdispl hdispl' hn ξ)
            (bExtHomeomorph hΦ hΨ hdispl hdispl' hn η) / 2) ^ (K' : ℝ)⁻¹ := by
  set φ := bExtHomeomorph hΦ hΨ hdispl hdispl' hn with hφdef
  have h1 := bratioB_bExt_le hΨ hn (φ ξ) (φ η)
  have he : bExt (gromovCauchy_image_ray hΨ hn) = φ.symm := rfl
  rw [he] at h1
  rw [φ.symm_apply_apply, φ.symm_apply_apply] at h1
  exact h1

theorem exists_equivariant_homeomorph_boundaryExtension
    (hn : 1 ≤ n) (Γ Λ : Subgroup (PO n 1))
    (disc_Γ : IsDiscrete (SetLike.coe Γ)) (disc_Λ : IsDiscrete (SetLike.coe Λ))
    (hcoΓ : UniformPseudoIsometry.ActsCocompactly hn Γ)
    (hcoΛ : UniformPseudoIsometry.ActsCocompactly hn Λ) (f : Γ ≃* Λ) :
    ∃ (Φ : HUpper n → HUpper n) (K C : ℝ) (φ : BoundaryH n ≃ₜ BoundaryH n),
      PseudoIsometry.IsPseudoIsometry K C Φ
      ∧ PseudoIsometry.IsFEquivariant f hn Φ
      ∧ (∀ (γ : Γ) (ξ : BoundaryH n),
          φ ((poBoundaryMulAction hn).smul (γ : PO n 1) ξ)
            = (poBoundaryMulAction hn).smul (f γ : PO n 1) (φ ξ))
      ∧ (∀ ξ : BoundaryH n,
          ConvergesToBoundary (fun m : ℕ => Φ (geodesicRay ξ (m : ℝ))) (φ ξ)) := by
  let := poMulAction hn
  obtain ⟨Φ, Ψ, K, C, K', C', E, E', hΦ, hΦeq, hΨ, hΨeq, hdispl, hdispl'⟩ :=
    UniformPseudoIsometry.exists_twoSided_pseudoIsometry_of_actsCocompactly hn Γ Λ disc_Γ disc_Λ
      hcoΓ hcoΛ f
  refine ⟨Φ, K, C, bExtHomeomorph hΦ hΨ hdispl hdispl' hn, hΦ, hΦeq, ?_, ?_⟩
  · intro γ ξ
    rw [bExtHomeomorph_apply]
    exact bExt_equivariant hΦ (gromovCauchy_image_ray hΦ hn) hn hΦeq γ ξ
  · intro ξ
    rw [bExtHomeomorph_apply]
    have h := bExt_spec (gromovCauchy_image_ray hΦ hn) ξ
    have h2 : (fun m : ℕ => Φ (rayTo basepointH ξ (m : ℝ)))
        = (fun m : ℕ => Φ (geodesicRay ξ (m : ℝ))) := by
      funext m
      rw [rayTo_basepointH_eq_geodesicRay]
    rwa [h2] at h

end DifferentialGeometry.BoundaryHomeomorph
