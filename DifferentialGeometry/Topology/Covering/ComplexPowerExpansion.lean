import DifferentialGeometry.Topology.LocalDegree.ComplexPower
import DifferentialGeometry.Topology.PuncturedConnected
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Data.Set.Card

set_option autoImplicit false

noncomputable section

open Set Metric Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Topology.Covering

open DifferentialGeometry.LocalDegree

/-- A real continuously differentiable perturbation of a normalized complex
power, regular off its center, has exactly the predicted number of sheets
over one punctured target disk. Both radii are fixed before the target point. -/
theorem exists_nsheeted_covering_of_complex_power_expansion
    {F : ℂ → ℂ} {a : ℂ} {n : ℕ} {C R0 : ℝ}
    (hn : 0 < n) (hR0 : 0 < R0) (hC : 0 ≤ C)
    (hF : ContDiffOn ℝ 1 F (Metric.ball a R0))
    (hreg : ∀ z ∈ Metric.ball a R0, z ≠ a →
      (fderiv ℝ F z).IsInvertible)
    (hexp : ∀ z ∈ Metric.ball a R0,
      ‖F z - F a - (z - a) ^ n / (n : ℂ)‖ ≤
        C * ‖z - a‖ ^ (n + 1)) :
    ∃ r δ : ℝ, 0 < r ∧ r < R0 ∧ 0 < δ ∧
      (∀ z ∈ Metric.closedBall a r, F z = F a ↔ z = a) ∧
      (∀ z ∈ Metric.sphere a r, δ < ‖F z - F a‖) ∧
      let f : Metric.closedBall a r → ℂ := fun z => F z.val
      let S : Set ℂ := Metric.ball (F a) δ \ {F a}
      IsCoveringMapOn f S ∧
        ∀ y ∈ S, (f ⁻¹' {y}).encard = (n : ℕ∞) := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < (C + 1) * (2 * (n : ℝ)) := by positivity
  obtain ⟨r, hr, hrsmall⟩ := exists_between
    (lt_min hR0 (div_pos zero_lt_one hden))
  have hrR : r < R0 := hrsmall.trans_le (min_le_left _ _)
  have hcoef : C * r < 1 / (2 * (n : ℝ)) := by
    have ht := (lt_div_iff₀ hden).mp (hrsmall.trans_le (min_le_right _ _))
    apply (lt_div_iff₀ (by positivity : 0 < 2 * (n : ℝ))).mpr
    nlinarith [mul_pos hr hnR]
  have hclosed : closedBall a r ⊆ ball a R0 := closedBall_subset_ball hrR
  let δ : ℝ := r ^ n / (2 * (n : ℝ))
  have hδ : 0 < δ := div_pos (pow_pos hr _) (by positivity)
  have herr (z : ℂ) (hz : z ∈ closedBall a r) :
      ‖F z - F a - (z - a) ^ n / (n : ℂ)‖ ≤
        (C * r) * ‖z - a‖ ^ n := by
    calc
      _ ≤ C * ‖z - a‖ ^ (n + 1) := hexp z (hclosed hz)
      _ = (C * ‖z - a‖) * ‖z - a‖ ^ n := by rw [pow_succ]; ring
      _ ≤ (C * r) * ‖z - a‖ ^ n :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mem_closedBall_iff_norm.mp hz) hC)
          (pow_nonneg (norm_nonneg _) _)
  have hcenter (z : ℂ) (hz : z ∈ closedBall a r) : F z = F a ↔ z = a := by
    constructor
    · intro hzero
      by_contra hza
      have hpow : 0 < ‖z - a‖ ^ n :=
        pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hza)) _
      have hb := herr z hz
      rw [hzero, sub_self, zero_sub, norm_neg, norm_div, norm_pow,
        Complex.norm_natCast] at hb
      have hs := mul_lt_mul_of_pos_right hcoef hpow
      have hninv : 0 < 1 / (2 * (n : ℝ)) := by positivity
      have hid : ‖z - a‖ ^ n / (n : ℝ) =
          2 * ((1 / (2 * (n : ℝ))) * ‖z - a‖ ^ n) := by
        field_simp [hnR.ne']
      nlinarith [mul_pos hninv hpow]
    · rintro rfl
      rfl
  have hsphere_error (z : ℂ) (hz : z ∈ sphere a r) :
      ‖F z - F a - (z - a) ^ n / (n : ℂ)‖ < δ := by
    have hnorm : ‖z - a‖ = r := mem_sphere_iff_norm.mp hz
    calc
      _ ≤ (C * r) * ‖z - a‖ ^ n := herr z (sphere_subset_closedBall hz)
      _ = (C * r) * r ^ n := by rw [hnorm]
      _ < (1 / (2 * (n : ℝ))) * r ^ n :=
        mul_lt_mul_of_pos_right hcoef (pow_pos hr _)
      _ = δ := by dsimp [δ]; ring
  have hgap (z : ℂ) (hz : z ∈ sphere a r) : δ < ‖F z - F a‖ := by
    have hnorm : ‖z - a‖ = r := mem_sphere_iff_norm.mp hz
    have htri := norm_le_norm_sub_add ((z - a) ^ n / (n : ℂ)) (F z - F a)
    rw [norm_sub_rev, norm_div, norm_pow, Complex.norm_natCast, hnorm] at htri
    have htwo : r ^ n / (n : ℝ) = 2 * δ := by dsimp [δ]; ring
    linarith [hsphere_error z hz]
  let f : closedBall a r → ℂ := fun z => F z.val
  let S : Set ℂ := ball (F a) δ \ {F a}
  have hf : Continuous f := (hF.continuousOn.mono hclosed).domRestrict
  have hpre (z : closedBall a r) (hz : f z ∈ S) : z.val ∈ ball a r ∧ z.val ≠ a := by
    have hnval : ‖F z.val - F a‖ < δ := mem_ball_iff_norm.mp hz.1
    have hstrict : dist z.val a < r := by
      have hle := mem_closedBall.mp z.property
      by_contra hnot
      have hs : z.val ∈ sphere a r := mem_sphere.mpr (le_antisymm hle (le_of_not_gt hnot))
      exact (hgap z.val hs).not_ge hnval.le
    refine ⟨hstrict, ?_⟩
    intro hza
    apply hz.2
    change F z.val = F a
    rw [hza]
  have hlocal : IsLocalHomeomorphOn f (f ⁻¹' S) := by
    apply (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict (f ⁻¹' S)).mpr
    intro z hz
    obtain ⟨hzball, hza⟩ := hpre z hz
    have hzR := hclosed z.property
    have hcz : ContDiffAt ℝ 1 F z.val := hF.contDiffAt (isOpen_ball.mem_nhds hzR)
    obtain ⟨A, hA⟩ := hreg z.val hzR hza
    have hd : HasFDerivAt F (A : ℂ →L[ℝ] ℂ) z.val := by
      rw [hA]
      exact (hcz.differentiableAt (by norm_num)).hasFDerivAt
    let e := hcz.toOpenPartialHomeomorph F hd (by norm_num)
    have hze : z.val ∈ e.source := hcz.mem_toOpenPartialHomeomorph_source hd (by norm_num)
    let V : Set (closedBall a r) := {w | w.val ∈ ball a r ∩ e.source}
    have hV : IsOpen V := (isOpen_ball.inter e.open_source).preimage continuous_subtype_val
    let j : V → e.source := fun w => ⟨w.val.val, w.property.2⟩
    have hj : _root_.Topology.IsEmbedding j :=
      (_root_.Topology.IsEmbedding.subtypeVal.comp
        _root_.Topology.IsEmbedding.subtypeVal).codRestrict e.source (fun w => w.property.2)
    have hjrange : Set.range j = {w : e.source | w.val ∈ ball a r} := by
      ext w
      constructor
      · rintro ⟨v, rfl⟩
        exact v.property.1
      · intro hw
        refine ⟨⟨⟨w.val, ball_subset_closedBall hw⟩, hw, w.property⟩, ?_⟩
        rfl
    have hjopen : _root_.Topology.IsOpenEmbedding j := ⟨hj, by
      rw [hjrange]
      exact isOpen_ball.preimage continuous_subtype_val⟩
    refine ⟨V, hV.mem_nhds ⟨hzball, hze⟩, ?_⟩
    exact e.isOpenEmbedding_restrict.comp hjopen
  have hcover : IsCoveringMapOn f S := IsCoveringMapOn.of_isLocalHomeomorphOn hf hlocal
  let D : Set ℂ := ball a R0 \ {a}
  let dF : ℂ → ℝ := fun z => LinearMap.det (fderiv ℝ F z).toLinearMap
  have hdet (z : ℂ) (hz : z ∈ D) : dF z ≠ 0 := by
    obtain ⟨A, hA⟩ := hreg z hz.1 hz.2
    dsimp only [dF]
    rw [← hA]
    exact A.toLinearEquiv.isUnit_det'.ne_zero
  have hdetcont : ContinuousOn dF (ball a R0) :=
    ContinuousLinearMap.continuous_det.comp_continuousOn
      (hF.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl)
  have hsigncont : ContinuousOn (fun z => SignType.sign (dF z)) D := by
    intro z hz
    exact ((continuousAt_sign_of_ne_zero (hdet z hz)).comp
      (hdetcont.continuousAt (isOpen_ball.mem_nhds hz.1))).continuousWithinAt
  have hconn : IsPathConnected D := Metric.isPathConnected_ball_sdiff_singleton
    (by rw [← Module.finrank_eq_rank, Complex.finrank_real_complex]; norm_num) a hR0
  obtain ⟨b, hb⟩ := hconn.isConnected.nonempty
  have hsign (z : ℂ) (hz : z ∈ D) : SignType.sign (dF z) = SignType.sign (dF b) :=
    hconn.isConnected.isPreconnected.constant hsigncont hz hb
  refine ⟨r, δ, hr, hrR, hδ, hcenter, hgap, hcover, ?_⟩
  intro y hy
  have hfinite : (f ⁻¹' {y}).Finite :=
    (isClosed_singleton.preimage hf).isCompact.finite
      ⟨(hcover y hy).discreteTopology_fiber⟩
  let := hfinite.fintype
  let V := EuclideanSpace ℝ (Fin 2)
  let e : ℂ ≃ₗᵢ[ℝ] V := Complex.orthonormalBasisOneI.repr
  let G : V → V := fun x => e (F (e.symm x) - y)
  have hcoord (x : V) : dist (e.symm x) a = dist x (e a) := by
    simpa only [LinearIsometryEquiv.symm_apply_apply] using e.symm.dist_map x (e a)
  have hGc : ContinuousOn G (closedBall (e a) r) := by
    intro x hx
    have hz : e.symm x ∈ closedBall a r := by
      simpa only [mem_closedBall, hcoord] using hx
    exact (e.continuous.continuousAt.comp
      (((hF.contDiffAt (isOpen_ball.mem_nhds (hclosed hz))).continuousAt.comp
        e.symm.continuous.continuousAt).sub continuousAt_const)).continuousWithinAt
  let gc : C(closedBall (e a) r, V) := ⟨fun x => G x.val, hGc.domRestrict⟩
  let model := (normalizedComplexPower a n).restrict (closedBall (e a) r)
  obtain ⟨hbmodel, hdegmodel⟩ := euclideanBallDegree_normalizedComplexPower a n hn r hr
  have hclose : ∀ x : closedBall (e a) r, x.val ∈ sphere (e a) r →
      ‖gc x - model x‖ < ‖model x‖ := by
    intro x hx
    have hz : e.symm x.val ∈ sphere a r := by
      simpa only [mem_sphere, hcoord] using hx
    have hnorm : ‖e.symm x.val - a‖ = r := mem_sphere_iff_norm.mp hz
    change ‖e (F (e.symm x.val) - y) - e ((e.symm x.val - a) ^ n / (n : ℂ))‖ <
      ‖e ((e.symm x.val - a) ^ n / (n : ℂ))‖
    rw [← map_sub, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map,
      norm_div, norm_pow, Complex.norm_natCast, hnorm]
    calc
      _ = ‖(F (e.symm x.val) - F a - (e.symm x.val - a) ^ n / (n : ℂ)) +
          (F a - y)‖ := by congr 1; ring
      _ ≤ ‖F (e.symm x.val) - F a - (e.symm x.val - a) ^ n / (n : ℂ)‖ +
          ‖F a - y‖ := norm_add_le _ _
      _ < δ + δ := add_lt_add (hsphere_error _ hz) (by
        rw [norm_sub_rev]
        exact mem_ball_iff_norm.mp hy.1)
      _ = r ^ n / (n : ℝ) := by dsimp [δ]; ring
  obtain ⟨hbG, hcmp⟩ := euclideanBallDegree_eq_of_norm_sub_lt hr model hbmodel gc hclose
  have hdegree : euclideanBallDegree (d := 1) hr gc hbG = (n : ℤ) :=
    hcmp.symm.trans hdegmodel
  let Z : Set V := {x | x ∈ closedBall (e a) r ∧ G x = 0}
  let rootEquiv : (f ⁻¹' {y}) ≃ Z :=
    { toFun := fun x => ⟨e x.val.val, by
        constructor
        · simpa only [mem_closedBall, e.dist_map] using x.val.property
        · change e (F (e.symm (e x.val.val)) - y) = 0
          rw [e.symm_apply_apply, e.map_eq_zero_iff, sub_eq_zero]
          exact x.property⟩
      invFun := fun x => ⟨⟨e.symm x.val, by
        simpa only [mem_closedBall, hcoord] using x.property.1⟩, by
          change F (e.symm x.val) = y
          exact sub_eq_zero.mp (e.map_eq_zero_iff.mp x.property.2)⟩
      left_inv := fun x => by
        apply Subtype.ext
        apply Subtype.ext
        exact e.symm_apply_apply x.val.val
      right_inv := fun x => by
        apply Subtype.ext
        exact e.apply_symm_apply x.val }
  let : Finite Z := Finite.of_equiv (f ⁻¹' {y}) rootEquiv
  let : Fintype Z := Fintype.ofFinite Z
  have hZfinite : {x ∈ closedBall (e a) r | G x = 0}.Finite :=
    Set.finite_coe_iff.mp inferInstance
  have hboundary : ∀ x ∈ sphere (e a) r, G x ≠ 0 :=
    fun x hx => hbG ⟨x, sphere_subset_closedBall hx⟩ hx
  have hxD (x : Z) : e.symm x.val ∈ D := by
    have hz : e.symm x.val ∈ closedBall a r := by
      simpa only [mem_closedBall, hcoord] using x.property.1
    refine ⟨hclosed hz, ?_⟩
    intro hza
    change e.symm x.val = a at hza
    have heq : F (e.symm x.val) = y :=
      sub_eq_zero.mp (e.map_eq_zero_iff.mp x.property.2)
    apply hy.2
    change y = F a
    simpa only [hza] using heq.symm
  have hGderiv (x : Z) : HasFDerivAt G
      (e.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((fderiv ℝ F (e.symm x.val)).comp
          e.symm.toContinuousLinearEquiv.toContinuousLinearMap)) x.val := by
    have hd := (hF.contDiffAt (isOpen_ball.mem_nhds (hxD x).1)).differentiableAt
      (by norm_num)
    exact e.toContinuousLinearEquiv.hasFDerivAt.comp x.val
      ((hd.hasFDerivAt.sub_const y).comp x.val
        e.symm.toContinuousLinearEquiv.hasFDerivAt)
  have hGdet (x : Z) :
      LinearMap.det (fderiv ℝ G x.val).toLinearMap = dF (e.symm x.val) := by
    rw [(hGderiv x).fderiv]
    change LinearMap.det
      ((e.toLinearEquiv : ℂ →ₗ[ℝ] V) ∘ₗ
        (fderiv ℝ F (e.symm x.val)).toLinearMap ∘ₗ
        (e.symm.toLinearEquiv : V →ₗ[ℝ] ℂ)) = _
    exact LinearMap.det_conj (fderiv ℝ F (e.symm x.val)).toLinearMap e.toLinearEquiv
  have hlocaldegree (x : Z) :
      euclideanLocalDegree G x.val
        (isolatedZero_of_finite_closedBall_zeroSet hGc hZfinite hboundary
          x.property.1 x.property.2) = (SignType.sign (dF b) : ℤ) := by
    rw [euclideanLocalDegree_eq_sign_det_fderiv _ (hGderiv x).differentiableAt
      (by rw [hGdet]; exact hdet _ (hxD x)), hGdet, hsign _ (hxD x)]
  have hsum : (n : ℤ) = (Fintype.card Z : ℤ) * (SignType.sign (dF b) : ℤ) := by
    calc
      (n : ℤ) = euclideanBallDegree (d := 1) hr gc hbG := hdegree.symm
      _ = ∑ᶠ x : Z, euclideanLocalDegree G x.val
          (isolatedZero_of_finite_closedBall_zeroSet hGc hZfinite hboundary
            x.property.1 x.property.2) :=
        euclideanBallDegree_eq_finsum_localDegrees hr hGc hZfinite hboundary
      _ = ∑ x : Z, (SignType.sign (dF b) : ℤ) := by
        rw [finsum_eq_sum_of_fintype]
        exact Finset.sum_congr rfl (fun x _ => hlocaldegree x)
      _ = (Fintype.card Z : ℤ) * (SignType.sign (dF b) : ℤ) := by simp
  have hcard : Fintype.card Z = n := by
    rcases (hdet b hb).lt_or_gt with hneg | hpos
    · rw [sign_neg hneg] at hsum
      norm_num at hsum
      have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
      have hcZ : (0 : ℤ) ≤ Fintype.card Z := by positivity
      omega
    · rw [sign_pos hpos] at hsum
      norm_num at hsum
      rw [Set.fintypeCard_eq_ncard]
      exact_mod_cast hsum.symm
  change ENat.card (f ⁻¹' {y}) = (n : ℕ∞)
  rw [ENat.card_congr rootEquiv, ENat.card_eq_coe_fintype_card, hcard]

end DifferentialGeometry.Topology.Covering
