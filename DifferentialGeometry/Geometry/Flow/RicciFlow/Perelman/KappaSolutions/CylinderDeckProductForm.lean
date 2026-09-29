import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderDeckDifferential
import DifferentialGeometry.Geometry.Coordinates.Calculus.FixedBaseDerivative
import DifferentialGeometry.Geometry.Metric.Sphere.Isometry.Representation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry
open scoped Manifold ContDiff

local notation "SphereAmbient" => EuclideanSpace ℝ (Fin 3)
local notation "SphereTwo" => Metric.sphere (0 : SphereAmbient) 1
private abbrev CylinderI := (𝓡 2).prod (𝓘(ℝ, ℝ))
local notation "sphereMetric" => roundMetric (E := SphereAmbient) (n := 2)

private local instance cylinderProductSphereDimension :
    Fact (Module.finrank ℝ SphereAmbient = 2 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

private local instance cylinderProductSpherePreconnected : PreconnectedSpace SphereTwo :=
  Subtype.preconnectedSpace (isPreconnected_sphere
    (Module.one_lt_rank_of_one_lt_finrank (by
      norm_num [finrank_euclideanSpace_fin] : 1 < Module.finrank ℝ SphereAmbient)) 0 1)

private def cylinderProductSpherePoint : SphereTwo :=
  ⟨EuclideanSpace.single (0 : Fin 3) (1 : ℝ), by
    simp only [Metric.mem_sphere, dist_zero_right, PiLp.norm_single, norm_one]⟩

variable (Phi : (SphereTwo × ℝ) ≃ₘ⟮CylinderI, CylinderI⟯ (SphereTwo × ℝ))

private theorem cylinderProduct_fst_horizontal (x : SphereTwo) (s : ℝ)
    (v : TangentSpace (𝓡 2) x) :
    mfderiv (𝓡 2) (𝓡 2) (fun y : SphereTwo => (Phi (y, s)).1) x v =
      (mfderiv CylinderI CylinderI Phi (x, s) (v, 0)).1 := by
  change mfderiv (𝓡 2) (𝓡 2)
    ((fun p : SphereTwo × ℝ => (Phi p).1) ∘ fun y : SphereTwo => (y, s)) x v = _
  erw [mfderiv_comp_apply x ((Phi.mdifferentiable (by decide) (x, s)).fst)
    (mdifferentiableAt_id.prodMk mdifferentiableAt_const) v, mfderiv_prod_left]
  change mfderiv CylinderI (𝓡 2)
    ((Prod.fst : SphereTwo × ℝ → SphereTwo) ∘ Phi) (x, s) (v, 0) = _
  erw [mfderiv_comp_apply (x, s) mdifferentiableAt_fst
    (Phi.mdifferentiable (by decide) (x, s)) (v, 0), mfderiv_fst]
  rfl

private theorem cylinderProduct_fst_vertical (x : SphereTwo) (s a : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (fun r : ℝ => (Phi (x, r)).1) s a =
      (mfderiv CylinderI CylinderI Phi (x, s) (0, a)).1 := by
  change mfderiv 𝓘(ℝ, ℝ) (𝓡 2)
    ((fun p : SphereTwo × ℝ => (Phi p).1) ∘ fun r : ℝ => (x, r)) s a = _
  rw [mfderiv_comp_apply s ((Phi.mdifferentiable (by decide) (x, s)).fst)
    (mdifferentiableAt_const.prodMk mdifferentiableAt_id) a, mfderiv_prod_right]
  change mfderiv CylinderI (𝓡 2)
    ((Prod.fst : SphereTwo × ℝ → SphereTwo) ∘ Phi) (x, s) (0, a) = _
  rw [mfderiv_comp_apply (x, s) mdifferentiableAt_fst
    (Phi.mdifferentiable (by decide) (x, s)) (0, a), mfderiv_fst]
  rfl

private theorem cylinderProduct_snd_horizontal (x : SphereTwo) (s : ℝ)
    (v : TangentSpace (𝓡 2) x) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y : SphereTwo => (Phi (y, s)).2) x v =
      (mfderiv CylinderI CylinderI Phi (x, s) (v, 0)).2 := by
  change mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
    ((fun p : SphereTwo × ℝ => (Phi p).2) ∘ fun y : SphereTwo => (y, s)) x v = _
  erw [mfderiv_comp_apply x ((Phi.mdifferentiable (by decide) (x, s)).snd)
    (mdifferentiableAt_id.prodMk mdifferentiableAt_const) v, mfderiv_prod_left]
  change mfderiv CylinderI 𝓘(ℝ, ℝ)
    ((Prod.snd : SphereTwo × ℝ → ℝ) ∘ Phi) (x, s) (v, 0) = _
  erw [mfderiv_comp_apply (x, s) mdifferentiableAt_snd
    (Phi.mdifferentiable (by decide) (x, s)) (v, 0), mfderiv_snd]
  rfl

private theorem cylinderProduct_snd_vertical (x : SphereTwo) (s a : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r : ℝ => (Phi (x, r)).2) s a =
      (mfderiv CylinderI CylinderI Phi (x, s) (0, a)).2 := by
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
    ((fun p : SphereTwo × ℝ => (Phi p).2) ∘ fun r : ℝ => (x, r)) s a = _
  rw [mfderiv_comp_apply s ((Phi.mdifferentiable (by decide) (x, s)).snd)
    (mdifferentiableAt_const.prodMk mdifferentiableAt_id) a, mfderiv_prod_right]
  change mfderiv CylinderI 𝓘(ℝ, ℝ)
    ((Prod.snd : SphereTwo × ℝ → ℝ) ∘ Phi) (x, s) (0, a) = _
  rw [mfderiv_comp_apply (x, s) mdifferentiableAt_snd
    (Phi.mdifferentiable (by decide) (x, s)) (0, a), mfderiv_snd]
  rfl

private theorem cylinderProduct_line_affine (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b)
    (hsquare : ∀ s : ℝ, deriv b s ^ 2 = 1) :
    ∃ epsilon c : ℝ, epsilon ^ 2 = 1 ∧ ∀ s : ℝ, b s = epsilon * s + c := by
  have hd : Differentiable ℝ (deriv b) :=
    (contDiff_infty_iff_deriv.mp hb).2.differentiable (by decide)
  have hsecond : ∀ s : ℝ, deriv (deriv b) s = 0 := by
    intro s
    have hfun : (fun r : ℝ => deriv b r ^ 2) = fun _ => (1 : ℝ) := funext hsquare
    have hdiff := ((hd s).hasDerivAt.fun_pow 2).deriv
    rw [hfun, deriv_const] at hdiff
    have hmul : deriv b s * deriv (deriv b) s = 0 := by
      norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one] at hdiff
      nlinarith [hdiff]
    have hnonzero : deriv b s ≠ 0 := by
      intro hz
      have h := hsquare s
      rw [hz] at h
      norm_num at h
    exact (mul_eq_zero.mp hmul).resolve_left hnonzero
  have hconstant (s : ℝ) : deriv b s = deriv b 0 :=
    is_const_of_deriv_eq_zero hd hsecond s 0
  have hsubdiff : Differentiable ℝ (fun s : ℝ => b s - deriv b 0 * s) :=
    (hb.differentiable (by decide)).sub (differentiable_id.const_mul (deriv b 0))
  have hsubzero : ∀ s : ℝ, deriv (fun r : ℝ => b r - deriv b 0 * r) s = 0 := by
    intro s
    have h := ((hb.differentiable (by decide) s).hasDerivAt.sub
      ((hasDerivAt_id s).const_mul (deriv b 0))).deriv
    calc
      _ = deriv b s - deriv b 0 * 1 := h
      _ = 0 := by rw [hconstant, mul_one, sub_self]
  refine ⟨deriv b 0, b 0, hsquare 0, ?_⟩
  intro s
  have h := is_const_of_deriv_eq_zero hsubdiff hsubzero s 0
  simp only [mul_zero, sub_zero] at h
  linarith

variable {T t₀ t₁ : ℝ} (hdifferent : t₀ ≠ t₁)
  (hmetric : ∀ t : ℝ, t = t₀ ∨ t = t₁ →
    ∀ (p : SphereTwo × ℝ) (v w : TangentSpace (𝓡 2) p.1) (a c : ℝ),
      (2 * (T - t)) * (sphereMetric).inner (Phi p).1
          (mfderiv CylinderI CylinderI Phi p (v, a)).1
          (mfderiv CylinderI CylinderI Phi p (w, c)).1 +
        (mfderiv CylinderI CylinderI Phi p (v, a)).2 *
          (mfderiv CylinderI CylinderI Phi p (w, c)).2 =
      (2 * (T - t)) * (sphereMetric).inner p.1 v w + a * c)

include hdifferent hmetric

theorem cylinderDeck_fst_eq_at_zero (x : SphereTwo) (s : ℝ) :
    (Phi (x, s)).1 = (Phi (x, 0)).1 := by
  let f : ℝ → SphereTwo := fun r => (Phi (x, r)).1
  have hf : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ f :=
    (Phi.contMDiff.comp (contMDiff_const.prodMk contMDiff_id)).fst
  have hz (r : ℝ) : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) f r = 0 := by
    apply ContinuousLinearMap.ext
    intro a
    change mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (fun q : ℝ => (Phi (x, q)).1) r a = 0
    exact (cylinderProduct_fst_vertical Phi x r a).trans
      (cylinderDeck_mfderiv_preserves_factors Phi hdifferent hmetric (x, r) 0 a).2
  have hcoe : ContMDiff (𝓡 2) 𝓘(ℝ, SphereAmbient) ∞
      ((↑) : SphereTwo → SphereAmbient) := contMDiff_coe_sphere
  have hzero : ∀ r : ℝ, fderiv ℝ (fun q : ℝ => (f q : SphereAmbient)) r = 0 := by
    intro r
    have h : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, SphereAmbient)
        (((↑) : SphereTwo → SphereAmbient) ∘ f) r = 0 := by
      apply ContinuousLinearMap.ext
      intro a
      rw [mfderiv_comp_apply r (hcoe.mdifferentiable (by decide) (f r))
        (hf.mdifferentiable (by decide) r) a, hz, zero_apply, map_zero]
      rfl
    rw [mfderiv_eq_fderiv] at h
    apply ContinuousLinearMap.ext
    intro a
    have ha := congrArg (fun D => NormedSpace.fromTangentSpace (𝕜 := ℝ) (f r : SphereAmbient)
      (D ((NormedSpace.fromTangentSpace (𝕜 := ℝ) r).symm a))) h
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, zero_apply, map_zero] using! ha
  apply Subtype.ext
  exact is_const_of_fderiv_eq_zero
    ((hcoe.comp hf).contDiff.differentiable (by decide)) hzero s 0

theorem cylinderDeck_snd_eq_at_point (x y : SphereTwo) (s : ℝ) :
    (Phi (x, s)).2 = (Phi (y, s)).2 := by
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun z : SphereTwo => (Phi (z, s)).2) :=
    (Phi.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)).snd
  have hz : ∀ z : SphereTwo,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun q : SphereTwo => (Phi (q, s)).2) z = 0 := by
    intro z
    apply ContinuousLinearMap.ext
    intro v
    change mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun q : SphereTwo => (Phi (q, s)).2) z v = 0
    rw [cylinderProduct_snd_horizontal]
    exact (cylinderDeck_mfderiv_preserves_factors Phi hdifferent hmetric (z, s) v 0).1
  exact (DifferentialGeometry.isLocallyConstant_of_mfderiv_eq_zero
    (hf.mdifferentiable (by decide)) hz).apply_eq_of_preconnectedSpace x y

theorem cylinderDeck_exists_product_affine :
    ∃ (A : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo) (b : ℝ ≃ᵃⁱ[ℝ] ℝ),
      (∀ (x : SphereTwo) (v w : TangentSpace (𝓡 2) x),
        (sphereMetric).inner (A x)
            (mfderiv (𝓡 2) (𝓡 2) A x v) (mfderiv (𝓡 2) (𝓡 2) A x w) =
          (sphereMetric).inner x v w) ∧
      (∀ (x : SphereTwo) (s : ℝ), Phi (x, s) = (A x, b s)) ∧
      ∃ epsilon c : ℝ, epsilon ^ 2 = 1 ∧ ∀ s : ℝ, b s = epsilon * s + c := by
  let x₀ : SphereTwo := cylinderProductSpherePoint
  let a : SphereTwo → SphereTwo := fun x => (Phi (x, 0)).1
  let line : ℝ → ℝ := fun s => (Phi (x₀, s)).2
  have hproduct (x : SphereTwo) (s : ℝ) : Phi (x, s) = (a x, line s) := by
    exact Prod.ext (cylinderDeck_fst_eq_at_zero Phi hdifferent hmetric x s)
      (cylinderDeck_snd_eq_at_point Phi hdifferent hmetric x x₀ s)
  let invA : SphereTwo → SphereTwo := fun y => (Phi.symm (y, line 0)).1
  have hleft : Function.LeftInverse invA a := by
    intro x
    change (Phi.symm (a x, line 0)).1 = x
    rw [← hproduct x 0]
    exact congrArg Prod.fst (Phi.symm_apply_apply (x, 0))
  have hright : Function.RightInverse invA a := by
    intro y
    calc
      a (invA y) = (Phi ((Phi.symm (y, line 0)).1, (Phi.symm (y, line 0)).2)).1 :=
        (cylinderDeck_fst_eq_at_zero Phi hdifferent hmetric
          (Phi.symm (y, line 0)).1 (Phi.symm (y, line 0)).2).symm
      _ = y := congrArg Prod.fst (Phi.apply_symm_apply (y, line 0))
  let A : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo := {
    toEquiv := {
      toFun := a
      invFun := invA
      left_inv := hleft
      right_inv := hright }
    contMDiff_toFun :=
      (Phi.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)).fst
    contMDiff_invFun :=
      (Phi.symm.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)).fst }
  have hA : ∀ (x : SphereTwo) (v w : TangentSpace (𝓡 2) x),
      (sphereMetric).inner (A x)
          (mfderiv (𝓡 2) (𝓡 2) A x v) (mfderiv (𝓡 2) (𝓡 2) A x w) =
        (sphereMetric).inner x v w := by
    intro x v w
    change (sphereMetric).inner (Phi (x, 0)).1
        (mfderiv (𝓡 2) (𝓡 2) (fun y : SphereTwo => (Phi (y, 0)).1) x v)
        (mfderiv (𝓡 2) (𝓡 2) (fun y : SphereTwo => (Phi (y, 0)).1) x w) = _
    rw [cylinderProduct_fst_horizontal, cylinderProduct_fst_horizontal]
    exact (cylinderDeck_mfderiv_block_inner Phi hdifferent hmetric (x, 0) v w 0 0).1
  have hlineSmooth : ContDiff ℝ ∞ line :=
    ((Phi.contMDiff.comp (contMDiff_const.prodMk contMDiff_id)).snd).contDiff
  have hlineSquare : ∀ s : ℝ, deriv line s ^ 2 = 1 := by
    intro s
    have hderiv : deriv line s =
        (mfderiv CylinderI CylinderI Phi (x₀, s) (0, 1)).2 := by
      change fderiv ℝ (fun r : ℝ => (Phi (x₀, r)).2) s 1 = _
      have h := cylinderProduct_snd_vertical Phi x₀ s 1
      rw [mfderiv_eq_fderiv] at h
      have hv := congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) ((Phi (x₀, s)).2)) h
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply] using! hv
    rw [hderiv, pow_two]
    convert (cylinderDeck_mfderiv_block_inner Phi hdifferent hmetric (x₀, s) 0 0 1 1).2
      using 1 <;> first | rfl | norm_num
  obtain ⟨epsilon, c, hε, hline⟩ := cylinderProduct_line_affine line hlineSmooth hlineSquare
  have hAff : ∃ b : ℝ ≃ᵃⁱ[ℝ] ℝ, ∀ s : ℝ, b s = epsilon * s + c := by
    rcases sq_eq_one_iff.mp hε with hplus | hminus
    · refine ⟨AffineIsometryEquiv.vaddConst ℝ c, ?_⟩
      intro s
      change s + c = epsilon * s + c
      rw [hplus, one_mul]
    · refine ⟨(LinearIsometryEquiv.neg ℝ).toAffineIsometryEquiv.trans
        (AffineIsometryEquiv.vaddConst ℝ c), ?_⟩
      intro s
      change -s + c = epsilon * s + c
      rw [hminus, neg_one_mul]
  obtain ⟨b, hb⟩ := hAff
  refine ⟨A, b, hA, ?_, epsilon, c, hε, hb⟩
  intro x s
  exact (hproduct x s).trans (Prod.ext rfl ((hline s).trans (hb s).symm))

omit hdifferent hmetric in
private theorem cylinderProduct_sphere_orthogonal
    (A : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo)
    (hA : ∀ (x : SphereTwo) (v w : TangentSpace (𝓡 2) x),
      (sphereMetric).inner (A x)
          (mfderiv (𝓡 2) (𝓡 2) A x v) (mfderiv (𝓡 2) (𝓡 2) A x w) =
        (sphereMetric).inner x v w) :
    ∃ e : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient, sphereDiffeo (n := 2) e = A := by
  let p : SphereTwo := cylinderProductSpherePoint
  let L : TangentSpace (𝓡 2) p ≃L[ℝ] TangentSpace (𝓡 2) (A p) :=
    A.mfderivToContinuousLinearEquiv (by decide) p
  have hL : ∀ v w, (sphereMetric).inner (A p) (L v) (L w) =
      (sphereMetric).inner p v w := by
    intro v w
    with_unfolding_all exact hA p v w
  obtain ⟨e, hep, hde⟩ := ambient_iso_of_tan (E := SphereAmbient) (n := 2) p (A p) L hL
  refine ⟨e, ?_⟩
  have hfun : (fun x : SphereTwo => sphereDiffeo (n := 2) e x) = fun x => A x := by
    apply Riemannian.localIso_rigid (sphereMetric) (sphereMetric)
      (sphereDiffeo (n := 2) e).isLocalDiffeomorph A.isLocalDiffeomorph
      (fun x v w => (roundInner_sphereDiffeo e x v w).symm)
      (fun x v w => (hA x v w).symm) p
    · apply Subtype.ext
      simpa only [sphereDiffeo_coe] using hep
    · apply ContinuousLinearMap.ext
      intro v
      with_unfolding_all exact hde v
  apply Diffeomorph.ext
  exact congrFun hfun

theorem cylinderDeck_exists_orthogonal_product :
    ∃ (e : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient) (epsilon c : ℝ),
      epsilon ^ 2 = 1 ∧ ∀ (x : SphereTwo) (s : ℝ),
        Phi (x, s) = (sphereDiffeo (n := 2) e x, epsilon * s + c) := by
  obtain ⟨A, b, hA, hproduct, epsilon, c, hε, hb⟩ :=
    cylinderDeck_exists_product_affine Phi hdifferent hmetric
  obtain ⟨e, he⟩ := cylinderProduct_sphere_orthogonal A hA
  refine ⟨e, epsilon, c, hε, ?_⟩
  intro x s
  rw [hproduct, he, hb]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
