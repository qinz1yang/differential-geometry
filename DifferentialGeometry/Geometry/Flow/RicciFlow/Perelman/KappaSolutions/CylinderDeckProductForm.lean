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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry
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
