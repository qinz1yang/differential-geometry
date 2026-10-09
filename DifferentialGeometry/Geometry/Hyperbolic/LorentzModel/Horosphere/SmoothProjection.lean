import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Horosphere.SmoothCoordinates
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Horosphere.Projection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.HorosphereProjection

open Hyperbolic (HUpper)
open HyperbolicBoundary (BoundaryH)
open AsymptoticRays (rayTo)
open Busemann (busemann)

variable {n : ℕ}

theorem contMDiff_rayTo (ξ : BoundaryH n) (r : ℕ∞ω) :
    ContMDiff ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) r
      (fun z : HUpper n × ℝ => rayTo z.1 ξ z.2) := by
  let I := (𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ, ℝ)
  have hs : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) r
      (fun z : HUpper n × ℝ => (Hyperboloid.hUpperIsometryEquiv n z.1).space) :=
    Hyperboloid.contMDiff_space.comp
      ((Hyperboloid.hUpperDiffeomorph n r).contMDiff.comp contMDiff_fst)
  have he : ContMDiff I 𝓘(ℝ, ℝ) r
      (fun z : HUpper n × ℝ => Real.exp (-z.2)) :=
    Real.contDiff_exp.contMDiff.comp contMDiff_snd.neg
  have hh : ContMDiff I 𝓘(ℝ, ℝ) r
      (fun z : HUpper n × ℝ => Real.sinh z.2) :=
    Real.contDiff_sinh.contMDiff.comp contMDiff_snd
  have hd : ContMDiff I 𝓘(ℝ, ℝ) r
      (fun z : HUpper n × ℝ => Real.exp (busemann ξ z.1)) :=
    Real.contDiff_exp.contMDiff.comp ((Busemann.contMDiff_busemann ξ r).comp contMDiff_fst)
  have hv := (he.smul hs).add
    ((hh.div₀ hd (fun z => Real.exp_ne_zero _)).smul
      (contMDiff_const (c := BoundaryTopology.spatial ξ)))
  have h := (Hyperboloid.hUpperDiffeomorph n r).symm.contMDiff.comp
    (Hyperboloid.contMDiff_ofSpace.comp hv)
  apply h.congr
  intro z
  dsimp only [Function.comp_def]
  apply (Hyperboloid.hUpperIsometryEquiv n).injective
  rw [Hyperboloid.hUpperDiffeomorph_symm_apply, IsometryEquiv.apply_symm_apply]
  apply Hyperboloid.ext
  apply PiLp.ext
  intro i
  rw [Hyperboloid.space_ofSpace]
  symm
  change Real.exp (-z.2) * (Hyperboloid.hUpperIsometryEquiv n z.1).space i +
      (Real.sinh z.2 / Real.exp (busemann ξ z.1)) * BoundaryTopology.spatial ξ i =
        (Hyperboloid.hUpperIsometryEquiv n (rayTo z.1 ξ z.2)).space i
  rw [Hyperboloid.hUpperIsometryEquiv_space_apply,
    Hyperboloid.hUpperIsometryEquiv_space_apply, BoundaryTopology.spatial_apply,
    rayTo_val_exp]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [busemann, Real.exp_log (Busemann.neg_lorB_upper_boundary_pos z.1 ξ)]

theorem contMDiff_retract (ξ : BoundaryH n) (c : ℝ) (r : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) r (retract ξ c) :=
  (contMDiff_rayTo ξ r).comp
    (contMDiff_id.prodMk ((Busemann.contMDiff_busemann ξ r).sub contMDiff_const))

end DifferentialGeometry.HorosphereProjection

namespace DifferentialGeometry.Busemann

open Hyperbolic (HUpper)
open HyperbolicBoundary (BoundaryH)
open AsymptoticRays (rayTo)
open HorosphereProjection (contMDiff_rayTo busemann_rayTo)

variable {n : ℕ}

theorem mfderiv_busemann_ne_zero (ξ : BoundaryH n) (p : HUpper n) :
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) (busemann ξ) p ≠ 0 := by
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let c : ℝ → HUpper n := fun t => rayTo p ξ t
  have hp : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun t : ℝ => (p, t)) := contMDiff_const.prodMk contMDiff_id
  have hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ c := (contMDiff_rayTo ξ ∞).comp hp
  have hc0 : c 0 = p := AsymptoticRays.rayTo_zero p ξ
  have he : busemann ξ ∘ c = fun t : ℝ => busemann ξ p - t :=
    funext fun t => busemann_rayTo p ξ t
  have hf : MDifferentiableAt I 𝓘(ℝ, ℝ) (busemann ξ) (c 0) :=
    (Busemann.contMDiff_busemann ξ ∞).mdifferentiable (by simp) (c 0)
  have hd := mfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := I) (I'' := 𝓘(ℝ, ℝ))
    0 hf (hc.mdifferentiable (by simp) 0)
    ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1)
  intro hz
  have hz0 : mfderiv I 𝓘(ℝ, ℝ) (busemann ξ) (c 0) = 0 := by
    change (show EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ from
      mfderiv I 𝓘(ℝ, ℝ) (busemann ξ) (c 0)) = 0
    exact (congrArg (fun x : HUpper n => (show EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ from
      mfderiv I 𝓘(ℝ, ℝ) (busemann ξ) x)) hc0).trans hz
  rw [hz0, zero_apply, he, mfderiv_eq_fderiv] at hd
  have hder : HasDerivAt (fun t : ℝ => busemann ξ p - t) (-1) 0 := by
    convert! (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).const_sub (busemann ξ p) using 1
  rw [hder.hasFDerivAt.fderiv] at hd
  have hval := congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) (busemann ξ p - (0 : ℝ))) hd
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, one_mul] at hval
  have hc : (-1 : ℝ) = 0 := by convert! hval using 1
  norm_num at hc

end DifferentialGeometry.Busemann
