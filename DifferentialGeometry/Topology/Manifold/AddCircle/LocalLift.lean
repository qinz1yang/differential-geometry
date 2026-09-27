import DifferentialGeometry.Topology.Manifold.AddCircle.ParameterDerivative
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

section

open Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

theorem exists_contDiffWithinAt_addCircle_lift {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {U : Set E} {q : E} {f : E → AddCircle (1 : ℝ)}
    (hf : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f U q) :
    ∃ φ : E → ℝ, ContDiffWithinAt ℝ ∞ φ U q ∧
      (fun p => (φ p : AddCircle (1 : ℝ))) =ᶠ[𝓝[U] q] f := by
  obtain ⟨r₀, hr₀⟩ : ∃ r : ℝ, (r : AddCircle (1 : ℝ)) = f q :=
    ⟨_, AddCircle.coe_equivIco (p := (1 : ℝ)) (a := (0 : ℝ))⟩
  obtain ⟨Φ, hqΦ, hΦ⟩ := AddCircle.isLocalDiffeomorph_coe r₀
  have hΦq : Φ r₀ = f q := (hΦ hqΦ).symm.trans hr₀
  have hfq : f q ∈ Φ.target := by
    rw [← hΦq]
    exact Φ.toPartialEquiv.map_source hqΦ
  refine ⟨fun p => (Φ.symm : AddCircle (1 : ℝ) → ℝ) (f p), ?_, ?_⟩
  · have hsymm : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
        (Φ.symm : AddCircle (1 : ℝ) → ℝ) (f q) :=
      Φ.symm.contMDiffOn_toFun.contMDiffAt (Φ.open_target.mem_nhds hfq)
    have hcomp : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
        ((Φ.symm : AddCircle (1 : ℝ) → ℝ) ∘ f) U q :=
      hsymm.contMDiffWithinAt.comp q hf (fun _ _ => mem_univ _)
    exact contMDiffWithinAt_iff_contDiffWithinAt.mp hcomp
  · filter_upwards
      [(hf.continuousWithinAt).preimage_mem_nhdsWithin (Φ.open_target.mem_nhds hfq)]
      with p hfp
    have h1 : Φ ((Φ.symm : AddCircle (1 : ℝ) → ℝ) (f p)) = f p :=
      Φ.toPartialEquiv.right_inv' hfp
    have h2 : (((Φ.symm : AddCircle (1 : ℝ) → ℝ) (f p)) : AddCircle (1 : ℝ)) =
        Φ ((Φ.symm : AddCircle (1 : ℝ) → ℝ) (f p)) :=
      hΦ (Φ.toPartialEquiv.map_target hfp)
    exact h2.trans h1

end DifferentialGeometry.Topology

end

noncomputable section
open scoped Manifold ContDiff Topology
open Filter

namespace AddCircle

theorem hasDerivWithinAt_of_local_lift {J : Set ℝ} {t : ℝ} {φ : ℝ → ℝ}
    {γ : ℝ → AddCircle (1 : ℝ)} {b : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t)
    (hφ : DifferentiableWithinAt ℝ φ J t)
    (heq : (fun s => (φ s : AddCircle (1 : ℝ))) =ᶠ[𝓝[J] t] γ)
    (hγ : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) γ J t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (b • parameterTangent (γ t)))) :
    HasDerivWithinAt φ b J t := by
  have heqt : (φ t : AddCircle (1 : ℝ)) = γ t := heq.eq_of_nhdsWithin ht
  have hφm := hφ.hasDerivWithinAt.hasFDerivWithinAt.hasMFDerivWithinAt
  have hq := (contMDiff_coe.mdifferentiableAt (x := φ t) (by decide : (∞ : ℕ∞ω) ≠ 0)).hasMFDerivAt
  have hcomp := hq.comp_hasMFDerivWithinAt t hφm
  have hγ' := hγ.congr_of_eventuallyEq heq heqt
  have heqd := (hcomp.mfderivWithin hJ.uniqueMDiffWithinAt).symm.trans
    (hγ'.mfderivWithin hJ.uniqueMDiffWithinAt)
  have heqd1 := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) heqd
  have hb : derivWithin φ J t = b := by
    apply (bijective_mfderiv_coe (φ t)).1
    have hsmul : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (fun x : ℝ => (x : AddCircle (1 : ℝ))) (φ t) b =
        b • parameterTangent (γ t) := by
      rw [← heqt, parameterTangent_coe]
      let L : ℝ →L[ℝ] ℝ := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (fun x : ℝ => (x : AddCircle (1 : ℝ))) (φ t)
      change L b = b • L 1
      simpa only [smul_eq_mul, mul_one] using L.map_smul b (1 : ℝ)
    rw [hsmul]
    change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun x : ℝ => (x : AddCircle (1 : ℝ))) (φ t))
      ((1 : ℝ) • derivWithin φ J t) = (1 : ℝ) • (b • parameterTangent (γ t)) at heqd1
    simpa only [one_smul] using heqd1
  rw [← hb]
  exact hφ.hasDerivWithinAt

end AddCircle

end
