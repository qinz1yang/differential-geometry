import DifferentialGeometry.Topology.Manifold.Attachment.RadialCollarOrientation
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

section

set_option autoImplicit false
noncomputable section

open Set Function Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold.Attachment

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

theorem mfderiv_radialCollarOrientationMap {L B : ℝ} (hB : 0 < B)
    (q : S2 × Ico (0 : ℝ) B)
    (v : EuclideanSpace ℝ (Fin 2)) (t : EuclideanSpace ℝ (Fin 1)) :
    let := halfClosedIntervalChartedSpace hB
    mfderiv IR (𝓡 3) (radialCollarOrientationMap L B) q (v, t) =
      (L + q.2.val) • mvfderiv (I := (𝓡 2)) (Subtype.val : S2 → E3) q.1 v +
        (mvfderiv (I := (𝓡∂ 1)) (Subtype.val : Ico (0 : ℝ) B → ℝ) q.2 t : ℝ) • q.1.val := by
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  let a : S2 × Ico (0 : ℝ) B → ℝ := fun q => L + q.2.val
  let g : S2 × Ico (0 : ℝ) B → E3 := fun q => q.1.val
  have hs := (isSmoothEmbedding_halfClosedInterval_inclusion hB).contMDiff
  have ha : MDifferentiableAt IR 𝓘(ℝ) a q :=
    (contMDiff_const.add (hs.comp contMDiff_snd)).mdifferentiableAt (by simp)
  have hg : MDifferentiableAt IR (𝓡 3) g q :=
    ((contMDiff_coe_sphere (m := ∞)).comp contMDiff_fst).mdifferentiableAt (by simp)
  have h := congrArg (fun D => D (v, t)) (mvfderiv_smul ha hg)
  change mfderiv IR (𝓡 3) (fun q => a q • g q) q (v, t) =
    a q • mvfderiv (I := IR) g q (v, t) + (mvfderiv (I := IR) a q (v, t)) • g q at h
  change mfderiv IR (𝓡 3) (fun q => a q • g q) q (v, t) = _
  rw [h]
  have hga : mvfderiv (I := IR) g q (v, t) =
      mvfderiv (I := (𝓡 2)) (Subtype.val : S2 → E3) q.1 v := by
    change mfderiv IR (𝓡 3) ((Subtype.val : S2 → E3) ∘ Prod.fst) q (v, t) = _
    erw [mfderiv_comp_apply q ((contMDiff_coe_sphere (m := ∞)).mdifferentiableAt (by simp))
      mdifferentiableAt_fst, mfderiv_fst]
    rfl
  have haa : mvfderiv (I := IR) a q (v, t) =
      mvfderiv (I := (𝓡∂ 1)) (Subtype.val : Ico (0 : ℝ) B → ℝ) q.2 t := by
    change mfderiv IR 𝓘(ℝ) (fun p : S2 × Ico (0 : ℝ) B => L + p.2.val) q (v, t) = _
    change mfderiv IR 𝓘(ℝ) (fun p : S2 × Ico (0 : ℝ) B => L + p.2.val) q (v, t) =
      mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Ico (0 : ℝ) B → ℝ) q.2 t
    erw [mfderiv_add mdifferentiableAt_const ((hs.comp contMDiff_snd).mdifferentiableAt (by simp)),
      mfderiv_const, zero_add]
    erw [mfderiv_comp_apply q (hs.mdifferentiableAt (by simp)) mdifferentiableAt_snd, mfderiv_snd]
    rfl
  rw [hga, haa]

end DifferentialGeometry.Topology.Manifold.Attachment

end

end

section

set_option autoImplicit false
noncomputable section

open Set Function Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold.Attachment

private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev E1 := EuclideanSpace ℝ (Fin 1)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

theorem mfderiv_sphere_linear_isometry_coe
    (A : E3 ≃ₗᵢ[ℝ] E3) (a : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2)
    (ha : ∀ z, (a z : E3) = A z) (z : S2) (v : E2) :
    mvfderiv (I := (𝓡 2)) (Subtype.val : S2 → E3) (a z)
        (mfderiv (𝓡 2) (𝓡 2) a z v) =
      A (mvfderiv (I := (𝓡 2)) (Subtype.val : S2 → E3) z v) := by
  have heq : (Subtype.val : S2 → E3) ∘ a = A ∘ (Subtype.val : S2 → E3) := funext ha
  have hc : MDifferentiableAt (𝓡 2) (𝓡 3) (Subtype.val : S2 → E3) (a z) :=
    (contMDiff_coe_sphere (m := ∞)).mdifferentiableAt (by simp)
  have h := mfderiv_comp_apply z hc (a.contMDiff.mdifferentiableAt (by simp)) v
  rw [heq] at h
  have hc' : MDifferentiableAt (𝓡 2) (𝓡 3) (Subtype.val : S2 → E3) z :=
    (contMDiff_coe_sphere (m := ∞)).mdifferentiableAt (by simp)
  erw [mfderiv_comp_apply z ((A.contDiff (n := ∞)).contMDiff.mdifferentiableAt (by simp)) hc',
    mfderiv_eq_fderiv, A.toContinuousLinearEquiv.fderiv] at h
  exact h.symm

theorem radialCollar_mfderiv_normal {L B : ℝ} (hB : 0 < B) (z : S2) (ν : E1) :
    letI := halfClosedIntervalChartedSpace hB
    let q : S2 × Ico (0 : ℝ) B := (z, ⟨0, le_rfl, hB⟩)
    mvfderiv (I := (𝓡∂ 1)) (Subtype.val : Ico (0 : ℝ) B → ℝ) q.2 ν = 1 →
      mfderiv IR (𝓡 3) (radialCollarOrientationMap L B) q (0, ν) = (z : E3) := by
  let := halfClosedIntervalChartedSpace hB
  intro q hν
  erw [mfderiv_radialCollarOrientationMap hB q 0 ν, map_zero, smul_zero, zero_add, hν, one_smul]

theorem radialCollar_mfderiv_tangent {L B : ℝ} (hB : 0 < B)
    (A : E3 ≃ₗᵢ[ℝ] E3) (a : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2)
    (ha : ∀ z, (a z : E3) = A z) (z : S2) (v : E2) :
    letI := halfClosedIntervalChartedSpace hB
    let q : S2 × Ico (0 : ℝ) B := (a z, ⟨0, le_rfl, hB⟩)
    mfderiv IR (𝓡 3) (radialCollarOrientationMap L B) q
      (mfderiv (𝓡 2) (𝓡 2) a z v, (0 : E1)) =
        L • A (mvfderiv (I := (𝓡 2)) (Subtype.val : S2 → E3) z v) := by
  let := halfClosedIntervalChartedSpace hB
  intro q
  erw [mfderiv_radialCollarOrientationMap hB q _ 0, map_zero, zero_smul, add_zero]
  change (L + 0) • _ = _
  rw [add_zero, mfderiv_sphere_linear_isometry_coe A a ha z v]
  rfl

end DifferentialGeometry.Topology.Manifold.Attachment

end

end
