import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace



noncomputable section

open Set Function Bundle Manifold
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]




theorem contMDiffAt_deriv_fst {f : ℝ × M → ℝ} {q : ℝ × M}
    (hf : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ f q) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => deriv (fun r => f (r, p.2)) p.1) q := by
  have hcomp : ContMDiffAt ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : (ℝ × M) × ℝ => f (p.2, p.1.2)) (q, q.1) :=
    hf.comp (q, q.1) (contMDiffAt_snd.prodMk (contMDiffAt_snd.comp _ contMDiffAt_fst))
  have h := hcomp.mfderiv_apply (m := ∞) (fun p : ℝ × M => fun r : ℝ => f (r, p.2))
    Prod.fst id (fun _ : ℝ × M => (1 : ℝ)) contMDiffAt_fst contMDiffAt_id contMDiffAt_const (by simp)
  convert h using 1
  funext p
  simp only [inTangentCoordinates, mfderiv_eq_fderiv]
  dsimp only [ContinuousLinearMap.inCoordinates]
  simp only [TangentBundle.continuousLinearMapAt_model_space,
    TangentBundle.symmL_model_space]
  change deriv (fun r => f (r, p.2)) p.1 =
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f (p.1, p.2)))
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (f (p.1, p.2))).symm
        (fderiv ℝ (fun r => f (r, p.2)) p.1
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) p.1)
            ((NormedSpace.fromTangentSpace (𝕜 := ℝ) p.1).symm 1))))
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  rfl



theorem contDiffAt_deriv_fst {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : ℝ × V → ℝ} {q : ℝ × V} (hf : ContDiffAt ℝ ∞ f q) :
    ContDiffAt ℝ ∞ (fun p : ℝ × V => deriv (fun r => f (r, p.2)) p.1) q := by
  have h := hf.contMDiffAt
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h
  have hd := contMDiffAt_deriv_fst h
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hd
  exact hd.contDiffAt

end DifferentialGeometry.Geometry

end

section

noncomputable section

open Set Function Bundle Manifold
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem contMDiffOn_derivWithin_fst {f : ℝ × M → ℝ} {T : Set ℝ} {U : Set M}
    (hT : UniqueDiffOn ℝ T)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ f (T ×ˢ U)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => derivWithin (fun r => f (r, p.2)) T p.1) (T ×ˢ U) := by
  intro q hq
  have hcomp : ContMDiffWithinAt ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : (ℝ × M) × ℝ => f (p.2, p.1.2)) ((T ×ˢ U) ×ˢ T) (q, q.1) :=
    (hf q hq).comp (f := fun p : (ℝ × M) × ℝ => (p.2, p.1.2)) (q, q.1)
      (contMDiffWithinAt_snd.prodMk contMDiffWithinAt_fst.snd)
      (fun p hp => ⟨hp.2, hp.1.2⟩)
  have h := ContMDiffWithinAt.mfderivWithin_apply (m := ∞)
    (f := fun p : ℝ × M => fun r : ℝ => f (r, p.2))
    (g := Prod.fst) (g₁ := id) (g₂ := fun _ : ℝ × M => (1 : ℝ))
    hcomp contMDiffWithinAt_fst contMDiffWithinAt_id contMDiffWithinAt_const (by simp)
    (mapsTo_id _) hq (fun _ hp => hp.1) hT.uniqueMDiffOn
  convert h using 1
  funext p
  simp only [inTangentCoordinates, mfderivWithin_eq_fderivWithin]
  dsimp only [ContinuousLinearMap.inCoordinates]
  simp only [TangentBundle.continuousLinearMapAt_model_space,
    TangentBundle.symmL_model_space]
  change derivWithin (fun r => f (r, p.2)) T p.1 =
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f (p.1, p.2)))
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (f (p.1, p.2))).symm
        (fderivWithin ℝ (fun r => f (r, p.2)) T p.1
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) p.1)
            ((NormedSpace.fromTangentSpace (𝕜 := ℝ) p.1).symm 1))))
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  rfl

end DifferentialGeometry.Geometry

end

end
