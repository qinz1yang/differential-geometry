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
  simpa only [inTangentCoordinates_model_space, id_eq, mfderiv_eq_fderiv,
    fderiv_apply_one_eq_deriv] using h



theorem contDiffAt_deriv_fst {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : ℝ × V → ℝ} {q : ℝ × V} (hf : ContDiffAt ℝ ∞ f q) :
    ContDiffAt ℝ ∞ (fun p : ℝ × V => deriv (fun r => f (r, p.2)) p.1) q := by
  have h := hf.contMDiffAt
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h
  have hd := contMDiffAt_deriv_fst h
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hd
  exact hd.contDiffAt

end DifferentialGeometry.Geometry
