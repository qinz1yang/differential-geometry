import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations


noncomputable section

namespace DifferentialGeometry.Analysis

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem deriv_deriv_comp_affine_line
    {f : E → F} {y v : E} {t : 𝕜}
    (hf : ContDiffAt 𝕜 2 f (y + t • v)) :
    deriv (deriv (fun r : 𝕜 => f (y + r • v))) t =
      iteratedFDeriv 𝕜 2 f (y + t • v) ![v, v] := by
  have hline (r : 𝕜) : HasDerivAt (fun s : 𝕜 => y + s • v) v r := by
    have h :=
      HasDerivAt.add (hasDerivAt_const r y) ((hasDerivAt_id r).smul_const v)
    simp only [id_eq, one_smul, zero_add] at h
    have heq : ((fun _ : 𝕜 => y) + fun s : 𝕜 => s • v) =
        (fun s : 𝕜 => y + s • v) := by
      funext s
      rfl
    rw [heq] at h
    exact h
  have hlineDeriv : deriv (fun s : 𝕜 => y + s • v) = fun _ => v :=
    funext fun r => (hline r).deriv
  have hlineSecond : iteratedDeriv 2 (fun s : 𝕜 => y + s • v) t = 0 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hlineDeriv]
    exact deriv_const t v
  have hlineSmooth : ContDiffAt 𝕜 2 (fun r : 𝕜 => y + r • v) t := by
    simpa only [id_eq] using contDiffAt_const.add (contDiffAt_id.smul_const v)
  have htuple : (fun _ : Fin 2 => v) = ![v, v] :=
    funext <| Fin.forall_fin_two.mpr ⟨rfl, rfl⟩
  have hcomp := iteratedDeriv_vcomp_two hf hlineSmooth
  calc
    deriv (deriv (fun r : 𝕜 => f (y + r • v))) t =
        iteratedDeriv 2 (f ∘ fun r : 𝕜 => y + r • v) t := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
      rfl
    _ = iteratedFDeriv 𝕜 2 f (y + t • v) (fun _ => deriv
          (fun r : 𝕜 => y + r • v) t) +
        fderiv 𝕜 f (y + t • v) (iteratedDeriv 2 (fun r : 𝕜 => y + r • v) t) := hcomp
    _ = iteratedFDeriv 𝕜 2 f (y + t • v) ![v, v] := by
      rw [hlineDeriv, hlineSecond]
      simp only [map_zero, add_zero, htuple]

end DifferentialGeometry.Analysis
