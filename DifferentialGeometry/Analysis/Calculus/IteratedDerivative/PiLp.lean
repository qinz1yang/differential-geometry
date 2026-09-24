import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Normed.Lp.PiLp

open scoped ENNReal

namespace PiLp

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {ι : Type*} [Fintype ι]
variable {β : ι → Type*} [∀ i, NormedAddCommGroup (β i)] [∀ i, NormedSpace 𝕜 (β i)]
variable {f g : 𝕜 → PiLp p β} {m : ℕ} {x : 𝕜}

theorem iteratedDeriv_apply (hf : ContDiffAt 𝕜 m f x) (i : ι) :
    iteratedDeriv m (fun y => f y i) x = (iteratedDeriv m f x) i := by
  let L : PiLp p β →L[𝕜] β i := PiLp.proj p β i
  change iteratedDeriv m (L ∘ f) x = L (iteratedDeriv m f x)
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv,
    L.iteratedFDeriv_comp_left hf le_rfl]
  rfl

theorem norm_iteratedDeriv_apply_sub_le
    (hf : ContDiffAt 𝕜 m f x) (hg : ContDiffAt 𝕜 m g x) (i : ι) :
    ‖iteratedDeriv m (fun y => f y i) x - iteratedDeriv m (fun y => g y i) x‖ ≤
      ‖iteratedDeriv m f x - iteratedDeriv m g x‖ := by
  rw [iteratedDeriv_apply hf, iteratedDeriv_apply hg]
  exact PiLp.norm_apply_le (iteratedDeriv m f x - iteratedDeriv m g x) i

end PiLp
