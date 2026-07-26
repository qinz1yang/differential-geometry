import DifferentialGeometry.Analysis.Calculus.SmoothExtension.ChartRicciJet

/-!
# Bridge: jet slots of a matrix-valued field ↔ entrywise Fréchet/partial derivatives

For the `chartRicci = Φ(jet2 chartGram)` identity (`hglue` corollary (a)), the abstract jet operator
`jetRicci`/`Φ` reads the chart-Gram's spatial partials off the `jet2` slots, while the geometric
`chartChristoffel`/`chartRiemann`/`chartRicci` use `partialDeriv` of the scalar entry fields. These
agree because the matrix-entry projection `M ↦ M l m` is a continuous linear map, so it commutes with
`fderiv`: the `(l,m)` entry of `D G` is `D (G·_{lm})`. Here `partialDeriv i u y = D u y (basis i)`,
so the basis-evaluated jet slots are exactly the chart partials.
-/

noncomputable section

open scoped ContDiff

namespace DifferentialGeometry
namespace Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

/-- The matrix-entry projection `M ↦ M l m` on `Fin n → Fin n → ℝ`, as a continuous linear map. -/
def matEntryCLM (l m : Fin n) : (Fin n → Fin n → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) m).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin n → ℝ) l)

@[simp] theorem matEntryCLM_apply (l m : Fin n) (M : Fin n → Fin n → ℝ) :
    matEntryCLM l m M = M l m := rfl

/-- **First-order jet ↔ entry bridge.** The `(l,m)` entry of the Fréchet derivative of a
matrix(`Pi`)-valued map equals the Fréchet derivative of its `(l,m)` entry field (the entry
projection is continuous-linear, so it commutes with `fderiv`). -/
theorem fderiv_matEntry {G : E → (Fin n → Fin n → ℝ)} {y : E} (hG : DifferentiableAt ℝ G y)
    (v : E) (l m : Fin n) :
    (fderiv ℝ G y) v l m = fderiv ℝ (fun w => G w l m) y v := by
  have hL : fderiv ℝ (fun w => G w l m) y = (matEntryCLM l m).comp (fderiv ℝ G y) :=
    ((matEntryCLM l m).hasFDerivAt.comp y hG.hasFDerivAt).fderiv
  rw [hL]
  rfl

/-- **Second-order jet ↔ entry bridge.** The `(v, l, m)` slot of the second Fréchet derivative
(`jet2`'s `.2.2`) equals the Fréchet derivative of the first-order `(v,l,m)` slot field (the
"evaluate at `v` then entry `(l,m)`" map is continuous-linear, so it commutes with the outer
`fderiv`). Requires `w ↦ D G w` differentiable at `y` (i.e. `G` is `C²` near `y`). -/
theorem fderiv2_matEntry {G : E → (Fin n → Fin n → ℝ)} {y : E}
    (hG : DifferentiableAt ℝ (fun w => fderiv ℝ G w) y) (u v : E) (l m : Fin n) :
    ((fderiv ℝ (fun w => fderiv ℝ G w) y) u) v l m
      = fderiv ℝ (fun w => (fderiv ℝ G w) v l m) y u := by
  have hL : fderiv ℝ (fun w => (fderiv ℝ G w) v l m) y
      = ((matEntryCLM l m).comp (ContinuousLinearMap.apply ℝ (Fin n → Fin n → ℝ) v)).comp
          (fderiv ℝ (fun w => fderiv ℝ G w) y) :=
    (((matEntryCLM l m).comp (ContinuousLinearMap.apply ℝ (Fin n → Fin n → ℝ) v)).hasFDerivAt.comp
      y hG.hasFDerivAt).fderiv
  rw [hL]
  rfl

end Analysis
end DifferentialGeometry

end
