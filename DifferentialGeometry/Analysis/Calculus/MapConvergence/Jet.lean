import DifferentialGeometry.Analysis.Calculus.MapConvergence.Composition
import DifferentialGeometry.Analysis.Calculus.TimeJet.Evolution

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem mapCInfConvergence_jet2 {U : Set E} (hU : IsOpen U)
    {G : ℕ → E → F} {Ginf : E → F}
    (h : MapCInfConvergenceOnCompacts U G Ginf)
    (hG : ∀ k, ContDiffOn ℝ ∞ (G k) U) (hGinf : ContDiffOn ℝ ∞ Ginf U) :
    MapCInfConvergenceOnCompacts U (fun k => jet2 (G k)) (jet2 Ginf) := by
  have hd (k : ℕ) := (hG k).fderiv_of_isOpen hU (m := ∞) (by simp)
  have hdi := hGinf.fderiv_of_isOpen hU (m := ∞) (by simp)
  have hdd (k : ℕ) := (hd k).fderiv_of_isOpen hU (m := ∞) (by simp)
  have hddi := hdi.fderiv_of_isOpen hU (m := ∞) (by simp)
  have h1 := h.fderivOn hU hG hGinf
  have h2 := h1.fderivOn hU hd hdi
  exact mapCInfConvergence_prodMk hU h (mapCInfConvergence_prodMk hU h1 h2 hd hdi hdd hddi)
    hG hGinf (fun k => (hd k).prodMk (hdd k)) (hdi.prodMk hddi)


end DifferentialGeometry.CheegerGromovCompactness
