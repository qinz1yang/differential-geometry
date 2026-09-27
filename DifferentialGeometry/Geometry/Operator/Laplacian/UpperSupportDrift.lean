import DifferentialGeometry.Geometry.Operator.Laplacian.ChartPrincipalPart
import DifferentialGeometry.Geometry.Operator.Laplacian.LocalVossWeyl
import Mathlib.Analysis.Calculus.LocalExtr.Basic


noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open Set Filter
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem sum_chartDensity_invGram_mul_iteratedFDeriv_two_upper_support
    (g : SmoothRiemannianMetric I M) (a : M) {y : E}
    (hy : y ∈ (extChartAt I a).target) {f phi : M → ℝ} {U : Set M}
    (hU : IsOpen U) (hyU : (extChartAt I a).symm y ∈ U)
    (hphi : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ phi U)
    (hf : DifferentiableAt ℝ (scalarOnE (I := I) a f) y)
    (hcontact : phi ((extChartAt I a).symm y) = f ((extChartAt I a).symm y))
    (hupper : ∀ z ∈ U, f z ≤ phi z) :
    (∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      (chartDensityOnE g a y * chartInvGramOnE g a ij.1 ij.2 y) *
        iteratedFDeriv ℝ 2 (scalarOnE (I := I) a phi) y
          ![chartModelBasis E ij.1, chartModelBasis E ij.2]) =
      chartDensityOnE g a y *
        laplacian (Connection.LeviCivita g) g phi ((extChartAt I a).symm y) -
        ∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          iteratedFDeriv ℝ 1
            (fun z => chartDensityOnE g a z * chartInvGramOnE g a ij.1 ij.2 z) y
            (fun _ => chartModelBasis E ij.1) *
              iteratedFDeriv ℝ 1 (scalarOnE (I := I) a f) y
                (fun _ => chartModelBasis E ij.2) := by
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I a).symm y :=
    (contMDiffOn_extChartAt_symm a).contMDiffAt
      ((isOpen_extChartAt_target a).mem_nhds hy)
  have hphic : ContDiffAt ℝ ∞ (scalarOnE (I := I) a phi) y :=
    ((hphi.contMDiffAt (hU.mem_nhds hyU)).comp y hsymm).contDiffAt
  have hphid := hphic.differentiableAt (by simp)
  have hup : ∀ᶠ z in 𝓝 y, scalarOnE (I := I) a f z ≤ scalarOnE (I := I) a phi z := by
    filter_upwards [hsymm.continuousAt.preimage_mem_nhds (hU.mem_nhds hyU)] with z hz
    exact hupper _ hz
  have hmin : IsLocalMin
      (fun z => scalarOnE (I := I) a phi z - scalarOnE (I := I) a f z) y := by
    change ∀ᶠ z in 𝓝 y, _ ≤ _
    filter_upwards [hup] with z hz
    change phi ((extChartAt I a).symm y) - f ((extChartAt I a).symm y) ≤ _
    rw [hcontact, sub_self]
    exact sub_nonneg.mpr hz
  have hz := hmin.fderiv_eq_zero
  rw [fderiv_fun_sub hphid hf] at hz
  have hd : fderiv ℝ (scalarOnE (I := I) a phi) y =
      fderiv ℝ (scalarOnE (I := I) a f) y := sub_eq_zero.mp hz
  have hsum := sum_chartDensity_invGram_mul_iteratedFDeriv_two (f := phi) g a hy
    (hphic.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
  rw [laplacian_eq_chartVossWeyl_of_contMDiffOn g a hU hyU hphi
    (by
      have hm := (extChartAt I a).map_target hy
      rwa [extChartAt_source (I := I) a] at hm)]
  simpa only [iteratedFDeriv_one_apply, hd] using hsum

end DifferentialGeometry.Geometry.Operator
