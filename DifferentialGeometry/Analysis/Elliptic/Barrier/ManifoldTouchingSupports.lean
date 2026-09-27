import DifferentialGeometry.Analysis.Elliptic.Barrier.TouchingSupportsDifferentiability
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

set_option autoImplicit false
noncomputable section

open Set Filter Function Manifold
open scoped Topology Manifold

namespace DifferentialGeometry.Analysis

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

theorem mdifferentiableAt_of_opposite_upper_supports
    {f phi psi : M → ℝ} {x : M}
    (hphi : MDifferentiableAt I 𝓘(ℝ, ℝ) phi x)
    (hpsi : MDifferentiableAt I 𝓘(ℝ, ℝ) psi x)
    (hphi_eq : phi x = f x) (hpsi_eq : psi x = -f x)
    (hphi_le : ∀ᶠ y in 𝓝 x, f y ≤ phi y)
    (hpsi_le : ∀ᶠ y in 𝓝 x, -f y ≤ psi y) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) f x := by
  let e := extChartAt I x
  let z : E := e x
  have hleft : e.symm z = x := (extChartAt I x).left_inv (mem_extChartAt_source x)
  have htarget : z ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source (mem_extChartAt_source x)
  have hinv : MDifferentiableAt 𝓘(ℝ, E) I e.symm z := by
    simpa only [I.range_eq_univ, mdifferentiableWithinAt_univ] using
      (mdifferentiableWithinAt_extChartAt_symm (I := I) htarget)
  have htend : Tendsto e.symm (𝓝 z) (𝓝 x) := by
    simpa only [hleft] using hinv.continuousAt.tendsto
  have hphi_chart : DifferentiableAt ℝ (phi ∘ e.symm) z :=
    (hphi.comp_of_eq z hinv hleft).differentiableAt
  have hpsi_chart : DifferentiableAt ℝ (psi ∘ e.symm) z :=
    (hpsi.comp_of_eq z hinv hleft).differentiableAt
  have hphi_contact : (phi ∘ e.symm) z = (f ∘ e.symm) z := by
    simpa only [comp_apply, hleft] using hphi_eq
  have hpsi_contact : (psi ∘ e.symm) z = -(f ∘ e.symm) z := by
    simpa only [comp_apply, hleft] using hpsi_eq
  have hf_chart : DifferentiableAt ℝ (f ∘ e.symm) z :=
    differentiableAt_of_opposite_upper_supports hphi_chart hpsi_chart
      hphi_contact hpsi_contact (htend.eventually hphi_le) (htend.eventually hpsi_le)
  apply (mdifferentiableAt_iff_source_of_mem_source (I := I) (I' := 𝓘(ℝ, ℝ))
    (x := x) (f := f) (ChartedSpace.mem_chart_source x)).mpr
  exact hf_chart.mdifferentiableAt.mdifferentiableWithinAt

end DifferentialGeometry.Analysis

end
