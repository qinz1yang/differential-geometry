import DifferentialGeometry.Geometry.Operator.Laplacian.UpperSupportDrift
import DifferentialGeometry.Analysis.Calculus.Derivative.RankOneContraction
import DifferentialGeometry.Analysis.Calculus.Derivative.AffineLineSecond
import DifferentialGeometry.Geometry.Coordinates.Fields.LocalScalarRegularity


noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open Set Filter
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Analysis.Calculus
  (sum_mul_iteratedFDeriv_two_diagonal_eq_sum_coordinates)
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_affine_line_upper_supports_of_contMDiffOn
    (g : SmoothRiemannianMetric I M) (a : M) {y : E}
    (hy : y ∈ (extChartAt I a).target) {f phi : M → ℝ} {U : Set M}
    (hU : IsOpen U) (hyU : (extChartAt I a).symm y ∈ U)
    (hphi : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ phi U)
    (hf : DifferentiableAt ℝ (scalarOnE (I := I) a f) y)
    (hcontact : phi ((extChartAt I a).symm y) = f ((extChartAt I a).symm y))
    (hupper : ∀ z ∈ U, f z ≤ phi z)
    {κ : Type*} [Fintype κ] (v : κ → E) (w : κ → ℝ)
    (hC : ∀ i j : Fin (Module.finrank ℝ E),
      chartDensityOnE g a y * chartInvGramOnE g a i j y =
        ∑ k, w k * (chartModelBasis E).repr (v k) i * (chartModelBasis E).repr (v k) j) :
    ∃ ψ : κ → ℝ → ℝ,
      (∀ k, ContDiffAt ℝ 2 (ψ k) 0) ∧
      (∀ k, ∀ᶠ t in 𝓝 0, scalarOnE (I := I) a f (y + t • v k) ≤ ψ k t) ∧
      (∀ k, scalarOnE (I := I) a f y = ψ k 0) ∧
      (∑ k, w k * deriv (deriv (ψ k)) 0) =
        chartDensityOnE g a y *
          laplacian (Connection.LeviCivita g) g phi ((extChartAt I a).symm y) -
          ∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            iteratedFDeriv ℝ 1
              (fun z => chartDensityOnE g a z * chartInvGramOnE g a ij.1 ij.2 z) y
              (fun _ => chartModelBasis E ij.1) *
                iteratedFDeriv ℝ 1 (scalarOnE (I := I) a f) y
                  (fun _ => chartModelBasis E ij.2) := by
  let ψ : κ → ℝ → ℝ := fun k t => scalarOnE (I := I) a phi (y + t • v k)
  have hp : ContDiffAt ℝ 2 (scalarOnE (I := I) a phi) y :=
    (scalarOnE_contDiffAt_of_contMDiffOn a hphi hU hy hyU).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hline (k : κ) : ContDiffAt ℝ 2 (fun t : ℝ => y + t • v k) 0 :=
    contDiffAt_const.add (contDiffAt_id.smul_const (v k))
  have hsymm : ContinuousAt (extChartAt I a).symm y :=
    (continuousOn_extChartAt_symm a y hy).continuousAt
      ((isOpen_extChartAt_target a).mem_nhds hy)
  refine ⟨ψ, ?_, ?_, ?_, ?_⟩
  · intro k
    have hpc : ContDiffAt ℝ 2 (scalarOnE (I := I) a phi) (y + (0 : ℝ) • v k) := by
      simpa only [zero_smul, add_zero] using hp
    exact ContDiffAt.comp (g := scalarOnE (I := I) a phi)
      (f := fun t : ℝ => y + t • v k) 0 hpc (hline k)
  · intro k
    have ht : Tendsto (fun t : ℝ => (extChartAt I a).symm (y + t • v k))
        (𝓝 0) (𝓝 ((extChartAt I a).symm y)) := by
      apply hsymm.tendsto.comp
      simpa only [zero_smul, add_zero] using (hline k).continuousAt.tendsto
    filter_upwards [ht.eventually (hU.mem_nhds hyU)] with t ht
    exact hupper _ ht
  · intro k
    simpa only [ψ, zero_smul, add_zero, scalarOnE] using hcontact.symm
  · have hsecond (k : κ) : deriv (deriv (ψ k)) 0 =
        iteratedFDeriv ℝ 2 (scalarOnE (I := I) a phi) y ![v k, v k] := by
      simpa only [ψ, zero_smul, add_zero] using
        DifferentialGeometry.Analysis.deriv_deriv_comp_affine_line
          (y := y) (v := v k) (t := (0 : ℝ))
          (by simpa only [zero_smul, add_zero] using hp)
    simp_rw [hsecond]
    rw [sum_mul_iteratedFDeriv_two_diagonal_eq_sum_coordinates
      _ y (chartModelBasis E) Finset.univ w v
      (fun i j => chartDensityOnE g a y * chartInvGramOnE g a i j y) hC]
    simpa only [Fintype.sum_prod_type] using
      sum_chartDensity_invGram_mul_iteratedFDeriv_two_upper_support
        g a hy hU hyU hphi hf hcontact hupper

end DifferentialGeometry.Geometry.Operator
