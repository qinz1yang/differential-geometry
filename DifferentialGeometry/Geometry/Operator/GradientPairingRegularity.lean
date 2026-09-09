import DifferentialGeometry.Geometry.Operator.LaplacianRegularity

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]

theorem contMDiffOn_inner_gradient_prod_of_isOpen
    {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
    {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP ∞ P]
    [IP.Boundaryless] [FiniteDimensional ℝ EP] [T2Space P]
    (g : SmoothRiemannianMetric I M) {f h : P → M → ℝ} {D : Set (P × M)}
    (hD : IsOpen D)
    (hf : ContMDiffOn (IP.prod I) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f) D)
    (hh : ContMDiffOn (IP.prod I) 𝓘(ℝ, ℝ) ∞ (Function.uncurry h) D) :
    ContMDiffOn (IP.prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : P × M => g.inner z.2 (gradientFun g (f z.1) z.2)
        (gradientFun g (h z.1) z.2)) D := by
  have hLfh := contMDiffOn_laplacian_leviCivita_prod_of_isOpen
    (IP := IP) (f := fun p q => f p q * h p q) g hD (hf.mul hh)
  have hLf := contMDiffOn_laplacian_leviCivita_prod_of_isOpen (IP := IP) g hD hf
  have hLh := contMDiffOn_laplacian_leviCivita_prod_of_isOpen (IP := IP) g hD hh
  apply (((hLfh.sub (hf.mul hLh)).sub (hh.mul hLf)).div_const 2).congr
  intro z hz
  let Q : Set M := (fun q => (z.1, q)) ⁻¹' D
  have hQ : IsOpen Q := hD.preimage (continuous_const.prodMk continuous_id)
  have hfs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (f z.1) Q :=
    hf.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn (fun _ hq => hq)
  have hhs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (h z.1) Q :=
    hh.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn (fun _ hq => hq)
  have hfn : ∀ᶠ q in 𝓝 z.2, MDifferentiableAt I 𝓘(ℝ, ℝ) (f z.1) q := by
    filter_upwards [hQ.mem_nhds hz] with q hq
    exact (hfs.contMDiffAt (hQ.mem_nhds hq)).mdifferentiableAt (by simp)
  have hhn : ∀ᶠ q in 𝓝 z.2, MDifferentiableAt I 𝓘(ℝ, ℝ) (h z.1) q := by
    filter_upwards [hQ.mem_nhds hz] with q hq
    exact (hhs.contMDiffAt (hQ.mem_nhds hq)).mdifferentiableAt (by simp)
  have hmul := laplacian_mul_at (Connection.LeviCivita g) g hfn hhn
    ((gradientFun_contMDiffAt g (hfs.contMDiffAt (hQ.mem_nhds hz))).mdifferentiableAt (by simp))
    ((gradientFun_contMDiffAt g (hhs.contMDiffAt (hQ.mem_nhds hz))).mdifferentiableAt (by simp))
  change _ = (laplacian (Connection.LeviCivita g) g (fun q => f z.1 q * h z.1 q) z.2 -
    f z.1 z.2 * laplacian (Connection.LeviCivita g) g (h z.1) z.2 -
    h z.1 z.2 * laplacian (Connection.LeviCivita g) g (f z.1) z.2) / 2
  rw [hmul]
  ring

end DifferentialGeometry.Geometry.Operator
