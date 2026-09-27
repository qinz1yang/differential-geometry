import DifferentialGeometry.Analysis.Integration.RadialIntegralSmoothness
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Integral

theorem contMDiffOn_radialIntegral_joint
    {EP E F : Type*}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
    [IP.Boundaryless] {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
    (n : ℕ∞) [IsManifold IP n P]
    (k : ℕ) {S : Set P} {U : Set E} (hS : IsOpen S) (hU : IsOpen U)
    (hstar : StarConvex ℝ 0 U) {f : P → E → F}
    (hf : ContMDiffOn (IP.prod 𝓘(ℝ, E)) 𝓘(ℝ, F) n
      (Function.uncurry f) (S ×ˢ U)) :
    ContMDiffOn (IP.prod 𝓘(ℝ, E)) 𝓘(ℝ, F) n
      (fun p : P × E => radialIntegral k (f p.1) p.2) (S ×ˢ U) := by
  intro z hz
  let V : Set EP := (extChartAt IP z.1).target ∩ (extChartAt IP z.1).symm ⁻¹' S
  have hV : IsOpen V := (continuousOn_extChartAt_symm z.1).isOpen_inter_preimage
    (isOpen_extChartAt_target z.1) hS
  have hcoord : ContMDiffOn (𝓘(ℝ, EP).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) n
      (fun w : EP × E => f ((extChartAt IP z.1).symm w.1) w.2) (V ×ˢ U) := by
    change ContMDiffOn _ _ n (Function.uncurry f ∘
      fun w : EP × E => ((extChartAt IP z.1).symm w.1, w.2)) _
    apply hf.comp
    · exact ((contMDiffOn_extChartAt_symm (I := IP) z.1).comp contMDiffOn_fst
        (fun w hw => hw.1.1)).prodMk contMDiffOn_snd
    · intro w hw
      exact ⟨hw.1.2, hw.2⟩
  have hcoord' : ContMDiffOn (𝓘(ℝ, EP × E)) 𝓘(ℝ, F) n
      (Function.uncurry (fun p x => f ((extChartAt IP z.1).symm p) x)) (V ×ˢ U) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hcoord
  have hint := DifferentialGeometry.Integral.contDiffOn_radialIntegral_joint n k hV hU hstar
    (f := fun p x => f ((extChartAt IP z.1).symm p) x) hcoord'.contDiffOn
  let W := (S ∩ (extChartAt IP z.1).source) ×ˢ U
  have hW : IsOpen W := (hS.inter (isOpen_extChartAt_source z.1)).prod hU
  have hzW : z ∈ W := ⟨⟨hz.1, mem_extChartAt_source z.1⟩, hz.2⟩
  have harg : ContMDiffOn (IP.prod 𝓘(ℝ, E)) 𝓘(ℝ, EP × E) n
      (fun w : P × E => (extChartAt IP z.1 w.1, w.2)) W := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact ((contMDiffOn_extChartAt (I := IP) (x := z.1)).comp contMDiffOn_fst
      (fun w hw => by simpa only [mem_preimage, extChartAt_source] using hw.1.2)).prodMk contMDiffOn_snd
  have hmaps : MapsTo (fun w : P × E => (extChartAt IP z.1 w.1, w.2)) W (V ×ˢ U) := by
    intro w hw
    refine ⟨⟨(extChartAt IP z.1).map_source hw.1.2, ?_⟩, hw.2⟩
    change (extChartAt IP z.1).symm (extChartAt IP z.1 w.1) ∈ S
    rw [(extChartAt IP z.1).left_inv hw.1.2]
    exact hw.1.1
  have hresult := hint.contMDiffOn.comp harg hmaps
  have hfinal : ContMDiffOn (IP.prod 𝓘(ℝ, E)) 𝓘(ℝ, F) n
      (fun w : P × E => radialIntegral k (f w.1) w.2) W := by
    apply hresult.congr
    intro w hw
    simp only [Function.comp_apply, (extChartAt IP z.1).left_inv hw.1.2]
  exact (hfinal.contMDiffAt (hW.mem_nhds hzW)).contMDiffWithinAt

end DifferentialGeometry.Integral
