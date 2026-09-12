import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.AssemblyReduction

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open Bundle Manifold Set Topology

namespace DifferentialGeometry.Topology
namespace ConnectedSumQuotient

variable {M : Type} [TopologicalSpace M] [ChartedSpace csModel M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M]
variable {N : Type} [TopologicalSpace N] [ChartedSpace csModel N]
  [IsManifold (𝓡 3) ∞ N] [T2Space N]
variable (c : BallChart 3 (𝓡 3) M) (d : BallChart 3 (𝓡 3) N)
variable (aD : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere)
variable [ChartedSpace csModel (ConnectedSumQuotient c d aD.toHomeomorph)]
variable [IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c d aD.toHomeomorph)]

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space N]
  [ChartedSpace csModel (ConnectedSumQuotient c d aD.toHomeomorph)]
  [IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c d aD.toHomeomorph)] in
theorem leftChart_symm_comp_interiorLeft_eventuallyEq
    (f : OpenPartialHomeomorph M csModel) (u : c.interior) (hu : (u : M) ∈ f.source) :
    (fun u' : c.interior =>
        (leftChart c d aD.toHomeomorph hn3 f).symm (interiorLeft c d aD u'))
      =ᶠ[𝓝 u] (fun u' : c.interior => f (u' : M)) := by
  refine Filter.eventuallyEq_of_mem
    ((f.open_source.preimage continuous_subtype_val).mem_nhds hu) ?_
  intro u' hu'
  exact leftChart_symm_apply_inl c d aD.toHomeomorph hn3 f ⟨hu', u'.2⟩

omit [IsManifold (𝓡 3) ∞ N] [T2Space N] in
theorem mfderiv_leftChart_symm_comp_interiorLeft
    (hL : ∀ (f : OpenPartialHomeomorph M csModel), f ∈ atlas csModel M →
      (leftChart c d aD.toHomeomorph hn3 f).symm ∈
        atlas csModel (ConnectedSumQuotient c d aD.toHomeomorph))
    (f : OpenPartialHomeomorph M csModel) (hf : f ∈ atlas csModel M)
    (u : c.interior) (hu : (u : M) ∈ f.source) :
    (mfderiv (𝓡 3) 𝓘(ℝ, csModel)
        (leftChart c d aD.toHomeomorph hn3 f).symm (interiorLeft c d aD u)) ∘L
      (mfderiv (𝓡 3) (𝓡 3) (interiorLeft c d aD) u)
    = mfderiv (𝓡 3) 𝓘(ℝ, csModel) (fun u' : c.interior => f (u' : M)) u := by
  have hmd_i : MDifferentiableAt (𝓡 3) (𝓡 3) (interiorLeft c d aD) u :=
    ((interiorLeft_isLocalDiffeomorph c d aD hL) u).mdifferentiableAt (by decide)
  have hmemtgt : interiorLeft c d aD u ∈ (leftChart c d aD.toHomeomorph hn3 f).target :=
    mem_leftChart_target_of_mem_source c d aD.toHomeomorph hn3 f hu
  have hsymmsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (leftChart c d aD.toHomeomorph hn3 f).symm
      (leftChart c d aD.toHomeomorph hn3 f).target :=
    contMDiffOn_leftChart_symm c d aD f (hL f hf)
  have hmd_e : MDifferentiableAt (𝓡 3) 𝓘(ℝ, csModel)
      (leftChart c d aD.toHomeomorph hn3 f).symm (interiorLeft c d aD u) :=
    (hsymmsmooth.contMDiffAt
      ((leftChart c d aD.toHomeomorph hn3 f).open_target.mem_nhds hmemtgt)).mdifferentiableAt
      (by decide)
  have hchain := mfderiv_comp (x := u) hmd_e hmd_i
  have hmain : mfderiv (𝓡 3) 𝓘(ℝ, csModel)
      (fun u' : c.interior =>
        (leftChart c d aD.toHomeomorph hn3 f).symm (interiorLeft c d aD u')) u
      = (mfderiv (𝓡 3) 𝓘(ℝ, csModel)
            (leftChart c d aD.toHomeomorph hn3 f).symm (interiorLeft c d aD u)).comp
          (mfderiv (𝓡 3) (𝓡 3) (interiorLeft c d aD) u) := hchain
  have hEqderiv : mfderiv (𝓡 3) 𝓘(ℝ, csModel)
      (fun u' : c.interior =>
        (leftChart c d aD.toHomeomorph hn3 f).symm (interiorLeft c d aD u')) u
      = mfderiv (𝓡 3) 𝓘(ℝ, csModel) (fun u' : c.interior => f (u' : M)) u :=
    Filter.EventuallyEq.mfderiv_eq
      (leftChart_symm_comp_interiorLeft_eventuallyEq c d aD f u hu)
  rw [hEqderiv] at hmain
  exact hmain.symm

omit [IsManifold (𝓡 3) ∞ M] [T2Space M] [IsManifold (𝓡 3) ∞ N]
  [ChartedSpace csModel (ConnectedSumQuotient c d aD.toHomeomorph)]
  [IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c d aD.toHomeomorph)] in
theorem rightChart_symm_comp_interiorRight_eventuallyEq
    (g : OpenPartialHomeomorph N csModel) (v : d.interior) (hv : (v : N) ∈ g.source) :
    (fun v' : d.interior =>
        (rightChart c d aD.toHomeomorph hn3 g).symm (interiorRight c d aD v'))
      =ᶠ[𝓝 v] (fun v' : d.interior => g (v' : N)) := by
  refine Filter.eventuallyEq_of_mem
    ((g.open_source.preimage continuous_subtype_val).mem_nhds hv) ?_
  intro v' hv'
  exact rightChart_symm_apply_inr c d aD.toHomeomorph hn3 g ⟨hv', v'.2⟩

omit [IsManifold (𝓡 3) ∞ M] [T2Space M] in
theorem mfderiv_rightChart_symm_comp_interiorRight
    (hR : ∀ (g : OpenPartialHomeomorph N csModel), g ∈ atlas csModel N →
      (rightChart c d aD.toHomeomorph hn3 g).symm ∈
        atlas csModel (ConnectedSumQuotient c d aD.toHomeomorph))
    (g : OpenPartialHomeomorph N csModel) (hg : g ∈ atlas csModel N)
    (v : d.interior) (hv : (v : N) ∈ g.source) :
    (mfderiv (𝓡 3) 𝓘(ℝ, csModel)
        (rightChart c d aD.toHomeomorph hn3 g).symm (interiorRight c d aD v)) ∘L
      (mfderiv (𝓡 3) (𝓡 3) (interiorRight c d aD) v)
    = mfderiv (𝓡 3) 𝓘(ℝ, csModel) (fun v' : d.interior => g (v' : N)) v := by
  have hmd_i : MDifferentiableAt (𝓡 3) (𝓡 3) (interiorRight c d aD) v :=
    ((interiorRight_isLocalDiffeomorph c d aD hR) v).mdifferentiableAt (by decide)
  have hmemtgt : interiorRight c d aD v ∈ (rightChart c d aD.toHomeomorph hn3 g).target :=
    mem_rightChart_target_of_mem_source c d aD.toHomeomorph hn3 g hv
  have hsymmsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (rightChart c d aD.toHomeomorph hn3 g).symm
      (rightChart c d aD.toHomeomorph hn3 g).target :=
    contMDiffOn_rightChart_symm c d aD g (hR g hg)
  have hmd_e : MDifferentiableAt (𝓡 3) 𝓘(ℝ, csModel)
      (rightChart c d aD.toHomeomorph hn3 g).symm (interiorRight c d aD v) :=
    (hsymmsmooth.contMDiffAt
      ((rightChart c d aD.toHomeomorph hn3 g).open_target.mem_nhds hmemtgt)).mdifferentiableAt
      (by decide)
  have hchain := mfderiv_comp (x := v) hmd_e hmd_i
  have hmain : mfderiv (𝓡 3) 𝓘(ℝ, csModel)
      (fun v' : d.interior =>
        (rightChart c d aD.toHomeomorph hn3 g).symm (interiorRight c d aD v')) v
      = (mfderiv (𝓡 3) 𝓘(ℝ, csModel)
            (rightChart c d aD.toHomeomorph hn3 g).symm (interiorRight c d aD v)).comp
          (mfderiv (𝓡 3) (𝓡 3) (interiorRight c d aD) v) := hchain
  have hEqderiv : mfderiv (𝓡 3) 𝓘(ℝ, csModel)
      (fun v' : d.interior =>
        (rightChart c d aD.toHomeomorph hn3 g).symm (interiorRight c d aD v')) v
      = mfderiv (𝓡 3) 𝓘(ℝ, csModel) (fun v' : d.interior => g (v' : N)) v :=
    Filter.EventuallyEq.mfderiv_eq
      (rightChart_symm_comp_interiorRight_eventuallyEq c d aD g v hv)
  rw [hEqderiv] at hmain
  exact hmain.symm

open DifferentialGeometry.Topology in
theorem mfderiv_leftChart_symm_comp_interiorLeft'
    (c : BallChart 3 (𝓡 3) M) (d : BallChart 3 (𝓡 3) N)
    (aD : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere)
    (f : OpenPartialHomeomorph M csModel) (hf : f ∈ atlas csModel M)
    (u : c.interior) (hu : (u : M) ∈ f.source) :
    letI := csChartedSpace c d aD.toHomeomorph
    letI := csIsManifold c d aD.toHomeomorph
      (contDiffOn_reflectMap aD) (contDiffOn_reflectMapInv aD)
    (mfderiv (𝓡 3) 𝓘(ℝ, csModel)
        (leftChart c d aD.toHomeomorph hn3 f).symm (interiorLeft c d aD u)) ∘L
      (mfderiv (𝓡 3) (𝓡 3) (interiorLeft c d aD) u)
    = mfderiv (𝓡 3) 𝓘(ℝ, csModel) (fun u' : c.interior => f (u' : M)) u := by
  let _ := csChartedSpace c d aD.toHomeomorph
  let _ := csIsManifold c d aD.toHomeomorph
    (contDiffOn_reflectMap aD) (contDiffOn_reflectMapInv aD)
  exact mfderiv_leftChart_symm_comp_interiorLeft c d aD
    (fun f hf => OrientationAssembly.mem_atlas_leftChart c d aD.toHomeomorph f hf) f hf u hu

open DifferentialGeometry.Topology in
theorem mfderiv_rightChart_symm_comp_interiorRight'
    (c : BallChart 3 (𝓡 3) M) (d : BallChart 3 (𝓡 3) N)
    (aD : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere)
    (g : OpenPartialHomeomorph N csModel) (hg : g ∈ atlas csModel N)
    (v : d.interior) (hv : (v : N) ∈ g.source) :
    letI := csChartedSpace c d aD.toHomeomorph
    letI := csIsManifold c d aD.toHomeomorph
      (contDiffOn_reflectMap aD) (contDiffOn_reflectMapInv aD)
    (mfderiv (𝓡 3) 𝓘(ℝ, csModel)
        (rightChart c d aD.toHomeomorph hn3 g).symm (interiorRight c d aD v)) ∘L
      (mfderiv (𝓡 3) (𝓡 3) (interiorRight c d aD) v)
    = mfderiv (𝓡 3) 𝓘(ℝ, csModel) (fun v' : d.interior => g (v' : N)) v := by
  let _ := csChartedSpace c d aD.toHomeomorph
  let _ := csIsManifold c d aD.toHomeomorph
    (contDiffOn_reflectMap aD) (contDiffOn_reflectMapInv aD)
  exact mfderiv_rightChart_symm_comp_interiorRight c d aD
    (fun g hg => OrientationAssembly.mem_atlas_rightChart c d aD.toHomeomorph g hg) g hg v hv

end ConnectedSumQuotient
end DifferentialGeometry.Topology
