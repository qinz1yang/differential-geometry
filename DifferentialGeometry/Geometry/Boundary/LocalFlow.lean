import DifferentialGeometry.Geometry.Boundary.ModelFlow
import DifferentialGeometry.Geometry.Boundary.ChartTangent
import DifferentialGeometry.Geometry.Boundary.Normal.Outward
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique

noncomputable section
open Set Filter Function Topology Manifold
open scoped ContDiff

namespace Poincare.Geometry.Boundary

open DifferentialGeometry
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]

set_option backward.isDefEq.respectTransparency false in
private theorem contDiffOn_chartVectorField {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) (x : M) :
    ContDiffOn ℝ ∞ (fun y ↦ tangentCoordChange I ((extChartAt I x).symm y) x
      ((extChartAt I x).symm y) (v ((extChartAt I x).symm y))) (extChartAt I x).target := by
  have hh := (contMDiff_iff.mp hv).2 x (⟨x, v x⟩ : TangentBundle I M)
  apply hh.snd.mono
  intro z hz
  refine ⟨hz, ?_⟩
  simpa only [mfld_simps] using (extChartAt I x).map_target hz

set_option backward.isDefEq.respectTransparency false in
private theorem isMIntegralCurveOn_chartInverse (x : M) {v : (x : M) → TangentSpace I x} {γ : ℝ → E} {S : Set ℝ}
    (hγ : ∀ t ∈ S, HasDerivWithinAt γ
      (mfderiv I 𝓘(ℝ, E) (extChartAt I x) ((extChartAt I x).symm (γ t))
        (v ((extChartAt I x).symm (γ t)))) S t)
    (hmem : MapsTo γ S (extChartAt I x).target) :
    IsMIntegralCurveOn ((extChartAt I x).symm ∘ γ) v S := by
  intro t ht
  have hd := (hγ t ht).hasFDerivWithinAt.hasMFDerivWithinAt
  have hs := (mdifferentiableWithinAt_extChartAt_symm (hmem ht)).hasMFDerivWithinAt
  apply (hs.comp t hd (fun s hs ↦ extChartAt_target_subset_range x (hmem hs))).congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  have h := congrArg
    (fun L : TangentSpace I ((extChartAt I x).symm (γ t)) →L[ℝ]
      TangentSpace I ((extChartAt I x).symm (γ t)) ↦ L (v ((extChartAt I x).symm (γ t))))
    (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (hmem ht))
  change (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) (γ t))
    (a • mfderiv I 𝓘(ℝ, E) (extChartAt I x) ((extChartAt I x).symm (γ t))
      (v ((extChartAt I x).symm (γ t)))) = a • v ((extChartAt I x).symm (γ t))
  rw [map_smul]
  exact congrArg (a • ·) h

variable [FiniteDimensional ℝ E] [hI : HasSmoothBoundary E H I]

set_option backward.isDefEq.respectTransparency false in
theorem exists_inward_localFlow
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (x : BoundaryManifold I M)
    (hinward : ∃ (w : TangentSpace hI.boundaryI x) (c : ℝ), 0 < c ∧
      v x.1 = boundaryInclusionMfderiv x w + c • inwardCoord x) :
    ∃ ε > 0, ∃ V : Set M, IsOpen V ∧ x.1 ∈ V ∧
      ∃ Φ : M × ℝ → M,
        (∀ y ∈ V, Φ (y, 0) = y) ∧
        ContMDiffOn (I.prod 𝓘(ℝ)) I ∞ Φ (V ×ˢ Ico 0 ε) ∧
        (∀ y ∈ V, IsMIntegralCurveOn (fun t ↦ Φ (y, t)) v (Ico 0 ε)) ∧
        ∀ y ∈ V, ∀ t ∈ Ioo 0 ε, I.IsInteriorPoint (Φ (y, t)) := by
  let c := extChartAt I x.1
  let p := extChartAt hI.boundaryI x x
  have hp : modelBoundaryParam I p = c x.1 :=
    modelBoundaryParam_extChartAt_boundary x x (mem_chart_source H x.1)
  let w : E → E := fun z ↦ tangentCoordChange I (c.symm z) x.1 (c.symm z) (v (c.symm z))
  have hw : ContDiffOn ℝ ∞ w c.target := contDiffOn_chartVectorField hv x.1
  obtain ⟨U₀, hU₀, hU₀c⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp
    (extChartAt_target_mem_nhdsWithin (I := I) x.1)
  obtain ⟨U, hUU₀, hU, hxU⟩ := mem_nhds_iff.mp hU₀
  have hUc : U ∩ range I ⊆ c.target := fun z hz ↦ hU₀c ⟨hUU₀ hz.1, hz.2⟩
  have hwIn : ∃ (a : hI.boundaryE) (r : ℝ), 0 < r ∧
      w (modelBoundaryParam I p) = fderiv ℝ (modelBoundaryParam I) p a + r • hI.inwardCoordE := by
    obtain ⟨a, r, hr, hva⟩ := hinward
    refine ⟨tangentSpaceModelContinuousLinearEquiv (I := hI.boundaryI) x a, r, hr, ?_⟩
    change tangentCoordChange I (c.symm (modelBoundaryParam I p)) x.1
      (c.symm (modelBoundaryParam I p)) (v (c.symm (modelBoundaryParam I p))) = _
    rw [hp, c.left_inv (mem_extChartAt_source x.1), tangentCoordChange_self (mem_extChartAt_source x.1), hva]
    have ha := boundaryInclusionMfderiv_model x a
    have hi := inwardCoord_eq x
    change boundaryInclusionMfderiv x a + r • inwardCoord x = _
    change boundaryInclusionMfderiv x a = fderiv ℝ (modelBoundaryParam I) p
      (tangentSpaceModelContinuousLinearEquiv (I := hI.boundaryI) x a) at ha
    change inwardCoord x = hI.inwardCoordE at hi
    rw [ha, hi]
  obtain ⟨ε, hε, W, hW, hpW, hWU, Ψ, hzero, hΨ, hflow, hinside⟩ :=
    exists_inward_localFlow_of_model I hU (hp.symm ▸ hxU) (hw.mono hUc) hwIn
  let V := c.source ∩ c ⁻¹' W
  have hV : IsOpen V := (continuousOn_extChartAt x.1).isOpen_inter_preimage
    (isOpen_extChartAt_source x.1) hW
  have hxV : x.1 ∈ V := ⟨mem_extChartAt_source x.1, by
    simpa only [mem_preimage, hp] using hpW⟩
  have hstart : ∀ y ∈ V, c y ∈ W ∩ range I :=
    fun y hy ↦ ⟨hy.2, extChartAt_target_subset_range x.1 (c.map_source hy.1)⟩
  have htarget : ∀ y ∈ V, ∀ t ∈ Ico 0 ε, Ψ (c y, t) ∈ c.target :=
    fun y hy t ht ↦ hUc (hflow _ (hstart y hy) t ht).1
  let Φ : M × ℝ → M := fun z ↦ c.symm (Ψ (c z.1, z.2))
  have hΦ : ContMDiffOn (I.prod 𝓘(ℝ)) I ∞ Φ (V ×ˢ Ico 0 ε) := by
    have hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c V :=
      (contMDiffOn_extChartAt (I := I) (x := x.1)).mono (fun y hy ↦ by
        simpa only [c, extChartAt_source] using hy.1)
    have hmap : ContMDiffOn (I.prod 𝓘(ℝ)) 𝓘(ℝ, E × ℝ) ∞
        (fun z : M × ℝ ↦ (c z.1, z.2)) (V ×ˢ Ico 0 ε) :=
      (hc.comp contMDiffOn_fst (fun z hz ↦ hz.1)).prodMk_space contMDiffOn_snd
    exact (contMDiffOn_extChartAt_symm x.1).comp
      (hΨ.contMDiffOn.comp hmap (fun z hz ↦ ⟨hz.1.2, by
        exact ⟨by linarith [hz.2.1], hz.2.2⟩⟩))
      (fun z hz ↦ htarget z.1 hz.1 z.2 hz.2)
  refine ⟨ε, hε, V, hV, hxV, Φ, ?_, hΦ, ?_, ?_⟩
  · intro y hy
    change c.symm (Ψ (c y, 0)) = y
    rw [hzero _ hy.2, c.left_inv hy.1]
  · intro y hy
    apply isMIntegralCurveOn_chartInverse x.1 (hmem := fun t ht ↦ htarget y hy t ht)
    intro t ht
    have hd := (hflow _ (hstart y hy) t ht).2.hasDerivWithinAt (s := Ico 0 ε)
    have hsrc : c.symm (Ψ (c y, t)) ∈ (chartAt H x.1).source := by
      simpa only [c, extChartAt_source] using c.map_target (htarget y hy t ht)
    rw [(hasMFDerivAt_extChartAt hsrc).mfderiv, mfderiv_chartAt_eq_tangentCoordChange hsrc]
    exact hd
  · intro y hy t ht
    have hqt := htarget y hy t ⟨ht.1.le, ht.2⟩
    have hqi := hinside _ (hstart y hy) t ht
    have hsrc : c.symm (Ψ (c y, t)) ∈ (chartAt H x.1).source := by
      simpa only [c, extChartAt_source] using c.map_target hqt
    apply (I.isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp) (chart_mem_atlas H x.1) hsrc).2
    change c (c.symm (Ψ (c y, t))) ∈ interior c.target
    rw [c.right_inv hqt, mem_interior_iff_mem_nhds]
    have hn := extChartAt_target_mem_nhdsWithin_of_mem hqt
    rwa [nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp hqi)] at hn

end Poincare.Geometry.Boundary
