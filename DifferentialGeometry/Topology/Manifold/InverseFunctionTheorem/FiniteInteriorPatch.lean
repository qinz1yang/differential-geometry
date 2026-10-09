import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.ManifoldDerivative
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import DifferentialGeometry.Topology.Manifold.InteriorChart
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph

/-!
# Finite-order inverse patches at intrinsic interior points

Actual interior charts reduce the derivative criterion to the existing finite-order inverse
function theorem, allowing different model spaces of the same finite dimension.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E F H H' S M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace S] [ChartedSpace H S] [IsManifold I ∞ S]
  [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M]

theorem exists_finiteInteriorPatch {n : ℕ} (hn : 1 ≤ n)
    {f : S → M} {U : Set S} (hU : IsOpen U) (hf : ContMDiffOn I J n f U)
    {x : S} (hxU : x ∈ U) (hx : I.IsInteriorPoint x)
    (hfx : J.IsInteriorPoint (f x))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (hinj : Injective (mfderiv I J f x)) :
    ∃ Φ : PartialDiffeomorph I J S M n,
      x ∈ Φ.source ∧ Φ.source ⊆ U ∧ EqOn f Φ Φ.source ∧
      Φ.source ⊆ I.interior S ∧ Φ.target ⊆ J.interior M := by
  have hn0 : (n : ℕ∞ω) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (by omega : 0 < n)
  have hnfinite : (n : ℕ∞ω) ≠ ∞ := by exact_mod_cast ENat.natCast_ne_top n
  have hnorder : (1 : ℕ∞ω) ≤ n := by exact_mod_cast hn
  let : IsManifold I n S := IsManifold.of_le (n := ∞) (by simp)
  let : IsManifold J n M := IsManifold.of_le (n := ∞) (by simp)
  let c := DifferentialGeometry.Manifold.interiorChart I n x
  let d := DifferentialGeometry.Manifold.interiorChart J n (f x)
  have hxc : x ∈ c.source :=
    (DifferentialGeometry.Manifold.mem_interiorChart_source_iff I n x).mpr hx
  have hfd : f x ∈ d.source :=
    (DifferentialGeometry.Manifold.mem_interiorChart_source_iff J n (f x)).mpr hfx
  have hcleft (y : S) (hy : y ∈ c.source) : c.symm (c y) = y := c.left_inv' hy
  have hdleft (y : M) (hy : y ∈ d.source) : d.symm (d y) = y := d.left_inv' hy
  let V : Set E := c.target ∩ c.symm ⁻¹' (U ∩ f ⁻¹' d.source)
  have hVo : IsOpen V := c.symm.contMDiffOn.continuousOn.isOpen_inter_preimage
    c.open_target (hf.continuousOn.isOpen_inter_preimage hU d.open_source)
  have hcxV : c x ∈ V := by
    refine ⟨c.map_source hxc, ?_⟩
    change c.symm (c x) ∈ U ∩ f ⁻¹' d.source
    rw [hcleft x hxc]
    exact ⟨hxU, hfd⟩
  let g : E → F := d ∘ f ∘ c.symm
  have hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) n g V :=
    d.contMDiffOn.comp
      (hf.comp (c.symm.contMDiffOn.mono inter_subset_left) (fun y hy => hy.2.1))
      (fun y hy => hy.2.2)
  have hcf := c.symm.isLocalDiffeomorphAt 𝓘(ℝ, E) I n (c.map_source hxc)
  have hdf := d.isLocalDiffeomorphAt J 𝓘(ℝ, F) n hfd
  have hfs := (hf.contMDiffAt (hU.mem_nhds hxU)).mdifferentiableAt hn0
  have hcg : Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g (c x)) := by
    have hfs' : MDifferentiableAt I J f (c.symm (c x)) := by
      rw [hcleft x hxc]
      exact hfs
    have hdf' : MDifferentiableAt J 𝓘(ℝ, F) d (f (c.symm (c x))) := by
      rw [hcleft x hxc]
      exact hdf.mdifferentiableAt hn0
    have hchain := mfderiv_comp (c x) hdf'
      (hfs'.comp (c x) (hcf.mdifferentiableAt hn0))
    have hinner := mfderiv_comp (c x) hfs' (hcf.mdifferentiableAt hn0)
    simp only [Function.comp_apply] at hchain
    rw [hcleft x hxc] at hchain hinner
    rw [show g = d ∘ (f ∘ c.symm) from rfl, hchain, hinner]
    change Injective (fun v => mfderiv J 𝓘(ℝ, F) d (f x)
      (mfderiv I J f x (mfderiv 𝓘(ℝ, E) I c.symm (c x) v)))
    exact (hdf.mfderivToContinuousLinearEquiv hn0).injective.comp
      (hinj.comp (hcf.mfderivToContinuousLinearEquiv hn0).injective)
  let L := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g (c x)
  let A : E ≃L[ℝ] F := (L.toLinearMap.linearEquivOfInjective hcg hdim).toContinuousLinearEquiv
  have hinv : L.IsInvertible := ⟨A, rfl⟩
  have hga := hg.contMDiffAt (hVo.mem_nhds hcxV)
  have hcoord : (fderiv ℝ (writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, F) (c x) g)
      (extChartAt 𝓘(ℝ, E) (c x) (c x))).IsInvertible :=
    (hga.mdifferentiableAt hn0).isInvertible_mfderiv_iff.mp hinv
  obtain ⟨ψ, hcxψ, hψV, hψg⟩ :=
    DifferentialGeometry.Coordinates.exists_partialDiffeomorph_of_contMDiffOn
      hnorder hnfinite hVo hcxV hg hcoord
  let Φ := (c.trans ψ).trans d.symm
  have hEq : EqOn f Φ Φ.source := by
    intro y hy
    have hyc : y ∈ c.source := hy.1.1
    have hcy : c y ∈ ψ.source := hy.1.2
    have hfyd : f y ∈ d.source := by
      have h := (hψV hcy).2.2
      change f (c.symm (c y)) ∈ d.source at h
      rwa [hcleft y hyc] at h
    change f y = d.symm (ψ (c y))
    rw [← hψg hcy]
    change f y = d.symm (d (f (c.symm (c y))))
    rw [hcleft y hyc, hdleft (f y) hfyd]
  refine ⟨Φ, ?_, ?_, hEq, ?_, ?_⟩
  · refine ⟨⟨hxc, hcxψ⟩, ?_⟩
    change ψ (c x) ∈ d.target
    rw [← hψg hcxψ]
    change d (f (c.symm (c x))) ∈ d.target
    rw [hcleft x hxc]
    exact d.map_source hfd
  · intro y hy
    have h := (hψV hy.1.2).2.1
    change c.symm (c y) ∈ U at h
    rwa [hcleft y hy.1.1] at h
  · intro y hy
    exact DifferentialGeometry.Manifold.isInteriorPoint_of_mem_interiorChart_source I n hn0
      (show y ∈ c.source from hy.1.1)
  · intro y hy
    exact DifferentialGeometry.Manifold.isInteriorPoint_of_mem_interiorChart_source J n hn0
      (show y ∈ d.source from hy.1)

end DifferentialGeometry.Topology.Manifold
