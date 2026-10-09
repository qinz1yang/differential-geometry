import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.FiniteTaylorPolynomial
import DifferentialGeometry.Topology.Manifold.InteriorChart
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry

namespace Analysis

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A finite Taylor polynomial with invertible first derivative gives a smooth
partial diffeomorphism in prescribed neighborhoods, with the original finite jet. -/
theorem exists_partialDiffeomorph_finiteTaylorPolynomial
    {f : E → F} {x : E} {r : ℕ}
    (hf : ContDiffAt ℝ r f x) (hr : 1 ≤ r)
    (hDf : (fderiv ℝ f x).IsInvertible)
    {U : Set E} {V : Set F} (hU : IsOpen U) (hx : x ∈ U)
    (hV : IsOpen V) (hfx : f x ∈ V) :
    ∃ τ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞,
      x ∈ τ.source ∧ τ.source ⊆ U ∧ τ.target ⊆ V ∧
      (τ : E → F) = finiteTaylorPolynomial f x r ∧
      τ x = f x ∧ fderiv ℝ τ x = fderiv ℝ f x ∧
      ∀ k ≤ r, iteratedFDeriv ℝ k τ x = iteratedFDeriv ℝ k f x := by
  obtain ⟨e, hxe, heU, heV, heP, he, hei, hex, heD, hejets⟩ :=
    exists_smooth_localEquiv_finiteTaylorPolynomial hf hr hDf hU hx hV hfx
  let τ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞ :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := he.contMDiffOn
      contMDiffOn_invFun := hei.contMDiffOn }
  exact ⟨τ, hxe, heU, heV, heP, hex, heD, hejets⟩

end Analysis

namespace Manifold

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H H' M N : Type*} [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace H' N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [IsManifold I ∞ M] [IsManifold J ∞ N]

/-- At interior points, an invertible finite jet is realized by a smooth local
diffeomorphism. Both coordinate charts are fixed at the original point and image;
the original map is only assumed to have the stated finite regularity. -/
theorem exists_partialDiffeomorph_eq_finiteJet
    {f : M → N} {p : M} {r : ℕ}
    (hf : ContMDiffAt I J r f p) (hr : 1 ≤ r)
    (hDf : (mfderiv I J f p).IsInvertible)
    (hp : I.IsInteriorPoint p) (hfp : J.IsInteriorPoint (f p))
    {U : Set M} {V : Set N} (hU : IsOpen U) (hpU : p ∈ U)
    (hV : IsOpen V) (hfpV : f p ∈ V) :
    ∃ Φ : PartialDiffeomorph I J M N ∞,
      p ∈ Φ.source ∧ Φ.source ⊆ U ∧ Φ.target ⊆ V ∧
      Φ p = f p ∧ mfderiv I J Φ p = mfderiv I J f p ∧
      ∀ k ≤ r,
        iteratedFDeriv ℝ k
            (extChartAt J (f p) ∘ Φ ∘ (extChartAt I p).symm) (extChartAt I p p) =
          iteratedFDeriv ℝ k
            (extChartAt J (f p) ∘ f ∘ (extChartAt I p).symm) (extChartAt I p p) := by
  let c := interiorChart I ∞ p
  let d := interiorChart J ∞ (f p)
  let x := c p
  let fcoord : E → F := d ∘ f ∘ c.symm
  have hpc : p ∈ c.source := (mem_interiorChart_source_iff I ∞ p).mpr hp
  have hfd : f p ∈ d.source := (mem_interiorChart_source_iff J ∞ (f p)).mpr hfp
  have hc_inv : c.symm (c p) = p := c.toPartialEquiv.left_inv hpc
  have hd_inv : d.symm (d (f p)) = f p := d.toPartialEquiv.left_inv hfd
  have hRange : range I ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hp
  have hfcoord : ContDiffAt ℝ r fcoord x :=
    (contMDiffAt_iff.mp hf).2.contDiffAt hRange
  have hf_diff : MDifferentiableAt I J f p :=
    hf.mdifferentiableAt (by exact_mod_cast (show r ≠ 0 by omega))
  have hDcoord : (mfderiv I J f p : E →L[ℝ] F) = fderiv ℝ fcoord x := by
    have hmf : (mfderiv I J f p : E →L[ℝ] F) =
        fderivWithin ℝ fcoord (range I) x := hf_diff.mfderiv_abuse
    exact hmf.trans (fderivWithin_of_mem_nhds hRange)
  have hcoordInv : (fderiv ℝ fcoord x).IsInvertible := hDcoord ▸ hDf
  let Uc : Set E := c.target ∩ c.symm ⁻¹' U
  let Vd : Set F := d.target ∩ d.symm ⁻¹' V
  have hUc : IsOpen Uc := c.toOpenPartialHomeomorph.isOpen_inter_preimage_symm hU
  have hVd : IsOpen Vd := d.toOpenPartialHomeomorph.isOpen_inter_preimage_symm hV
  have hxUc : x ∈ Uc := by
    refine ⟨c.toOpenPartialHomeomorph.map_source hpc, ?_⟩
    change c.symm (c p) ∈ U
    rwa [hc_inv]
  have hfcoordx : fcoord x = d (f p) := by
    change d (f (c.symm (c p))) = d (f p)
    rw [hc_inv]
  have hfxVd : fcoord x ∈ Vd := by
    rw [hfcoordx]
    refine ⟨d.toOpenPartialHomeomorph.map_source hfd, ?_⟩
    change d.symm (d (f p)) ∈ V
    rwa [hd_inv]
  obtain ⟨τ, hxτ, hτU, hτV, _, hτx, hτD, hτjets⟩ :=
    Analysis.exists_partialDiffeomorph_finiteTaylorPolynomial
      hfcoord hr hcoordInv hUc hxUc hVd hfxVd
  let Φ := (c.trans τ).trans d.symm
  have hpΦ : p ∈ Φ.source := by
    change (p ∈ c.source ∧ c p ∈ τ.source) ∧ τ (c p) ∈ d.target
    exact ⟨⟨hpc, hxτ⟩, (hτV (τ.toOpenPartialHomeomorph.map_source hxτ)).1⟩
  have hΦU : Φ.source ⊆ U := by
    intro q hq
    change (q ∈ c.source ∧ c q ∈ τ.source) ∧ τ (c q) ∈ d.target at hq
    have h := (hτU hq.1.2).2
    have hcinv : c.symm (c q) = q := c.toPartialEquiv.left_inv hq.1.1
    change c.symm (c q) ∈ U at h
    rwa [hcinv] at h
  have hΦV : Φ.target ⊆ V := by
    intro q hq
    change q ∈ d.source ∧ d q ∈ τ.target ∧ τ.symm (d q) ∈ c.target at hq
    have h := (hτV hq.2.1).2
    have hdinv : d.symm (d q) = q := d.toPartialEquiv.left_inv hq.1
    change d.symm (d q) ∈ V at h
    rwa [hdinv] at h
  have hΦp : Φ p = f p := by
    change d.symm (τ x) = f p
    rw [hτx, hfcoordx]
    exact hd_inv
  have hlocal : d ∘ Φ ∘ c.symm =ᶠ[𝓝 x] (τ : E → F) := by
    filter_upwards [τ.open_source.mem_nhds hxτ] with y hy
    have hcy : y ∈ c.target := (hτU hy).1
    have hdτy : τ y ∈ d.target := (hτV (τ.toOpenPartialHomeomorph.map_source hy)).1
    have hcr : c (c.symm y) = y := c.toPartialEquiv.right_inv hcy
    have hdr : d (d.symm (τ y)) = τ y := d.toPartialEquiv.right_inv hdτy
    change d (d.symm (τ (c (c.symm y)))) = τ y
    rw [hcr, hdr]
  have hΦDcoord : (mfderiv I J Φ p : E →L[ℝ] F) =
      fderiv ℝ (d ∘ Φ ∘ c.symm) x := by
    have hmf : (mfderiv I J Φ p : E →L[ℝ] F) =
        fderivWithin ℝ (writtenInExtChartAt I J p Φ) (range I) x :=
      (Φ.mdifferentiableAt (by simp) hpΦ).mfderiv_abuse
    have hfd : fderivWithin ℝ (writtenInExtChartAt I J p Φ) (range I) x =
        fderiv ℝ (writtenInExtChartAt I J p Φ) x :=
      fderivWithin_of_mem_nhds hRange
    have hchart : writtenInExtChartAt I J p Φ = d ∘ Φ ∘ c.symm := by
      change extChartAt J (Φ p) ∘ Φ ∘ (extChartAt I p).symm = d ∘ Φ ∘ c.symm
      rw [hΦp]
      rfl
    exact (hmf.trans hfd).trans (congrArg (fun f' : E → F => fderiv ℝ f' x) hchart)
  refine ⟨Φ, hpΦ, hΦU, hΦV, hΦp, ?_, ?_⟩
  · rw [hΦDcoord, hlocal.fderiv_eq, hτD, ← hDcoord]
  · intro k hk
    exact ((hlocal.iteratedFDeriv ℝ k).self_of_nhds).trans (hτjets k hk)

end Manifold

end DifferentialGeometry
