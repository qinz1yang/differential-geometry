import DifferentialGeometry.Analysis.Calculus.Inverse.WithinInverse
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.UniqueDifferential

set_option autoImplicit false
noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.OpenPartialHomeomorph

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N]

/-- The existing inverse of an open partial homeomorphism has the same finite
regularity as its forward map when the manifold derivative is invertible.
The within-chart argument includes boundary points of either model. -/
theorem contMDiffOn_symm_of_isInvertible_mfderiv
    (r : ℕ) (hr : 1 ≤ r) [IsManifold I r M] [IsManifold J r N]
    (d : _root_.OpenPartialHomeomorph M N)
    (hf : ContMDiffOn I J r d d.source)
    (hinv : ∀ p ∈ d.source, (mfderiv I J d p).IsInvertible) :
    ContMDiffOn J I r d.symm d.target := by
  have hr' : (1 : ℕ∞ω) ≤ r := by exact_mod_cast hr
  have hr0 : (r : ℕ∞ω) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hr')
  let : IsManifold I 1 M := IsManifold.of_le hr'
  let : IsManifold J 1 N := IsManifold.of_le hr'
  apply contMDiffOn_iff.mpr
  refine ⟨d.continuousOn_symm, ?_⟩
  intro y x
  let c := extChartAt I x
  let k := extChartAt J y
  let S : Set E := c.target ∩ c.symm ⁻¹' (d.source ∩ d ⁻¹' k.source)
  let T : Set F := k.target ∩ k.symm ⁻¹' (d.target ∩ d.symm ⁻¹' c.source)
  let f : E → F := k ∘ d ∘ c.symm
  let g : F → E := c ∘ d.symm ∘ k.symm
  change ContDiffOn ℝ r g T
  have hdsource : UniqueMDiffOn I d.source := d.open_source.uniqueMDiffOn
  have hdtarget : UniqueMDiffOn J d.target := d.open_target.uniqueMDiffOn
  have hS : UniqueDiffOn ℝ S :=
    hdsource.uniqueDiffOn_inter_preimage (I' := J) x y d.continuousOn
  have hT : UniqueDiffOn ℝ T :=
    hdtarget.uniqueDiffOn_inter_preimage (I' := I) y x d.continuousOn_symm
  have hfcoord : ContDiffOn ℝ r f S := (contMDiffOn_iff.mp hf).2 x y
  have hgcoord : ContinuousOn g T :=
    (continuousOn_extChartAt x).comp
      (d.continuousOn_symm.comp
        ((continuousOn_extChartAt_symm y).mono inter_subset_left)
        (fun z hz => hz.2.1))
      (fun z hz => hz.2.2)
  have hgs : MapsTo g T S := by
    intro z hz
    have hzsource : d.symm (k.symm z) ∈ c.source := hz.2.2
    have hztarget : k.symm z ∈ d.target := hz.2.1
    refine ⟨c.map_source hzsource, ?_, ?_⟩
    · change c.symm (c (d.symm (k.symm z))) ∈ d.source
      rw [c.left_inv hzsource]
      exact d.map_target hztarget
    · change d (c.symm (c (d.symm (k.symm z)))) ∈ k.source
      rw [c.left_inv hzsource, d.right_inv hztarget]
      exact k.map_target hz.1
  have hfg : ∀ z ∈ T, f (g z) = z := by
    intro z hz
    change k (d (c.symm (c (d.symm (k.symm z))))) = z
    rw [c.left_inv hz.2.2, d.right_inv hz.2.1, k.right_inv hz.1]
  have hcoordInv : ∀ u ∈ S, (fderivWithin ℝ f S u).IsInvertible := by
    intro u hu
    have hup : c.symm u ∈ d.source := hu.2.1
    have huq : d (c.symm u) ∈ k.source := hu.2.2
    have hdu :=
      ((hf.contMDiffAt (d.open_source.mem_nhds hup)).mdifferentiableAt hr0).hasMFDerivAt
    have hcu := (mdifferentiableWithinAt_extChartAt_symm
      (I := I) (x := x) hu.1).hasMFDerivWithinAt
    have hku := (mdifferentiableAt_extChartAt (I := J) (x := y)
      (by simpa only [k, extChartAt_source] using huq)).hasMFDerivAt
    have hcomp := hku.comp_hasMFDerivWithinAt u (hdu.comp_hasMFDerivWithinAt u hcu)
    let D : E →L[ℝ] F := (mfderiv J 𝓘(ℝ, F) k (d (c.symm u))).comp
      ((mfderiv I J d (c.symm u)).comp
        (mfderivWithin 𝓘(ℝ, E) I c.symm (range I) u))
    have hcompF : HasFDerivWithinAt f D (range I) u := hcomp.hasFDerivWithinAt
    have hderiv := (hcompF.mono
      (show S ⊆ range I from fun z hz => extChartAt_target_subset_range x hz.1)).fderivWithin
        (hS u hu)
    change fderivWithin ℝ f S u = _ at hderiv
    rw [hderiv]
    exact (isInvertible_mfderiv_extChartAt (I := J) (x := y) huq).comp
      ((hinv (c.symm u) hup).comp
        (isInvertible_mfderivWithin_extChartAt_symm (I := I) (x := x) hu.1))
  exact DifferentialGeometry.Analysis.contDiffOn_rightInverse_of_invertible_fderivWithin
    r hS hT hfcoord hgcoord hgs hfg (fun z hz => hcoordInv (g z) (hgs hz))

/-- Bundle finite inverse regularity without changing either map or domain of
the supplied open partial homeomorphism. -/
def toPartialDiffeomorphOfIsInvertibleMFDeriv
    (r : ℕ) (hr : 1 ≤ r) [IsManifold I r M] [IsManifold J r N]
    (d : _root_.OpenPartialHomeomorph M N)
    (hf : ContMDiffOn I J r d d.source)
    (hinv : ∀ p ∈ d.source, (mfderiv I J d p).IsInvertible) :
    PartialDiffeomorph I J M N r where
  toPartialEquiv := d.toPartialEquiv
  open_source := d.open_source
  open_target := d.open_target
  contMDiffOn_toFun := hf
  contMDiffOn_invFun := contMDiffOn_symm_of_isInvertible_mfderiv r hr d hf hinv

end DifferentialGeometry.Topology.OpenPartialHomeomorph
