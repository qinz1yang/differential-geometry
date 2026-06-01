import DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.Manifold
import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Topology.VectorBundle.Basic

/-!
# Smoothness of the lifted metric on the universal cover

Chart-conjugacy lemmas used to prove that the fiberwise pullback of a smooth
Riemannian metric `g` on `M` along `proj : UC M → M` is itself smooth.

The tangent bundle of `UC M` is built independently of `M`'s (not as a
pullback), so smoothness of the lifted metric reduces to comparing chart
trivialisations of the tangent bundle of `UC M` with those of `M` via the
local-section factorisation `coverChartAt = (localSection a).trans (chartAt …)`.

This file decomposes the smoothness assembly into four ingredients:

* `uc_coverChartAt_extend_conjugacy` — extended-chart factorisation of the
  cover-charts through the local section and the base chart.
* `uc_tangentBundleCore_coordChange_agree` — coordinate-change of the tangent
  bundle of `UC M` agrees with that of `M` on the chart intersection.
* `uc_hom_bundle_inCoordinates_pullback` — the `inCoordinates` representation
  of the metric, viewed in the Hom-bundle, pulls back along `proj`.
* `uc_liftedMetric_contMDiff` — assembly: the metric section is smooth.
-/

open Set Function Filter Bundle
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Integral.Measure (SmoothRiemannianMetric)

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocPathConnectedSpace M]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
  [Inhabited M]

/-- **Extended-chart conjugacy at a cover-point.**

For every cover-point `a : UC M`, the extended cover-chart at `a` factors
through the local section followed by the extended base-chart at `proj a`, and
the inverse factors symmetrically through the inverse base-chart followed by
the inverse local section:
```
(coverChartAt a).extend I = ((chartAt H (proj a)).extend I) ∘ (localSection a)
((coverChartAt a).extend I).symm
    = (localSection a).symm ∘ ((chartAt H (proj a)).extend I).symm
```

These are global function equalities (definitional via
`OpenPartialHomeomorph.coe_trans`, `coe_trans_symm`, and the defining unfolding
`coverChartAt a = (localSection a).trans (chartAt H (proj a))`). The downstream
tangent-bundle coordinate-change comparison combines this with
`localSection_collapse` to identify the universal-cover transition with the
base-manifold transition. -/
theorem uc_coverChartAt_extend_conjugacy
    (a : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :
    ((coverChartAt a).extend I : _ → E)
        = ((chartAt H (proj a)).extend I) ∘ (localSection a) ∧
      (((coverChartAt a).extend I).symm : E → _)
        = (localSection a).symm ∘ ((chartAt H (proj a)).extend I).symm := by
  refine ⟨?_, ?_⟩
  · funext z
    change I ((coverChartAt a) z) = ((chartAt H (proj a)).extend I) ((localSection a) z)
    have hcov : (coverChartAt a) z
        = (chartAt H (proj a)) ((localSection a) z) := by
      change ((localSection a).trans (chartAt H (proj a))) z
          = (chartAt H (proj a)) ((localSection a) z)
      rw [OpenPartialHomeomorph.trans_apply]
    have hext : ((chartAt H (proj a)).extend I) ((localSection a) z)
        = I ((chartAt H (proj a)) ((localSection a) z)) := by
      rw [OpenPartialHomeomorph.extend_coe]; rfl
    rw [hcov, hext]
  · funext y
    change ((coverChartAt a).extend I).symm y
        = (localSection a).symm
            (((chartAt H (proj a)).extend I).symm y)
    have hExtSymm :
        ((coverChartAt a).extend I).symm y
          = (coverChartAt a).symm (I.symm y) := by
      rw [OpenPartialHomeomorph.extend_coe_symm]; rfl
    have hSymm : (coverChartAt a).symm (I.symm y)
        = (localSection a).symm
            ((chartAt H (proj a)).symm (I.symm y)) := by
      change ((localSection a).trans (chartAt H (proj a))).symm (I.symm y)
          = (localSection a).symm ((chartAt H (proj a)).symm (I.symm y))
      rw [OpenPartialHomeomorph.coe_trans_symm]
      rfl
    have hChartExtSymm :
        ((chartAt H (proj a)).extend I).symm y
          = (chartAt H (proj a)).symm (I.symm y) := by
      rw [OpenPartialHomeomorph.extend_coe_symm]; rfl
    rw [hExtSymm, hSymm, hChartExtSymm]

/-- **Tangent-bundle coordinate-change agreement.**

For cover-points `a b : UC M` and `z` in the chart-source intersection
of `chartAt H a` and `chartAt H b` on the universal cover, the tangent-bundle
coordinate change of `UC M` between `achart H a` and `achart H b` agrees with
that of `M` between `achart H (proj a)` and `achart H (proj b)` evaluated at
`proj z`:
```
(tangentBundleCore I (UC M)).coordChange (achart H a) (achart H b) z
  = (tangentBundleCore I M).coordChange (achart H (proj a)) (achart H (proj b)) (proj z)
```

Proof: `coordChange` unfolds via `tangentBundleCore_coordChange_achart` to
`fderivWithin ℝ (extChartAt I _ ∘ (extChartAt I _).symm) (range I) (extChartAt I _ _)`.
By `uc_coverChartAt_extend_conjugacy` the cover-side composition factors
through the base-side composition by `localSection ∘ (localSection).symm`,
which collapses to the identity on the local section's target by
`localSection_collapse`. The factor `localSection a z = proj z` identifies the
base-points of `fderivWithin`. The remaining filter-pointwise equality on a
neighbourhood follows from continuity of the base-side chart inverse plus
openness of `(localSection a).target`, packaged via
`Filter.EventuallyEq.fderivWithin_eq`. -/
theorem uc_tangentBundleCore_coordChange_agree
    (a b : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    {z : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M}
    (hz : z ∈ (chartAt H a).source ∩ (chartAt H b).source) :
    (tangentBundleCore I
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)).coordChange
        (achart H a) (achart H b) z
      = (tangentBundleCore I M).coordChange
          (achart H (proj a)) (achart H (proj b)) (proj z) := by
  set Ea : OpenPartialHomeomorph
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) H :=
    coverChartAt a with hEa
  set Fa : OpenPartialHomeomorph M H := chartAt H (proj a) with hFa
  obtain ⟨hConjA_fwd, hConjA_inv⟩ := uc_coverChartAt_extend_conjugacy (I := I) a
  obtain ⟨hConjB_fwd, _hConjB_inv⟩ := uc_coverChartAt_extend_conjugacy (I := I) b
  have hz_a : z ∈ (coverChartAt a).source := hz.1
  have hz_b : z ∈ (coverChartAt b).source := hz.2
  have hz_a_inter : z ∈ (localSection (M := M) a).source ∩
      (localSection (M := M) a) ⁻¹' (chartAt H (proj a)).source := by
    have hsrc : ((coverChartAt a) :
        OpenPartialHomeomorph
          (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) H).source
        = (localSection a).source ∩
          (localSection a) ⁻¹' (chartAt H (proj a)).source :=
      coverChartAt_source_eq a
    rw [hsrc] at hz_a; exact hz_a
  have hz_b_inter : z ∈ (localSection (M := M) b).source ∩
      (localSection (M := M) b) ⁻¹' (chartAt H (proj b)).source := by
    have hsrc : ((coverChartAt b) :
        OpenPartialHomeomorph
          (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) H).source
        = (localSection b).source ∩
          (localSection b) ⁻¹' (chartAt H (proj b)).source :=
      coverChartAt_source_eq b
    rw [hsrc] at hz_b; exact hz_b
  obtain ⟨hzLSa_src, hzLSa_chart⟩ := hz_a_inter
  obtain ⟨_hzLSb_src, hzLSb_chart⟩ := hz_b_inter
  have hLSa_z : (localSection a) z = proj z := by
    have := congrArg (fun f => f z) (proj_eq_localSection a)
    simpa using this.symm
  have hLSb_z : (localSection b) z = proj z := by
    have := congrArg (fun f => f z) (proj_eq_localSection b)
    simpa using this.symm
  have hprojz_Fa : proj z ∈ Fa.source := by
    rw [Set.mem_preimage, hLSa_z] at hzLSa_chart; exact hzLSa_chart
  have _hprojz_Fb : proj z ∈ (chartAt H (proj b)).source := by
    rw [Set.mem_preimage, hLSb_z] at hzLSb_chart; exact hzLSb_chart
  have hprojz_LSa_tgt : proj z ∈ (localSection a).target := by
    have := (localSection a).map_source hzLSa_src
    rwa [hLSa_z] at this
  have hBase : (Ea.extend I) z = (Fa.extend I) (proj z) := by
    have := congrArg (fun f => f z) hConjA_fwd
    simp only [Function.comp_apply] at this
    rw [this, hLSa_z]
  rw [tangentBundleCore_coordChange_achart, tangentBundleCore_coordChange_achart]
  change fderivWithin ℝ ((extChartAt I b) ∘ (extChartAt I a).symm) (Set.range I)
      (extChartAt I a z)
    = fderivWithin ℝ ((extChartAt I (proj b)) ∘ (extChartAt I (proj a)).symm)
        (Set.range I) (extChartAt I (proj a) (proj z))
  have hBase' : extChartAt I a z = extChartAt I (proj a) (proj z) := hBase
  rw [hBase']
  refine Filter.EventuallyEq.fderivWithin_eq ?_ ?_
  · have hContSymm : ContinuousAt ((chartAt H (proj a)).extend I).symm
        ((chartAt H (proj a)).extend I (proj z)) :=
      OpenPartialHomeomorph.continuousAt_extend_symm (I := I) _ hprojz_Fa
    have hOpenTgt : IsOpen (localSection a).target := (localSection a).open_target
    have hMemTgt : ((chartAt H (proj a)).extend I).symm
          ((chartAt H (proj a)).extend I (proj z)) ∈ (localSection a).target := by
      rw [OpenPartialHomeomorph.extend_left_inv _ hprojz_Fa]
      exact hprojz_LSa_tgt
    have hPre : ((chartAt H (proj a)).extend I).symm ⁻¹' (localSection a).target
        ∈ 𝓝 ((chartAt H (proj a)).extend I (proj z)) :=
      hContSymm (hOpenTgt.mem_nhds hMemTgt)
    refine mem_nhdsWithin_of_mem_nhds ?_
    filter_upwards [hPre] with y hy
    show ((extChartAt I b) ∘ (extChartAt I a).symm) y
        = ((extChartAt I (proj b)) ∘ (extChartAt I (proj a)).symm) y
    simp only [Function.comp_apply]
    have hLHS_symm : (extChartAt I a).symm y =
        (localSection a).symm (((chartAt H (proj a)).extend I).symm y) := by
      change ((coverChartAt a).extend I).symm y =
          (localSection a).symm (((chartAt H (proj a)).extend I).symm y)
      have := congrArg (fun f => f y) hConjA_inv
      simpa [Function.comp_apply] using this
    have hLHS_fwd :
        (extChartAt I b) ((extChartAt I a).symm y) =
          ((chartAt H (proj b)).extend I)
            ((localSection b) ((extChartAt I a).symm y)) := by
      change ((coverChartAt b).extend I) ((extChartAt I a).symm y) =
          ((chartAt H (proj b)).extend I)
            ((localSection b) ((extChartAt I a).symm y))
      have := congrArg (fun f => f ((extChartAt I a).symm y)) hConjB_fwd
      simpa [Function.comp_apply] using this
    rw [hLHS_fwd, hLHS_symm]
    have hCollapse := localSection_collapse a b hy
    rw [hCollapse]
    rfl
  · show ((extChartAt I b) ∘ (extChartAt I a).symm) (extChartAt I (proj a) (proj z))
        = ((extChartAt I (proj b)) ∘ (extChartAt I (proj a)).symm)
          (extChartAt I (proj a) (proj z))
    simp only [Function.comp_apply]
    have hSymmFa : (extChartAt I (proj a)).symm (extChartAt I (proj a) (proj z)) = proj z := by
      change ((chartAt H (proj a)).extend I).symm
          (((chartAt H (proj a)).extend I) (proj z)) = proj z
      exact OpenPartialHomeomorph.extend_left_inv _ hprojz_Fa
    rw [hSymmFa]
    rw [← hBase']
    have hSymmEa : (extChartAt I a).symm (extChartAt I a z) = z := by
      change ((coverChartAt a).extend I).symm (((coverChartAt a).extend I) z) = z
      exact OpenPartialHomeomorph.extend_left_inv _ hz_a
    rw [hSymmEa]
    have hBaseB : (extChartAt I b) z = (extChartAt I (proj b)) (proj z) := by
      change ((coverChartAt b).extend I) z = ((chartAt H (proj b)).extend I) (proj z)
      have := congrArg (fun f => f z) hConjB_fwd
      simp only [Function.comp_apply] at this
      rw [this, hLSb_z]
    exact hBaseB

/-- **Hom-bundle `inCoordinates` pulls back along `proj`.**

For a smooth Riemannian metric `g : SmoothRiemannianMetric I M` on `M` and
cover-points `a x : UC M` with `x ∈ (chartAt H a).source` (so that the
trivializations at `a` are valid at `x`), the `inCoordinates` representation
(in the Hom-bundle `TangentSpace I · →L[ℝ] ℝ` over `UC M`, with model fibre
`E →L[ℝ] ℝ`) of the metric value `g.inner (proj x)` at base point `x` viewed
via the cover-trivialisation at `a` equals the corresponding `inCoordinates`
representation on `M` evaluated via the base-trivialisation at `proj a` and
base-point `proj x`.

The proof reduces, by definition of `inCoordinates`, to agreement of
`continuousLinearMapAt` and `symmL` of the tangent-bundle trivialisations
between `UC M` and `M`; this in turn follows from
`uc_tangentBundleCore_coordChange_agree` (which packages the cover-side
coordinate-change as the base-side coordinate-change at `proj x`) combined
with `continuousLinearMapAt_trivializationAt_eq_core` and
`symmL_trivializationAt_eq_core`. -/
theorem uc_hom_bundle_inCoordinates_pullback
    (g : SmoothRiemannianMetric I M)
    (a : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    {x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M}
    (hx : x ∈ (chartAt H a).source) :
    ContinuousLinearMap.inCoordinates (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
        E (TangentSpace I :
            DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
              → Type _)
        (E →L[ℝ] ℝ)
        (fun b : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
          => TangentSpace I b →L[ℝ] ℝ)
        a x a x (g.inner (proj x))
      = ContinuousLinearMap.inCoordinates (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
          E (TangentSpace I : M → Type _)
          (E →L[ℝ] ℝ) (fun b : M => TangentSpace I b →L[ℝ] ℝ)
          (proj a) (proj x) (proj a) (proj x) (g.inner (proj x)) := by
  have hx_UC : x ∈ (trivializationAt E
      (TangentSpace I :
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → Type _) a).baseSet := by
    change x ∈ (chartAt H a).source; exact hx
  have hxAA : x ∈ (chartAt H a).source ∩ (chartAt H a).source := ⟨hx, hx⟩
  have hpx_M : proj x ∈ (trivializationAt E (TangentSpace I : M → Type _) (proj a)).baseSet := by
    have hsrc : ((coverChartAt a) :
        OpenPartialHomeomorph
          (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) H).source
        = (localSection a).source ∩
          (localSection a) ⁻¹' (chartAt H (proj a)).source :=
      coverChartAt_source_eq a
    have hx' : x ∈ (coverChartAt a).source := hx
    rw [hsrc] at hx'
    obtain ⟨hLS, hLSproj⟩ := hx'
    rw [Set.mem_preimage] at hLSproj
    have hLSx : (localSection a) x = proj x := by
      have := congrArg (fun f => f x) (proj_eq_localSection a)
      simpa using this.symm
    rw [hLSx] at hLSproj
    change proj x ∈ (chartAt H (proj a)).source; exact hLSproj
  have hSymmL :
      ((trivializationAt E (TangentSpace I :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → Type _) a).symmL
            ℝ x : E →L[ℝ] E)
        = ((trivializationAt E (TangentSpace I : M → Type _) (proj a)).symmL ℝ (proj x)
            : E →L[ℝ] E) := by
    rw [TangentBundle.symmL_trivializationAt_eq_core (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (b₀ := a) (b := x) hx,
        TangentBundle.symmL_trivializationAt_eq_core (I := I) (M := M)
          (b₀ := proj a) (b := proj x)
          (show proj x ∈ (chartAt H (proj a)).source from hpx_M)]
    exact uc_tangentBundleCore_coordChange_agree (I := I) a x ⟨hx, mem_chart_source H x⟩
  have hCLM :
      ((trivializationAt E (TangentSpace I :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → Type _) a).continuousLinearMapAt
            ℝ x : E →L[ℝ] E)
        = ((trivializationAt E (TangentSpace I : M → Type _) (proj a)).continuousLinearMapAt
            ℝ (proj x) : E →L[ℝ] E) := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (b₀ := a) (b := x) hx,
        TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := I) (M := M)
          (b₀ := proj a) (b := proj x)
          (show proj x ∈ (chartAt H (proj a)).source from hpx_M)]
    exact uc_tangentBundleCore_coordChange_agree (I := I) x a
      ⟨mem_chart_source H x, hx⟩
  unfold ContinuousLinearMap.inCoordinates
  refine congrArg₂ ContinuousLinearMap.comp ?_ ?_
  · have hx_hom_UC : x ∈ (trivializationAt (E →L[ℝ] ℝ)
        (fun b : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
          => TangentSpace I b →L[ℝ] ℝ) a).baseSet := by
      change x ∈ (trivializationAt E
        (TangentSpace I :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → Type _) a).baseSet ∩
          (trivializationAt ℝ (Bundle.Trivial _ ℝ) a).baseSet
      exact ⟨hx_UC, Set.mem_univ _⟩
    have hpx_hom_M : proj x ∈ (trivializationAt (E →L[ℝ] ℝ)
        (fun b : M => TangentSpace I b →L[ℝ] ℝ) (proj a)).baseSet := by
      change proj x ∈ (trivializationAt E (TangentSpace I : M → Type _) (proj a)).baseSet ∩
          (trivializationAt ℝ (Bundle.Trivial M ℝ) (proj a)).baseSet
      exact ⟨hpx_M, Set.mem_univ _⟩
    ext L v
    have hLHS :
        ((trivializationAt (E →L[ℝ] ℝ)
          (fun b : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
            => TangentSpace I b →L[ℝ] ℝ) a).continuousLinearMapAt ℝ x L : E →L[ℝ] ℝ)
        = ((trivializationAt ℝ (Bundle.Trivial _ ℝ) a).continuousLinearMapAt ℝ x).comp
            (L.comp ((trivializationAt E
              (TangentSpace I :
                DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → Type _)
                a).symmL ℝ x)) := by
      rw [Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hx_hom_UC]
      rfl
    have hRHS :
        ((trivializationAt (E →L[ℝ] ℝ) (fun b : M => TangentSpace I b →L[ℝ] ℝ)
              (proj a)).continuousLinearMapAt ℝ (proj x) L : E →L[ℝ] ℝ)
        = ((trivializationAt ℝ (Bundle.Trivial M ℝ) (proj a)).continuousLinearMapAt ℝ (proj x)).comp
            (L.comp ((trivializationAt E (TangentSpace I : M → Type _)
              (proj a)).symmL ℝ (proj x))) := by
      rw [Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hpx_hom_M]
      rfl
    change ((trivializationAt (E →L[ℝ] ℝ)
          (fun b : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
            => TangentSpace I b →L[ℝ] ℝ) a).continuousLinearMapAt ℝ x L : E →L[ℝ] ℝ) v
      = ((trivializationAt (E →L[ℝ] ℝ) (fun b : M => TangentSpace I b →L[ℝ] ℝ)
              (proj a)).continuousLinearMapAt ℝ (proj x) L : E →L[ℝ] ℝ) v
    rw [hLHS, hRHS]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      Bundle.Trivial.fiberBundle_trivializationAt',
      Bundle.Trivial.continuousLinearMapAt_trivialization,
      ContinuousLinearMap.coe_id', id_eq]
    have hsymm_eq :
        ((trivializationAt E
          (TangentSpace I :
            DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → Type _)
            a).symmL ℝ x : E →L[ℝ] E) v
        = ((trivializationAt E (TangentSpace I : M → Type _)
            (proj a)).symmL ℝ (proj x) : E →L[ℝ] E) v :=
      congrArg (fun (f : E →L[ℝ] E) => f v) hSymmL
    exact congrArg L hsymm_eq
  · exact congrArg (fun (f : E →L[ℝ] E) => (g.inner (proj x)).comp f) hSymmL

/-- **The lifted metric is a smooth section of the `(0,2)`-Hom-bundle.**

For a smooth Riemannian metric `g` on `M`, the metric section
`fun a : UC M => TotalSpace.mk' _ a (g.inner (proj a))` is `ContMDiff` from
`UC M` into the total space of the `(0,2)`-Hom-bundle
`TangentSpace I · →L[ℝ] TangentSpace I · →L[ℝ] ℝ` over `UC M`.

Strategy: apply `contMDiffAt_hom_bundle` pointwise; the base-projection is
the identity (smooth); the in-coordinates piece equals — by
`uc_hom_bundle_inCoordinates_pullback` on the chart neighbourhood of each
point — the corresponding in-coordinates on `M` evaluated at `proj x`, which
is smooth as the composition of `g.contMDiff` and `proj_contMDiff` followed
by the `inCoordinates` map. The eventually-equal transfer is via
`ContMDiffAt.congr_of_eventuallyEq`. -/
theorem uc_liftedMetric_contMDiff
    (g : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun a : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
        => (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) a (g.inner (proj a)) :
              TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
                (fun b : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
                  => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ))) := by
  intro a₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨?_, ?_⟩
  · exact contMDiffAt_id
  · have hopen : (chartAt H a₀).source ∈
        (𝓝 a₀ : Filter
          (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)) :=
      (chartAt H a₀).open_source.mem_nhds (mem_chart_source H a₀)
    have hEvEq : (fun a : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
        => ContinuousLinearMap.inCoordinates (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
          E (TangentSpace I :
              DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → Type _)
          (E →L[ℝ] ℝ)
          (fun b : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
            => TangentSpace I b →L[ℝ] ℝ)
          a₀ a a₀ a (g.inner (proj a)))
        =ᶠ[𝓝 a₀] (fun a : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
        => ContinuousLinearMap.inCoordinates (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
          E (TangentSpace I : M → Type _)
          (E →L[ℝ] ℝ) (fun b : M => TangentSpace I b →L[ℝ] ℝ)
          (proj a₀) (proj a) (proj a₀) (proj a) (g.inner (proj a))) := by
      filter_upwards [hopen] with a ha
      exact uc_hom_bundle_inCoordinates_pullback (I := I) (M := M) g a₀ ha
    have hgAt : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) b (g.inner b)
          : M → TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
              (fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)) (proj a₀) :=
      g.contMDiff (proj a₀)
    rw [contMDiffAt_hom_bundle] at hgAt
    obtain ⟨_, hInCoords_M⟩ := hgAt
    have hproj : ContMDiffAt I I ∞
        (proj :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M) a₀ :=
      (proj_contMDiff (I := I) (M := M)).contMDiffAt
    have hcomp : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
        (fun a : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
          => ContinuousLinearMap.inCoordinates (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
            E (TangentSpace I : M → Type _)
            (E →L[ℝ] ℝ) (fun b : M => TangentSpace I b →L[ℝ] ℝ)
            (proj a₀) (proj a) (proj a₀) (proj a) (g.inner (proj a))) a₀ :=
      hInCoords_M.comp a₀ hproj
    exact hcomp.congr_of_eventuallyEq hEvEq

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end
