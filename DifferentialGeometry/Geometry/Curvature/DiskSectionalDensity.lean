import DifferentialGeometry.Geometry.Curvature.DiskGauss
import DifferentialGeometry.Geometry.Curvature.CompactSectionalBound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Ricci.Basic



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry Filter
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]



def diskMapSectionalDensity (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M) (z : ℂ) : ℝ :=
  sectionalCurvature g (U z) (diskMapPartial U z 1) (diskMapPartial U z Complex.I) *
    diskMapConformalCoefficient g U z

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem contDiffOn_diskMapCurvatureNumerator
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) :
    ContDiffOn ℝ ∞ (fun z => g.inner (U z) (diskMapPartial U z 1)
      (riemannOp (LeviCivita g) (U z) (diskMapPartial U z 1)
        (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I))) s := by
  let : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
  have hV (v : ℂ) : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z => TotalSpace.mk' E (U z) (diskMapPartial (E := E) U z v)) s :=
    contMDiffOn_source_partial hs hU (by simp) v
  intro z hz
  have hR : ContMDiffWithinAt 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q => TotalSpace.mk' E (U q)
        (riemannOp (LeviCivita g) (U q) (diskMapPartial U q 1)
          (diskMapPartial U q Complex.I) (diskMapPartial U q Complex.I))) s z := by
    apply ContMDiffWithinAt.clm_bundle_apply (F₁ := E) (F₂ := E)
    · apply ContMDiffWithinAt.clm_bundle_apply (F₁ := E) (F₂ := E →L[ℝ] E)
      · apply ContMDiffWithinAt.clm_bundle_apply (F₁ := E) (F₂ := E →L[ℝ] E →L[ℝ] E)
        · exact (riemannOp_section_contMDiff g).contMDiffAt.comp_contMDiffWithinAt z (hU z hz)
        · exact hV 1 z hz
      · exact hV Complex.I z hz
    · exact hV Complex.I z hz
  have hscalar : ContMDiffWithinAt 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) ∞
      (fun q => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (U q)
        (g.inner (U q) (diskMapPartial U q 1)
          (riemannOp (LeviCivita g) (U q) (diskMapPartial U q 1)
            (diskMapPartial U q Complex.I) (diskMapPartial U q Complex.I)))) s z := by
    apply ContMDiffWithinAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E)
    · exact g.contMDiff.contMDiffAt.comp_contMDiffWithinAt z (hU z hz)
    · exact hV 1 z hz
    · exact hR
  exact (contMDiffWithinAt_totalSpace.mp hscalar).2.contDiffWithinAt



theorem DiskMapConformalAt.sectionalDensity_eq_riemann_div
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {U : ℂ → M} {z : ℂ}
    (hc : DiskMapConformalAt g U z) :
    diskMapSectionalDensity g U z =
      g.inner (U z) (diskMapPartial U z 1)
        (riemannOp (LeviCivita g) (U z) (diskMapPartial U z 1)
          (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I)) /
        diskMapConformalCoefficient g U z := by
  have h := hc.sectional_mul_coefficient
  rw [g.symm (U z)] at h
  exact h



theorem exists_norm_diskMapSectionalDensity_le [CompactSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hconf : ∀ q ∈ s, DiskMapConformalAt g U q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ s,
      ‖diskMapSectionalDensity g U q‖ ≤ C * diskMapConformalCoefficient g U q := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_abs_sectionalCurvature_bound_orthogonal g
  refine ⟨C, hC, ?_⟩
  intro q hq
  have h := hbound (U q) (diskMapPartial U q 1) (diskMapPartial U q Complex.I) (hconf q hq).1
  simpa only [diskMapSectionalDensity, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (diskMapConformalCoefficient_nonneg g U q)] using
    mul_le_mul_of_nonneg_right h (diskMapConformalCoefficient_nonneg g U q)




theorem continuousOn_diskMapSectionalDensity [CompactSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s K : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hKs : K ⊆ s) (hconf : ∀ q ∈ K, DiskMapConformalAt g U q) :
    ContinuousOn (diskMapSectionalDensity g U) K := by
  have ha := (contDiffOn_diskMapConformalCoefficient g hs hU).continuousOn.mono hKs
  have hR := (contDiffOn_diskMapCurvatureNumerator g hs hU).continuousOn.mono hKs
  obtain ⟨C, _, hbound⟩ := exists_norm_diskMapSectionalDensity_le g hconf
  intro z hz
  by_cases hzero : diskMapConformalCoefficient g U z = 0
  · have hbzero : diskMapSectionalDensity g U z = 0 := by
      simp [diskMapSectionalDensity, hzero]
    rw [ContinuousWithinAt, hbzero]
    apply squeeze_zero_norm'
    · filter_upwards [self_mem_nhdsWithin] with q hq
      exact hbound q hq
    · have h := (ha z hz).const_mul C
      simpa only [ContinuousWithinAt, hzero, mul_zero] using h
  · exact ((hR z hz).div (ha z hz) hzero).congr
      (fun q hq => (hconf q hq).sectionalDensity_eq_riemann_div)
      (hconf z hz).sectionalDensity_eq_riemann_div




theorem integrableOn_diskMapSectionalDensity [CompactSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s K : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hK : IsCompact K) (hKs : K ⊆ s) (hconf : ∀ q ∈ K, DiskMapConformalAt g U q) :
    MeasureTheory.IntegrableOn (diskMapSectionalDensity g U) K :=
  (continuousOn_diskMapSectionalDensity g hs hU hKs hconf).integrableOn_compact hK

end DifferentialGeometry.Geometry
