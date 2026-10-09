import DifferentialGeometry.Geometry.MinimalSurface.Variation.ParameterMetricDerivative
import DifferentialGeometry.Geometry.MinimalSurface.Variation.DiskDivergence
import DifferentialGeometry.Geometry.MinimalSurface.Variation.DiskIsotopyIntegral
import DifferentialGeometry.Bundle.PartialMfderiv.TimeDerivative
import DifferentialGeometry.Topology.Order.Interval
import DifferentialGeometry.Bundle.TangentChart
import DifferentialGeometry.Bundle.PartialMfderiv.Parameter
import DifferentialGeometry.Geometry.Connection.SourceSectionPairing
import DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation.Basic
import DifferentialGeometry.Analysis.Calculus.TimeJet.Commutation
import DifferentialGeometry.Geometry.Metric.FamilySourceDerivative
import DifferentialGeometry.Geometry.MinimalSurface.Variation.DiskMetricVariation



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry Filter MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
private theorem contMDiffOn_isotopyDisk
    {Φ : ℝ → M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M} {T : Set ℝ}
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2) (T ×ˢ univ))
    {U : ℂ → M} {s : Set ℂ} (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) ∞
      (fun p : ℝ × ℂ => Φ p.1 (U p.2)) (T ×ˢ s) := by
  have hmap : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℂ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × ℂ => (p.1, U p.2)) (T ×ˢ s) :=
    contMDiffOn_fst.prodMk (hU.comp contMDiffOn_snd (fun _ hp => hp.2))
  have h := hΦ.comp hmap (fun p hp => ⟨hp.1, mem_univ _⟩)
  rwa [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
private theorem isotopyDisk_time_partial
    {Φ : ℝ → M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M} {U : ℂ → M}
    {t : ℝ} {z : ℂ}
    (hA : MDifferentiableAt 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E)
      (fun p : ℝ × ℂ => Φ p.1 (U p.2)) (t, z)) :
    mfderiv 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) (fun p : ℝ × ℂ => Φ p.1 (U p.2)) (t, z) (1, 0) =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => Φ r (U z)) t 1 := by
  have hAp : MDifferentiableAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, E)
      (fun p : ℝ × ℂ => Φ p.1 (U p.2)) (t, z) := by
    rwa [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have h := mfderiv_parameter_time hAp 1
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
  exact h.symm

omit [FiniteDimensional ℝ E] in
theorem contMDiffOn_isotopyDiskVelocity
    {Φ : ℝ → M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M} {T : Set ℝ}
    (hT : IsOpen T) {t : ℝ} (ht : t ∈ T)
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2) (T ×ˢ univ))
    (hΦt : Φ t = Diffeomorph.refl 𝓘(ℝ, E) M ∞)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) :
    ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q => TotalSpace.mk' E (E := TangentSpace 𝓘(ℝ, E)) (U q)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => Φ r (U q)) t 1)) s := by
  have hA := contMDiffOn_isotopyDisk hΦ hU
  have hopen := hT.prod hs
  have hp := contMDiffOn_source_partial hopen hA (m := ∞) (by simp) (1, 0)
  have hc : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ × ℂ) ∞ (fun q : ℂ => (t, q)) :=
    (contDiff_const.prodMk contDiff_id).contMDiff
  apply (hp.comp hc.contMDiffOn (fun q hq => ⟨ht, hq⟩)).congr
  intro q hq
  have htime := isotopyDisk_time_partial
    (((hA _ ⟨ht, hq⟩).contMDiffAt (hopen.mem_nhds ⟨ht, hq⟩)).mdifferentiableAt (by simp))
  dsimp only [Function.comp_apply]
  rw [htime]
  have heq : Φ t (U q) = U q := by rw [hΦt]; rfl
  rw [heq]

variable [T2Space M]

private theorem deriv_isotopyPartialPairing
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t : ℝ} (ht : D.regular ∈ 𝓝 t)
    {Φ : ℝ → M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M} {T : Set ℝ}
    (hT : IsOpen T) (hTt : t ∈ T)
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2) (T ×ˢ univ))
    (hΦt : Φ t = Diffeomorph.refl 𝓘(ℝ, E) M ∞)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) {z : ℂ} (hz : z ∈ s) (v : ℂ) :
    let W := fun q => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => Φ r (U q)) t 1
    deriv (fun r => (Diffeomorph.pullbackMetric (G r) (Φ r)).inner (U z)
      (diskMapPartial U z v) (diskMapPartial U z v)) t =
      deriv (fun r => (G r).inner (U z) (diskMapPartial U z v) (diskMapPartial U z v)) t +
        2 * (G t).inner (U z) (sourceSectionCovariantDerivative (G t) U W z v)
          (diskMapPartial U z v) := by
  let A : ℝ × ℂ → M := fun p => Φ p.1 (U p.2)
  let V := fun p => mfderiv 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) A p (0, v)
  let W := fun q => mfderiv 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) A (t, q) (1, 0)
  have hA := contMDiffOn_isotopyDisk hΦ hU
  have hopen := hT.prod hs
  have hAz (r : ℝ) (hr : r ∈ T) : MDifferentiableAt 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) A (r, z) :=
    ((hA _ ⟨hr, hz⟩).contMDiffAt (hopen.mem_nhds ⟨hr, hz⟩)).mdifferentiableAt (by simp)
  have hUz := ((hU z hz).contMDiffAt (hs.mem_nhds hz)).mdifferentiableAt (by simp)
  have hV (r : ℝ) (hr : r ∈ T) : V (r, z) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ r) (U z) (diskMapPartial U z v) := by
    have hAp : MDifferentiableAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, E) A (r, z) := by
      rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
      exact hAz r hr
    have hh := mfderiv_parameter_slice hAp v
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hh
    have hcomp := mfderiv_comp z ((Φ r).contMDiff.contMDiffAt.mdifferentiableAt (by simp)) hUz
    change mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q => A (r, q)) z = _ at hcomp
    rw [hcomp] at hh
    exact hh.symm
  have hpair : (fun r => (Diffeomorph.pullbackMetric (G r) (Φ r)).inner (U z)
      (diskMapPartial U z v) (diskMapPartial U z v)) =ᶠ[𝓝 t]
      (fun r => (G r).inner (A (r, z)) (V (r, z)) (V (r, z))) := by
    filter_upwards [hT.mem_nhds hTt] with r hr
    rw [Diffeomorph.pullbackMetric_inner, hV r hr]
  have hVt : V (t, z) = diskMapPartial U z v := by
    have hfun : (Φ t : M → M) = id := by
      rw [hΦt]
      rfl
    have hv := hV t hTt
    rw [hfun, mfderiv_id] at hv
    exact hv
  have hAt : (fun q => A (t, q)) = U := by
    funext q
    simp [A, hΦt]
  have hW : ∀ᶠ q in 𝓝 z, W q =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => Φ r (U q)) t 1 := by
    filter_upwards [hs.mem_nhds hz] with q hq
    exact isotopyDisk_time_partial
      (((hA _ ⟨hTt, hq⟩).contMDiffAt (hopen.mem_nhds ⟨hTt, hq⟩)).mdifferentiableAt (by simp))
  have hd := (hasDerivAt_parameterMetricPartial hG ht hopen hA ⟨hTt, hz⟩ v).deriv
  change deriv (fun r => (G r).inner (A (r, z)) (V (r, z)) (V (r, z))) t = _ at hd
  rw [hpair.deriv_eq, hd]
  dsimp only
  change deriv (fun r => (G r).inner (A (t, z)) (V (t, z)) (V (t, z))) t +
      2 * (G t).inner (A (t, z))
        (sourceSectionCovariantDerivative (G t) (fun q => A (t, q)) W z v) (V (t, z)) = _
  rw [hVt, hAt]
  rw [sourceSectionCovariantDerivative_congr (G t) U hW v]
  rw [congrFun hAt z]




theorem diskMapMetricVariationDensity_pullback
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t : ℝ} (ht : D.regular ∈ 𝓝 t)
    {Φ : ℝ → M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M} {T : Set ℝ}
    (hT : IsOpen T) (hTt : t ∈ T)
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2) (T ×ˢ univ))
    (hΦt : Φ t = Diffeomorph.refl 𝓘(ℝ, E) M ∞)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) {z : ℂ} (hz : z ∈ s) :
    diskMapMetricVariationDensity (fun r => Diffeomorph.pullbackMetric (G r) (Φ r)) t U z =
      diskMapMetricVariationDensity G t U z + diskMapSectionDivergence (G t) U
        (fun q => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => Φ r (U q)) t 1) z := by
  unfold diskMapMetricVariationDensity diskMapSectionDivergence
  rw [deriv_isotopyPartialPairing hG ht hT hTt hΦ hΦt hs hU hz 1,
    deriv_isotopyPartialPairing hG ht hT hTt hΦ hΦt hs hU hz Complex.I]
  ring

end DifferentialGeometry.Geometry

end

section

noncomputable section
open Set Function Bundle Manifold
open scoped Topology ContDiff Bundle Manifold
namespace DifferentialGeometry.Geometry
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
theorem contMDiffOn_isotopyDiskVelocityWithin
    {Φ : ℝ → M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M} {T : Set ℝ}
    (hT : UniqueDiffOn ℝ T) {t : ℝ} (ht : t ∈ T)
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2) (T ×ˢ univ))
    (hΦt : Φ t = Diffeomorph.refl 𝓘(ℝ, E) M ∞)
    {U : ℂ → M} {s : Set ℂ}
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) :
    ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q => TotalSpace.mk' E (E := TangentSpace 𝓘(ℝ, E)) (U q)
        (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => Φ r (U q)) T t 1)) s := by
  have hp := ContMDiffOn.time_mfderivWithin (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
    (γ := fun r x => Φ r x) hΦ hT (m := ∞) (n := ∞) (by simp)
  have hc : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun q : ℂ => (t, U q)) s := contMDiffOn_const.prodMk hU
  apply (hp.comp hc (fun q _ => ⟨ht, mem_univ (U q)⟩)).congr
  intro q hq
  dsimp only [Function.comp_apply]
  have heq : Φ t (U q) = U q := by rw [hΦt]; rfl
  rw [heq]
  rfl
end DifferentialGeometry.Geometry

end

end

section

noncomputable section

open Set Function Bundle Manifold Filter DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
private theorem contMDiffOn_isotopyDisk_local
    {Φ : ℝ → M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M} {T : Set ℝ}
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2) (T ×ˢ univ))
    {U : ℂ → M} {s : Set ℂ} (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) ∞
      (fun p : ℝ × ℂ => Φ p.1 (U p.2)) (T ×ˢ s) := by
  have hmap : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℂ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × ℂ => (p.1, U p.2)) (T ×ˢ s) :=
    contMDiffOn_fst.prodMk (hU.comp contMDiffOn_snd (fun _ hp => hp.2))
  have h := hΦ.comp hmap (fun p hp => ⟨hp.1, mem_univ _⟩)
  rwa [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivWithinAt_isotopyPartialPairing_of_chart
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {Φ : ℝ → M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M} {T : Set ℝ}
    (hT : UniqueDiffOn ℝ T) (hTacc : T ⊆ closure (interior T)) {t : ℝ} (ht : t ∈ T)
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2) (T ×ˢ univ))
    (hΦt : Φ t = Diffeomorph.refl 𝓘(ℝ, E) M ∞)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) {z : ℂ} (hz : z ∈ s)
    (hchart : ∀ r ∈ T, ∀ q ∈ s, Φ r (U q) ∈ (chartAt E (U z)).source) (v : ℂ) :
    let V := fun r => mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q => Φ r (U q)) z v
    let W : ∀ q, TangentSpace 𝓘(ℝ, E) (U q) := fun q => mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => Φ r (U q)) T t 1
    HasDerivWithinAt (fun r => g.inner (Φ r (U z)) (V r) (V r))
      (2 * g.inner (U z) (sourceSectionCovariantDerivative g U W z v)
        (diskMapPartial U z v)) T t := by
  let A : ℝ × ℂ → M := fun p => Φ p.1 (U p.2)
  let F : ℝ → ℂ → E := fun r q => extChartAt 𝓘(ℝ, E) (U z) (A (r, q))
  let γ : ℝ → M := fun r => A (r, z)
  let V := fun r => mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q => A (r, q)) z v
  let W : ∀ q, TangentSpace 𝓘(ℝ, E) (U q) := fun q => mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => A (r, q)) T t 1
  have hA := contMDiffOn_isotopyDisk_local hΦ hU
  have hAt : ∀ q, A (t, q) = U q := by intro q; simp [A, hΦt]
  have hγt : γ t = U z := hAt z
  have hF : ContDiffOn ℝ ∞ (Function.uncurry F) (T ×ˢ s) := by
    intro p hp
    exact ((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (hchart p.1 hp.1 p.2 hp.2)).comp_contMDiffWithinAt
      p (hA p hp)).contDiffWithinAt
  have hγ : ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ T t := by
    exact (hA (t, z) ⟨ht, hz⟩).comp (f := fun r : ℝ => (r, z)) t
      ((contDiffWithinAt_id.prodMk contDiffWithinAt_const).contMDiffWithinAt)
      (fun r hr => ⟨hr, hz⟩)
  have hW : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q => TotalSpace.mk' E (U q) (W q)) s :=
    contMDiffOn_isotopyDiskVelocityWithin hT ht hΦ hΦt hU
  have hRepV : ∀ r ∈ T, chartRepAt γ V t r = fderiv ℝ (F r) z v := by
    intro r hr
    have hAr : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q => A (r, q)) s := by
      exact hA.comp (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffOn
        (fun q hq => ⟨hr, hq⟩)
    change (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (γ t)).continuousLinearMapAt ℝ (γ r) (V r) = _
    rw [hγt]
    exact congrArg (fun L => L v) (chartCoord_source_mfderiv
      (((hAr z hz).contMDiffAt (hs.mem_nhds hz)).mdifferentiableAt (by simp)) (U z)
      (hchart r hr z hz))
  let R : ℂ → E := fun q => (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (U z)).continuousLinearMapAt ℝ
    (U q) (W q)
  have hRepW : ∀ q ∈ s, R q = derivWithin (fun r => F r q) T t := by
    intro q hq
    have hAq : ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun r => A (r, q)) T t := by
      exact (hA (t, q) ⟨ht, hq⟩).comp (f := fun r : ℝ => (r, q)) t
        ((contDiffWithinAt_id.prodMk contDiffWithinAt_const).contMDiffWithinAt)
        (fun r hr => ⟨hr, hq⟩)
    have hh := TangentBundle.chartCoord_source_mfderivWithin (hT t ht)
      (hAq.mdifferentiableWithinAt (by simp)) (U z) (hchart t ht q hq)
    have he := congrArg (fun L => L (1 : ℝ)) hh
    change (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (U z)).continuousLinearMapAt ℝ
      (A (t, q)) (W q) = derivWithin (fun r => F r q) T t at he
    rw [hAt] at he
    exact he
  have hvdiff : DifferentiableWithinAt ℝ (fun r => fderiv ℝ (F r) z v) T t := by
    have hh := spatialFDeriv_contDiffOn hT hs hF
    have hc := (hh (t, z) ⟨ht, hz⟩).comp (f := fun r : ℝ => (r, z)) t
      (contDiffWithinAt_id.prodMk contDiffWithinAt_const) (fun r hr => ⟨hr, hz⟩)
    exact (hc.clm_apply contDiffWithinAt_const).differentiableWithinAt (by simp)
  have hmixed : derivWithin (fun r => fderiv ℝ (F r) z v) T t = fderiv ℝ R z v := by
    have he := fderiv_derivWithin_time_comm hT hTacc hs ht hz hF
    have hdiff : DifferentiableWithinAt ℝ (fun r => fderiv ℝ (F r) z) T t := by
      have hh := spatialFDeriv_contDiffOn hT hs hF
      exact ((hh (t, z) ⟨ht, hz⟩).comp (f := fun r : ℝ => (r, z)) t
        (contDiffWithinAt_id.prodMk contDiffWithinAt_const) (fun r hr => ⟨hr, hz⟩)).differentiableWithinAt (by simp)
    rw [hdiff.hasDerivWithinAt.clm_apply (hasDerivWithinAt_const t T v) |>.derivWithin (hT t ht)]
    rw [← he, (eventuallyEq_of_mem (hs.mem_nhds hz) hRepW).fderiv_eq]
    simp
  have hv : HasDerivWithinAt (chartRepAt γ V t) (fderiv ℝ R z v) T t := by
    rw [← hmixed]
    exact hvdiff.hasDerivWithinAt.congr_of_eventuallyEq
      (eventuallyEq_of_mem self_mem_nhdsWithin hRepV) (hRepV t ht)
  have hu : HasDerivWithinAt (chartCurve (I := 𝓘(ℝ, E)) (γ t) γ) (R z) T t := by
    have hc : ContDiffWithinAt ℝ ∞ (fun r => F r z) T t :=
      (hF (t, z) ⟨ht, hz⟩).comp (f := fun r : ℝ => (r, z)) t
        (contDiffWithinAt_id.prodMk contDiffWithinAt_const) (fun r hr => ⟨hr, hz⟩)
    rw [hRepW z hz]
    have hd := (hc.differentiableWithinAt (by simp)).hasDerivWithinAt
    rw [hγt]
    change HasDerivWithinAt (fun r => extChartAt 𝓘(ℝ, E) (U z) (A (r,z))) _ T t
    exact hd
  have hi := hasDerivWithinAt_inner_of_chart_derivatives g γ V V hγ.continuousWithinAt hu hv hv
  have hcov := sourceSectionCovariantDerivative_chart g hs hU hW hz v
  have hVt : V t = diskMapPartial U z v := by
    change (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q => A (t, q)) z v : E) = diskMapPartial U z v
    rw [show (fun q => A (t, q)) = U from funext hAt]
    rfl
  have hrepVt : chartRepAt γ V t t = fderiv ℝ ((extChartAt 𝓘(ℝ, E) (U z)) ∘ U) z v := by
    rw [hRepV t ht]
    congr 2
    funext q
    simp [F, hAt]
  have hcorr : (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (γ t)).symmL ℝ (γ t)
      (fderiv ℝ R z v + chartChristoffelContraction g (γ t) (R z)
        (chartRepAt γ V t t) (chartCurve (I := 𝓘(ℝ, E)) (γ t) γ t)) =
      sourceSectionCovariantDerivative g U W z v := by
    rw [hγt, hrepVt, chartChristoffelContraction_symm]
    have hcov' := congrArg ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) (U z)).symmL ℝ (U z)) hcov
    rw [(trivializationAt E (TangentSpace 𝓘(ℝ, E)) (U z)).symmL_continuousLinearMapAt
      (mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ, E)) (U z))] at hcov'
    simpa only [chartCurve_def, hγt, Function.comp_apply] using hcov'.symm
  dsimp only at hi
  rw [hcorr, hγt, hVt] at hi
  rw [g.symm (U z) (diskMapPartial U z v)] at hi
  convert hi using 1
  ring

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivWithinAt_isotopyPartialPairing
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {Φ : ℝ → M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M} {a b t : ℝ} (ht : t ∈ Ico a b)
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2) (Icc a b ×ˢ univ))
    (hΦt : Φ t = Diffeomorph.refl 𝓘(ℝ, E) M ∞)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) {z : ℂ} (hz : z ∈ s) (v : ℂ) :
    let V := fun r => mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q => Φ r (U q)) z v
    let W := fun q => mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => Φ r (U q)) (Icc a b) t 1
    HasDerivWithinAt (fun r => g.inner (Φ r (U z)) (V r) (V r))
      (2 * g.inner (U z) (sourceSectionCovariantDerivative g U W z v)
        (diskMapPartial U z v)) (Icc a b) t := by
  have htcc : t ∈ Icc a b := ⟨ht.1, ht.2.le⟩
  have hA := contMDiffOn_isotopyDisk_local hΦ hU
  have hchart : (chartAt E (U z)).source ∈ 𝓝 (Φ t (U z)) := by
    rw [hΦt]
    exact (chartAt E (U z)).open_source.mem_nhds (mem_chart_source E (U z))
  obtain ⟨c, d, hcd, ht', hneigh, hsub, S, hS, hzS, hSs, hmaps⟩ :=
    (hA (t, z) ⟨htcc, hz⟩).continuousWithinAt.exists_mapsTo_Icc_prod_open ht hs hz hchart
  have hacc : Icc c d ⊆ closure (interior (Icc c d)) := by
    rw [interior_Icc, closure_Ioo hcd.ne]
  have hΦ' := hΦ.mono (prod_mono hsub (Subset.refl univ))
  have hres := hasDerivWithinAt_isotopyPartialPairing_of_chart g (uniqueDiffOn_Icc hcd) hacc
    ht' hΦ' hΦt hS (hU.mono hSs) hzS (fun (r : ℝ) (hr : r ∈ Icc c d) (q : ℂ) (hq : q ∈ S) => hmaps (show (r,q) ∈ Icc c d ×ˢ S from ⟨hr,hq⟩)) v
  have heq : (fun q => mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => Φ r (U q)) (Icc c d) t 1) =
      (fun q => mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => Φ r (U q)) (Icc a b) t 1) := by
    funext q
    have hq : ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun r => Φ r (U q)) (Icc a b) t :=
      (hΦ (t, U q) ⟨htcc, mem_univ _⟩).comp (f := fun r => (r, U q)) t
        (contMDiffWithinAt_id.prodMk contMDiffWithinAt_const) (fun r hr => ⟨hr, mem_univ _⟩)
    exact congrArg (fun L => L 1) ((hq.mdifferentiableWithinAt (by simp)).mfderivWithin_mono
      ((uniqueDiffOn_Icc hcd t ht').uniqueMDiffWithinAt) hsub)
  dsimp only at hres ⊢
  rw [heq] at hres
  exact hres.mono_of_mem_nhdsWithin hneigh

end DifferentialGeometry.Geometry

end

end

section

noncomputable section

open Set Function Bundle Manifold Filter DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

set_option backward.isDefEq.respectTransparency false in
theorem derivWithin_isotopyPartialPairing
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t : ℝ} (ht : D.regular ∈ 𝓝 t)
    {a b : ℝ} (hab : a < b) (hIco : t ∈ Ico a b)
    {Φ : ℝ → M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M}
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2) (Icc a b ×ˢ univ))
    (hΦt : Φ t = Diffeomorph.refl 𝓘(ℝ, E) M ∞)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) {z : ℂ} (hz : z ∈ s) (v : ℂ) :
    derivWithin (fun r => (Diffeomorph.pullbackMetric (G r) (Φ r)).inner (U z)
      (diskMapPartial U z v) (diskMapPartial U z v)) (Icc a b) t =
      deriv (fun r => (G r).inner (U z) (diskMapPartial U z v) (diskMapPartial U z v)) t +
        2 * (G t).inner (U z)
          (sourceSectionCovariantDerivative (G t) U
            (fun q => mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => Φ r (U q)) (Icc a b) t 1) z v)
          (diskMapPartial U z v) := by
  let A : ℝ × ℂ → M := fun p => Φ p.1 (U p.2)
  let V := fun r => mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q => A (r, q)) z v
  have htcc : t ∈ Icc a b := ⟨hIco.1, hIco.2.le⟩
  have hT : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  have hA : ContMDiffOn 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) ∞ A (Icc a b ×ˢ s) := by
    have hmap : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℂ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
        (fun p : ℝ × ℂ => (p.1, U p.2)) (Icc a b ×ˢ s) :=
      contMDiffOn_fst.prodMk (hU.comp contMDiffOn_snd (fun _ hp => hp.2))
    have h := hΦ.comp hmap (fun p hp => ⟨hp.1, mem_univ _⟩)
    rwa [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
  have hγ : ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun r => A (r, z)) (Icc a b) t :=
    (hA (t,z) ⟨htcc,hz⟩).comp (f := fun r : ℝ => (r,z)) t
      ((contDiffWithinAt_id.prodMk contDiffWithinAt_const).contMDiffWithinAt)
      (fun r hr => ⟨hr,hz⟩)
  have hV : ContMDiffWithinAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun r => TotalSpace.mk' E (A (r, z)) (V r)) (Icc a b) t := by
    have hsp := contMDiffOn_source_spatialPartial hT hs hA v
    exact (hsp (t,z) ⟨htcc,hz⟩).comp (f := fun r : ℝ => (r,z)) t
      ((contDiffWithinAt_id.prodMk contDiffWithinAt_const).contMDiffWithinAt)
      (fun r hr => ⟨hr,hz⟩)
  have hm := derivWithin_metricFamilyPairing hG ht (hT t htcc) htcc hγ hV hV
  have hstatic := (hasDerivWithinAt_isotopyPartialPairing (G t) hIco hΦ hΦt hs hU hz v).derivWithin
    (hT t htcc)
  have hVt : V t = diskMapPartial U z v := by
    change (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q => A (t, q)) z v : E) = diskMapPartial U z v
    rw [show (fun q => A (t, q)) = U by funext q; simp [A,hΦt]]
    rfl
  have hAt : A (t, z) = U z := by simp [A,hΦt]
  have hUz := ((hU z hz).contMDiffAt (hs.mem_nhds hz)).mdifferentiableAt (by simp)
  have heq : (fun r => (Diffeomorph.pullbackMetric (G r) (Φ r)).inner (U z)
      (diskMapPartial U z v) (diskMapPartial U z v)) =
      (fun r => (G r).inner (A (r,z)) (V r) (V r)) := by
    funext r
    rw [Diffeomorph.pullbackMetric_inner]
    have hc := mfderiv_comp z ((Φ r).contMDiff.contMDiffAt.mdifferentiableAt (by simp)) hUz
    have hv : V r = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ r) (U z) (diskMapPartial U z v) := by
      change mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (Φ r ∘ U) z v = _
      rw [hc]
      rfl
    rw [hv]
  rw [heq, hm, hVt, hAt]
  exact congrArg (fun k => deriv (fun r => (G r).inner (U z)
    (diskMapPartial U z v) (diskMapPartial U z v)) t + k) hstatic

theorem diskMapMetricVariationWithinDensity_pullback
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t : ℝ} (ht : D.regular ∈ 𝓝 t)
    {a b : ℝ} (hab : a < b) (hIco : t ∈ Ico a b)
    {Φ : ℝ → M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M}
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2) (Icc a b ×ˢ univ))
    (hΦt : Φ t = Diffeomorph.refl 𝓘(ℝ, E) M ∞)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) {z : ℂ} (hz : z ∈ s) :
    diskMapMetricVariationWithinDensity (fun r => Diffeomorph.pullbackMetric (G r) (Φ r))
      (Icc a b) t U z = diskMapMetricVariationDensity G t U z + diskMapSectionDivergence (G t) U
        (fun q => mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => Φ r (U q)) (Icc a b) t 1) z := by
  unfold diskMapMetricVariationWithinDensity diskMapMetricVariationDensity diskMapSectionDivergence
  rw [derivWithin_isotopyPartialPairing hG ht hab hIco hΦ hΦt hs hU hz 1,
    derivWithin_isotopyPartialPairing hG ht hab hIco hΦ hΦt hs hU hz Complex.I]
  ring

end DifferentialGeometry.Geometry

end

end
