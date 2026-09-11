import DifferentialGeometry.Geometry.MinimalSurface.Variation.ParameterMetricDerivative
import DifferentialGeometry.Geometry.MinimalSurface.Variation.DiskDivergence
import DifferentialGeometry.Geometry.MinimalSurface.Variation.DiskIsotopyIntegral



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
