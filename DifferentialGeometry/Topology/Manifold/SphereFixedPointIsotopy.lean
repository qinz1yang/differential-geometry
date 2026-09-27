import DifferentialGeometry.Topology.Manifold.PlanarChartGermIsotopy
import DifferentialGeometry.Topology.Manifold.SphereRelativeIsotopy

noncomputable section
open Set Metric Filter Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Topology.Manifold

theorem exists_sphere_isotopy_of_positive_fixed_point_chart
    (e : OpenPartialHomeomorph (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ℂ)
    (htarget : e.target = univ)
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 2) ∞ e.symm e.target)
    (f : Diffeomorph (𝓡 2) (𝓡 2)
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)
    (v : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hv : v ∈ e.source) (hev : e v = 0) (hfv : f v = v)
    (hpos : 0 < (fderiv ℝ (fun z ↦ e (f (e.symm z))) 0).toLinearMap.det) :
    ∃ J : ℝ → Diffeomorph (𝓡 2) (𝓡 2)
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞,
      ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun q : ℝ × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ J q.1 q.2) ∧
      ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun q : ℝ × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (J q.1).symm q.2) ∧
      J 0 = f ∧ J 1 = Diffeomorph.refl (𝓡 2) _ ∞ := by
  obtain ⟨B, hB, hBi, hB0, hBg, _⟩ :=
    exists_isotopy_realizing_positive_chart_germ e htarget he hei f v hv hev hfv hpos
  let g := f.trans (B 1).symm
  have hg : (g : _ → _) =ᶠ[𝓝 v] id := by
    filter_upwards [hBg] with x hx
    change (B 1).symm (f x) = x
    rw [← hx, (B 1).symm_apply_apply]
  obtain ⟨H, hH, hHi, hH0, hH1, _⟩ := exists_sphere_isotopy_of_identity_near_point g v hg
  let J (p : ℝ) := (H p).trans (B (1 - p))
  have ht : ContMDiff (𝓘(ℝ).prod (𝓡 2)) 𝓘(ℝ) ∞
      (fun q : ℝ × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ 1 - q.1) :=
    contMDiff_const.sub contMDiff_fst
  have hJ : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun q : ℝ × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ J q.1 q.2) :=
    hB.comp (ht.prodMk hH)
  have hJi : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun q : ℝ × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (J q.1).symm q.2) :=
    hHi.comp (contMDiff_fst.prodMk (hBi.comp (ht.prodMk contMDiff_snd)))
  refine ⟨J, hJ, hJi, ?_, ?_⟩
  · apply Diffeomorph.ext
    intro x
    change B (1 - 0) (H 0 x) = f x
    rw [sub_zero, hH0]
    exact (B 1).apply_symm_apply (f x)
  · apply Diffeomorph.ext
    intro x
    change B (1 - 1) (H 1 x) = x
    rw [sub_self, hB0, hH1]
    rfl

end DifferentialGeometry.Topology.Manifold
