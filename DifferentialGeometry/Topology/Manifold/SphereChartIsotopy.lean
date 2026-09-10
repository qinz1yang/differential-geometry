import DifferentialGeometry.Topology.Manifold.SphereFixedPointIsotopy
import DifferentialGeometry.Analysis.ODE.Flow.Planar.CompactPointMotion
import DifferentialGeometry.Analysis.ODE.Flow.Planar.PlanarIsotopyJacobian

noncomputable section
open Set Metric Filter Topology Manifold
open scoped ContDiff

namespace Poincare.Topology.Manifold

theorem exists_sphere_isotopy_of_positive_chart_derivative
    (e : OpenPartialHomeomorph (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ℂ)
    (htarget : e.target = univ)
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 2) ∞ e.symm e.target)
    (f : Diffeomorph (𝓡 2) (𝓡 2)
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)
    (v : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hv : v ∈ e.source) (hev : e v = 0) (hfv : f v ∈ e.source)
    (hpos : 0 < (fderiv ℝ (fun z ↦ e (f (e.symm z))) 0).toLinearMap.det) :
    ∃ J : ℝ → Diffeomorph (𝓡 2) (𝓡 2)
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞,
      ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun q : ℝ × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ J q.1 q.2) ∧
      ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun q : ℝ × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (J q.1).symm q.2) ∧
      J 0 = f ∧ J 1 = Diffeomorph.refl (𝓡 2) _ ∞ := by
  have hiv : e.symm 0 = v := by rw [← hev]; exact e.left_inv hv
  have hi : ContMDiff 𝓘(ℝ, ℂ) (𝓡 2) ∞ e.symm := contMDiffOn_univ.mp (htarget ▸ hei)
  obtain ⟨D, hD, hDi, hD0, hmove, K, hK, hDfix⟩ :=
    Poincare.Analysis.exists_compact_isotopy_moving_point (e (f v)) (0 : ℂ)
  obtain ⟨B, hB, hBi, hBe, _, _, _⟩ :=
    exists_diffeomorph_extension_of_chart_family e htarget he hei D hD hDi hK hDfix
  have hB0 : B 0 = Diffeomorph.refl (𝓡 2) _ ∞ := by
    apply Diffeomorph.ext
    intro x
    rw [(hBe 0 x).1, hD0]
    change extendChartById e (id : ℂ → ℂ) x = x
    by_cases hx : x ∈ e.source
    · exact (show extendChartById e id x = e.symm (e x) from if_pos hx).trans (e.left_inv hx)
    · exact if_neg hx
  let g := f.trans (B 1)
  have hgv : g v = v := by
    change B 1 (f v) = v
    rw [(hBe 1 (f v)).1]
    have hx : extendChartById e (D 1) (f v) = e.symm (D 1 (e (f v))) := if_pos hfv
    rw [hx, hmove, hiv]
  let F : ℂ → ℂ := fun z ↦ e (f (e.symm z))
  let G : ℂ → ℂ := fun z ↦ e (g (e.symm z))
  let U : Set ℂ := (fun z ↦ f (e.symm z)) ⁻¹' e.source
  have hU : IsOpen U := e.open_source.preimage (f.continuous.comp hi.continuous)
  have h0U : (0 : ℂ) ∈ U := by
    change f (e.symm 0) ∈ e.source
    simpa only [hiv] using hfv
  have hF : ContDiffOn ℝ ∞ F U :=
    (he.comp (f.contMDiff.comp hi).contMDiffOn (fun _ hz ↦ hz)).contDiffOn
  have hGeq : G =ᶠ[𝓝 0] (D 1) ∘ F := by
    filter_upwards [hU.mem_nhds h0U] with z hz
    change e (B 1 (f (e.symm z))) = D 1 (F z)
    rw [(hBe 1 (f (e.symm z))).1]
    have hx : extendChartById e (D 1) (f (e.symm z)) =
        e.symm (D 1 (e (f (e.symm z)))) := if_pos hz
    rw [hx, e.right_inv (htarget ▸ mem_univ _)]
  have hGpos : 0 < (fderiv ℝ G 0).toLinearMap.det := by
    have hFA := ((hF.contDiffAt (hU.mem_nhds h0U)).differentiableAt (by simp)).hasFDerivAt
    have hDA := ((D 1).contMDiff.contDiff.differentiable (by simp) (F 0)).hasFDerivAt
    have hGA := (hDA.comp 0 hFA).congr_of_eventuallyEq hGeq
    rw [hGA.fderiv]
    change 0 < ((fderiv ℝ (D 1) (F 0)).toLinearMap.comp
      (fderiv ℝ F 0).toLinearMap).det
    rw [LinearMap.det_comp]
    exact mul_pos (Poincare.Analysis.det_fderiv_pos_of_planar_isotopy D hD hD0 1 (F 0)) hpos
  obtain ⟨H, hH, hHi, hH0, hH1⟩ :=
    exists_sphere_isotopy_of_positive_fixed_point_chart e htarget he hei g v hv hev hgv hGpos
  let J (p : ℝ) := (H p).trans (B (1 - p)).symm
  have ht : ContMDiff (𝓘(ℝ).prod (𝓡 2)) 𝓘(ℝ) ∞
      (fun q : ℝ × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ 1 - q.1) :=
    contMDiff_const.sub contMDiff_fst
  have hJ : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun q : ℝ × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ J q.1 q.2) :=
    hBi.comp (ht.prodMk hH)
  have hJi : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun q : ℝ × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (J q.1).symm q.2) :=
    hHi.comp (contMDiff_fst.prodMk (hB.comp (ht.prodMk contMDiff_snd)))
  refine ⟨J, hJ, hJi, ?_, ?_⟩
  · apply Diffeomorph.ext
    intro x
    change (B (1 - 0)).symm (H 0 x) = f x
    rw [sub_zero, hH0]
    exact (B 1).symm_apply_apply (f x)
  · apply Diffeomorph.ext
    intro x
    change (B (1 - 1)).symm (H 1 x) = x
    rw [sub_self, hB0, hH1]
    rfl

end Poincare.Topology.Manifold
