import DifferentialGeometry.Topology.Manifold.SphereRadialDiffeomorph

noncomputable section
open Set Metric Manifold Module
open scoped ContDiff

namespace DifferentialGeometry.Topology.Manifold

theorem det_fderiv_sphereRadialExtension_pos_of_isotopy
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} [Fact (finrank ℝ E = n + 1)]
    (D : ℝ → Diffeomorph (𝓡 n) (𝓡 n) (sphere (0 : E) 1) (sphere (0 : E) 1) ∞)
    (hD : ContMDiff (𝓘(ℝ).prod (𝓡 n)) (𝓡 n) ∞
      (fun q : ℝ × sphere (0 : E) 1 ↦ D q.1 q.2))
    (hzero : D 0 = Diffeomorph.refl (𝓡 n) _ ∞) (p : ℝ) {x : E} (hx : x ≠ 0) :
    0 < (fderiv ℝ (sphereRadialExtension (D p)) x).toLinearMap.det := by
  let F : ℝ × E → E := fun q ↦ sphereRadialExtension (D q.1) q.2
  let U : Set (ℝ × E) := {q | q.2 ≠ 0}
  have hU : IsOpen U := isOpen_compl_singleton.preimage continuous_snd
  have hF : ContDiffOn ℝ ∞ F U :=
    contDiffOn_sphereRadialExtension_family (n := n) (fun t ↦ (D t : _ → _)) hD
  have hder (t : ℝ) : fderiv ℝ (sphereRadialExtension (D t)) x =
      (fderiv ℝ F (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
    have hd := ((hF.contDiffAt (hU.mem_nhds (show (t, x) ∈ U from hx))).differentiableAt
      (by simp)).hasFDerivAt
    exact (hd.comp x ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))).fderiv
  have hcF : Continuous (fun t : ℝ ↦ fderiv ℝ F (t, x)) :=
    (hF.continuousOn_fderiv_of_isOpen hU (by simp)).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ ↦ hx)
  let d : ℝ → ℝ := fun t ↦ (fderiv ℝ (sphereRadialExtension (D t)) x).toLinearMap.det
  have hd : Continuous d := by
    have heq : d = fun t ↦ ((fderiv ℝ F (t, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ E)).toLinearMap.det := funext (fun t ↦ by rw [← hder])
    rw [heq]
    exact ContinuousLinearMap.continuous_det.comp (hcF.clm_comp continuous_const)
  have hd0 : d 0 = 1 := by
    change (fderiv ℝ (sphereRadialExtension (D 0)) x).toLinearMap.det = 1
    rw [hzero]
    change (fderiv ℝ (sphereRadialExtension id) x).toLinearMap.det = 1
    rw [sphereRadialExtension_id]
    simp
  change 0 < d p
  by_contra hp
  obtain ⟨t, ht⟩ := intermediate_value_univ p 0 hd
    (show (0 : ℝ) ∈ Icc (d p) (d 0) from ⟨le_of_not_gt hp, by rw [hd0]; exact zero_le_one⟩)
  exact det_fderiv_sphereRadialExtension_ne_zero (D t) hx ht

end DifferentialGeometry.Topology.Manifold
