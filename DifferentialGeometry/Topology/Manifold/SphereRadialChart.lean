import DifferentialGeometry.Topology.Manifold.SphereDirection
import Mathlib.Geometry.Manifold.LocalDiffeomorph

noncomputable section
open Set Metric Manifold Module
open scoped ContDiff

namespace DifferentialGeometry.Topology.Manifold

theorem exists_smooth_radial_chart
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} [Fact (finrank ℝ E = n + 1)]
    (e : OpenPartialHomeomorph (sphere (0 : E) 1) F) (htarget : e.target = univ)
    (he : ContMDiffOn (𝓡 n) 𝓘(ℝ, F) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, F) (𝓡 n) ∞ e.symm e.target) :
    ∃ c : PartialDiffeomorph 𝓘(ℝ, ℝ × F) 𝓘(ℝ, E) (ℝ × F) E ∞,
      c.source = Ioi 0 ×ˢ univ ∧
      (∀ q : ℝ × F, c q = q.1 • (e.symm q.2 : E)) ∧
      c.target = {x | x ≠ 0 ∧ sphereDirection (e.symm 0) x ∈ e.source} ∧
      ∀ x : E, c.symm x = (‖x‖, e (sphereDirection (e.symm 0) x)) := by
  let v := e.symm 0
  let S : Set (ℝ × F) := Ioi 0 ×ˢ univ
  let T : Set E := {x | x ≠ 0 ∧ sphereDirection v x ∈ e.source}
  have hd := contMDiffOn_sphereDirection (n := n) v
  have hT : IsOpen T :=
    hd.continuousOn.isOpen_inter_preimage isOpen_compl_singleton e.open_source
  have hi : ContMDiff 𝓘(ℝ, F) (𝓡 n) ∞ e.symm := contMDiffOn_univ.mp (htarget ▸ hei)
  have hfor : ContDiff ℝ ∞ (fun q : ℝ × F ↦ q.1 • (e.symm q.2 : E)) :=
    (contDiff_fst.contMDiff.smul
      (contMDiff_coe_sphere.comp (hi.comp contDiff_snd.contMDiff))).contDiff
  have hnorm : ContDiffOn ℝ ∞ (fun x : E ↦ ‖x‖) T := fun x hx ↦
    (contDiffAt_norm ℝ hx.1).contDiffWithinAt
  have hchart : ContDiffOn ℝ ∞ (fun x : E ↦ e (sphereDirection v x)) T :=
    (he.comp (hd.mono (fun _ hx ↦ hx.1)) (fun _ hx ↦ hx.2)).contDiffOn
  let c : PartialDiffeomorph 𝓘(ℝ, ℝ × F) 𝓘(ℝ, E) (ℝ × F) E ∞ :=
    { toFun := fun q ↦ q.1 • (e.symm q.2 : E)
      invFun := fun x ↦ (‖x‖, e (sphereDirection v x))
      source := S
      target := T
      map_source' := by
        intro q hq
        refine ⟨smul_ne_zero hq.1.ne' (ne_zero_of_mem_unit_sphere (e.symm q.2)), ?_⟩
        rw [sphereDirection_pos_smul v (e.symm q.2) hq.1]
        exact e.map_target (htarget ▸ mem_univ _)
      map_target' := by
        intro x hx
        exact ⟨norm_pos_iff.mpr hx.1, mem_univ _⟩
      left_inv' := by
        intro q hq
        apply Prod.ext
        · simp [norm_smul, norm_eq_of_mem_sphere, abs_of_pos (show 0 < q.1 from hq.1)]
        · rw [sphereDirection_pos_smul v (e.symm q.2) hq.1,
            e.right_inv (htarget ▸ mem_univ _)]
      right_inv' := by
        intro x hx
        rw [e.left_inv hx.2]
        exact norm_smul_sphereDirection v hx.1
      open_source := isOpen_Ioi.prod isOpen_univ
      open_target := hT
      contMDiffOn_toFun := hfor.contDiffOn.contMDiffOn
      contMDiffOn_invFun := (hnorm.prodMk hchart).contMDiffOn }
  exact ⟨c, rfl, fun _ ↦ rfl, rfl, fun _ ↦ rfl⟩

end DifferentialGeometry.Topology.Manifold
