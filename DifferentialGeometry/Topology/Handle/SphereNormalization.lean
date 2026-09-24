import DifferentialGeometry.Topology.Handle.SphereEmbedding
import DifferentialGeometry.Topology.Manifold.BallNormalization
import DifferentialGeometry.Topology.Manifold.ChartSupportedExtension

open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Handle

open Set Metric

attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

private local instance (k : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (k + 1))) = k + 1) := ⟨by simp⟩

theorem exists_isotopy_eqOn_closedCell_sphere (m : ℕ)
    {r : ℝ} (hr : 0 < r)
    {u : ClosedCell (m + 1) →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1}
    (hu : Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ u) :
    ∃ (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1)
      (Q : EuclideanSpace ℝ (Fin (m + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))
      (H : ℝ → Diffeomorph (𝓡 (m + 1)) (𝓡 (m + 1))
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1)
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1) ∞),
      ContMDiff (𝓘(ℝ).prod (𝓡 (m + 1))) (𝓡 (m + 1)) ∞
        (fun q : ℝ × Metric.sphere
          (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1 => H q.1 q.2) ∧
      ContMDiff (𝓘(ℝ).prod (𝓡 (m + 1))) (𝓡 (m + 1)) ∞
        (fun q : ℝ × Metric.sphere
          (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1 => (H q.1).symm q.2) ∧
      H 0 = Diffeomorph.refl (𝓡 (m + 1)) _ ∞ ∧
      (∀ x : ClosedCell (m + 1),
        H 1 ((stereographic' (m + 1) p).symm (r • Q x.val)) = u x) ∧
      ∃ K, IsCompact K ∧ p ∉ K ∧
        ∀ t x, x ∉ K → H t x = x ∧ (H t).symm x = x := by
  obtain ⟨p, Φ, hsource, htarget, hΦu⟩ :=
    exists_partialDiffeomorph_extension_closedCell_sphere m hu
  let E := EuclideanSpace ℝ (Fin (m + 1))
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1
  let c := stereographic' (m + 1) p
  have hchart : chartAt E (-p) = c := by
    change stereographic' (m + 1) (-(-p)) = c
    rw [neg_neg]
  have hc : ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ c c.source := by
    rw [← hchart]
    exact contMDiffOn_chart
  have hci : ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ c.symm c.target := by
    rw [← hchart]
    exact contMDiffOn_chart_symm
  let e : PartialDiffeomorph (𝓡 (m + 1)) (𝓡 (m + 1)) S E ∞ :=
    { toPartialEquiv := c.toPartialEquiv
      open_source := c.open_source
      open_target := c.open_target
      contMDiffOn_toFun := hc
      contMDiffOn_invFun := hci }
  have hΦsource (x : E) : x ∈ Φ.source := by rw [hsource]; trivial
  have hΦc (x : E) : Φ x ∈ c.source := by
    have hx := Φ.map_source (hΦsource x)
    simpa only [htarget, stereographic'_source, c] using hx
  let T : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (Units.mk0 r⁻¹ (inv_ne_zero hr.ne'))
  have hT (x : E) : T x = r⁻¹ • x := rfl
  let φ := T.toDiffeomorph.toPartialDiffeomorph.trans (Φ.trans e)
  have hφsource : closedBall 0 r ⊆ φ.source := by
    intro x _
    exact ⟨mem_univ _, hΦsource (T x), hΦc (T x)⟩
  obtain ⟨Q, J, hJ, hJi, hJ0, hJ1, K, hK, _, hfix⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_isotopy_eqOn_closedBall_of_partialDiffeomorph
      φ hr hφsource isOpen_univ (subset_univ _) (subset_univ _)
      (fun _ _ => mem_univ _)
  obtain ⟨H, hH, hHi, hHformula, hHK, hHKsource, hHfix⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorph_extension_of_chart_family
      c (stereographic'_target p) hc hci J hJ hJi hK hfix
  have hHeq (t : ℝ) (x : E) : H t (c.symm x) = c.symm (J t x) := by
    rw [(hHformula t (c.symm x)).1]
    unfold DifferentialGeometry.Topology.Manifold.extendChartById
    rw [if_pos (c.map_target (by simp [c])), c.right_inv (by simp [c])]
  refine ⟨p, Q, H, hH, hHi, ?_, ?_, c.symm '' K, hHK, ?_, hHfix⟩
  · apply Diffeomorph.ext
    intro x
    rw [(hHformula 0 x).1]
    unfold DifferentialGeometry.Topology.Manifold.extendChartById
    by_cases hx : x ∈ c.source
    · rw [if_pos hx, hJ0]
      exact c.left_inv hx
    · rw [if_neg hx]
      rfl
  · intro x
    rw [hHeq]
    have hx : r • x.val ∈ closedBall (0 : E) r := by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      exact (mul_le_mul_of_nonneg_left x.property hr.le).trans (by simp)
    have heq := hJ1 (r • x.val) hx
    rw [map_smul] at heq
    rw [heq]
    change c.symm (c (Φ (T (r • x.val)))) = u x
    rw [c.left_inv (hΦc _), hT, smul_smul, inv_mul_cancel₀ hr.ne', one_smul, hΦu]
  · intro hp
    have h := hHKsource hp
    simp [c] at h

theorem exists_isotopy_image_closedCell_sphere (m : ℕ)
    {r : ℝ} (hr : 0 < r)
    {u : ClosedCell (m + 1) →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1}
    (hu : Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ u) :
    ∃ (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1)
      (H : ℝ → Diffeomorph (𝓡 (m + 1)) (𝓡 (m + 1))
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1)
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1) ∞),
      ContMDiff (𝓘(ℝ).prod (𝓡 (m + 1))) (𝓡 (m + 1)) ∞
        (fun q : ℝ × Metric.sphere
          (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1 => H q.1 q.2) ∧
      ContMDiff (𝓘(ℝ).prod (𝓡 (m + 1))) (𝓡 (m + 1)) ∞
        (fun q : ℝ × Metric.sphere
          (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1 => (H q.1).symm q.2) ∧
      H 0 = Diffeomorph.refl (𝓡 (m + 1)) _ ∞ ∧
      H 1 '' ((stereographic' (m + 1) p).symm '' closedBall 0 r) = range u ∧
      ∃ K, IsCompact K ∧ p ∉ K ∧
        ∀ t x, x ∉ K → H t x = x ∧ (H t).symm x = x := by
  obtain ⟨p, Q, H, hH, hHi, hH0, hH1, K, hK, hpK, hfix⟩ :=
    exists_isotopy_eqOn_closedCell_sphere m hr hu
  refine ⟨p, H, hH, hHi, hH0, ?_, K, hK, hpK, hfix⟩
  ext y
  constructor
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    have hnorm : ‖r⁻¹ • Q.symm w‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), Q.symm.norm_map]
      rw [inv_mul_le_iff₀ hr]
      simpa only [mul_one] using mem_closedBall_zero_iff.mp hw
    let x : ClosedCell (m + 1) := ⟨r⁻¹ • Q.symm w, hnorm⟩
    refine ⟨x, ?_⟩
    have hx : r • Q x.val = w := by
      simp [x, map_smul, smul_smul, hr.ne']
    rw [← hH1 x, hx]
  · rintro ⟨x, rfl⟩
    refine ⟨(stereographic' (m + 1) p).symm (r • Q x.val), ?_, hH1 x⟩
    refine ⟨r • Q x.val, ?_, rfl⟩
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr, Q.norm_map]
    exact (mul_le_mul_of_nonneg_left x.property hr.le).trans (by simp)

end DifferentialGeometry.Topology.Handle
