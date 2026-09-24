import DifferentialGeometry.Topology.Handle.AttachingDisk
import DifferentialGeometry.Topology.Handle.SphereEmbedding
import DifferentialGeometry.Topology.Diffeomorph.SphereGerm
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.SphereLocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph

open Set Metric
open scoped ContDiff Manifold

namespace PartialDiffeomorph

variable (m : ℕ)

private local instance :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m + 1) + 1))) = (m + 1) + 1) := ⟨by simp⟩

private theorem exists_diffeomorph_eqOn_of_boundary_disk_charts
    (F : PartialDiffeomorph (𝓡 ((m + 1) + 1)) (𝓡 ((m + 1) + 1))
      (EuclideanSpace ℝ (Fin ((m + 1) + 1)))
      (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ∞)
    (φ₀ φ₁ : PartialDiffeomorph (𝓡 (m + 1)) (𝓡 (m + 1))
      (EuclideanSpace ℝ (Fin (m + 1)))
      (sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1) ∞)
    {R : ℝ} (hR : 0 < R) (hφ₀ : closedBall 0 R ⊆ φ₀.source)
    (hφ₁ : closedBall 0 R ⊆ φ₁.source)
    (hF : ∀ x ∈ closedBall 0 R, (φ₀ x).val ∈ F.source)
    (heq : ∀ x ∈ closedBall 0 R, F (φ₀ x).val = (φ₁ x).val)
    (hside : MapsTo F (closedBall 0 1 ∩ F.source) (closedBall 0 1))
    {K : Set (EuclideanSpace ℝ (Fin ((m + 1) + 1)))} (hK : IsCompact K)
    (hKφ : K ⊆ Subtype.val '' (φ₀ '' ball 0 R)) :
    ∃ Q : (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ≃ₘ[ℝ]
        (EuclideanSpace ℝ (Fin ((m + 1) + 1))),
      Q '' closedBall 0 1 = closedBall 0 1 ∧
      ∃ V, IsOpen V ∧ K ⊆ V ∧ V ⊆ F.source ∧ EqOn Q F V := by
  let E := EuclideanSpace ℝ (Fin (m + 1))
  let A := EuclideanSpace ℝ (Fin ((m + 1) + 1))
  let S := sphere (0 : A) 1
  obtain ⟨C, hCnorm, hC⟩ :=
    DifferentialGeometry.Topology.Handle.exists_diffeomorph_closedCell_sphere_product_collar m
      (DifferentialGeometry.Topology.Handle.isSmoothEmbedding_scaled_closedCell_sphere_chart m φ₀ hR hφ₀)
      (DifferentialGeometry.Topology.Handle.isSmoothEmbedding_scaled_closedCell_sphere_chart m φ₁ hR hφ₁)
  have hCeq (x : E) (hx : x ∈ closedBall 0 R) : C (φ₀ x).val = F (φ₀ x).val := by
    let y : DifferentialGeometry.Topology.ClosedCell (m + 1) :=
      ⟨R⁻¹ • x, by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
        rw [inv_mul_le_iff₀ hR, mul_one]
        exact mem_closedBall_zero_iff.mp hx⟩
    have hy : R • y.val = x := by
      change R • (R⁻¹ • x) = x
      rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
    have h := hC y 1 (by constructor <;> norm_num)
    simpa only [one_smul, hy, heq x hx] using h
  have hpatch : IsOpen (φ₀ '' ball (0 : E) R) :=
    φ₀.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_ball
      (ball_subset_closedBall.trans hφ₀)
  obtain ⟨W, hW, hWS⟩ := _root_.Topology.IsInducing.subtypeVal.isOpen_iff.mp hpatch
  let G := DifferentialGeometry.Topology.PartialDiffeomorph.restrict
    (F.trans C.symm.toPartialDiffeomorph) W hW
  have hGs : G.source = F.source ∩ W := by
    ext z
    change ((z ∈ F.source ∧ F z ∈ (univ : Set A)) ∧ z ∈ W) ↔ _
    simp only [mem_univ, and_true, mem_inter_iff]
  have hG (z : A) : G z = C.symm (F z) := rfl
  have hfixed : EqOn G id (sphere (0 : A) 1 ∩ G.source) := by
    intro z hz
    change G z = z
    have hzW : z ∈ W := (hGs ▸ hz.2).2
    have hzpatch : (⟨z, hz.1⟩ : S) ∈ φ₀ '' ball 0 R := by
      rw [← hWS]
      exact hzW
    obtain ⟨x, hx, hxeq⟩ := hzpatch
    have he : (φ₀ x).val = z := congrArg Subtype.val hxeq
    rw [hG, ← he, ← hCeq x (ball_subset_closedBall hx), C.symm_apply_apply]
  have hKG : K ⊆ sphere (0 : A) 1 ∩ G.source := by
    intro z hz
    obtain ⟨p, ⟨x, hx, hxp⟩, hpz⟩ := hKφ hz
    have he : (φ₀ x).val = z := (congrArg Subtype.val hxp).trans hpz
    refine ⟨hpz ▸ p.property, ?_⟩
    rw [hGs]
    refine ⟨he ▸ hF x (ball_subset_closedBall hx), ?_⟩
    have hpW : p ∈ Subtype.val ⁻¹' W := by
      rw [hWS]
      exact ⟨x, hx, hxp⟩
    exact hpz ▸ hpW
  have hGside : MapsTo G (closedBall 0 1 ∩ G.source) (closedBall 0 1) := by
    intro z hz
    rw [mem_closedBall_zero_iff, hG, (hCnorm (F z)).2]
    exact mem_closedBall_zero_iff.mp (hside ⟨hz.1, (hGs ▸ hz.2).1⟩)
  obtain ⟨V, hV, hKV, hVG, Φ, _, _, _, hΦ, _, hΦball, _⟩ :=
    G.exists_contDiff_compact_isotopy_eqOn_neighborhood_of_eqOn_sphere
      (by norm_num : (0 : ℝ) < 1) hfixed hK hKG hGside isOpen_univ (subset_univ K)
  let Q := (Φ 1).trans C
  refine ⟨Q, ?_, V, hV, hKV, fun x hx => (hGs ▸ hVG hx).1, ?_⟩
  · change (C ∘ Φ 1) '' closedBall 0 1 = closedBall 0 1
    rw [image_comp]
    rw [hΦball 1 ⟨zero_le_one, le_rfl⟩]
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [mem_closedBall_zero_iff, (hCnorm x).1]
      exact mem_closedBall_zero_iff.mp hx
    · intro hz
      refine ⟨C.symm z, ?_, C.apply_symm_apply z⟩
      rw [mem_closedBall_zero_iff, (hCnorm z).2]
      exact mem_closedBall_zero_iff.mp hz
  · intro x hx
    change C (Φ 1 x) = F x
    rw [hΦ hx, hG, C.apply_symm_apply]

private theorem exists_partialDiffeomorph_sphere_chart_comp
    (F : PartialDiffeomorph (𝓡 ((m + 1) + 1)) (𝓡 ((m + 1) + 1))
      (EuclideanSpace ℝ (Fin ((m + 1) + 1)))
      (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ∞)
    (φ : PartialDiffeomorph (𝓡 (m + 1)) (𝓡 (m + 1))
      (EuclideanSpace ℝ (Fin (m + 1)))
      (sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1) ∞)
    (hboundary : MapsTo F (sphere 0 1 ∩ F.source) (sphere 0 1))
    (hne : (φ.source ∩ (fun x => (φ x).val) ⁻¹' F.source).Nonempty) :
    ∃ ψ : PartialDiffeomorph (𝓡 (m + 1)) (𝓡 (m + 1))
      (EuclideanSpace ℝ (Fin (m + 1)))
      (sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1) ∞,
      ψ.source = φ.source ∩ (fun x => (φ x).val) ⁻¹' F.source ∧
      ∀ x ∈ ψ.source, (ψ x).val = F (φ x).val := by
  let E := EuclideanSpace ℝ (Fin (m + 1))
  let A := EuclideanSpace ℝ (Fin ((m + 1) + 1))
  let c : E → A := fun x => (φ x).val
  let U : Set E := φ.source ∩ c ⁻¹' F.source
  have hcoe := (isSmoothEmbedding_coe_sphere (E := A) (n := m + 1))
  have hc : ContDiffOn ℝ ∞ c φ.source :=
    (hcoe.contMDiff.comp_contMDiffOn φ.contMDiffOn).contDiffOn
  have hU : IsOpen U := hc.continuousOn.isOpen_inter_preimage φ.open_source F.open_source
  let f : E → A := F ∘ c
  have hf : ContDiffOn ℝ ∞ f U :=
    F.contMDiffOn.contDiffOn.comp (hc.mono inter_subset_left) (fun _ hx => hx.2)
  have hnorm (x : E) (hx : x ∈ U) : ‖f x‖ = 1 :=
    mem_sphere_zero_iff_norm.mp (hboundary ⟨(φ x).property, hx.2⟩)
  have hcder (x : E) (hx : x ∈ U) : Function.Injective (fderiv ℝ c x) := by
    have hi : Function.Injective (mfderiv (𝓡 (m + 1)) (𝓡 ((m + 1) + 1)) c x) := by
      change Function.Injective (mfderiv (𝓡 (m + 1)) (𝓡 ((m + 1) + 1)) (Subtype.val ∘ φ) x)
      rw [mfderiv_comp x (hcoe.contMDiff.mdifferentiableAt (by simp))
        ((φ.contMDiffOn.contMDiffAt (φ.open_source.mem_nhds hx.1)).mdifferentiableAt (by simp))]
      exact ((hcoe.isImmersion.isImmersionAt (φ x)).injective_mfderiv (by simp)).comp
        ((φ.isLocalDiffeomorphAt _ _ _ hx.1).mfderivToContinuousLinearEquiv (by simp)).injective
    simp only [mfderiv_eq_fderiv, TangentSpace] at hi
    convert! hi using 1
  have hd (x : E) (hx : x ∈ U) : Function.Injective (fderiv ℝ f x) := by
    rw [show f = F ∘ c from rfl, fderiv_comp x
      ((F.contMDiffOn.contDiffOn.contDiffAt (F.open_source.mem_nhds hx.2)).differentiableAt (by simp))
      ((hc.contDiffAt (φ.open_source.mem_nhds hx.1)).differentiableAt (by simp))]
    exact (DifferentialGeometry.Analysis.bijective_fderiv_of_partialDiffeomorph F hx.2).injective.comp
      (hcder x hx)
  let g := DifferentialGeometry.Topology.Manifold.sphereDirection (φ 0) ∘ f
  have hg := DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphOn_sphereDirection_comp_of_norm_eq_one
    (n := m + 1) (φ 0) hU hf hnorm hd (by simp [E])
  have heq (x : E) (hx : x ∈ U) : (g x : A) = f x := by
    change (DifferentialGeometry.Topology.Manifold.sphereDirection (φ 0) (f x) : A) = f x
    rw [DifferentialGeometry.Topology.Manifold.coe_sphereDirection (φ 0)
      (norm_ne_zero_iff.mp ((hnorm x hx).trans_ne one_ne_zero)), hnorm x hx, inv_one, one_smul]
  have hinj : InjOn g U := by
    intro x hx y hy hxy
    apply φ.injOn hx.1 hy.1
    apply Subtype.ext
    apply F.injOn hx.2 hy.2
    exact (heq x hx).symm.trans ((congrArg Subtype.val hxy).trans (heq y hy))
  obtain ⟨ψ, hψs, _, hψ⟩ :=
    DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn hg hU hne hinj
  refine ⟨ψ, hψs, ?_⟩
  intro x hx
  change (ψ.toFun x).val = _
  rw [hψ]
  exact heq x (hψs ▸ hx)

theorem exists_diffeomorph_eqOn_of_boundary_disk_chart
    (F : PartialDiffeomorph (𝓡 ((m + 1) + 1)) (𝓡 ((m + 1) + 1))
      (EuclideanSpace ℝ (Fin ((m + 1) + 1)))
      (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ∞)
    (φ : PartialDiffeomorph (𝓡 (m + 1)) (𝓡 (m + 1))
      (EuclideanSpace ℝ (Fin (m + 1)))
      (sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1) ∞)
    {R : ℝ} (hR : 0 < R) (hφ : closedBall 0 R ⊆ φ.source)
    (hF : ∀ x ∈ closedBall 0 R, (φ x).val ∈ F.source)
    (hboundary : MapsTo F (sphere 0 1 ∩ F.source) (sphere 0 1))
    (hside : MapsTo F (closedBall 0 1 ∩ F.source) (closedBall 0 1))
    {K : Set (EuclideanSpace ℝ (Fin ((m + 1) + 1)))} (hK : IsCompact K)
    (hKφ : K ⊆ Subtype.val '' (φ '' ball 0 R)) :
    ∃ Q : (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ≃ₘ[ℝ]
        (EuclideanSpace ℝ (Fin ((m + 1) + 1))),
      Q '' closedBall 0 1 = closedBall 0 1 ∧
      ∃ V, IsOpen V ∧ K ⊆ V ∧ V ⊆ F.source ∧ EqOn Q F V := by
  have hzero : (0 : EuclideanSpace ℝ (Fin (m + 1))) ∈ closedBall 0 R :=
    mem_closedBall_self hR.le
  obtain ⟨ψ, hψs, hψ⟩ := exists_partialDiffeomorph_sphere_chart_comp m F φ hboundary
    ⟨0, hφ hzero, hF 0 hzero⟩
  have hψR : closedBall 0 R ⊆ ψ.source := by
    rw [hψs]
    exact fun x hx => ⟨hφ hx, hF x hx⟩
  exact exists_diffeomorph_eqOn_of_boundary_disk_charts m F φ ψ hR hφ hψR hF
    (fun x hx => (hψ x (hψR hx)).symm) hside hK hKφ

end PartialDiffeomorph
