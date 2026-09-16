import DifferentialGeometry.Analysis.InnerProductSpace.EllipsoidNeighborhood
import DifferentialGeometry.Topology.Manifold.ManifoldIsotopyExtension
import DifferentialGeometry.Topology.Manifold.NormalChartOrientation
import DifferentialGeometry.Analysis.Calculus.Derivative.Coordinates.JacobianSign

open Set Metric
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Manifold

theorem exists_isotopy_eqOn_disk_collar_of_partialDiffeomorphs {n : ℕ}
    (φ₀ φ₁ : PartialDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1))
      (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin (n + 1))) ∞)
    {r : ℝ} (hr : 0 ≤ r)
    (h₀ : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ r →
      (EuclideanSpace.equivProdLast n).symm (x, 0) ∈ φ₀.source)
    (h₁ : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ r →
      (EuclideanSpace.equivProdLast n).symm (x, 0) ∈ φ₁.source)
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hV : IsOpen V)
    (hV₀ : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ r →
      φ₀ ((EuclideanSpace.equivProdLast n).symm (x, 0)) ∈ V)
    (hV₁ : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ r →
      φ₁ ((EuclideanSpace.equivProdLast n).symm (x, 0)) ∈ V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, (1 - t) • φ₀ 0 + t • φ₁ 0 ∈ V)
    (hori : 0 < (fderiv ℝ φ₀ 0).det * (fderiv ℝ φ₁ 0).det) :
    ∃ (δ : ℝ), 0 < δ ∧
      ∃ J : ℝ → Diffeomorph (𝓡 (n + 1)) (𝓡 (n + 1))
          (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin (n + 1))) ∞,
        ContDiff ℝ ∞ (fun q : ℝ × EuclideanSpace ℝ (Fin (n + 1)) => J q.1 q.2) ∧
        ContDiff ℝ ∞ (fun q : ℝ × EuclideanSpace ℝ (Fin (n + 1)) => (J q.1).symm q.2) ∧
        J 0 = Diffeomorph.refl (𝓡 (n + 1)) (EuclideanSpace ℝ (Fin (n + 1))) ∞ ∧
        (∀ (x : EuclideanSpace ℝ (Fin n)) (s : ℝ), ‖x‖ ≤ r + δ → |s| ≤ δ →
          let p := (EuclideanSpace.equivProdLast n).symm (x, s)
          p ∈ φ₀.source ∧ p ∈ φ₁.source ∧ J 1 (φ₀ p) = φ₁ p) ∧
        ∃ K : Set (EuclideanSpace ℝ (Fin (n + 1))), IsCompact K ∧ K ⊆ V ∧
          ∀ t y, y ∉ K → J t y = y ∧ (J t).symm y = y := by
  let E := EuclideanSpace ℝ (Fin (n + 1))
  let W := (φ₀.source ∩ φ₀ ⁻¹' V) ∩ (φ₁.source ∩ φ₁ ⁻¹' V)
  have hW : IsOpen W :=
    (φ₀.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage φ₀.open_source hV).inter
      (φ₁.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage φ₁.open_source hV)
  obtain ⟨A, δ, hδ, hAW, hstrip⟩ :=
    EuclideanSpace.exists_linearEquiv_image_closedBall_subset_of_disk_subset hr hW
      (fun x hx => ⟨⟨h₀ x hx, hV₀ x hx⟩, ⟨h₁ x hx, hV₁ x hx⟩⟩)
  let σ := A.toDiffeomorph.toPartialDiffeomorph
  have hσ (z : E) : σ z = A z := rfl
  have hsrc₀ : closedBall (0 : E) 1 ⊆ (σ.trans φ₀).source := by
    intro z hz
    exact ⟨mem_univ _, (hAW ⟨z, hz, rfl⟩).1.1⟩
  have hsrc₁ : closedBall (0 : E) 1 ⊆ (σ.trans φ₁).source := by
    intro z hz
    exact ⟨mem_univ _, (hAW ⟨z, hz, rfl⟩).2.1⟩
  have hφ₀diff : DifferentiableAt ℝ (φ₀ : E → E) 0 := by
    apply (φ₀.contMDiffOn_toFun.contDiffOn.contDiffAt
      (φ₀.open_source.mem_nhds ?_)).differentiableAt (by simp)
    simpa only [Prod.mk_zero_zero, map_zero] using h₀ 0 (by simpa using hr)
  have hφ₁diff : DifferentiableAt ℝ (φ₁ : E → E) 0 := by
    apply (φ₁.contMDiffOn_toFun.contDiffOn.contDiffAt
      (φ₁.open_source.mem_nhds ?_)).differentiableAt (by simp)
    simpa only [Prod.mk_zero_zero, map_zero] using h₁ 0 (by simpa using hr)
  have hchain (φ : PartialDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) E E ∞)
      (hφ : DifferentiableAt ℝ (φ : E → E) 0) :
      (fderiv ℝ (σ.trans φ) 0).det = (fderiv ℝ φ 0).det * A.toContinuousLinearMap.det := by
    have hcomp : (σ.trans φ : E → E) = (φ : E → E) ∘ A := rfl
    rw [hcomp, fderiv_comp 0 (by simpa only [map_zero] using hφ) A.differentiableAt,
      A.hasFDerivAt.fderiv, map_zero]
    exact LinearMap.det_comp (fderiv ℝ φ 0).toLinearMap A.toLinearEquiv.toLinearMap
  have hdetA : 0 < A.toContinuousLinearMap.det ^ 2 :=
    sq_pos_of_ne_zero A.toLinearEquiv.isUnit_det'.ne_zero
  have hori' : 0 < (fderiv ℝ (σ.trans φ₀) 0).det *
      (fderiv ℝ (σ.trans φ₁) 0).det := by
    rw [hchain φ₀ hφ₀diff, hchain φ₁ hφ₁diff]
    nlinarith [mul_pos hori hdetA]
  obtain ⟨J, hJ, hJi, hJ0, hJ1, K, hK, hKV, hfix⟩ :=
    exists_isotopy_eqOn_closedBall_of_partialDiffeomorphs_of_subset_of_radius
      (σ.trans φ₀) (σ.trans φ₁) (by norm_num : (0 : ℝ) < 1) hsrc₀ hsrc₁ hV
      (by rintro y ⟨z, hz, rfl⟩; exact (hAW ⟨z, hz, rfl⟩).1.2)
      (by rintro y ⟨z, hz, rfl⟩; exact (hAW ⟨z, hz, rfl⟩).2.2)
      (by simpa only [PartialDiffeomorph.trans_apply, hσ, map_zero] using hseg) hori'
  refine ⟨δ, hδ, J, hJ, hJi, hJ0, ?_, K, hK, hKV, hfix⟩
  intro x s hx hs
  obtain ⟨z, hz, hzp⟩ := hstrip x s hx hs
  have hp := hAW ⟨z, hz, hzp⟩
  refine ⟨hp.1.1, hp.2.1, ?_⟩
  simpa only [PartialDiffeomorph.trans_apply, hσ, hzp] using hJ1 z hz

theorem exists_diffeomorph_eqOn_disk_collar_of_eqOn_disk {n : ℕ}
    (φ₀ φ₁ : PartialDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1))
      (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin (n + 1))) ∞)
    {r : ℝ} (hr : 0 ≤ r)
    (h₀ : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ r →
      (EuclideanSpace.equivProdLast n).symm (x, 0) ∈ φ₀.source)
    (h₁ : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ r →
      (EuclideanSpace.equivProdLast n).symm (x, 0) ∈ φ₁.source)
    (heq : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ r →
      φ₀ ((EuclideanSpace.equivProdLast n).symm (x, 0)) =
        φ₁ ((EuclideanSpace.equivProdLast n).symm (x, 0)))
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hV : IsOpen V)
    (hV₀ : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ r →
      φ₀ ((EuclideanSpace.equivProdLast n).symm (x, 0)) ∈ V)
    (hori : 0 < (fderiv ℝ φ₀ 0).det * (fderiv ℝ φ₁ 0).det) :
    ∃ (δ : ℝ), 0 < δ ∧
      ∃ D : Diffeomorph (𝓡 (n + 1)) (𝓡 (n + 1))
          (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin (n + 1))) ∞,
        (∀ (x : EuclideanSpace ℝ (Fin n)) (s : ℝ), ‖x‖ ≤ r + δ → |s| ≤ δ →
          let p := (EuclideanSpace.equivProdLast n).symm (x, s)
          p ∈ φ₀.source ∧ p ∈ φ₁.source ∧ D (φ₀ p) = φ₁ p) ∧
        (∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ r →
          D (φ₀ ((EuclideanSpace.equivProdLast n).symm (x, 0))) =
            φ₀ ((EuclideanSpace.equivProdLast n).symm (x, 0))) ∧
        ∃ K : Set (EuclideanSpace ℝ (Fin (n + 1))), IsCompact K ∧ K ⊆ V ∧
          ∀ y, y ∉ K → D y = y ∧ D.symm y = y := by
  have hcenter : φ₀ 0 = φ₁ 0 := by
    simpa only [Prod.mk_zero_zero, map_zero] using heq 0 (by simpa using hr)
  obtain ⟨δ, hδ, J, _, _, _, hmatch, K, hK, hKV, hfix⟩ :=
    exists_isotopy_eqOn_disk_collar_of_partialDiffeomorphs φ₀ φ₁ hr h₀ h₁ hV hV₀
      (fun x hx => heq x hx ▸ hV₀ x hx)
      (by
        intro t _
        rw [← hcenter, ← add_smul, sub_add_cancel, one_smul]
        simpa only [Prod.mk_zero_zero, map_zero] using hV₀ 0 (by simpa using hr)) hori
  refine ⟨δ, hδ, J 1, hmatch, ?_, K, hK, hKV, hfix 1⟩
  intro x hx
  exact ((hmatch x 0 (hx.trans (le_add_of_nonneg_right hδ.le))
    (by simpa using hδ.le)).2.2).trans (heq x hx).symm

theorem exists_diffeomorph_eqOn_disk_collar_of_hasNormalSideFlipAt {n : ℕ}
    (φ₀ φ₁ : PartialDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1))
      (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin (n + 1))) ∞)
    {r : ℝ} (hr : 0 < r)
    (h₀ : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ r →
      (EuclideanSpace.equivProdLast n).symm (x, 0) ∈ φ₀.source)
    (h₁ : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ r →
      (EuclideanSpace.equivProdLast n).symm (x, 0) ∈ φ₁.source)
    (heq : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ r →
      φ₀ ((EuclideanSpace.equivProdLast n).symm (x, 0)) =
        φ₁ ((EuclideanSpace.equivProdLast n).symm (x, 0)))
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hV : IsOpen V)
    (hV₀ : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ r →
      φ₀ ((EuclideanSpace.equivProdLast n).symm (x, 0)) ∈ V)
    (hside : let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) n
      HasNormalSideFlipAt
        ((((L.symm.toDiffeomorph.toPartialDiffeomorph.trans φ₀).trans φ₁.symm).trans
          L.toDiffeomorph.toPartialDiffeomorph).toOpenPartialHomeomorph) 0 false) :
    ∃ (δ : ℝ), 0 < δ ∧
      ∃ D : Diffeomorph (𝓡 (n + 1)) (𝓡 (n + 1))
          (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin (n + 1))) ∞,
        (∀ (x : EuclideanSpace ℝ (Fin n)) (s : ℝ), ‖x‖ ≤ r + δ → |s| ≤ δ →
          let p := (EuclideanSpace.equivProdLast n).symm (x, s)
          p ∈ φ₀.source ∧ p ∈ φ₁.source ∧ D (φ₀ p) = φ₁ p) ∧
        (∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ r →
          D (φ₀ ((EuclideanSpace.equivProdLast n).symm (x, 0))) =
            φ₀ ((EuclideanSpace.equivProdLast n).symm (x, 0))) ∧
        ∃ K : Set (EuclideanSpace ℝ (Fin (n + 1))), IsCompact K ∧ K ⊆ V ∧
          ∀ y, y ∉ K → D y = y ∧ D.symm y = y := by
  apply exists_diffeomorph_eqOn_disk_collar_of_eqOn_disk φ₀ φ₁ hr.le h₀ h₁ heq hV hV₀
  apply det_fderiv_mul_pos_of_hasNormalSideFlipAt (EuclideanSpace.equivProdLast n) φ₀ φ₁
  · simpa only [Prod.mk_zero_zero, map_zero] using h₀ 0 (by simpa using hr.le)
  · simpa only [Prod.mk_zero_zero, map_zero] using h₁ 0 (by simpa using hr.le)
  · filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin n)) hr] with x hx
    exact heq x (mem_ball_zero_iff.mp hx).le
  · exact hside

theorem exists_diffeomorph_eqOn_disk_collar_up_to_normal_sign {n : ℕ}
    (φ₀ φ₁ : PartialDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1))
      (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin (n + 1))) ∞)
    {r : ℝ} (hr : 0 ≤ r)
    (h₀ : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ r →
      (EuclideanSpace.equivProdLast n).symm (x, 0) ∈ φ₀.source)
    (h₁ : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ r →
      (EuclideanSpace.equivProdLast n).symm (x, 0) ∈ φ₁.source)
    (heq : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ r →
      φ₀ ((EuclideanSpace.equivProdLast n).symm (x, 0)) =
        φ₁ ((EuclideanSpace.equivProdLast n).symm (x, 0)))
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hV : IsOpen V)
    (hV₀ : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ r →
      φ₀ ((EuclideanSpace.equivProdLast n).symm (x, 0)) ∈ V) :
    ∃ (δ σ : ℝ), 0 < δ ∧ |σ| = 1 ∧
      ∃ D : (EuclideanSpace ℝ (Fin (n + 1))) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin (n + 1)),
        (∀ (x : EuclideanSpace ℝ (Fin n)) (s : ℝ), ‖x‖ ≤ r + δ → |s| ≤ δ →
          (EuclideanSpace.equivProdLast n).symm (x, s) ∈ φ₀.source ∧
          (EuclideanSpace.equivProdLast n).symm (x, σ * s) ∈ φ₁.source ∧
          D (φ₀ ((EuclideanSpace.equivProdLast n).symm (x, s))) =
            φ₁ ((EuclideanSpace.equivProdLast n).symm (x, σ * s))) ∧
        (∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ r →
          D (φ₀ ((EuclideanSpace.equivProdLast n).symm (x, 0))) =
            φ₀ ((EuclideanSpace.equivProdLast n).symm (x, 0))) ∧
        ∃ K : Set (EuclideanSpace ℝ (Fin (n + 1))), IsCompact K ∧ K ⊆ V ∧
          ∀ y, y ∉ K → D y = y ∧ D.symm y = y := by
  by_cases hpos : 0 < (fderiv ℝ φ₀ 0).det * (fderiv ℝ φ₁ 0).det
  · obtain ⟨δ, hδ, D, hD, hfix, K, hK, hKV, houtside⟩ :=
      exists_diffeomorph_eqOn_disk_collar_of_eqOn_disk φ₀ φ₁ hr h₀ h₁ heq hV hV₀ hpos
    refine ⟨δ, 1, hδ, by norm_num, D, ?_, hfix, K, hK, hKV, houtside⟩
    simpa only [one_mul] using hD
  · let E := EuclideanSpace ℝ (Fin (n + 1))
    let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) n
    let Q := (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))).prodCongr
      (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ)
    let R : E ≃L[ℝ] E := (L.trans Q).trans L.symm
    have hR (x : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
        R (L.symm (x, s)) = L.symm (x, -s) := by
      change L.symm (Q (L (L.symm (x, s)))) = _
      rw [L.apply_symm_apply]
      rfl
    have hdetR : R.toContinuousLinearMap.det = -1 := by
      have hc := LinearMap.det_conj Q.toLinearMap L.symm.toLinearEquiv
      change R.toContinuousLinearMap.det = Q.toContinuousLinearMap.det at hc
      rw [hc]
      change LinearMap.det ((LinearMap.id : (EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] _).prodMap
        (-LinearMap.id : ℝ →ₗ[ℝ] ℝ)) = -1
      rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul]
      rw [show (-LinearMap.id : ℝ →ₗ[ℝ] ℝ) = (-1 : ℝ) • LinearMap.id by simp]
      simp
    let ψ := R.toDiffeomorph.toPartialDiffeomorph.trans φ₁
    have hψ (q : E) : ψ q = φ₁ (R q) := rfl
    have hψsrc (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ r) :
        L.symm (x, 0) ∈ ψ.source := by
      refine ⟨mem_univ _, ?_⟩
      change R (L.symm (x, 0)) ∈ φ₁.source
      simpa only [hR, neg_zero] using h₁ x hx
    have hψeq (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ r) :
        φ₀ (L.symm (x, 0)) = ψ (L.symm (x, 0)) := by
      rw [hψ, hR, neg_zero]
      exact heq x hx
    have hzero₀ : (0 : E) ∈ φ₀.source := by
      simpa only [Prod.mk_zero_zero, map_zero] using h₀ 0 (by simpa using hr)
    have hzero₁ : (0 : E) ∈ φ₁.source := by
      simpa only [Prod.mk_zero_zero, map_zero] using h₁ 0 (by simpa using hr)
    have hne : (fderiv ℝ φ₀ 0).det * (fderiv ℝ φ₁ 0).det ≠ 0 :=
      mul_ne_zero (DifferentialGeometry.Analysis.det_fderiv_ne_zero_of_partialDiffeomorph φ₀ hzero₀)
        (DifferentialGeometry.Analysis.det_fderiv_ne_zero_of_partialDiffeomorph φ₁ hzero₁)
    have hneg : (fderiv ℝ φ₀ 0).det * (fderiv ℝ φ₁ 0).det < 0 :=
      lt_of_le_of_ne (le_of_not_gt hpos) hne
    have hdφ₁ : DifferentiableAt ℝ (φ₁ : E → E) 0 :=
      (φ₁.contMDiffOn_toFun.contDiffOn.contDiffAt
        (φ₁.open_source.mem_nhds hzero₁)).differentiableAt (by simp)
    have hdetψ : (fderiv ℝ ψ 0).det = -(fderiv ℝ φ₁ 0).det := by
      have hcomp : (ψ : E → E) = (φ₁ : E → E) ∘ R := rfl
      rw [hcomp, fderiv_comp 0 (by simpa only [map_zero] using hdφ₁) R.differentiableAt,
        R.hasFDerivAt.fderiv, map_zero]
      rw [show ((fderiv ℝ φ₁ 0).comp R.toContinuousLinearMap).det =
          (fderiv ℝ φ₁ 0).det * R.toContinuousLinearMap.det from LinearMap.det_comp _ _, hdetR]
      ring
    obtain ⟨δ, hδ, D, hD, hfix, K, hK, hKV, houtside⟩ :=
      exists_diffeomorph_eqOn_disk_collar_of_eqOn_disk φ₀ ψ hr h₀ hψsrc hψeq hV hV₀
        (by rw [hdetψ]; nlinarith)
    refine ⟨δ, -1, hδ, by norm_num, D, ?_, hfix, K, hK, hKV, houtside⟩
    intro x s hx hs
    obtain ⟨hx₀, hx₁, hmatch⟩ := hD x s hx hs
    refine ⟨hx₀, ?_, ?_⟩
    · have hmem := hx₁.2
      change R (L.symm (x, s)) ∈ φ₁.source at hmem
      simpa only [hR, neg_one_mul] using hmem
    · change D (φ₀ (L.symm (x, s))) = φ₁ (R (L.symm (x, s))) at hmatch
      rw [hR] at hmatch
      simpa only [neg_one_mul] using hmatch

end DifferentialGeometry.Topology.Manifold
