import DifferentialGeometry.Topology.Handle.SphereNormalization
import DifferentialGeometry.Topology.Diffeomorph.SphereIsotopy
import DifferentialGeometry.Analysis.InnerProductSpace.EuclideanSplit
import DifferentialGeometry.Topology.Manifold.SphereRadialChart
import DifferentialGeometry.Topology.Manifold.StereographicHemisphere

open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Handle

open Set Metric

attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

private local instance (k : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (k + 1))) = k + 1) := ⟨by simp⟩

theorem exists_isotopy_image_closedCell_sphere_product_collar (m : ℕ)
    {r : ℝ} (hr : 0 < r)
    {u : ClosedCell (m + 1) →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1}
    (hu : Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ u) :
    ∃ (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1)
      (F : ℝ → (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ≃ₘ[ℝ]
        (EuclideanSpace ℝ (Fin ((m + 1) + 1)))),
      ContDiff ℝ ∞ (fun q : ℝ × EuclideanSpace ℝ (Fin ((m + 1) + 1)) => F q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × EuclideanSpace ℝ (Fin ((m + 1) + 1)) =>
        (F q.1).symm q.2) ∧
      F 0 = Diffeomorph.refl (𝓡 ((m + 1) + 1)) _ ∞ ∧
      (∀ t x, ‖F t x‖ = ‖x‖ ∧ ‖(F t).symm x‖ = ‖x‖) ∧
      (∀ t x, ‖x‖ ≤ 1 / 4 ∨ 2 ≤ ‖x‖ → F t x = x ∧ (F t).symm x = x) ∧
      ∀ s ∈ Icc (1 / 2 : ℝ) (3 / 2),
        F 1 '' ((fun θ : Metric.sphere
          (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1 => s • θ.val) ''
            ((stereographic' (m + 1) p).symm '' closedBall 0 r)) =
          range (fun x => s • (u x).val) := by
  obtain ⟨p, H, hH, hHi, hH0, hHimage, _⟩ :=
    exists_isotopy_image_closedCell_sphere m hr hu
  obtain ⟨F, hF, hFi, hF0, hnorm, hfix, hcollar, _⟩ :=
    Diffeomorph.exists_isotopy_extension_sphere_product_collar H hH hHi hH0
  refine ⟨p, F, hF, hFi, hF0, hnorm, hfix, ?_⟩
  intro s hs
  let a := fun θ : Metric.sphere
    (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1 => s • θ.val
  calc
    F 1 '' (a '' ((stereographic' (m + 1) p).symm '' closedBall 0 r)) =
        a '' (H 1 '' ((stereographic' (m + 1) p).symm '' closedBall 0 r)) := by
      simp only [image_image]
      exact image_congr (fun x _ =>
        (hcollar 1 ((stereographic' (m + 1) p).symm x) s hs).1)
    _ = a '' range u := by rw [hHimage]
    _ = range (fun x => s • (u x).val) := by rw [← range_comp]; rfl

theorem exists_partialDiffeomorph_closedCell_sphere_collar (m : ℕ)
    {u : ClosedCell (m + 1) →
      sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1}
    (hu : Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ u) :
    ∃ Φ : PartialDiffeomorph (𝓡 ((m + 1) + 1)) (𝓡 ((m + 1) + 1))
        (EuclideanSpace ℝ (Fin ((m + 1) + 1)))
        (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ∞,
      Φ.source = {q | -1 < (EuclideanSpace.equivProdLast (m + 1) q).2} ∧
      ∀ (x : ClosedCell (m + 1)) (s : ℝ),
        Φ ((EuclideanSpace.equivProdLast (m + 1)).symm (x.val, s)) =
          (1 + s) • (u x).val := by
  let E := EuclideanSpace ℝ (Fin ((m + 1) + 1))
  let F := EuclideanSpace ℝ (Fin (m + 1))
  let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) (m + 1)
  obtain ⟨_, ψ, hψs, _, hψ⟩ := exists_partialDiffeomorph_extension_closedCell_sphere m hu
  obtain ⟨c, hcs, hc, _, _⟩ := Manifold.exists_smooth_radial_chart
    ψ.symm.toOpenPartialHomeomorph hψs ψ.contMDiffOn_invFun ψ.contMDiffOn_toFun
  let Q : Diffeomorph (𝓡 ((m + 1) + 1)) 𝓘(ℝ, ℝ × F) E (ℝ × F) ∞ :=
    { toEquiv :=
        { toFun := fun q => (1 + (L q).2, (L q).1)
          invFun := fun q => L.symm (q.2, q.1 - 1)
          left_inv := by intro q; simp
          right_inv := by intro q; simp
        }
      contMDiff_toFun :=
        ((contDiff_const.add L.contDiff.snd).prodMk L.contDiff.fst).contMDiff
      contMDiff_invFun :=
        (L.symm.contDiff.comp (contDiff_snd.prodMk (contDiff_fst.sub contDiff_const))).contMDiff }
  refine ⟨Q.toPartialDiffeomorph.trans c, ?_, ?_⟩
  · ext q
    rw [PartialDiffeomorph.trans_source, hcs]
    change q ∈ univ ∩ Q ⁻¹' (Ioi 0 ×ˢ univ) ↔ -1 < (L q).2
    simp only [mem_inter_iff, mem_univ, mem_preimage, mem_prod, mem_Ioi, and_true,
      true_and]
    change 0 < 1 + (L q).2 ↔ -1 < (L q).2
    constructor <;> intro h <;> linarith
  · intro x s
    rw [PartialDiffeomorph.trans_apply, hc]
    change (1 + (L (L.symm (x.val, s))).2) •
      (ψ (L (L.symm (x.val, s))).1).val = _
    simp only [ContinuousLinearEquiv.apply_symm_apply, hψ]

theorem exists_partialDiffeomorph_closedCell_boundary_collar (m : ℕ)
    {b : ClosedCell ((m + 1) + 1) → EuclideanSpace ℝ (Fin ((m + 1) + 1))}
    (hb : Manifold.IsSmoothEmbedding (𝓡∂ ((m + 1) + 1)) (𝓡 ((m + 1) + 1)) ∞ b)
    {u : ClosedCell (m + 1) →
      sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1}
    (hu : Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ u) :
    ∃ (D : (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ≃ₘ[ℝ]
        EuclideanSpace ℝ (Fin ((m + 1) + 1)))
      (Φ : PartialDiffeomorph (𝓡 ((m + 1) + 1)) (𝓡 ((m + 1) + 1))
        (EuclideanSpace ℝ (Fin ((m + 1) + 1)))
        (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ∞),
      (∀ z : ClosedCell ((m + 1) + 1), D z.val = b z) ∧
      Φ.source = {q | -1 < (EuclideanSpace.equivProdLast (m + 1) q).2} ∧
      ∀ (x : ClosedCell (m + 1)) (s : ℝ),
        Φ ((EuclideanSpace.equivProdLast (m + 1)).symm (x.val, s)) =
          D ((1 + s) • (u x).val) := by
  obtain ⟨D, hD⟩ := exists_diffeomorph_extension_closedCell (m + 1) hb
  obtain ⟨ψ, hψs, hψ⟩ := exists_partialDiffeomorph_closedCell_sphere_collar m hu
  refine ⟨D, ψ.trans D.toPartialDiffeomorph, hD, ?_, ?_⟩
  · rw [PartialDiffeomorph.trans_source]
    change ψ.source ∩ ψ ⁻¹' univ = _
    simpa only [preimage_univ, inter_univ] using hψs
  · intro x s
    change D (ψ ((EuclideanSpace.equivProdLast (m + 1)).symm (x.val, s))) = _
    rw [hψ]

private theorem exists_diffeomorph_sphericalCap_product_collar (m : ℕ)
    {u : ClosedCell (m + 1) →
      sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1}
    (hu : Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ u) :
    ∃ D : (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ≃ₘ[ℝ]
        EuclideanSpace ℝ (Fin ((m + 1) + 1)),
      (∀ z, ‖D z‖ = ‖z‖) ∧
      ∀ (x : ClosedCell (m + 1)) (s : ℝ), s ∈ Icc (1 / 2 : ℝ) (3 / 2) →
        D (s • (EuclideanSpace.equivProdLast (m + 1)).symm
          (EuclideanGeometry.sphericalCap (-1) x.val)) = s • (u x).val := by
  let E := EuclideanSpace ℝ (Fin ((m + 1) + 1))
  let F := EuclideanSpace ℝ (Fin (m + 1))
  let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) (m + 1)
  obtain ⟨p, Q, H, hH, hHi, hH0, hH1, _⟩ :=
    exists_isotopy_eqOn_closedCell_sphere m (r := 2) (by norm_num) hu
  obtain ⟨N, _, _, _, hnorm, _, hcollar, _⟩ :=
    Diffeomorph.exists_isotopy_extension_sphere_product_collar H hH hHi hH0
  let R := Q.toContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  let B : E ≃L[ℝ] E := (L.trans R).trans (sphereChartEquiv p)
  have hBnorm (z : E) : ‖B z‖ = ‖z‖ := by
    have h₀ := sphereChartEquiv_norm_sq p (R (L z))
    have h₁ := EuclideanSpace.norm_sq_equivProdLast (𝕜 := ℝ) (m + 1) z
    change ‖B z‖ ^ 2 = ‖Q (L z).1‖ ^ 2 + (L z).2 ^ 2 at h₀
    change ‖z‖ ^ 2 = ‖(L z).1‖ ^ 2 + ‖(L z).2‖ ^ 2 at h₁
    rw [Q.norm_map] at h₀
    rw [Real.norm_eq_abs, sq_abs] at h₁
    nlinarith [norm_nonneg (B z), norm_nonneg z]
  have hBcap (x : F) :
      B (L.symm (EuclideanGeometry.sphericalCap (-1) x)) =
        ((stereographic' (m + 1) p).symm ((2 : ℝ) • Q x)).val := by
    change sphereChartEquiv p (R (L (L.symm (EuclideanGeometry.sphericalCap (-1) x)))) = _
    rw [L.apply_symm_apply]
    have hR : R (EuclideanGeometry.sphericalCap (-1) x) =
        EuclideanGeometry.sphericalCap (-1) (Q x) := by
      ext <;> simp [R, EuclideanGeometry.sphericalCap, EuclideanGeometry.sphericalCapHeight,
        Q.norm_map, map_smul]
    rw [hR, sphereChartEquiv_sphericalCap_neg_one]
  refine ⟨B.toDiffeomorph.trans (N 1), fun z => (hnorm 1 (B z)).1.trans (hBnorm z), ?_⟩
  intro x s hs
  change N 1 (B (s • L.symm (EuclideanGeometry.sphericalCap (-1) x.val))) = _
  rw [B.map_smul, hBcap, (hcollar 1 _ s hs).1]
  exact congrArg (fun θ : sphere (0 : E) 1 => s • θ.val) (hH1 x)

theorem exists_diffeomorph_closedCell_sphere_product_collar (m : ℕ)
    {u v : ClosedCell (m + 1) →
      sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1}
    (hu : Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ u)
    (hv : Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ v) :
    ∃ D : (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ≃ₘ[ℝ]
        EuclideanSpace ℝ (Fin ((m + 1) + 1)),
      (∀ z, ‖D z‖ = ‖z‖ ∧ ‖D.symm z‖ = ‖z‖) ∧
      ∀ (x : ClosedCell (m + 1)) (s : ℝ), s ∈ Icc (1 / 2 : ℝ) (3 / 2) →
        D (s • (u x).val) = s • (v x).val := by
  obtain ⟨A, hAnorm, hA⟩ := exists_diffeomorph_sphericalCap_product_collar m hu
  obtain ⟨B, hBnorm, hB⟩ := exists_diffeomorph_sphericalCap_product_collar m hv
  refine ⟨A.symm.trans B, ?_, ?_⟩
  · intro z
    constructor
    · change ‖B (A.symm z)‖ = ‖z‖
      rw [hBnorm, ← hAnorm (A.symm z), A.apply_symm_apply]
    · change ‖A (B.symm z)‖ = ‖z‖
      rw [hAnorm, ← hBnorm (B.symm z), B.apply_symm_apply]
  · intro x s hs
    change B (A.symm (s • (u x).val)) = s • (v x).val
    rw [← hA x s hs, A.symm_apply_apply, hB x s hs]

theorem exists_diffeomorph_closedCell_boundary_product_collar (m : ℕ)
    {b₀ b₁ : ClosedCell ((m + 1) + 1) → EuclideanSpace ℝ (Fin ((m + 1) + 1))}
    (hb₀ : Manifold.IsSmoothEmbedding (𝓡∂ ((m + 1) + 1)) (𝓡 ((m + 1) + 1)) ∞ b₀)
    (hb₁ : Manifold.IsSmoothEmbedding (𝓡∂ ((m + 1) + 1)) (𝓡 ((m + 1) + 1)) ∞ b₁)
    {u₀ u₁ : ClosedCell (m + 1) →
      sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1}
    (hu₀ : Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ u₀)
    (hu₁ : Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ u₁) :
    ∃ A₀ A₁ D : (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ≃ₘ[ℝ]
        EuclideanSpace ℝ (Fin ((m + 1) + 1)),
      (∀ x : ClosedCell ((m + 1) + 1), A₀ x.val = b₀ x) ∧
      (∀ x : ClosedCell ((m + 1) + 1), A₁ x.val = b₁ x) ∧
      D '' range b₀ = range b₁ ∧
      ∀ (x : ClosedCell (m + 1)) (s : ℝ), s ∈ Icc (1 / 2 : ℝ) (3 / 2) →
        D (A₀ (s • (u₀ x).val)) = A₁ (s • (u₁ x).val) := by
  let E := EuclideanSpace ℝ (Fin ((m + 1) + 1))
  obtain ⟨A₀, hA₀⟩ := exists_diffeomorph_extension_closedCell (m + 1) hb₀
  obtain ⟨A₁, hA₁⟩ := exists_diffeomorph_extension_closedCell (m + 1) hb₁
  obtain ⟨C, hCnorm, hC⟩ := exists_diffeomorph_closedCell_sphere_product_collar m hu₀ hu₁
  let D := (A₀.symm.trans C).trans A₁
  have hD (z : E) : D (A₀ z) = A₁ (C z) := by
    change A₁ (C (A₀.symm (A₀ z))) = _
    rw [A₀.symm_apply_apply]
  refine ⟨A₀, A₁, D, hA₀, hA₁, ?_, ?_⟩
  · ext z
    constructor
    · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
      let w : ClosedCell ((m + 1) + 1) := ⟨C x.val, (hCnorm x.val).1 ▸ x.property⟩
      refine ⟨w, ?_⟩
      rw [← hA₀ x, hD, ← hA₁ w]
    · rintro ⟨x, rfl⟩
      let w : ClosedCell ((m + 1) + 1) :=
        ⟨C.symm x.val, (hCnorm x.val).2 ▸ x.property⟩
      refine ⟨b₀ w, mem_range_self w, ?_⟩
      rw [← hA₀ w, hD, ← hA₁ x]
      exact congrArg A₁ (C.apply_symm_apply x.val)
  · intro x s hs
    rw [hD, hC x s hs]

end DifferentialGeometry.Topology.Handle
