import DifferentialGeometry.Topology.Handle.Embedding
import DifferentialGeometry.Topology.Diffeomorph.SphereIsotopy

open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Handle

attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

private noncomputable def restrictClosedCell {m : ℕ}
    (F : EuclideanSpace ℝ (Fin (m + 1)) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))
    (hF : ∀ x, ‖F x‖ = ‖x‖) :
    Diffeomorph (𝓡∂ (m + 1)) (𝓡∂ (m + 1)) (ClosedCell (m + 1))
      (ClosedCell (m + 1)) ∞ := by
  let e : ClosedCell (m + 1) ≃ ClosedCell (m + 1) :=
    F.toEquiv.subtypeEquiv (fun x => by change ‖x‖ ≤ 1 ↔ ‖F x‖ ≤ 1; rw [hF x])
  refine { toEquiv := e, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · apply (ContMDiff.iff_comp_isImmersion
      (closedCellInclusion_isSmoothEmbedding m).isImmersion).mpr
    exact ⟨(F.continuous.comp continuous_subtype_val).subtype_mk _,
      F.contMDiff.comp (closedCellInclusion_contMDiff m)⟩
  · apply (ContMDiff.iff_comp_isImmersion
      (closedCellInclusion_isSmoothEmbedding m).isImmersion).mpr
    exact ⟨(F.symm.continuous.comp continuous_subtype_val).subtype_mk _,
      F.symm.contMDiff.comp (closedCellInclusion_contMDiff m)⟩

theorem exists_closedCell_isotopy_extension_sphere_product_collar (m : ℕ)
    (h : ℝ → Diffeomorph (𝓡 m) (𝓡 m)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) ∞)
    (hh : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 m)) (𝓡 m) ∞
      (fun z : ℝ × Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 => h z.1 z.2))
    (hi : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 m)) (𝓡 m) ∞
      (fun z : ℝ × Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
        (h z.1).symm z.2))
    (hzero : h 0 = Diffeomorph.refl (𝓡 m)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) ∞) :
    ∃ B : ℝ → Diffeomorph (𝓡∂ (m + 1)) (𝓡∂ (m + 1))
        (ClosedCell (m + 1)) (ClosedCell (m + 1)) ∞,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (m + 1))) (𝓡∂ (m + 1)) ∞
        (fun z : ℝ × ClosedCell (m + 1) => B z.1 z.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (m + 1))) (𝓡∂ (m + 1)) ∞
        (fun z : ℝ × ClosedCell (m + 1) => (B z.1).symm z.2) ∧
      B 0 = Diffeomorph.refl (𝓡∂ (m + 1)) (ClosedCell (m + 1)) ∞ ∧
      (∀ t (x : ClosedCell (m + 1)),
        ‖(B t x : EuclideanSpace ℝ (Fin (m + 1)))‖ = ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ ∧
        ‖((B t).symm x : EuclideanSpace ℝ (Fin (m + 1)))‖ =
          ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖) ∧
      (∀ t (x : ClosedCell (m + 1)), ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ ≤ 1 / 4 →
        B t x = x ∧ (B t).symm x = x) ∧
      ∀ t (x : ClosedCell (m + 1))
        (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) (r : ℝ),
        r ∈ Set.Icc (1 / 2 : ℝ) 1 → (x : EuclideanSpace ℝ (Fin (m + 1))) = r • θ.val →
        (B t x : EuclideanSpace ℝ (Fin (m + 1))) = r • (h t θ).val ∧
        ((B t).symm x : EuclideanSpace ℝ (Fin (m + 1))) = r • ((h t).symm θ).val := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  obtain ⟨H, hH, hHi, hH0, hnorm, hfix, hcollar, _⟩ :=
    Diffeomorph.exists_isotopy_extension_sphere_product_collar h hh hi hzero
  let B := fun t => restrictClosedCell (H t) (fun x => (hnorm t x).1)
  have hB : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (m + 1))) (𝓡∂ (m + 1)) ∞
      (fun z : ℝ × ClosedCell (m + 1) => B z.1 z.2) := by
    apply (ContMDiff.iff_comp_isImmersion
      (closedCellInclusion_isSmoothEmbedding m).isImmersion).mpr
    exact ⟨(hH.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _,
      hH.comp_contMDiff (contMDiff_fst.prodMk_space
        ((closedCellInclusion_contMDiff m).comp contMDiff_snd))⟩
  have hBi : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (m + 1))) (𝓡∂ (m + 1)) ∞
      (fun z : ℝ × ClosedCell (m + 1) => (B z.1).symm z.2) := by
    apply (ContMDiff.iff_comp_isImmersion
      (closedCellInclusion_isSmoothEmbedding m).isImmersion).mpr
    exact ⟨(hHi.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _,
      hHi.comp_contMDiff (contMDiff_fst.prodMk_space
        ((closedCellInclusion_contMDiff m).comp contMDiff_snd))⟩
  refine ⟨B, hB, hBi, ?_, fun t x => hnorm t x, ?_, ?_⟩
  · apply Diffeomorph.ext
    intro x
    apply Subtype.ext
    change H 0 x = (x : EuclideanSpace ℝ (Fin (m + 1)))
    rw [hH0]
    rfl
  · intro t x hx
    exact ⟨Subtype.ext (hfix t x (Or.inl hx)).1,
      Subtype.ext (hfix t x (Or.inl hx)).2⟩
  · intro t x θ r hr hx
    have h := hcollar t θ r ⟨hr.1, hr.2.trans (by norm_num)⟩
    change H t x = _ ∧ (H t).symm x = _
    rw [hx]
    exact h

end DifferentialGeometry.Topology.Handle
