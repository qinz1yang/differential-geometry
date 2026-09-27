import DifferentialGeometry.Topology.Manifold.ProductChartSection
import DifferentialGeometry.Topology.Manifold.ProductChartCollar
import DifferentialGeometry.Topology.Manifold.TransverseGraph

noncomputable section
open Set DifferentialGeometry
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

theorem exists_diffeomorph_graph_of_product_chart_section
    {E₀ E₁ F H₀ H₁ H N₀ N₁ M : Type*}
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H₀] [TopologicalSpace H₁] [TopologicalSpace H]
    {I₀ : ModelWithCorners ℝ E₀ H₀} {I₁ : ModelWithCorners ℝ E₁ H₁}
    {J : ModelWithCorners ℝ F H}
    [I₀.Boundaryless] [I₁.Boundaryless]
    [TopologicalSpace N₀] [ChartedSpace H₀ N₀] [IsManifold I₀ ∞ N₀]
    [CompactSpace N₀] [PathConnectedSpace N₀]
    [TopologicalSpace N₁] [ChartedSpace H₁ N₁] [IsManifold I₁ ∞ N₁]
    [T2Space N₁] [ConnectedSpace N₁]
    [TopologicalSpace M] [ChartedSpace H M]
    (O₀ : TopologicalSpace.Opens (N₀ × ℝ)) (O₁ : TopologicalSpace.Opens (N₁ × ℝ))
    (V₀ V₁ : TopologicalSpace.Opens M)
    (Φ₀ : O₀ ≃ₘ⟮I₀.prod 𝓘(ℝ), J⟯ V₀) (Φ₁ : O₁ ≃ₘ⟮I₁.prod 𝓘(ℝ), J⟯ V₁)
    (t : ℝ) (hsection : ∀ p : N₀, (p, t) ∈ O₀)
    (htarget : ∀ p : N₀, (Φ₀ ⟨(p, t), hsection p⟩ : M) ∈ V₁)
    (htransverse : ∀ p, (0, 1) ∉ range
      (mfderiv I₀ (I₁.prod 𝓘(ℝ))
        (fun p : N₀ ↦ (Φ₁.symm ⟨(Φ₀ ⟨(p, t), hsection p⟩ : M), htarget p⟩ : N₁ × ℝ)) p)) :
    ∃ (η : N₁ ≃ₘ⟮I₁, I₀⟯ N₀) (h : N₁ → ℝ), ContMDiff I₁ 𝓘(ℝ) ∞ h ∧
      ∃ hmem : ∀ p, (p, h p) ∈ O₁,
        ∀ p, (Φ₁ ⟨(p, h p), hmem p⟩ : M) = (Φ₀ ⟨(η p, t), hsection (η p)⟩ : M) := by
  let e₀ : N₀ → M := fun p ↦ (Φ₀ ⟨(p, t), hsection p⟩ : M)
  obtain ⟨he₀, hi₀, hd₀⟩ :=
    contMDiff_injective_and_injective_mfderiv_of_product_chart_section O₀ V₀ Φ₀ t hsection
  let f : N₀ → V₁ := fun p ↦ ⟨e₀ p, htarget p⟩
  have hf : ContMDiff I₀ J ∞ f := (ContMDiff.subtypeVal_comp_iff V₁ f).mp he₀
  have hdf (p : N₀) : mfderiv I₀ J e₀ p = mfderiv I₀ J f p := by
    change mfderiv I₀ J (Subtype.val ∘ f) p = _
    rw [mfderiv_comp p ((contMDiff_subtype_val (I := J) (n := ∞)).mdifferentiable (by decide) (f p))
      (hf.mdifferentiable (by decide) p), mfderiv_subtype_val]
    change (ContinuousLinearMap.id ℝ F).comp (mfderiv I₀ J f p : E₀ →L[ℝ] F) = _
    exact ContinuousLinearMap.id_comp _
  let ψ : N₀ → O₁ := Φ₁.symm ∘ f
  have hψ : ContMDiff I₀ (I₁.prod 𝓘(ℝ)) ∞ ψ := Φ₁.symm.contMDiff.comp hf
  have hdψ (p : N₀) : Function.Injective (mfderiv I₀ (I₁.prod 𝓘(ℝ)) ψ p) := by
    change Function.Injective (mfderiv I₀ (I₁.prod 𝓘(ℝ)) (Φ₁.symm ∘ f) p)
    rw [mfderiv_comp p (Φ₁.symm.contMDiff.mdifferentiable (by decide) (f p))
      (hf.mdifferentiable (by decide) p), ← hdf]
    exact (Φ₁.symm.mfderivToContinuousLinearEquiv (by decide) (f p)).injective.comp (hd₀ p)
  let e : N₀ → N₁ × ℝ := fun p ↦ (ψ p : N₁ × ℝ)
  have he : ContMDiff I₀ (I₁.prod 𝓘(ℝ)) ∞ e := contMDiff_subtype_val.comp hψ
  have hei : Function.Injective e :=
    Subtype.val_injective.comp (Φ₁.symm.injective.comp
      (fun _ _ h ↦ hi₀ (congrArg (Subtype.val : V₁ → M) h)))
  have hde (p : N₀) : Function.Injective (mfderiv I₀ (I₁.prod 𝓘(ℝ)) e p) := by
    change Function.Injective (mfderiv I₀ (I₁.prod 𝓘(ℝ)) (Subtype.val ∘ ψ) p)
    rw [mfderiv_comp p
      ((contMDiff_subtype_val (I := I₁.prod 𝓘(ℝ)) (n := ∞)).mdifferentiable (by decide) (ψ p))
      (hψ.mdifferentiable (by decide) p), mfderiv_subtype_val]
    exact Function.injective_id.comp (hdψ p)
  have hdim : Module.finrank ℝ E₀ = Module.finrank ℝ E₁ := by
    let p : N₀ := Classical.choice inferInstance
    let A₀ : (E₀ × ℝ) ≃L[ℝ] F :=
      Φ₀.mfderivToContinuousLinearEquiv (by decide) ⟨(p, t), hsection p⟩
    let A₁ : F ≃L[ℝ] (E₁ × ℝ) :=
      Φ₁.symm.mfderivToContinuousLinearEquiv (by decide) (f p)
    have hd := (A₀.trans A₁).toLinearEquiv.finrank_eq
    simp only [Module.finrank_prod, Module.finrank_self] at hd
    exact Nat.add_right_cancel hd
  obtain ⟨η, h, hh, heq⟩ :=
    exists_diffeomorph_graph_of_transverse_embedding e he hei hde hdim htransverse
  have hmem (p : N₁) : (p, h p) ∈ O₁ := by
    rw [← heq p]
    exact (ψ (η p)).property
  refine ⟨η, h, hh, hmem, ?_⟩
  intro p
  have hz : (⟨(p, h p), hmem p⟩ : O₁) = ψ (η p) := Subtype.ext (heq p).symm
  rw [hz]
  change (Φ₁ (Φ₁.symm (f (η p))) : M) = e₀ (η p)
  rw [Φ₁.apply_symm_apply]

theorem exists_smoothTwoSidedCollar_of_transverse_product_chart_section
    {E₀ E₁ F H₀ H₁ H N₀ N₁ M : Type*}
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H₀] [TopologicalSpace H₁] [TopologicalSpace H]
    {I₀ : ModelWithCorners ℝ E₀ H₀} {I₁ : ModelWithCorners ℝ E₁ H₁}
    {J : ModelWithCorners ℝ F H}
    [I₀.Boundaryless] [I₁.Boundaryless]
    [TopologicalSpace N₀] [ChartedSpace H₀ N₀] [IsManifold I₀ ∞ N₀]
    [CompactSpace N₀] [PathConnectedSpace N₀]
    [TopologicalSpace N₁] [ChartedSpace H₁ N₁] [IsManifold I₁ ∞ N₁]
    [T2Space N₁] [ConnectedSpace N₁]
    [TopologicalSpace M] [ChartedSpace H M]
    (O₀ : TopologicalSpace.Opens (N₀ × ℝ)) (O₁ : TopologicalSpace.Opens (N₁ × ℝ))
    (V₀ V₁ : TopologicalSpace.Opens M)
    (Φ₀ : O₀ ≃ₘ⟮I₀.prod 𝓘(ℝ), J⟯ V₀) (Φ₁ : O₁ ≃ₘ⟮I₁.prod 𝓘(ℝ), J⟯ V₁)
    (t : ℝ) (hsection : ∀ p : N₀, (p, t) ∈ O₀)
    (htarget : ∀ p : N₀, (Φ₀ ⟨(p, t), hsection p⟩ : M) ∈ V₁)
    (htransverse : ∀ p, (0, 1) ∉ range
      (mfderiv I₀ (I₁.prod 𝓘(ℝ))
        (fun p : N₀ ↦ (Φ₁.symm ⟨(Φ₀ ⟨(p, t), hsection p⟩ : M), htarget p⟩ : N₁ × ℝ)) p))
    {r : ℝ} (hr : 0 < r) :
    ∃ (η : N₁ ≃ₘ⟮I₁, I₀⟯ N₀) (a : N₁ → ℝ), ContMDiff I₁ 𝓘(ℝ) ∞ a ∧
      ∃ hmem : ∀ p, (p, a p) ∈ O₁,
        (∀ p, (Φ₁ ⟨(p, a p), hmem p⟩ : M) =
          (Φ₀ ⟨(η p, t), hsection (η p)⟩ : M)) ∧
        ∃ c : DifferentialGeometry.Topology.SmoothTwoSidedCollar I₀ J
            (fun p ↦ (Φ₀ ⟨(p, t), hsection p⟩ : M)),
          c.radius < r ∧
          (∀ p s, s ∈ Icc (-c.radius) c.radius → (p, a p + s) ∈ O₁) ∧
          ∀ p : N₀ × DifferentialGeometry.Topology.symmetricOpenInterval c.radius,
            ∃ hp : (η.symm p.1, a (η.symm p.1) + (p.2 : ℝ)) ∈ O₁,
              c.toFun p = (Φ₁ ⟨(η.symm p.1, a (η.symm p.1) + (p.2 : ℝ)), hp⟩ : M) := by
  obtain ⟨η, a, ha, hmem, heq⟩ :=
    exists_diffeomorph_graph_of_product_chart_section O₀ O₁ V₀ V₁ Φ₀ Φ₁
      t hsection htarget htransverse
  let _ : CompactSpace N₁ := η.symm.toHomeomorph.compactSpace
  have heq' (p : N₀) : (Φ₀ ⟨(p, t), hsection p⟩ : M) =
      (Φ₁ ⟨(η.symm p, a (η.symm p)), hmem (η.symm p)⟩ : M) := by
    simpa only [η.apply_symm_apply] using (heq (η.symm p)).symm
  obtain ⟨c, hcr, hstrip, hpoint⟩ :=
    DifferentialGeometry.Topology.exists_smoothTwoSidedCollar_of_reparametrized_product_chart_graph
      O₁ V₁ Φ₁ a ha hmem (fun p ↦ (Φ₀ ⟨(p, t), hsection p⟩ : M)) η.symm heq' hr
  refine ⟨η, a, ha, hmem, heq, c, hcr, ?_, hpoint⟩
  intro p s hs
  simpa only [η.symm_apply_apply] using hstrip (η p) s hs

end DifferentialGeometry.Topology.Manifold
