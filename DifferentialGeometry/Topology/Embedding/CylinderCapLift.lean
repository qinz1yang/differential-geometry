import DifferentialGeometry.Topology.Embedding.CylinderCap
import DifferentialGeometry.Topology.Embedding.Lift
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph
import DifferentialGeometry.Topology.Embedding.LocalDiffeomorph

open Set Metric TopologicalSpace
open scoped ContDiff Manifold

namespace Manifold

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]

theorem IsSmoothEmbedding.exists_partialDiffeomorph_cylinderCap
    {e : M → F} (he : IsSmoothEmbedding I 𝓘(ℝ, F) ∞ e)
    (Ψ : (E × ℝ) ≃ₘ[ℝ] F)
    {ε a : ℝ} (hε : 0 < ε) (ha : a ≠ 0)
    (hwall : ∀ x ∈ sphere (0 : E) 1,
      ∀ t ∈ Ioo (-ε) ε, Ψ (x, t) ∈ range e) :
    ∃ ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞,
      ψ.source = {x | 3 / 4 < ‖x‖ ^ 2 ∧ |a * (‖x‖ ^ 2 - 1)| < ε} ∧
      sphere (0 : E) 1 ⊆ ψ.source ∧
      ψ.target = e ⁻¹' (Ψ '' (EuclideanGeometry.cylinderCap a '' ψ.source)) ∧
      ∀ x ∈ ψ.source, e (ψ x) = Ψ (EuclideanGeometry.cylinderCap a x) := by
  let U : Opens E := ⟨{x | 3 / 4 < ‖x‖ ^ 2 ∧ |a * (‖x‖ ^ 2 - 1)| < ε},
    (isOpen_lt (f := fun _ : E => (3 : ℝ) / 4) (g := fun x => ‖x‖ ^ 2)
      continuous_const (continuous_norm.pow 2)).inter
      (isOpen_lt (f := fun x : E => |a * (‖x‖ ^ 2 - 1)|) (g := fun _ => ε)
        ((continuous_const.mul ((continuous_norm.pow 2).sub continuous_const)).abs)
        continuous_const)⟩
  have hSU : sphere (0 : E) 1 ⊆ U := by
    intro x hx
    have hn := mem_sphere_zero_iff_norm.mp hx
    change 3 / 4 < ‖x‖ ^ 2 ∧ |a * (‖x‖ ^ 2 - 1)| < ε
    simp only [hn, one_pow, sub_self, mul_zero, abs_zero]
    exact ⟨by norm_num, hε⟩
  obtain ⟨v, hvnorm⟩ := exists_norm_eq (E := E) (by norm_num : (0 : ℝ) ≤ 1)
  have hv : v ∈ U := hSU (mem_sphere_zero_iff_norm.mpr hvnorm)
  have hUne : Nonempty U := ⟨⟨v, hv⟩⟩
  let w : U → F := fun x => Ψ (EuclideanGeometry.cylinderCap a x.val)
  have hcap := (IsSmoothEmbedding.of_opens U).cylinderCap ha
  have hw : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ w :=
    ⟨hcap.isImmersion.isLocalDiffeomorphOn_comp_of_ne_zero
      (fun y => Ψ.isLocalDiffeomorph y.val) (by simp),
      Ψ.toHomeomorph.isEmbedding.comp hcap.isEmbedding⟩
  have hwrange : range w ⊆ range e := by
    rintro z ⟨x, rfl⟩
    have hxpos : 0 < ‖x.val‖ := by nlinarith [x.property.1, norm_nonneg x.val]
    rw [show w x = Ψ (‖x.val‖⁻¹ • x.val, a * (‖x.val‖ ^ 2 - 1)) by
      dsimp [w]; rw [EuclideanGeometry.cylinderCap_of_norm_sq_ge a x.property.1.le]]
    apply hwall
    · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos hxpos, inv_mul_cancel₀ hxpos.ne']
    · exact abs_lt.mp x.property.2
  let c : U → M := he.lift w hwrange
  have hc : IsSmoothEmbedding 𝓘(ℝ, E) I ∞ c :=
    he.isSmoothEmbedding_lift hw (by simp) hwrange
  have hce (x : U) : e (c x) = w x := he.comp_lift hwrange x
  obtain ⟨V, C, hV, hC, _⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorph_onto_range_of_injective_immersion
      c hc.contMDiff hc.isEmbedding.injective
      (fun x => (hc.isImmersion.isImmersionAt x).injective_mfderiv (by simp)) rfl
  have hVne : Nonempty V := ⟨C ⟨v, hv⟩⟩
  let iU := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph 𝓘(ℝ, E) U hUne
  let iV := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph I V hVne
  let ψ := (iU.symm.trans C.toPartialDiffeomorph).trans iV
  have hsource : ψ.source = U := by
    ext x
    change ((x ∈ iU.target ∧ iU.symm x ∈ (univ : Set U)) ∧
      C (iU.symm x) ∈ (univ : Set V)) ↔ x ∈ U
    simp only [mem_univ, and_true, iU,
      DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
    rfl
  have htarget : ψ.target = V := by
    ext y
    change (y ∈ iV.target ∧ (iV.symm y ∈ (univ : Set V) ∧
      C.symm (iV.symm y) ∈ (univ : Set U))) ↔ y ∈ V
    simp only [mem_univ, and_self, and_true, iV,
      DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
    rfl
  have hformula (x : E) (hx : x ∈ U) : e (ψ x) = Ψ (EuclideanGeometry.cylinderCap a x) := by
    change e (C (iU.symm x)) = _
    rw [show iU.symm x = ⟨x, hx⟩ from
      DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply 𝓘(ℝ, E) U hUne hx,
      hC, hce]
  refine ⟨ψ, hsource, hsource ▸ hSU, ?_, ?_⟩
  · rw [htarget, hV, hsource]
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨EuclideanGeometry.cylinderCap a p.val, ⟨p.val, p.property, rfl⟩, (hce p).symm⟩
    · rintro ⟨q, ⟨y, hy, rfl⟩, heq⟩
      refine ⟨⟨y, hy⟩, he.isEmbedding.injective ?_⟩
      exact (hce _).trans heq
  · intro x hx
    exact hformula x (hsource.subset hx)

end Manifold
