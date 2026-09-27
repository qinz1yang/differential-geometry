import DifferentialGeometry.Topology.Embedding.CylinderCap
import DifferentialGeometry.Topology.Embedding.Replacement
import DifferentialGeometry.Topology.Embedding.LocalDiffeomorph
import Mathlib.Topology.Instances.Real.Lemmas

open Set Metric TopologicalSpace
open scoped ContDiff Manifold Topology

namespace EuclideanGeometry

variable {E B M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace B] [TopologicalSpace M] [TopologicalSpace F]

theorem disjoint_cylinderCap_image_of_cylinder_sides
    (e : M → F) (Ψ : (E × ℝ) ≃ₜ F) {ε a σ : ℝ}
    (ha : |a| < ε) (hσa : 0 ≤ σ * a)
    (V : Opens M) (C : (B × (⟨Ioo (-ε) ε, isOpen_Ioo⟩ : Opens ℝ)) ≃ₜ V)
    (q : B → E) {D : Set M}
    (hwall : ∀ x ∈ closedBall (0 : E) 1, ∀ t ∈ Ioo (-ε) ε,
      Ψ (x, t) ∈ range e → ‖x‖ = 1)
    (hV : (V : Set M) = e ⁻¹' (Ψ '' (sphere (0 : E) 1 ×ˢ Ioo (-ε) ε)))
    (hC : ∀ p, e (C p) = Ψ (q p.1, p.2.val))
    (hside : ∀ p, (C p : M) ∈ D ↔ σ * p.2.val ≤ 0) :
    Disjoint ((Ψ ∘ cylinderCap a) '' closedBall (0 : E) 1) (e '' Dᶜ) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hye⟩
  have hxnorm : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
  have hsquare : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
  have htime : |(cylinderCap a x).2| < ε := by
    rw [cylinderCap_snd, abs_mul]
    have habs : |‖x‖ ^ 2 - 1| ≤ 1 := abs_le.mpr ⟨by nlinarith [sq_nonneg ‖x‖], by linarith⟩
    exact (mul_le_mul_of_nonneg_left habs (abs_nonneg a)).trans_lt (by simpa using ha)
  have hfiber : Ψ ((cylinderCap a x).1, (cylinderCap a x).2) ∈ range e := ⟨y, hye⟩
  have hnorm := hwall (cylinderCap a x).1
    (mem_closedBall_zero_iff.mpr (norm_cylinderCap_fst_le_one a x))
    (cylinderCap a x).2 (abs_lt.mp htime) hfiber
  have hyV : y ∈ V := by
    change y ∈ (V : Set M)
    rw [hV]
    exact ⟨cylinderCap a x, ⟨mem_sphere_zero_iff_norm.mpr hnorm, abs_lt.mp htime⟩, hye.symm⟩
  let p := C.symm ⟨y, hyV⟩
  have hp : (C p : M) = y := congrArg Subtype.val (C.apply_symm_apply ⟨y, hyV⟩)
  have hpt : p.2.val = (cylinderCap a x).2 := by
    exact congrArg Prod.snd (Ψ.injective ((hC p).symm.trans ((congrArg e hp).trans hye)))
  apply hy
  rw [← hp, hside, hpt, cylinderCap_snd, ← mul_assoc]
  exact mul_nonpos_of_nonneg_of_nonpos hσa (sub_nonpos.mpr hsquare)

end EuclideanGeometry

namespace Manifold

variable {E F B M H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace B] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [CompactSpace M] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]

theorem IsSmoothEmbedding.exists_cylinderCap_replacement
    {e : M → F} (he : IsSmoothEmbedding I 𝓘(ℝ, F) ∞ e)
    (Ψ : (E × ℝ) ≃ₘ[ℝ] F) {ε a σ : ℝ}
    (ha : a ≠ 0) (haε : |a| < ε) (hσa : 0 ≤ σ * a)
    (V : Opens M) (C : (B × (⟨Ioo (-ε) ε, isOpen_Ioo⟩ : Opens ℝ)) ≃ₜ V)
    (q : B → E) {D : Set M}
    (hwall : ∀ x ∈ closedBall (0 : E) 1, ∀ t ∈ Ioo (-ε) ε,
      Ψ (x, t) ∈ range e → ‖x‖ = 1)
    (hV : (V : Set M) = e ⁻¹' (Ψ '' (sphere (0 : E) 1 ×ˢ Ioo (-ε) ε)))
    (hC : ∀ p, e (C p) = Ψ (q p.1, p.2.val))
    (hside : ∀ p, (C p : M) ∈ D ↔ σ * p.2.val ≤ 0)
    (φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    (hballφ : closedBall (0 : E) 1 ⊆ φ.source)
    (hφD : φ '' closedBall (0 : E) 1 = D)
    (hcollar : ∀ x ∈ sphere (0 : E) 1,
      Ψ ∘ EuclideanGeometry.cylinderCap a =ᶠ[nhds x] e ∘ φ) :
    ∃ f : M → F, IsSmoothEmbedding I 𝓘(ℝ, F) ∞ f ∧
      (∀ x ∈ closedBall (0 : E) 1, f (φ x) = Ψ (EuclideanGeometry.cylinderCap a x)) ∧
      EqOn f e Dᶜ ∧
      ∀ y ∈ D, f =ᶠ[nhds y] (Ψ ∘ EuclideanGeometry.cylinderCap a) ∘ φ.symm := by
  let L : (E × ℝ) ≃L[ℝ] F := Ψ.mfderivToContinuousLinearEquiv (by simp) 0
  let _ : FiniteDimensional ℝ F :=
    FiniteDimensional.of_injective L.symm.toLinearMap L.symm.injective
  have hcap := (IsSmoothEmbedding.id (I := 𝓘(ℝ, E)) (M := E) (n := ∞)).cylinderCap ha
  have hg : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (Ψ ∘ EuclideanGeometry.cylinderCap a) :=
    ⟨hcap.isImmersion.isLocalDiffeomorphOn_comp_of_ne_zero
      (fun y => Ψ.isLocalDiffeomorph y.val) (by simp),
      Ψ.toHomeomorph.isEmbedding.comp hcap.isEmbedding⟩
  have hdisj := EuclideanGeometry.disjoint_cylinderCap_image_of_cylinder_sides
    e Ψ.toHomeomorph haε hσa V C q hwall hV hC hside
  have hfront : frontier (closedBall (0 : E) 1) = sphere 0 1 :=
    frontier_closedBall (0 : E) (by norm_num)
  obtain ⟨f, hf, hmap, hfix, hnear⟩ := he.exists_replacement_of_partialDiffeomorph (by simp)
    φ (isCompact_closedBall (0 : E) 1) hballφ hg
    (fun x hx => hcollar x (hfront.subset hx)) (hφD.symm ▸ hdisj)
  exact ⟨f, hf, hmap, hφD ▸ hfix, hφD ▸ hnear⟩

end Manifold
