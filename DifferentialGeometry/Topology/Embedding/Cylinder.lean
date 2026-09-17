import DifferentialGeometry.Topology.Embedding.Lift
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorphImmersion
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition
import DifferentialGeometry.Topology.Manifold.AddCircle

open Set Metric TopologicalSpace
open scoped ContDiff Manifold

namespace Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M]

theorem IsSmoothEmbedding.exists_cylinder_diffeomorph
    {e : M → EuclideanSpace ℝ (Fin 3)} (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    {η : AddCircle (1 : ℝ) → M} (hη : IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ η)
    (Ψ : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin 3)) (T : Opens ℝ)
    (hboundary : Ψ '' (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ {0}) = e '' range η)
    (hwall : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, ∀ t ∈ T, Ψ (x, t) ∈ range e) :
    ∃ q : AddCircle (1 : ℝ) → EuclideanSpace ℝ (Fin 2),
      IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ q ∧
      range q = sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
      ∃ (V : Opens M)
        (C : (AddCircle (1 : ℝ) × T) ≃ₘ⟮𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ), 𝓡 2⟯ V),
        (V : Set M) = e ⁻¹' (Ψ '' (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ (T : Set ℝ))) ∧
        (∀ p, e (C p) = Ψ (q p.1, p.2.val)) ∧
        ∀ θ (t : T), t.val = 0 → (C (θ, t) : M) = η θ := by
  have hΨ := DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
    Ψ.isLocalDiffeomorph Ψ.injective
  have hΨi := DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
    Ψ.symm.isLocalDiffeomorph Ψ.symm.injective
  let q : AddCircle (1 : ℝ) → EuclideanSpace ℝ (Fin 2) := fun θ => (Ψ.symm (e (η θ))).1
  have hzero (θ : AddCircle (1 : ℝ)) : (Ψ.symm (e (η θ))).2 = 0 := by
    obtain ⟨p, hp, hpe⟩ := hboundary.symm.subset ⟨η θ, mem_range_self θ, rfl⟩
    rw [← hpe, Ψ.symm_apply_apply]
    exact hp.2
  have hqe (θ : AddCircle (1 : ℝ)) : Ψ (q θ, 0) = e (η θ) := by
    have hp : (q θ, 0) = Ψ.symm (e (η θ)) := Prod.ext rfl (hzero θ).symm
    rw [hp, Ψ.apply_symm_apply]
  have hq : IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ q :=
    (hΨi.comp (he.comp hη (by simp)) (by simp)).fst_of_snd_eq_const (by simp) hzero
  have hqrange : range q = sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    ext x
    constructor
    · rintro ⟨θ, rfl⟩
      obtain ⟨p, hp, hpe⟩ := hboundary.symm.subset ⟨η θ, mem_range_self θ, rfl⟩
      change (Ψ.symm (e (η θ))).1 ∈ sphere 0 1
      rw [← hpe, Ψ.symm_apply_apply]
      exact hp.1
    · intro hx
      obtain ⟨y, ⟨θ, rfl⟩, hy⟩ := hboundary.subset ⟨(x, 0), ⟨hx, rfl⟩, rfl⟩
      exact ⟨θ, congrArg Prod.fst (Ψ.injective ((hqe θ).trans hy))⟩
  let w : AddCircle (1 : ℝ) × T → EuclideanSpace ℝ (Fin 3) := fun p => Ψ (q p.1, p.2.val)
  have hwprod : IsSmoothEmbedding (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞ (fun p : AddCircle (1 : ℝ) × T => (q p.1, p.2.val)) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hq.prodMap (IsSmoothEmbedding.of_opens T)
  have hw : IsSmoothEmbedding (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ w :=
    hΨ.comp hwprod (by simp)
  have hwrange : range w ⊆ range e := by
    rintro y ⟨p, rfl⟩
    exact hwall (q p.1) (hqrange.subset (mem_range_self p.1)) p.2.val p.2.property
  let c := he.lift w hwrange
  have hc : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ c :=
    he.contMDiff_lift hw.contMDiff hwrange
  have hce (p) : e (c p) = w p := he.comp_lift hwrange p
  have hcemb : IsSmoothEmbedding (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ c :=
    he.isSmoothEmbedding_lift hw (by simp) hwrange
  obtain ⟨V, C, hV, hC, _⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorph_onto_range_of_injective_immersion
      c hc hcemb.isEmbedding.injective
      (fun x => (hcemb.isImmersion.isImmersionAt x).injective_mfderiv (by simp))
      (by simp [Module.finrank_prod])
  refine ⟨q, hq, hqrange, V, C, ?_, ?_, ?_⟩
  · rw [hV]
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨(q p.1, p.2.val), ⟨hqrange.subset (mem_range_self p.1), p.2.property⟩,
        (hce p).symm⟩
    · rintro ⟨⟨y, t⟩, ⟨hy, ht⟩, heq⟩
      obtain ⟨θ, rfl⟩ := hqrange.symm.subset hy
      refine ⟨(θ, ⟨t, ht⟩), he.isEmbedding.injective ?_⟩
      exact (hce _).trans heq
  · intro p
    rw [hC]
    exact hce p
  · intro θ t ht
    apply he.isEmbedding.injective
    rw [hC, hce]
    change Ψ (q θ, t.val) = e (η θ)
    rw [ht, hqe]

end Manifold
