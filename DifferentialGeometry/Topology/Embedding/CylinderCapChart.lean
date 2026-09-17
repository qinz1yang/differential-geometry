import DifferentialGeometry.Topology.Embedding.CylinderCapLift
import DifferentialGeometry.Topology.Embedding.CylinderCapReplacement
import DifferentialGeometry.Topology.Manifold.DiskChart

open Set Metric TopologicalSpace
open scoped ContDiff Manifold Topology

namespace Manifold

variable {E F B H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 1 + 1)] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace B] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]

theorem IsSmoothEmbedding.exists_cylinderCap_chart
    {e : M → F} (he : IsSmoothEmbedding I 𝓘(ℝ, F) ∞ e)
    (Ψ : (E × ℝ) ≃ₘ[ℝ] F) {ε a σ : ℝ}
    (ha : a ≠ 0) (haε : |a| < ε) (hσa : 0 ≤ σ * a)
    (V : Opens M) (C : (B × (⟨Ioo (-ε) ε, isOpen_Ioo⟩ : Opens ℝ)) ≃ₜ V)
    (q : B → E) {D : Set M}
    (hwall : ∀ x ∈ closedBall (0 : E) 1, ∀ t ∈ Ioo (-ε) ε,
      Ψ (x, t) ∈ range e ↔ ‖x‖ = 1)
    (hV : (V : Set M) = e ⁻¹' (Ψ '' (sphere (0 : E) 1 ×ˢ Ioo (-ε) ε)))
    (hC : ∀ p, e (C p) = Ψ (q p.1, p.2.val))
    (hside : ∀ p, (C p : M) ∈ D ↔ σ * p.2.val ≤ 0)
    (φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    (hballφ : closedBall (0 : E) 1 ⊆ φ.source)
    (hφD : φ '' closedBall (0 : E) 1 = D)
    (hboundary : e '' (φ '' sphere (0 : E) 1) = Ψ '' (sphere (0 : E) 1 ×ˢ {0})) :
    ∃ χ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞,
      closedBall (0 : E) 1 ⊆ χ.source ∧ χ '' closedBall (0 : E) 1 = D ∧
      ∀ x ∈ sphere (0 : E) 1,
        Ψ ∘ EuclideanGeometry.cylinderCap a =ᶠ[nhds x] e ∘ χ := by
  have hε : 0 < ε := (abs_nonneg a).trans_lt haε
  let _ : FiniteDimensional ℝ E := FiniteDimensional.of_fact_finrank_eq_succ 1
  let _ : Nontrivial E := Module.nontrivial_of_finrank_pos
    (by rw [show Module.finrank ℝ E = 1 + 1 from Fact.out]; norm_num : 0 < Module.finrank ℝ E)
  let _ : T2Space M := he.isEmbedding.t2Space
  obtain ⟨ψ, _, hψ, _, hψeq⟩ := he.exists_partialDiffeomorph_cylinderCap Ψ hε ha
    (fun x hx t ht => (hwall x (sphere_subset_closedBall hx) t ht).mpr
      (mem_sphere_zero_iff_norm.mp hx))
  have hψboundary : e '' (ψ '' sphere (0 : E) 1) = Ψ '' (sphere (0 : E) 1 ×ˢ {0}) := by
    rw [image_image, ← EuclideanGeometry.cylinderCap_image_sphere a, ← image_comp]
    exact image_congr fun x hx => hψeq x (hψ hx)
  have hboundary' : φ '' sphere (0 : E) 1 = ψ '' sphere (0 : E) 1 :=
    (Set.image_injective.mpr he.isEmbedding.injective) (hboundary.trans hψboundary.symm)
  have hdisj := EuclideanGeometry.disjoint_cylinderCap_image_of_cylinder_sides e Ψ.toHomeomorph
    haε hσa V C q (fun x hx t ht hh => (hwall x hx t ht).mp hh) hV hC hside
  have hside' : MapsTo ψ (closedBall (0 : E) 1 ∩ ψ.source) (φ '' closedBall (0 : E) 1) := by
    intro x hx
    rw [hφD]
    by_contra hh
    exact (Set.disjoint_left.mp hdisj) ⟨x, hx.1, (hψeq x hx.2).symm⟩ ⟨ψ x, hh, rfl⟩
  obtain ⟨χ, hχ, hχD, W, hW, hSW, hWψ, hχψ⟩ :=
    φ.exists_disk_chart_eqOn_circle_neighborhood ψ hballφ hψ hboundary' hside'
  refine ⟨χ, hχ, hχD.trans hφD, ?_⟩
  intro x hx
  filter_upwards [hW.mem_nhds (hSW hx)] with y hy
  change Ψ (EuclideanGeometry.cylinderCap a y) = e (χ y)
  rw [hχψ hy]
  exact (hψeq y (hWψ hy)).symm

end Manifold
