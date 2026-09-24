import DifferentialGeometry.Topology.Covering.SphereLifts
import DifferentialGeometry.Topology.Manifold.StereographicAntipodal

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev S3 := Metric.sphere (0 : E4) 1

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]

theorem exists_smooth_sphere_lift_disjoint_antipodal
    (p : S3 → M) (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
    (honto : Function.Surjective p)
    (hfib : ∀ x y : S3, p x = p y ↔ x = y ∨ (x : E4) = -(y : E4))
    (e : S2 → M) (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) :
    ∃ f : S2 → S3,
      IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f ∧
      (∀ x, p (f x) = e x) ∧
      IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun x => -(f x)) ∧
      Disjoint (range f) (range (fun x => -(f x))) ∧
      p ⁻¹' range e = range f ∪ range (fun x => -(f x)) := by
  have hcov : IsCoveringMap p := isLocalHomeomorph_iff_isCoveringMap.mp hp.isLocalHomeomorph
  let z : S2 := DifferentialGeometry.Topology.sphereTwoNorth
  obtain ⟨x₀, hx₀⟩ := honto (e z)
  obtain ⟨f, _, hpf, _⟩ := exists_smooth_lift_of_simplyConnected hcov hp e he.contMDiff z x₀ hx₀
  have hf : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f :=
    isSmoothEmbedding_of_lift_through_localDiffeomorph hp he f.continuous hpf
  have hneg (x : S3) : p (-x) = p x :=
    (hfib (-x) x).mpr (Or.inr rfl)
  have hnemb : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun x => -(f x)) :=
    isSmoothEmbedding_of_lift_through_localDiffeomorph hp he
      ((DifferentialGeometry.Topology.Manifold.sphereAntipodalDiffeomorph
        (E := E4) (n := 3)).contMDiff.continuous.comp f.continuous)
      (fun x => (hneg (f x)).trans (hpf x))
  refine ⟨f, hf, hpf, hnemb, ?_, ?_⟩
  · apply disjoint_left.mpr
    rintro y ⟨u, rfl⟩ ⟨v, hv⟩
    have huv : u = v := he.isEmbedding.injective
      ((hpf u).symm.trans ((congrArg p hv.symm).trans ((hneg (f v)).trans (hpf v))))
    subst v
    have hval : -(f u : E4) = (f u : E4) := congrArg Subtype.val hv
    have hzero : (f u : E4) = 0 := by
      have htwo : (2 : ℝ) • (f u : E4) = 0 := by
        rw [two_smul]
        exact neg_eq_iff_add_eq_zero.mp hval
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    have hn : ‖(f u : E4)‖ = 1 := norm_eq_of_mem_sphere (f u)
    simp only [hzero, norm_zero, zero_ne_one] at hn
  · ext y
    constructor
    · rintro ⟨x, hx⟩
      rcases (hfib y (f x)).mp (hx.symm.trans (hpf x).symm) with h | h
      · exact Or.inl ⟨x, h.symm⟩
      · exact Or.inr ⟨x, Subtype.ext h.symm⟩
    · rintro (⟨x, rfl⟩ | ⟨x, rfl⟩)
      · exact ⟨x, (hpf x).symm⟩
      · exact ⟨x, ((hneg (f x)).trans (hpf x)).symm⟩

end DifferentialGeometry.Topology
