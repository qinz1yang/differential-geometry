import DifferentialGeometry.Topology.Ehresmann.SphereBoundaryDegree

noncomputable section
open Set Topology Manifold
open scoped ContDiff
open DifferentialGeometry.Geometry.Boundary DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

namespace DifferentialGeometry.Topology.Ehresmann

local notation "S²" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

theorem exists_sphere_tube_with_boundary_matching
    {E H W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H]
    [TopologicalSpace W] [ChartedSpace H W] [CompactSpace W] [T2Space W]
    {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] [IsManifold I ∞ W]
    {u : W → ℝ} {a b : ℝ} (hab : a < b) (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (hreg : ∀ w, mfderiv I 𝓘(ℝ) u w ≠ 0)
    (hboundary : ∀ w, I.IsBoundaryPoint w → u w = a ∨ u w = b)
    (ha : a ∈ range u) (hb : b ∈ range u)
    (η : S² ≃ₘ⟮𝓡 2, hI.boundaryI⟯ boundaryLevel u a b hab.ne hu.continuous hboundary) :
    let _ : Fact (a < b) := ⟨hab⟩
    let F₀ := boundaryLevel u a b hab.ne hu.continuous hboundary
    let F₁ := boundaryLevel u b a hab.ne.symm hu.continuous (fun w hw ↦ (hboundary w hw).symm)
    ∃ Θ : (F₀ × Icc a b) ≃ₘ⟮hI.boundaryI.prod (𝓡∂ 1), I⟯ W,
      (∀ p, u (Θ p) = (p.2 : ℝ)) ∧
      (∀ x, Θ (x, ⟨a, le_rfl, hab.le⟩) = x.1.1) ∧
      ∃ P : F₀ ≃ₘ⟮hI.boundaryI, hI.boundaryI⟯ F₁,
        (∀ x, (P x).1.1 = Θ (x, ⟨b, hab.le, le_rfl⟩)) ∧
        ∃ Ψ : (S² × unitInterval) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), I⟯ W,
          (∀ p, u (Ψ p) = a + (b - a) * (p.2 : ℝ)) ∧
          (∀ p, Ψ (p, 0) = (η p).1.1) ∧
          (∀ p, Ψ (p, 1) = (P (η p)).1.1) ∧
          ∀ (η₀ : S² ≃ₘ⟮𝓡 2, hI.boundaryI⟯ F₀) (η₁ : S² ≃ₘ⟮𝓡 2, hI.boundaryI⟯ F₁),
            ((∃ Φ : (S² × unitInterval) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), I⟯ W,
              (∀ p, Φ (p, 0) = (η₀ p).1.1) ∧ (∀ p, Φ (p, 1) = (η₁ p).1.1)) ↔
                sphereDiffeomorphDegree (η₁.trans (η₀.trans P).symm) = 1) ∧
            (sphereDiffeomorphDegree (η₁.trans (η₀.trans P).symm) = 1 →
              ∃ Φ : (S² × unitInterval) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), I⟯ W,
                (∀ p, u (Φ p) = a + (b - a) * (p.2 : ℝ)) ∧
                (∀ p, Φ (p, 0) = (η₀ p).1.1) ∧ (∀ p, Φ (p, 1) = (η₁ p).1.1) ∧
                (∀ t : unitInterval, (t : ℝ) ≤ 1 / 3 → ∀ p,
                  Φ (p, t) = Θ (η₀ p, affineIntervalDiffeomorph a b t)) ∧
                ∀ t : unitInterval, 2 / 3 ≤ (t : ℝ) → ∀ p,
                  Φ (p, t) = Θ (P.symm (η₁ p), affineIntervalDiffeomorph a b t)) := by
  let _ : Fact (a < b) := ⟨hab⟩
  obtain ⟨Θ, hh, hl, P, hP, _⟩ := exists_boundary_endpoint_transport hab hu hreg hboundary ha hb
  let Ψ := unitCylinderDiffeomorphOfProduct a b η Θ
  refine ⟨Θ, hh, hl, P, hP, Ψ, ?_, ?_, ?_, ?_⟩
  · intro p
    rw [unitCylinderDiffeomorphOfProduct_apply, hh, affineIntervalDiffeomorph_apply]
    exact add_comm _ _
  · intro p
    exact (unitCylinderDiffeomorphOfProduct_lower a b η Θ p).trans (hl (η p))
  · intro p
    exact (unitCylinderDiffeomorphOfProduct_upper a b η Θ p).trans (hP (η p)).symm
  · intro η₀ η₁
    exact ⟨prescribed_sphere_boundary_matching_iff_degree_one hab hu.continuous hboundary
      Θ P hh hl hP η₀ η₁, exists_prescribed_sphere_boundary_matching_of_degree_one
        hab hu.continuous hboundary Θ P hh hl hP η₀ η₁⟩

end DifferentialGeometry.Topology.Ehresmann
