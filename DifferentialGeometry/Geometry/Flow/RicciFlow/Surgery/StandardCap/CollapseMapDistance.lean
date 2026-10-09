import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CollapseDomination
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.WeakLength

set_option autoImplicit false
noncomputable section
open Bundle Set Manifold TopologicalSpace DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology ENNReal NNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private abbrev EC := EuclideanSpace ℝ (Fin 2) × ℝ
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

theorem collapseMap_riemannianCurveLength_le_of_cylinder_lower {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (g : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (hlower : ∀ q : DifferentialGeometry.Geometry.Neck.openCylinder B, ∀ v : TangentSpace IC q,
      η * (roundCylinderMetric (E := E3) (n := 2)).inner q.val v v ≤ g.inner q v v)
    (γ : ℝ → DifferentialGeometry.Geometry.Neck.openCylinder B) (a b : ℝ)
    (hγ : ContinuousOn γ (Icc a b)) :
    DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength
        (insertedMetric hA hAB hη g) (collapseMap hA hAB ∘ γ) a b ≤
      DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength g γ a b := by
  have h := collapseMap_eVariationOn_le_of_cylinder_lower hA hAB hη g hlower γ a b hγ
  rw [DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_eq_eVariationOn
      (insertedMetric hA hAB hη g) (collapseMap hA hAB ∘ γ) a b,
    DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_eq_eVariationOn
      g γ a b]
  exact h

theorem collapseMap_riemannianEDistOf_le_of_cylinder_lower {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (g : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (hlower : ∀ q : DifferentialGeometry.Geometry.Neck.openCylinder B, ∀ v : TangentSpace IC q,
      η * (roundCylinderMetric (E := E3) (n := 2)).inner q.val v v ≤ g.inner q v v) :
    ∀ x y : DifferentialGeometry.Geometry.Neck.openCylinder B,
      riemannianEDistOf (insertedMetric hA hAB hη g) (collapseMap hA hAB x)
          (collapseMap hA hAB y) ≤
        riemannianEDistOf g x y := by
  let F : C(DifferentialGeometry.Geometry.Neck.openCylinder B, insertionBall B) :=
    ⟨collapseMap hA hAB, continuous_collapseMap hA hAB⟩
  have hF : ⇑F = collapseMap hA hAB := rfl
  have hloc : ∀ x : DifferentialGeometry.Geometry.Neck.openCylinder B,
      ∃ U ∈ 𝓝 x, ∀ (a b : ℝ)
        (γ : ℝ → DifferentialGeometry.Geometry.Neck.openCylinder B),
        a ≤ b → ContinuousOn γ (Icc a b) → MapsTo γ (Icc a b) U →
        DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength g γ a b ≠ ⊤ →
        DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength
            (insertedMetric hA hAB hη g) (⇑F ∘ γ) a b ≤
          1 * DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength
            g γ a b := by
    intro x
    exact ⟨univ, Filter.univ_mem, fun a b γ _ hγ _ _ => by
      rw [one_mul]
      simpa only [← hF] using
        collapseMap_riemannianCurveLength_le_of_cylinder_lower hA hAB hη g hlower γ a b hγ⟩
  have hmain := DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_local_to_global_length_of_ne_zero
    g (insertedMetric hA hAB hη g) F 1 (by norm_num) hloc
  intro x y
  simpa [hF, one_mul] using hmain x y

end DifferentialGeometry.PDE.RicciFlow.StandardCap
