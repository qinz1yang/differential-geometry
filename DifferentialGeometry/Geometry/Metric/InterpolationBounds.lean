import DifferentialGeometry.Geometry.Metric.GeodesicInterpolation
import DifferentialGeometry.Geometry.Metric.ShortGeodesicBounds
import DifferentialGeometry.Geometry.Metric.SmoothLipschitz



noncomputable section

open Bundle Manifold Set DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M] [Nonempty M] [PreconnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

set_option backward.isDefEq.respectTransparency false in



theorem exists_geodesicInterpolation_ambient_bound (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) :
    ∃ (n : ℕ) (e : M → EuclideanSpace ℝ (Fin n)) (r : EuclideanSpace ℝ (Fin n) → M),
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e ∧
      (∀ x, r (e x) = x) ∧
      ∃ (ρ C : ℝ≥0) (O : Set (ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))),
        let F := fun p : ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
          geodesicInterpolation g (r p.2.1) (r p.2.2) p.1
        0 < ρ ∧ IsOpen O ∧
        ContMDiffOn 𝓘(ℝ, ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
          𝓘(ℝ, E) ∞ F O ∧
        ∀ t ∈ Icc (0 : ℝ) 1, ∀ x y,
          riemannianEDistOf g x y ≤ (ρ : ℝ≥0∞) →
            (t, (e x, e y)) ∈ O ∧
            ∀ v : ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
              Real.sqrt (g.inner (F (t, (e x, e y)))
                (mfderiv 𝓘(ℝ, ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
                  𝓘(ℝ, E) F (t, (e x, e y)) v)
                (mfderiv 𝓘(ℝ, ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
                  𝓘(ℝ, E) F (t, (e x, e y)) v)) ≤ C * ‖v‖ := by
  obtain ⟨n, e, r, U, he, _, _, hU, heU, hr, hleft⟩ :=
    exists_compact_embedding_and_retraction (E := E) (M := M)
  refine ⟨n, e, r, he, hleft, ?_⟩
  by_cases hdim : Module.finrank ℝ E = 0
  · let : Subsingleton M := subsingleton_of_zero_model hdim
    let q : M := Classical.choice ‹Nonempty M›
    have hconst : geodesicInterpolation g = fun _ _ _ => q := by
      funext x y t
      exact Subsingleton.elim _ _
    refine ⟨1, 0, univ, ?_⟩
    dsimp only
    rw [hconst]
    refine ⟨zero_lt_one, isOpen_univ, contMDiffOn_const, fun _ _ _ _ _ => ⟨mem_univ _, ?_⟩⟩
    intro v
    rw [mfderiv_const]
    change Real.sqrt (g.inner q (0 : E) 0) ≤ 0 * ‖v‖
    simp only [map_zero, Real.sqrt_zero, zero_mul, le_refl]
  · let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
    let hg : IsMetricNorm (I := 𝓘(ℝ, E)) (M := M) g :=
      fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := 𝓘(ℝ, E)) g x v
    have hG : geodesicInterpolation g = shortGeodesic g hg := by
      funext x y t
      simp only [geodesicInterpolation, dif_neg hdim]
      rfl
    erw [hG]
    exact exists_ambientShortGeodesic_bound g hg he.continuous hU heU hr hleft

end DifferentialGeometry.Geometry
