import Batteries.Tactic.Alias
import DifferentialGeometry.Geometry.Geodesic.Ray
import Mathlib.Topology.Connected.Basic

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.HopfRinow

namespace DifferentialGeometry.Geometry

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def isTotallyConvex (g : SmoothRiemannianMetric I M) (A : Set M) : Prop :=
  ∀ (γ : ℝ → M) (a b : ℝ), a ≤ b →
    IsGeodesicOn (I := I) g γ (Ioo a b) → ContinuousOn γ (Icc a b) →
    γ a ∈ A → γ b ∈ A → MapsTo γ (Icc a b) A

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem isTotallyConvex.isPreconnected
    {g : SmoothRiemannianMetric I M} (hcomplete : RiemannianMetricComplete (I := I) g)
    {A : Set M} (hA : isTotallyConvex g A) : IsPreconnected A := by
  let : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := (∞ : ℕ∞ω))
    (by decide : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M := (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let : CompleteSpace M := hcomplete.complete
  let : MetricSpace M := riemMetricSpace (I := I) (M := M)
  have hEnorm : IsMetricNorm (I := I) (M := M) g :=
    fun x v ↦ tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  apply isPreconnected_of_forall_pair
  intro p hp q hq
  by_cases hpq : p = q
  · subst q
    exact ⟨{p}, singleton_subset_iff.mpr hp, mem_singleton p, mem_singleton p,
      isPreconnected_singleton⟩
  obtain ⟨γ, _hisom, hzero, hend, hgeo, _hunit⟩ :=
    exists_unitSpeed_minimizing_riemannian_geodesic g hEnorm p q hpq
  have hcont : Continuous γ :=
    (show ContMDiff 𝓘(ℝ, ℝ) I ∞ γ from fun t ↦ contMDiffAt_of_isGeodesicAt (hgeo t)).continuous
  have hmaps := hA γ 0 (dist p q) dist_nonneg
    (fun t _ht ↦ (hgeo t).hasGeodesicEquationAt) hcont.continuousOn
    (by rw [hzero]; exact hp) (by rw [hend]; exact hq)
  exact ⟨γ '' Icc 0 (dist p q), hmaps.image_subset,
    ⟨0, ⟨le_rfl, dist_nonneg⟩, hzero⟩,
    ⟨dist p q, ⟨dist_nonneg, le_rfl⟩, hend⟩,
    isPreconnected_Icc.image γ hcont.continuousOn⟩

end DifferentialGeometry.Geometry

namespace Poincare.Geometry

@[reducible] alias IsTotallyConvex := DifferentialGeometry.Geometry.isTotallyConvex
end Poincare.Geometry

namespace Poincare.Geometry.IsTotallyConvex

alias isPreconnected := DifferentialGeometry.Geometry.isTotallyConvex.isPreconnected

end Poincare.Geometry.IsTotallyConvex
