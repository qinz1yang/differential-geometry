import DifferentialGeometry.Topology.VectorField.Index

set_option autoImplicit false
open Bundle Filter Set
open scoped Manifold ContDiff Topology
noncomputable section
namespace Poincare.VectorField
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem continuousOn_model_tangentSection_iff {V : E → E} {s : Set E} :
    ContinuousOn (fun y => (⟨y, V y⟩ : TangentBundle 𝓘(ℝ, E) E)) s ↔ ContinuousOn V s := by
  constructor
  · intro hc y hy
    have hh := (FiberBundle.continuousWithinAt_section E).mp (hc y hy)
    simpa only [trivializationAt_model_space_apply] using! hh
  · intro hc y hy
    apply (FiberBundle.continuousWithinAt_section E).mpr
    simpa only [trivializationAt_model_space_apply] using! hc y hy

theorem hasContinuousIsolatedZero_model_iff {V : E → E} {x : E} :
    HasContinuousIsolatedZero 𝓘(ℝ, E) V x ↔ Poincare.LocalDegree.isolatedZero V x := by
  constructor
  · intro h
    obtain ⟨s, hs, hc⟩ := h.continuous
    apply Poincare.LocalDegree.isolatedZero_of_nhds hs
      (continuousOn_model_tangentSection_iff.mp hc) h.zero
    apply eventually_nhdsWithin_iff.mpr
    filter_upwards [h.isolated] with y hy
    exact fun hne hz => hne (hy hz)
  · rintro ⟨R, hR⟩
    refine ⟨hR.zero, ⟨Metric.closedBall x R, Metric.closedBall_mem_nhds x hR.pos,
      continuousOn_model_tangentSection_iff.mpr hR.continuousOn⟩, ?_⟩
    filter_upwards [Metric.closedBall_mem_nhds x hR.pos] with y hy
    exact (hR.zero_iff y hy).mp

theorem index_model_eq_localDegree {d : ℕ}
    {V : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {x : EuclideanSpace ℝ (Fin (d + 1))}
    (hV : HasContinuousIsolatedZero 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) V x) :
    index 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) V x hV =
      Poincare.LocalDegree.euclideanLocalDegree V x (hasContinuousIsolatedZero_model_iff.mp hV) := by
  let f : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1)))
      (EuclideanSpace ℝ (Fin (d + 1))) (EuclideanSpace ℝ (Fin (d + 1))) 1 :=
    (Diffeomorph.refl 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1)))
      (EuclideanSpace ℝ (Fin (d + 1))) 1).toPartialDiffeomorph
  have hh := index_eq_localDegree 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) f (Set.mem_univ x) hV
  change index 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) V x hV =
    Poincare.LocalDegree.euclideanLocalDegree
      (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) id V) x _ at hh
  have hid : _root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) id V = V :=
    _root_.VectorField.mpullback_id
  exact hh.trans (Poincare.LocalDegree.euclideanLocalDegree_congr _
    (hasContinuousIsolatedZero_model_iff.mp hV) (Filter.Eventually.of_forall (congrFun hid)))

end Poincare.VectorField
