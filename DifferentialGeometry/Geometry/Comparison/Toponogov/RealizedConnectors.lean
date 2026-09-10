import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ENNReal Manifold ContDiff Topology

namespace Poincare.Toponogov

open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]

structure RealizedMinimizingConnector
    (g : SmoothRiemannianMetric I M) (p q : M) where
  curve : ℝ → M
  length : ℝ
  length_nonneg : 0 ≤ length
  source : curve 0 = p
  target : curve length = q
  smooth : ContMDiffOn 𝓘(ℝ, ℝ) I 1 curve (Set.Icc 0 length)
  geodesic : IsGeodesicOn (I := I) g curve (Set.Icc 0 length)
  unitSpeed : ∀ t ∈ Set.Ioo (0 : ℝ) length,
    g.inner (curve t) (mfderiv 𝓘(ℝ, ℝ) I curve t 1)
        (mfderiv 𝓘(ℝ, ℝ) I curve t 1) = 1
  realizes : riemannianEDistOf (I := I) g p q = ENNReal.ofReal length

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem RealizedMinimizingConnector.constant_on_of_length_eq_zero
    {g : SmoothRiemannianMetric I M} {p q : M}
    (c : RealizedMinimizingConnector (I := I) g p q)
    (hc : c.length = 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) c.length, c.curve t = p := by
  intro t ht
  have ht0 : t = 0 := by
    rw [hc] at ht
    exact le_antisymm ht.2 ht.1
  simpa [ht0] using c.source

def RealizedConnectors (g : SmoothRiemannianMetric I M) (p : M)
    (β : ℝ → M) (J : Set ℝ) : Prop :=
  ∀ r ∈ J, Nonempty (RealizedMinimizingConnector (I := I) g p (β r))

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem RealizedConnectors.exists_connector
    {g : SmoothRiemannianMetric I M} {p : M} {β : ℝ → M} {J : Set ℝ}
    (h : RealizedConnectors (I := I) g p β J) {r : ℝ} (hr : r ∈ J) :
    Nonempty (RealizedMinimizingConnector (I := I) g p (β r)) :=
  h r hr

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem RealizedConnectors.mono
    {g : SmoothRiemannianMetric I M} {p : M} {β : ℝ → M} {J K : Set ℝ}
    (h : RealizedConnectors (I := I) g p β J) (hKJ : K ⊆ J) :
    RealizedConnectors (I := I) g p β K := by
  intro r hr
  exact h r (hKJ hr)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem nonempty_realizedMinimizingConnector_of_complete
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (p q : M) :
    Nonempty (RealizedMinimizingConnector (I := I) g p q) := by
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace M :=
    Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M :=
    (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) g := by
    intro x v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  obtain ⟨γ, L, hL, hγ0, hγL, hγsmooth, hγgeo, hγunit, hdist⟩ :=
    exists_unit_speed_minimizing_geodesic_between_points
      (I := I) (M := M) g hEnorm p q
  refine ⟨⟨γ, L, hL, hγ0, hγL, hγsmooth, hγgeo, hγunit, ?_⟩⟩
  simpa only [riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm] using hdist

theorem realizedConnectors_of_complete
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (p : M) (β : ℝ → M) (J : Set ℝ) :
    RealizedConnectors (I := I) g p β J := by
  intro r _
  exact nonempty_realizedMinimizingConnector_of_complete
    (I := I) g hcomplete p (β r)

end Poincare.Toponogov
