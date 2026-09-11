import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Product
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Continuation

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [hT2 : T2Space M] [hCompact : CompactSpace M]
    [hNonempty : Nonempty M] [hBoundary : I.Boundaryless]

namespace ProductCurve

def ricciTangent (c : ProductCurve M) (G : SolutionFamily (I := I) (M := M))
    (lambda x t : ℝ) : ℝ :=
  G.ricciAt t (c.projection.lift x t)
    (vec2 (c.unitTangent G.metric lambda x t).1 (c.unitTangent G.metric lambda x t).1)


def initialMinAngle (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda a : ℝ) : ℝ :=
  sInf ((fun x => c.angle g lambda x a) '' Icc (0 : ℝ) 1)


def initialMaxCurvature (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda a : ℝ) : ℝ :=
  sSup ((fun x => c.curvature g lambda x a) '' Icc (0 : ℝ) 1)

def curvatureEnvelope (c₀ : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda B₀ C a b t : ℝ) : ℝ :=
  Real.exp ((C + B₀) * (t - a)) *
    ((c₀.initialMaxCurvature g lambda a + 1) / c₀.initialMinAngle g lambda a +
      C * (t - a) / (c₀.initialMinAngle g lambda a * Real.exp (-B₀ * (b - a))))

end ProductCurve

variable {D : RealTimeInterval} {a b s v : ℝ}

include hT2 hCompact hNonempty hBoundary

theorem rfs_csf_ramp_angle (B : RicciBackground (I := I) (M := M) D a b)
    (lambda : ℝ) (hlambda : 0 < lambda) (hsv : s < v) (hwindow : Icc s v ⊆ Icc a b)
    (c : ProductCurve M) (hc : c.IsSolutionOn B.family.metric lambda (Icc s v))
    (u₀ : ℝ) (hu₀ : 0 < u₀) (hinit : ∀ x, u₀ ≤ c.angle B.family.metric lambda x s) :
    (∀ x t, t ∈ Icc s v →
      derivWithin (c.angle B.family.metric lambda x) (Icc s v) t =
        c.ds B.family.metric lambda (c.ds B.family.metric lambda
          (c.angle B.family.metric lambda)) x t +
          (c.curvatureSq B.family.metric lambda x t + c.ricciTangent B.family lambda x t) *
            c.angle B.family.metric lambda x t) ∧
    (∀ x t, t ∈ Icc s v →
      u₀ * Real.exp (-B.B₀ * (t - s)) ≤ c.angle B.family.metric lambda x t ∧
        c.angle B.family.metric lambda x t ≤ 1) ∧
    (∀ t ∈ Icc s v,
      c.integral B.family.metric lambda (c.angle B.family.metric lambda) t = c.degree * lambda) ∧
    0 < c.degree ∧
    (c.degree = 1 → ∀ t ∈ Icc s v, Topology.IsEmbedding (fun z => c.map z t)) := by
  sorry

theorem ramp_curvature_bound (B : RicciBackground (I := I) (M := M) D a b)
    (lambda : ℝ) (hlambda : 0 < lambda) (hlambda_one : lambda ≤ 1)
    (T : ℝ) (haT : a < T) (hTb : T ≤ b) (J : Set ℝ)
    (hJ : J = Ico a T ∨ J = Icc a T) (c : ProductCurve M)
    (hc : c.IsSolutionOn B.family.metric lambda J)
    (hramp : c.IsRampOn B.family.metric lambda {a}) :
    0 < c.initialMinAngle B.family.metric lambda a ∧
      ∀ x t, t ∈ J → c.curvature B.family.metric lambda x t ≤
        c.curvatureEnvelope B.family.metric lambda B.B₀ B.C a b t := by
  sorry

theorem rfs_csf_ramp_existence (B : RicciBackground (I := I) (M := M) D a b)
    (lambda : ℝ) (hlambda : 0 < lambda) (hlambda_one : lambda ≤ 1)
    (c₀ : ProductCurve M) (hsmooth : c₀.SmoothOn (I := I) {a})
    (hramp : c₀.IsRampOn B.family.metric lambda {a}) :
    ∃ c : ProductCurve M,
      c.IsSolutionOn B.family.metric lambda (Icc a b) ∧
      c.IsRampOn B.family.metric lambda (Icc a b) ∧
      (∀ z, c.map z a = c₀.map z a) ∧
      (∀ x t, t ∈ Icc a b → c.curvature B.family.metric lambda x t ≤
        c₀.curvatureEnvelope B.family.metric lambda B.B₀ B.C a b t) ∧
      (∀ d : ProductCurve M, d.IsSolutionOn B.family.metric lambda (Icc a b) →
        (∀ z, d.map z a = c₀.map z a) →
        ∀ z t, t ∈ Icc a b → d.map z t = c.map z t) := by
  sorry

def productEmbeddedCoordinates {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (c : ProductCurve M) (x t : ℝ) : EuclideanSpace ℝ (Fin N) × ℂ :=
  (e.map (c.projection.lift x t),
    ((AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0))
      (c.map (x : Surgery.Topology.Circle) t).2 : ℂ))


@[instance_reducible]
def smoothProductInitialTopology {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) (a : ℝ) :
    TopologicalSpace (ProductCurve M) :=
  TopologicalSpace.generateFrom {U | ∃ c : ProductCurve M, ∃ m : ℕ, ∃ ε : ℝ,
    0 < ε ∧ U = {d | ∃ ρ : ℝ, ρ < ε ∧ ∀ x ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv m (fun y => productEmbeddedCoordinates e d y a) x -
        iteratedDeriv m (fun y => productEmbeddedCoordinates e c y a) x‖ ≤ ρ}}

@[instance_reducible]
def smoothProductCylinderTopology {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) (J : Set ℝ) :
    TopologicalSpace (ProductCurve M) :=
  TopologicalSpace.generateFrom {U | ∃ c : ProductCurve M, ∃ m : ℕ, ∃ ε : ℝ,
    0 < ε ∧ U = {d | ∃ ρ : ℝ, ρ < ε ∧ ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ J,
      ‖iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => productEmbeddedCoordinates e d q.1 q.2)
          (univ ×ˢ J) p -
        iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => productEmbeddedCoordinates e c q.1 q.2)
          (univ ×ˢ J) p‖ ≤ ρ}}

theorem rfs_csf_ramp_family (B : RicciBackground (I := I) (M := M) D a b)
    (lambda : ℝ) (hlambda : 0 < lambda) (hlambda_one : lambda ≤ 1)
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P] [CompactSpace P] (initial : P → ProductCurve M)
    (hcontinuous : @Continuous P (ProductCurve M) inferInstance
      (smoothProductInitialTopology e a) initial)
    (hsmooth : ∀ p, (initial p).SmoothOn (I := I) {a})
    (hramp : ∀ p, (initial p).IsRampOn B.family.metric lambda {a}) :
    ∃ solutions : P → ProductCurve M,
      (@Continuous P (ProductCurve M) inferInstance
        (smoothProductCylinderTopology e (Icc a b)) solutions) ∧
      ∀ p, (solutions p).IsSolutionOn B.family.metric lambda (Icc a b) ∧
        (solutions p).IsRampOn B.family.metric lambda (Icc a b) ∧
        ∀ z, (solutions p).map z a = (initial p).map z a := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
