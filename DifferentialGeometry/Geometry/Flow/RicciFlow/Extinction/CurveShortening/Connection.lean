import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.DifferenceTimeDerivative

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace CurveMap

def Field.SmoothOn {c : CurveMap M} (V : c.Field (I := I)) (J : Set ℝ) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I.tangent ∞
    (fun p : ℝ × ℝ => (⟨c.lift p.1 p.2, V p.1 p.2⟩ : TangentBundle I M))
    (univ ×ˢ J)

omit [CompleteSpace E] in
theorem Dt_eq_covDerivAlong (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (J : Set ℝ) (V : c.Field (I := I)) (x t : ℝ) (ht : J ∈ 𝓝 t) :
    c.Dt g J V x t = covDerivAlong (g t) (c.lift x) (V x) t := by
  simp only [Dt, covDerivAlong, chartCovDerivAlong, derivWithin_of_mem_nhds ht]

end CurveMap

variable [SigmaCompactSpace M] [T2Space M]


def connectionVariation (G : SolutionFamily (I := I) (M := M)) (J : Set ℝ)
    (t : ℝ) (p : M) (A B : TangentSpace I p) : TangentSpace I p :=
  derivWithin (fun s => G.connection s (tangentConstAt (I := I) p B) p A) J t

def nablaRicci (G : SolutionFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (A B Z : TangentSpace I p) : ℝ :=
  totalNabla0SFun 2 (G.connection t) (G.ricci t) p (Fin.cons A (vec2 B Z))

def riemannVector (G : SolutionFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (A B Z : TangentSpace I p) : TangentSpace I p :=
  connectionRiemannCurvatureField (G.connection t)
    (tangentConstAt (I := I) p A) (tangentConstAt (I := I) p B)
    (tangentConstAt (I := I) p Z) p

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem hasDerivWithinAt_of_metric_pairings
    (g : SmoothRiemannianMetric I M) (p : M) (V : ℝ → TangentSpace I p)
    (Z : TangentSpace I p) {J : Set ℝ} {t : ℝ}
    (h : ∀ w : TangentSpace I p,
      HasDerivWithinAt (fun r => g.inner p (V r) w) (g.inner p Z w) J t) :
    HasDerivWithinAt V Z J t := by
  classical
  let : FiniteDimensional ℝ (TangentSpace I p) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TangentSpace I p)
  have hrec (w : TangentSpace I p) :
      (∑ i, g.inner p w (metricSharp g p (b.coord i)) • b i) = w := by
    simp only [inner_metricSharp_right]
    exact b.sum_repr w
  have hsum := HasDerivWithinAt.fun_sum (u := Finset.univ)
    (fun i _ => (h (metricSharp g p (b.coord i))).smul_const (b i))
  simpa only [hrec] using hsum

variable [hBoundary : I.Boundaryless]
include hBoundary

omit [SigmaCompactSpace M] in
private theorem hasDerivWithinAt_spatialConnection {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b) (t : ℝ) (ht : t ∈ Icc a b)
    (p : M) (A V : TangentSpace I p) :
    HasDerivWithinAt
      (fun r => B.family.connection r (tangentConstAt (I := I) p V) p A)
      (connectionVariationSpeed (show SolutionOn (I := I) (M := M) D from ⟨B.family⟩)
        t p V A) (Icc a b) t := by
  let S : SolutionOn (I := I) (M := M) D := ⟨B.family⟩
  let delta : ℝ → TangentSpace I p := fun r =>
    CovariantDerivative.difference (LeviCivita (S.base.metric r))
      (LeviCivita (S.base.metric 0)) p V A
  let Z := connectionVariationSpeed S t p V A
  have hvec : HasDerivWithinAt delta Z (Icc a b) t :=
    hasDerivWithinAt_of_metric_pairings (S.base.metric 0) p delta Z
      (fun w => hasDerivWithinAt_connectionDifference_pairing S B.equation
        (B.regular.trans D.regular_subset) (B.regular ht) p V A w)
  let fixed := B.family.connection 0 (tangentConstAt (I := I) p V) p A
  have hdelta (r : ℝ) : delta r =
      B.family.connection r (tangentConstAt (I := I) p V) p A - fixed := by
    have h := DifferentialGeometry.PDE.DeTurck.connectionDifference_apply
      (S.base.metric r) (S.base.metric 0)
      (mdifferentiableAt_tangentConstAt_self (I := I) p V) A
    simpa only [DifferentialGeometry.PDE.DeTurck.connectionDifference,
      tangentConstAt_self, delta, fixed, S, SolutionFamily.connection, LeviCivita] using h
  have hsum := hvec.add_const fixed
  have hf : (fun r => delta r + fixed) =
      (fun r => B.family.connection r (tangentConstAt (I := I) p V) p A) := by
    funext r
    rw [hdelta, sub_add_cancel]
  rw [hf] at hsum
  exact hsum

omit [SigmaCompactSpace M] in
private theorem connectionVariation_eq_nativeSpeed {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b) (t : ℝ) (ht : t ∈ Icc a b)
    (p : M) (A V : TangentSpace I p) :
    connectionVariation B.family (Icc a b) t p A V =
      connectionVariationSpeed (show SolutionOn (I := I) (M := M) D from ⟨B.family⟩)
        t p V A :=
  (hasDerivWithinAt_spatialConnection B t ht p A V).derivWithin
    ((uniqueDiffOn_Icc B.lt) t ht)

omit [SigmaCompactSpace M] hBoundary in
private theorem nablaRicci_eq_metricNablaRic
    (G : SolutionFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (A V Z : TangentSpace I p) :
    nablaRicci G t p A V Z = metricNablaRic (G.metric t) p (vec3 A V Z) := by
  change metricNablaRic (G.metric t) p (Fin.cons A (vec2 V Z)) = _
  congr 1
  funext i
  fin_cases i <;> rfl

omit [SigmaCompactSpace M] hBoundary in
private theorem nablaRicci_last_two_symm
    (G : SolutionFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (A V Z : TangentSpace I p) : nablaRicci G t p A V Z = nablaRicci G t p A Z V := by
  simpa only [nablaRicci_eq_metricNablaRic] using
    metricNablaRic_last_two_symm (G.metric t) p A V Z

omit [SigmaCompactSpace M] in
theorem rfs_csf_connection [_sigmaCompactM : SigmaCompactSpace M]
    {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b) (t : ℝ) (ht : t ∈ Icc a b)
    (p : M) (A V Z : TangentSpace I p) :
    (B.family.metric t).inner p (connectionVariation B.family (Icc a b) t p A V) Z =
      -nablaRicci B.family t p A V Z - nablaRicci B.family t p V A Z +
        nablaRicci B.family t p Z A V := by
  rw [connectionVariation_eq_nativeSpeed B t ht p A V]
  have hpair :
      (B.family.metric t).inner p
        (connectionVariationSpeed (show SolutionOn (I := I) (M := M) D from ⟨B.family⟩)
          t p V A) Z =
      -nablaRicci B.family t p V A Z - nablaRicci B.family t p A V Z +
        nablaRicci B.family t p Z V A := by
    simp only [nablaRicci_eq_metricNablaRic]
    exact inner_metricSharp (B.family.metric t) p
      (koszulRicciCovector
        (DifferentialGeometry.PDE.RicciFlow.nablaRicci
          (show SolutionOn (I := I) (M := M) D from ⟨B.family⟩) t p) V A) Z
  rw [hpair, nablaRicci_last_two_symm B.family t p Z V A]
  ring


theorem connectionVariation_tensor {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b) (t : ℝ) (ht : t ∈ Icc a b)
    (p : M) :
    (∀ A V, connectionVariation B.family (Icc a b) t p A V =
      connectionVariation B.family (Icc a b) t p V A) ∧
    (∀ A A' V, connectionVariation B.family (Icc a b) t p (A + A') V =
      connectionVariation B.family (Icc a b) t p A V +
      connectionVariation B.family (Icc a b) t p A' V) ∧
    (∀ (r : ℝ) A V, connectionVariation B.family (Icc a b) t p (r • A) V =
      r • connectionVariation B.family (Icc a b) t p A V) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A V
    apply metricFlatLinear_injective (B.family.metric t) p
    ext Z
    change (B.family.metric t).inner p (connectionVariation B.family (Icc a b) t p A V) Z =
      (B.family.metric t).inner p (connectionVariation B.family (Icc a b) t p V A) Z
    rw [rfs_csf_connection B t ht p A V Z, rfs_csf_connection B t ht p V A Z,
      nablaRicci_last_two_symm B.family t p Z V A]
    ring
  · intro A A' V
    unfold connectionVariation
    simp only [map_add]
    exact derivWithin_fun_add
      (hasDerivWithinAt_spatialConnection B t ht p A V).differentiableWithinAt
      (hasDerivWithinAt_spatialConnection B t ht p A' V).differentiableWithinAt
  · intro r A V
    unfold connectionVariation
    simp only [map_smul]
    exact derivWithin_fun_const_smul r
      (hasDerivWithinAt_spatialConnection B t ht p A V).differentiableWithinAt

theorem moving_inner_derivative {D : RealTimeInterval} {a b s u : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.SmoothOn (I := I) (Icc s u))
    (V W : c.Field (I := I)) (hV : V.SmoothOn (I := I) (Icc s u))
    (hW : W.SmoothOn (I := I) (Icc s u)) (x t : ℝ) (ht : t ∈ Icc s u) :
    derivWithin (fun r => (B.family.metric r).inner (c.lift x r) (V x r) (W x r))
      (Icc s u) t =
      (B.family.metric t).inner (c.lift x t) (c.Dt B.family.metric (Icc s u) V x t) (W x t) +
      (B.family.metric t).inner (c.lift x t) (V x t) (c.Dt B.family.metric (Icc s u) W x t) -
      2 * B.family.ricciAt t (c.lift x t) (vec2 (V x t) (W x t)) := by
  sorry

theorem pullback_commutator {D : RealTimeInterval} {a b s u : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.SmoothOn (I := I) (Icc s u))
    (V : c.Field (I := I)) (hV : V.SmoothOn (I := I) (Icc s u))
    (x t : ℝ) (ht : t ∈ Icc s u) :
    c.Dt B.family.metric (Icc s u) (c.Dx B.family.metric V) x t -
      c.Dx B.family.metric (c.Dt B.family.metric (Icc s u) V) x t =
    riemannVector B.family t (c.lift x t) (c.velocity (Icc s u) x t) (c.X x t) (V x t) +
      connectionVariation B.family (Icc s u) t (c.lift x t) (c.X x t) (V x t) := by
  sorry

theorem pullback_torsion_free {D : RealTimeInterval} {a b s u : ℝ}
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.SmoothOn (I := I) (Icc s u))
    (x t : ℝ) (ht : t ∈ Icc s u) :
    c.Dt B.family.metric (Icc s u) c.X x t =
      c.Dx B.family.metric (c.velocity (Icc s u)) x t := by
  sorry

omit [CompleteSpace E] in
theorem CurveMap.Dt_eq_covDerivAlong_of_mem_Ioo (c : CurveMap M)
    (g : ℝ → SmoothRiemannianMetric I M) (V : c.Field (I := I))
    {s u x t : ℝ} (ht : t ∈ Ioo s u) :
    c.Dt g (Icc s u) V x t = covDerivAlong (g t) (c.lift x) (V x) t :=
  CurveMap.Dt_eq_covDerivAlong c g (Icc s u) V x t (Icc_mem_nhds ht.1 ht.2)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
