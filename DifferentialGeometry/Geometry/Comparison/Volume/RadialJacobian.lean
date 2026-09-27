import DifferentialGeometry.Geometry.Comparison.Volume.PolarCoordinates
import DifferentialGeometry.Geometry.Comparison.Volume.RadialComparison

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.Volume
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

def radialJacobianInFrame
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p)
    (v : Fin (Module.finrank ℝ E - 1) → TangentSpace I p)
    (t : ℝ) : ℝ :=
  curveDensity (I := I) g
    (intrinsicGeodesic (I := I) g hEnorm p u)
    (fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)) t

theorem radialJacobianComparisonInFrame [_hConnected : ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (_hn : 2 ≤ Module.finrank ℝ E)
    (p : M) (u : gUnitTangentSphere (I := I) g p)
    (K L : ℝ) (hL : 0 < L)
    (hLcut : ENNReal.ofReal L < cutTime (I := I) g hEnorm p u)
    (hconj : 0 < K → L < Real.pi / Real.sqrt K)
    (v : Fin (Module.finrank ℝ E - 1) → TangentSpace I p)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0)
    (hperp : ∀ i, g.inner p (u : TangentSpace I p) (v i) = 0)
    (hRic :
      let γ := intrinsicGeodesic (I := I) g hEnorm p
        (u : TangentSpace I p)
      ∀ t ∈ Set.Ioo (0 : ℝ) L,
        (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * K) ≤
          ricciTensor (I := I) g (γ t)
            (curveVelocity (I := I) γ t)
            (curveVelocity (I := I) γ t)) :
    AntitoneOn
        (fun t => radialJacobianInFrame (I := I) g hEnorm p u v t /
          modelDensity K (Module.finrank ℝ E - 1) t)
        (Set.Ioo (0 : ℝ) L) ∧
      Tendsto
        (fun t => radialJacobianInFrame (I := I) g hEnorm p u v t /
          modelDensity K (Module.finrank ℝ E - 1) t)
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hd : 0 < Module.finrank ℝ E - 1 := by omega
  have hadm : ∀ t ∈ Set.Ioo (0 : ℝ) L, modelRadiusAdmissible K t := by
    intro t ht
    exact ⟨ht.1, fun hK => ht.2.trans (hconj hK)⟩
  have hno : ∀ t ∈ Set.Ioo (0 : ℝ) L,
      ¬ IsConjVec (I := I) g hEnorm p
        ((t • (u : TangentSpace I p) : TangentSpace I p) : E) := by
    intro t ht
    have htL : ENNReal.ofReal t < ENNReal.ofReal L :=
      (ENNReal.ofReal_lt_ofReal_iff hL).2 ht.2
    have htcut : ENNReal.ofReal t < cutTime (I := I) g hEnorm p u :=
      htL.trans hLcut
    have hseg : t • (u : TangentSpace I p) ∈
        DifferentialGeometry.Geometry.Riemannian.VolumeComparison.SegmentInt
          (I := I) g hEnorm p :=
      (ofReal_lt_cutTime_iff_smul_mem_segInt
        (I := I) g hEnorm p u ht.1).mp htcut
    exact DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segmentInt_no_conj
      (I := I) g hEnorm hseg
  have hspeed :
      let γ := intrinsicGeodesic (I := I) g hEnorm p
        (u : TangentSpace I p)
      ∀ t ∈ Set.Ioo (0 : ℝ) L,
        g.inner (γ t) (curveVelocity (I := I) γ t)
          (curveVelocity (I := I) γ t) = 1 := by
    dsimp only
    intro t _ht
    calc
      g.inner (intrinsicGeodesic (I := I) g hEnorm p u t)
          (curveVelocity (I := I)
            (intrinsicGeodesic (I := I) g hEnorm p u) t)
          (curveVelocity (I := I)
            (intrinsicGeodesic (I := I) g hEnorm p u) t) =
          g.inner p (u : TangentSpace I p) u := by
        change g.inner (intrinsicGeodesic (I := I) g hEnorm p u t)
          (mfderiv 𝓘(ℝ, ℝ) I
            (intrinsicGeodesic (I := I) g hEnorm p u) t 1)
          (mfderiv 𝓘(ℝ, ℝ) I
            (intrinsicGeodesic (I := I) g hEnorm p u) t 1) =
            g.inner p (u : TangentSpace I p) u
        exact intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p u t
      _ = 1 := u.property
  have hRic' :
      let γ := intrinsicGeodesic (I := I) g hEnorm p
        (u : TangentSpace I p)
      ∀ t ∈ Set.Ioo (0 : ℝ) L,
        (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * K) *
            g.inner (γ t) (curveVelocity (I := I) γ t)
              (curveVelocity (I := I) γ t) ≤
          ricciTensor (I := I) g (γ t)
            (curveVelocity (I := I) γ t)
            (curveVelocity (I := I) γ t) := by
    dsimp only
    intro t ht
    rw [hspeed t ht, mul_one]
    exact hRic t ht
  have hanti := intrModelRatioOfFrame_on
    (I := I) g hEnorm p (u : TangentSpace I p) K L u.property hd hadm
      v hON hperp hno hRic'
  have hlim := modelPoleLimit
    (I := I) g hEnorm p (u : TangentSpace I p) K v hON
  simpa only [radialJacobianInFrame] using And.intro hanti hlim

omit [T2Space (TangentBundle I M)] in
theorem normalPolarJacobian_eq_radialJacobianInFrame
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : Metric.sphere (0 : E) 1)
    (v : Fin (Module.finrank ℝ E - 1) → TangentSpace I p)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0)
    (hperp : ∀ i,
      g.inner p (normalFrame (I := I) (E := E) g p (u : E)) (v i) = 0)
    {t : ℝ} (ht : 0 < t) :
    normalPolarJacobian (I := I) g hEnorm p t u =
      radialJacobianInFrame (I := I) g hEnorm p
        (normalUnitTangent (I := I) g p u) v t := by
  have hu : 0 < g.inner p
      (normalFrame (I := I) (E := E) g p (u : E))
      (normalFrame (I := I) (E := E) g p (u : E)) := by
    rw [normalFrame_inner, real_inner_self_eq_norm_sq]
    have hunorm : ‖(u : E)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using u.property
    rw [hunorm, one_pow]
    norm_num
  have hscale := expDens_scale (I := I) g hEnorm p
    (normalFrame (I := I) (E := E) g p (u : E)) hu
    (normalBasis (I := I) g p) (normalBasis_inner (I := I) g p)
    v hON hperp ht
  have hmap : normalFrame (I := I) (E := E) g p (t • (u : E)) =
      t • normalFrame (I := I) (E := E) g p (u : E) :=
    (normalFrame (I := I) (E := E) g p).map_smul t (u : E)
  rw [normalPolarJacobian, normalExpJacobian, radialJacobianInFrame, hmap]
  exact hscale

theorem radialJacobianComparison [_hConnected : ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (_hn : 2 ≤ Module.finrank ℝ E)
    (p : M) (u : Metric.sphere (0 : E) 1)
    (K L : ℝ) (hL : 0 < L)
    (hLcut : ENNReal.ofReal L < cutTime (I := I) g hEnorm p
      (normalUnitTangent (I := I) g p u))
    (hconj : 0 < K → L < Real.pi / Real.sqrt K)
    (hRic :
      let γ := intrinsicGeodesic (I := I) g hEnorm p
        (normalUnitTangent (I := I) g p u : TangentSpace I p)
      ∀ t ∈ Set.Ioo (0 : ℝ) L,
        (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * K) ≤
          ricciTensor (I := I) g (γ t)
            (curveVelocity (I := I) γ t)
            (curveVelocity (I := I) γ t)) :
    AntitoneOn
        (fun t => normalPolarJacobian (I := I) g hEnorm p t u /
          modelDensity K (Module.finrank ℝ E - 1) t)
        (Set.Ioo (0 : ℝ) L) ∧
      Tendsto
        (fun t => normalPolarJacobian (I := I) g hEnorm p t u /
          modelDensity K (Module.finrank ℝ E - 1) t)
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  let uT : TangentSpace I p := normalUnitTangent (I := I) g p u
  have huT : g.inner p uT uT = 1 :=
    (normalUnitTangent (I := I) g p u).property
  obtain ⟨v, hON, hperp'⟩ := exists_ortho_perp (I := I) g p uT huT
  have hperp : ∀ i, g.inner p uT (v i) = 0 := by
    intro i
    rw [g.symm p uT (v i)]
    exact hperp' i
  have hframe := radialJacobianComparisonInFrame
    (I := I) g hEnorm _hn p
    (normalUnitTangent (I := I) g p u) K L hL hLcut hconj
    v hON hperp hRic
  have hbridge : ∀ t : ℝ, 0 < t →
      normalPolarJacobian (I := I) g hEnorm p t u =
        radialJacobianInFrame (I := I) g hEnorm p
          (normalUnitTangent (I := I) g p u) v t := by
    intro t ht
    exact normalPolarJacobian_eq_radialJacobianInFrame
      (I := I) g hEnorm p u v hON hperp ht
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab
    change normalPolarJacobian (I := I) g hEnorm p b u /
        modelDensity K (Module.finrank ℝ E - 1) b ≤
      normalPolarJacobian (I := I) g hEnorm p a u /
        modelDensity K (Module.finrank ℝ E - 1) a
    rw [hbridge b hb.1, hbridge a ha.1]
    exact hframe.1 ha hb hab
  · apply hframe.2.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [hbridge t ht]

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
