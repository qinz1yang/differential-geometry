import DifferentialGeometry.Geometry.Comparison.CheegerGromovTaylor.InjectivityRadius
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.BallEuclideanUpper
import DifferentialGeometry.Geometry.Exponential.Intrinsic.FramedCoordinates
import DifferentialGeometry.Geometry.Exponential.Intrinsic.FramedJacobi

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold MeasureTheory Metric Set
open scoped ENNReal Manifold

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [CompleteSpace E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (↑(⊤ : ℕ∞) : WithTop ℕ∞) M]
  [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [ConnectedSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

theorem intrInj_ge_vol
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) {K R r₀ s q : Real} {v : ENNReal}
    (hK : 0 < K) (hR : 0 < R)
    (hRpi : R ≤ Real.pi / Real.sqrt K)
    (hRmBall :
      ∀ y : M, y ∈ Metric.eball p (ENNReal.ofReal (3 * R / 4)) →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          y 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g y)) ≤ K)
    (hloc :
      IsLocalDiffeomorphOn (modelWithCornersSelf Real E) I
        (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (intrinsicFramedExp (I := I) g hEnorm p)
        (ball (0 : E) R))
    (hr₀ : 0 < r₀) (hs : 0 < s)
    (hfit : r₀ + 2 * s < R) (hquarter : r₀ < R / 4)
    (hq : 0 ≤ q)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2)))
    (hvol : v ≤ riemannianVolumeMeasure (I := I) (M := M) g
      {y : M | riemannianEDist I p y < ENNReal.ofReal s}) :
    ENNReal.ofReal (r₀ / 2) * v /
        (((volume : Measure
            (EuclideanSpace Real (Fin (Module.finrank Real E)))).toSphere Set.univ) *
          ENNReal.ofReal (hypRadVol q (Module.finrank Real E - 1) s) +
        (volume : Measure E).toSphere Set.univ *
          ENNReal.ofReal (hypRadVol q (Module.finrank Real E - 1) (r₀ + s)))
      ≤ intrInjRadius (I := I) g hEnorm p := by
  classical
  let V : ENNReal :=
    riemannianVolumeMeasure (I := I) (M := M) g
      {y : M | riemannianEDist I p y < ENNReal.ofReal s}
  let P : ENNReal := intrPullVol (I := I) g hEnorm p (r₀ + s)
  let D : ENNReal :=
    ((volume : Measure
        (EuclideanSpace Real (Fin (Module.finrank Real E)))).toSphere Set.univ) *
      ENNReal.ofReal (hypRadVol q (Module.finrank Real E - 1) s) +
    (volume : Measure E).toSphere Set.univ *
      ENNReal.ofReal (hypRadVol q (Module.finrank Real E - 1) (r₀ + s))
  have hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K := by
    intro z hz
    exact hRmBall _ (intrFrame_mem_eball (I := I) g hEnorm p hz)
  have hno : ∀ z, z ∈ ball (0 : E) (r₀ + s) → z ≠ 0 →
      ∀ t, t ∈ Ioo (0 : Real) 1 →
        ¬ IsConjVec (I := I) g hEnorm p
          ((t • normalFrame (I := I) g p z : TangentSpace I p) : E) := by
    intro z hz hz0 t ht
    have htz : t • z ∈ ball (0 : E) R := by
      rw [Metric.mem_ball, dist_zero_right] at hz ⊢
      rw [norm_smul, Real.norm_of_nonneg ht.1.le]
      calc
        t * ‖z‖ < 1 * ‖z‖ :=
          mul_lt_mul_of_pos_right ht.2 (norm_pos_iff.mpr hz0)
        _ = ‖z‖ := one_mul _
        _ < r₀ + s := hz
        _ < R := by linarith
    have hraw := framedExp_not_conj (I := I) g hEnorm p (t • z)
      (hloc ⟨t • z, htz⟩)
    simpa only [map_smul] using hraw
  have hvolV : v ≤ V := by
    simpa only [V] using hvol
  have hV :
      V ≤ ((volume : Measure
          (EuclideanSpace Real (Fin (Module.finrank Real E)))).toSphere Set.univ) *
        ENNReal.ofReal (hypRadVol q (Module.finrank Real E - 1) s) := by
    simpa only [V] using
      (segBall_vol_le_euclidean (I := I) g hEnorm p hq hs hRic)
  have hP :
      P ≤ (volume : Measure E).toSphere Set.univ *
        ENNReal.ofReal
          (hypRadVol q (Module.finrank Real E - 1) (r₀ + s)) := by
    simpa only [P] using
      (intrPullVol_le_hyp (I := I) g hEnorm p hq
        (add_pos hr₀ hs) hno hRic)
  have hDen : V + P ≤ D := by
    simpa only [D] using add_le_add hV hP
  have hcgt :
      ENNReal.ofReal (r₀ / 2) * V / (V + P) ≤
        intrInjRadius (I := I) g hEnorm p := by
    simpa only [V, P] using
      (intrInj_ge_cgt_on (I := I) (K := K) (R := R) (r₀ := r₀)
        (s := s) g hEnorm p hK hR hRpi hRm hloc hr₀ hs hfit hquarter)
  change ENNReal.ofReal (r₀ / 2) * v / D ≤
    intrInjRadius (I := I) g hEnorm p
  exact
    (ENNReal.div_le_div
      (mul_le_mul_right hvolV (ENNReal.ofReal (r₀ / 2))) hDen).trans hcgt

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
