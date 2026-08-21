import DifferentialGeometry.Geometry.Comparison.Volume.JacobianBounds
import DifferentialGeometry.Geometry.Comparison.GeodesicConvexity
import DifferentialGeometry.Geometry.Exponential.IntrinsicBallChart

set_option autoImplicit false

noncomputable section

open scoped ContDiff ENNReal Manifold Matrix

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open Bundle MeasureTheory Metric Set
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

private local instance : CompleteSpace E :=
  FiniteDimensional.complete Real E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

noncomputable def modelCoeffMin : Real :=
  (‖(toEuclidean (E := E) : E →L[Real]
      EuclideanSpace Real (Fin (Module.finrank Real E)))‖ + 1)⁻¹

omit [NeZero (Module.finrank Real E)] in
theorem modelCoeffMin_pos : 0 < modelCoeffMin (E := E) := by
  apply inv_pos.mpr
  exact add_pos_of_nonneg_of_pos (norm_nonneg _) one_pos

omit [NeZero (Module.finrank Real E)] in
theorem modelCoeffMin_le
    (v : EuclideanSpace Real (Fin (Module.finrank Real E)))
    (hv : ‖v‖ = 1) :
    modelCoeffMin (E := E) ≤
      ‖∑ i, v i • (chartModelBasis E) i‖ := by
  let L : E →L[Real] EuclideanSpace Real (Fin (Module.finrank Real E)) :=
    (toEuclidean (E := E)).toContinuousLinearMap
  let K : Real := ‖L‖ + 1
  let w : E := (toEuclidean (E := E)).symm v
  have hK : 0 < K :=
    add_pos_of_nonneg_of_pos (norm_nonneg L) one_pos
  have hanti :=
    (ContinuousLinearEquiv.antilipschitz
      ((toEuclidean (E := E)).symm)).le_mul_dist v 0
  have hone : 1 ≤ K * ‖w‖ := by
    simp only [map_zero, dist_zero_right, hv] at hanti
    have hnorm_le : (↑‖L‖₊ : Real) ≤ K := by
      simp [K, L]
    exact hanti.trans
      (mul_le_mul_of_nonneg_right hnorm_le (norm_nonneg w))
  have hmin : K⁻¹ ≤ ‖w‖ := by
    have hdiv : 1 / K ≤ ‖w‖ :=
      (div_le_iff₀ hK).2 (by simpa [mul_comm] using hone)
    simpa only [one_div] using hdiv
  have hw :
      w = ∑ i, v i • (chartModelBasis E) i := by
    have hvsum :
        v = ∑ i, v i • EuclideanSpace.single i (1 : Real) := by
      let b :=
        (EuclideanSpace.basisFun
          (Fin (Module.finrank Real E)) Real).toBasis
      simpa [b, EuclideanSpace.basisFun_apply] using (b.sum_repr v).symm
    calc
      w = (toEuclidean (E := E)).symm v := rfl
      _ = (toEuclidean (E := E)).symm
          (∑ i, v i • EuclideanSpace.single i (1 : Real)) := by
            exact congrArg (toEuclidean (E := E)).symm hvsum
      _ = ∑ i, v i •
          (toEuclidean (E := E)).symm
            (EuclideanSpace.single i (1 : Real)) := by
            rw [map_sum]
            simp only [map_smul]
      _ = ∑ i, v i • (chartModelBasis E) i := by
            simp only [chartModelBasis_apply]
  simpa [modelCoeffMin, K, L, hw] using hmin

omit [NeZero (Module.finrank Real E)] [T2Space M] [SigmaCompactSpace M] in
omit [I.Boundaryless] [T2Space (TangentBundle I M)] in
theorem param_dens_ge
    (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p)
    (heq : c.MetricEquivOn g (Metric.ball (0 : E) c.radius))
    {z : E} (hz : z ∈ Metric.ball (0 : E) c.radius) :
    Real.sqrt
        (((1 / 2 : Real) * modelCoeffMin (E := E) ^ 2) ^
          Module.finrank Real E) ≤
      paramDensity (I := I) g c.hom z := by
  let a : Real := (1 / 2 : Real) * modelCoeffMin (E := E) ^ 2
  have ha : 0 ≤ a :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  have hgram :=
    paramGramMatrix_posDef (I := I) g c.hom (c.ball_subset hz)
  have hray :
      ∀ v : EuclideanSpace Real (Fin (Module.finrank Real E)),
        ‖v‖ = 1 →
        a ≤ RCLike.re
          (star (⇑v) ⬝ᵥ
            (paramGramMatrix (I := I) g c.hom z) *ᵥ (⇑v)) := by
    intro v hv
    let w : E := ∑ i, v i • (chartModelBasis E) i
    have hcoeff : modelCoeffMin (E := E) ≤ ‖w‖ :=
      modelCoeffMin_le (E := E) v hv
    have haw : a ≤ (1 / 2 : Real) * ‖w‖ ^ 2 := by
      dsimp only [a]
      nlinarith [modelCoeffMin_pos (E := E), norm_nonneg w]
    have hmetric :
        c.metric g z w w =
          g.inner (c.hom z)
            (∑ i, v i •
              mfderiv (modelWithCornersSelf Real E) I c.hom z
                ((chartModelBasis E) i))
            (∑ i, v i •
              mfderiv (modelWithCornersSelf Real E) I c.hom z
                ((chartModelBasis E) i)) := by
      have hD :
          mfderiv (modelWithCornersSelf Real E) I c.hom z w =
            ∑ i, v i •
              mfderiv (modelWithCornersSelf Real E) I c.hom z
                ((chartModelBasis E) i) := by
        change
          (mfderiv (modelWithCornersSelf Real E) I c.hom z)
              (∑ i, v i • (chartModelBasis E) i) =
            ∑ i, v i •
              (mfderiv (modelWithCornersSelf Real E) I c.hom z)
                ((chartModelBasis E) i)
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact ContinuousLinearMap.map_smul
          (mfderiv (modelWithCornersSelf Real E) I c.hom z)
          (v i) ((chartModelBasis E) i)
      rw [NormalBallChart.metric_apply]
      exact congrArg₂ (fun a b => g.inner (c.hom z) a b) hD hD
    have hquad :=
      paramGramMatrix_dotProduct_mulVec (I := I) g c.hom z (⇑v)
    have hfinal :
        a ≤ star (⇑v) ⬝ᵥ
          (paramGramMatrix (I := I) g c.hom z) *ᵥ (⇑v) := by
      calc
      a ≤ (1 / 2 : Real) * ‖w‖ ^ 2 := haw
      _ ≤ c.metric g z w w := (heq z hz w).1
      _ = g.inner (c.hom z)
          (∑ i, v i •
            mfderiv (modelWithCornersSelf Real E) I c.hom z
              ((chartModelBasis E) i))
          (∑ i, v i •
            mfderiv (modelWithCornersSelf Real E) I c.hom z
              ((chartModelBasis E) i)) := hmetric
      _ = star (⇑v) ⬝ᵥ
          (paramGramMatrix (I := I) g c.hom z) *ᵥ (⇑v) := hquad.symm
    simpa using hfinal
  simpa only [a, paramDensity_apply, Fintype.card_fin] using
    (sqrt_pow_le_sqrt_det_of_rayleigh
      (ι := Fin (Module.finrank Real E))
      (A := paramGramMatrix (I := I) g c.hom z) (a := a)
      hgram.posSemidef ha hray)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem intrBall_vol_ge
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {r : Real} (hr : 0 < r)
    (c : IntrinsicBallChart (I := I) g hEnorm p r)
    (hmetric : ∀ z ∈ Metric.ball (0 : E) r, ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤
          intrFrameMetric (I := I) g hEnorm p z v v ∧
        intrFrameMetric (I := I) g hEnorm p z v v ≤
          2 * ‖v‖ ^ 2) :
    ENNReal.ofReal
        (Real.sqrt
          (((1 / 2 : Real) * modelCoeffMin (E := E) ^ 2) ^
            Module.finrank Real E)) *
        (modelHaar (E := E)) (Metric.ball (0 : E) r) ≤
      riemannianVolumeMeasure (I := I) (M := M) g
        (smallNormalBall (I := I) p r) := by
  let nc : NormalBallChart (I := I) p :=
    c.toNormalBallChart (I := I) g hEnorm p hr
  have heq :
      nc.MetricEquivOn g (Metric.ball (0 : E) nc.radius) := by
    intro z hz v
    change z ∈ Metric.ball (0 : E) r at hz
    have hev :
        c.hom =ᶠ[nhds z]
          intrinsicFramedExp (I := I) g hEnorm p :=
      Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hz)
        (fun q hq => c.hom_eq hq)
    have hD :
        mfderiv (modelWithCornersSelf Real E) I c.hom z =
          mfderiv (modelWithCornersSelf Real E) I
            (intrinsicFramedExp (I := I) g hEnorm p) z :=
      Filter.EventuallyEq.mfderiv_eq
        (I := modelWithCornersSelf Real E) (I' := I) hev
    change
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤
          g.inner (c.hom z)
            (mfderiv (modelWithCornersSelf Real E) I c.hom z v)
            (mfderiv (modelWithCornersSelf Real E) I c.hom z v) ∧
        g.inner (c.hom z)
            (mfderiv (modelWithCornersSelf Real E) I c.hom z v)
            (mfderiv (modelWithCornersSelf Real E) I c.hom z v) ≤
          2 * ‖v‖ ^ 2
    rw [c.hom_eq hz, hD]
    simpa only [intrFrameMetric_apply] using hmetric z hz v
  have hparam :
      ENNReal.ofReal
          (Real.sqrt
            (((1 / 2 : Real) * modelCoeffMin (E := E) ^ 2) ^
              Module.finrank Real E)) *
          (modelHaar (E := E)) (Metric.ball (0 : E) r) ≤
        riemannianVolumeMeasure (I := I) (M := M) g
          (nc.hom '' Metric.ball (0 : E) r) := by
    apply param_vol_ge (I := I) g nc.hom measurableSet_ball
    · simpa only [nc, IntrinsicBallChart.toNormalBallChart] using
        nc.ball_subset
    · intro z hz
      apply param_dens_ge (I := I) g nc heq
      simpa only [nc, IntrinsicBallChart.toNormalBallChart] using hz
  have himage :
      nc.hom '' Metric.ball (0 : E) r ⊆
        smallNormalBall (I := I) p r := by
    rintro y ⟨z, hz, rfl⟩
    change c.hom z ∈ smallNormalBall (I := I) p r
    rw [c.hom_eq hz, intrFrame_apply, expMapIntrinsic_def]
    apply smallNormalBall_radial_confined (I := I) g hEnorm p
    · simpa only [normalFrame_sqrt, Metric.mem_ball, dist_zero_right] using hz
    · exact ⟨zero_le_one, le_rfl⟩
  exact hparam.trans (measure_mono himage)

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry
