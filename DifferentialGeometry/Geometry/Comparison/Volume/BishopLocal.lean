import DifferentialGeometry.Geometry.Comparison.Volume.BishopBall
import DifferentialGeometry.Geometry.Comparison.Volume.BallVolume
import DifferentialGeometry.Geometry.Comparison.GeodesicConvexity
import DifferentialGeometry.Geometry.Comparison.InjectivityRadius

/-!
# Local Bishop comparison for intrinsic metric balls

This file identifies sufficiently small framed normal balls with intrinsic
Riemannian-distance balls and transfers the normal-ball comparison theorem.
No cut-time or cut-locus measurability is used.
-/

noncomputable section

open Metric Set Bundle
open scoped ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Below the named realized/intrinsic exponential agreement radius, the
framed normal image of a center-metric tangent ball is the intrinsic distance
ball with the same radius. -/
theorem framedBall_eq_small
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {R : Real} (hR : 0 < R)
    (hRexp : R < expDiffeoRadius (I := I) g hEnorm p) :
    framedExpDiffeo (I := I) g p '' ball (0 : E) R =
      smallNormalBall (I := I) p R := by
  classical
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hzNorm : ‖z‖ < R := by
      simpa only [mem_ball, dist_zero_right] using hz
    have hzExp : ‖z‖ < expDiffeoRadius (I := I) g hEnorm p :=
      hzNorm.trans hRexp
    have hvExp : Real.sqrt
        (g.inner p (normalFrame (I := I) g p z)
          (normalFrame (I := I) g p z)) <
        expDiffeoRadius (I := I) g hEnorm p := by
      simpa only [normalFrame_sqrt] using hzExp
    have hvSrc := expDiffeo_mem_of_lt (I := I) g hEnorm p hvExp
    have hvGp : Real.sqrt
        (g.inner p (normalFrame (I := I) g p z)
          (normalFrame (I := I) g p z)) < expRadiusGp (I := I) g p :=
      hvExp.trans_le (min_le_right _ _)
    rw [mem_smallNormalBall, framedExp_apply,
      expMapDiffeo_apply_eq (I := I) g p hvSrc,
      edist_exp_eq_radius (I := I) g p hEnorm hvGp,
      normalFrame_sqrt]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg z)).2 hzNorm
  · intro hq
    obtain ⟨v, hvExp, hvLen⟩ :=
      hopf_rinow_expMapIntrinsic_surjective_minimizing (I := I) g hEnorm p q
    have hdist : (Manifold.riemannianEDist I p q).toReal < R := by
      have hlt := (ENNReal.toReal_lt_toReal
        (riemannianEDist_ne_top (I := I) p q) ENNReal.ofReal_ne_top).2 hq
      simpa only [ENNReal.toReal_ofReal hR.le] using hlt
    have hvSmall : Real.sqrt (g.inner p (v : E) (v : E)) <
        expDiffeoRadius (I := I) g hEnorm p := by
      rw [hvLen]
      exact hdist.trans hRexp
    let z : E := (normalFrame (I := I) g p).symm v
    have hzFrame : normalFrame (I := I) g p z = v := by
      exact (normalFrame (I := I) g p).apply_symm_apply v
    have hzNorm : ‖z‖ = Real.sqrt (g.inner p (v : E) (v : E)) := by
      have h := normalFrame_sqrt (I := I) g p z
      rw [hzFrame] at h
      exact h.symm
    have hzBall : z ∈ ball (0 : E) R := by
      rw [mem_ball, dist_zero_right, hzNorm, hvLen]
      exact hdist
    refine ⟨z, hzBall, ?_⟩
    rw [framedExp_apply, hzFrame,
      expDiffeo_eq_intr (I := I) g hEnorm p hvSmall, hvExp]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Volume of a ball for the canonical Hopf--Rinow realization of the
Riemannian distance. -/
def localBallVolume
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) (R : Real) : ENNReal :=
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  riemannianVolumeMeasure (I := I) (M := M) g (ball p R)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Below the realized exponential agreement radius, metric-ball volume and
framed normal-ball volume agree. -/
theorem localBall_eq_normal
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {R : Real} (hR : 0 < R)
    (hRexp : R < expDiffeoRadius (I := I) g hEnorm p) :
    localBallVolume (I := I) g p R = normalBallVolume (I := I) g p R := by
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  have hball : ball p R = smallNormalBall (I := I) p R :=
    Set.Subset.antisymm
      (metricBall_subset_smallNormalBall (I := I) (M := M))
      (smallNormalBall_subset_metricBall (I := I) (M := M))
  rw [localBallVolume, normalBallVolume, hball]
  congr 1
  exact (framedBall_eq_small (I := I) g hEnorm p hR hRexp).symm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Local Bishop comparison for intrinsic metric balls.  The returned radius
lies strictly below the injectivity radius, but also records the smaller local
analytic radius currently supplied by the radial Jacobi comparison. -/
theorem localBall_cross
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (q : Real) (hq : 0 ≤ q)
    (hd : 0 < Module.finrank Real E - 1)
    (hRic : BonnetMyers.RicciBoundedBelow (I := I) g
      (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2))) :
    ∃ ρ : Real, 0 < ρ ∧
      ENNReal.ofReal ρ < injRadius (I := I) g p ∧
      ∀ {r R : Real}, 0 < r → r ≤ R → R < ρ →
        localBallVolume (I := I) g p R *
            ENNReal.ofReal (hypRadVol q (Module.finrank Real E - 1) r) ≤
          localBallVolume (I := I) g p r *
            ENNReal.ofReal (hypRadVol q (Module.finrank Real E - 1) R) := by
  obtain ⟨ρc, hρc, hcross⟩ :=
    normalBall_cross (I := I) g hEnorm p q hq hd hRic
  obtain ⟨ri, hri, hiinj⟩ :=
    exists_pos_injOn_metric_ball (I := I) g p
  let re : Real := expDiffeoRadius (I := I) g hEnorm p
  let a : Real := min ρc (min re ri)
  let ρ : Real := a / 2
  have hre : 0 < re := by
    simpa only [re] using expDiffeoRadius_pos (I := I) g hEnorm p
  have ha : 0 < a := by
    simpa only [a] using lt_min hρc (lt_min hre hri)
  have hρ : 0 < ρ := by
    simpa only [ρ] using div_pos ha (by norm_num : (0 : Real) < 2)
  have hρa : ρ < a := by
    dsimp only [ρ]
    linarith
  have hρc' : ρ < ρc := hρa.trans_le (min_le_left _ _)
  have hρre : ρ < re :=
    hρa.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hρri : ρ < ri :=
    hρa.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hriMem : ENNReal.ofReal ri ∈ injRadiusSet (I := I) g p := by
    rw [mem_injRadiusSet_iff]
    rw [Metric.eball_ofReal]
    exact hiinj
  have hρinj : ENNReal.ofReal ρ < injRadius (I := I) g p := by
    exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hρ.le).2 hρri).trans_le
      (le_injRadius_of_mem (I := I) g p hriMem)
  refine ⟨ρ, hρ, hρinj, ?_⟩
  intro r R hr hrR hRρ
  have hR : 0 < R := hr.trans_le hrR
  have hRexp : R < expDiffeoRadius (I := I) g hEnorm p := by
    simpa only [re] using hRρ.trans hρre
  have hrexp : r < expDiffeoRadius (I := I) g hEnorm p :=
    hrR.trans_lt hRexp
  rw [localBall_eq_normal (I := I) g hEnorm p hR hRexp,
    localBall_eq_normal (I := I) g hEnorm p hr hrexp]
  exact hcross hr hrR (hRρ.trans hρc')

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The intrinsic metric-ball volume divided by the hyperbolic model volume is
antitone on one center-dependent interval below the injectivity radius. -/
theorem localBall_ratio
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T3Space M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (q : Real) (hq : 0 ≤ q)
    (hd : 0 < Module.finrank Real E - 1)
    (hRic : BonnetMyers.RicciBoundedBelow (I := I) g
      (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2))) :
    ∃ ρ : Real, 0 < ρ ∧
      ENNReal.ofReal ρ < injRadius (I := I) g p ∧
      AntitoneOn
        (fun R => localBallVolume (I := I) g p R /
          ENNReal.ofReal (hypRadVol q (Module.finrank Real E - 1) R))
        (Ioo (0 : Real) ρ) := by
  obtain ⟨ρ, hρ, hρinj, hcross⟩ :=
    localBall_cross (I := I) g hEnorm p q hq hd hRic
  refine ⟨ρ, hρ, hρinj, ?_⟩
  intro r hr R hR hrR
  have hmr : 0 < hypRadVol q (Module.finrank Real E - 1) r :=
    hypRadVol_pos hq hr.1
  have hmR : 0 < hypRadVol q (Module.finrank Real E - 1) R :=
    hypRadVol_pos hq hR.1
  have hmr0 : ENNReal.ofReal
      (hypRadVol q (Module.finrank Real E - 1) r) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hmr
  have hmR0 : ENNReal.ofReal
      (hypRadVol q (Module.finrank Real E - 1) R) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hmR
  rw [ENNReal.div_le_iff hmR0 ENNReal.ofReal_ne_top]
  rw [← ENNReal.mul_div_right_comm]
  rw [ENNReal.le_div_iff_mul_le (Or.inl hmr0) (Or.inl ENNReal.ofReal_ne_top)]
  exact hcross hr.1 hrR hR.2

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

end
