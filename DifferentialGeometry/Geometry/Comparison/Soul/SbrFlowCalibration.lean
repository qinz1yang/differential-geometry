import DifferentialGeometry.Geometry.Comparison.Soul.SbrFlowUniqueness
import DifferentialGeometry.Geometry.Comparison.Soul.SbrRightTangent

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

variable (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
  {F : M → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
  (hconc : ∀ (p : M) (v : TangentSpace I p),
    ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm p v t)))

set_option backward.isDefEq.respectTransparency false in
theorem normalized_ascent_level_increment (eta : ℝ → M) {a b : ℝ}
    (heta : ContinuousOn eta (Icc a b))
    (hvelocity : ∀ t ∈ Ico a b,
      let G := intrinsicGeneralizedGradient g hEnorm hF hconc (eta t)
      G ≠ 0 ∧ HasMFDerivWithinAt 𝓘(ℝ, ℝ) I eta (Ici t) t
        (ContinuousLinearMap.toSpanSingleton ℝ ((g.inner (eta t) G G)⁻¹ • G))) :
    ∀ s ∈ Icc a b, F (eta s) = F (eta a) + (s - a) := by
  have hslopes : ∀ t ∈ Ico a b,
      Tendsto (fun u => slope (fun v => F (eta v)) t u) (𝓝[>] t) (𝓝 1) := by
    intro t ht
    let G := intrinsicGeneralizedGradient g hEnorm hF hconc (eta t)
    let V := (g.inner (eta t) G G)⁻¹ • G
    obtain ⟨hG, hder⟩ := hvelocity t ht
    have hnorm : 0 < g.inner (eta t) G G := g.pos (eta t) G hG
    have hD : intrinsicRightDerivative g hEnorm F (eta t) V = 1 := by
      dsimp only [V]
      rw [intrinsicRightDerivative_smul g hEnorm F (eta t) G (hconc (eta t) G)
        (inv_nonneg.mpr hnorm.le),
        (intrinsicGeneralizedGradient_spec g hEnorm hF hconc (eta t)).2,
        inv_mul_cancel₀ hnorm.ne']
    have houter : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I eta (Ici t) (0 + t)
        (ContinuousLinearMap.toSpanSingleton ℝ V) := by
      rw [zero_add]
      exact hder
    have htime : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (fun h : ℝ => h + t) (Ici 0) 0 (ContinuousLinearMap.id ℝ ℝ) :=
      ((hasFDerivAt_id (0 : ℝ)).add_const t).hasMFDerivAt.hasMFDerivWithinAt
    have hzero : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun h => eta (h + t)) (Ici 0) 0
        (ContinuousLinearMap.toSpanSingleton ℝ V) := by
      have hcomp := houter.comp (f := fun h : ℝ => h + t) 0 htime (by
        intro h hh
        change t ≤ h + t
        linarith [show 0 ≤ h from hh])
      convert! hcomp using 1
    have hquot : Tendsto (fun h => (F (eta (h + t)) - F (eta t)) / h)
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have hchain := tendsto_intrinsicRightDerivative_of_right_velocity
        g hEnorm hF hzero (hconc _ _)
      rw [zero_add] at hchain
      change Tendsto (fun h : ℝ => (F (eta (h + t)) - F (eta t)) / h)
        (𝓝[>] (0 : ℝ)) (𝓝 (intrinsicRightDerivative g hEnorm F (eta t) ((1 : ℝ) • V)))
        at hchain
      rw [one_smul, hD] at hchain
      exact hchain
    have hshift : Tendsto (fun u : ℝ => u - t) (𝓝[>] t) (𝓝[>] (0 : ℝ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · have hcontinuous : Continuous (fun u : ℝ => u - t) :=
          continuous_id.sub continuous_const
        simpa only [sub_self] using
          (hcontinuous.continuousAt (x := t)).tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with u hu
        change t < u at hu
        exact sub_pos.mpr hu
    simpa only [Function.comp_def, slope_def_field, sub_add_cancel] using hquot.comp hshift
  have hcont : ContinuousOn (fun t => F (eta t)) (Icc a b) :=
    hF.continuous.comp_continuousOn heta
  have hupper := image_le_affine_of_upper_right_slope_le (c := 1) hcont
    (fun t ht r hr => (hslopes t ht).eventually (gt_mem_nhds hr))
  have hnegSlopes : ∀ t ∈ Ico a b,
      Tendsto (fun u => slope (fun v => -F (eta v)) t u) (𝓝[>] t) (𝓝 (-1)) := by
    intro t ht
    convert! (hslopes t ht).neg using 1
    funext u
    simp only [slope_def_field]
    ring
  have hnegative := image_le_affine_of_upper_right_slope_le (c := -1) hcont.neg
    (fun t ht r hr => (hnegSlopes t ht).eventually (gt_mem_nhds hr))
  intro s hs
  have hhi := hupper s hs
  have hlo := hnegative s hs
  change -F (eta s) ≤ -F (eta a) + -1 * (s - a) at hlo
  linarith

theorem normalized_ascent_calibration_of_lt (eta : ℝ → M) {a b m : ℝ}
    (heta : ContinuousOn eta (Icc a b)) (hmax : ∃ q : M, F q = m)
    (hbelow : ∀ t ∈ Ico a b, F (eta t) < m)
    (hvelocity : ∀ t ∈ Ico a b,
      let G := intrinsicGeneralizedGradient g hEnorm hF hconc (eta t)
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I eta (Ici t) t
        (ContinuousLinearMap.toSpanSingleton ℝ ((g.inner (eta t) G G)⁻¹ • G)))
    (hstart : F (eta a) = a) : ∀ s ∈ Icc a b, F (eta s) = s := by
  obtain ⟨q, hq⟩ := hmax
  have hcal := normalized_ascent_level_increment g hEnorm hF hconc eta heta (by
    intro t ht
    refine ⟨?_, hvelocity t ht⟩
    apply intrinsicGeneralizedGradient_ne_zero_of_lt g hEnorm hF hconc (q := q)
    simpa only [hq] using hbelow t ht)
  intro s hs
  rw [hcal s hs, hstart]
  ring

theorem eqOn_normalized_ascent_curves (xi zeta : ℝ → M) {a b : ℝ}
    (hxi : ContinuousOn xi (Icc a b)) (hzeta : ContinuousOn zeta (Icc a b))
    (hX : ∀ t ∈ Ico a b,
      let G := intrinsicGeneralizedGradient g hEnorm hF hconc (xi t)
      G ≠ 0 ∧ HasMFDerivWithinAt 𝓘(ℝ, ℝ) I xi (Ici t) t
        (ContinuousLinearMap.toSpanSingleton ℝ ((g.inner (xi t) G G)⁻¹ • G)))
    (hY : ∀ t ∈ Ico a b,
      let G := intrinsicGeneralizedGradient g hEnorm hF hconc (zeta t)
      G ≠ 0 ∧ HasMFDerivWithinAt 𝓘(ℝ, ℝ) I zeta (Ici t) t
        (ContinuousLinearMap.toSpanSingleton ℝ ((g.inner (zeta t) G G)⁻¹ • G)))
    (hinitial : xi a = zeta a) : EqOn xi zeta (Icc a b) := by
  have hxLevel := normalized_ascent_level_increment g hEnorm hF hconc xi hxi hX
  have hyLevel := normalized_ascent_level_increment g hEnorm hF hconc zeta hzeta hY
  apply eqOn_normalized_intrinsicGeneralizedGradient_curves
    g hEnorm hF hconc xi zeta hxi hzeta
    (fun t ht => (hX t ht).2) (fun t ht => (hY t ht).2) ?_ hinitial
  intro t ht
  rw [hxLevel t ⟨ht.1, ht.2.le⟩, hyLevel t ⟨ht.1, ht.2.le⟩, hinitial]

end DifferentialGeometry.Geometry.Topology

end
