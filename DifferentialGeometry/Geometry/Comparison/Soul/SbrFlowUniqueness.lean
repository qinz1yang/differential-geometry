import DifferentialGeometry.Geometry.Comparison.Soul.SbrGradient
import DifferentialGeometry.Geometry.Comparison.Soul.SbrGradientContraction

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

theorem antitoneOn_dist_normalized_intrinsicGeneralizedGradient
    (xi zeta : ℝ → M) {a b : ℝ}
    (hxi : ContinuousOn xi (Icc a b)) (hzeta : ContinuousOn zeta (Icc a b))
    (hX : ∀ t ∈ Ico a b,
      let G := intrinsicGeneralizedGradient g hEnorm hF hconc (xi t)
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I xi (Ici t) t
        (ContinuousLinearMap.toSpanSingleton ℝ ((g.inner (xi t) G G)⁻¹ • G)))
    (hY : ∀ t ∈ Ico a b,
      let G := intrinsicGeneralizedGradient g hEnorm hF hconc (zeta t)
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I zeta (Ici t) t
        (ContinuousLinearMap.toSpanSingleton ℝ ((g.inner (zeta t) G G)⁻¹ • G)))
    (hlevel : ∀ t ∈ Ico a b, F (xi t) = F (zeta t)) :
    AntitoneOn (fun t => dist (xi t) (zeta t)) (Icc a b) := by
  apply antitoneOn_dist_of_normalized_gradient_right_derivatives g hEnorm F hconc
    (intrinsicGeneralizedGradient g hEnorm hF hconc)
    (fun p => (intrinsicGeneralizedGradient_spec g hEnorm hF hconc p).1)
    xi zeta hxi hzeta ?_ ?_ hlevel
  · intro t ht
    exact (hX t ht).congr_mfderiv
      (ContinuousLinearMap.smulRight_one_eq_toSpanSingleton ℝ _).symm
  · intro t ht
    exact (hY t ht).congr_mfderiv
      (ContinuousLinearMap.smulRight_one_eq_toSpanSingleton ℝ _).symm

theorem antitoneOn_dist_fixed_normalized_intrinsicGeneralizedGradient
    (xi : ℝ → M) {a b : ℝ} (hxi : ContinuousOn xi (Icc a b))
    (hX : ∀ t ∈ Ico a b,
      let G := intrinsicGeneralizedGradient g hEnorm hF hconc (xi t)
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I xi (Ici t) t
        (ContinuousLinearMap.toSpanSingleton ℝ ((g.inner (xi t) G G)⁻¹ • G)))
    (q : M) (hlevel : ∀ t ∈ Ico a b, F (xi t) ≤ F q) :
    AntitoneOn (fun t => dist (xi t) q) (Icc a b) := by
  apply antitoneOn_dist_fixed_of_normalized_gradient_right_derivative g hEnorm F hconc
    (intrinsicGeneralizedGradient g hEnorm hF hconc)
    (fun p => (intrinsicGeneralizedGradient_spec g hEnorm hF hconc p).1)
    xi hxi ?_ q hlevel
  intro t ht
  exact (hX t ht).congr_mfderiv
    (ContinuousLinearMap.smulRight_one_eq_toSpanSingleton ℝ _).symm

theorem eqOn_normalized_intrinsicGeneralizedGradient_curves
    (xi zeta : ℝ → M) {a b : ℝ}
    (hxi : ContinuousOn xi (Icc a b)) (hzeta : ContinuousOn zeta (Icc a b))
    (hX : ∀ t ∈ Ico a b,
      let G := intrinsicGeneralizedGradient g hEnorm hF hconc (xi t)
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I xi (Ici t) t
        (ContinuousLinearMap.toSpanSingleton ℝ ((g.inner (xi t) G G)⁻¹ • G)))
    (hY : ∀ t ∈ Ico a b,
      let G := intrinsicGeneralizedGradient g hEnorm hF hconc (zeta t)
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I zeta (Ici t) t
        (ContinuousLinearMap.toSpanSingleton ℝ ((g.inner (zeta t) G G)⁻¹ • G)))
    (hlevel : ∀ t ∈ Ico a b, F (xi t) = F (zeta t))
    (hinitial : xi a = zeta a) : EqOn xi zeta (Icc a b) := by
  have hdist := antitoneOn_dist_normalized_intrinsicGeneralizedGradient g hEnorm hF hconc
    xi zeta hxi hzeta hX hY hlevel
  intro t ht
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  have hd := hdist ha ht ht.1
  change dist (xi t) (zeta t) ≤ dist (xi a) (zeta a) at hd
  rw [hinitial, dist_self] at hd
  exact dist_eq_zero.mp (le_antisymm hd dist_nonneg)

theorem eqOn_normalized_intrinsicGeneralizedGradient_overlap
    (xi zeta : ℝ → M) {a b₁ b₂ : ℝ}
    (hxi : ContinuousOn xi (Icc a b₁)) (hzeta : ContinuousOn zeta (Icc a b₂))
    (hX : ∀ t ∈ Ico a b₁,
      let G := intrinsicGeneralizedGradient g hEnorm hF hconc (xi t)
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I xi (Ici t) t
        (ContinuousLinearMap.toSpanSingleton ℝ ((g.inner (xi t) G G)⁻¹ • G)))
    (hY : ∀ t ∈ Ico a b₂,
      let G := intrinsicGeneralizedGradient g hEnorm hF hconc (zeta t)
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I zeta (Ici t) t
        (ContinuousLinearMap.toSpanSingleton ℝ ((g.inner (zeta t) G G)⁻¹ • G)))
    (hxiLevel : ∀ t ∈ Ico a b₁, F (xi t) = t)
    (hzetaLevel : ∀ t ∈ Ico a b₂, F (zeta t) = t)
    (hinitial : xi a = zeta a) : EqOn xi zeta (Icc a (min b₁ b₂)) := by
  apply eqOn_normalized_intrinsicGeneralizedGradient_curves g hEnorm hF hconc xi zeta
    (hxi.mono (fun _ ht => ⟨ht.1, ht.2.trans (min_le_left b₁ b₂)⟩))
    (hzeta.mono (fun _ ht => ⟨ht.1, ht.2.trans (min_le_right b₁ b₂)⟩))
    (fun t ht => hX t ⟨ht.1, ht.2.trans_le (min_le_left b₁ b₂)⟩)
    (fun t ht => hY t ⟨ht.1, ht.2.trans_le (min_le_right b₁ b₂)⟩)
    ?_ hinitial
  intro t ht
  exact (hxiLevel t ⟨ht.1, ht.2.trans_le (min_le_left b₁ b₂)⟩).trans
    (hzetaLevel t ⟨ht.1, ht.2.trans_le (min_le_right b₁ b₂)⟩).symm

end DifferentialGeometry.Geometry.Topology
