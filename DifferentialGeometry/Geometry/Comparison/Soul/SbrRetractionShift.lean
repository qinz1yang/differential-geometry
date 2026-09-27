import DifferentialGeometry.Geometry.Comparison.Soul.SbrRetraction
import DifferentialGeometry.Geometry.Comparison.Soul.SbrGradientShift

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

set_option backward.isDefEq.respectTransparency false in
theorem sharafutdinovLevelMap_add_const
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (F : M → ℝ) (L : ℝ≥0) (hF : LipschitzWith L F)
    (hconc : ∀ (p : M) (v : TangentSpace I p),
      ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm p v t)))
    (hC : IsCompact {z : M | 0 ≤ F z}) {m : ℝ}
    (hmax : ∃ q : M, F q = m ∧ ∀ z : M, F z ≤ m)
    (k : ℝ) (hk : 0 ≤ k)
    (hCk : IsCompact {z : M | 0 ≤ F z + k})
    (hmaxk : ∃ q : M, F q + k = m + k ∧ ∀ z : M, F z + k ≤ m + k)
    {s : ℝ} (hs : s ∈ Icc 0 m) {x : M} (hx : 0 ≤ F x) :
    sharafutdinovLevelMap g hEnorm (fun z => F z + k) L
        ((Isometry.lipschitzWith_iff L (isometry_add_right k)).mpr hF)
        (fun p v => (hconc p v).add_const k) hCk hmaxk (s + k) x =
      sharafutdinovLevelMap g hEnorm F L hF hconc hC hmax s x := by
  let hFk : LipschitzWith L (fun z => F z + k) :=
    (Isometry.lipschitzWith_iff L (isometry_add_right k)).mpr hF
  let hconck : ∀ (p : M) (v : TangentSpace I p),
      ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm p v t) + k) :=
    fun p v => (hconc p v).add_const k
  let R := sharafutdinovLevelMap g hEnorm F L hF hconc hC hmax
  let Rk := sharafutdinovLevelMap g hEnorm (fun z => F z + k) L hFk hconck hCk hmaxk
  change Rk (s + k) x = R s x
  by_cases hfixed : s ≤ F x
  · dsimp only [Rk, R]
    rw [sharafutdinovLevelMap_of_le g hEnorm (fun z => F z + k) L
      hFk hconck hCk hmaxk (s + k) x (add_le_add hfixed le_rfl),
      sharafutdinovLevelMap_of_le g hEnorm F L hF hconc hC hmax s x hfixed]
  have hxs : F x < s := lt_of_not_ge hfixed
  have hxk : 0 ≤ F x + k := add_nonneg hx hk
  have hsub : Icc (F x) s ⊆ Icc 0 m :=
    fun _ ht => ⟨hx.trans ht.1, ht.2.trans hs.2⟩
  have hsubk : MapsTo (fun t : ℝ => t + k) (Icc (F x) s) (Icc 0 (m + k)) := by
    intro t ht
    exact ⟨add_nonneg (hx.trans ht.1) hk, add_le_add (ht.2.trans hs.2) le_rfl⟩
  have hcont := (sharafutdinovLevelMap_continuousOn_orbit
    g hEnorm F L hF hconc hC hmax hx).mono hsub
  have hcontk := (sharafutdinovLevelMap_continuousOn_orbit
    g hEnorm (fun z => F z + k) L hFk hconck hCk hmaxk hxk).comp
      (continuous_id.add_const k).continuousOn hsubk
  have hderk : ∀ t ∈ Ico (F x) s,
      let G := intrinsicGeneralizedGradient g hEnorm hF hconc (Rk (t + k) x)
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u => Rk (u + k) x) (Ici t) t
        (ContinuousLinearMap.toSpanSingleton ℝ ((g.inner (Rk (t + k) x) G G)⁻¹ • G)) := by
    intro t ht
    have houter := (sharafutdinovLevelMap_hasMFDerivWithinAt_orbit
      g hEnorm (fun z => F z + k) L hFk hconck hCk hmaxk hxk
      (add_le_add ht.1 le_rfl) (add_lt_add_of_lt_of_le (ht.2.trans_le hs.2) le_rfl)).2
    rw [intrinsicGeneralizedGradient_add_const g hEnorm hF hconc k
      (Rk (t + k) x)] at houter
    have htime : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (fun u : ℝ => u + k) (Ici t) t (ContinuousLinearMap.id ℝ ℝ) :=
      ((hasFDerivAt_id t).add_const k).hasMFDerivAt.hasMFDerivWithinAt
    have hcomp := houter.comp (f := fun u : ℝ => u + k) t htime (by
      intro u hu
      change t ≤ u at hu
      change t + k ≤ u + k
      exact add_le_add hu le_rfl)
    convert! hcomp using 1
  have hsame := eqOn_normalized_intrinsicGeneralizedGradient_curves
    g hEnorm hF hconc (fun t => Rk (t + k) x) (fun t => R t x)
    hcontk hcont hderk
    (fun t ht => (sharafutdinovLevelMap_hasMFDerivWithinAt_orbit
      g hEnorm F L hF hconc hC hmax hx ht.1 (ht.2.trans_le hs.2)).2)
    (by
      intro t ht
      have ht' : t ∈ Icc (F x) s := ⟨ht.1, ht.2.le⟩
      have hlev := sharafutdinovLevelMap_level
        g hEnorm (fun z => F z + k) L hFk hconck hCk hmaxk (hsubk ht') hxk
      rw [max_eq_right (add_le_add ht.1 le_rfl)] at hlev
      have hlev' := sharafutdinovLevelMap_level
        g hEnorm F L hF hconc hC hmax (hsub ht') hx
      rw [max_eq_right ht.1] at hlev'
      change F (Rk (t + k) x) + k = t + k at hlev
      exact (add_right_cancel hlev).trans hlev'.symm)
    (by
      dsimp only [Rk, R]
      rw [sharafutdinovLevelMap_of_le g hEnorm (fun z => F z + k) L
        hFk hconck hCk hmaxk (F x + k) x le_rfl,
        sharafutdinovLevelMap_of_le g hEnorm F L hF hconc hC hmax (F x) x le_rfl])
  exact hsame ⟨hxs.le, le_rfl⟩

end DifferentialGeometry.Geometry.Topology

end
