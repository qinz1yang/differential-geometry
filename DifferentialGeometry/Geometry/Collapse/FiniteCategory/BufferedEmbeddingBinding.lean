import DifferentialGeometry.Geometry.Collapse.FiniteCategory.BufferedEmbedding
import DifferentialGeometry.Geometry.Collapse.FiniteCategory.BasepointInjectivity
import DifferentialGeometry.Geometry.Collapse.ComparisonImageContainment

/-!
# LFR10 for complete smooth targets with LFR08 data

Blueprint 207A, LFR10 (A:25488–25555), both clauses, for targets `(X i, g i, q i)` in the aligned
block (complete smooth `k`-manifolds carrying their Riemannian distance) with a common basepoint
volume lower bound `Vol B(q i, r₀) ≥ v₀` and, for every `S`, a common bound on `|Rm|` over
`B(q i, S)` (the data of LFR08).

* `HasInjRadiusAt.injOn_expMap`: an injectivity radius lower bound `ρ` gives injectivity of `exp`
  on every ball of radius `r < ρ` (converse of `hasInjRadiusAt_of_expMap_injOn`).
* `exists_uniform_injOn_expMap_of_basepoint_volume`: the injectivity input of the kernel
  `eventually_exists_partialDiffeomorph_ball` from the LFR08 data
  (`exists_uniform_injRadius_of_basepoint_volume_seq`).
* `eventually_buffered_embedding_of_basepoint_volume`: **LFR10** — for `r < R`, eventually the same
  map `f i` restricts to a `C^m` diffeomorphism of `B(p, R)` onto its open image, and
  `B(q i, r) ⊆ f i (B(p, R))` (containment clause: W4-F7b's
  `eventually_riemannian_ball_subset_image_of_localDiffeomorph`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Metric Bundle
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.CheegerGromovCompactness

open Geometry.Riemannian.NormalCoordinates

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]

section

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- An injectivity radius lower bound `ρ` at `x` gives injectivity of `exp_x` on the `r`-ball of
`T_x` for every `r < ρ`. -/
theorem HasInjRadiusAt.injOn_expMap {X : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {x : X.M} {ρ r : ℝ} (h : HasInjRadiusAt X x ρ) (hcomplete : MetricComplete X)
    (hr : r < ρ) :
    InjOn (fun v : TangentSpace I x =>
      DifferentialGeometry.Geometry.Riemannian.Exponential.expMap (I := I) X.metric x v)
      {v | Real.sqrt (X.metric.inner x v v) < r} := by
  have hinj := h.injOn_ball hcomplete hr
  let _ : IsManifold I 1 X.M :=
    IsManifold.of_le (I := I) (M := X.M) (n := ∞) (by decide)
  let _ : Bundle.RiemannianBundle (fun y : X.M => TangentSpace I y) := X.riemBundle
  let _ : (y : X.M) → InnerProductSpace ℝ (TangentSpace I y) := X.riemInner
  let _ : IsContinuousRiemannianBundle E
      (fun y : X.M => TangentSpace I y) := X.riemBundle_cont
  let _ : EMetricSpace X.M := X.emetricSpace
  let _ : CompleteSpace X.M := MetricComplete.complete X hcomplete
  let hEnorm : ∀ (y : X.M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (X.metric.inner y w w)) := by
    intro y w
    with_unfolding_all
      exact Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) X.metric y w
  have hmem : ∀ v : TangentSpace I x, Real.sqrt (X.metric.inner x v v) < r →
      (normalFrame (I := I) X.metric x).symm v ∈ Metric.ball (0 : E) r := by
    intro v hv
    rw [Metric.mem_ball, dist_zero_right,
      ← normalFrame_sqrt (I := I) X.metric x ((normalFrame (I := I) X.metric x).symm v),
      ContinuousLinearEquiv.apply_symm_apply]
    exact hv
  intro v hv w hw heq
  apply (normalFrame (I := I) X.metric x).symm.injective
  apply hinj (hmem v hv) (hmem w hw)
  change intrinsicFramedExp (I := I) X.metric hEnorm x ((normalFrame (I := I) X.metric x).symm v) =
    intrinsicFramedExp (I := I) X.metric hEnorm x ((normalFrame (I := I) X.metric x).symm w)
  simp only [intrinsicFrame_apply, ContinuousLinearEquiv.apply_symm_apply,
    ← DifferentialGeometry.Geometry.Riemannian.Exponential.expMap_eq_expMapIntrinsic
      (I := I) X.metric hEnorm x]
  exact heq

end

end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.Geometry.Collapse.FiniteCategory

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry (pullbackMetricCoefficients)
open DifferentialGeometry.Geometry.MetricSmoothing (chartCoeff)

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **The injectivity input of LFR10 from the LFR08 data.** For complete smooth aligned
`k`-manifolds with a common basepoint volume lower bound and, on every ball `B(q i, S)`, a common
bound on `|Rm|`, every ball `B(q i, S)` has a common radius on which all exponential maps are
injective. -/
theorem exists_uniform_injOn_expMap_of_basepoint_volume (k : ℕ) (hk : 2 ≤ k) {r₀ v₀ : ℝ}
    (hr₀ : 0 < r₀) (hv₀ : 0 < v₀)
    {X : ℕ → Type u} [∀ i, MetricSpace (X i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin k)) (X i)]
    [∀ i, IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ (X i)]
    [∀ i, T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (X i))]
    [∀ i, SigmaCompactSpace (X i)] [∀ i, CompleteSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (q : ∀ i, X i) (hvol : ∀ i, ENNReal.ofReal v₀ ≤ ballVolume (g i) (q i) r₀)
    (hRm : letI : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin k))) :=
        ⟨by simpa using (show k ≠ 0 by omega)⟩
      ∀ S : ℝ, ∃ A : ℝ, 0 < A ∧ ∀ i, ∀ y ∈ ball (q i) S,
        Real.sqrt (Tensor0SBundle.normSq0S (g i) y 4 (metricRm04At (g i) y)) ≤ A)
    (S : ℝ) :
    ∃ ι : ℝ, 0 < ι ∧ ∀ i, ∀ x ∈ ball (q i) S,
      InjOn (fun v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) x =>
          Riemannian.Exponential.expMap (g i) x v)
        {v | Real.sqrt ((g i).inner x v v) < ι} := by
  have : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin k))) :=
    ⟨by simpa using (show k ≠ 0 by omega)⟩
  set S' : ℝ := max S 1 with hS'_def
  have hS' : 0 < S' := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨A, hA, hRmA⟩ := hRm (2 * S' + r₀ + 2)
  obtain ⟨ι, hι, hinj⟩ := exists_uniform_injRadius_of_basepoint_volume_seq k hk hr₀ hv₀ hS' hA g
    hmetric q hvol hRmA
  refine ⟨ι / 2, half_pos hι, fun i x hx => ?_⟩
  have hcomplete : RiemannianMetricComplete (g i) :=
    (riemannianMetricComplete_iff_completeSpace (hmetric i)).mpr inferInstance
  exact (hinj i x (ball_subset_ball (le_max_left _ _) hx)).injOn_expMap hcomplete.complete
    (half_lt_self hι)

/-- **LFR10 (both clauses) for complete smooth targets with LFR08 data.** `(N, G, p)` complete
with a `C^n` metric `G`, `2 ≤ n`, carrying its Riemannian distance; `(X i, g i, q i)` complete
smooth aligned `k`-manifolds (`k ≥ 2`) with `Vol B(q i, r₀) ≥ v₀` and a common `|Rm|` bound on
every ball `B(q i, S)`; `C^m` maps `f i` (`3 ≤ m`) on open sets `U i` eventually containing every
compact set, `f i p = q i`, chart `C²` convergence `f_i^* g_i → G` and pointed distortion `→ 0` on
every ball. Then for `r < R`, eventually `f i` restricts to a `C^m` diffeomorphism of `B(p, R)`
onto its open image and `B(q i, r) ⊆ f i (B(p, R))`. -/
theorem eventually_buffered_embedding_of_basepoint_volume (k : ℕ) (hk : 2 ≤ k)
    {N : Type*} [MetricSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin k)) N]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ N] [CompleteSpace N]
    {n : ℕ∞ω} (G : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) n
      (EuclideanSpace ℝ (Fin k)) (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) : N → Type _))
    (hn : (2 : ℕ∞ω) ≤ n)
    (hG : letI : RiemannianBundle
            (fun x : N => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) x) :=
          ⟨G.toRiemannianMetric⟩
      IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) N)
    {r₀ v₀ : ℝ} (hr₀ : 0 < r₀) (hv₀ : 0 < v₀)
    {X : ℕ → Type u} [∀ i, MetricSpace (X i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin k)) (X i)]
    [∀ i, IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ (X i)]
    [∀ i, T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (X i))]
    [∀ i, SigmaCompactSpace (X i)] [∀ i, CompleteSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (q : ∀ i, X i) (hvol : ∀ i, ENNReal.ofReal v₀ ≤ ballVolume (g i) (q i) r₀)
    (hRm : letI : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin k))) :=
        ⟨by simpa using (show k ≠ 0 by omega)⟩
      ∀ S : ℝ, ∃ A : ℝ, 0 < A ∧ ∀ i, ∀ y ∈ ball (q i) S,
        Real.sqrt (Tensor0SBundle.normSq0S (g i) y 4 (metricRm04At (g i) y)) ≤ A)
    (f : ∀ i, N → X i) (p : N) (hp : ∀ i, f i p = q i)
    (U : ℕ → Set N) (hUo : ∀ i, IsOpen (U i))
    (hUK : ∀ K : Set N, IsCompact K → ∀ᶠ i in atTop, K ⊆ U i)
    {m : ℕ} (hm : 3 ≤ m)
    (hf : ∀ i, ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) m
      (f i) (U i))
    (hconv : ∀ (z : N) (K : Set (EuclideanSpace ℝ (Fin k))), IsCompact K →
      K ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) z).target →
      MapCPConvergenceOn K 2
        (fun i => pullbackMetricCoefficients (g i)
          (f i ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) z).symm))
        (chartCoeff G z))
    (hdist : ∀ S ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball p S, ∀ y ∈ ball p S,
      |dist (f i x) (f i y) - dist x y| < ε)
    {r R : ℝ} (hrR : r < R) :
    ∀ᶠ i in atTop,
      (∃ d : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, EuclideanSpace ℝ (Fin k))
          N (X i) m,
        d.source = ball p R ∧ d.target = f i '' ball p R ∧ (d : N → X i) = f i) ∧
      ball (q i) r ⊆ f i '' ball p R := by
  have : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin k))) :=
    ⟨by simpa using (show k ≠ 0 by omega)⟩
  have : ProperSpace N := by
    let _ : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) x) :=
      ⟨G.toRiemannianMetric⟩
    have := hG
    exact Manifold.properSpace_of_isRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin k))
  have hinjrad : ∀ S : ℝ, ∃ ι : ℝ, 0 < ι ∧ ∀ᶠ i in atTop, ∀ x ∈ ball (q i) S,
      InjOn (fun v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) x =>
          Riemannian.Exponential.expMap (g i) x v)
        {v | Real.sqrt ((g i).inner x v v) < ι} := fun S => by
    obtain ⟨ι, hι, h⟩ := exists_uniform_injOn_expMap_of_basepoint_volume k hk hr₀ hv₀ g hmetric q
      hvol hRm S
    exact ⟨ι, hι, Eventually.of_forall h⟩
  have hemb := eventually_exists_partialDiffeomorph_ball G hn hG g hmetric f p q hp U hUo hUK hm
    hf hconv hdist hinjrad R
  have hloc : ∀ᶠ i in atTop, IsLocalDiffeomorphOn 𝓘(ℝ, EuclideanSpace ℝ (Fin k))
      𝓘(ℝ, EuclideanSpace ℝ (Fin k)) m (f i) (ball p R) := by
    filter_upwards [hemb] with i hi
    obtain ⟨d, hds, -, hdf⟩ := hi
    intro x
    refine ⟨d, ?_, fun y _ => ?_⟩
    · rw [hds]
      exact x.2
    · rw [hdf]
  exact hemb.and (DifferentialGeometry.Geometry.Metric.eventually_riemannian_ball_subset_image_of_localDiffeomorph
    g hmetric f p q hp hloc (hdist R) hrR)

end DifferentialGeometry.Geometry.Collapse.FiniteCategory
