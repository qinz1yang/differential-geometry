import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitDiagonal_CX6
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Composition.PartialDiffeomorphForward
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Addition

set_option autoImplicit false

/-! # CH12-CX6: the second diagonal, from actual slices back to models -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Curvature
open Set Filter TopologicalSpace
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch12
universe u

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

/-- A convergent actual diagonal and the finite-order row approximations have
the same canonical limit.  The proof constructs the inverse compositions,
controls every fixed derivative order, and restricts to a monotone exhaustion. -/
theorem exists_convergence_of_diagonal_CX6
    {X Y : PointedRiemannianSeq.{u, 0, 0} ThreeModel}
    {L : PointedRiemannianManifold.{u, 0, 0} ThreeModel} [PreconnectedSpace L.M]
    (hc : MetricComplete L) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (Φ : PointedRiemannianConvergenceMaps X L σ) (C : MetricConvergenceData Φ)
    (hcan : ∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData Φ n)
    (B : ∀ j, PartialDiffeomorph ThreeModel ThreeModel (Y.obj j).M (X.obj j).M ∞)
    (U : ∀ j, Opens (Y.obj j).M)
    (hp : ∀ j, (Y.obj j).basepoint ∈ U j)
    (hb : ∀ j, B j (Y.obj j).basepoint = (X.obj j).basepoint)
    (hcap : ∀ j, riemannianBallOf (X.obj j).metric (X.obj j).basepoint ((j : ℝ) + 1) ⊆
      B j '' (U j : Set (Y.obj j).M))
    (happrox : ∀ j, Nonempty (PartialDiffeomorphMetricApproximation (U j : Set (Y.obj j).M)
      (1 / ((j : ℝ) + 2)) j (B j) (Y.obj j).metric (X.obj j).metric)) :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      ∃ Ψ : PointedRiemannianConvergenceMaps Y L (σ ∘ k),
        ∃ D : MetricConvergenceData Ψ,
          ∀ n, D.domain n = CanonicalMetricCompactness.canonicalSourceData Ψ n := by
  classical
  let A (n : ℕ) := (Φ.partialDiffeomorph n).trans (B (σ n)).symm
  have href : ∀ n, (C.domain n).referenceMetric = (C.domain n).limitMetric := by
    intro n
    rw [hcan n]
    exact canonicalSourceData_referenceMetric_eq_limitMetric _ _
  have himage : ∀ K : Set L.M, IsCompact K → ∀ᶠ n in atTop,
      K ⊆ Φ.source n ∧ Φ.map n '' K ⊆ B (σ n) '' (U (σ n) : Set (Y.obj (σ n)).M) := by
    intro K hK
    obtain ⟨R, hR, hbound⟩ := Φ.exists_eventually_image_compact_subset_ball C href hc hK
    have ht : Tendsto (fun n => (σ n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp hσ.tendsto_atTop)
    filter_upwards [hbound, ht.eventually (eventually_gt_atTop R)] with n hn hlarge
    refine ⟨hn.1, fun y hy => hcap (σ n) ?_⟩
    exact (hn.2 hy).trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hlarge)
  have hsrc : ∀ K : Set L.M, IsCompact K → ∀ᶠ n in atTop, K ⊆ (A n).source := by
    intro K hK
    filter_upwards [himage K hK] with n hn
    intro x hx
    refine ⟨hn.1 hx, ?_⟩
    obtain ⟨y, hy, heq⟩ := hn.2 ⟨x, hx, rfl⟩
    change Φ.map n x ∈ (B (σ n)).target
    rw [← heq]
    exact (B (σ n)).map_source ((happrox (σ n)).some.source_sub hy)
  have hbase (n : ℕ) : A n L.basepoint = (Y.obj (σ n)).basepoint := by
    change (B (σ n)).symm (Φ.map n L.basepoint) = _
    have heq : Φ.map n L.basepoint = (X.obj (σ n)).basepoint := Φ.basepoint_map n
    rw [heq, ← hb (σ n)]
    exact (B (σ n)).left_inv ((happrox (σ n)).some.source_sub (hp (σ n)))
  apply exists_canonical_convergence_of_approximations_CX6 σ A hbase hsrc
  intro K hK p ε hε hε1
  let : LocallyCompactSpace L.M := Manifold.locallyCompact_of_finiteDimensional ThreeModel
  obtain ⟨T, hT, hKT, _⟩ := exists_compact_between hK isOpen_univ (subset_univ K)
  let W : Opens L.M := ⟨interior T, isOpen_interior⟩
  obtain ⟨Cp, hCp, hCpbound⟩ :=
    exists_uniform_iterated_covariant_derivative_add_norm_bound (I := ThreeModel) p
  let δ := ε / 4
  have hδ : 0 < δ := by positivity
  have hδhalf : δ ≤ 1 / 2 := by dsimp [δ]; linarith
  have hδ1 : δ < 1 := by linarith
  have hsmall : Tendsto (fun n => 1 / ((σ n : ℝ) + 2) * max Cp 2) atTop (𝓝 0) := by
    have hden : Tendsto (fun n => (σ n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 (tendsto_natCast_atTop_atTop.comp hσ.tendsto_atTop)
    simpa only [one_div, zero_mul, Function.comp_def] using (tendsto_inv_atTop_zero.comp hden).mul_const (max Cp 2)
  filter_upwards [eventually_partial_approximation_CX6 Φ C hcan T hT (W : Set L.M) (Subset.refl _) p hδ hδ1,
    himage T hT, hsmall.eventually (eventually_lt_nhds (half_pos hε)),
    eventually_ge_atTop p] with n hn hTn hβ hnorder
  let D₁ := hn.some
  let D₂ := (inverse_approximation_CX6 (B (σ n)) (happrox (σ n)).some).monoOrder
    (hnorder.trans (hσ.id_le n))
  let V : Opens (X.obj (σ n)).M := ⟨B (σ n) '' (U (σ n) : Set (Y.obj (σ n)).M),
    (B (σ n)).toOpenPartialHomeomorph.isOpen_image_of_subset_source (U (σ n)).isOpen
      (happrox (σ n)).some.source_sub⟩
  have hWV : Φ.map n '' (W : Set L.M) ⊆ V := (image_mono interior_subset).trans hTn.2
  apply PartialDiffeomorphMetricApproximation.trans_forward
    (Φ.partialDiffeomorph n) (B (σ n)).symm D₁.source_sub D₂.source_sub hWV hK hKT
    hδhalf Cp hCp hCpbound L.metric (X.obj (σ n)).metric (Y.obj (σ n)).metric D₁ D₂ ε
  · have hfrac := (ratio_div_one_sub_bounds_of_le_half hδ hδhalf).2.2.2.2
    dsimp [δ] at hfrac
    linarith
  · exact hε1

end GC.LongTime.Ch12
