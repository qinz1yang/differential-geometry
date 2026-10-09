import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitTransport_CX6
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.ForwardApproximation
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Exhaustion
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Pullback
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Monotonicity
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Congruence

set_option autoImplicit false

/-! # CH12-CX6: finite metric approximations and canonical convergence -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Curvature
open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12
universe u

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

def inverse_approximation_CX6
    {M N : PointedRiemannianManifold.{u, 0, 0} ThreeModel}
    (Φ : PartialDiffeomorph ThreeModel ThreeModel M.M N.M ∞)
    {U : Set M.M} {ε : ℝ} {p : ℕ}
    (D : PartialDiffeomorphMetricApproximation U ε p Φ M.metric N.metric) :
    PartialDiffeomorphMetricApproximation (Φ '' U) ε p Φ.symm N.metric M.metric where
  source_sub := by
    rintro _ ⟨x, hx, rfl⟩
    exact Φ.map_source (D.source_sub hx)
  forward := D.reverse
  reverse := by
    have hset : Φ.symm '' (Φ '' U) = U := by
      ext x
      constructor
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        have heq : Φ.symm (Φ y) = y := Φ.left_inv (D.source_sub hy)
        exact heq.symm ▸ hy
      · intro hx
        exact ⟨Φ x, ⟨x, hx, rfl⟩, Φ.left_inv (D.source_sub hx)⟩
    change MapMetricApproximationOn (Φ.symm '' (Φ '' U)) ε p (Φ : M.M → N.M) M.metric N.metric
    rw [hset]
    exact D.forward

theorem eventually_partial_approximation_CX6
    {X : PointedRiemannianSeq.{u, 0, 0} ThreeModel}
    {L : PointedRiemannianManifold.{u, 0, 0} ThreeModel} {σ : ℕ → ℕ}
    (Φ : PointedRiemannianConvergenceMaps X L σ) (C : MetricConvergenceData Φ)
    (hcan : ∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData Φ n)
    (K : Set L.M) (hK : IsCompact K) (U : Set L.M) (hU : U ⊆ interior K)
    (p : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ n in atTop, Nonempty (PartialDiffeomorphMetricApproximation U ε p
      (Φ.partialDiffeomorph n) L.metric (X.obj (σ n)).metric) := by
  filter_upwards [C.eventually_map_metric_approximation hcan K hK p hε hε1,
    C.eventually_inverse_map_metric_approximation hcan K hK p hε hε1] with n hf hr
  exact ⟨⟨hU.trans (interior_subset.trans hf.1), (hf.2 U hU).some, (hr.2 U hU).some⟩⟩

theorem canonical_sup_le_of_approximation_CX6
    {X : PointedRiemannianSeq.{u, 0, 0} ThreeModel}
    {L : PointedRiemannianManifold.{u, 0, 0} ThreeModel} {σ : ℕ → ℕ}
    (Φ : PointedRiemannianConvergenceMaps X L σ) (n : ℕ)
    (U : Opens L.M) (hU : (U : Set L.M) ⊆ Φ.source n)
    (K : Set L.M) (hKU : K ⊆ U) {ε : ℝ} {p : ℕ}
    (D : MapMetricApproximationOn (U : Set L.M) ε p (Φ.map n) L.metric (X.obj (σ n)).metric) :
    (CanonicalMetricCompactness.canonicalSourceData Φ n).derivNormSupOn K p ≤ ε := by
  let G := PartialDiffeomorph.pullbackMetricOn (Φ.partialDiffeomorph n) U hU (X.obj (σ n)).metric
  rw [canonicalSourceData_derivNormSupOn_eq_of_open_pullback Φ n U hU G K hKU p
    (fun x v w => PartialDiffeomorph.pullbackMetricOn_inner _ _ _ _ x v w)]
  apply Real.sSup_le ?_ D.eps_pos.le
  rintro r ⟨a, ha, x, _, rfl⟩
  exact pullback_metric_deriv_norm_le (Φ.partialDiffeomorph n) U hU (Subset.refl _)
    L.metric (X.obj (σ n)).metric D ha x

/-- Exhausting partial diffeomorphisms with arbitrarily small finite-order
approximations give canonical pointed convergence after restriction and reindexing. -/
theorem exists_canonical_convergence_of_approximations_CX6
    {X : PointedRiemannianSeq.{u, 0, 0} ThreeModel}
    {L : PointedRiemannianManifold.{u, 0, 0} ThreeModel} [PreconnectedSpace L.M]
    (σ : ℕ → ℕ)
    (B : ∀ n, PartialDiffeomorph ThreeModel ThreeModel L.M (X.obj (σ n)).M ∞)
    (hbase : ∀ n, B n L.basepoint = (X.obj (σ n)).basepoint)
    (hsource : ∀ K : Set L.M, IsCompact K → ∀ᶠ n in atTop, K ⊆ (B n).source)
    (happrox : ∀ K : Set L.M, IsCompact K → ∀ p : ℕ, ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ᶠ n in atTop, Nonempty (MapMetricApproximationOn K ε p
        (B n) L.metric (X.obj (σ n)).metric)) :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      ∃ Φ : PointedRiemannianConvergenceMaps X L (σ ∘ k),
        ∃ C : MetricConvergenceData Φ,
          ∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData Φ n := by
  let : LocallyCompactSpace L.M := Manifold.locallyCompact_of_finiteDimensional ThreeModel
  obtain ⟨k, hk, Φ, hmap, _, _, _, _⟩ :=
    PointedRiemannianConvergenceMaps.exists_subsequence_restriction_of_eventually_contains_compacts
      B hbase hsource
  obtain ⟨C, hC, _⟩ := exists_metricConvergenceData_canonicalSourceData Φ (by
    intro K hK p ε hε
    obtain ⟨A, hA, hKA, _⟩ := exists_compact_between hK isOpen_univ (subset_univ K)
    let U : Opens L.M := ⟨interior A, isOpen_interior⟩
    let η := min (ε / 2) (1 / 2)
    have hη : 0 < η := lt_min (half_pos hε) (by norm_num)
    have hη1 : η < 1 := (min_le_right _ _).trans_lt (by norm_num)
    have hηε : η < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
    obtain ⟨N, hN⟩ := Φ.source_subset hA
    have hevent := hk.tendsto_atTop.eventually (happrox A hA p η hη hη1)
    obtain ⟨N', hN'⟩ := eventually_atTop.mp hevent
    refine ⟨max N N', fun n hn => ?_⟩
    obtain ⟨D⟩ := hN' n ((le_max_right _ _).trans hn)
    have hU : (U : Set L.M) ⊆ Φ.source n := interior_subset.trans (hN n ((le_max_left _ _).trans hn))
    have D' := (D.mono interior_subset le_rfl hη1).congrEq (hmap n)
    exact (canonical_sup_le_of_approximation_CX6 Φ n U hU K hKA D').trans_lt hηε)
  exact ⟨k, hk, Φ, C, hC⟩

end GC.LongTime.Ch12
