import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Congruence


import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Metric.Proper
import DifferentialGeometry.Geometry.Comparison.NormalCoordinates.ExponentialBallPartialDiffeomorph
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Bundle
open scoped Manifold ContDiff BigOperators Topology
open DifferentialGeometry.Geometry.Riemannian

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

section Glue

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [MetricSpace M] [Nonempty M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [T2Space N] [IsManifold I ∞ N]
  [SigmaCompactSpace N]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
theorem exists_partial_diffeomorph_metric_approximation
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (Ok : M) (Oℓ : N) (r : Real) (ε : Real) (p : Nat)
    (U : Set M) (hU : IsOpen U) (hOkU : Ok ∈ U)
    (hKU : Metric.closedBall Ok r ⊆ U)
    (F : M → N)
    (hloc : IsLocalDiffeomorphOn I I (∞ : WithTop ℕ∞) F U)
    (hinj : Set.InjOn F U)
    (hbase : F Ok = Oℓ)
    (hfwd : MapMetricApproximationOn (I := I) (Metric.closedBall Ok r) ε p F g h)
    (hrev : MapMetricApproximationOn (I := I) (F '' Metric.closedBall Ok r) ε p
      (Function.invFunOn F U) h g) :
    ∃ Phi : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞),
      Metric.closedBall Ok r ⊆ Phi.source ∧
      Phi Ok = Oℓ ∧
      Nonempty (PartialDiffeomorphMetricApproximation (I := I) (Metric.closedBall Ok r) ε p Phi g h) := by
  obtain ⟨Φ, hsrc, htgt, hEq⟩ := exists_partial_diffeomorph_of_is_local_diffeomorph_on_inj_on hloc hU hinj
  have hclosed_sub : Metric.closedBall Ok r ⊆ Φ.source := by rw [hsrc]; exact hKU
  have hev_fwd : ∀ x ∈ Metric.closedBall Ok r, (Φ : M → N) =ᶠ[nhds x] F := fun x hx =>
    Filter.eventuallyEq_of_mem (hU.mem_nhds (hKU hx)) hEq
  have fwdΦ : MapMetricApproximationOn (I := I) (Metric.closedBall Ok r) ε p (Φ : M → N) g h :=
    hfwd.congr hev_fwd
  have hsymmEq : Set.EqOn (Φ.symm : N → M) (Function.invFunOn F U) Φ.target := by
    intro z hz
    rw [htgt] at hz
    obtain ⟨x, hxU, rfl⟩ := hz
    have hΦx : (Φ : M → N) x = F x := hEq hxU
    have h1 : (Φ.symm : N → M) (F x) = x := by
      rw [← hΦx]; exact Φ.toPartialEquiv.left_inv (by rw [hsrc]; exact hxU)
    have h2 : Function.invFunOn F U (F x) = x := hinj.leftInvOn_invFunOn hxU
    rw [h1, h2]
  have hsetEq : (Φ : M → N) '' Metric.closedBall Ok r = F '' Metric.closedBall Ok r :=
    Set.EqOn.image_eq (fun x hx => hEq (hKU hx))
  have revΦ : MapMetricApproximationOn (I := I) ((Φ : M → N) '' Metric.closedBall Ok r) ε p
      (Φ.symm : N → M) h g := by
    rw [hsetEq]
    refine hrev.congr (fun y hy => ?_)
    have hy_target : y ∈ Φ.target := by rw [htgt]; exact Set.image_mono hKU hy
    exact Filter.eventuallyEq_of_mem (Φ.open_target.mem_nhds hy_target) hsymmEq
  exact ⟨Φ, hclosed_sub, (hEq hOkU).trans hbase,
    ⟨{ source_sub := hclosed_sub, forward := fwdΦ, reverse := revΦ }⟩⟩

end Glue

structure HasPairwiseApproximateIsometries (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) : Prop where
  comparison : ∀ (r : Real), 0 < r → ∀ (ε : Real), 0 < ε → ε < 1 → ∀ (p : Nat),
    ∃ k₀ : Nat, ∀ k ℓ : Nat, k₀ ≤ k → k₀ ≤ ℓ →
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (X.obj k).M := (X.obj k).t2
      letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj k).M := (X.obj k).smooth
      letI : TopologicalSpace (X.obj ℓ).M := (X.obj ℓ).topology
      letI : ChartedSpace H (X.obj ℓ).M := (X.obj ℓ).charted
      letI : IsManifold I ∞ (X.obj ℓ).M := (X.obj ℓ).smooth
      letI : T2Space (X.obj ℓ).M := (X.obj ℓ).t2
      letI : SigmaCompactSpace (X.obj ℓ).M := (X.obj ℓ).sigmaCompact
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj ℓ).M := (X.obj ℓ).smooth
      letI : MetricSpace (X.obj k).M := (P k).ms
      letI : MetricSpace (X.obj ℓ).M := (P ℓ).ms
      letI : Nonempty (X.obj k).M := ⟨(X.obj k).basepoint⟩
      ∃ (R : Real) (_ : r < R) (F : (X.obj k).M → (X.obj ℓ).M),
        IsLocalDiffeomorphOn I I (∞ : WithTop ℕ∞) F (Metric.ball (X.obj k).basepoint R) ∧
        Set.InjOn F (Metric.ball (X.obj k).basepoint R) ∧
        F (X.obj k).basepoint = (X.obj ℓ).basepoint ∧
        Nonempty (MapMetricApproximationOn (I := I) (Metric.closedBall (X.obj k).basepoint r) ε p F
          (X.obj k).metric (X.obj ℓ).metric) ∧
        Nonempty (MapMetricApproximationOn (I := I) (F '' Metric.closedBall (X.obj k).basepoint r) ε p
          (Function.invFunOn F (Metric.ball (X.obj k).basepoint R))
          (X.obj ℓ).metric (X.obj k).metric)

omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem HasPairwiseApproximateIsometries.exists_partial_approximate_isometry
    [FiniteDimensional Real E]
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (B : HasPairwiseApproximateIsometries (X := X) P)
    (r : Real) (hr : 0 < r) (ε : Real) (hε : 0 < ε) (hε1 : ε < 1) (p : Nat) :
    ∃ k₀ : Nat, ∀ k ℓ : Nat, k₀ ≤ k → k₀ ≤ ℓ →
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (X.obj k).M := (X.obj k).t2
      letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj k).M := (X.obj k).smooth
      letI : TopologicalSpace (X.obj ℓ).M := (X.obj ℓ).topology
      letI : ChartedSpace H (X.obj ℓ).M := (X.obj ℓ).charted
      letI : IsManifold I ∞ (X.obj ℓ).M := (X.obj ℓ).smooth
      letI : T2Space (X.obj ℓ).M := (X.obj ℓ).t2
      letI : SigmaCompactSpace (X.obj ℓ).M := (X.obj ℓ).sigmaCompact
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj ℓ).M := (X.obj ℓ).smooth
      letI : MetricSpace (X.obj k).M := (P k).ms
      letI : MetricSpace (X.obj ℓ).M := (P ℓ).ms
      ∃ Phi : PartialDiffeomorph I I (X.obj k).M (X.obj ℓ).M (∞ : WithTop ℕ∞),
        Metric.closedBall (X.obj k).basepoint r ⊆ Phi.source ∧
        Phi (X.obj k).basepoint = (X.obj ℓ).basepoint ∧
        Nonempty (PartialDiffeomorphMetricApproximation (I := I)
          (Metric.closedBall (X.obj k).basepoint r)
          ε p Phi (X.obj k).metric (X.obj ℓ).metric) := by
  obtain ⟨k₀, hk₀⟩ := B.comparison r hr ε hε hε1 p
  refine ⟨k₀, fun k ℓ hk hl => ?_⟩
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : TopologicalSpace (X.obj ℓ).M := (X.obj ℓ).topology
  let : ChartedSpace H (X.obj ℓ).M := (X.obj ℓ).charted
  let : IsManifold I ∞ (X.obj ℓ).M := (X.obj ℓ).smooth
  let : T2Space (X.obj ℓ).M := (X.obj ℓ).t2
  let : SigmaCompactSpace (X.obj ℓ).M := (X.obj ℓ).sigmaCompact
  let : MetricSpace (X.obj k).M := (P k).ms
  let : MetricSpace (X.obj ℓ).M := (P ℓ).ms
  have : Nonempty (X.obj k).M := ⟨(X.obj k).basepoint⟩
  obtain ⟨R, hRr, F, hloc, hinj, hbase, ⟨hfwd⟩, ⟨hrev⟩⟩ := hk₀ k ℓ hk hl
  have hR0 : (0 : Real) < R := lt_trans hr hRr
  have hU : IsOpen (Metric.ball (X.obj k).basepoint R) := by
    have hb := Metric.isOpen_ball (x := (X.obj k).basepoint) (ε := R)
    rwa [ProperMetricOn.top_eq (X.obj k) (P k)] at hb
  exact exists_partial_diffeomorph_metric_approximation (X.obj k).metric (X.obj ℓ).metric (X.obj k).basepoint (X.obj ℓ).basepoint
    r ε p (Metric.ball (X.obj k).basepoint R) hU (Metric.mem_ball_self hR0)
    (Metric.closedBall_subset_ball hRr) F hloc hinj hbase hfwd hrev

end CheegerGromovCompactness
end DifferentialGeometry
