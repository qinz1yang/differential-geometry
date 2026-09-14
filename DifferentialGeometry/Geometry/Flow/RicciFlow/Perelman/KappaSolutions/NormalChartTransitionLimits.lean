import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalChart.BallBounds
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalChart.TransitionLimits

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Filter Topology
open scoped Manifold ContDiff Topology Bundle
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E : Type uE} [NormedAddCommGroup E]

section Basic

variable [NormedSpace Real E]

namespace MetricIsometry

theorem isom_bounds_on_of_shell
    [FiniteDimensional Real E] [CompleteSpace E]
    (B C : Nat → E → E →L[Real] E →L[Real] Real)
    (Phi : Nat → E → E) (U V : Set E)
    (hU : IsOpen U) (hV : IsOpen V)
    (hVnorm : ∃ Z : Real, ∀ y ∈ V, ‖y‖ ≤ Z)
    (hBsm : ∀ k, ContDiffOn Real (⊤ : ℕ∞) (B k) U)
    (hCsm : ∀ k, ContDiffOn Real (⊤ : ℕ∞) (C k) V)
    (hPhi : ∀ k, ContDiffOn Real (⊤ : ℕ∞) (Phi k) U)
    (hmap : ∀ k, Set.MapsTo (Phi k) U V)
    (hiso : ∀ k, ∀ x ∈ U, ∀ u v : E,
      B k x u v = C k (Phi k x)
        (fderiv Real (Phi k) x u) (fderiv Real (Phi k) x v))
    (hCsymm : ∀ k, ∀ y ∈ V, ∀ a b : E, C k y a b = C k y b a)
    (hBequiv : ∀ k, ∀ x ∈ U, ∀ q : E,
      (1 / 2 : Real) * ‖q‖ ^ 2 ≤ B k x q q ∧
        B k x q q ≤ 2 * ‖q‖ ^ 2)
    (hCequiv : ∀ k, ∀ y ∈ V, ∀ q : E,
      (1 / 2 : Real) * ‖q‖ ^ 2 ≤ C k y q q ∧
        C k y q q ≤ 2 * ‖q‖ ^ 2)
    (n : Nat) (CB CC : Nat → Real)
    (hCB : ∀ i, 0 ≤ CB i) (hCC : ∀ i, 0 ≤ CC i)
    (hDB : ∀ i, ∀ k, n + i ≤ k → ∀ x ∈ U,
      ‖iteratedFDeriv Real i (B k) x‖ ≤ CB i)
    (hDC : ∀ i, ∀ k, n + i ≤ k → ∀ y ∈ V,
      ‖iteratedFDeriv Real i (C k) y‖ ≤ CC i) :
    iteratedFDerivBoundsOnCompactsWithin U Phi := by
  intro r K hK hKU
  rcases r with _ | r
  · obtain ⟨Z, hZ⟩ := hVnorm
    exact ⟨Z, fun k x hx => by
      rw [norm_iteratedFDeriv_zero]
      exact hZ (Phi k x) (hmap k (hKU hx))⟩
  · let D : Real := 1 + (Finset.range (Nat.succ r + 1)).sum (fun i => CB i + CC i)
    have hD1 : 1 ≤ D := by
      have hsum : 0 ≤ (Finset.range (Nat.succ r + 1)).sum (fun i => CB i + CC i) :=
        Finset.sum_nonneg fun i _ => add_nonneg (hCB i) (hCC i)
      dsimp only [D]
      linarith
    have hCB_D : ∀ i, i ≤ Nat.succ r → CB i ≤ D := by
      intro i hi
      have himem : i ∈ Finset.range (Nat.succ r + 1) := Finset.mem_range.mpr (by omega)
      have hterm : CB i + CC i ≤
          (Finset.range (Nat.succ r + 1)).sum (fun j => CB j + CC j) :=
        Finset.single_le_sum (fun j _ => add_nonneg (hCB j) (hCC j)) himem
      dsimp only [D]
      linarith [hCC i]
    have hCC_D : ∀ i, i ≤ Nat.succ r → CC i ≤ D := by
      intro i hi
      have himem : i ∈ Finset.range (Nat.succ r + 1) := Finset.mem_range.mpr (by omega)
      have hterm : CB i + CC i ≤
          (Finset.range (Nat.succ r + 1)).sum (fun j => CB j + CC j) :=
        Finset.single_le_sum (fun j _ => add_nonneg (hCB j) (hCC j)) himem
      dsimp only [D]
      linarith [hCB i]
    obtain ⟨Mtail, hMtail⟩ : ∃ Mt : Real, ∀ k, n + Nat.succ r ≤ k → ∀ x ∈ K,
        ‖iteratedFDeriv Real (Nat.succ r) (Phi k) x‖ ≤ Mt :=
      ⟨_, fun k hk x hx =>
        isom_deriv_on (B k) (C k) (Phi k) U V hU hV (hBsm k) (hCsm k) (hPhi k)
          (hmap k) (hiso k) (hCsymm k) (hBequiv k) (hCequiv k)
          (Nat.succ_le_succ (Nat.zero_le r)) (D := D)
          (fun i _ hir y hy =>
            (hDB i k (le_trans (Nat.add_le_add_left hir n) hk) y hy).trans
              ((hCB_D i hir).trans (le_self_pow₀ hD1 (by omega))))
          (fun i _ hir y hy =>
            (hDC i k (le_trans (Nat.add_le_add_left hir n) hk) y hy).trans
              ((hCC_D i hir).trans (le_self_pow₀ hD1 (by omega))))
          (hKU hx)⟩
    have hfin : ∀ k : Nat, ∃ Mₖ : Real, ∀ x ∈ K,
        ‖iteratedFDeriv Real (Nat.succ r) (Phi k) x‖ ≤ Mₖ := fun k => by
      obtain ⟨Mₖ, hMₖ⟩ := hK.exists_bound_of_continuousOn
        (((hPhi k).continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top)
          hU.uniqueDiffOn).mono hKU)
      exact ⟨Mₖ, fun x hx => by
        rw [← iteratedFDerivWithin_of_isOpen (Nat.succ r) hU (hKU hx)]
        exact hMₖ x hx⟩
    choose Mₖ hMₖ using hfin
    let S : Finset Real := (Finset.range (n + Nat.succ r + 1)).image Mₖ
    have hSne : S.Nonempty :=
      ⟨Mₖ 0, Finset.mem_image.mpr
        ⟨0, Finset.mem_range.mpr (Nat.succ_pos _), rfl⟩⟩
    refine ⟨max Mtail (S.max' hSne), fun k x hx => ?_⟩
    rcases lt_or_ge k (n + Nat.succ r + 1) with hk | hk
    · have hm : Mₖ k ∈ S := Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
      exact (hMₖ k x hx).trans
        ((Finset.le_max' S (Mₖ k) hm).trans (le_max_right _ _))
    · exact (hMtail k (Nat.le_of_succ_le hk) x hx).trans (le_max_left _ _)

end MetricIsometry

end Basic

section Staircase

variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

namespace SeqBallNormalChartData

def chartTransition
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (k : Nat)
    (x y : (X.obj k).M) : E → E :=
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  (d.chart k x).transition (d.chart k y)

def chartOverlapOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (k : Nat)
    (x y : (X.obj k).M) (U : Set E) : Prop :=
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  (d.chart k x).OverlapOn (d.chart k y) U

theorem trans_bounds_on
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (hreal : hd.RealizesDistance)
    (n : Nat) (x y : ∀ k : Nat, (X.obj k).M) (U V : Set E)
    (hU : IsOpen U) (hV : IsOpen V)
    (hVnorm : ∃ Z : Real, ∀ z ∈ V, ‖z‖ ≤ Z)
    (hxdist : ∀ k, hd.dist k (x k) (X.obj k).basepoint ≤ (n : Real))
    (hydist : ∀ k, hd.dist k (y k) (X.obj k).basepoint ≤ (n : Real))
    (hVrad : ∀ k,
      V ⊆ Metric.ball (0 : E)
        (d.ratio * hd.mu (hd.dist k (y k) (X.obj k).basepoint)))
    (hovl : ∀ k, d.chartOverlapOn k (x k) (y k) U)
    (hmap : ∀ k, Set.MapsTo (d.chartTransition k (x k) (y k)) U V) :
    iteratedFDerivBoundsOnCompactsWithin U
      (fun k => d.chartTransition k (x k) (y k)) := by
  apply MetricIsometry.isom_bounds_on_of_shell
    (n := n) (CB := fun i => d.metricC n i) (CC := fun i => d.metricC n i)
    (fun k =>
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) :=
        (X.obj k).t2TangentBundle
      (d.chart k (x k)).metric (X.obj k).metric)
    (fun k =>
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) :=
        (X.obj k).t2TangentBundle
      (d.chart k (y k)).metric (X.obj k).metric)
    (fun k => d.chartTransition k (x k) (y k))
    U V hU hV hVnorm
  · intro k
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    have hovl' :
        (d.chart k (x k)).OverlapOn (d.chart k (y k)) U := by
      simpa only [SeqBallNormalChartData.chartOverlapOn] using hovl k
    have hUrad :
        U ⊆ Metric.ball (0 : E) (d.chart k (x k)).radius :=
      fun z hz => (hovl' z hz).1
    exact (d.chart k (x k)).metric_cont_diff_on (X.obj k).metric hU
      ((d.chart k (x k)).smooth_to.mono hUrad)
  · intro k
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    have hVrad' :
        V ⊆ Metric.ball (0 : E) (d.chart k (y k)).radius := by
      simpa only [d.radius_eq k (y k)] using hVrad k
    exact (d.chart k (y k)).metric_cont_diff_on (X.obj k).metric hV
      ((d.chart k (y k)).smooth_to.mono hVrad')
  · intro k
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    have hovl' :
        (d.chart k (x k)).OverlapOn (d.chart k (y k)) U := by
      simpa only [SeqBallNormalChartData.chartOverlapOn] using hovl k
    simpa only [SeqBallNormalChartData.chartTransition] using
      (d.chart k (x k)).transition_smooth (d.chart k (y k)) hovl'
  · exact hmap
  · intro k z hz u v
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    have hovl' :
        (d.chart k (x k)).OverlapOn (d.chart k (y k)) U := by
      simpa only [SeqBallNormalChartData.chartOverlapOn] using hovl k
    simpa only [SeqBallNormalChartData.chartTransition] using
      ((d.chart k (x k)).transition_isom (X.obj k).metric
        (d.chart k (y k)) hovl' hz u v).symm
  · intro k z _ a b
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    change (d.chart k (y k)).metric (X.obj k).metric z a b =
      (d.chart k (y k)).metric (X.obj k).metric z b a
    rw [(d.chart k (y k)).metric_apply (X.obj k).metric,
      (d.chart k (y k)).metric_apply (X.obj k).metric]
    exact (X.obj k).metric.symm _ _ _
  · intro k z hz q
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    have hovl' :
        (d.chart k (x k)).OverlapOn (d.chart k (y k)) U := by
      simpa only [SeqBallNormalChartData.chartOverlapOn] using hovl k
    exact d.metric_equiv k (x k) z (hovl' z hz).1 q
  · intro k z hz q
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    have hVrad' :
        V ⊆ Metric.ball (0 : E) (d.chart k (y k)).radius := by
      simpa only [d.radius_eq k (y k)] using hVrad k
    exact d.metric_equiv k (y k) z (hVrad' hz) q
  · exact d.metricC_nonneg n
  · exact d.metricC_nonneg n
  · intro i k hnk z hz
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    let : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
    have hovl' :
        (d.chart k (x k)).OverlapOn (d.chart k (y k)) U := by
      simpa only [SeqBallNormalChartData.chartOverlapOn] using hovl k
    have hx : riemannianEDistOf (I := I) (X.obj k).metric (X.obj k).basepoint (x k) ≤
        ENNReal.ofReal (n : Real) := by
      have hbridge : edist (X.obj k).basepoint (x k) =
          riemannianEDistOf (I := I) (X.obj k).metric
            (X.obj k).basepoint (x k) := rfl
      rw [← hbridge, edist_comm, hreal.edist_eq k (x k) (X.obj k).basepoint]
      exact ENNReal.ofReal_le_ofReal (hxdist k)
    exact d.metric_deriv n i k hnk (x k) hx z (hovl' z hz).1
  · intro i k hnk z hz
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    let : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
    have hVrad' :
        V ⊆ Metric.ball (0 : E) (d.chart k (y k)).radius := by
      simpa only [d.radius_eq k (y k)] using hVrad k
    have hy : riemannianEDistOf (I := I) (X.obj k).metric (X.obj k).basepoint (y k) ≤
        ENNReal.ofReal (n : Real) := by
      have hbridge : edist (X.obj k).basepoint (y k) =
          riemannianEDistOf (I := I) (X.obj k).metric
            (X.obj k).basepoint (y k) := rfl
      rw [← hbridge, edist_comm, hreal.edist_eq k (y k) (X.obj k).basepoint]
      exact ENNReal.ofReal_le_ofReal (hydist k)
    exact d.metric_deriv n i k hnk (y k) hy z (hVrad' hz)

end SeqBallNormalChartData

end Staircase

end CheegerGromovCompactness
end DifferentialGeometry
