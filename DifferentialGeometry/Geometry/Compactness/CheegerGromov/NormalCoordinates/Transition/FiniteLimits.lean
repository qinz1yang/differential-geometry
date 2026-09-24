import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalCoordinates.TransitionBounds
import DifferentialGeometry.Geometry.Exponential.NormalBall.Chart
import DifferentialGeometry.Analysis.Calculus.MapConvergence.FiniteInverse
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Transition.IntrinsicOverlap

section

set_option autoImplicit false

namespace DifferentialGeometry.CheegerGromovCompactness.MetricIsometry

open Filter Topology
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

theorem isom_bounds_on_of_eventually_bounded
    [FiniteDimensional Real E]
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
    (CB CC : Nat → Real)
    (hCB : ∀ i, 0 ≤ CB i) (hCC : ∀ i, 0 ≤ CC i)
    (hDB : ∀ i, ∀ᶠ k in atTop, ∀ x ∈ U,
      ‖iteratedFDeriv Real i (B k) x‖ ≤ CB i)
    (hDC : ∀ i, ∀ᶠ k in atTop, ∀ y ∈ V,
      ‖iteratedFDeriv Real i (C k) y‖ ≤ CC i) :
    iteratedFDerivBoundsOnCompactsWithin U Phi := by
  intro r K hK hKU
  rcases r with _ | r
  · obtain ⟨Z, hZ⟩ := hVnorm
    exact ⟨Z, fun k x hx => by
      rw [norm_iteratedFDeriv_zero]
      exact hZ (Phi k x) (hmap k (hKU hx))⟩
  · have htail : ∀ᶠ k in atTop, ∀ i : Fin (Nat.succ r + 1),
        (∀ x ∈ U, ‖iteratedFDeriv Real (i : Nat) (B k) x‖ ≤ CB i) ∧
          (∀ y ∈ V, ‖iteratedFDeriv Real (i : Nat) (C k) y‖ ≤ CC i) :=
      Filter.eventually_all.mpr fun i => (hDB i).and (hDC i)
    obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp htail
    let D : Real := 1 + (Finset.range (Nat.succ r + 1)).sum (fun i => CB i + CC i)
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
    obtain ⟨Mtail, hMtail⟩ : ∃ Mt : Real, ∀ k, n ≤ k → ∀ x ∈ K,
        ‖iteratedFDeriv Real (Nat.succ r) (Phi k) x‖ ≤ Mt :=
      ⟨_, fun k hk x hx =>
        isom_deriv_on (B k) (C k) (Phi k) U V hU hV (hBsm k) (hCsm k) (hPhi k)
          (hmap k) (hiso k) (hCsymm k) (hBequiv k) (hCequiv k)
          (Nat.succ_le_succ (Nat.zero_le r)) (D := D)
          (fun i _ hir y hy =>
            ((hn k hk ⟨i, by omega⟩).1 y hy).trans
              ((hCB_D i hir).trans (le_self_pow₀ hD1 (by omega))))
          (fun i _ hir y hy =>
            ((hn k hk ⟨i, by omega⟩).2 y hy).trans
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
    let S : Finset Real := (Finset.range (n + 1)).image Mₖ
    have hSne : S.Nonempty :=
      ⟨Mₖ 0, Finset.mem_image.mpr
        ⟨0, Finset.mem_range.mpr (Nat.succ_pos _), rfl⟩⟩
    refine ⟨max Mtail (S.max' hSne), fun k x hx => ?_⟩
    rcases lt_or_ge k (n + 1) with hk | hk
    · have hm : Mₖ k ∈ S := Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
      exact (hMₖ k x hx).trans
        ((Finset.le_max' S (Mₖ k) hm).trans (le_max_right _ _))
    · exact (hMtail k (Nat.le_of_succ_le hk) x hx).trans (le_max_left _ _)


end DifferentialGeometry.CheegerGromovCompactness.MetricIsometry


end

section

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

open Filter Topology
open scoped ContDiff Manifold
open CheegerGromovCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Nat → Type u} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  [∀ k, IsManifold I ∞ (M k)] [∀ k, T2Space (TangentBundle I (M k))]

omit [I.Boundaryless] [∀ k, T2Space (TangentBundle I (M k))] in
theorem transition_bounds_on_of_eventually_bounded
    (g : ∀ k, SmoothRiemannianMetric I (M k))
    (x y : ∀ k, M k) (c : ∀ k, NormalBallChart (I := I) (x k))
    (d : ∀ k, NormalBallChart (I := I) (y k))
    (U V : Set E) (hU : IsOpen U) (hV : IsOpen V)
    (hVrad : ∀ k, V ⊆ Metric.ball (0 : E) (d k).radius)
    (hovl : ∀ k, (c k).OverlapOn (d k) U)
    (hmap : ∀ k, Set.MapsTo ((c k).transition (d k)) U V)
    (hcequiv : ∀ k z, z ∈ U → ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ (c k).metric (g k) z v v ∧
        (c k).metric (g k) z v v ≤ 2 * ‖v‖ ^ 2)
    (hdequiv : ∀ k z, z ∈ V → ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ (d k).metric (g k) z v v ∧
        (d k).metric (g k) z v v ≤ 2 * ‖v‖ ^ 2)
    (C D : Nat → Real) (hC : ∀ p, 0 ≤ C p) (hD : ∀ p, 0 ≤ D p)
    (hcjets : ∀ p, ∀ᶠ k in atTop, ∀ z ∈ U,
      ‖iteratedFDeriv Real p ((c k).metric (g k)) z‖ ≤ C p)
    (hdjets : ∀ p, ∀ᶠ k in atTop, ∀ z ∈ V,
      ‖iteratedFDeriv Real p ((d k).metric (g k)) z‖ ≤ D p) :
    iteratedFDerivBoundsOnCompactsWithin U (fun k => (c k).transition (d k)) := by
  have hVnorm : ∃ Z : Real, ∀ z ∈ V, ‖z‖ ≤ Z := by
    refine ⟨(d 0).radius, ?_⟩
    intro z hz
    simpa only [dist_zero_right] using (Metric.mem_ball.mp ((hVrad 0) hz)).le
  apply MetricIsometry.isom_bounds_on_of_eventually_bounded
    (fun k => (c k).metric (g k)) (fun k => (d k).metric (g k))
    (fun k => (c k).transition (d k)) U V hU hV hVnorm
  · intro k
    exact (c k).metric_cont_diff_on (g k) hU
      ((c k).smooth_to.mono fun z hz => (hovl k z hz).1)
  · intro k
    exact (d k).metric_cont_diff_on (g k) hV ((d k).smooth_to.mono (hVrad k))
  · exact fun k => (c k).transition_smooth (d k) (hovl k)
  · exact hmap
  · exact fun k z hz u v => ((c k).transition_isom (g k) (d k) (hovl k) hz u v).symm
  · intro k z hz u v
    rw [(d k).metric_apply, (d k).metric_apply]
    exact (g k).symm _ _ _
  · exact hcequiv
  · exact hdequiv
  · exact hC
  · exact hD
  · exact hcjets
  · exact hdjets

omit [I.Boundaryless] [∀ k, T2Space (TangentBundle I (M k))] in
theorem exists_transition_limit_subsequence_of_eventually_bounded
    (g : ∀ k, SmoothRiemannianMetric I (M k))
    (x y : ∀ k, M k) (c : ∀ k, NormalBallChart (I := I) (x k))
    (d : ∀ k, NormalBallChart (I := I) (y k))
    (U V Ua Va : Set E) (hU : IsOpen U) (hV : IsOpen V)
    (hUa : IsOpen Ua) (hVa : IsOpen Va)
    (hUUa : U ⊆ Ua) (hVVa : V ⊆ Va)
    (hUarad : ∀ k, Ua ⊆ Metric.ball (0 : E) (c k).radius)
    (hVarad : ∀ k, Va ⊆ Metric.ball (0 : E) (d k).radius)
    (hovl : ∀ k, (c k).OverlapOn (d k) U)
    (hovlrev : ∀ k, (d k).OverlapOn (c k) V)
    (hmap : ∀ k, Set.MapsTo ((c k).transition (d k)) U Va)
    (hmaprev : ∀ k, Set.MapsTo ((d k).transition (c k)) V Ua)
    (hcequiv : ∀ k z, z ∈ Ua → ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ (c k).metric (g k) z v v ∧
        (c k).metric (g k) z v v ≤ 2 * ‖v‖ ^ 2)
    (hdequiv : ∀ k z, z ∈ Va → ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ (d k).metric (g k) z v v ∧
        (d k).metric (g k) z v v ≤ 2 * ‖v‖ ^ 2)
    (C D : Nat → Real) (hC : ∀ p, 0 ≤ C p) (hD : ∀ p, 0 ≤ D p)
    (hcjets : ∀ p, ∀ᶠ k in atTop, ∀ z ∈ Ua,
      ‖iteratedFDeriv Real p ((c k).metric (g k)) z‖ ≤ C p)
    (hdjets : ∀ p, ∀ᶠ k in atTop, ∀ z ∈ Va,
      ‖iteratedFDeriv Real p ((d k).metric (g k)) z‖ ≤ D p) :
    ∃ (phi : Nat → Nat) (Jinf Jbarinf : E → E), StrictMono phi ∧
      ContDiffOn Real (⊤ : ℕ∞) Jinf U ∧ ContDiffOn Real (⊤ : ℕ∞) Jbarinf V ∧
      MapCInfConvergenceOnCompacts U (fun k => (c (phi k)).transition (d (phi k))) Jinf ∧
      MapCInfConvergenceOnCompacts V (fun k => (d (phi k)).transition (c (phi k))) Jbarinf ∧
      (∀ z ∈ U, Jinf z ∈ V → Jbarinf (Jinf z) = z) ∧
      (∀ z ∈ V, Jbarinf z ∈ U → Jinf (Jbarinf z) = z) := by
  apply exists_smooth_inverse_limit_subsequence_on hU hV
    (fun k => (c k).transition (d k)) (fun k => (d k).transition (c k))
    (fun k => (c k).transition_smooth (d k) (hovl k))
    (fun k => (d k).transition_smooth (c k) (hovlrev k))
  · apply transition_bounds_on_of_eventually_bounded g x y c d U Va hU hVa
      hVarad hovl hmap
      (fun k z hz v => hcequiv k z (hUUa hz) v) hdequiv C D hC hD
    · intro p
      filter_upwards [hcjets p] with k hk
      exact fun z hz => hk z (hUUa hz)
    · exact hdjets
  · apply transition_bounds_on_of_eventually_bounded g y x d c V Ua hV hUa
      hUarad hovlrev hmaprev
      (fun k z hz v => hdequiv k z (hVVa hz) v) hcequiv D C hD hC
    · intro p
      filter_upwards [hdjets p] with k hk
      exact fun z hz => hk z (hVVa hz)
    · exact hcjets
  · exact fun k z hz => (c k).transition_cancel (d k) (hovl k) hz
  · exact fun k z hz => (d k).transition_cancel (c k) (hovlrev k) hz

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart


end

section

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

open Filter Topology
open scoped ContDiff Manifold
open CheegerGromovCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Nat → Type u} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  [∀ k, IsManifold I ∞ (M k)]

theorem exists_finite_transition_limit_subsequence_of_eventually_bounded
    {ι : Type*} [Finite ι]
    (g : ∀ k, SmoothRiemannianMetric I (M k))
    (x y : ι → ∀ k, M k)
    (c : ∀ i k, NormalBallChart (I := I) (x i k))
    (d : ∀ i k, NormalBallChart (I := I) (y i k))
    (U V Ua Va : ι → Set E)
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ i, IsOpen (V i))
    (hUa : ∀ i, IsOpen (Ua i)) (hVa : ∀ i, IsOpen (Va i))
    (hUUa : ∀ i, U i ⊆ Ua i) (hVVa : ∀ i, V i ⊆ Va i)
    (hUarad : ∀ i k, Ua i ⊆ Metric.ball (0 : E) (c i k).radius)
    (hVarad : ∀ i k, Va i ⊆ Metric.ball (0 : E) (d i k).radius)
    (hovl : ∀ i k, (c i k).OverlapOn (d i k) (U i))
    (hovlrev : ∀ i k, (d i k).OverlapOn (c i k) (V i))
    (hmap : ∀ i k, Set.MapsTo ((c i k).transition (d i k)) (U i) (Va i))
    (hmaprev : ∀ i k, Set.MapsTo ((d i k).transition (c i k)) (V i) (Ua i))
    (hcequiv : ∀ i k z, z ∈ Ua i → ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ (c i k).metric (g k) z v v ∧
        (c i k).metric (g k) z v v ≤ 2 * ‖v‖ ^ 2)
    (hdequiv : ∀ i k z, z ∈ Va i → ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ (d i k).metric (g k) z v v ∧
        (d i k).metric (g k) z v v ≤ 2 * ‖v‖ ^ 2)
    (C D : ι → Nat → Real)
    (hC : ∀ i p, 0 ≤ C i p) (hD : ∀ i p, 0 ≤ D i p)
    (hcjets : ∀ i p, ∀ᶠ k in atTop, ∀ z ∈ Ua i,
      ‖iteratedFDeriv Real p ((c i k).metric (g k)) z‖ ≤ C i p)
    (hdjets : ∀ i p, ∀ᶠ k in atTop, ∀ z ∈ Va i,
      ‖iteratedFDeriv Real p ((d i k).metric (g k)) z‖ ≤ D i p) :
    ∃ (phi : Nat → Nat) (Jinf Jbarinf : ι → E → E), StrictMono phi ∧
      ∀ i, ContDiffOn Real (⊤ : ℕ∞) (Jinf i) (U i) ∧
        ContDiffOn Real (⊤ : ℕ∞) (Jbarinf i) (V i) ∧
        MapCInfConvergenceOnCompacts (U i)
          (fun k => (c i (phi k)).transition (d i (phi k))) (Jinf i) ∧
        MapCInfConvergenceOnCompacts (V i)
          (fun k => (d i (phi k)).transition (c i (phi k))) (Jbarinf i) ∧
        (∀ z ∈ U i, Jinf i z ∈ V i → Jbarinf i (Jinf i z) = z) ∧
        (∀ z ∈ V i, Jbarinf i z ∈ U i → Jinf i (Jbarinf i z) = z) := by
  apply exists_finite_smooth_inverse_limit_subsequence_on U V
    (fun i k => (c i k).transition (d i k))
    (fun i k => (d i k).transition (c i k)) hU hV
    (fun i k => (c i k).transition_smooth (d i k) (hovl i k))
    (fun i k => (d i k).transition_smooth (c i k) (hovlrev i k))
  · intro i
    apply transition_bounds_on_of_eventually_bounded g (x i) (y i) (c i) (d i)
      (U i) (Va i) (hU i) (hVa i) (hVarad i) (hovl i) (hmap i)
      (fun k z hz v => hcequiv i k z (hUUa i hz) v) (hdequiv i)
      (C i) (D i) (hC i) (hD i)
    · intro p
      filter_upwards [hcjets i p] with k hk
      exact fun z hz => hk z (hUUa i hz)
    · exact hdjets i
  · intro i
    apply transition_bounds_on_of_eventually_bounded g (y i) (x i) (d i) (c i)
      (V i) (Ua i) (hV i) (hUa i) (hUarad i) (hovlrev i) (hmaprev i)
      (fun k z hz v => hdequiv i k z (hVVa i hz) v) (hcequiv i)
      (D i) (C i) (hD i) (hC i)
    · intro p
      filter_upwards [hdjets i p] with k hk
      exact fun z hz => hk z (hVVa i hz)
    · exact hcjets i
  · exact fun i k z hz => (c i k).transition_cancel (d i k) (hovl i k) hz
  · exact fun i k z hz => (d i k).transition_cancel (c i k) (hovlrev i k) hz

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart


end

section

set_option autoImplicit false

noncomputable section

open Bundle Filter
open scoped Bundle Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Nat → Type u}
  [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  [∀ k, IsManifold I ∞ (M k)] [∀ k, T2Space (M k)]
  [∀ k, SigmaCompactSpace (M k)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [∀ k, PseudoEMetricSpace (M k)]
  [∀ k, RiemannianBundle (fun x : M k => TangentSpace I x)]
  [∀ k, IsRiemannianManifold I (M k)] [∀ k, CompleteSpace (M k)]
  [∀ k, IsContinuousRiemannianBundle E (fun x : M k => TangentSpace I x)]

theorem IntrinsicBallChart.exists_finite_transition_limit_subsequence
    {ι : Type*} [Finite ι]
    (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k (x : M k) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g k).inner x v v)))
    (x : ι → ∀ k, M k) {ρ : Real} (hρ : 0 < ρ)
    (c : ∀ i k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (x i k) ρ)
    (hequiv : ∀ i k z, z ∈ Metric.ball (0 : E) ρ → ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤
          ((c i k).toNormalBallChart (g k) (hEnorm k) (x i k) hρ).metric (g k) z v v ∧
        ((c i k).toNormalBallChart (g k) (hEnorm k) (x i k) hρ).metric (g k) z v v ≤
          2 * ‖v‖ ^ 2)
    (C : ι → Nat → Real) (hC : ∀ i p, 0 ≤ C i p)
    (hjets : ∀ i p, ∀ᶠ k in atTop, ∀ z ∈ Metric.ball (0 : E) ρ,
      ‖iteratedFDeriv Real p
        (((c i k).toNormalBallChart (g k) (hEnorm k) (x i k) hρ).metric (g k)) z‖ ≤
          C i p) :
    ∃ phi : Nat → Nat, StrictMono phi ∧ ∃ near : ι → ι → Bool,
      (∀ k i j,
        (near i j = true → edist (x i (phi k)) (x j (phi k)) < ENNReal.ofReal (ρ / 4)) ∧
        (near i j = false → ENNReal.ofReal (ρ / 4) ≤ edist (x i (phi k)) (x j (phi k)))) ∧
      (∀ k i j, near i j = false →
        Disjoint ((c i (phi k)).hom '' Metric.ball (0 : E) (ρ / 10))
          ((c j (phi k)).hom '' Metric.ball (0 : E) (ρ / 10))) ∧
      ∃ Jinf Jbarinf : {a : ι × ι // near a.1 a.2 = true} → E → E,
        ∀ a, ContDiffOn Real (⊤ : ℕ∞) (Jinf a) (Metric.ball (0 : E) (ρ / 2)) ∧
          ContDiffOn Real (⊤ : ℕ∞) (Jbarinf a) (Metric.ball (0 : E) (ρ / 2)) ∧
          CheegerGromovCompactness.MapCInfConvergenceOnCompacts
            (Metric.ball (0 : E) (ρ / 2))
            (fun k =>
              ((c a.1.1 (phi k)).toNormalBallChart
                (g (phi k)) (hEnorm (phi k)) (x a.1.1 (phi k)) hρ).transition
              ((c a.1.2 (phi k)).toNormalBallChart
                (g (phi k)) (hEnorm (phi k)) (x a.1.2 (phi k)) hρ)) (Jinf a) ∧
          CheegerGromovCompactness.MapCInfConvergenceOnCompacts
            (Metric.ball (0 : E) (ρ / 2))
            (fun k =>
              ((c a.1.2 (phi k)).toNormalBallChart
                (g (phi k)) (hEnorm (phi k)) (x a.1.2 (phi k)) hρ).transition
              ((c a.1.1 (phi k)).toNormalBallChart
                (g (phi k)) (hEnorm (phi k)) (x a.1.1 (phi k)) hρ)) (Jbarinf a) ∧
          (∀ z ∈ Metric.ball (0 : E) (ρ / 2),
            Jinf a z ∈ Metric.ball (0 : E) (ρ / 2) → Jbarinf a (Jinf a z) = z) ∧
          (∀ z ∈ Metric.ball (0 : E) (ρ / 2),
            Jbarinf a z ∈ Metric.ball (0 : E) (ρ / 2) → Jinf a (Jbarinf a z) = z) := by
  classical
  obtain ⟨phi0, hphi0, near, hnear⟩ :=
    EMetric.exists_subseq_eventually_edist_lt_or_ge x (ENNReal.ofReal (ρ / 4))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hnear
  let τ : Nat → Nat := fun k => phi0 (N + k)
  have hτ : StrictMono τ := hphi0.comp (fun _ _ h => Nat.add_lt_add_left h N)
  have hclass : ∀ k i j,
      (near i j = true → edist (x i (τ k)) (x j (τ k)) < ENNReal.ofReal (ρ / 4)) ∧
      (near i j = false → ENNReal.ofReal (ρ / 4) ≤ edist (x i (τ k)) (x j (τ k))) :=
    fun k => hN (N + k) (Nat.le_add_right N k)
  let nc : ∀ i k, NormalBallChart (I := I) (x i (τ k)) := fun i k =>
    (c i (τ k)).toNormalBallChart (g (τ k)) (hEnorm (τ k)) (x i (τ k)) hρ
  let P := {a : ι × ι // near a.1 a.2 = true}
  have hhalf : ρ / 2 ≤ ρ := by linarith
  have hbuffer : 3 * ρ / 4 ≤ ρ := by linarith
  have hsub : ρ / 2 ≤ 3 * ρ / 4 := by linarith
  have hnonneg : 0 ≤ ρ / 2 := le_of_lt (div_pos hρ (by norm_num : (0:ℝ) < 2))
  have hsum : ENNReal.ofReal (ρ / 4) + ENNReal.ofReal (ρ / 2) =
      ENNReal.ofReal (3 * ρ / 4) := by
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ ρ / 4) hnonneg]
    congr 1
    ring
  have hmargin : ∀ a : P, ∀ k,
      edist (x a.1.1 (τ k)) (x a.1.2 (τ k)) + ENNReal.ofReal (ρ / 2) ≤
        ENNReal.ofReal (3 * ρ / 4) := by
    intro a k
    rw [← hsum]
    simpa only [add_comm] using add_le_add_right ((hclass k a.1.1 a.1.2).1 a.2).le (ENNReal.ofReal (ρ / 2))
  have hmarginrev : ∀ a : P, ∀ k,
      edist (x a.1.2 (τ k)) (x a.1.1 (τ k)) + ENNReal.ofReal (ρ / 2) ≤
        ENNReal.ofReal (3 * ρ / 4) := by
    intro a k
    rw [edist_comm]
    exact hmargin a k
  have hovl : ∀ a : P, ∀ k,
      (nc a.1.1 k).OverlapOn (nc a.1.2 k) (Metric.ball (0 : E) (ρ / 2)) := by
    intro a k
    exact (c a.1.1 (τ k)).overlap_on_ball_of_edist_add_le
      (g (τ k)) (hEnorm (τ k)) (x a.1.1 (τ k)) (x a.1.2 (τ k))
      (c a.1.2 (τ k)) hρ hρ hhalf
      ((hmargin a k).trans (ENNReal.ofReal_le_ofReal hbuffer))
  have hovlrev : ∀ a : P, ∀ k,
      (nc a.1.2 k).OverlapOn (nc a.1.1 k) (Metric.ball (0 : E) (ρ / 2)) := by
    intro a k
    exact (c a.1.2 (τ k)).overlap_on_ball_of_edist_add_le
      (g (τ k)) (hEnorm (τ k)) (x a.1.2 (τ k)) (x a.1.1 (τ k))
      (c a.1.1 (τ k)) hρ hρ hhalf
      ((hmarginrev a k).trans (ENNReal.ofReal_le_ofReal hbuffer))
  have hmap : ∀ a : P, ∀ k, Set.MapsTo ((nc a.1.1 k).transition (nc a.1.2 k))
      (Metric.ball (0 : E) (ρ / 2)) (Metric.ball (0 : E) (3 * ρ / 4)) := by
    intro a k
    exact (c a.1.1 (τ k)).transition_maps_to_ball_of_edist_add_le
      (g (τ k)) (hEnorm (τ k)) (x a.1.1 (τ k)) (x a.1.2 (τ k))
      (c a.1.2 (τ k)) hρ hρ hhalf hbuffer (hmargin a k)
  have hmaprev : ∀ a : P, ∀ k, Set.MapsTo ((nc a.1.2 k).transition (nc a.1.1 k))
      (Metric.ball (0 : E) (ρ / 2)) (Metric.ball (0 : E) (3 * ρ / 4)) := by
    intro a k
    exact (c a.1.2 (τ k)).transition_maps_to_ball_of_edist_add_le
      (g (τ k)) (hEnorm (τ k)) (x a.1.2 (τ k)) (x a.1.1 (τ k))
      (c a.1.1 (τ k)) hρ hρ hhalf hbuffer (hmarginrev a k)
  have hjetτ : ∀ i p, ∀ᶠ k in atTop, ∀ z ∈ Metric.ball (0 : E) (3 * ρ / 4),
      ‖iteratedFDeriv Real p ((nc i k).metric (g (τ k))) z‖ ≤ C i p := by
    intro i p
    filter_upwards [hτ.tendsto_atTop.eventually (hjets i p)] with k hk
    exact fun z hz => hk z (Metric.ball_subset_ball hbuffer hz)
  obtain ⟨psi, Jinf, Jbarinf, hpsi, hlim⟩ :=
    NormalBallChart.exists_finite_transition_limit_subsequence_of_eventually_bounded
      (fun k => g (τ k)) (fun a : P => fun k => x a.1.1 (τ k))
      (fun a : P => fun k => x a.1.2 (τ k))
      (fun a : P => nc a.1.1) (fun a : P => nc a.1.2)
      (fun _ => Metric.ball (0 : E) (ρ / 2)) (fun _ => Metric.ball (0 : E) (ρ / 2))
      (fun _ => Metric.ball (0 : E) (3 * ρ / 4))
      (fun _ => Metric.ball (0 : E) (3 * ρ / 4))
      (fun _ => Metric.isOpen_ball) (fun _ => Metric.isOpen_ball)
      (fun _ => Metric.isOpen_ball) (fun _ => Metric.isOpen_ball)
      (fun _ => Metric.ball_subset_ball hsub) (fun _ => Metric.ball_subset_ball hsub)
      (fun _ _ => Metric.ball_subset_ball hbuffer)
      (fun _ _ => Metric.ball_subset_ball hbuffer) hovl hovlrev hmap hmaprev
      (fun a k z hz v => hequiv a.1.1 (τ k) z (Metric.ball_subset_ball hbuffer hz) v)
      (fun a k z hz v => hequiv a.1.2 (τ k) z (Metric.ball_subset_ball hbuffer hz) v)
      (fun a => C a.1.1) (fun a => C a.1.2) (fun a => hC a.1.1) (fun a => hC a.1.2)
      (fun a => hjetτ a.1.1) (fun a => hjetτ a.1.2)
  refine ⟨τ ∘ psi, hτ.comp hpsi, near, fun k => hclass (psi k), ?_, Jinf, Jbarinf, hlim⟩
  intro k i j hij
  apply (c i (τ (psi k))).disjoint_image_ball_of_add_le_edist
    (g (τ (psi k))) (hEnorm (τ (psi k))) (x i (τ (psi k))) (x j (τ (psi k)))
    (c j (τ (psi k))) (by linarith) (by linarith)
  apply le_trans _ ((hclass (psi k) i j).2 hij)
  have h10 : 0 ≤ ρ / 10 := le_of_lt (div_pos hρ (by norm_num : (0:ℝ) < 10))
  rw [← ENNReal.ofReal_add h10 h10]
  apply ENNReal.ofReal_le_ofReal
  linarith

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

end
