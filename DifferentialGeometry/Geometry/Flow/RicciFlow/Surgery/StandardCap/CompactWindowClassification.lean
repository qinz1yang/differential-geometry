import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.AmbientSpatialCap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactCanonicalCover
import DifferentialGeometry.Geometry.Neck.CompactCapClassification

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v

theorem exists_eventually_poincareStandard_of_canonical_and_cap_windows_tolerance :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, 0 < eps → eps ≤ eta →
      ∀ (D r : ℝ), StandardCap.transitionEnd + eps⁻¹ + 1 < r →
      r + eps⁻¹ + 1 ≤ D → 2 * StandardCap.transitionEnd + 2000 < r / 2 →
      ∀ N : ℕ, ⌈eps⁻¹⌉₊ ≤ N →
      ∀ (J : Type v) [Finite J]
        (M : ℕ → ConnectedClosedOrientedManifold.{u} 3)
        (T : ℕ → RealTimeInterval)
        (S : ∀ n, SolutionOn (I := I3) (M := (M n).Carrier) (T n))
        (time : ℕ → ℝ) (C1 C2 : ℝ)
        (g : ℕ → J → SmoothRiemannianMetric I3 (standardCapWindow D))
        (q : ℕ → J → ℝ) (hq : ∀ n j, 0 < q n j)
        (Phi : ∀ n, J → standardCapWindow D → (M n).Carrier),
      (∀ j, MetricCPConvergenceOn {y : standardCapWindow D | ‖y.val‖ ≤ r+eps⁻¹} N
        (fun n => g n j) (StandardCap.metric.restrictOpen (standardCapWindow D))
        (StandardCap.metric.restrictOpen (standardCapWindow D))) →
      (∀ n j, IsLocalDiffeomorph I3 I3 ∞ (Phi n j)) →
      (∀ n j, Injective (Phi n j)) →
      (∀ n j (y : standardCapWindow D) (v w : TangentSpace I3 y),
        (g n j).inner y v w =
          (scaleMetric (q n j) (hq n j) ((S n).base.metric (time n))).inner (Phi n j y)
            (mfderiv I3 I3 (Phi n j) y v) (mfderiv I3 I3 (Phi n j) y w)) →
      (∀ᶠ n in atTop, ∀ x : (M n).Carrier,
        ¬ Nonempty (SpatialNeck ((S n).base.metric (time n)) eps x) →
        (∃ W : CanonicalWitness (S n) eps C1 C2 x (time n), W.capTubeHasNeckChart eps) ∨
          ∃ (j : J) (y : standardCapWindow D), ‖y.val‖ ≤ StandardCap.transitionEnd ∧
            Phi n j y = x) →
      ∀ᶠ n in atTop, isPoincareStandard (M n).Carrier := by
  obtain ⟨eta, heta, hclass⟩ := exists_compact_spatial_poincareStandard_tolerance.{u}
  refine ⟨min eta (1 / 22), lt_min heta (by norm_num), ?_⟩
  intro eps heps hsmall D r hr hfit hdepth N hN J _ M T S time C1 C2 g q hq Phi
    hconv hPhi hinj hmetric hcover
  have hepssmall : eps < 1 / 11 := (hsmall.trans (min_le_right _ _)).trans_lt (by norm_num)
  have hcaps (j : J) := StandardCap.eventually_spatial_cap_of_rescaled_window_convergence
    D r eps heps hepssmall hr hfit hdepth N hN (fun n => g n j) (hconv j)
    (fun n => (M n).Carrier) (fun n => (S n).base.metric (time n))
    (fun n => q n j) (fun n => hq n j) (fun n => Phi n j)
    (fun n => hPhi n j) (fun n => hinj n j) (fun n => hmetric n j)
  have hall := eventually_all.mpr hcaps
  filter_upwards [hcover, hall] with n hn hcap
  apply hclass eps (hsmall.trans (min_le_left _ _)) (M n) ((S n).base.metric (time n))
  intro x hx
  rcases hn x hx with ⟨W, hchart⟩ | ⟨j, y, hy, hpoint⟩
  · rcases W.spatial_cap_or_whole_of_not_spatial_neck hchart hx with hp | hr | hc
    · exact Or.inl hp
    · obtain ⟨z, hz⟩ := hr
      exact Or.inr (Or.inl
        (admitsConstantPositiveSectionalCurvature_of_roundComponent (M n) hz.some))
    · exact Or.inr (Or.inr hc)
  · obtain ⟨p, nk, K, _, hcore, hmarks, hfront, _⟩ := hcap j
    obtain ⟨hR, _, hball⟩ := hmarks y hy
    refine Or.inr (Or.inr ⟨K, Phi n j p, nk, 0, ?_, hcore, by norm_num, hfront, ?_⟩)
    · simpa only [hpoint] using hR
    · simpa only [hpoint] using hball

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
