import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Transition.IntrinsicOverlap
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Basic
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Transition.LimitIdentities
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Transition.CenterClassification

section

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

open Bundle Filter Topology
open scoped Manifold ContDiff ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  [∀ k, IsManifold I ∞ (M k)] [∀ k, T2Space (M k)] [∀ k, SigmaCompactSpace (M k)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [∀ k, PseudoEMetricSpace (M k)]
  [∀ k, RiemannianBundle (fun x : M k => TangentSpace I x)]
  [∀ k, IsRiemannianManifold I (M k)] [∀ k, CompleteSpace (M k)]
  [∀ k, IsContinuousRiemannianBundle E (fun x : M k => TangentSpace I x)]

theorem IntrinsicBallChart.norm_transition_limit_le_of_edist_add_le
    (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k (x : M k) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g k).inner x v v)))
    (p q : ∀ k, M k) {r r' a b : Real}
    (c : ∀ k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (p k) r)
    (d : ∀ k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (q k) r')
    (hr : 0 < r) (hr' : 0 < r') (har : a ≤ r) (hbr : b ≤ r')
    {U : Set E} {J : E → E}
    (hconv : CheegerGromovCompactness.MapCInfConvergenceOnCompacts U
      (fun k => ((c k).toNormalBallChart (g k) (hEnorm k) (p k) hr).transition
        ((d k).toNormalBallChart (g k) (hEnorm k) (q k) hr')) J)
    (hmargin : ∀ᶠ k in atTop, edist (p k) (q k) + ENNReal.ofReal a ≤ ENNReal.ofReal b)
    {z : E} (hzU : z ∈ U) (hz : z ∈ Metric.ball (0 : E) a) :
    ‖J z‖ ≤ b := by
  have htail : ∀ᶠ k in atTop,
      ‖((c k).toNormalBallChart (g k) (hEnorm k) (p k) hr).transition
        ((d k).toNormalBallChart (g k) (hEnorm k) (q k) hr') z‖ ≤ b := by
    filter_upwards [hmargin] with k hk
    have hm := (c k).transition_maps_to_ball_of_edist_add_le (g k) (hEnorm k)
      (p k) (q k) (d k) hr hr' har hbr hk hz
    exact (show ‖_‖ < b by simpa only [Metric.mem_ball, dist_zero_right] using hm).le
  exact le_of_tendsto (CheegerGromovCompactness.tendsto_of_cInf hconv hzU).norm htail

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates


end

section

set_option autoImplicit false

noncomputable section

open Bundle Filter
open scoped Manifold ContDiff ENNReal

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

variable (g : ∀ k, SmoothRiemannianMetric I (M k))
  (hEnorm : ∀ k (x : M k) (v : TangentSpace I x),
    ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g k).inner x v v)))
  (p q : ∀ k, M k) {ρ : Real} (hρ : 0 < ρ)
  (c : ∀ k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (p k) ρ)
  (d : ∀ k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (q k) ρ)

private theorem eventually_overlap_on_half_ball
    (hnear : ∀ᶠ k in atTop, edist (p k) (q k) < ENNReal.ofReal (ρ / 4)) :
    ∀ᶠ k in atTop,
      ((c k).toNormalBallChart (g k) (hEnorm k) (p k) hρ).OverlapOn
        ((d k).toNormalBallChart (g k) (hEnorm k) (q k) hρ)
        (Metric.ball (0 : E) (ρ / 2)) := by
  filter_upwards [hnear] with k hk
  apply (c k).overlap_on_ball_of_edist_add_le
    (g k) (hEnorm k) (p k) (q k) (d k) hρ hρ (by linarith)
  calc
    edist (p k) (q k) + ENNReal.ofReal (ρ / 2)
        ≤ ENNReal.ofReal (ρ / 4) + ENNReal.ofReal (ρ / 2) :=
      add_le_add hk.le le_rfl
    _ = ENNReal.ofReal (ρ / 4 + ρ / 2) :=
      (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal ρ := ENNReal.ofReal_le_ofReal (by linarith)

theorem IntrinsicBallChart.transition_limit_mapsTo_ball_of_lt
    {s : Real} (hs : 0 ≤ s) (hsρ : s < ρ / 4)
    {J : E → E}
    (hconv : CheegerGromovCompactness.MapCInfConvergenceOnCompacts
      (Metric.ball (0 : E) (ρ / 2))
      (fun k => ((c k).toNormalBallChart (g k) (hEnorm k) (p k) hρ).transition
        ((d k).toNormalBallChart (g k) (hEnorm k) (q k) hρ)) J)
    (hnear : ∀ᶠ k in atTop, edist (p k) (q k) < ENNReal.ofReal (ρ / 4)) :
    Set.MapsTo J (Metric.ball (0 : E) s) (Metric.ball (0 : E) (ρ / 2)) := by
  intro z hz
  have hnorm : ‖J z‖ ≤ (ρ / 4 + s) := by
    apply IntrinsicBallChart.norm_transition_limit_le_of_edist_add_le
      g hEnorm p q c d hρ hρ (by linarith) (by linarith) hconv
      (a := s) (b := (ρ / 4 + s)) ?_
      (Metric.ball_subset_ball (by linarith) hz) hz
    filter_upwards [hnear] with k hk
    calc
      edist (p k) (q k) + ENNReal.ofReal s
          ≤ ENNReal.ofReal (ρ / 4) + ENNReal.ofReal s := add_le_add hk.le le_rfl
      _ = ENNReal.ofReal (ρ / 4 + s) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
  simpa only [Metric.mem_ball, dist_zero_right] using
    hnorm.trans_lt (show (ρ / 4 + s) < ρ / 2 by linarith)

theorem IntrinsicBallChart.transition_limit_inverse_on_ball_of_lt
    {s : Real} (hs : 0 ≤ s) (hsρ : s < ρ / 4)
    {J K : E → E}
    (hJ : CheegerGromovCompactness.MapCInfConvergenceOnCompacts
      (Metric.ball (0 : E) (ρ / 2))
      (fun k => ((c k).toNormalBallChart (g k) (hEnorm k) (p k) hρ).transition
        ((d k).toNormalBallChart (g k) (hEnorm k) (q k) hρ)) J)
    (hK : CheegerGromovCompactness.MapCInfConvergenceOnCompacts
      (Metric.ball (0 : E) (ρ / 2))
      (fun k => ((d k).toNormalBallChart (g k) (hEnorm k) (q k) hρ).transition
        ((c k).toNormalBallChart (g k) (hEnorm k) (p k) hρ)) K)
    (hcontJ : ContinuousOn J (Metric.ball (0 : E) (ρ / 2)))
    (hcontK : ContinuousOn K (Metric.ball (0 : E) (ρ / 2)))
    (hnear : ∀ᶠ k in atTop, edist (p k) (q k) < ENNReal.ofReal (ρ / 4)) :
    Set.InvOn K J (Metric.ball (0 : E) s) (Metric.ball (0 : E) s) := by
  have hrev : ∀ᶠ k in atTop, edist (q k) (p k) < ENNReal.ofReal (ρ / 4) := by
    simpa only [edist_comm] using hnear
  have hsub : Metric.ball (0 : E) s ⊆ Metric.ball (0 : E) (ρ / 2) :=
    Metric.ball_subset_ball (by linarith)
  constructor
  · intro z hz
    exact NormalBallChart.transition_limit_cancel
      (fun k => (c k).toNormalBallChart (g k) (hEnorm k) (p k) hρ)
      (fun k => (d k).toNormalBallChart (g k) (hEnorm k) (q k) hρ)
      Metric.isOpen_ball hJ hK hcontK
      (eventually_overlap_on_half_ball g hEnorm p q hρ c d hnear)
      (hsub hz) (IntrinsicBallChart.transition_limit_mapsTo_ball_of_lt g hEnorm p q hρ c d hs hsρ hJ hnear hz)
  · intro z hz
    exact NormalBallChart.transition_limit_cancel
      (fun k => (d k).toNormalBallChart (g k) (hEnorm k) (q k) hρ)
      (fun k => (c k).toNormalBallChart (g k) (hEnorm k) (p k) hρ)
      Metric.isOpen_ball hK hJ hcontJ
      (eventually_overlap_on_half_ball g hEnorm q p hρ d c hrev)
      (hsub hz) (IntrinsicBallChart.transition_limit_mapsTo_ball_of_lt g hEnorm q p hρ d c hs hsρ hK hrev hz)

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

end

section

set_option autoImplicit false

noncomputable section

open Bundle Filter
open scoped Manifold ContDiff ENNReal

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

theorem IntrinsicBallChart.transition_limit_trans_on_ball
    {ι : Type*}
    (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k (x : M k) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g k).inner x v v)))
    (x : ι → ∀ k, M k) {ρ : Real} (hρ : 0 < ρ)
    (c : ∀ i k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (x i k) ρ)
    (near : ι → ι → Bool)
    (hnear : ∀ i j, ∀ᶠ k in atTop,
      (near i j = true → edist (x i k) (x j k) < ENNReal.ofReal (ρ / 4)) ∧
      (near i j = false → ENNReal.ofReal (ρ / 4) ≤ edist (x i k) (x j k)))
    (J : {a : ι × ι // near a.1 a.2 = true} → E → E)
    (hcont : ∀ a, ContinuousOn (J a) (Metric.ball (0 : E) (ρ / 2)))
    (hconv : ∀ a, CheegerGromovCompactness.MapCInfConvergenceOnCompacts
      (Metric.ball (0 : E) (ρ / 2))
      (fun k => ((c a.1.1 k).toNormalBallChart (g k) (hEnorm k) (x a.1.1 k) hρ).transition
        ((c a.1.2 k).toNormalBallChart (g k) (hEnorm k) (x a.1.2 k) hρ)) (J a))
    {s : Real} (hs : 0 ≤ s) (hsρ : s ≤ ρ / 8)
    {i j l : ι} (hij : near i j = true) (hjl : near j l = true)
    {z : E} (hz : z ∈ Metric.ball (0 : E) s)
    (hJij : J ⟨(i, j), hij⟩ z ∈ Metric.ball (0 : E) s)
    (hJjl : J ⟨(j, l), hjl⟩ (J ⟨(i, j), hij⟩ z) ∈ Metric.ball (0 : E) s) :
    ∃ hil : near i l = true,
      J ⟨(i, l), hil⟩ z = J ⟨(j, l), hjl⟩ (J ⟨(i, j), hij⟩ z) := by
  let nc : ∀ i k, NormalBallChart (I := I) (x i k) := fun i k =>
    (c i k).toNormalBallChart (g k) (hEnorm k) (x i k) hρ
  have hovl : ∀ a : {a : ι × ι // near a.1 a.2 = true},
      ∀ᶠ k in atTop, (nc a.1.1 k).OverlapOn (nc a.1.2 k)
        (Metric.ball (0 : E) (ρ / 2)) := by
    intro a
    filter_upwards [hnear a.1.1 a.1.2] with k hk
    apply (c a.1.1 k).overlap_on_ball_of_edist_add_le
      (g k) (hEnorm k) (x a.1.1 k) (x a.1.2 k) (c a.1.2 k) hρ hρ
      (by linarith)
    calc
      edist (x a.1.1 k) (x a.1.2 k) + ENNReal.ofReal (ρ / 2)
          ≤ ENNReal.ofReal (ρ / 4) + ENNReal.ofReal (ρ / 2) :=
        add_le_add (hk.1 a.2).le le_rfl
      _ = ENNReal.ofReal (ρ / 4 + ρ / 2) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ ENNReal.ofReal ρ := ENNReal.ofReal_le_ofReal (by linarith)
  have hfar : ∀ i j, near i j = false →
      ∀ᶠ k in atTop, Disjoint ((nc i k).hom '' Metric.ball (0 : E) s)
        ((nc j k).hom '' Metric.ball (0 : E) s) := by
    intro i j hij
    filter_upwards [hnear i j] with k hk
    apply (c i k).disjoint_image_ball_of_add_le_edist
      (g k) (hEnorm k) (x i k) (x j k) (c j k) (by linarith) (by linarith)
    apply le_trans _ (hk.2 hij)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    linarith
  have hsub : Metric.ball (0 : E) s ⊆ Metric.ball (0 : E) (ρ / 2) :=
    Metric.ball_subset_ball (by linarith)
  have hil : near i l = true :=
    NormalBallChart.near_of_composable_transition_limits x nc near
      Metric.isOpen_ball Metric.isOpen_ball hsub J hconv hcont hovl hfar
      hij hjl hz (hsub hJij) hJjl
  refine ⟨hil, ?_⟩
  exact (NormalBallChart.transition_limit_comp_of_near x nc near
    Metric.isOpen_ball J hconv hcont hovl hij hjl hil (hsub hz) (hsub hJij)).symm

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

end
