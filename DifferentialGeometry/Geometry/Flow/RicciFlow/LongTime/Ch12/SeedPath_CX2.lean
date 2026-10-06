import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SmoothFirstExit_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SliceSeeds_CX2

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
  DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- The final seed and every point of the doubled test ball are joined by a
smooth path shorter than 3r, as in D-WBD §4.4. -/
theorem exists_seed_to_ball_path_CX2 (P : OrientedThreeStage.{u}) (g : P.Metric)
    {p y x : P.Carrier} {r : ℝ} (hr : 0 < r)
    (hy : y ∈ riemannianBallOf g p r) (hx : x ∈ riemannianBallOf g p (2 * r)) :
    ∃ γ : ℝ → P.Carrier, γ 0 = y ∧ γ 1 = x ∧
      ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 γ (Icc (0 : ℝ) 1) ∧
      metricPathELength g γ 0 1 < ENNReal.ofReal (3 * r) := by
  have hd : riemannianEDistOf g y x < ENNReal.ofReal (3 * r) := by
    have hy' : riemannianEDistOf g y p < ENNReal.ofReal r := by
      rw [riemannianEDistOf_comm]
      exact hy
    have hsum := (riemannianEDistOf_triangle g y p x).trans_lt (ENNReal.add_lt_add hy' hx)
    have heq : ENNReal.ofReal r + ENNReal.ofReal (2 * r) = ENNReal.ofReal (3 * r) := by
      rw [← ENNReal.ofReal_add hr.le (by positivity)]
      congr 1
      ring
    exact hsum.trans_eq heq
  exact exists_lt_of_edistOf_lt g hd

/-- Pointwise seeds chosen independently at different times have the same
centre as the restriction of a single seed trace. -/
theorem seed_trace_point_unique_CX2 (H : ObservedHistory.{u})
    {a v t : Icc (0 : ℝ) H.horizon} {hat : a ≤ t} (hav : a ≤ v) (hvt : v ≤ t)
    {y : (H.stageAt t).Carrier}
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) y)
    (B : BackwardPointTrace H (H.activeStage v) (H.activeStage t) (H.activeStage_mono hvt) y) :
    A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt) =
      B.point (H.activeStage v) le_rfl (H.activeStage_mono hvt) := by
  have heq : A.restrictFirst (H.activeStage_mono hav) (H.activeStage_mono hvt) = B :=
    Subsingleton.elim _ _
  exact congrArg (fun C => C.point (H.activeStage v) le_rfl (H.activeStage_mono hvt)) heq

/-- The frozen G2 centres and seeds feed G3a along a single actual trace.
The hypothesis below spells out G2's backward-trace clause; it does not
assume a traced region for the doubled test ball. -/
theorem enlarged_rm_bound_along_seed_trace_CX2
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    {a c₁ : ℝ} (ha : 0 < a) (hc₁ : 0 < c₁) :
    ∃ T₀ ρ₀ K₀ : ℝ, 0 < T₀ ∧ 0 < ρ₀ ∧ 0 < K₀ ∧
      ∀ (s : RegularSlice F.observation) (l : Icc (0 : ℝ) s.history.horizon)
        (hlt : l ≤ sliceTop_S8 s) (y : (s.history.stageAt (sliceTop_S8 s)).Carrier)
        (r : ℝ), 0 < r →
      (∀ v : Icc (0 : ℝ) s.history.horizon, l ≤ v →
        T₀ ≤ (v : ℝ) ∧ r ≤ ρ₀ * Real.sqrt v) →
      (∀ (v : Icc (0 : ℝ) s.history.horizon) (_ : l ≤ v),
        ∃ yv : (s.history.stageAt v).Carrier,
          hasSmallParabolicCurvature s.history v yv (a * r) ∧
          ENNReal.ofReal (c₁ * (a * r) ^ 3) ≤
            ballVolume (s.history.stageMetric (s.history.activeStage v) v) yv (a * r) ∧
          ∃ A : BackwardPointTrace s.history (s.history.activeStage v)
              (s.history.activeStage (sliceTop_S8 s))
              (s.history.activeStage_mono (show v ≤ sliceTop_S8 s from v.property.2)) y,
            A.point (s.history.activeStage v) le_rfl
              (s.history.activeStage_mono (show v ≤ sliceTop_S8 s from v.property.2)) = yv) →
      ∃ A : BackwardPointTrace s.history (s.history.activeStage l)
          (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono hlt) y,
        ∀ (v : Icc (0 : ℝ) s.history.horizon) (hlv : l ≤ v),
          ∀ q ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage v) v)
            (A.point (s.history.activeStage v) (s.history.activeStage_mono hlv)
              (s.history.activeStage_mono (show v ≤ sliceTop_S8 s from v.property.2))) (20 * r),
            Real.sqrt (normSq0S (s.history.stageMetric (s.history.activeStage v) v) q 4
              (metricRm04At (s.history.stageMetric (s.history.activeStage v) v) q)) ≤ K₀ / r ^ 2 := by
  obtain ⟨T₀, ρ₀, K₀, hT, hρ, hK, henlarge⟩ := enlarged_rm_bound_of_slice_seed_CX2 Hp ha hc₁
  refine ⟨T₀, ρ₀, K₀, hT, hρ, hK, ?_⟩
  intro s l hlt y r hr hsize hseed
  obtain ⟨_, _, _, A, _⟩ := hseed l le_rfl
  refine ⟨A, ?_⟩
  intro v hlv q hq
  obtain ⟨yv, hseedv, hvolv, B, hB⟩ := hseed v hlv
  have hpoint := (seed_trace_point_unique_CX2 s.history (hat := hlt) hlv
    (show v ≤ sliceTop_S8 s from v.property.2) A B).trans hB
  have hq' : q ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage v) v) yv (20 * r) := by
    rwa [hpoint] at hq
  exact henlarge s v yv r hr (hsize v hlv).1 (hsize v hlv).2 hseedv hvolv q hq'

/-- The precise 20r smooth-stage buffer used in G3b, with the original
parabolic time and curvature normalizations. -/
theorem smooth_path_first_exit_scaled_CX2 (P : OrientedThreeStage.{u}) {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := P.Carrier) D) (hS : IsSolutionOn S)
    {a b K τ r : ℝ} (hab : a ≤ b) (hK : 0 ≤ K) (hr : 0 < r)
    (hcarrier : Icc a b ⊆ D.carrier) (hregular : Ioo a b ⊆ D.regular)
    (htime : b - a ≤ τ * r ^ 2) (hτ : Real.exp (9 * K * τ) < 2)
    (γ : ℝ → P.Carrier) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 γ (Icc (0 : ℝ) 1))
    (hlen : metricPathELength (S.base.metric b) γ 0 1 ≤ ENNReal.ofReal (3 * r))
    (hRm : ∀ t ∈ Icc a b, ∀ x ∈ riemannianBallOf (S.base.metric t) (γ 0) (20 * r),
      Real.sqrt (normSq0S (S.base.metric t) x 4 (S.base.rm04 t x)) ≤ K / r ^ 2) :
    ∀ t ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) 1,
      γ s ∈ riemannianBallOf (S.base.metric t) (γ 0) (20 * r) ∧
      Real.sqrt (normSq0S (S.base.metric t) (γ s) 4 (S.base.rm04 t (γ s))) ≤ K / r ^ 2 := by
  have hroom : Real.exp (9 * (K / r ^ 2) * (b - a)) * (3 * r) < 20 * r := by
    have he : 9 * (K / r ^ 2) * (b - a) ≤ 9 * K * τ := by
      have heq : 9 * (K / r ^ 2) * (τ * r ^ 2) = 9 * K * τ := by
        field_simp
      exact (mul_le_mul_of_nonneg_left htime (by positivity)).trans_eq heq
    have hlt := (Real.exp_le_exp.mpr he).trans_lt hτ
    have hprod := mul_lt_mul_of_pos_right hlt (by positivity : 0 < 3 * r)
    nlinarith
  have hstay := smooth_path_first_exit_CX2 P S hS hab (by positivity : 0 ≤ K / r ^ 2)
    (by positivity : 0 ≤ 3 * r) hcarrier hregular γ hγ hlen hroom hRm
  intro t ht s hs
  exact ⟨hstay t ht s hs, hRm t ht (γ s) (hstay t ht s hs)⟩

end GC.LongTime.Ch12
