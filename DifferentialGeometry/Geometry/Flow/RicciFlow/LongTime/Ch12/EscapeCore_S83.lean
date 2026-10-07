import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HoneFin_S72

set_option autoImplicit false

/-! # CH12-S83 G1: abstract core of escape persistence

* `no_reentry_dyadic_S83`: a track `x t` that is outside the "outer old core" `C1 t` at the start time `T`, whose
  membership in `C1` forces membership in the "inner old core" `C0` (thin barrier, `hband`), and such that
  membership in `C0` at a later time `t ∈ [r, 2r]` forces membership in `C1` at the earlier time `r` (slow drift,
  `hdrift`), stays outside `C1` for all `t ≥ T` (induction over dyadic windows).
* `thick_thin_false_S83`: a point cannot be both `wstar`-thick and `wstar`-thin at the same scale.
* `anchor_escape_S83`: at `T = t_i` the explicit dyadic map sends the basepoint to `S.point i` (anchor, `θ = 0` near 1). -/
noncomputable section
open Set Filter Topology DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open Manifold GC.LongTime DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal
namespace GC.LongTime.Ch12
universe u v

theorem no_reentry_dyadic_S83 {X : ℝ → Type v} (T : ℝ) (hT : 0 < T)
    (x : ∀ t, T ≤ t → X t) (C0 C1 : ∀ t, Set (X t))
    (hband : ∀ t (ht : T ≤ t), x t ht ∈ C1 t → x t ht ∈ C0 t)
    (hdrift : ∀ r t (hr : T ≤ r) (ht : T ≤ t), r ≤ t → t ≤ 2 * r → x t ht ∈ C0 t → x r hr ∈ C1 r)
    (hstart : x T le_rfl ∉ C1 T) : ∀ t (ht : T ≤ t), x t ht ∉ C1 t := by
  have step : ∀ r (hr : T ≤ r), x r hr ∉ C1 r → ∀ t (ht : T ≤ t), r ≤ t → t ≤ 2 * r →
      x t ht ∉ C1 t := by
    intro r hr hxr t ht h1 h2 hxt
    exact hxr (hdrift r t hr ht h1 h2 (hband t ht hxt))
  have hge : ∀ k : ℕ, T ≤ 2 ^ k * T := fun k =>
    le_mul_of_one_le_left hT.le (one_le_pow₀ (by norm_num))
  have h0 : ∀ t (h : t = T) (ht : T ≤ t), x t ht ∉ C1 t := by
    intro t h; subst h; intro ht; exact hstart
  have dy : ∀ k : ℕ, x (2 ^ k * T) (hge k) ∉ C1 (2 ^ k * T) := by
    intro k
    induction k with
    | zero => exact h0 _ (by simp) _
    | succ k ih =>
      have hp : (0 : ℝ) < 2 ^ k := by positivity
      exact step _ (hge k) ih _ (hge (k + 1)) (by rw [pow_succ]; nlinarith)
        (by rw [pow_succ]; nlinarith)
  intro t ht
  obtain ⟨hj1, hj2⟩ := dyadicIndex_mem_CX5 hT ht
  have hj1' : 2 ^ dyadicIndex_CX5 T t * T ≤ t := hj1
  have hj2' : t ≤ 2 * (2 ^ dyadicIndex_CX5 T t * T) := by
    have : t < 2 ^ (dyadicIndex_CX5 T t + 1) * T := hj2
    have hp : (0 : ℝ) < 2 ^ dyadicIndex_CX5 T t := by positivity
    rw [pow_succ] at this; nlinarith
  exact step _ (hge _) (dy _) t ht hj1' hj2'

theorem thick_thin_false_S83 {α : Type*} (cr : α → ENNReal) (vol : α → ℝ → ENNReal) (w : ℝ) (y : α)
    (hk : ∃ r : ℝ, 0 < r ∧ cr y = ENNReal.ofReal r ∧ ENNReal.ofReal (w * r ^ 3) ≤ vol y r)
    (hn : ∀ r : ℝ, 0 < r → cr y = ENNReal.ofReal r → vol y r < ENNReal.ofReal (w * r ^ 3)) : False := by
  obtain ⟨r, hr, hcr, hv⟩ := hk
  exact absurd (hn r hr hcr) (not_lt.mpr hv)

theorem anchor_escape_S83 {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (S : LatePointSequence_S13 F) (H : FiniteVolumeHyperbolicModel.{u})
    (Φ : PointedRiemannianConvergenceMaps S.pointedSeq (modelPointed_S13 H) id) (i : ℕ)
    (hT : 0 < (S.slices i).time) (θ : ℝ → ℝ) (hθ0 : ∀ s, s ≤ 7 / 4 → θ s = 0)
    (f : (j : ℕ) → (t : ℝ) → t ∈ Icc (2 ^ j * (S.slices i).time) (2 ^ (j + 1) * (S.slices i).time) →
      H.Carrier → (postStage F.observation t).Carrier)
    (E : ℕ → ℝ × H.Carrier → H.Carrier) (ρ : ℕ → ℝ) (hρpos : ∀ j, 0 < ρ j)
    (hE0 : ∀ j p, E j (0, p) = p)
    (hanchor : ∀ (h0 : 2 ^ 0 * (S.slices i).time ∈ Icc (2 ^ 0 * (S.slices i).time) (2 ^ (0 + 1) * (S.slices i).time)),
      ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ 0),
        HEq (f 0 _ h0 p) (sliceApprox_O32 S H Φ i p)) :
    sliceCast_CX4 (S.slices i) (smoothedPhysicalMap_CX5 H (S.slices i).time hT θ f E (S.slices i).time le_rfl H.basepoint) =
      S.point i := by
  have hj : dyadicIndex_CX5 (S.slices i).time (S.slices i).time = 0 := by
    apply dyadicIndex_eq_CX5 hT
    refine ⟨by simp [dyadicTime_CX5], ?_⟩
    simp only [dyadicTime_CX5]; norm_num; linarith
  have hbp : H.basepoint ∈ riemannianBallOf H.metric H.basepoint (4 * ρ 0) :=
    (by change riemannianEDistOf H.metric H.basepoint H.basepoint < ENNReal.ofReal (4 * ρ 0)
        rw [riemannianEDistOf_self]
        exact ENNReal.ofReal_pos.mpr (by linarith [hρpos 0]))
  have gen : ∀ (j : ℕ), j = 0 → ∀ (hm : (S.slices i).time ∈ Icc (2 ^ j * (S.slices i).time)
      (2 ^ (j + 1) * (S.slices i).time)),
      sliceCast_CX4 (S.slices i) (f j (S.slices i).time hm
        (E j (θ ((S.slices i).time / (2 ^ j * (S.slices i).time)), H.basepoint))) = S.point i := by
    intro j hj0 hm
    subst hj0
    have h1 : θ ((S.slices i).time / (2 ^ 0 * (S.slices i).time)) = 0 :=
      hθ0 _ (by simp [div_self hT.ne']; norm_num)
    rw [h1, hE0]
    have hcongr : ∀ (t t' : ℝ) (e : t = t') (h : t ∈ Icc (2 ^ 0 * (S.slices i).time)
        (2 ^ (0 + 1) * (S.slices i).time)) (h' : t' ∈ Icc (2 ^ 0 * (S.slices i).time)
        (2 ^ (0 + 1) * (S.slices i).time)), HEq (f 0 t h H.basepoint) (f 0 t' h' H.basepoint) := by
      intro t t' e h h'; subst e; rfl
    have hh := hanchor ⟨le_rfl, by norm_num; linarith⟩ H.basepoint hbp
    have h2 := (hcongr _ _ (by simp) hm ⟨le_rfl, by norm_num; linarith⟩).trans hh
    have h3 : HEq (sliceApprox_O32 S H Φ i H.basepoint) (Φ.partialDiffeomorph i H.basepoint) :=
      cast_heq _ _
    have h4 : Φ.partialDiffeomorph i H.basepoint = S.point i := Φ.basepoint_map i
    exact eq_of_heq ((cast_heq _ _).trans ((h2.trans h3).trans (heq_of_eq h4)))
  exact gen _ hj _

end GC.LongTime.Ch12
