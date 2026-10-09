import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.H0Defect_S103
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ScalarNegDefect_S56
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HoneS83_S129

set_option autoImplicit false

/-! # CH12-S135 G2: `hneg_S135` = the `hneg` binder of `hone_S129` (all-`j` conditional form), proved.

* `ckErr0_eval_S135`: `|c * g'(df V, df V) - h(V,V)| ≤ ckErr_S45 H g' c f 0 p * h(V,V)` for ANY `f` (no immersion needed):
  the order-0 pull-back error is the `Tensor0S` fibre norm of `c • localPullInner g' f p - h`, evaluated on `(V,V)`
  (`abs_apply_le_sqrt_normSq0S`).
* `pos_inj_of_ckErr0_S135`: order-0 error `< 1` forces `0 < c` and `Injective (mfderiv f p)` (no `0 < T`, no immersion premise
  is needed in `hneg`: both are derived from the error at one point of the ball).
* `hneg_S135`: `ε₁ := 1/2882`; `defect_of_ckErr_S103` (δ := ε₁, η := 1, `U` := the ball `B(4 ρ j)`, open) gives the Ricci defect
  `|2 t Ric + g| ≤ g`, hence `scalar_nonpos_of_quad_defect_S56` (c := t) gives `scal ≤ 0`.  Binder text of `hneg` cut from
  `HoneS83_S129.lean` l.67-79 by `scratch/s135/gen_g2.py`. -/

noncomputable section
open Set Filter Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Topology.Manifold TopologicalSpace
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
  DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Connection
  DifferentialGeometry.Tensor0SBundle GC.LongTime
open scoped Manifold ContDiff Topology
namespace GC.LongTime.Ch12
universe u

theorem ckErr0_eval_S135 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g' : SmoothRiemannianMetric (𝓡 3) N) (c : ℝ) (f : H.Carrier → N) (p : H.Carrier)
    (V : TangentSpace (𝓡 3) p) :
    |c * g'.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p V) (mfderiv (𝓡 3) (𝓡 3) f p V) -
        H.metric.inner p V V| ≤ ckErr_S45 H g' c f 0 p * H.metric.inner p V V := by
  classical
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis
    (I := 𝓡 3) H.metric p
  let T : Tensor0SBundle.Tensor0SSpace 2 (𝓡 3) p :=
    ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) p) ℝ).symm.toContinuousLinearMap.comp
          (c • localPullInner g' f p - H.metric.inner p)).uncurryLeft
  have hb := Tensor0SBundle.abs_apply_le_sqrt_normSq0S (I := 𝓡 3) (g := H.metric) (x := p) (s := 2) basis hON
    T (vec2 (I := 𝓡 3) V V)
  have hval : T (vec2 (I := 𝓡 3) V V) =
      c * g'.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p V) (mfderiv (𝓡 3) (𝓡 3) f p V) -
        H.metric.inner p V V := by
    refine (ContinuousLinearMap.uncurryLeft_apply _ _).trans ?_
    simp [vec2, localPullInner_apply, continuousMultilinearCurryFin1_symm_apply, Fin.tail]
  have hck : ckErr_S45 H g' c f 0 p = Real.sqrt (normSq0S (I := 𝓡 3) H.metric p 2 T) := by
    unfold ckErr_S45 tensor0SFiberNorm
    rfl
  have hs : Real.sqrt (H.metric.inner p V V) * Real.sqrt (H.metric.inner p V V) = H.metric.inner p V V :=
    Real.mul_self_sqrt (metric_inner_self_nonneg H.metric p V)
  have hprod : ∏ a : Fin 2, Real.sqrt (H.metric.inner p (vec2 (I := 𝓡 3) V V a) (vec2 (I := 𝓡 3) V V a)) =
      H.metric.inner p V V := by
    rw [Fin.prod_univ_two]
    simpa [vec2] using hs
  rw [hval, hprod] at hb
  rw [hck]
  exact hb

theorem pos_inj_of_ckErr0_S135 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g' : SmoothRiemannianMetric (𝓡 3) N) (c : ℝ) (f : H.Carrier → N) (p : H.Carrier)
    (h : ckErr_S45 H g' c f 0 p < 1) :
    0 < c ∧ Function.Injective (mfderiv (𝓡 3) (𝓡 3) f p) := by
  have hpos : ∀ V : TangentSpace (𝓡 3) p, V ≠ 0 → 0 < H.metric.inner p V V :=
    fun V hV => H.metric.pos p V hV
  constructor
  · by_contra hc
    replace hc := not_lt.mp hc
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) p) = 3 := by
      change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
      simp
    obtain ⟨V, hV⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by rw [hdim]; norm_num)
    have hVV := hpos V hV
    have h1 := ckErr0_eval_S135 H g' c f p V
    have hg : 0 ≤ g'.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p V) (mfderiv (𝓡 3) (𝓡 3) f p V) :=
      metric_inner_self_nonneg g' _ _
    have h2 : c * g'.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p V) (mfderiv (𝓡 3) (𝓡 3) f p V) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hc hg
    have h3 := (abs_le.mp h1).1
    nlinarith
  · rw [injective_iff_map_eq_zero]
    intro V hV0
    by_contra hV
    have hVV := hpos V hV
    have h1 := ckErr0_eval_S135 H g' c f p V
    rw [hV0] at h1
    simp only [map_zero, mul_zero, zero_sub, abs_neg] at h1
    rw [abs_of_pos hVV] at h1
    nlinarith

theorem hneg_S135 {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ (H : FiniteVolumeHyperbolicModel.{u}) (T : ℝ) (ρ : ℕ → ℝ) (η : ℕ → ℝ)
      (ν : ℕ → ℕ)
      (f : (j : ℕ) → (t : ℝ) → t ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1)) →
        H.Carrier → (postStage F.observation t).Carrier),
      (∀ j, η j ≤ ε₁) → (∀ j, 2 ≤ ν j) →
      (∀ j t (ht : t ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1))),
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f j t ht) (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
        Set.InjOn (f j t ht) (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
        ∀ k : ℕ, k ≤ ν j → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
          ckErr_S45 H (postMetric F.observation t) t⁻¹ (f j t ht) k p < η j) →
      ∀ j (t : ℝ) (ht : t ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1))),
        ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
          metricScalarAt (postMetric F.observation t) (f j t ht p) ≤ 0 := by
  refine ⟨1 / 2882, by norm_num, ?_⟩
  intro H T ρ η ν f hη hν hf j t ht p hp
  obtain ⟨hC, _hinjOn, herr⟩ := hf j t ht
  have hck : ∀ q ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j), ∀ k : ℕ, k ≤ 2 →
      ckErr_S45 H (postMetric F.observation t) t⁻¹ (f j t ht) k q < 1 / 2882 :=
    fun q hq k hk => lt_of_lt_of_le (herr k (hk.trans (hν j)) q hq) (hη j)
  have hlt1 : ∀ q ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
      ckErr_S45 H (postMetric F.observation t) t⁻¹ (f j t ht) 0 q < 1 :=
    fun q hq => lt_trans (hck q hq 0 (by norm_num)) (by norm_num)
  obtain ⟨htinv, _⟩ := pos_inj_of_ckErr0_S135 H (postMetric F.observation t) t⁻¹ (f j t ht) p (hlt1 p hp)
  have htpos : 0 < t := inv_pos.mp htinv
  let U : TopologicalSpace.Opens H.Carrier :=
    ⟨riemannianBallOf H.metric H.basepoint (4 * ρ j), isOpen_riemannianBallOf H.metric H.basepoint _⟩
  have hinj : ∀ y ∈ U, Function.Injective (mfderiv (𝓡 3) (𝓡 3) (f j t ht) y) :=
    fun y hy => (pos_inj_of_ckErr0_S135 H (postMetric F.observation t) t⁻¹ (f j t ht) y (hlt1 y hy)).2
  have hdef := fun V : TangentSpace (𝓡 3) (f j t ht p) =>
    defect_of_ckErr_S103 H (postMetric F.observation t) htpos (f j t ht) U hC hinj
      (δ := 1 / 2882) (η := 1) (by norm_num) (by norm_num) hp (fun k hk => hck p hp k hk) V
  exact scalar_nonpos_of_quad_defect_S56 (postMetric F.observation t) (f j t ht p) htpos le_rfl hdef

end GC.LongTime.Ch12
