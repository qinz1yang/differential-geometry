import DifferentialGeometry.Geometry.Collapse.EdgeFullCollar
import DifferentialGeometry.Geometry.Collapse.EdgeSharedLowCollar
import DifferentialGeometry.Geometry.Collapse.SublevelCore.ScaledMinimizingDirections
import DifferentialGeometry.Geometry.Collapse.StrongEdgeDiskCover

/-!
# LFR38 for a finite family: one smoothing, the full collar at every centre

Blueprint 207A, LFR38 (A:28243–28320), second paragraph of the statement and last paragraph of the
proof. The physical shared smoothing (`exists_shared_low_collar_smoothing`) is transported to the
normalization `(M, ρ(p)⁻¹ d, ρ(p)⁻² g)` of every centre, realized by the instances
`m.rescale ρ(p)⁻¹`, `radialScaledBundle`, `radialScaledContinuous`, `radialScaledManifold`, and
`exists_edge_full_collar_parameters` is applied there with `F/ρ(p)`, `ρ/ρ(p)` and the normalized
chart `ρ(p)⁻¹ Q_p`. Note `(F/ρ(p))/(ρ/ρ(p)) = F/ρ`: the SAME `η` at every centre.

Transport lemmas:
* `radialScaled_low_collar_gradient`: the nearest-direction gradient clause of `F` becomes that of
  `F/R` in the normalized metric (same `ε`);
* `radialScaled_chart_clauses`: a coarse-border chart at physical scale `ΔR` becomes the chart
  `R⁻¹ Q` at scale `Δ` of the normalized metric;
* `radialScaled_div_lipschitzWith`: `(1+ε)`-Lipschitz `F` gives `(1+ε)`-Lipschitz `F/R` for `R⁻¹ d`.

Main theorem: `exists_edge_full_collar_family`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Topology
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- A `K`-Lipschitz function divided by `R` is `K`-Lipschitz for the rescaled distance `R⁻¹ d`. -/
theorem radialScaled_div_lipschitzWith {X : Type*} [m : MetricSpace X] {F : X → ℝ} {K : ℝ≥0}
    (hF : LipschitzWith K F) {R : ℝ} (hR : 0 < R) :
    letI := m.rescale R⁻¹ (inv_pos.mpr hR)
    LipschitzWith K (fun x => F x / R) := by
  let := m.rescale R⁻¹ (inv_pos.mpr hR)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := @LipschitzWith.dist_le_mul X ℝ m.toPseudoMetricSpace _ K F hF x y
  change dist (F x / R) (F y / R) ≤ K * (R⁻¹ * @dist X m.toDist x y)
  rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hR]
  rw [Real.dist_eq] at h
  calc |F x - F y| / R ≤ (K * @dist X m.toDist x y) / R :=
      div_le_div_of_nonneg_right h hR.le
    _ = K * (R⁻¹ * @dist X m.toDist x y) := by field_simp

/-- A coarse-border chart at physical scale `ΔR` is, after division by `R`, a coarse-border chart at
scale `Δ` of the rescaled distance `R⁻¹ d`. -/
theorem radialScaled_chart_clauses {X : Type*} [m : MetricSpace X] {Q : X → WithLp 2 (ℝ × ℝ)}
    {p : X} {A : Set X} {Δ τ R : ℝ} (hR : 0 < R) (hQp : Q p = 0)
    (hdist : ∀ x ∈ ball p (200 * (Δ * R)), ∀ y ∈ ball p (200 * (Δ * R)),
      |dist (Q x) (Q y) - dist x y| ≤ τ * (Δ * R))
    (hheight : ∀ x ∈ ball p (200 * (Δ * R)), 0 ≤ (Q x).snd)
    (hcover : ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * (Δ * R) →
      z.snd ∈ Icc 0 (100 * (Δ * R)) →
        ∃ x ∈ ball p (200 * (Δ * R)), dist (Q x) z ≤ τ * (Δ * R))
    (hborder : ∀ a ∈ A ∩ ball p (190 * (Δ * R)), (Q a).snd ≤ τ * (Δ * R))
    (hbordercover : ∀ t : ℝ, |t| ≤ 100 * (Δ * R) →
      ∃ a ∈ A ∩ ball p (190 * (Δ * R)),
        dist (Q a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * (Δ * R)) :
    letI := m.rescale R⁻¹ (inv_pos.mpr hR)
    (fun x => R⁻¹ • Q x) p = 0 ∧
      (∀ y ∈ ball p (200 * Δ), ∀ z ∈ ball p (200 * Δ),
        |dist ((fun x => R⁻¹ • Q x) y) ((fun x => R⁻¹ • Q x) z) - dist y z| ≤ τ * Δ) ∧
      (∀ y ∈ ball p (200 * Δ), 0 ≤ ((fun x => R⁻¹ • Q x) y).snd) ∧
      (∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
        ∃ y ∈ ball p (200 * Δ), dist ((fun x => R⁻¹ • Q x) y) z ≤ τ * Δ) ∧
      (∀ a ∈ A ∩ ball p (190 * Δ), ((fun x => R⁻¹ • Q x) a).snd ≤ τ * Δ) ∧
      (∀ t : ℝ, |t| ≤ 100 * Δ → ∃ a ∈ A ∩ ball p (190 * Δ),
        dist ((fun x => R⁻¹ • Q x) a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ) := by
  have hRi : 0 < R⁻¹ := inv_pos.mpr hR
  have hball (r : ℝ) (x : X) :
      x ∈ @ball X (m.rescale R⁻¹ hRi).toPseudoMetricSpace p r ↔ x ∈ ball p (r * R) := by
    change R⁻¹ * dist x p < r ↔ dist x p < r * R
    rw [← div_eq_inv_mul, div_lt_iff₀ hR]
  have hsd (a b : WithLp 2 (ℝ × ℝ)) : dist (R⁻¹ • a) (R⁻¹ • b) = R⁻¹ * dist a b := by
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hRi]
  have hsnd (a : WithLp 2 (ℝ × ℝ)) : (R⁻¹ • a).snd = R⁻¹ * a.snd := rfl
  have hfst (a : WithLp 2 (ℝ × ℝ)) : (R⁻¹ • a).fst = R⁻¹ * a.fst := rfl
  have hin (r : ℝ) (x : X) (hx : x ∈ @ball X (m.rescale R⁻¹ hRi).toPseudoMetricSpace p (r * Δ)) :
      x ∈ ball p (r * (Δ * R)) := by
    have h := (hball _ x).mp hx
    rwa [mul_assoc] at h
  have hout (r : ℝ) (x : X) (hx : x ∈ ball p (r * (Δ * R))) :
      x ∈ @ball X (m.rescale R⁻¹ hRi).toPseudoMetricSpace p (r * Δ) := by
    rw [← mul_assoc] at hx
    exact (hball _ x).mpr hx
  let := m.rescale R⁻¹ hRi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change R⁻¹ • Q p = 0
    rw [hQp, smul_zero]
  · intro y hy z hz
    have h := hdist y (hin _ y hy) z (hin _ z hz)
    change |dist (R⁻¹ • Q y) (R⁻¹ • Q z) - R⁻¹ * @dist X m.toDist y z| ≤ τ * Δ
    rw [hsd, ← mul_sub, abs_mul, abs_of_pos hRi]
    calc R⁻¹ * |dist (Q y) (Q z) - @dist X m.toDist y z| ≤ R⁻¹ * (τ * (Δ * R)) :=
        mul_le_mul_of_nonneg_left h hRi.le
      _ = τ * Δ := by field_simp
  · intro y hy
    change 0 ≤ (R⁻¹ • Q y).snd
    rw [hsnd]
    exact mul_nonneg hRi.le (hheight y (hin _ y hy))
  · intro z hz1 hz2
    obtain ⟨y, hy, hyz⟩ := hcover (R • z) (by
        change |R * z.fst| ≤ 100 * (Δ * R)
        rw [abs_mul, abs_of_pos hR]
        nlinarith [abs_nonneg z.fst])
      (by
        change R * z.snd ∈ Icc 0 (100 * (Δ * R))
        exact ⟨mul_nonneg hR.le hz2.1, by nlinarith [hz2.2]⟩)
    refine ⟨y, hout _ y hy, ?_⟩
    change dist (R⁻¹ • Q y) z ≤ τ * Δ
    have hz : z = R⁻¹ • (R • z) := by rw [smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
    rw [hz, hsd]
    calc R⁻¹ * dist (Q y) (R • z) ≤ R⁻¹ * (τ * (Δ * R)) :=
        mul_le_mul_of_nonneg_left hyz hRi.le
      _ = τ * Δ := by field_simp
  · intro a ha
    change (R⁻¹ • Q a).snd ≤ τ * Δ
    rw [hsnd]
    have h := hborder a ⟨ha.1, hin _ a ha.2⟩
    calc R⁻¹ * (Q a).snd ≤ R⁻¹ * (τ * (Δ * R)) := mul_le_mul_of_nonneg_left h hRi.le
      _ = τ * Δ := by field_simp
  · intro t ht
    obtain ⟨a, ⟨haA, hab⟩, hat⟩ := hbordercover (R * t) (by
      rw [abs_mul, abs_of_pos hR]
      nlinarith [abs_nonneg t])
    refine ⟨a, ⟨haA, hout _ a hab⟩, ?_⟩
    change dist (R⁻¹ • Q a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ
    have hz : WithLp.toLp 2 (t, (0 : ℝ)) = R⁻¹ • WithLp.toLp 2 (R * t, (0 : ℝ)) := by
      change WithLp.toLp 2 (t, (0 : ℝ)) = WithLp.toLp 2 (R⁻¹ * (R * t), R⁻¹ * (0 : ℝ))
      rw [← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul, mul_zero]
    rw [hz, hsd]
    calc R⁻¹ * dist (Q a) (WithLp.toLp 2 (R * t, (0 : ℝ))) ≤ R⁻¹ * (τ * (Δ * R)) :=
        mul_le_mul_of_nonneg_left hat hRi.le
      _ = τ * Δ := by field_simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [hM : CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- The nearest-direction gradient clause transported to the normalization at scale `R`. -/
theorem radialScaled_low_collar_gradient (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {R : ℝ} (hR : 0 < R) {F : M → ℝ} {A : Set M}
    {y : M} {ε : ℝ} (hF : MDifferentiableAt I 𝓘(ℝ, ℝ) F y)
    (hgrad : ∀ v ∈ minimizingDirectionsTo g hEnorm A y,
      Real.sqrt (g.inner y (gradFun g F y + v) (gradFun g F y + v)) < ε) :
    (have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
    letI := m.rescale R⁻¹ (inv_pos.mpr hR)
    letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
    letI : IsRiemannianManifold I M :=
      radialScaledManifold (m := m) g hmetric R⁻¹ (inv_pos.mpr hR)
    letI : CompleteSpace M := (m.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hM
    let gR : SmoothRiemannianMetric I M := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
    have hnR : IsMetricNorm (I := I) (M := M) gR := isMetricNorm_of_riemannianBundle gR
    ∀ v ∈ minimizingDirectionsTo gR hnR A y,
      Real.sqrt (gR.inner y (gradFun gR (fun z => F z / R) y + v)
        (gradFun gR (fun z => F z / R) y + v)) < ε) := by
  intro hmetric gR hnR v hv
  have hRi : 0 < R⁻¹ := inv_pos.mpr hR
  have hgeo := intrinsicGeodesic_radialScaled_eq g hEnorm hR y v
  have hinner : g.inner y (R⁻¹ • v) (R⁻¹ • v) = gR.inner y v v := by
    change _ = (scaleMetric (R⁻¹ ^ 2) (pow_pos hRi 2) g).inner y v v
    rw [scaleMetric_inner, map_smul, map_smul, smul_apply, smul_eq_mul, smul_eq_mul]
    ring
  have hinf : @infDist M (m.rescale R⁻¹ hRi).toPseudoMetricSpace y A = R⁻¹ * infDist y A :=
    infDist_rescale m R⁻¹ hRi y A
  have hv' : R⁻¹ • v ∈ minimizingDirectionsTo g hEnorm A y := by
    obtain ⟨hv1, hvA⟩ := hv
    refine ⟨by rw [hinner]; exact hv1, ?_⟩
    have hsmul := intrinsicGeo_smul_apply (I := I) g hEnorm y v R⁻¹ (infDist y A)
    rw [hsmul]
    convert hvA using 1
    refine Eq.trans ?_ (congrFun hgeo _).symm
    rw [hinf]
  have he : (fun z => F z / R) = R⁻¹ • F := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  have hgr := gradientFun_const_smul g R⁻¹ hF
  rw [← he] at hgr
  change gradFun g (fun z => F z / R) y = R⁻¹ • gradFun g F y at hgr
  have hgR : gradFun gR (fun z => F z / R) y = R • gradFun g F y := by
    change gradientFun (scaleMetric (R⁻¹ ^ 2) (pow_pos hRi 2) g) (fun z => F z / R) y = _
    rw [gradientFun_scale]
    change (R⁻¹ ^ 2)⁻¹ • gradFun g (fun z => F z / R) y = _
    rw [hgr, smul_smul]
    congr 1
    field_simp
  have hsplit : gradFun gR (fun z => F z / R) y + v = R • (gradFun g F y + R⁻¹ • v) := by
    rw [hgR, smul_add, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  have hval : gR.inner y (R • (gradFun g F y + R⁻¹ • v)) (R • (gradFun g F y + R⁻¹ • v)) =
      g.inner y (gradFun g F y + R⁻¹ • v) (gradFun g F y + R⁻¹ • v) := by
    change (scaleMetric (R⁻¹ ^ 2) (pow_pos hRi 2) g).inner y _ _ = _
    rw [scaleMetric_inner, map_smul, map_smul, smul_apply, smul_eq_mul, smul_eq_mul]
    field_simp
  rw [hsplit, hval]
  exact hgrad _ hv'

/-- The value clause transported to the normalization at scale `R`. -/
theorem radialScaled_value_clause {X : Type*} [m : MetricSpace X] {F : X → ℝ} {A : Set X}
    {μ Δ R : ℝ} (hR : 0 < R) (hval : ∀ x, |F x - infDist x A| < μ * (Δ * R)) :
    letI := m.rescale R⁻¹ (inv_pos.mpr hR)
    ∀ x, |F x / R - infDist x A| ≤ μ * Δ := by
  intro x
  rw [infDist_rescale, div_eq_inv_mul, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hR)]
  have h := hval x
  rw [← div_eq_inv_mul, div_le_iff₀ hR]
  linarith

/-- The smoothing collar `C⁺` at physical scale `ΔR` is the collar `C⁺` at scale `Δ` of the
normalized distance. -/
theorem radialScaled_collar_subset {X : Type*} [m : MetricSpace X] {A O : Set X} {p : X}
    {Δ R : ℝ} (hR : 0 < R)
    (hCO : closedBall p (20 * (Δ * R)) ∩ {x | Δ * R / 25 ≤ infDist x A ∧
      infDist x A ≤ 21 / 2 * (Δ * R)} ⊆ O) :
    letI := m.rescale R⁻¹ (inv_pos.mpr hR)
    closedBall p (20 * Δ) ∩ {y | Δ / 25 ≤ infDist y A ∧ infDist y A ≤ 21 / 2 * Δ} ⊆ O := by
  intro y hy
  obtain ⟨hy1, hy2, hy3⟩ := hy
  have hRi : 0 < R⁻¹ := inv_pos.mpr hR
  have hd : R⁻¹ * dist y p ≤ 20 * Δ := hy1
  rw [infDist_rescale] at hy2 hy3
  apply hCO
  refine ⟨?_, ?_, ?_⟩
  · change dist y p ≤ 20 * (Δ * R)
    rw [← div_eq_inv_mul, div_le_iff₀ hR] at hd
    linarith
  · rw [← div_eq_inv_mul, le_div_iff₀ hR] at hy2
    linarith
  · rw [← div_eq_inv_mul, div_le_iff₀ hR] at hy3
    linarith

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] hM
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
/-- The normalized lower curvature bound at scale `R`. -/
theorem radialScaled_sectional_bound (g : SmoothRiemannianMetric I M) {p : M} {R κ r : ℝ}
    (hR : 0 < R)
    (hsec : ∀ z ∈ ball p (r * R), SectionalBoundedBelowAt g z (-(κ / R) ^ 2)) :
    letI := m.rescale R⁻¹ (inv_pos.mpr hR)
    ∀ z ∈ ball p r,
      SectionalBoundedBelowAt (scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g) z
        (-κ ^ 2) := by
  intro z hz
  have hRi : 0 < R⁻¹ := inv_pos.mpr hR
  have hz' : R⁻¹ * dist z p < r := hz
  rw [sectionalBoundedBelowAt_scaleMetric_iff]
  have he : -κ ^ 2 * R⁻¹ ^ 2 = -(κ / R) ^ 2 := by ring
  rw [he]
  apply hsec z
  change dist z p < r * R
  rw [← div_eq_inv_mul, div_lt_iff₀ hR] at hz'
  exact hz'

end DifferentialGeometry.Geometry.Collapse

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe uE uH uM uY

/-- **LFR38, finite family.** With the ordered parameters of `exists_edge_full_collar_parameters`
(the strong tolerance `b₀` is fixed BEFORE the family), a finite family `P` of centres with
coarse-border charts for the SAME closed set at their physical scales `Δρ(p)` and the normalized
curvature bound gets ONE smoothing `F`: `0 ≤ F`, `(1+ε)`-Lipschitz, `μΔρ(p)`-close to `d_A`; and at
every centre, in its normalization `(ρ(p)⁻¹ d, ρ(p)⁻² g)`, for every actual `(1, b)`-splitting `α`
whose first coordinate is the chart's and every LFR19-type `f` for `α`, the original pair
`(f, (F/ρ(p))/(ρ/ρ(p))) = (f, F/ρ)` has the full adapted collar of quality `γ` on the whole band. -/
theorem exists_edge_full_collar_family {β γ : ℝ} (hβ : 0 < β) (hβγ : β < γ / 1000)
    (hγ : 0 < γ) (hγ1 : γ < 1 / 100) :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ ∀ Δ : ℝ, Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ (σ ε μ τ κ b : ℝ) (Λ : ℝ≥0), 0 ≤ σ → σ ≤ σ₀ → 0 < ε → ε < 1 / 100 →
        0 < μ → μ ≤ 1 / 1000000 → 0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 →
        0 ≤ κ → κ ≤ κ₀ → 0 < b → b < b₀ → 100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γ / 1000 →
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type uM) [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [hM : CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
        (A : Set M) (P : Finset M) (Q : M → M → WithLp 2 (ℝ × ℝ)) (ρ : M → ℝ)
        (hρpos : ∀ x, 0 < ρ x),
      P.Nonempty → IsClosed A → (∀ p ∈ P, Q p p = 0) →
      (∀ p ∈ P, ∀ x ∈ ball p (200 * (Δ * ρ p)), ∀ y ∈ ball p (200 * (Δ * ρ p)),
        |dist (Q p x) (Q p y) - dist x y| ≤ τ * (Δ * ρ p)) →
      (∀ p ∈ P, ∀ x ∈ ball p (200 * (Δ * ρ p)), 0 ≤ (Q p x).snd) →
      (∀ p ∈ P, ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * (Δ * ρ p) →
        z.snd ∈ Icc 0 (100 * (Δ * ρ p)) →
          ∃ x ∈ ball p (200 * (Δ * ρ p)), dist (Q p x) z ≤ τ * (Δ * ρ p)) →
      (∀ p ∈ P, p ∈ A) →
      (∀ p ∈ P, ∀ a ∈ A ∩ ball p (190 * (Δ * ρ p)), (Q p a).snd ≤ τ * (Δ * ρ p)) →
      (∀ p ∈ P, ∀ t : ℝ, |t| ≤ 100 * (Δ * ρ p) →
        ∃ a ∈ A ∩ ball p (190 * (Δ * ρ p)),
          dist (Q p a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * (Δ * ρ p)) →
      (∀ p ∈ P, ∀ z ∈ ball p (10000 * (Δ * ρ p)),
        SectionalBoundedBelowAt g z (-(κ / ρ p) ^ 2)) →
      LipschitzWith Λ ρ → ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ →
      ∃ F : M → ℝ, (∀ x, 0 ≤ F x) ∧ LipschitzWith (Real.toNNReal (1 + ε)) F ∧
        ∀ p ∈ P, (∀ x, |F x - infDist x A| < μ * (Δ * ρ p)) ∧
        (have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
        letI := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        letI := radialScaledBundle g (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
          radialScaledContinuous g (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        letI : IsRiemannianManifold I M :=
          radialScaledManifold (m := m) g hmetric (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        letI : CompleteSpace M :=
          (m.rescale_completeSpace_iff (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).mpr hM
        let gR : SmoothRiemannianMetric I M :=
          scaleMetric ((ρ p)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρpos p)) 2) g
        have hnR : IsMetricNorm (I := I) (M := M) gR := isMetricNorm_of_riemannianBundle gR
        ∀ (Y : Type uY) [MetricSpace Y] (y₀ : Y)
          (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) b),
        (∀ z ∈ ball p b⁻¹, SectionalBoundedBelowAt gR z (-b ^ 2)) →
        (∀ z ∈ ball p (200 * Δ), (Q p z).fst = ρ p * (α.toFun z).fst) →
        ∀ f : M → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f (ball p (100 * Δ)) →
        LipschitzWith (Real.toNNReal (1 + σ)) f →
        (∀ x ∈ ball p (100 * Δ), |f x - (α.toFun x).fst| ≤ μ * Δ) →
        (∀ x ∈ ball p (100 * Δ), ∀ x' ∈ ball p (1000 * Δ), 100 * Δ < dist x x' →
          ∀ w : TangentSpace I x, gR.inner x w w = 1 →
          intrinsicGeodesic gR hnR x w (dist x x') = x' →
          |mvfderiv (I := I) f x w - ((α.toFun x').fst - (α.toFun x).fst) / dist x x'| < σ) →
        ∀ x ∈ ball p (100 * Δ), |f x| ≤ 10 * Δ →
          Δ / 10 ≤ F x / ρ p / (ρ x / ρ p) → F x / ρ p / (ρ x / ρ p) ≤ 10 * Δ →
        ∃ hq : 99 / 100 ≤ ρ x / ρ p ∧ ρ x / ρ p ≤ 101 / 100,
          (letI := (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).rescale (ρ x / ρ p)⁻¹
            (inv_pos.mpr (lt_of_lt_of_le (by norm_num) hq.1));
            ∃ Φ : KleinerLottApprox x (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) β,
              ∀ y, Φ.toFun y = @planeComparisonMap M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p)))
                (fun z => (ρ p)⁻¹ • Q p z) p x Δ (ρ x / ρ p) y) ∧
          let J := edgeReferenceCoordinates ![f, fun z => F z / ρ p / (ρ z / ρ p)]
          ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ J (ball x (300 * (ρ x / ρ p))) ∧
          (∀ y ∈ ball x (100 * (ρ x / ρ p)), Function.Surjective (mvfderiv (I := I) J y)) ∧
          (∀ y ∈ ball x (100 * (ρ x / ρ p)), ∀ z ∈ ball x (100 * (ρ x / ρ p)),
            ‖J y - J z‖ ≤ (1 + γ) * (dist y z / (ρ x / ρ p))) ∧
          (∀ y ∈ ball x (100 * (ρ x / ρ p)), infDist (J y) (ball (J x) 100) < 100 * γ) ∧
          (∀ v ∈ ball (J x) 100, ∃ y ∈ ball x (100 * (ρ x / ρ p)), ‖J y - v‖ < 100 * γ) ∧
          ∀ y ∈ ball x (100 * (ρ x / ρ p)), ∀ z ∈ ball x (100 * (ρ x / ρ p) / γ),
            ρ x / ρ p < dist y z →
            ∀ W : TangentSpace I y, gR.inner y W W = 1 →
            intrinsicGeodesic gR hnR y W (dist y z) = z →
            ‖(ρ x / ρ p) • mvfderiv (I := I) J y W - (dist y z / (ρ x / ρ p))⁻¹ •
              (planeReferenceIsometry (planeComparisonMap (fun z => (ρ p)⁻¹ • Q p z) p x Δ
                (ρ x / ρ p) z) -
                planeReferenceIsometry (planeComparisonMap (fun z => (ρ p)⁻¹ • Q p z) p x Δ
                  (ρ x / ρ p) y))‖ < γ) := by
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hcollar⟩ :=
    exists_edge_full_collar_parameters.{uE, uH, uM, uY} hβ hβγ hγ hγ1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun Δ hΔ => ?_⟩
  have hΔpos : 0 < Δ := hΔ₀.trans_le hΔ
  obtain ⟨τ₀, hτ₀, κ₀, hκ₀, b₀, hb₀, hΔcollar⟩ := hcollar Δ hΔ
  refine ⟨min τ₀ (1 / 20000), lt_min hτ₀ (by norm_num), min κ₀ (1 / (100 * Δ)),
    lt_min hκ₀ (by positivity), b₀, hb₀, ?_⟩
  intro σ ε μ τ κ b Λ hσ hσσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ hκ hκκ₀ hb hbb₀ hlam hbudget
    E _ _ _ _ H _ I _ M m _ _ _ hM _ _ _ g hEnorm A P Q ρ hρpos hP hA hQp hdist hheight hcover
    hpA hborder hbordercover hsec hρ hρs
  have hκΔ : κ * Δ ≤ 1 / 100 := by
    have h : κ ≤ 1 / (100 * Δ) := hκκ₀.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hτsmall : τ < 1 / 10000 :=
    (hττ₀.trans (min_le_right _ _)).trans_lt (by norm_num)
  obtain ⟨F, O, hO, hFO, hF0, hFL, -, hcent⟩ :=
    exists_shared_low_collar_smoothing g hEnorm hA hP hρpos hΔpos hτ hτsmall hQp hdist hheight
      hcover hpA hborder hbordercover hκ hκΔ
      (fun p hp z hz => hsec p hp z (ball_subset_ball (by nlinarith [hρpos p]) hz))
      hε hε1 hμ (by linarith) hθ hρ hρs (by linarith)
  refine ⟨F, hF0, hFL, fun p hp => ⟨(hcent p hp).1, ?_⟩⟩
  obtain ⟨-, hCO, hgrad, -⟩ := hcent p hp
  have hr : 0 < ρ p := hρpos p
  have hchart := radialScaled_chart_clauses (A := A) hr (hQp p hp) (hdist p hp) (hheight p hp)
    (hcover p hp) (hborder p hp) (hbordercover p hp)
  have hsecR := radialScaled_sectional_bound g (r := 10000 * Δ) hr
    (fun z hz => hsec p hp z (by rwa [mul_assoc] at hz))
  have hvalR := radialScaled_value_clause (A := A) hr (hcent p hp).1
  have hCOR := radialScaled_collar_subset hr hCO
  have hFLR := radialScaled_div_lipschitzWith hFL hr
  have hρR := lipschitzWith_normalized_scale hρ hr
  have hgradR (y : M) (hy : y ∈ closedBall p (20 * (Δ * ρ p)) ∩ {x | Δ * ρ p / 25 ≤
      infDist x A ∧ infDist x A ≤ 21 / 2 * (Δ * ρ p)}) :=
    radialScaled_low_collar_gradient g hEnorm hr
      ((hFO.contMDiffAt (hO.mem_nhds (hCO hy))).mdifferentiableAt (by simp)) (hgrad y hy)
  have hCC := radialScaled_collar_subset (A := A) (p := p) (Δ := Δ)
    (O := closedBall p (20 * (Δ * ρ p)) ∩ {x | Δ * ρ p / 25 ≤ infDist x A ∧
      infDist x A ≤ 21 / 2 * (Δ * ρ p)}) hr subset_rfl
  intro hmetric gR hnR Y _ y₀ α hsecb hQα f hfs hfL hfval htest x hx hfx hη hη'
  let mR : MetricSpace M := m.rescale (ρ p)⁻¹ (inv_pos.mpr hr)
  let _ : CompleteSpace M := (m.rescale_completeSpace_iff (ρ p)⁻¹ (inv_pos.mpr hr)).mpr hM
  let _ := radialScaledBundle g (ρ p)⁻¹ (inv_pos.mpr hr)
  let _ := radialScaledContinuous g (ρ p)⁻¹ (inv_pos.mpr hr)
  let _ := radialScaledManifold (m := m) g hmetric (ρ p)⁻¹ (inv_pos.mpr hr)
  obtain ⟨hQp', hdist', hheight', hcover', hborder', hbordercover'⟩ := hchart
  have hQα' : ∀ z ∈ ball p (200 * Δ), ((fun z => (ρ p)⁻¹ • Q p z) z).fst = (α.toFun z).fst := by
    intro z hz
    change (ρ p)⁻¹ * (Q p z).fst = _
    rw [hQα z hz, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  have hfval' : ∀ x ∈ ball p (100 * Δ), |f x - ((fun z => (ρ p)⁻¹ • Q p z) x).fst| ≤ μ * Δ := by
    intro z hz
    rw [hQα' z (ball_subset_ball (by linarith) hz)]
    exact hfval z hz
  exact hΔcollar σ ε μ τ κ b Λ hσ hσσ₀ hε.le hε1 hμ1 (hττ₀.trans (min_le_left _ _)) hκ
    (hκκ₀.trans (min_le_left _ _)) hb hbb₀ hlam hbudget E H I M gR hnR Y p y₀ α
    (fun z => (ρ p)⁻¹ • Q p z) A (fun z => ρ z / ρ p) (fun z => F z / ρ p) f O hsecR hsecb hA
    hQp' hdist' hheight' hcover' (hpA p hp) hborder' hbordercover' hQα' hρR
    (div_self hr.ne') (hρs.div_const _) hO hCOR (hFO.div_const _) hFLR hvalR (fun y hy => hgradR y (hCC hy)) hfs hfL
    hfval' htest x hx hfx hη hη'

end DifferentialGeometry.Geometry.Collapse
