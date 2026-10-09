import DifferentialGeometry.Geometry.Metric.ActualCloudPrunedPlanes
import DifferentialGeometry.Geometry.Metric.RetainedMarkerLocality
import DifferentialGeometry.Geometry.Metric.LargeCloudAffineMarkerLocality

/-! CFS28 (master207B, B:3686): with the plane rule (PP) of CFS27 and `Σ ≤ 1/(640 b)`, EVERY selected centre `u` whose
closed `80 b r(u)` ball meets the core ball `B(x, 8 b r(x))` has `J_i u = 0` and `L_u ⊆ ker J_i` for every retained
block with `R_i < ρ(p)/16` — whatever preimages were chosen for the radius at `u`, the model at `u`, and the core.

Binding to CFS24 on the literal large-cloud construction: these are exactly the contributor hypotheses of
`large_cloud_affine_marker_locality` (weights `w`, spectral projector `Q`, section `η`) with `K = V i`, `c = 0`, so
every zero of `η` near the affine approximant of the core has zero `i` block. -/

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis
open scoped BigOperators

namespace GC.MetricGeometry

/-- CFS28 (AL): every contributing centre and its pruned (PP) plane are orthogonal to each small block. -/
theorem actualCloud_contributor_marker_locality
    {M H E A : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F' : M → H) (ρ : M → ℝ) (V : A → Submodule ℝ H) (marker : A → H → ℝ) (R : A → ℝ)
    (hR : ∀ i, 0 < R i) (hmarker : ∀ i, LipschitzWith 1 (marker i))
    (hfull : ∀ q, ∃ i, marker i (F' q) = R i)
    (hnonneg : ∀ i q, 0 ≤ marker i (F' q))
    (hsupport : ∀ i q, 0 < marker i (F' q) → 3 * R i / 4 ≤ ρ q ∧ ρ q ≤ 5 * R i / 4)
    (hblock : ∀ i q, marker i (F' q) = 0 → (V i).starProjection (F' q) = 0)
    {b σ : ℝ} (hb : 1 ≤ b) (hσ : 0 ≤ σ) (hσb : 640 * b * σ ≤ 1)
    (select model : H → M) (ref : H → A) (Tm : H → E →L[ℝ] H)
    (p : M) (x : H) (hx : F' p = x) (hselx : F' (select x) = x)
    (u : H) (hselu : F' (select u) = u) (hmodel : F' (model u) = u)
    (hfullu : marker (ref u) u = R (ref u))
    (hmeet : (closedBall u (80 * b * (σ * ρ (select u))) ∩
      ball x (8 * b * (σ * ρ (select x)))).Nonempty)
    (i : A) (hi : R i < ρ p / 16) :
    (V i).starProjection u = 0 ∧
      LinearMap.range (((actualCloudPrunedProjection V R (ref u)).comp (Tm u) : E →L[ℝ] H) :
        E →ₗ[ℝ] H) ≤ (V i)ᗮ := by
  have hb0 : 0 ≤ b := by linarith
  have hsmall : (128 * b) * σ ≤ 1 / 5 := by nlinarith
  have hlt : R i < R (ref u) / 2 :=
    small_radius_lt_half_reference_of_contributing_support F' ρ marker R hR hmarker hfull
      hsupport hb0 hσ hsmall p (select x) (select u) (model u) (hselx.trans hx.symm)
      (hselu.trans hmodel.symm) (by rw [hselu, hselx]; exact hmeet) (ref u) i
      (by rw [hmodel]; exact hfullu) hi
  have hRa := hsupport (ref u) (model u) (by rw [hmodel, hfullu]; exact hR _)
  have hzero : marker i (F' (model u)) = 0 := by
    apply le_antisymm ?_ (hnonneg i (model u))
    by_contra hpos
    have hs := hsupport i (model u) (lt_of_not_ge hpos)
    linarith [hs.2, hRa.1, hR (ref u)]
  refine ⟨by rw [← hmodel]; exact hblock i (model u) hzero, ?_⟩
  rintro w ⟨t, rfl⟩
  exact actualCloudPrunedProjection_apply_mem_orthogonal V R (ref u) i hlt.le (Tm u t)

/-- CFS28 → CFS24 on the literal large-cloud section: with radii `σ ρ(select ·)` and the pruned (PP) planes, every
zero of `η` near the affine approximant of the core point `x = F' p` has zero block `i` whenever `R_i < ρ(p)/16`. -/
theorem actualCloud_zero_set_small_marker_locality
    {M H E A : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F' : M → H) (ρ : M → ℝ) (V : A → Submodule ℝ H) (marker : A → H → ℝ) (R : A → ℝ)
    (hR : ∀ i, 0 < R i) (hmarker : ∀ i, LipschitzWith 1 (marker i))
    (hfull : ∀ q, ∃ i, marker i (F' q) = R i)
    (hnonneg : ∀ i q, 0 ≤ marker i (F' q))
    (hsupport : ∀ i q, 0 < marker i (F' q) → 3 * R i / 4 ≤ ρ q ∧ ρ q ≤ 5 * R i / 4)
    (hblock : ∀ i q, marker i (F' q) = 0 → (V i).starProjection (F' q) = 0)
    {ε σ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hσ : 0 < σ) (hσε : σ ≤ ε / 640)
    (I : Set H) (hI : I.Finite) (select model : H → M) (ref : H → A) (Tm : H → E →L[ℝ] H)
    (hselI : ∀ u ∈ I, F' (select u) = u) (hmodel : ∀ u ∈ I, F' (model u) = u)
    (hfullI : ∀ u ∈ I, marker (ref u) u = R (ref u))
    (p : M) (x : H) (hx : F' p = x) (hselx : F' (select x) = x)
    (htube : ball x (8 * ε⁻¹ * (σ * ρ (select x))) ⊆
      ⋃ u ∈ I, ball u (20 * ε⁻¹ * (σ * ρ (select u)))) :
    let r : H → ℝ := fun u => σ * ρ (select u)
    let P : H → Submodule ℝ H := fun u =>
      LinearMap.range (((actualCloudPrunedProjection V R (ref u)).comp (Tm u) : E →L[ℝ] H) :
        E →ₗ[ℝ] H)
    let w : H → H → ℝ := fun c y => ballCutoff c (40 * ε⁻¹ * r c) (2 * (40 * ε⁻¹ * r c)) y /
        (∑ a ∈ hI.toFinset, ballCutoff a (40 * ε⁻¹ * r a) (2 * (40 * ε⁻¹ * r a)) y)
    let Q : H → Submodule ℝ H := fun y => ⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
        (∑ c ∈ hI.toFinset, w c y • (P c)ᗮ.starProjection).toLinearMap μ
    let η : H → H := fun y => (Q y).starProjection (y - ∑ c ∈ hI.toFinset, w c y • c)
    ∀ z ∈ ball x (r x), ∀ y : H, η y = 0 →
      ‖y - (x + (P x).starProjection (z - x))‖ ≤ ε * r x →
      ∀ i, R i < ρ p / 16 → (V i).starProjection y = 0 := by
  intro r P w Q η z hz y hy hyval i hi
  have hr : ∀ c ∈ I, 0 < r c := by
    intro c _
    obtain ⟨j, hj⟩ := hfull (select c)
    have hs := hsupport j (select c) (by rw [hj]; exact hR j)
    exact mul_pos hσ (by linarith [hR j, hs.1])
  have hb : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).mpr hε1
  have hσb : 640 * ε⁻¹ * σ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hσε (by positivity : (0 : ℝ) ≤ 640 * ε⁻¹)
    have heq : 640 * ε⁻¹ * (ε / 640) = 1 := by field_simp
    linarith
  have hcontrib : ∀ c ∈ I, (closedBall c (80 * ε⁻¹ * r c) ∩ ball x (8 * ε⁻¹ * r x)).Nonempty →
      (V i).starProjection c = 0 ∧ P c ≤ (V i)ᗮ := fun c hc hmeet =>
    actualCloud_contributor_marker_locality F' ρ V marker R hR hmarker hfull hnonneg hsupport
      hblock hb hσ.le hσb select model ref Tm p x hx hselx c (hselI c hc) (hmodel c hc)
      (hfullI c hc) hmeet i hi
  have hloc := large_cloud_affine_marker_locality I hI r P hε hε1 hr x htube (V i) 0 hcontrib
  exact hloc.2.2 z hz y hy hyval

end GC.MetricGeometry
