import DifferentialGeometry.Geometry.Fibration.ActualSlimRank

/-!
# TCP06: the two-dimensional projected rank (FC06 for a plane, semidefinite source form)

Blueprint `master207B.tex`, TCP06 (`thm:fibration-actual-first-cloud`, B:5600–5640), proof, second
paragraph: "TCP01's Gram bound gives least singular value greater than `9/10` and operator norm
less than two for `R_iDη_i` in the physical metric. The identity component of `T_x` gives its least
singular value at least one and upper norm `C`. Apply FC06 to (TG), canceling `R_i` between source
and target ... the projection is actually onto the two-plane. Its upper norm is less than `3C` and
normal error less than `e`."

The two-dimensional analogue of SGP05's rank form (`sgp05_rank_form_SGP5`), with the source
measured by a positive semidefinite form `B` (`ν(v) = √(B v v)`) instead of an inner-product norm.

* `abs_form_le_of_unit_KA8`: `|B v w| ≤ ν(v)` for a `B`-unit `w` (Cauchy–Schwarz).
* `exists_coeff_of_near_basis_KA8`: a `δ`-perturbed standard basis of `ℝ²` (`δ ≤ 1/5`) spans `ℝ²`
  with coefficient sum `|a| + |b| ≤ 2‖z‖`.
* `tcp06_rank_form_KA8`: for `T : ℝ² → H` with `|z| ≤ ‖Tz‖`, `‖T‖ ≤ C`, a covector field
  `dη : V → ℝ²` whose image of `B`-unit vectors comes within `d` of every unit vector (TCP01's Gram
  clause in its norm form), `‖dη‖ ≤ 2ν`, and `‖D v − T(dη v)‖ ≤ eν(v)` with `d + e ≤ 1/5`,
  `e ≤ C`: the projection `P` of `D` onto `im T` is onto, the normal error is at most `eν`,
  `‖P v‖ ≥ ν(v)/2` on the `B`-orthogonal complement of `ker P`, and `‖P v‖ ≤ 3Cν(v)`.
* `tcp06_rank_metric_KA8`: the same for `B = c²g_q`, with `df_q` and `c·dF_q`, in metric form.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section PlaneKernel

/-- Cauchy–Schwarz against a unit vector of a positive semidefinite symmetric form:
`|B v w| ≤ √(B v v)` when `B w w = 1`. -/
theorem abs_form_le_of_unit_KA8 {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hBs : ∀ v w, B v w = B w v) (hBp : ∀ v, 0 ≤ B v v) {w : V}
    (hw : B w w = 1) (v : V) : |B v w| ≤ Real.sqrt (B v v) := by
  have h := hBp (v - B v w • w)
  have hexp : B (v - B v w • w) (v - B v w • w) = B v v - (B v w) ^ 2 := by
    simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul]
    rw [hBs w v, hw]
    ring
  rw [hexp] at h
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by linarith)

/-- A `δ`-perturbed standard basis of `ℝ²` with `δ ≤ 1/5` spans `ℝ²`, and every `z` is
`a z₁ + b z₂` with `|a| + |b| ≤ 2‖z‖` (from `‖(a, b)‖ ≥ (7/10)(|a| + |b|)`). -/
theorem exists_coeff_of_near_basis_KA8 {z₁ z₂ : ℝ²} {δ : ℝ} (hδ : δ ≤ 1 / 5)
    (h₁ : ‖z₁ - EuclideanSpace.single 0 1‖ ≤ δ) (h₂ : ‖z₂ - EuclideanSpace.single 1 1‖ ≤ δ)
    (z : ℝ²) : ∃ a b : ℝ, a • z₁ + b • z₂ = z ∧ |a| + |b| ≤ 2 * ‖z‖ := by
  have hlow : ∀ a b : ℝ, |a| + |b| ≤ 2 * ‖a • z₁ + b • z₂‖ := by
    intro a b
    have hab : ‖a • (EuclideanSpace.single 0 1 : ℝ²) + b • EuclideanSpace.single 1 1‖ =
        Real.sqrt (a ^ 2 + b ^ 2) := by
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
      simp
    have hsq : 7 / 10 * (|a| + |b|) ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [sq_abs a, sq_abs b, sq_nonneg (|a| - |b|), abs_nonneg a, abs_nonneg b]
    have herr : ‖a • (z₁ - EuclideanSpace.single 0 1) + b • (z₂ - EuclideanSpace.single 1 1)‖ ≤
        δ * (|a| + |b|) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      nlinarith [abs_nonneg a, abs_nonneg b, norm_nonneg (z₁ - EuclideanSpace.single 0 1),
        norm_nonneg (z₂ - EuclideanSpace.single 1 1)]
    have hsplit : a • z₁ + b • z₂ =
        (a • (EuclideanSpace.single 0 1 : ℝ²) + b • EuclideanSpace.single 1 1) +
          (a • (z₁ - EuclideanSpace.single 0 1) + b • (z₂ - EuclideanSpace.single 1 1)) := by
      simp only [smul_sub]
      abel
    have htri := norm_sub_norm_le
      (a • (EuclideanSpace.single 0 1 : ℝ²) + b • EuclideanSpace.single 1 1)
      (-(a • (z₁ - EuclideanSpace.single 0 1) + b • (z₂ - EuclideanSpace.single 1 1)))
    rw [sub_neg_eq_add, ← hsplit, norm_neg, hab] at htri
    have hs0 : 0 ≤ |a| + |b| := by positivity
    nlinarith
  let Lm : ℝ² →ₗ[ℝ] ℝ² :=
    { toFun := fun c => c 0 • z₁ + c 1 • z₂
      map_add' := fun c d => by
        simp only [PiLp.add_apply, add_smul]
        abel
      map_smul' := fun r c => by
        simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, smul_add] }
  have hLm : ∀ c, Lm c = c 0 • z₁ + c 1 • z₂ := fun c => rfl
  have hinj : Function.Injective Lm := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have h := hlow (c 0) (c 1)
    rw [← hLm, hc, norm_zero, mul_zero] at h
    have h0 : c 0 = 0 := abs_eq_zero.mp (le_antisymm (by linarith [abs_nonneg (c 1)])
      (abs_nonneg _))
    have h1 : c 1 = 0 := abs_eq_zero.mp (le_antisymm (by linarith [abs_nonneg (c 0)])
      (abs_nonneg _))
    ext i
    fin_cases i
    · simpa using h0
    · simpa using h1
  obtain ⟨c, hc⟩ := (LinearMap.injective_iff_surjective.mp hinj) z
  refine ⟨c 0, c 1, by rw [← hLm, hc], ?_⟩
  have h := hlow (c 0) (c 1)
  rwa [← hLm, hc] at h

/-- **TCP06's rank argument for a positive semidefinite form on the source** (FC06 for a plane).
A reference derivative `T : ℝ² → H` with identity component (`|z| ≤ ‖Tz‖`) and `‖T‖ ≤ C`, a covector
field `dη : V → ℝ²` such that every unit `ξ` is within `d` of `dη(w)` for a `B`-unit `w`, with
`|dη| ≤ 2ν`, and `D` with `‖D v − T(dη v)‖ ≤ eν(v)` (`d + e ≤ 1/5`, `e ≤ C`): the projection `P`
of `D` onto `im T` is onto, the normal error is at most `eν`, `‖P v‖ ≥ ν(v)/2` for `v`
`B`-orthogonal to `ker P`, and `‖P v‖ ≤ 3Cν(v)`. -/
theorem tcp06_rank_form_KA8 {V H : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hBs : ∀ v w, B v w = B w v) (hBp : ∀ v, 0 ≤ B v v)
    (T : ℝ² →L[ℝ] H) (hT : ∀ z, ‖z‖ ≤ ‖T z‖) {C d e : ℝ} (hTC : ‖T‖ ≤ C)
    (dη : V →L[ℝ] ℝ²) (hlow : ∀ ξ : ℝ², ‖ξ‖ = 1 → ∃ w, B w w = 1 ∧ ‖dη w - ξ‖ ≤ d)
    (hup : ∀ v, ‖dη v‖ ≤ 2 * Real.sqrt (B v v)) (D : V →L[ℝ] H)
    (hD : ∀ v, ‖D v - T (dη v)‖ ≤ e * Real.sqrt (B v v)) (hde : d + e ≤ 1 / 5) (heC : e ≤ C) :
    let P := T.range.orthogonalProjectionOnto.comp D
    Function.Surjective P ∧ (∀ v, ‖D v - (P v : H)‖ ≤ e * Real.sqrt (B v v)) ∧
      (∀ v, (∀ k, P k = 0 → B v k = 0) → 1 / 2 * Real.sqrt (B v v) ≤ ‖P v‖) ∧
      ∀ v, ‖P v‖ ≤ 3 * C * Real.sqrt (B v v) := by
  intro P
  have hPv : ∀ v, (P v : H) = T.range.starProjection (D v) := fun v => rfl
  have hprojT : ∀ z, T.range.starProjection (T z) = T z := fun z =>
    T.range.starProjection_mem_subspace_eq_self ⟨T z, ⟨z, rfl⟩⟩
  -- `P v` is within `eν` of `T(dη v)`
  have hPerr : ∀ v, ‖(P v : H) - T (dη v)‖ ≤ e * Real.sqrt (B v v) := by
    intro v
    rw [hPv, ← hprojT (dη v), ← map_sub]
    exact (T.range.norm_starProjection_apply_le _).trans (hD v)
  -- coordinates of the values of `P`
  have hS : ∀ v, ∃ z : ℝ², T z = (P v : H) ∧ ‖z - dη v‖ ≤ e * Real.sqrt (B v v) := by
    intro v
    obtain ⟨z, hz⟩ := (P v).2
    have hz' : T z = (P v : H) := hz
    refine ⟨z, hz', (hT _).trans ?_⟩
    rw [map_sub, hz']
    exact hPerr v
  -- the near basis
  have he1 : ‖(EuclideanSpace.single 0 1 : ℝ²)‖ = 1 := by simp
  have he2 : ‖(EuclideanSpace.single 1 1 : ℝ²)‖ = 1 := by simp
  obtain ⟨w₁, hw₁, hdw₁⟩ := hlow _ he1
  obtain ⟨w₂, hw₂, hdw₂⟩ := hlow _ he2
  obtain ⟨z₁, hTz₁, hz₁⟩ := hS w₁
  obtain ⟨z₂, hTz₂, hz₂⟩ := hS w₂
  rw [hw₁, Real.sqrt_one, mul_one] at hz₁
  rw [hw₂, Real.sqrt_one, mul_one] at hz₂
  have hn₁ : ‖z₁ - EuclideanSpace.single 0 1‖ ≤ d + e := by
    have h := norm_sub_le_norm_sub_add_norm_sub z₁ (dη w₁) (EuclideanSpace.single 0 1)
    linarith
  have hn₂ : ‖z₂ - EuclideanSpace.single 1 1‖ ≤ d + e := by
    have h := norm_sub_le_norm_sub_add_norm_sub z₂ (dη w₂) (EuclideanSpace.single 1 1)
    linarith
  have hcoef := exists_coeff_of_near_basis_KA8 hde hn₁ hn₂
  -- the preimage of `T z` along the near basis
  have hpre : ∀ z : ℝ², ∃ a b : ℝ, (P (a • w₁ + b • w₂) : H) = T z ∧ |a| + |b| ≤ 2 * ‖z‖ := by
    intro z
    obtain ⟨a, b, hab, hs⟩ := hcoef z
    refine ⟨a, b, ?_, hs⟩
    rw [map_add, map_smul, map_smul, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul,
      ← hTz₁, ← hTz₂, ← map_smul, ← map_smul, ← map_add, hab]
  refine ⟨?_, fun v => ?_, fun v hv => ?_, fun v => ?_⟩
  · -- onto
    rintro ⟨y, z, rfl⟩
    obtain ⟨a, b, hab, -⟩ := hpre z
    exact ⟨a • w₁ + b • w₂, Subtype.ext hab⟩
  · -- normal error
    rw [hPv]
    have h := Metric.infDist_le_dist_of_mem (show T (dη v) ∈ T.range from ⟨dη v, rfl⟩)
      (x := D v)
    rw [← T.range.dist_starProjection_eq_infDist, dist_eq_norm, dist_eq_norm] at h
    exact h.trans (hD v)
  · -- lower bound on the `B`-orthogonal complement of the kernel
    obtain ⟨z, hz, -⟩ := hS v
    obtain ⟨a, b, hab, hs⟩ := hpre z
    have hk : P (v - (a • w₁ + b • w₂)) = 0 := by
      apply Subtype.ext
      rw [map_sub, Submodule.coe_sub, hab, hz, sub_self]
      rfl
    have hBk := hv _ hk
    have hBvv : B v v = a * B v w₁ + b * B v w₂ := by
      rw [map_sub, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hBk
      linarith
    have hc₁ := abs_form_le_of_unit_KA8 B hBs hBp hw₁ v
    have hc₂ := abs_form_le_of_unit_KA8 B hBs hBp hw₂ v
    set ν := Real.sqrt (B v v) with hν
    have hν0 : 0 ≤ ν := Real.sqrt_nonneg _
    have hνsq : ν ^ 2 = B v v := Real.sq_sqrt (hBp v)
    have hPz : ‖z‖ ≤ ‖P v‖ := by
      have h := hT z
      rw [hz] at h
      exact h
    have hbound : ν ^ 2 ≤ (|a| + |b|) * ν := by
      rw [hνsq, hBvv]
      have h1 : a * B v w₁ ≤ |a| * ν := by
        calc a * B v w₁ ≤ |a * B v w₁| := le_abs_self _
          _ = |a| * |B v w₁| := abs_mul _ _
          _ ≤ |a| * ν := mul_le_mul_of_nonneg_left hc₁ (abs_nonneg _)
      have h2 : b * B v w₂ ≤ |b| * ν := by
        calc b * B v w₂ ≤ |b * B v w₂| := le_abs_self _
          _ = |b| * |B v w₂| := abs_mul _ _
          _ ≤ |b| * ν := mul_le_mul_of_nonneg_left hc₂ (abs_nonneg _)
      linarith
    rcases hν0.eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]
      exact norm_nonneg _
    · have hle : ν ≤ |a| + |b| := by
        by_contra hcon
        have hcon := lt_of_not_ge hcon
        have := mul_lt_mul_of_pos_right hcon hpos
        nlinarith
      linarith
  · -- upper bound
    have h1 : ‖P v‖ ≤ ‖D v‖ := by
      change ‖(P v : H)‖ ≤ ‖D v‖
      rw [hPv]
      exact T.range.norm_starProjection_apply_le _
    have h2 : ‖D v‖ ≤ ‖T (dη v)‖ + e * Real.sqrt (B v v) := by
      linarith [hD v, norm_sub_norm_le (D v) (T (dη v))]
    have h3 : ‖T (dη v)‖ ≤ C * (2 * Real.sqrt (B v v)) :=
      (T.le_opNorm _).trans (mul_le_mul hTC (hup v) (norm_nonneg _) ((norm_nonneg _).trans hTC))
    have hν0 := Real.sqrt_nonneg (B v v)
    nlinarith

end PlaneKernel

section Metric

/-- **TCP06's rank form in metric terms**: `tcp06_rank_form_KA8` for the form `c²g_q`, with the
covector field `df_q : T_qX → ℝ²` and the map `c·dF_q`, stated with `√(c²g_q(v,v))`. -/
theorem tcp06_rank_metric_KA8 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X) (q : X) (c : ℝ)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (f : X → ℝ²) (F : X → H)
    (T : ℝ² →L[ℝ] H) (hT : ∀ z, ‖z‖ ≤ ‖T z‖) {C d e : ℝ} (hTC : ‖T‖ ≤ C)
    (hlow : ∀ ξ : ℝ², ‖ξ‖ = 1 → ∃ w : TangentSpace 𝓘(ℝ, E3) q,
      c ^ 2 * g.inner q w w = 1 ∧ ‖mvfderiv 𝓘(ℝ, E3) f q w - ξ‖ ≤ d)
    (hup : ∀ v : TangentSpace 𝓘(ℝ, E3) q,
      ‖mvfderiv 𝓘(ℝ, E3) f q v‖ ≤ 2 * Real.sqrt (c ^ 2 * g.inner q v v))
    (hD : ∀ v : TangentSpace 𝓘(ℝ, E3) q,
      ‖c • mvfderiv 𝓘(ℝ, E3) F q v - T (mvfderiv 𝓘(ℝ, E3) f q v)‖ ≤
        e * Real.sqrt (c ^ 2 * g.inner q v v))
    (hde : d + e ≤ 1 / 5) (heC : e ≤ C) :
    let P := T.range.orthogonalProjectionOnto.comp (c • mvfderiv 𝓘(ℝ, E3) F q)
    Function.Surjective P ∧
      (∀ v, ‖c • mvfderiv 𝓘(ℝ, E3) F q v - (P v : H)‖ ≤ e * Real.sqrt (c ^ 2 * g.inner q v v)) ∧
      (∀ v, (∀ k, P k = 0 → g.inner q v k = 0) →
        1 / 2 * Real.sqrt (c ^ 2 * g.inner q v v) ≤ ‖P v‖) ∧
      ∀ v, ‖P v‖ ≤ 3 * C * Real.sqrt (c ^ 2 * g.inner q v v) := by
  intro P
  obtain ⟨hBapp, hBs, hBp⟩ := scaled_form_SGP5 g q c
  have hlow' : ∀ ξ : ℝ², ‖ξ‖ = 1 → ∃ w, (c ^ 2 • g.inner q) w w = 1 ∧
      ‖mvfderiv 𝓘(ℝ, E3) f q w - ξ‖ ≤ d := by
    intro ξ hξ
    obtain ⟨w, hw1, hw⟩ := hlow ξ hξ
    exact ⟨w, by rw [hBapp]; exact hw1, hw⟩
  have hup' : ∀ v, ‖mvfderiv 𝓘(ℝ, E3) f q v‖ ≤ 2 * Real.sqrt ((c ^ 2 • g.inner q) v v) := by
    intro v
    rw [hBapp]
    exact hup v
  have hD' : ∀ v, ‖(c • mvfderiv 𝓘(ℝ, E3) F q) v - T (mvfderiv 𝓘(ℝ, E3) f q v)‖ ≤
      e * Real.sqrt ((c ^ 2 • g.inner q) v v) := by
    intro v
    rw [hBapp, smul_apply]
    exact hD v
  obtain ⟨k1, k2, k3, k4⟩ := tcp06_rank_form_KA8 (c ^ 2 • g.inner q) hBs hBp T hT hTC
    (mvfderiv 𝓘(ℝ, E3) f q) hlow' hup' (c • mvfderiv 𝓘(ℝ, E3) F q) hD' hde heC
  refine ⟨k1, fun v => ?_, fun v hv => ?_, fun v => ?_⟩
  · have h := k2 v
    rw [hBapp, smul_apply] at h
    exact h
  · have h := k3 v (fun k hk => by rw [hBapp, hv k hk, mul_zero])
    rw [hBapp] at h
    exact h
  · have h := k4 v
    rw [hBapp] at h
    exact h

end Metric

end DifferentialGeometry.Geometry.Collapse
