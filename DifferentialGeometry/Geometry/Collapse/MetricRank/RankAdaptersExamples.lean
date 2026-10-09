import DifferentialGeometry.Geometry.Collapse.MetricRank.RankAdaptersBinding

/-!
# Explicit consumers of the rank adapters at the register numbers (review 75 section C,
S-X144b group G8)

Every adapter of `RankAdaptersBinding` is instantiated once, at the scale function `ρ ≡ 2` (so the
rescaled metric is `dist / 2` and the kernel hypotheses are checked in rescaled coordinates
`π x = x / 2`), with `ε_m = 0` and the tolerance register
`β 1 = 1/20` (the review's `ν`), `β 2 = 1/10`, `β 3 = 3/20` (the review's `β₃`; the kernels need
`β 2 ≤ 3/20` and `β 3 ≤ 3/20`, and two different numbers are used on purpose since no monotonicity
across tolerances is available):

* `ℝ` at `0`: `scaledSplittingRank = 1` (line adapter; the one-splitting is the scaled isometry
  `ℝ → ℝ¹ ×₂ PUnit`);
* `ℝ²` at `0`: `scaledSplittingRank = 2` and `≤ 2` (planar adapters; the two-splitting is the
  scaled isometry `ℝ² → ℝ² ×₂ PUnit`);
* the closed upper half plane `H = {v : ℝ² | 0 ≤ v₁}` at `(0, 1/50)`: `scaledSplittingRank = 1`
  and `≤ 1` (pointed half-plane adapters; `π p = (0, 1/100)`, `h = 1/100 ≤ 1/20`; the
  one-splitting is the scaled isometry `H → ℝ¹ ×₂ [0, ∞)`).

The existence sides (`h1`, `h2`) come from `kleinerLott_of_scaled_surjective_SMR`: a surjective map
that multiplies distances by the scale factor is a Kleiner-Lott approximation of every tolerance
`δ ∈ (0, 1)` at the rescaled metric.
-/

set_option autoImplicit false

namespace GC.MetricGeometry

/-- A surjective map that multiplies all distances by `c` is a Kleiner-Lott `δ`-approximation,
for every `δ ∈ (0, 1)`, at the metric rescaled by `c`. -/
theorem kleinerLott_of_scaled_surjective_SMR {M T : Type*} [m : MetricSpace M] [MetricSpace T]
    {c : ℝ} (hc : 0 < c) (e : M → T) (he : ∀ x y, dist (e x) (e y) = c * dist x y)
    (hs : Function.Surjective e) {p : M} {q : T} (hp : e p = q) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ < 1) : Nonempty (@KleinerLottApprox M T (m.rescale c hc) _ p q δ) := by
  let _ : MetricSpace M := m.rescale c hc
  have hd : ∀ x y : M, dist x y = c * @dist M m.toDist x y := fun x y => rfl
  refine ⟨⟨hδ, hδ1, e, hp, fun x _ x' _ => ?_, fun y hy => ?_⟩⟩
  · rw [he, hd, sub_self, abs_zero]
    exact hδ.le
  · obtain ⟨x', rfl⟩ := hs y
    have hm : x' ∈ Metric.ball p δ⁻¹ := by
      rw [Metric.mem_ball, hd, ← he, hp]
      linarith
    have hi : e x' ∈ e '' Metric.ball p δ⁻¹ := ⟨x', hm, rfl⟩
    exact (Metric.infDist_le_dist_of_mem hi).trans (by simpa only [dist_self] using hδ.le)

/-- Squared distance in `ℝ¹ = EuclideanSpace ℝ (Fin 1)` between two points `!₂[a]`, `!₂[b]`. -/
theorem dist_sq_euclideanOne_SMR (a b : ℝ) :
    dist (!₂[a] : EuclideanSpace ℝ (Fin 1)) (!₂[b] : EuclideanSpace ℝ (Fin 1)) ^ 2 =
      (a - b) ^ 2 := by
  rw [dist_eq_norm, EuclideanSpace.norm_sq_eq]
  simp

/-- The scaled line `(ℝ, dist / r)` has a one-splitting at `0` (factor `PUnit`). -/
theorem hasSplitting_real_scaled_SMR {r : ℝ} (hr : 0 < r) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    @HasEuclideanSplitting.{0, 0} ℝ ((inferInstance : MetricSpace ℝ).rescale r⁻¹ (inv_pos.mpr hr))
      0 1 δ := by
  refine ⟨PUnit.{1}, inferInstance, PUnit.unit,
    kleinerLott_of_scaled_surjective_SMR (inv_pos.mpr hr)
    (fun x => WithLp.toLp 2 ((!₂[r⁻¹ * x] : EuclideanSpace ℝ (Fin 1)), PUnit.unit)) ?_ ?_
    (p := (0 : ℝ)) (q := WithLp.toLp 2 (0, PUnit.unit)) ?_ hδ hδ1⟩
  · intro x y
    rw [(WithLp.isometry_prodMk_right (E := EuclideanSpace ℝ (Fin 1)) PUnit.unit).dist_eq]
    refine (sq_eq_sq₀ dist_nonneg (by positivity)).mp ?_
    rw [dist_sq_euclideanOne_SMR, mul_pow, Real.dist_eq, sq_abs]
    ring
  · rintro ⟨a, u⟩
    refine ⟨r * a 0, ?_⟩
    have hu : u = PUnit.unit := Subsingleton.elim _ _
    subst hu
    have ha : (!₂[r⁻¹ * (r * a 0)] : EuclideanSpace ℝ (Fin 1)) = a := by
      ext i
      fin_cases i
      simp [hr.ne']
    change WithLp.toLp 2 ((!₂[r⁻¹ * (r * a 0)] : EuclideanSpace ℝ (Fin 1)), PUnit.unit) = _
    rw [ha]
  · simp

/-- The scaled Euclidean space `(ℝᵏ, dist / r)` has a `k`-splitting at `0` (factor `PUnit`). -/
theorem hasSplitting_euclidean_scaled_SMR (k : ℕ) {r : ℝ} (hr : 0 < r) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    @HasEuclideanSplitting.{0, 0} (EuclideanSpace ℝ (Fin k))
      ((inferInstance : MetricSpace (EuclideanSpace ℝ (Fin k))).rescale r⁻¹ (inv_pos.mpr hr))
      0 k δ := by
  refine ⟨PUnit.{1}, inferInstance, PUnit.unit,
    kleinerLott_of_scaled_surjective_SMR (inv_pos.mpr hr)
    (fun x => WithLp.toLp 2 (r⁻¹ • x, PUnit.unit)) ?_ ?_
    (p := (0 : EuclideanSpace ℝ (Fin k))) (q := WithLp.toLp 2 (0, PUnit.unit)) ?_ hδ hδ1⟩
  · intro x y
    rw [(WithLp.isometry_prodMk_right (E := EuclideanSpace ℝ (Fin k)) PUnit.unit).dist_eq,
      dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  · rintro ⟨a, u⟩
    refine ⟨r • a, ?_⟩
    have hu : u = PUnit.unit := Subsingleton.elim _ _
    subst hu
    change WithLp.toLp 2 (r⁻¹ • r • a, PUnit.unit) = _
    rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  · simp

/-- The scaled closed upper half plane `({v : ℝ² | 0 ≤ v₁}, dist / r)` has a one-splitting at
`(0, b)` (factor `[0, ∞)`, base point `r⁻¹ b`). -/
theorem hasSplitting_halfplane_scaled_SMR {r b : ℝ} (hr : 0 < r) (hb : 0 ≤ b) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    @HasEuclideanSplitting.{0, 0} {v : EuclideanSpace ℝ (Fin 2) // 0 ≤ v 1}
      ((inferInstance : MetricSpace {v : EuclideanSpace ℝ (Fin 2) // 0 ≤ v 1}).rescale r⁻¹
        (inv_pos.mpr hr))
      ⟨EuclideanSpace.single (1 : Fin 2) b, by simpa using hb⟩ 1 δ := by
  have hc : 0 ≤ r⁻¹ := (inv_pos.mpr hr).le
  refine ⟨{t : ℝ // 0 ≤ t}, inferInstance, ⟨r⁻¹ * b, mul_nonneg hc hb⟩,
    kleinerLott_of_scaled_surjective_SMR (inv_pos.mpr hr)
    (fun v => WithLp.toLp 2 ((!₂[r⁻¹ * v.1 0] : EuclideanSpace ℝ (Fin 1)),
      (⟨r⁻¹ * v.1 1, mul_nonneg hc v.2⟩ : {t : ℝ // 0 ≤ t}))) ?_ ?_ ?_ hδ hδ1⟩
  · intro v w
    have h := WithLp.prod_dist_sq_eq_add_sq
      (WithLp.toLp 2 ((!₂[r⁻¹ * v.1 0] : EuclideanSpace ℝ (Fin 1)),
        (⟨r⁻¹ * v.1 1, mul_nonneg hc v.2⟩ : {t : ℝ // 0 ≤ t})))
      (WithLp.toLp 2 ((!₂[r⁻¹ * w.1 0] : EuclideanSpace ℝ (Fin 1)),
        (⟨r⁻¹ * w.1 1, mul_nonneg hc w.2⟩ : {t : ℝ // 0 ≤ t})))
    have hv := norm_sq_fin_two_SMR (v.1 - w.1)
    have hd : dist v w = ‖v.1 - w.1‖ := by rw [Subtype.dist_eq, dist_eq_norm]
    have h2 : ∀ (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b),
        dist (⟨a, ha⟩ : {t : ℝ // 0 ≤ t}) ⟨b, hb⟩ ^ 2 = (a - b) ^ 2 := by
      intro a b ha hb
      rw [Subtype.dist_eq, Real.dist_eq, sq_abs]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd] at h
    refine (sq_eq_sq₀ dist_nonneg (by positivity)).mp ?_
    rw [h, dist_sq_euclideanOne_SMR, h2, mul_pow, hd, hv]
    simp only [PiLp.sub_apply]
    ring
  · rintro ⟨a, ⟨t, ht⟩⟩
    refine ⟨⟨!₂[r * a 0, r * t], by simp [mul_nonneg hr.le ht]⟩, ?_⟩
    change WithLp.toLp 2 ((!₂[r⁻¹ * (!₂[r * a 0, r * t] : EuclideanSpace ℝ (Fin 2)) 0] :
      EuclideanSpace ℝ (Fin 1)), (⟨r⁻¹ * (!₂[r * a 0, r * t] : EuclideanSpace ℝ (Fin 2)) 1, _⟩ :
      {t : ℝ // 0 ≤ t})) = _
    congr 1
    refine Prod.ext ?_ (Subtype.ext ?_)
    · ext i
      fin_cases i
      simp [hr.ne']
    · simp [hr.ne']
  · change WithLp.toLp 2 ((!₂[r⁻¹ * (EuclideanSpace.single (1 : Fin 2) b) 0] :
      EuclideanSpace ℝ (Fin 1)), (⟨r⁻¹ * (EuclideanSpace.single (1 : Fin 2) b) 1, _⟩ :
      {t : ℝ // 0 ≤ t})) = _
    congr 1
    refine Prod.ext ?_ (Subtype.ext ?_)
    · ext i
      fin_cases i
      simp
    · simp

/-- The register of tolerances of the examples: `β 1 = 1/20` (`ν`), `β 2 = 1/10`,
`β 3 = 3/20` (`β₃`, review 75 section C.3); every other value is `1/20`. -/
noncomputable def betaRegister_SMR (k : ℕ) : ℝ :=
  if k = 3 then 3 / 20 else if k = 2 then 1 / 10 else 1 / 20

theorem betaRegister_one_SMR : betaRegister_SMR 1 = 1 / 20 := by norm_num [betaRegister_SMR]

theorem betaRegister_two_SMR : betaRegister_SMR 2 = 1 / 10 := by norm_num [betaRegister_SMR]

theorem betaRegister_three_SMR : betaRegister_SMR 3 = 3 / 20 := by norm_num [betaRegister_SMR]

/-- **Consumer, line adapter.** `ℝ` at `0`, scale `2`, `π x = x / 2`, `ε_m = 0`: rank exactly `1`
(`¬` rank two at `1/10` and `¬` rank three at `3/20` from the line kernel; one-splitting at
`1/20` from the scaled isometry). -/
theorem real_line_scaledSplittingRank_one_SMR :
    scaledSplittingRank.{0, 0} (fun _ : ℝ => (2 : ℝ)) (fun _ => two_pos) betaRegister_SMR 0 =
      1 := by
  have h1 : @HasEuclideanSplitting.{0, 0} ℝ
      ((inferInstance : MetricSpace ℝ).rescale 2⁻¹ (inv_pos.mpr two_pos)) 0 1
      (betaRegister_SMR 1) := by
    rw [betaRegister_one_SMR]
    exact hasSplitting_real_scaled_SMR two_pos (by norm_num) (by norm_num)
  refine scaledSplittingRank_eq_one_of_line_ball_SMR (εm := 0) h1
    (by rw [betaRegister_two_SMR]; norm_num) (by rw [betaRegister_three_SMR]) (by norm_num)
    (fun x => x / 2) ?_
  intro x y _ _
  change |((2 : ℝ)⁻¹ * dist x y - |x / 2 - y / 2|)| ≤ 0
  rw [Real.dist_eq, ← sub_div, abs_div, abs_two]
  have h0 : (2 : ℝ)⁻¹ * |x - y| - |x - y| / 2 = 0 := by ring
  rw [h0, abs_zero]

/-- The kernel hypothesis of the planar adapters for `ℝ²`, scale `2`, `π x = x / 2`. -/
theorem euclidean_plane_scaled_dist_SMR (x y : EuclideanSpace ℝ (Fin 2)) :
    |((2 : ℝ)⁻¹ * dist x y - ‖(2 : ℝ)⁻¹ • x - (2 : ℝ)⁻¹ • y‖)| ≤ 0 := by
  rw [dist_eq_norm, ← smul_sub, norm_smul]
  simp

/-- **Consumer, planar adapter (rank two).** `ℝ²` at `0`, scale `2`, `π x = x / 2`,
`ε_m = 0`: rank exactly `2` (`¬` rank three at `3/20` from the planar kernel; two-splitting at
`1/10` from the scaled isometry). -/
theorem euclidean_plane_scaledSplittingRank_two_SMR :
    scaledSplittingRank.{0, 0} (fun _ : EuclideanSpace ℝ (Fin 2) => (2 : ℝ)) (fun _ => two_pos)
      betaRegister_SMR 0 = 2 := by
  have h2 : @HasEuclideanSplitting.{0, 0} (EuclideanSpace ℝ (Fin 2))
      ((inferInstance : MetricSpace (EuclideanSpace ℝ (Fin 2))).rescale 2⁻¹
        (inv_pos.mpr two_pos)) 0 2 (betaRegister_SMR 2) := by
    rw [betaRegister_two_SMR]
    exact hasSplitting_euclidean_scaled_SMR 2 two_pos (by norm_num) (by norm_num)
  exact scaledSplittingRank_eq_two_of_planar_ball_SMR (εm := 0) h2
    (by rw [betaRegister_three_SMR]) (by norm_num) (fun x => (2 : ℝ)⁻¹ • x)
    (fun x y _ _ => euclidean_plane_scaled_dist_SMR x y)

/-- **Consumer, planar adapter (rank at most two)**, same data, no two-splitting needed. -/
theorem euclidean_plane_scaledSplittingRank_le_two_SMR :
    scaledSplittingRank.{0, 0} (fun _ : EuclideanSpace ℝ (Fin 2) => (2 : ℝ)) (fun _ => two_pos)
      betaRegister_SMR 0 ≤ 2 :=
  scaledSplittingRank_le_two_of_planar_ball_SMR (εm := 0) (by rw [betaRegister_three_SMR])
    (by norm_num) (fun x => (2 : ℝ)⁻¹ • x) (fun x y _ _ => euclidean_plane_scaled_dist_SMR x y)

local notation "HP" => {v : EuclideanSpace ℝ (Fin 2) // 0 ≤ v 1}

/-- The kernel hypothesis of the half-plane adapters for `H`, scale `2`, `π v = v / 2`. -/
theorem halfplane_scaled_dist_SMR (x y : HP) :
    |((2 : ℝ)⁻¹ * dist x y - ‖(2 : ℝ)⁻¹ • x.1 - (2 : ℝ)⁻¹ • y.1‖)| ≤ 0 := by
  rw [Subtype.dist_eq, dist_eq_norm, ← smul_sub, norm_smul]
  simp

/-- **Consumer, pointed half-plane adapter (rank one).** `H` at `(0, 1/50)`, scale `2`,
`π v = v / 2` (so `π p = (0, 1/100)`, `h = 1/100 ≤ 1/20`), `ε_m = 0`: rank exactly `1`
(`¬` rank two at `1/10` and `¬` rank three at `3/20` from the half-plane kernel; one-splitting at
`1/20` from the scaled isometry `H → ℝ¹ ×₂ [0, ∞)`). -/
theorem halfplane_boundary_scaledSplittingRank_one_SMR :
    scaledSplittingRank.{0, 0} (fun _ : HP => (2 : ℝ)) (fun _ => two_pos) betaRegister_SMR
      ⟨EuclideanSpace.single (1 : Fin 2) (1 / 50 : ℝ), by simp⟩ = 1 := by
  have h1 : @HasEuclideanSplitting.{0, 0} HP
      ((inferInstance : MetricSpace HP).rescale 2⁻¹ (inv_pos.mpr two_pos))
      ⟨EuclideanSpace.single (1 : Fin 2) (1 / 50 : ℝ), by simp⟩ 1 (betaRegister_SMR 1) := by
    rw [betaRegister_one_SMR]
    exact hasSplitting_halfplane_scaled_SMR (b := 1 / 50) two_pos (by norm_num) (by norm_num)
      (by norm_num)
  refine scaledSplittingRank_eq_one_of_halfplane_boundary_SMR (εm := 0) (h := 1 / 100) h1
    (by rw [betaRegister_two_SMR]; norm_num) (by rw [betaRegister_three_SMR]) (by norm_num)
    (fun x => (2 : ℝ)⁻¹ • x.1) (fun x y _ _ => halfplane_scaled_dist_SMR x y)
    (fun x _ => ?_) (by norm_num) (by norm_num) (by simp) (by simp; norm_num)
  simpa using mul_nonneg (inv_nonneg.mpr (by norm_num : (0 : ℝ) ≤ 2)) x.2

/-- **Consumer, pointed half-plane adapter (rank at most one)**, same data, no one-splitting
needed. -/
theorem halfplane_boundary_scaledSplittingRank_le_one_SMR :
    scaledSplittingRank.{0, 0} (fun _ : HP => (2 : ℝ)) (fun _ => two_pos) betaRegister_SMR
      ⟨EuclideanSpace.single (1 : Fin 2) (1 / 50 : ℝ), by simp⟩ ≤ 1 := by
  refine scaledSplittingRank_le_one_of_halfplane_boundary_SMR (εm := 0) (h := 1 / 100)
    (by rw [betaRegister_two_SMR]; norm_num) (by rw [betaRegister_three_SMR]) (by norm_num)
    (fun x => (2 : ℝ)⁻¹ • x.1) (fun x y _ _ => halfplane_scaled_dist_SMR x y)
    (fun x _ => ?_) (by norm_num) (by norm_num) (by simp) (by simp; norm_num)
  simpa using mul_nonneg (inv_nonneg.mpr (by norm_num : (0 : ℝ) ≤ 2)) x.2

end GC.MetricGeometry
