import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.HigherDerivativeReaction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Bernstein

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

private theorem bernstein_scaled_coefficient_step
    (m : ℕ) (A α ρ : ℝ) (hA : 0 ≤ A) (hα : 0 ≤ α) (hρ : 0 < ρ) :
    let q := 1 + α
    let τ := (q * ρ ^ 2)⁻¹
    let L := A * ρ ^ (2 * m + 2)
    let β := (α * A + 1) * ρ ^ (2 * m + 4)
    let γ := q * ρ ^ (2 * m + 6)
    0 < 3 + 2 * A * (1 + 2 * α) ∧
      2 * L / τ + γ * τ + 2 * β ≤
        (3 + 2 * A * (1 + 2 * α)) * ρ ^ (2 * m + 4) := by
  dsimp only
  have hq : 0 < 1 + α := by linarith
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  have hqρne : (1 + α) * ρ ^ 2 ≠ 0 := mul_ne_zero (ne_of_gt hq) (pow_ne_zero 2 hρne)
  constructor
  · positivity
  · have hfirst :
        2 * (A * ρ ^ (2 * m + 2)) / ((1 + α) * ρ ^ 2)⁻¹ =
          2 * A * (1 + α) * ρ ^ (2 * m + 4) := by
      rw [div_eq_mul_inv, inv_inv]
      calc
        2 * (A * ρ ^ (2 * m + 2)) * ((1 + α) * ρ ^ 2) =
            2 * A * (1 + α) * (ρ ^ (2 * m + 2) * ρ ^ 2) := by ring
        _ = 2 * A * (1 + α) * ρ ^ (2 * m + 4) := by rw [← pow_add]
    have hsecond :
        (1 + α) * ρ ^ (2 * m + 6) * ((1 + α) * ρ ^ 2)⁻¹ =
          ρ ^ (2 * m + 4) := by
      field_simp [hqρne]
      rw [← pow_add]
      congr 1
      omega
    rw [hfirst, hsecond]
    have hp : 0 ≤ ρ ^ (2 * m + 4) := pow_nonneg hρ.le _
    nlinarith only [hA, hα, hp]

private theorem exists_bernstein_subinterval {s u α : ℝ} (hsu : s < u) (hlen : u - s ≤ 1)
    (hα : 0 ≤ α) :
    ∃ ρ v : ℝ, 1 ≤ ρ ∧ s < v ∧ v < u ∧
      u - v = ((1 + α) * ρ ^ 2)⁻¹ ∧
      ρ ^ 2 = 2 / (u - s) ∧
      ∀ t ∈ Set.Icc v u, (u - s) / 2 ≤ t - s := by
  let τ := u - s
  let ρ := Real.sqrt (2 / τ)
  let v := u - ((1 + α) * ρ ^ 2)⁻¹
  have hτ : 0 < τ := sub_pos.mpr hsu
  have hρsq : ρ ^ 2 = 2 / τ := Real.sq_sqrt (by positivity)
  have hρ : 1 ≤ ρ := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    dsimp only [τ]
    apply (le_div_iff₀ (sub_pos.mpr hsu)).mpr
    norm_num
    linarith only [hlen]
  have hq : 0 < 1 + α := by linarith only [hα]
  have hρsq0 : 0 < ρ ^ 2 := by rw [hρsq]; positivity
  have hstep0 : 0 < ((1 + α) * ρ ^ 2)⁻¹ := inv_pos.mpr (mul_pos hq hρsq0)
  have hstep : ((1 + α) * ρ ^ 2)⁻¹ ≤ τ / 2 := by
    apply (inv_le_iff_one_le_mul₀ (mul_pos hq hρsq0)).mpr
    rw [hρsq]
    have heq : (τ / 2) * ((1 + α) * (2 / τ)) = 1 + α := by field_simp
    rw [heq]
    linarith only [hα]
  refine ⟨ρ, v, hρ, ?_, ?_, ?_, hρsq, ?_⟩
  · dsimp only [v]
    dsimp only [τ] at hstep
    linarith only [hstep, hsu]
  · dsimp only [v]
    linarith only [hstep0]
  · dsimp only [v]
    ring
  · intro t ht
    dsimp only [v] at ht
    dsimp only [τ] at hstep
    linarith only [ht.1, hstep]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [SigmaCompactSpace M] {J : RealTimeInterval} {a b s u : ℝ}
namespace CurveMap

theorem iteratedDs_curvature_bernstein_bound
    (B : RicciBackground (I := I) (M := M) J a b) (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    {m : ℕ} (hm : 2 ≤ m) {C D ρ α : ℝ} (hC : 1 ≤ C) (hD : 1 ≤ D) (hρ : 1 ≤ ρ)
    (hcoeff : ∀ j ∈ ({m, m + 1} : Set ℕ),
      2 * (curvatureForcingConstant j C D) ^ 2 + 2 * curvatureForcingConstant j C D + 2 * C ≤ α)
    (hlen : u - s = ((1 + α) * ρ ^ 2)⁻¹)
    (hambient : ∀ x t, t ∈ Icc s u → ∀ (kind : CurvatureTensorKind) (j : ℕ), j ≤ m + 2 →
      Real.sqrt (normSq0S (B.family.metric t) (c.lift x t) (kind.arity + j)
        (kind.field B.family j t (c.lift x t))) ≤ C)
    (hjets : ∀ x t, t ∈ Icc s u → ∀ j ≤ m,
      Real.sqrt (c.normSq B.family.metric
        (c.iteratedDs B.family.metric j (c.curvatureVector B.family.metric)) x t) ≤ D * ρ ^ (j + 1)) :
    ∀ x, c.normSq B.family.metric
      (c.iteratedDs B.family.metric (m + 1) (c.curvatureVector B.family.metric)) x u ≤
      (3 + 2 * D ^ 2 * (1 + 2 * α)) * ρ ^ (2 * m + 4) := by
  have hα : 0 ≤ α := by
    have hK : 0 ≤ curvatureForcingConstant m C D :=
      (zero_le_one.trans hC).trans (le_curvatureForcingConstant m (zero_le_one.trans hC) hD)
    have ha := hcoeff m (by simp)
    nlinarith only [ha, hK, hC, sq_nonneg (curvatureForcingConstant m C D)]
  let g := B.family.metric
  let V := fun j => c.iteratedDs g j (c.curvatureVector g)
  let f := fun j => c.normSq g (V j)
  have hJ : Icc s u ⊆ J.regular := fun τ hτ => B.regular (hwindow hτ)
  have hH := Field.smoothOn_curvatureVector g B.smooth hJ (uniqueDiffOn_Icc hsu) c hc.smooth hc.immersed
  have hV (j : ℕ) : (V j).SmoothOn (I := I) (Icc s u) :=
    Field.smoothOn_iteratedDs g B.smooth hJ (uniqueDiffOn_Icc hsu) c hc.smooth hc.immersed
      (c.curvatureVector g) hH j
  have hf (j : ℕ) : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f j p.1 p.2) (univ ×ˢ Icc s u) :=
    Field.smoothOn_inner g B.smooth hJ c hc.smooth (V j) (V j) (hV j) (hV j)
  have hper (j : ℕ) (t : ℝ) (ht : t ∈ Icc s u) :
      Function.Periodic (fun x => f j x t) 1 := by
    have hγ (x : ℝ) := (contMDiffOn_univ.mp
      (c.space_slice_contMDiffOn (Icc s u) hc.smooth t ht)).mdifferentiable (by simp) x
    have hDs (Z : c.Field (I := I))
        (hZ : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞ (fun y => (⟨c.lift y t, Z y t⟩ : TangentBundle I M)))
        (hZper : Function.Periodic (fun x => Z x t) 1) :
        Function.Periodic (fun x => c.Ds g Z x t) 1 := by
      intro x
      dsimp only [CurveMap.Ds]
      rw [c.speed_add_period g t x (hγ (x + 1)), c.Dx_add_period g t x Z hZper hZ (hγ (x + 1))]
      rfl
    have hVper (k : ℕ) : Function.Periodic (fun x => V k x t) 1 := by
      induction k with
      | zero =>
        exact hDs (c.unitTangent g)
          (c.unitTangent_contMDiff g (Icc s u) hc.smooth hc.immersed t ht)
          (fun x => c.unitTangent_add_period g t x (hγ (x + 1)))
      | succ k ih =>
        simpa only [V, CurveMap.iteratedDs, Function.iterate_succ_apply'] using
          hDs (V k)
            (c.iteratedDs_contMDiff g hc.smooth hc.immersed (c.curvatureVector g) t ht
              (c.curvatureVector_contMDiff g (Icc s u) hc.smooth hc.immersed t ht) k) ih
    intro x
    change (g t).inner (c.lift (x + 1) t) (V j (x + 1) t) (V j (x + 1) t) = _
    have heq : V j (x + 1) t = V j x t := hVper j x
    have hl : c.lift (x + 1) t = c.lift x t := c.lift_add_period t x
    rw [hl, heq]
    rfl
  have hρ0 : 0 < ρ := zero_lt_one.trans_le hρ
  have hq : 0 < 1 + α := by linarith only [hα]
  have hn (j : ℕ) (x t : ℝ) : 0 ≤ f j x t := c.normSq_nonneg g (V j) x t
  have hjetsSq (x t : ℝ) (ht : t ∈ Icc s u) (j : ℕ) (hj : j ≤ m) :
      f j x t ≤ D ^ 2 * ρ ^ (2 * j + 2) := by
    have hs := hjets x t ht j hj
    change Real.sqrt (f j x t) ≤ D * ρ ^ (j + 1) at hs
    have hpow : (D * ρ ^ (j + 1)) ^ 2 = D ^ 2 * ρ ^ (2 * j + 2) := by
      rw [mul_pow, ← pow_mul]
      congr 2
      omega
    rw [← Real.sq_sqrt (hn j x t), ← hpow]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
  have hevol (j : ℕ) (hj : j ∈ ({m, m + 1} : Set ℕ)) (x t : ℝ) (ht : t ∈ Icc s u) :
      derivWithin (f j x) (Icc s u) t - c.ds g (c.ds g (f j)) x t ≤
        -f (j + 1) x t + α * ρ ^ 2 * f j x t + ρ ^ (2 * j + 4) := by
    have hjcases : j = m ∨ j = m + 1 := by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hj
    have h0 := c.iteratedDs_curvature_evolution_le_of_lower_derivative_bounds B hsu hwindow hc
      (m := j) (by rcases hjcases with rfl | rfl <;> omega) hC hD hρ x t ht
      (fun kind k hk => hambient x t ht kind k (by rcases hjcases with rfl | rfl <;> omega))
      (fun k hk => hjets x t ht k (by rcases hjcases with rfl | rfl <;> omega))
    dsimp only at h0
    have hforce : (ρ ^ 2) ^ (j + 2) = ρ ^ (2 * j + 4) := by rw [← pow_mul]; congr 1
    rw [hforce] at h0
    refine h0.trans ?_
    have hmult := mul_le_mul_of_nonneg_right (hcoeff j hj) (mul_nonneg (sq_nonneg ρ) (hn j x t))
    change -f (j + 1) x t +
      (2 * (curvatureForcingConstant j C D) ^ 2 + 2 * curvatureForcingConstant j C D + 2 * C) *
      ρ ^ 2 * f j x t + ρ ^ (2 * j + 4) ≤ _
    nlinarith only [hmult]
  have hpde0 (x t : ℝ) (ht : t ∈ Icc s u) :
      derivWithin (f m x) (Icc s u) t - c.ds g (c.ds g (f m)) x t ≤
        -f (m + 1) x t + (α * D ^ 2 + 1) * ρ ^ (2 * m + 4) := by
    refine (hevol m (by simp) x t ht).trans ?_
    have hmult := mul_le_mul_of_nonneg_left (hjetsSq x t ht m le_rfl) (mul_nonneg hα (sq_nonneg ρ))
    have hpow : ρ ^ 2 * ρ ^ (2 * m + 2) = ρ ^ (2 * m + 4) := by rw [← pow_add]; congr 1; omega
    calc
      _ ≤ -f (m + 1) x t + α * ρ ^ 2 * (D ^ 2 * ρ ^ (2 * m + 2)) + ρ ^ (2 * m + 4) := by linarith only [hmult]
      _ = _ := by rw [mul_assoc α, mul_left_comm (ρ ^ 2), hpow]; ring
  have hpde1 (x t : ℝ) (ht : t ∈ Icc s u) :
      derivWithin (f (m + 1) x) (Icc s u) t - c.ds g (c.ds g (f (m + 1))) x t ≤
        (α * ρ ^ 2) * f (m + 1) x t + ((1 + α) * ρ ^ (2 * m + 6)) := by
    have hh := hevol (m + 1) (by simp) x t ht
    have hpow : 2 * (m + 1) + 4 = 2 * m + 6 := by omega
    rw [hpow] at hh
    have hsource : ρ ^ (2 * m + 6) ≤ (1 + α) * ρ ^ (2 * m + 6) := by
      have := mul_nonneg hα (pow_nonneg hρ0.le (2 * m + 6))
      linarith only [this]
    linarith only [hh, hn (m + 1 + 1) x t, hsource]
  have htime : α * ρ ^ 2 * (u - s) ≤ 1 := by
    rw [hlen]
    have heq : α * ρ ^ 2 * ((1 + α) * ρ ^ 2)⁻¹ = α / (1 + α) := by
      field_simp [ne_of_gt hq, ne_of_gt hρ0]
    rw [heq]
    apply (div_le_one hq).mpr
    linarith
  have hbound := c.bernstein_bound_of_coupled_scalar_inequalities g hsu hc.smooth hc.immersed
    (f m) (f (m + 1)) (hf m) (hf (m + 1)) (hper m) (hper (m + 1))
    (fun x => hn m x u) (fun x t _ => hn (m + 1) x t)
    (D ^ 2 * ρ ^ (2 * m + 2)) (α * ρ ^ 2) ((α * D ^ 2 + 1) * ρ ^ (2 * m + 4))
    ((1 + α) * ρ ^ (2 * m + 6)) (by positivity) htime hpde0 hpde1
    (fun x => hjetsSq x s ⟨le_rfl, hsu.le⟩ m le_rfl)
  intro x
  have hh := hbound x
  rw [hlen] at hh
  exact hh.trans (bernstein_scaled_coefficient_step m (D ^ 2) α ρ (sq_nonneg D) hα hρ0).2

theorem iteratedDs_curvature_bernstein_bound_of_normSq_le_div
    (B : RicciBackground (I := I) (M := M) J a b) (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    {m : ℕ} (hm : 2 ≤ m) {C D α : ℝ} (hC : 1 ≤ C) (hD : 1 ≤ D)
    (hcoeff : ∀ j ∈ ({m, m + 1} : Set ℕ),
      2 * (curvatureForcingConstant j C D) ^ 2 + 2 * curvatureForcingConstant j C D + 2 * C ≤ α)
    (hlen : u - s ≤ 1)
    (hambient : ∀ x t, t ∈ Icc s u → ∀ (kind : CurvatureTensorKind) (j : ℕ), j ≤ m + 2 →
      Real.sqrt (normSq0S (B.family.metric t) (c.lift x t) (kind.arity + j)
        (kind.field B.family j t (c.lift x t))) ≤ C)
    (hjets : ∀ x t, t ∈ Ioc s u → ∀ j ≤ m,
      c.normSq B.family.metric
        (c.iteratedDs B.family.metric j (c.curvatureVector B.family.metric)) x t ≤
        D ^ 2 / (t - s) ^ (j + 1)) :
    ∀ x, c.normSq B.family.metric
      (c.iteratedDs B.family.metric (m + 1) (c.curvatureVector B.family.metric)) x u ≤
      ((3 + 2 * D ^ 2 * (1 + 2 * α)) * 2 ^ (m + 2)) / (u - s) ^ (m + 2) := by
  have hα : 0 ≤ α := by
    have hK : 0 ≤ curvatureForcingConstant m C D :=
      (zero_le_one.trans hC).trans (le_curvatureForcingConstant m (zero_le_one.trans hC) hD)
    have ha := hcoeff m (by simp)
    nlinarith only [ha, hK, hC, sq_nonneg (curvatureForcingConstant m C D)]
  obtain ⟨ρ, v, hρ, hsv, hvu, hvlen, hρsq, htau⟩ :=
    exists_bernstein_subinterval hsu hlen hα
  have hsub : Icc v u ⊆ Icc s u := Icc_subset_Icc hsv.le le_rfl
  have hsuboc : Icc v u ⊆ Ioc s u := fun _ ht => ⟨hsv.trans_le ht.1, ht.2⟩
  have hc' := hc.mono hsub (fun t ht => (uniqueDiffOn_Icc hvu t ht).uniqueMDiffWithinAt)
  have hpow (j : ℕ) : ρ ^ (2 * j + 2) = (2 / (u - s)) ^ (j + 1) := by
    calc
      ρ ^ (2 * j + 2) = (ρ ^ 2) ^ (j + 1) := by rw [← pow_mul]; congr 1
      _ = _ := by rw [hρsq]
  have hjets' (x t : ℝ) (ht : t ∈ Icc v u) (j : ℕ) (hj : j ≤ m) :
      Real.sqrt (c.normSq B.family.metric
        (c.iteratedDs B.family.metric j (c.curvatureVector B.family.metric)) x t) ≤
        D * ρ ^ (j + 1) := by
    have hts : 0 < t - s := sub_pos.mpr (hsuboc ht).1
    have hδ : 0 < u - s := sub_pos.mpr hsu
    have hinv : 1 / (t - s) ≤ 2 / (u - s) := by
      apply (div_le_div_iff₀ hts hδ).mpr
      have hh := htau t ht
      nlinarith only [hh]
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg (zero_le_one.trans hD) (pow_nonneg (zero_le_one.trans hρ) _), ?_⟩
    calc
      _ ≤ D ^ 2 / (t - s) ^ (j + 1) := hjets x t (hsuboc ht) j hj
      _ = D ^ 2 * (1 / (t - s)) ^ (j + 1) := by rw [div_pow]; ring
      _ ≤ D ^ 2 * (2 / (u - s)) ^ (j + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hinv _) (sq_nonneg D)
      _ = (D * ρ ^ (j + 1)) ^ 2 := by
        rw [← hpow j, mul_pow, ← pow_mul]
        congr 2
        omega
  have hh := c.iteratedDs_curvature_bernstein_bound B hvu (hsub.trans hwindow) hc' hm hC hD hρ
    hcoeff hvlen (fun x t ht kind j hj => hambient x t (hsub ht) kind j hj) hjets'
  intro x
  refine (hh x).trans_eq ?_
  have hpower : ρ ^ (2 * m + 4) = (2 / (u - s)) ^ (m + 2) := by
    calc
      ρ ^ (2 * m + 4) = (ρ ^ 2) ^ (m + 2) := by rw [← pow_mul]; congr 1
      _ = _ := by rw [hρsq]
  rw [hpower, div_pow]
  ring

end CurveMap
end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
