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

theorem iteratedDs_two_curvature_bernstein_bound
    (B : RicciBackground (I := I) (M := M) J a b) (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    {C D ρ α : ℝ} (hC : 1 ≤ C) (hBC : B.C ≤ C) (hD : 1 ≤ D) (hρ : 1 ≤ ρ)
    (hfirst : 64 * (1 + C) * D ^ 2 ≤ α)
    (hnext : 2 * (curvatureForcingConstant 2 C D) ^ 2 +
      2 * curvatureForcingConstant 2 C D + 2 * C ≤ α)
    (hlen : u - s = ((1 + α) * ρ ^ 2)⁻¹)
    (hambient : ∀ x t, t ∈ Icc s u → ∀ (kind : CurvatureTensorKind) (j : ℕ), j ≤ 3 →
      Real.sqrt (normSq0S (B.family.metric t) (c.lift x t) (kind.arity + j)
        (kind.field B.family j t (c.lift x t))) ≤ C)
    (hjets : ∀ x t, t ∈ Icc s u → ∀ j ≤ 1,
      Real.sqrt (c.normSq B.family.metric
        (c.iteratedDs B.family.metric j (c.curvatureVector B.family.metric)) x t) ≤ D * ρ ^ (j + 1)) :
    ∀ x, c.normSq B.family.metric
      (c.iteratedDs B.family.metric 2 (c.curvatureVector B.family.metric)) x u ≤
      (1 + 2 * D ^ 2 * (1 + 3 * α)) * ρ ^ 6 := by
  have hα : 0 ≤ α := (by positivity : 0 ≤ 64 * (1 + C) * D ^ 2).trans hfirst
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
  have hjetsSq (x t : ℝ) (ht : t ∈ Icc s u) (j : ℕ) (hj : j ≤ 1) :
      f j x t ≤ D ^ 2 * ρ ^ (2 * j + 2) := by
    have hs := hjets x t ht j hj
    change Real.sqrt (f j x t) ≤ D * ρ ^ (j + 1) at hs
    have hpow : (D * ρ ^ (j + 1)) ^ 2 = D ^ 2 * ρ ^ (2 * j + 2) := by
      rw [mul_pow, ← pow_mul]
      congr 2
      omega
    rw [← Real.sq_sqrt (hn j x t), ← hpow]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
  have hpde0 (x t : ℝ) (ht : t ∈ Icc s u) :
      derivWithin (f 1 x) (Icc s u) t - c.ds g (c.ds g (f 1)) x t ≤
        -f 2 x t + (2 * α * D ^ 2) * ρ ^ 6 := by
    have hDR : normSq0S (g t) (c.lift x t) 5
        (totalNabla0SFun 4 (B.family.connection t) (B.family.rm04 t) (c.lift x t)) ≤ C ^ 2 := by
      have hh := hambient x t ht .riemann 1 (by norm_num)
      exact (Real.sqrt_le_iff.mp hh).2
    have hDDRic : normSq0S (g t) (c.lift x t) 4
        (totalNabla0SFun 3 (B.family.connection t)
          (CheegerGromovCompactness.covStep (g t) 2 (B.family.ricci t)) (c.lift x t)) ≤ C ^ 2 := by
      have hh := hambient x t ht .ricci 2 (by norm_num)
      exact (Real.sqrt_le_iff.mp hh).2
    have hΛ : 1 ≤ D ^ 2 * ρ ^ 2 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hD) (one_le_pow₀ hρ)
    have hk : c.curvatureSq g x t ≤ D ^ 2 * ρ ^ 2 := hjetsSq x t ht 0 (by omega)
    have hh := c.curvatureDerivative_evolution_le_of_tensor_bounds B hsu hwindow hc x t ht
      C (D ^ 2 * ρ ^ 2) hBC hΛ hk hDR hDDRic
    change derivWithin (f 1 x) (Icc s u) t - c.ds g (c.ds g (f 1)) x t ≤
      -f 2 x t + 64 * (1 + C) * (D ^ 2 * ρ ^ 2) * f 1 x t +
        64 * (1 + C) * (D ^ 2 * ρ ^ 2) ^ 2 at hh
    have hcoeff := mul_le_mul_of_nonneg_right hfirst
      (mul_nonneg (sq_nonneg ρ) (hn 1 x t))
    have hsource := mul_le_mul_of_nonneg_right hfirst
      (mul_nonneg (sq_nonneg D) (pow_nonneg hρ0.le 4))
    have hbounded := mul_le_mul_of_nonneg_left (hjetsSq x t ht 1 le_rfl)
      (mul_nonneg hα (sq_nonneg ρ))
    norm_num only at hbounded
    have hscale : ρ ^ 4 ≤ ρ ^ 6 := pow_le_pow_right₀ hρ (by omega)
    have hscale' := mul_le_mul_of_nonneg_left hscale (mul_nonneg hα (sq_nonneg D))
    nlinarith only [hh, hcoeff, hsource, hbounded, hscale']
  have hpde1 (x t : ℝ) (ht : t ∈ Icc s u) :
      derivWithin (f 2 x) (Icc s u) t - c.ds g (c.ds g (f 2)) x t ≤
        (α * ρ ^ 2) * f 2 x t + (1 + α) * ρ ^ 8 := by
    have hh := c.iteratedDs_curvature_evolution_le_of_lower_derivative_bounds B hsu hwindow hc
      (m := 2) (by norm_num) hC hD hρ x t ht
      (fun kind j hj => hambient x t ht kind j hj)
      (fun j hj => hjets x t ht j (by omega))
    change derivWithin (f 2 x) (Icc s u) t - c.ds g (c.ds g (f 2)) x t ≤
      -f 3 x t + (2 * curvatureForcingConstant 2 C D ^ 2 +
        2 * curvatureForcingConstant 2 C D + 2 * C) * ρ ^ 2 * f 2 x t + (ρ ^ 2) ^ 4 at hh
    have hcoeff := mul_le_mul_of_nonneg_right hnext
      (mul_nonneg (sq_nonneg ρ) (hn 2 x t))
    have hsource := mul_nonneg hα (pow_nonneg hρ0.le 8)
    nlinarith only [hh, hcoeff, hn 3 x t, hsource]
  have htime : α * ρ ^ 2 * (u - s) ≤ 1 := by
    rw [hlen]
    have heq : α * ρ ^ 2 * ((1 + α) * ρ ^ 2)⁻¹ = α / (1 + α) := by
      field_simp [ne_of_gt hq, ne_of_gt hρ0]
    rw [heq]
    apply (div_le_one hq).mpr
    linarith
  have hbound := c.bernstein_bound_of_coupled_scalar_inequalities g hsu hc.smooth hc.immersed
    (f 1) (f 2) (hf 1) (hf 2) (hper 1) (hper 2)
    (fun x => hn 1 x u) (fun x t _ => hn 2 x t)
    (D ^ 2 * ρ ^ 4) (α * ρ ^ 2) ((2 * α * D ^ 2) * ρ ^ 6)
    ((1 + α) * ρ ^ 8) (by positivity) htime hpde0 hpde1
    (fun x => hjetsSq x s ⟨le_rfl, hsu.le⟩ 1 le_rfl)
  intro x
  have hh := hbound x
  rw [hlen] at hh
  refine hh.trans_eq ?_
  field_simp [ne_of_gt hq, ne_of_gt hρ0]
  ring

theorem iteratedDs_two_curvature_bernstein_bound_of_normSq_le_div
    (B : RicciBackground (I := I) (M := M) J a b) (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    {C D α : ℝ} (hC : 1 ≤ C) (hBC : B.C ≤ C) (hD : 1 ≤ D)
    (hfirst : 64 * (1 + C) * D ^ 2 ≤ α)
    (hnext : 2 * (curvatureForcingConstant 2 C D) ^ 2 +
      2 * curvatureForcingConstant 2 C D + 2 * C ≤ α)
    (hlen : u - s ≤ 1)
    (hambient : ∀ x t, t ∈ Icc s u → ∀ (kind : CurvatureTensorKind) (j : ℕ), j ≤ 3 →
      Real.sqrt (normSq0S (B.family.metric t) (c.lift x t) (kind.arity + j)
        (kind.field B.family j t (c.lift x t))) ≤ C)
    (hjets : ∀ x t, t ∈ Ioc s u → ∀ j ≤ 1,
      c.normSq B.family.metric
        (c.iteratedDs B.family.metric j (c.curvatureVector B.family.metric)) x t ≤
        D ^ 2 / (t - s) ^ (j + 1)) :
    ∀ x, c.normSq B.family.metric
      (c.iteratedDs B.family.metric 2 (c.curvatureVector B.family.metric)) x u ≤
      ((1 + 2 * D ^ 2 * (1 + 3 * α)) * 8) / (u - s) ^ 3 := by
  have hα : 0 ≤ α := (by positivity : 0 ≤ 64 * (1 + C) * D ^ 2).trans hfirst
  obtain ⟨ρ, v, hρ, hsv, hvu, hvlen, hρsq, htau⟩ :=
    exists_bernstein_subinterval hsu hlen hα
  have hsub : Icc v u ⊆ Icc s u := Icc_subset_Icc hsv.le le_rfl
  have hsuboc : Icc v u ⊆ Ioc s u := fun _ ht => ⟨hsv.trans_le ht.1, ht.2⟩
  have hc' := hc.mono hsub (fun t ht => (uniqueDiffOn_Icc hvu t ht).uniqueMDiffWithinAt)
  have hpow (j : ℕ) : ρ ^ (2 * j + 2) = (2 / (u - s)) ^ (j + 1) := by
    calc
      ρ ^ (2 * j + 2) = (ρ ^ 2) ^ (j + 1) := by rw [← pow_mul]; congr 1
      _ = _ := by rw [hρsq]
  have hjets' (x t : ℝ) (ht : t ∈ Icc v u) (j : ℕ) (hj : j ≤ 1) :
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
  have hh := c.iteratedDs_two_curvature_bernstein_bound B hvu (hsub.trans hwindow) hc' hC hBC hD hρ
    hfirst hnext hvlen (fun x t ht kind j hj => hambient x t (hsub ht) kind j hj) hjets'
  intro x
  refine (hh x).trans_eq ?_
  have hpower : ρ ^ 6 = (2 / (u - s)) ^ 3 := by
    calc
      ρ ^ 6 = (ρ ^ 2) ^ 3 := by rw [← pow_mul]
      _ = _ := by rw [hρsq]
  rw [hpower, div_pow]
  ring

end CurveMap
end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
