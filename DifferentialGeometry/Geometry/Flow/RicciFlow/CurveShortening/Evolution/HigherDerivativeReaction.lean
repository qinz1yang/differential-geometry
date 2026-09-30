import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.CurvatureContractions
import DifferentialGeometry.Analysis.Estimates.ProductBounds
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem CurvatureContraction.abs_eval_le_of_lower_derivative_bounds
    (c : CurveMap M) (G : SolutionFamily (I := I) (M := M)) (W : c.Field (I := I))
    {m : ℕ} (hm : 2 ≤ m) {C D ρ : ℝ} (hC : 1 ≤ C) (hD : 1 ≤ D) (hρ : 1 ≤ ρ)
    (x t : ℝ)
    (hambient : ∀ (kind : CurvatureTensorKind) (j : ℕ), j ≤ m + 1 →
      Real.sqrt (normSq0S (G.metric t) (c.lift x t) (kind.arity + j)
        (kind.field G j t (c.lift x t))) ≤ C)
    (hjets : ∀ j ≤ m, Real.sqrt (c.normSq G.metric
      (c.iteratedDs G.metric j (c.unitTangent G.metric)) x t) ≤ D * ρ ^ j)
    (A : CurvatureContraction) (hA : A.Admissible (m + 3) (m + 2) (m + 1)) :
    let N := fun j => Real.sqrt (c.normSq G.metric
      (c.iteratedDs G.metric j (c.unitTangent G.metric)) x t)
    |A.eval c G W x t| ≤ C * D ^ (m + 4) *
      (ρ ^ (m + 3) + ρ ^ 2 * N (m + 1) + ρ * N (m + 2)) * Real.sqrt (c.normSq G.metric W x t) := by
  classical
  let Z := fun j => c.iteratedDs G.metric j (c.unitTangent G.metric) x t
  let N := fun j => Real.sqrt ((G.metric t).inner (c.lift x t) (Z j) (Z j))
  let NW := Real.sqrt (c.normSq G.metric W x t)
  let F := ρ ^ (m + 3) + ρ ^ 2 * N (m + 1) + ρ * N (m + 2)
  have hN (j : ℕ) : 0 ≤ N j := Real.sqrt_nonneg _
  have hNW : 0 ≤ NW := Real.sqrt_nonneg _
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hρ0 : 0 ≤ ρ := zero_le_one.trans hρ
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hprod (r : ℕ) (S : Finset (Fin r)) (v : Fin r → ℕ)
      (hw : (∑ i ∈ S, v i) ≤ m + 3) (hv : ∀ i ∈ S, v i ≤ m + 2)
      (hcard : S.card ≤ m + 4) : (∏ i ∈ S, N (v i)) ≤ D ^ (m + 4) * F := by
    have hh := prod_le_of_weight_sum_lt_two_mul S v N hD hρ hN
      (n := m + 1) (w := m + 3) (fun j hj => hjets j (by omega)) hw (by omega) hv
    have h2 : m + 3 - (m + 1) = 2 := by omega
    have h1 : m + 3 - (m + 1 + 1) = 1 := by omega
    rw [h2, h1, pow_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hD hcard) hF)
  change |A.eval c G W x t| ≤ C * D ^ (m + 4) * F * NW
  cases A with
  | inner i j k =>
    rcases hA with ⟨hw, hi, hj, hk⟩
    have hp : N i * N j * N k ≤ D ^ (m + 4) * F := by
      simpa [Fin.prod_univ_three] using hprod 3 Finset.univ ![i, j, k]
        (by simpa [Fin.sum_univ_three] using hw)
        (by simpa [Fin.forall_fin_succ] using And.intro hi (And.intro hj hk)) (by simp)
    have hab := abs_inner_le_sqrt_mul_sqrt (G.metric t) (c.lift x t) (Z i) (Z j)
    have hkw := abs_inner_le_sqrt_mul_sqrt (G.metric t) (c.lift x t) (Z k) (W x t)
    have hraw : |CurvatureContraction.eval c G W (.inner i j k) x t| ≤ (N i * N j * N k) * NW := by
      change |(G.metric t).inner (c.lift x t) (Z i) (Z j) *
        (G.metric t).inner (c.lift x t) (Z k) (W x t)| ≤ _
      rw [abs_mul]
      exact (mul_le_mul hab hkw (abs_nonneg _) (mul_nonneg (hN i) (hN j))).trans_eq (by dsimp only [N, NW, CurveMap.normSq]; ring)
    refine hraw.trans ((mul_le_mul_of_nonneg_right hp hNW).trans ?_)
    have hc := mul_le_mul_of_nonneg_right hC (mul_nonneg (mul_nonneg (pow_nonneg hD0 (m + 4)) hF) hNW)
    simpa only [one_mul, mul_assoc] using hc
  | ricci j v k =>
    rcases hA with ⟨hw, hv, hk, hj⟩
    have hp := hprod (2 + j + 1) Finset.univ (Fin.cons k v)
      (by simpa [Fin.sum_univ_succ, add_comm] using hw)
      (by intro i _; exact Fin.cases hk (fun i => hv i) i)
      (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
    rw [Fin.prod_univ_succ] at hp
    simp only [Fin.cons_zero, Fin.cons_succ] at hp
    have hab := abs_apply_le_norm0S (G.metric t) (c.lift x t) (2 + j)
      (CurvatureTensorKind.ricci.field G j t (c.lift x t)) (fun i => Z (v i))
    have htensor : |CurvatureTensorKind.ricci.field G j t (c.lift x t) (fun i => Z (v i))| ≤
        C * ∏ i, N (v i) :=
      hab.trans (mul_le_mul_of_nonneg_right (hambient .ricci j hj) (Finset.prod_nonneg (fun i _ => hN (v i))))
    have hkw := abs_inner_le_sqrt_mul_sqrt (G.metric t) (c.lift x t) (Z k) (W x t)
    have hraw : |CurvatureContraction.eval c G W (.ricci j v k) x t| ≤
        C * (N k * ∏ i, N (v i)) * NW := by
      change |CurvatureTensorKind.ricci.field G j t (c.lift x t) (fun i => Z (v i)) *
        (G.metric t).inner (c.lift x t) (Z k) (W x t)| ≤ _
      rw [abs_mul]
      exact (mul_le_mul htensor hkw (abs_nonneg _) (mul_nonneg hC0 (Finset.prod_nonneg (fun i _ => hN (v i))))).trans_eq (by dsimp only [N, NW, CurveMap.normSq]; ring)
    refine hraw.trans ?_
    calc
      _ ≤ C * (D ^ (m + 4) * F) * NW :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC0) hNW
      _ = _ := by ring
  | tensor kind j p v =>
    rcases hA with ⟨hw, hv, hj⟩
    have hp := hprod (kind.arity + j) (Finset.univ.erase p) v hw
      (fun i hi => hv i (Finset.ne_of_mem_erase hi)) (by
        rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin]
        cases kind <;> dsimp only [CurvatureTensorKind.arity] <;> omega)
    have hab := abs_apply_le_norm0S (G.metric t) (c.lift x t) (kind.arity + j)
      (kind.field G j t (c.lift x t)) (Function.update (fun i => Z (v i)) p (W x t))
    have hvals : (fun i => Real.sqrt ((G.metric t).inner (c.lift x t)
        (Function.update (fun i => Z (v i)) p (W x t) i)
        (Function.update (fun i => Z (v i)) p (W x t) i))) = Function.update (fun i => N (v i)) p NW := by
      funext i
      by_cases hip : i = p
      · subst i; simp only [Function.update_self]; rfl
      · simp only [Function.update_of_ne hip]; rfl
    rw [hvals, Finset.prod_update_of_mem (Finset.mem_univ p), Finset.sdiff_singleton_eq_erase] at hab
    have hraw : |CurvatureContraction.eval c G W (.tensor kind j p v) x t| ≤
        C * (NW * ∏ i ∈ Finset.univ.erase p, N (v i)) :=
      hab.trans (mul_le_mul_of_nonneg_right (hambient kind j hj)
        (mul_nonneg hNW (Finset.prod_nonneg fun i _ => hN (v i))))
    refine hraw.trans ?_
    calc
      _ ≤ C * (NW * (D ^ (m + 4) * F)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hNW) hC0
      _ = _ := by ring

def curvatureForcingConstant (m : ℕ) (C D : ℝ) : ℝ :=
  (1 + ((curvatureForcingExpansion m).map (fun z => |z.1|)).sum) * C * D ^ (m + 4)

theorem le_curvatureForcingConstant (m : ℕ) {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D) :
    C ≤ curvatureForcingConstant m C D := by
  have hsum : 0 ≤ ((curvatureForcingExpansion m).map (fun z => |z.1|)).sum := by
    apply List.sum_nonneg
    intro z hz
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
    exact abs_nonneg _
  have hfirst : C ≤ (1 + ((curvatureForcingExpansion m).map (fun z => |z.1|)).sum) * C := by
    nlinarith only [mul_nonneg hsum hC]
  exact hfirst.trans (le_mul_of_one_le_right (hC.trans hfirst) (one_le_pow₀ hD))

variable [CompleteSpace E] [SigmaCompactSpace M] [I.Boundaryless]
    {J : RealTimeInterval} {a b s u : ℝ}

theorem CurveMap.curvature_forcing_abs_le_of_lower_derivative_bounds
    (B : RicciBackground (I := I) (M := M) J a b) (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    {m : ℕ} (hm : 2 ≤ m) {C D ρ : ℝ} (hC : 1 ≤ C) (hD : 1 ≤ D) (hρ : 1 ≤ ρ)
    (W : c.Field (I := I)) (hW : W.SmoothOn (I := I) (Icc s u)) (x t : ℝ) (ht : t ∈ Icc s u)
    (hambient : ∀ (kind : CurvatureTensorKind) (j : ℕ), j ≤ m + 1 →
      Real.sqrt (normSq0S (B.family.metric t) (c.lift x t) (kind.arity + j)
        (kind.field B.family j t (c.lift x t))) ≤ C)
    (hjets : ∀ j < m, Real.sqrt (c.normSq B.family.metric
      (c.iteratedDs B.family.metric j (c.curvatureVector B.family.metric)) x t) ≤ D * ρ ^ (j + 1)) :
    let g := B.family.metric
    let V := fun j => c.iteratedDs g j (c.curvatureVector g)
    |(g t).inner (c.lift x t) (c.Dt g (Icc s u) (V m) x t - V (m + 2) x t) (W x t)| ≤
      curvatureForcingConstant m C D *
        (ρ ^ (m + 3) + ρ ^ 2 * Real.sqrt (c.normSq g (V m) x t) +
          ρ * Real.sqrt (c.normSq g (V (m + 1)) x t)) * Real.sqrt (c.normSq g W x t) := by
  let g := B.family.metric
  let V := fun j => c.iteratedDs g j (c.curvatureVector g)
  let F := ρ ^ (m + 3) + ρ ^ 2 * Real.sqrt (c.normSq g (V m) x t) +
    ρ * Real.sqrt (c.normSq g (V (m + 1)) x t)
  let Y := C * D ^ (m + 4) * F * Real.sqrt (c.normSq g W x t)
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hρ0 : 0 ≤ ρ := zero_le_one.trans hρ
  have hY : 0 ≤ Y := by dsimp only [Y, F]; positivity
  have hZ (j : ℕ) (hj : j ≤ m) : Real.sqrt (c.normSq g
      (c.iteratedDs g j (c.unitTangent g)) x t) ≤ D * ρ ^ j := by
    cases j with
    | zero =>
      change Real.sqrt ((g t).inner (c.lift x t) (c.unitTangent g x t) (c.unitTangent g x t)) ≤ D * ρ ^ 0
      rw [(tangent_curvature_geometry g c (Icc s u) hc.smooth hc.immersed x t ht).1, Real.sqrt_one, pow_zero, mul_one]
      exact hD
    | succ j =>
      rw [c.iteratedDs_unitTangent_succ]
      exact hjets j (by omega)
  have hbound (A : CurvatureContraction) (hA : A.Admissible (m + 3) (m + 2) (m + 1)) :
      |A.eval c B.family W x t| ≤ Y := by
    have hh := A.abs_eval_le_of_lower_derivative_bounds c B.family W hm hC hD hρ x t hambient hZ hA
    dsimp only at hh
    rw [c.iteratedDs_unitTangent_succ g m, c.iteratedDs_unitTangent_succ g (m + 1)] at hh
    exact hh
  have hsum (L : List (ℝ × CurvatureContraction))
      (hL : ∀ z ∈ L, z.2.Admissible (m + 3) (m + 2) (m + 1)) :
      |CurvatureContraction.evalExpansion c B.family W L x t| ≤ (L.map (fun z => |z.1|)).sum * Y := by
    induction L with
    | nil => simp [CurvatureContraction.evalExpansion]
    | cons z L ih =>
      simp only [CurvatureContraction.evalExpansion, List.map_cons, List.sum_cons]
      have hz : |z.1 * z.2.eval c B.family W x t| ≤ |z.1| * Y := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hbound z.2 (hL z List.mem_cons_self)) (abs_nonneg _)
      exact (abs_add_le _ _).trans ((add_le_add hz
        (ih (fun v hv => hL v (List.mem_cons_of_mem z hv)))).trans_eq (by ring))
  have hfull := hsum (curvatureForcingExpansion m) (curvature_forcing_expansion_admissible m)
  have hforce := c.curvature_forcing_eq_expansion B hsu hwindow hc m W hW x t ht
  dsimp only
  rw [hforce]
  refine hfull.trans ?_
  change _ ≤ curvatureForcingConstant m C D * F * Real.sqrt (c.normSq g W x t)
  dsimp only [curvatureForcingConstant, Y] at *
  nlinarith only [hY]

theorem CurveMap.iteratedDs_curvature_evolution_le_of_lower_derivative_bounds
    (B : RicciBackground (I := I) (M := M) J a b) (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    {m : ℕ} (hm : 2 ≤ m) {C D ρ : ℝ} (hC : 1 ≤ C) (hD : 1 ≤ D) (hρ : 1 ≤ ρ)
    (x t : ℝ) (ht : t ∈ Icc s u)
    (hambient : ∀ (kind : CurvatureTensorKind) (j : ℕ), j ≤ m + 1 →
      Real.sqrt (normSq0S (B.family.metric t) (c.lift x t) (kind.arity + j)
        (kind.field B.family j t (c.lift x t))) ≤ C)
    (hjets : ∀ j < m, Real.sqrt (c.normSq B.family.metric
      (c.iteratedDs B.family.metric j (c.curvatureVector B.family.metric)) x t) ≤ D * ρ ^ (j + 1)) :
    let g := B.family.metric
    let V := fun j => c.iteratedDs g j (c.curvatureVector g)
    let K := curvatureForcingConstant m C D
    derivWithin (c.normSq g (V m) x) (Icc s u) t - c.ds g (c.ds g (c.normSq g (V m))) x t ≤
      -c.normSq g (V (m + 1)) x t + (2 * K ^ 2 + 2 * K + 2 * C) * ρ ^ 2 * c.normSq g (V m) x t +
      (ρ ^ 2) ^ (m + 2) := by
  let g := B.family.metric
  let V := fun j => c.iteratedDs g j (c.curvatureVector g)
  let K := curvatureForcingConstant m C D
  let z := Real.sqrt (c.normSq g (V m) x t)
  let w := Real.sqrt (c.normSq g (V (m + 1)) x t)
  have hz2 : z ^ 2 = c.normSq g (V m) x t := Real.sq_sqrt (c.normSq_nonneg g (V m) x t)
  have hw2 : w ^ 2 = c.normSq g (V (m + 1)) x t := Real.sq_sqrt (c.normSq_nonneg g (V (m + 1)) x t)
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hJ : Icc s u ⊆ J.regular := fun τ hτ => B.regular (hwindow hτ)
  have hH := Field.smoothOn_curvatureVector g B.smooth hJ (uniqueDiffOn_Icc hsu) c hc.smooth hc.immersed
  have hV : (V m).SmoothOn (I := I) (Icc s u) :=
    Field.smoothOn_iteratedDs g B.smooth hJ (uniqueDiffOn_Icc hsu) c hc.smooth hc.immersed (c.curvatureVector g) hH m
  have hevol := c.normSq_evolution B hsu hwindow hc.smooth hc.immersed (V m) hV x t ht
  have hsucc (j : ℕ) : c.Ds g (V j) = V (j + 1) := by
    simp only [V, CurveMap.iteratedDs, Function.iterate_succ_apply']
  dsimp only [g] at hsucc
  simp_rw [hsucc] at hevol
  have hforce := c.curvature_forcing_abs_le_of_lower_derivative_bounds B hsu hwindow hc hm hC hD hρ
    (V m) hV x t ht hambient hjets
  have hforceU := (le_abs_self _).trans hforce
  change (g t).inner (c.lift x t) (c.Dt g (Icc s u) (V m) x t - V (m + 2) x t) (V m x t) ≤
    K * (ρ ^ (m + 3) + ρ ^ 2 * z + ρ * w) * z at hforceU
  have hRic : -(C * z ^ 2) ≤ B.family.ricciAt t (c.lift x t) (vec2 (V m x t) (V m x t)) := by
    have hb := abs_apply_le_norm0S (g t) (c.lift x t) 2
      (B.family.ricciAt t (c.lift x t)) (vec2 (V m x t) (V m x t))
    have hRic0 := hambient CurvatureTensorKind.ricci 0 (by omega)
    change Real.sqrt (normSq0S (g t) (c.lift x t) 2 (B.family.ricciAt t (c.lift x t))) ≤ C at hRic0
    have hh := hb.trans (mul_le_mul_of_nonneg_right hRic0 (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _))
    have hsq : (∏ i : Fin 2, Real.sqrt ((g t).inner (c.lift x t)
        (vec2 (V m x t) (V m x t) i) (vec2 (V m x t) (V m x t) i))) = z ^ 2 := by
      simp only [Fin.prod_univ_two, vec2, ite_self]
      change z * z = z ^ 2
      ring
    rw [hsq] at hh
    exact (abs_le.mp hh).1
  have hp : ρ ^ (m + 3) = ρ * ρ ^ (m + 2) := by rw [pow_succ]; ring
  have hp2 : (ρ ^ 2) ^ (m + 2) = (ρ ^ (m + 2)) ^ 2 := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  have hρ2 : 1 ≤ ρ ^ 2 := one_le_pow₀ hρ
  have hRicρ : 2 * C * z ^ 2 ≤ 2 * C * ρ ^ 2 * z ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hρ2 (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC0) (sq_nonneg z))
    nlinarith only [hh]
  dsimp only
  rw [hevol, ← hz2, ← hw2, hp2]
  rw [hp] at hforceU
  nlinarith only [hforceU, hRic, hRicρ, sq_nonneg (w - K * ρ * z), sq_nonneg (ρ ^ (m + 2) - K * ρ * z)]

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
