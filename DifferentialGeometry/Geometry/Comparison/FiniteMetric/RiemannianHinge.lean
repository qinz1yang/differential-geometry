import DifferentialGeometry.Geometry.Exponential.FiniteMetric.RayDistance
import DifferentialGeometry.Geometry.Comparison.FiniteMetric.GlobalComparison
import DifferentialGeometry.Geometry.Comparison.GermDistanceAsymptotic

/-!
# CM5.b: the Euclidean hinge comparison with the Riemannian angle for a finite metric

Lane CM-A2 (successor of CM-A), package CM5 of the D-FOUND design. For a complete
finite-regularity metric `g : C^{r+1}` (`1 ≤ r`) with `sec_g ≥ 0` everywhere, whose length
distance is the ambient distance (`hnorm`), and unit vectors `u, v ∈ T_oM` whose rays realize the
distance at times `a, b`:

  `comparisonAngle a b d(exp_o (a u), exp_o (b v)) ≤ arccos g_o(u, v)`
  (`comparisonAngle_le_arccos_inner_finite`).

Route A of CM-A's handback:
* the arms `t ↦ exp_o (t u)` are isometric segments (`dist_expMap_smul_eq_of_dist_eq`);
* CM-A's `endpointHingeComparison_zero_finite` bounds the comparison angle by the germ angle of the
  arms;
* `germComparisonAngle_expMap_le_arccos`: under the global four-point comparison the germ angle is a
  joint limit `α`, so `d(exp (s u), exp (s v)) / s → √(2 - 2 cos α)`
  (`dist_div_tendsto_of_joint_comparisonAngle`); the first-order bound
  `eventually_dist_expMap_smul_le` gives `≤ |u - v|_{g_o} = √(2 - 2 g_o(u,v))`, whence
  `g_o(u, v) ≤ cos α`.

Deviation from the frozen interface (decided by the lead): `sec ≥ 0` is global; the buffer
`2 (a + b) < R` is dropped; `3 ≤ r` is relaxed to `1 ≤ r`. The frozen form is kept as an `example`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.FiniteComparison

open DifferentialGeometry.Geometry.Comparison.Toponogov

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
/-- **The germ angle of two exponential arms is at most the Riemannian angle**, under the
four-point comparison at curvature `0`. -/
theorem germComparisonAngle_expMap_le_arccos
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hcomp : fourPointComparison 0 (univ : Set M))
    (o : M) (u v : E) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hu : g.inner o u u = 1) (hv : g.inner o v v = 1)
    (hminA : dist o (g.expMap (⟨o, a • u⟩ : TangentBundle I M)) = a)
    (hminB : dist o (g.expMap (⟨o, b • v⟩ : TangentBundle I M)) = b) :
    germComparisonAngle 0 (fun s => g.expMap (⟨o, s • u⟩ : TangentBundle I M))
      (fun t => g.expMap (⟨o, t • v⟩ : TangentBundle I M)) ≤ Real.arccos (g.inner o u v) := by
  obtain ⟨hγrad, hγmin⟩ := g.dist_expMap_smul_eq_of_dist_eq hr hnorm hu hminA
  obtain ⟨hβrad, hβmin⟩ := g.dist_expMap_smul_eq_of_dist_eq hr hnorm hv hminB
  set γ : ℝ → M := fun s => g.expMap (⟨o, s • u⟩ : TangentBundle I M) with hγ
  set β : ℝ → M := fun t => g.expMap (⟨o, t • v⟩ : TangentBundle I M) with hβ
  have hjoint := tendsto_limitingComparisonAngle_of_fourPointComparison le_rfl ha hb hcomp
    (mem_univ o) (γ := γ) (β := β)
    (fun s hs => hγrad s (Ioc_subset_Icc_self hs)) (fun t ht => hβrad t (Ioc_subset_Icc_self ht))
    (fun s hs t ht => hγmin s (Ioc_subset_Icc_self hs) t (Ioc_subset_Icc_self ht))
    (fun s hs t ht => hβmin s (Ioc_subset_Icc_self hs) t (Ioc_subset_Icc_self ht))
    (fun _ _ => mem_univ _) (fun _ _ => mem_univ _)
  have hα := limitingComparisonAngle_mem_Icc (κ := 0) γ β ha hb
  set α := limitingComparisonAngle 0 a b γ β with hα_def
  rw [germComparisonAngle_eq_of_tendsto hjoint]
  have hlim := dist_div_tendsto_of_joint_comparisonAngle le_rfl ha hb o γ β
    (fun s hs => hγrad s (Ioc_subset_Icc_self hs)) (fun t ht => hβrad t (Ioc_subset_Icc_self ht))
    hjoint one_pos one_pos
  have hle : Real.sqrt (1 ^ 2 + 1 ^ 2 - 2 * 1 * 1 * Real.cos α) ≤
      Real.sqrt (g.inner o (u - v) (u - v)) := by
    refine le_of_forall_pos_le_add fun ε hε => le_of_tendsto hlim ?_
    filter_upwards [g.eventually_dist_expMap_smul_le hr hnorm o u v hε, self_mem_nhdsWithin]
      with t ht htpos
    have ht' : dist (γ t) (β t) ≤ t * (Real.sqrt (g.inner o (u - v) (u - v)) + ε) := ht
    simp only [one_mul]
    rw [div_le_iff₀ (show (0 : ℝ) < t from htpos)]
    linarith
  have key : ∀ x y : TangentSpace I o, g.inner o (x - y) (x - y) =
      g.inner o x x - 2 * g.inner o x y + g.inner o y y := by
    intro x y
    simp only [map_sub, sub_apply]
    rw [g.symm o y x]
    ring
  have hexp : g.inner o (u - v) (u - v) = 2 - 2 * g.inner o u v := by
    have h := key u v
    rw [hu, hv] at h
    exact h.trans (by ring)
  have hnn : 0 ≤ g.inner o (u - v) (u - v) :=
    DifferentialGeometry.Geometry.Collapse.finite_inner_self_nonneg g o (u - v)
  rw [Real.sqrt_le_sqrt_iff hnn, hexp] at hle
  have hcos : g.inner o u v ≤ Real.cos α := by nlinarith
  calc α = Real.arccos (Real.cos α) := (Real.arccos_cos hα.1 hα.2).symm
    _ ≤ Real.arccos (g.inner o u v) := Real.arccos_le_arccos hcos

/-- **CM5.b, Euclidean hinge comparison with the Riemannian angle** for a complete
finite-regularity metric with `sec ≥ 0` (global form). -/
theorem comparisonAngle_le_arccos_inner_finite
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (o : M) (u v : E) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hu : g.inner o u u = 1) (hv : g.inner o v v = 1)
    (hminA : dist o (g.expMap (⟨o, a • u⟩ : TangentBundle I M)) = a)
    (hminB : dist o (g.expMap (⟨o, b • v⟩ : TangentBundle I M)) = b)
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂) :
    comparisonAngle a b (dist (g.expMap (⟨o, a • u⟩ : TangentBundle I M))
      (g.expMap (⟨o, b • v⟩ : TangentBundle I M))) ≤ Real.arccos (g.inner o u v) := by
  have hn : (2 : ℕ∞ω) ≤ (r : ℕ∞ω) + 1 := by
    have h1 : ((1 : ℕ∞) : ℕ∞ω) ≤ (r : ℕ∞ω) := by exact_mod_cast hr
    calc (2 : ℕ∞ω) = 1 + 1 := by norm_num
      _ ≤ (r : ℕ∞ω) + 1 := by gcongr; simpa using h1
  obtain ⟨hγrad, hγmin⟩ := g.dist_expMap_smul_eq_of_dist_eq hr hnorm hu hminA
  obtain ⟨hβrad, hβmin⟩ := g.dist_expMap_smul_eq_of_dist_eq hr hnorm hv hminB
  have hhinge := endpointHingeComparison_zero_finite g hn hnorm hsec
    (g.expMap (⟨o, a • u⟩ : TangentBundle I M)) (a + b + 1) o a b
    (fun s => g.expMap (⟨o, s • u⟩ : TangentBundle I M))
    (fun t => g.expMap (⟨o, t • v⟩ : TangentBundle I M)) ha hb (by linarith) rfl
    (fun s hs => hγrad s (Ioc_subset_Icc_self hs)) (fun t ht => hβrad t (Ioc_subset_Icc_self ht))
    (fun s hs t ht => hγmin s (Ioc_subset_Icc_self hs) t (Ioc_subset_Icc_self ht))
    (fun s hs t ht => hβmin s (Ioc_subset_Icc_self hs) t (Ioc_subset_Icc_self ht))
  rw [comparisonAngleNegCurvature_zero] at hhinge
  exact hhinge.trans (germComparisonAngle_expMap_le_arccos g hr hnorm
    (fourPointComparison_zero_univ_finite g hn hnorm hsec) o u v ha hb hu hv hminA hminB)

/-- The frozen interface of CM5.b (`3 ≤ r`, the buffer `2 (a + b) < R`), with the curvature
hypothesis in the global form decided by the lead (every consumer has global `sec ≥ 0`). -/
example
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (o : M) (u v : E) {a b R : ℝ} (ha : 0 < a) (hb : 0 < b) (_hR : 2 * (a + b) < R)
    (hu : g.inner o u u = 1) (hv : g.inner o v v = 1)
    (hminA : dist o (g.expMap (⟨o, a • u⟩ : TangentBundle I M)) = a)
    (hminB : dist o (g.expMap (⟨o, b • v⟩ : TangentBundle I M)) = b)
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂) :
    comparisonAngle a b (dist (g.expMap (⟨o, a • u⟩ : TangentBundle I M))
      (g.expMap (⟨o, b • v⟩ : TangentBundle I M))) ≤ Real.arccos (g.inner o u v) :=
  comparisonAngle_le_arccos_inner_finite g (le_trans (by norm_num) hr) hnorm o u v ha hb hu hv
    hminA hminB hsec

end DifferentialGeometry.Geometry.FiniteComparison
