import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.CoordinateLines
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.SpeedBound

/-!
# LFR11, tier T1 (T1.c, first part): `dt` is `1`-Lipschitz and line vectors are unique

Blueprint LFR11 (A:25566–25672), second paragraph: `t` is `1`-Lipschitz, so `‖dt_x(w)‖ ≤ |w|_g`
(`norm_mvfderiv_splitting_fst_le`). Equality in Cauchy–Schwarz then makes a `g_x`-unit vector
with `dt_x(w) = u`, `‖u‖ = 1`, unique (`eq_of_mvfderiv_splitting_fst_eq`). Consequently the
initial vector of a lifted coordinate line does not depend on the length of the segment, and the
line is `s ↦ exp_x(s w)` for ALL `s ≥ 0` (`exists_unit_line_expMap_forall`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric WithLp
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.ExactSplitting

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]
  {r : ℕ∞} {F Y : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace Y]

/-- **LFR11 S3.** The differential of the splitting coordinate is `1`-Lipschitz for `g_x`. -/
theorem norm_mvfderiv_splitting_fst_le
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (x : M) (w : E) :
    ‖mvfderiv I (fun x => (e x).fst) x w‖ ≤ Real.sqrt (g.inner x w w) := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : ∀ s : ℝ, ((⟨x, w⟩ : TangentBundle I M), s) ∈ g.geodesicFlowDomain := by
    rw [g.geodesicFlowDomain_eq_univ hr hnorm]
    exact fun _ => mem_univ _
  have hγ := g.hasMFDerivAt_geodesicFlow_proj hr1 (hD 0)
  rw [g.geodesicFlow_zero hr1] at hγ
  have h0 : (g.geodesicFlow (⟨x, w⟩ : TangentBundle I M) 0).proj = x := by
    rw [g.geodesicFlow_zero hr1]
  have htd : MDifferentiableAt I 𝓘(ℝ, F) (fun x => (e x).fst)
      (g.geodesicFlow (⟨x, w⟩ : TangentBundle I M) 0).proj := by
    rw [h0]
    exact ((contMDiff_splitting_fst g hr hnorm e) x).mdifferentiableAt (by simp)
  have hder0 := TauCeti.Manifold.hasDerivAt_comp_curve htd hγ
  have hder : HasDerivAt ((fun x => (e x).fst) ∘
      (fun s => (g.geodesicFlow (⟨x, w⟩ : TangentBundle I M) s).proj))
      (mvfderiv I (fun x => (e x).fst) x w) 0 := by
    rw [h0] at hder0
    exact hder0
  have hsq : 0 ≤ Real.sqrt (g.inner x w w) := Real.sqrt_nonneg _
  have hlip : LipschitzWith (Real.toNNReal (Real.sqrt (g.inner x w w)))
      ((fun x => (e x).fst) ∘
        (fun s => (g.geodesicFlow (⟨x, w⟩ : TangentBundle I M) s).proj)) := by
    apply LipschitzWith.of_dist_le_mul
    intro s s'
    simp only [Function.comp_apply]
    calc dist (e (g.geodesicFlow (⟨x, w⟩ : TangentBundle I M) s).proj).fst
          (e (g.geodesicFlow (⟨x, w⟩ : TangentBundle I M) s').proj).fst
        ≤ dist (e (g.geodesicFlow (⟨x, w⟩ : TangentBundle I M) s).proj)
            (e (g.geodesicFlow (⟨x, w⟩ : TangentBundle I M) s').proj) :=
          WithLp.dist_fst_le _ _
      _ = dist (g.geodesicFlow (⟨x, w⟩ : TangentBundle I M) s).proj
            (g.geodesicFlow (⟨x, w⟩ : TangentBundle I M) s').proj := e.dist_eq _ _
      _ ≤ Real.sqrt (g.inner x w w) * |s' - s| :=
          g.dist_proj_geodesicFlow_le hr1 hnorm (fun τ _ => hD τ)
      _ = (Real.toNNReal (Real.sqrt (g.inner x w w)) : ℝ) * dist s s' := by
          rw [Real.coe_toNNReal _ hsq, Real.dist_eq, abs_sub_comm]
  have h := hder.le_of_lipschitz hlip
  rwa [Real.coe_toNNReal _ hsq] at h

/-- **LFR11 S4 (uniqueness).** Two `g_x`-unit vectors with the same unit differential agree. -/
theorem eq_of_mvfderiv_splitting_fst_eq
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (x : M) {w₁ w₂ : E} {u : F} (hu : ‖u‖ = 1)
    (h₁ : g.inner x w₁ w₁ = 1) (h₂ : g.inner x w₂ w₂ = 1)
    (hd₁ : mvfderiv I (fun x => (e x).fst) x w₁ = u)
    (hd₂ : mvfderiv I (fun x => (e x).fst) x w₂ = u) : w₁ = w₂ := by
  set W₁ : TangentSpace I x := w₁
  set W₂ : TangentSpace I x := w₂
  have hsum : mvfderiv I (fun x => (e x).fst) x (W₁ + W₂) = (2 : ℝ) • u := by
    rw [map_add]
    change mvfderiv I (fun x => (e x).fst) x w₁ + mvfderiv I (fun x => (e x).fst) x w₂ = _
    rw [hd₁, hd₂, two_smul]
  have hle := norm_mvfderiv_splitting_fst_le g hr hnorm e x (W₁ + W₂)
  rw [hsum, norm_smul, hu, Real.norm_two, mul_one] at hle
  have hsymm : g.inner x W₂ W₁ = g.inner x W₁ W₂ := g.symm x W₂ W₁
  have hexp : g.inner x (W₁ + W₂) (W₁ + W₂) = 2 + 2 * g.inner x W₁ W₂ := by
    simp only [map_add, add_apply]
    change g.inner x w₁ w₁ + g.inner x W₂ W₁ + (g.inner x W₁ W₂ + g.inner x w₂ w₂) = _
    rw [h₁, h₂, hsymm]
    ring
  have h0 : 0 ≤ g.inner x (W₁ + W₂) (W₁ + W₂) := g.inner_self_nonneg' x _
  have h4 : 4 ≤ g.inner x (W₁ + W₂) (W₁ + W₂) := by
    have h1 := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 2) hle
    rw [Real.mul_self_sqrt h0] at h1
    linarith
  have hdiff : g.inner x (W₁ - W₂) (W₁ - W₂) = 2 - 2 * g.inner x W₁ W₂ := by
    simp only [map_sub, sub_apply]
    change g.inner x w₁ w₁ - g.inner x W₂ W₁ - (g.inner x W₁ W₂ - g.inner x w₂ w₂) = _
    rw [h₁, h₂, hsymm]
    ring
  by_contra hne
  have hne' : W₁ - W₂ ≠ 0 := sub_ne_zero.mpr hne
  have hpos := g.pos x (W₁ - W₂) hne'
  rw [hexp] at h4
  linarith

/-- **LFR11 T1.c (lines for all times).** For a unit direction `u`, there is a `g_x`-unit vector
`w` with `dt_x(w) = u` and `exp_x(s w) = e⁻¹((e x).fst + s u, (e x).snd)` for all `s ≥ 0`. -/
theorem exists_unit_line_expMap_forall [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (x : M) {u : F} (hu : ‖u‖ = 1) :
    ∃ w : E, g.inner x w w = 1 ∧ mvfderiv I (fun x => (e x).fst) x w = u ∧ ∀ s : ℝ, 0 ≤ s →
      g.expMap (⟨x, s • w⟩ : TangentBundle I M) =
        e.symm (toLp 2 ((e x).fst + s • u, (e x).snd)) := by
  obtain ⟨w, hw1, hw⟩ := exists_unit_line_expMap g hr hnorm e x hu 1
  have hdw := mvfderiv_splitting_fst_of_line g hr hnorm e x one_pos hw
  refine ⟨w, hw1, hdw, fun s hs => ?_⟩
  obtain ⟨w', hw'1, hw'⟩ := exists_unit_line_expMap g hr hnorm e x hu (s + 1)
  have hdw' := mvfderiv_splitting_fst_of_line g hr hnorm e x (by linarith) hw'
  have heq : w' = w := eq_of_mvfderiv_splitting_fst_eq g hr hnorm e x hu hw'1 hw1 hdw' hdw
  rw [← heq]
  exact hw' s ⟨hs, by linarith⟩

end DifferentialGeometry.Geometry.ExactSplitting
