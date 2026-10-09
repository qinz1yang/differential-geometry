import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.SplittingFrame

/-!
# Consumers of the LFR11 kernels and of tier T1

* `contDiffOn_id_of_connection_bootstrap`: kernel K1 on the identity map (`A = 0`, `B = 0`);
* `fst_eq_affine_of_line`: kernel K4 on a lifted line `s ↦ (a + s u, y)`;
* `splitting_regularZero_input`: the exact input of tier T2's regular-zero atlas
  (`C^{K+1}` coordinate with surjective differential), for actual complete finite metrics;
* `contMDiff_real_splitting_fst`: the rank-one case `F = ℝ` used by LFR16–LFR18.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set WithLp
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.ExactSplitting

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

/-- Kernel K1 on the identity map: `D² id = 0` gives `C^{m+2}` (consumer). -/
theorem contDiffOn_id_of_connection_bootstrap {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (m : ℕ) :
    ContDiffOn ℝ ((m + 2 : ℕ) : WithTop ℕ∞) (fun z : V => z) univ := by
  refine DifferentialGeometry.Analysis.contDiffOn_of_fderiv_fderiv_eq isOpen_univ
    contDiff_id.contDiffOn (mapsTo_univ _ _) (A := fun _ => 0) (B := fun _ => 0)
    contDiffOn_const contDiffOn_const ?_
  intro z _ v w
  have h : fderiv ℝ (fun z : V => z) = fun _ => ContinuousLinearMap.id ℝ V := by
    funext y
    exact fderiv_fun_id (𝕜 := ℝ)
  rw [h, fderiv_fun_const]
  simp

/-- Kernel K4 on a lifted line in an `ℓ²` product (consumer). -/
theorem fst_eq_affine_of_line {F Y : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MetricSpace Y] (a u : F) (hu : ‖u‖ = 1) (y : Y) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (toLp 2 (a + s • u, y) : WithLp 2 (F × Y)).fst =
      (toLp 2 (a + (0 : ℝ) • u, y) : WithLp 2 (F × Y)).fst +
        ((s - 0) / (1 - 0)) • ((toLp 2 (a + (1 : ℝ) • u, y) : WithLp 2 (F × Y)).fst -
          (toLp 2 (a + (0 : ℝ) • u, y) : WithLp 2 (F × Y)).fst) := by
  refine GC.MetricGeometry.fst_eq_affine_of_dist_eq_mul (c := fun s => toLp 2 (a + s • u, y))
    (lam := 1) one_pos (fun s _ s' _ => ?_) hs
  have h := (WithLp.isometry_prodMk_right (E := F) y).dist_eq (a + s • u) (a + s' • u)
  rw [h, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, hu, mul_one,
    Real.norm_eq_abs, one_mul]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] {r : ℕ∞} {Y : Type*} [MetricSpace Y]

/-- The input of tier T2's regular-zero atlas for an exact splitting (consumer of T1.a, T1.b). -/
theorem splitting_regularZero_input {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    ContMDiff I 𝓘(ℝ, F) ((r : ℕ∞ω) + 2) (fun x => (e x).fst) ∧
      ∀ x, (e x).fst = 0 → Function.Surjective (mvfderiv I (fun x => (e x).fst) x) :=
  ⟨contMDiff_splitting_fst g hr hnorm e,
    fun x _ => mvfderiv_splitting_fst_surjective g hr hnorm e x⟩

/-- The rank-one case `F = ℝ` (LFR16–LFR18): the real coordinate is `C^{K+1}` (consumer). -/
theorem contMDiff_real_splitting_fst
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (ℝ × Y)) :
    ContMDiff I 𝓘(ℝ, ℝ) ((r : ℕ∞ω) + 2) (fun x => (e x).fst) :=
  contMDiff_splitting_fst g hr hnorm e

end DifferentialGeometry.Geometry.ExactSplitting
