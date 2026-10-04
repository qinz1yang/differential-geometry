import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.FactorCurvature
import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.SplittingFactorDistance

/-!
# LFR11: finite regularity of an exact metric splitting (the row)

Chapter 13, row LFR11 (`thm:collapse-exact-splitting-regularity`). Let `(M, g)` be a complete
Riemannian manifold whose metric `g` is of class `C^{r+1}` (`r ≥ 2`, i.e. `K = r + 1 ≥ 3`) and let
`e : M ≃ᵢ ℓ²(F × Y)` be a surjective distance isometry onto an `ℓ²` product with a Euclidean factor
`F`; no structure on `Y` is assumed. Then, with `t = (e ·).fst` and `Z = t⁻¹(0)`:
* (T) `t` is `C^{K+1}`;
* (Z) `Z` is a `C^{K+1}` manifold (the actual subtype, X96's regular-zero atlas), the inclusion is
  a `C^{K+1}` immersion with image `ker dt`;
* (h) the induced metric `h` is `C^K`, is the pullback of `g` by the inclusion, its Riemannian
  distance is the subtype distance, and `Z` is complete (connected if `M` is);
* (Y) `y ↦ e.symm (0, y)` is an isometry `Y ≃ᵢ Z`;
* (Ψ) the actual product map `Ψ (u, z) = e.symm (u, π_Y e z)` is a `C^{K+1}` diffeomorphism
  `F × Z → M` with `Ψ^* g = du² + h`;
* (sec) `h` has the ambient sectional curvature on its tangent planes, so `sec_g ≥ 0` gives
  `sec_h ≥ 0`.
The orientation clause of the blueprint row is NOT part of this theorem: an orientation of a
manifold with only a `C^{K+1}` atlas is not expressible with the tree's `ManifoldOrientation`
(which carries `IsManifold I ∞`); see build-logs/resume/sheet-F7-LFR11b.md §6.

Tiers: T1 (F7-LFR11), T2 (Codex X96), T3 (Codex X97), T4 curvature (`FactorCurvature`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter WithLp Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.ExactSplitting

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E H M F Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace Y] [NeZero (Module.finrank ℝ E)] {r : ℕ∞}

local notation "P" => Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ
local notation "IZ" => 𝓘(ℝ, P)
local notation "IP" => ModelWithCorners.prod (𝓘(ℝ, F)) IZ

/-- **LFR11 (row).** Finite regularity of an exact metric splitting: clauses (T), (Z), (h),
(Y), (Ψ), (sec) of the module docstring. -/
theorem exactSplitting_regularity
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    -- (T)
    ContMDiff I 𝓘(ℝ, F) ((r : ℕ∞ω) + 2) (fun x => (e x).fst) ∧
    -- (Z)
    IsManifold IZ ((r : ℕ∞ω) + 2) {x : M // (e x).fst = 0} ∧
    ContMDiff IZ I ((r : ℕ∞ω) + 2) (Subtype.val : {x : M // (e x).fst = 0} → M) ∧
    (∀ z : {x : M // (e x).fst = 0},
      Function.Injective (mfderiv IZ I (Subtype.val : {x : M // (e x).fst = 0} → M) z)) ∧
    (∀ z : {x : M // (e x).fst = 0},
      LinearMap.range (mfderiv IZ I (Subtype.val : {x : M // (e x).fst = 0} → M) z).toLinearMap =
        LinearMap.ker (mvfderiv I (fun x => (e x).fst) z.val).toLinearMap) ∧
    -- (h)
    (∀ (z : {x : M // (e x).fst = 0}) (v w : TangentSpace IZ z),
      (inducedMetric g hr hnorm e).inner z v w = g.inner z.val
        (mfderiv IZ I (Subtype.val : {x : M // (e x).fst = 0} → M) z v)
        (mfderiv IZ I (Subtype.val : {x : M // (e x).fst = 0} → M) z w)) ∧
    (letI : RiemannianBundle (TangentSpace IZ : {x : M // (e x).fst = 0} → Type _) :=
      ⟨(inducedMetric g hr hnorm e).toRiemannianMetric⟩
     IsRiemannianManifold IZ {x : M // (e x).fst = 0}) ∧
    CompleteSpace {x : M // (e x).fst = 0} ∧
    (ConnectedSpace M → ConnectedSpace {x : M // (e x).fst = 0}) ∧
    -- (Y)
    (∀ y : Y, (splittingFactorEquiv e y).val = e.symm (toLp 2 (0, y))) ∧
    -- (Ψ)
    ContMDiff IP I ((r : ℕ∞ω) + 2) (splittingProductDiffeomorph g hr hnorm e) ∧
    ContMDiff I IP ((r : ℕ∞ω) + 2) (splittingProductDiffeomorph g hr hnorm e).symm ∧
    (∀ p : F × {x : M // (e x).fst = 0},
      splittingProductDiffeomorph g hr hnorm e p = e.symm (toLp 2 (p.1, (e p.2.val).snd))) ∧
    (∀ (p : F × {x : M // (e x).fst = 0}) (v w : TangentSpace IP p),
      g.inner (splittingProductDiffeomorph g hr hnorm e p)
        (mfderiv IP I (splittingProductDiffeomorph g hr hnorm e) p v)
        (mfderiv IP I (splittingProductDiffeomorph g hr hnorm e) p w) =
      inner ℝ v.1 w.1 + (inducedMetric g hr hnorm e).inner p.2 v.2 w.2) ∧
    -- (sec)
    (∀ (z : {x : M // (e x).fst = 0}) (v w : TangentSpace IZ z),
      (inducedMetric g hr hnorm e).sectionalCurvature z v w =
        g.sectionalCurvature z.val
          (mfderiv IZ I (Subtype.val : {x : M // (e x).fst = 0} → M) z v)
          (mfderiv IZ I (Subtype.val : {x : M // (e x).fst = 0} → M) z w)) ∧
    ((∀ (x : M) (v w : TangentSpace I x), 0 ≤ g.sectionalCurvature x v w) →
      ∀ (z : {x : M // (e x).fst = 0}) (v w : TangentSpace IZ z),
        0 ≤ (inducedMetric g hr hnorm e).sectionalCurvature z v w) := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let _ := splittingFactor_isManifold_one g hr hnorm e
  let _ : IsManifold I ((r : ℕ∞ω) + 2) M := IsManifold.of_le (n := ∞) (by
    simpa only [← WithTop.coe_ofNat, ← WithTop.coe_add, WithTop.coe_le_coe] using
      (show r + 2 ≤ (⊤ : ℕ∞) from le_top))
  have hfun : (splittingProductDiffeomorph g hr hnorm e : F × {x : M // (e x).fst = 0} → M) =
      splittingProductMap e := by
    funext p
    change (splittingProductDiffeomorph g hr hnorm e).toEquiv p = _
    rw [splittingProductDiffeomorph_toEquiv]
    rfl
  refine ⟨contMDiff_splitting_fst g hr hnorm e, splittingFactor_isManifold g hr hnorm e,
    contMDiff_splittingFactor_val g hr hnorm e, fun z => ?_, fun z => ?_,
    inducedMetric_inner g hr hnorm e, isRiemannianManifold_inducedMetric g hr hnorm e,
    completeSpace_splittingFactor e, fun hM => connectedSpace_splittingFactor e,
    splittingFactorEquiv_apply e, (splittingProductDiffeomorph g hr hnorm e).contMDiff,
    (splittingProductDiffeomorph g hr hnorm e).symm.contMDiff, fun p => ?_,
    splittingProductDiffeomorph_metric g hr hnorm e, inducedMetric_sectionalCurvature_eq g hr hnorm e,
    inducedMetric_sectionalCurvature_nonneg g hr hnorm e⟩
  · exact Manifold.RegularZero.injective_mfderiv_manifold_val (by simp) (fun x => (e x).fst)
      (splitting_regularZero_input g hr hnorm e).1 (splitting_regularZero_input g hr hnorm e).2 z
  · exact Manifold.RegularZero.range_mfderiv_manifold_val (by simp) (fun x => (e x).fst)
      (splitting_regularZero_input g hr hnorm e).1 (splitting_regularZero_input g hr hnorm e).2 z
  · rw [hfun]
    rfl

end DifferentialGeometry.Geometry.ExactSplitting
