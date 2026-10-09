import DifferentialGeometry.Topology.Manifold.RegularZero.ManifoldTangent
import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.Applications
import DifferentialGeometry.Geometry.Metric.Pullback.FiniteOrder
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Geometry.Metric.L2Product

/-!
# The regular-zero factor of an exact metric splitting

The zero fibre keeps its actual subtype metric and receives the finite regular-zero atlas.
The metric is the actual pullback by the inclusion, with one derivative of regularity lost.
-/

set_option autoImplicit false
noncomputable section
open Bundle Set Filter Manifold WithLp
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Geometry.ExactSplitting

variable {M F Y : Type*} [MetricSpace M] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MetricSpace Y]

def splittingFactorEquiv (e : M ≃ᵢ WithLp 2 (F × Y)) :
    Y ≃ᵢ {x : M // (e x).fst = 0} := e.l2ProductSlice 0

omit [InnerProductSpace ℝ F] in
theorem splittingFactorEquiv_apply (e : M ≃ᵢ WithLp 2 (F × Y)) (y : Y) :
    (splittingFactorEquiv e y).val = e.symm (toLp 2 (0, y)) := rfl

omit [InnerProductSpace ℝ F] in
theorem completeSpace_splittingFactor [CompleteSpace M]
    (e : M ≃ᵢ WithLp 2 (F × Y)) : CompleteSpace {x : M // (e x).fst = 0} :=
  (e.isClosed_l2ProductSlice 0).completeSpace_coe

omit [InnerProductSpace ℝ F] in
theorem connectedSpace_splittingFactor [ConnectedSpace M]
    (e : M ≃ᵢ WithLp 2 (F × Y)) : ConnectedSpace {x : M // (e x).fst = 0} := by
  let : ConnectedSpace (WithLp 2 (F × Y)) :=
    e.surjective.connectedSpace e.continuous
  have hY : ConnectedSpace Y :=
    (show Function.Surjective (fun p : WithLp 2 (F × Y) => p.snd) from
      fun y => ⟨toLp 2 (0, y), rfl⟩).connectedSpace (WithLp.continuous_snd 2 F Y)
  let _ := hY
  exact (splittingFactorEquiv e).surjective.connectedSpace (splittingFactorEquiv e).continuous

def splittingFactorProductEquiv (e : M ≃ᵢ WithLp 2 (F × Y)) :
    WithLp 2 (F × {x : M // (e x).fst = 0}) ≃ᵢ M :=
  ((IsometryEquiv.refl F).withLpProdCongr (p := 2) (splittingFactorEquiv e).symm).trans e.symm

omit [InnerProductSpace ℝ F] in
theorem splittingFactorProductEquiv_apply (e : M ≃ᵢ WithLp 2 (F × Y))
    (p : WithLp 2 (F × {x : M // (e x).fst = 0})) :
    splittingFactorProductEquiv e p = e.symm (toLp 2 (p.fst, (e p.snd.val).snd)) := rfl

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [FiniteDimensional ℝ F] [NeZero (Module.finrank ℝ E)] {r : ℕ∞}

open DifferentialGeometry.Manifold.RegularZero

@[instance_reducible]
def splittingFactorChartedSpace
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    ChartedSpace (Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ)
      {x : M // (e x).fst = 0} := by
  let : IsManifold I ((r : ℕ∞ω) + 2) M := IsManifold.of_le (n := ∞) (by
    simpa only [← WithTop.coe_ofNat, ← WithTop.coe_add, WithTop.coe_le_coe] using
      (show r + 2 ≤ (⊤ : ℕ∞) from le_top))
  exact manifoldChartedSpace (by simp) (fun x => (e x).fst)
    (splitting_regularZero_input g hr hnorm e).1
    (splitting_regularZero_input g hr hnorm e).2

theorem splittingFactor_isManifold
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ)
      ((r : ℕ∞ω) + 2) {x : M // (e x).fst = 0} := by
  let : IsManifold I ((r : ℕ∞ω) + 2) M := IsManifold.of_le (n := ∞) (by
    simpa only [← WithTop.coe_ofNat, ← WithTop.coe_add, WithTop.coe_le_coe] using
      (show r + 2 ≤ (⊤ : ℕ∞) from le_top))
  exact manifold_isManifold (by simp) (fun x => (e x).fst)
    (splitting_regularZero_input g hr hnorm e).1
    (splitting_regularZero_input g hr hnorm e).2

theorem contMDiff_splittingFactor_val
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) I ((r : ℕ∞ω) + 2)
      (Subtype.val : {x : M // (e x).fst = 0} → M) := by
  let : IsManifold I ((r : ℕ∞ω) + 2) M := IsManifold.of_le (n := ∞) (by
    simpa only [← WithTop.coe_ofNat, ← WithTop.coe_add, WithTop.coe_le_coe] using
      (show r + 2 ≤ (⊤ : ℕ∞) from le_top))
  exact contMDiff_manifold_val (by simp) (fun x => (e x).fst)
    (splitting_regularZero_input g hr hnorm e).1
    (splitting_regularZero_input g hr hnorm e).2

theorem splittingFactor_isManifold_one
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ)
      1 {x : M // (e x).fst = 0} := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let _ := splittingFactor_isManifold g hr hnorm e
  exact IsManifold.of_le (n := (r : ℕ∞ω) + 2) (by
    simpa only [← WithTop.coe_ofNat, ← WithTop.coe_one, ← WithTop.coe_add,
      WithTop.coe_le_coe] using
      (show (1 : ℕ∞) ≤ r + 2 from le_add_of_le_right (by norm_num)))

theorem exists_inducedMetric
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    ∃ h : ContMDiffRiemannianMetric 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ)
      ((r : ℕ∞ω) + 1) (Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ)
      (TangentSpace 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) :
        {x : M // (e x).fst = 0} → Type _),
      ∀ z v w, h.inner z v w = g.inner z.val
        (mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) I
          (Subtype.val : {x : M // (e x).fst = 0} → M) z v)
        (mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) I
          (Subtype.val : {x : M // (e x).fst = 0} → M) z w) := by
  cases r using ENat.recTopCoe with
  | top =>
    have h1 : (∞ : ℕ∞ω) + 1 = ∞ := by norm_cast
    have h2 : (∞ : ℕ∞ω) + 2 = ∞ := by norm_cast
    let : IsManifold I ((∞ : ℕ∞ω) + 2) M :=
      IsManifold.of_le (n := ∞) (by simp)
    let _ := splittingFactorChartedSpace g hr hnorm e
    let _ := splittingFactor_isManifold g hr hnorm e
    let _ := splittingFactor_isManifold_one g hr hnorm e
    have hi := contMDiff_splittingFactor_val g hr hnorm e
    have hinj := fun z => injective_mfderiv_manifold_val (by simp)
      (fun x => (e x).fst) (splitting_regularZero_input g hr hnorm e).1
      (splitting_regularZero_input g hr hnorm e).2 z
    let gt : DifferentialGeometry.SmoothRiemannianMetric I M :=
      { g with contMDiff := by simpa only [h1] using g.contMDiff }
    have hit : ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) I ∞
        (Subtype.val : {x : M // (e x).fst = 0} → M) := by
      simpa only [h2] using hi
    let : IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) ∞
        {x : M // (e x).fst = 0} := by
      simpa only [h2] using splittingFactor_isManifold g hr hnorm e
    let h := gt.pullback (Subtype.val : {x : M // (e x).fst = 0} → M) hit hinj
    refine ⟨{ h with contMDiff := ?_ }, fun z v w => rfl⟩
    simpa only [h1] using h.contMDiff
  | coe n =>
    let : IsManifold I (((n : ℕ∞) : ℕ∞ω) + 2) M :=
      IsManifold.of_le (n := ∞) (by
        simpa only [← WithTop.coe_ofNat, ← WithTop.coe_add, WithTop.coe_le_coe] using
          (show (n : ℕ∞) + 2 ≤ (⊤ : ℕ∞) from le_top))
    let _ := splittingFactorChartedSpace g hr hnorm e
    let _ := splittingFactor_isManifold g hr hnorm e
    let _ := splittingFactor_isManifold_one g hr hnorm e
    have hi := contMDiff_splittingFactor_val g hr hnorm e
    have hinj := fun z => injective_mfderiv_manifold_val (by simp)
      (fun x => (e x).fst) (splitting_regularZero_input g hr hnorm e).1
      (splitting_regularZero_input g hr hnorm e).2 z
    let : IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ)
        (((n + 1 + 1 : ℕ) : ℕ∞ω)) {x : M // (e x).fst = 0} := by
      simpa [add_assoc] using splittingFactor_isManifold g hr hnorm e
    exact exists_finite_order_pullback_metric (n + 1) (n + 2) (n + 1) le_rfl
      (by omega) g (Subtype.val : {x : M // (e x).fst = 0} → M) hi hinj

def inducedMetric
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    ContMDiffRiemannianMetric 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ)
      ((r : ℕ∞ω) + 1) (Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ)
      (TangentSpace 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) :
        {x : M // (e x).fst = 0} → Type _) :=
  (exists_inducedMetric g hr hnorm e).choose

theorem inducedMetric_inner
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    ∀ z v w, (inducedMetric g hr hnorm e).inner z v w = g.inner z.val
      (mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) I
        (Subtype.val : {x : M // (e x).fst = 0} → M) z v)
      (mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) I
        (Subtype.val : {x : M // (e x).fst = 0} → M) z w) :=
  (exists_inducedMetric g hr hnorm e).choose_spec

end DifferentialGeometry.Geometry.ExactSplitting
