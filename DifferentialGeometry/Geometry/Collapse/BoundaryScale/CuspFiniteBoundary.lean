import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspFinitePatch
import DifferentialGeometry.Geometry.Curvature.ContinuousEvaluation
import DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.Riemannian
import DifferentialGeometry.Topology.Manifold.InteriorBoundary
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import DifferentialGeometry.Bundle.Section

/-!
# Finite cusp curvature estimates extend to height zero

The original cusp embedding has a continuous bundled derivative on its actual domain.
Dense intrinsic interior and continuous tensor evaluation extend the interior inequality.
-/

set_option autoImplicit false

noncomputable section

open Bundle DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint Set TopologicalSpace
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

universe u

theorem cusp_metricRm04StandardAt_near_model_boundary (C : ℝ) (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ) (δ : ℝ) (X : Set W.Carrier)
    (hK : 2 ≤ K) (e : CuspEmbedding W g K δ X)
    (hint : ∀ p : CuspHalfSpace, p ∈ cuspDomain → 0 < p.2.val 0 →
      ∀ v w : TangentSpace halfCollarModel p,
        |metricRm04StandardAt g (e.toFun p) (mfderiv halfCollarModel W.model e.toFun p v)
            (mfderiv halfCollarModel W.model e.toFun p w)
            (mfderiv halfCollarModel W.model e.toFun p w)
            (mfderiv halfCollarModel W.model e.toFun p v) +
          (1 / 4 : ℝ) * (e.cusp.metric.inner p v v * e.cusp.metric.inner p w w -
            (e.cusp.metric.inner p v w) ^ 2)| ≤
        C * δ * e.cusp.metric.inner p v v * e.cusp.metric.inner p w w)
    (p : CuspHalfSpace) (hp : p ∈ cuspDomain) (v w : TangentSpace halfCollarModel p) :
    |metricRm04StandardAt g (e.toFun p) (mfderiv halfCollarModel W.model e.toFun p v)
        (mfderiv halfCollarModel W.model e.toFun p w)
        (mfderiv halfCollarModel W.model e.toFun p w)
        (mfderiv halfCollarModel W.model e.toFun p v) +
      (1 / 4 : ℝ) * (e.cusp.metric.inner p v v * e.cusp.metric.inner p w w -
        (e.cusp.metric.inner p v w) ^ 2)| ≤
    C * δ * e.cusp.metric.inner p v v * e.cusp.metric.inner p w w := by
  let U : Opens CuspHalfSpace := ⟨cuspDomain, isOpen_cuspDomain⟩
  let : T2Space (EuclideanHalfSpace 1) := by
    unfold EuclideanHalfSpace
    infer_instance
  let : T2Space U := inferInstance
  let p₀ : U := ⟨p, hp⟩
  let f : U → W.Carrier := fun q => e.toFun q.val
  have hf : ContMDiff halfCollarModel W.model (K + 1) f := by
    intro q
    rw [contMDiffAt_subtype_iff]
    exact e.contMDiffOn.contMDiffAt (isOpen_cuspDomain.mem_nhds q.property)
  obtain ⟨V, hV⟩ := ContMDiffSection.exists_eq_at (I := halfCollarModel)
    (F := (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
      EuclideanSpace ℝ (Fin 1)) (V := (TangentSpace halfCollarModel : U → Type _))
    (n := (⊤ : ℕ∞)) p₀ v
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := halfCollarModel)
    (F := (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
      EuclideanSpace ℝ (Fin 1)) (V := (TangentSpace halfCollarModel : U → Type _))
    (n := (⊤ : ℕ∞)) p₀ w
  let v' := fun q : U => mfderiv halfCollarModel W.model f q (V q)
  let w' := fun q : U => mfderiv halfCollarModel W.model f q (Y q)
  have hT := hf.continuous_tangentMap (by
    exact_mod_cast Nat.le_succ_of_le ((by norm_num : 1 ≤ 2).trans hK))
  have hv' : Continuous (fun q : U => (⟨f q, v' q⟩ : TangentBundle W.model W.Carrier)) :=
    hT.comp V.contMDiff.continuous
  have hw' : Continuous (fun q : U => (⟨f q, w' q⟩ : TangentBundle W.model W.Carrier)) :=
    hT.comp Y.contMDiff.continuous
  have hR := continuous_sectional_contraction g f hf.continuous v' w' hv' hw'
  let G := e.cusp.metric.restrictOpen U
  have hVV := TangentBundle.continuous_g_inner_of_smooth_sections G V V
  have hYY := TangentBundle.continuous_g_inner_of_smooth_sections G Y Y
  have hVY := TangentBundle.continuous_g_inner_of_smooth_sections G V Y
  let S : Set U := {q | |metricRm04StandardAt g (f q) (v' q) (w' q) (w' q) (v' q) +
      (1 / 4 : ℝ) * (G.inner q (V q) (V q) * G.inner q (Y q) (Y q) -
        (G.inner q (V q) (Y q)) ^ 2)| ≤
      C * δ * G.inner q (V q) (V q) * G.inner q (Y q) (Y q)}
  have hS : IsClosed S := isClosed_le
    ((hR.add (continuous_const.mul ((hVV.mul hYY).sub (hVY.pow 2)))).abs)
    (((continuous_const.mul hVV).mul hYY))
  have hsub : halfCollarModel.interior U ⊆ S := by
    intro q hq
    have hq' : halfCollarModel.IsInteriorPoint (q : CuspHalfSpace) :=
      halfCollarModel.isInteriorPoint_iff_isInteriorPoint_val.mp hq
    change (q : CuspHalfSpace) ∈ halfCollarModel.interior CuspHalfSpace at hq'
    rw [ModelWithCorners.interior_prod] at hq'
    have hz := hq'.2
    change extChartAt (𝓡∂ 1) q.val.2 q.val.2 ∈ interior (range (𝓡∂ 1)) at hz
    rw [interior_range_modelWithCornersEuclideanHalfSpace] at hz
    have h := hint q.val q.property (by simpa using hz) (V q) (Y q)
    have hderiv := mfderiv_restrict_open (I := halfCollarModel) (J := W.model) e.toFun U q
    change mfderiv halfCollarModel W.model f q = _ at hderiv
    simp only [S, Set.mem_ofPred_eq, v', w', G]
    rw [hderiv]
    exact h
  have hpS : p₀ ∈ S := by
    have heq := (ModelWithCorners.dense_interior halfCollarModel (M := U)).closure_eq
    exact closure_minimal hsub hS (by rw [heq]; exact Set.mem_univ p₀)
  have hderiv := mfderiv_restrict_open (I := halfCollarModel) (J := W.model) e.toFun U p₀
  change mfderiv halfCollarModel W.model f p₀ = _ at hderiv
  simp only [S, Set.mem_ofPred_eq, v', w', G] at hpS
  rw [hderiv, hV, hY] at hpS
  exact hpS

end DifferentialGeometry.Geometry.Collapse
