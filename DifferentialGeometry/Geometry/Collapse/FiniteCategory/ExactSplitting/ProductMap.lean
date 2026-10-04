import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.SplittingFrameRegularity
import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.SplittingFrameExamples
import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.SplittingFactor
import DifferentialGeometry.Geometry.Metric.Isometry.FiniteRegularity
import DifferentialGeometry.Geometry.Metric.Distance.FiniteDifferential

/-!
# The actual finite-order splitting product map

The original splitting isometry defines the whole map. Its exponential formula uses the
actual linear frame and the same zero-fibre atlas, without choosing another metric splitting.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter WithLp
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.ExactSplitting

variable {M F Y : Type*} [MetricSpace M] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MetricSpace Y]

def splittingProductMap (e : M ≃ᵢ WithLp 2 (F × Y))
    (p : F × {x : M // (e x).fst = 0}) : M :=
  e.symm (toLp 2 (p.1, (e p.2.val).snd))

def splittingProductEquiv (e : M ≃ᵢ WithLp 2 (F × Y)) :
    (F × {x : M // (e x).fst = 0}) ≃ M :=
  (WithLp.equiv 2 _).symm.trans (splittingFactorProductEquiv e).toEquiv


omit [InnerProductSpace ℝ F] in
theorem splittingProductEquiv_symm_fst (e : M ≃ᵢ WithLp 2 (F × Y)) (x : M) :
    ((splittingProductEquiv e).symm x).1 = (e x).fst := rfl

omit [InnerProductSpace ℝ F] in
theorem splittingProductEquiv_symm_val (e : M ≃ᵢ WithLp 2 (F × Y)) (x : M) :
    ((splittingProductEquiv e).symm x).2.val = e.symm (toLp 2 (0, (e x).snd)) := rfl

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
   [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] {r : ℕ∞}
  [FiniteDimensional ℝ F] [NeZero (Module.finrank ℝ E)]


theorem splittingProductMap_eq_expMap
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (u : F) (z : {x : M // (e x).fst = 0}) :
    splittingProductMap e (u, z) =
      g.expMap (⟨z.val, splittingFrame g e z.val u⟩ : TangentBundle I M) := by
  have h := expMap_splittingFrame g hr hnorm e z.val u 1
  rw [one_smul, z.property, zero_add, one_smul] at h
  exact h.symm

theorem contMDiff_splittingProductMap
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    ContMDiff (𝓘(ℝ, F).prod 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ))
      I r (splittingProductMap e) := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let Z := {x : M // (e x).fst = 0}
  let IZ := 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ)
  have hval : ContMDiff IZ I r (Subtype.val : Z → M) :=
    (contMDiff_splittingFactor_val g hr hnorm e).of_le le_self_add
  have harg : ContMDiff ((𝓘(ℝ, F)).prod IZ) ((𝓘(ℝ, F)).prod I) r
      (fun p : F × Z => (p.1, p.2.val)) :=
    contMDiff_fst.prodMk (hval.comp contMDiff_snd)
  have hframe := ((contMDiff_splittingFrame_apply g hr hnorm e).of_le le_self_add).comp harg
  have hexp : ContMDiff I.tangent I r g.expMap := by
    intro v
    have hv : v ∈ g.expDomain := by
      change (v, (1 : ℝ)) ∈ g.geodesicFlowDomain
      rw [g.geodesicFlowDomain_eq_univ hr hnorm]
      exact mem_univ _
    exact (g.contMDiffOn_expMap (one_le_two.trans hr)).contMDiffAt
      ((g.isOpen_expDomain (one_le_two.trans hr)).mem_nhds hv)
  apply (hexp.comp hframe).congr
  intro p
  exact splittingProductMap_eq_expMap g hr hnorm e p.1 p.2

theorem splittingProductEquiv_symm_val_eq_expMap
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (x : M) :
    ((splittingProductEquiv e).symm x).2.val =
      g.expMap (⟨x, -splittingFrame g e x (e x).fst⟩ : TangentBundle I M) := by
  have h := expMap_splittingFrame g hr hnorm e x (e x).fst (-1)
  rw [neg_one_smul, neg_one_smul, add_neg_cancel] at h
  exact h.symm

theorem contMDiff_splittingProductEquiv_symm
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    ContMDiff I (𝓘(ℝ, F).prod 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ))
      r (splittingProductEquiv e).symm := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let IZ := 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ)
  let Z := {x : M // (e x).fst = 0}
  let gamma : M → M := fun x => g.expMap
    (⟨x, -splittingFrame g e x (e x).fst⟩ : TangentBundle I M)
  have ht : ContMDiff I 𝓘(ℝ, F) r (fun x => (e x).fst) :=
    (contMDiff_splitting_fst g hr hnorm e).of_le le_self_add
  have ha : ContMDiff I ((𝓘(ℝ, F)).prod I) r
      (fun x => (-(e x).fst, x)) := ht.neg.prodMk contMDiff_id
  have hf := ((contMDiff_splittingFrame_apply g hr hnorm e).of_le le_self_add).comp ha
  have hexp : ContMDiff I.tangent I r g.expMap := by
    intro v
    have hv : v ∈ g.expDomain := by
      change (v, (1 : ℝ)) ∈ g.geodesicFlowDomain
      rw [g.geodesicFlowDomain_eq_univ hr hnorm]
      exact mem_univ _
    exact (g.contMDiffOn_expMap (one_le_two.trans hr)).contMDiffAt
      ((g.isOpen_expDomain (one_le_two.trans hr)).mem_nhds hv)
  have hgamma : ContMDiff I I r gamma := by
    apply (hexp.comp hf).congr
    intro x
    simp only [Function.comp_apply, map_neg]
    rfl
  have hg : ∀ x, gamma x = ((splittingProductEquiv e).symm x).2.val :=
    fun x => (splittingProductEquiv_symm_val_eq_expMap g hr hnorm e x).symm
  have hz : ∀ x, (e (gamma x)).fst = 0 := by
    intro x
    rw [hg x]
    exact ((splittingProductEquiv e).symm x).2.property
  let : IsManifold I ((r : ℕ∞ω) + 2) M := IsManifold.of_le (n := ∞) (by
    simpa only [← WithTop.coe_ofNat, ← WithTop.coe_add, WithTop.coe_le_coe] using
      (show r + 2 ≤ (⊤ : ℕ∞) from le_top))
  have hl : ContMDiff I IZ r (fun x => (⟨gamma x, hz x⟩ : Z)) :=
    DifferentialGeometry.Manifold.RegularZero.contMDiff_manifold_lift_of_le le_self_add
      (by simp) (fun x => (e x).fst) (splitting_regularZero_input g hr hnorm e).1
      (splitting_regularZero_input g hr hnorm e).2 gamma hgamma hz
  apply (ht.prodMk hl).congr
  intro x
  apply Prod.ext
  · exact splittingProductEquiv_symm_fst e x
  · apply Subtype.ext
    exact (hg x).symm

def splittingProductInitialDiffeomorph
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    Diffeomorph (𝓘(ℝ, F).prod 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ))
      I (F × {x : M // (e x).fst = 0}) M r := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  exact { toEquiv := splittingProductEquiv e
          contMDiff_toFun := contMDiff_splittingProductMap g hr hnorm e
          contMDiff_invFun := contMDiff_splittingProductEquiv_symm g hr hnorm e }

private theorem realProduct_enorm : ∀ (x : ℝ) (w : TangentSpace 𝓘(ℝ, ℝ) x),
    ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (realFrameMetric.inner x w w)) := by
  intro x w
  change ‖(w : ℝ)‖ₑ = ENNReal.ofReal (Real.sqrt (inner ℝ (w : ℝ) w))
  rw [← norm_eq_sqrt_real_inner, ← ofReal_norm]

local instance realProductDimension : NeZero (Module.finrank ℝ ℝ) :=
  ⟨by rw [Module.finrank_self]; decide⟩

def realProductInitialDiffeomorph :=
  splittingProductInitialDiffeomorph (r := 2) realFrameMetric le_rfl realProduct_enorm
    realFrameSplitting

end DifferentialGeometry.Geometry.ExactSplitting
