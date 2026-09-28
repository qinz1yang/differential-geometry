import DifferentialGeometry.Geometry.Metric.CurveVariation.Comparison
import DifferentialGeometry.Geometry.Metric.RestrictionDistance
import DifferentialGeometry.Topology.LocalLipschitzVariation

noncomputable section
open Set Filter MeasureTheory Bundle Manifold
open scoped Manifold ContDiff NNReal ENNReal Topology
namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [RegularSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
 theorem riemannianCurveVariation_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) [T2Space U]
    (γ : ℝ → U) (a b : ℝ) (hγ : ContinuousOn γ (Icc a b)) :
    riemannianCurveVariation (g.restrictOpen U) γ a b =
      riemannianCurveVariation g (Subtype.val ∘ γ) a b := by
  classical
  apply le_antisymm
  · let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    let : PseudoEMetricSpace M := .ofRiemannianMetric I M
    let : RiemannianBundle (TangentSpace I : U → Type _) :=
      ⟨(g.restrictOpen U).toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E (TangentSpace I : U → Type _) :=
      ⟨(g.restrictOpen U).inner, (g.restrictOpen U).contMDiff.continuous, fun _ _ _ => rfl⟩
    let : PseudoEMetricSpace U := .ofRiemannianMetric I U
    let : WeakPseudoEMetricSpace U := PseudoEMetricSpace.toWeakPseudoEMetricSpace U
    let f : M → U := fun x => if hx : x ∈ U then ⟨x, hx⟩ else γ a
    have hcomp : f ∘ (Subtype.val ∘ γ) = γ := by
      funext t
      simp [f, (γ t).property]
    have hbound : eVariationOn (f ∘ (Subtype.val ∘ γ)) (Icc a b) ≤
        (1 : ℝ≥0) * eVariationOn (Subtype.val ∘ γ) (Icc a b) := by
      apply DifferentialGeometry.Topology.eVariationOn_comp_le_of_locally_lipschitzOn
        (continuous_subtype_val.comp_continuousOn hγ)
      intro x hx
      obtain ⟨t, ht, rfl⟩ := hx
      obtain ⟨V, hV, hdist⟩ :=
        DifferentialGeometry.Geometry.Metric.exists_mem_nhds_riemannianEDistOf_restrictOpen_eq
          g U (γ t)
      refine ⟨V ∩ (U : Set M), inter_mem hV (U.isOpen.mem_nhds (γ t).property), ?_⟩
      intro y hy z hz
      change riemannianEDistOf (g.restrictOpen U) (f y) (f z) ≤
        (1 : ℝ≥0∞) * riemannianEDistOf g y z
      have heq := hdist ⟨y, hy.2⟩ ⟨z, hz.2⟩ hy.1 hz.1
      dsimp [f]
      have hyU : y ∈ U := hy.2
      have hzU : z ∈ U := hz.2
      rw [dite_eq_left hyU, dite_eq_left hzU, one_mul]
      exact heq.le
    rw [hcomp, ENNReal.coe_one, one_mul] at hbound
    exact hbound
  · have hbound := riemannianCurveVariation_comp_le (g.restrictOpen U) g
      (Subtype.val : U → M) 1
      (fun x y => by simpa only [ENNReal.coe_one, one_mul] using
        riemannianEDistOf_le_restrictOpen g U x y) γ a b
    simpa only [ENNReal.coe_one, one_mul] using hbound

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_restrictOpen_le_of_lipschitz
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) [T2Space U]
    {s : Set ℝ} (hs : s.OrdConnected) {γ : s → U} {C : ℝ≥0}
    (hγ : ∀ x y : s, riemannianEDistOf g (γ x) (γ y) ≤ C * edist x y)
    (a b : s) :
    riemannianEDistOf (g.restrictOpen U) (γ a) (γ b) ≤ C * edist a b := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric I M
  have hLip : LipschitzWith C (fun x : s => (γ x : M)) := hγ
  have hcont : Continuous γ :=
    hLip.continuous.subtype_mk _
  wlog hab : (a : ℝ) ≤ b generalizing a b
  · simpa only [riemannianEDistOf_comm, edist_comm] using
      this b a (le_of_not_ge hab)
  let δ : ℝ → U := fun t => γ ⟨projIcc (a : ℝ) (b : ℝ) hab t,
    hs.out a.property b.property (projIcc (a : ℝ) (b : ℝ) hab t).property⟩
  have hδ : Continuous δ := hcont.comp
    ((continuous_subtype_val.comp continuous_projIcc).subtype_mk _)
  have hδeq (t : ℝ) (ht : t ∈ Icc (a : ℝ) b) :
      δ t = γ ⟨t, hs.out a.property b.property ht⟩ := by
    dsimp [δ]
    apply congrArg γ
    apply Subtype.ext
    exact congrArg (fun z : Icc (a : ℝ) b => (z : ℝ)) (projIcc_of_mem hab ht)
  have hδa : δ a = γ a := hδeq a ⟨le_rfl, hab⟩
  have hδb : δ b = γ b := hδeq b ⟨hab, le_rfl⟩
  have hδLip : LipschitzOnWith C (Subtype.val ∘ δ) (Icc (a : ℝ) b) := by
    intro x hx y hy
    change riemannianEDistOf g (δ x) (δ y) ≤ C * edist x y
    rw [hδeq x hx, hδeq y hy]
    exact hγ _ _
  have hvar := hδLip.comp_eVariationOn_le (mapsTo_id (Icc (a : ℝ) b))
  rw [Function.comp_id, eVariationOn_id_Icc] at hvar
  have hupper := (riemannianEDistOf_le_riemannianCurveVariation
    (g.restrictOpen U) δ hab).trans_eq
    (riemannianCurveVariation_restrictOpen g U δ a b hδ.continuousOn)
  change riemannianEDistOf (g.restrictOpen U) (δ a) (δ b) ≤
    eVariationOn (Subtype.val ∘ δ) (Icc (a : ℝ) b) at hupper
  have he : edist a b = ENNReal.ofReal ((b : ℝ) - a) := by
    rw [Subtype.edist_eq, edist_dist, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hab)]
    congr 1
    ring
  rw [he, ← hδa, ← hδb]
  exact hupper.trans hvar


end DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]

variable [FiniteDimensional ℝ E] [RegularSpace M]

theorem riemannianCurveVariation_le_of_quad_on
    (g h : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) [T2Space U]
    {c : ℝ} (hc : 0 < c)
    (hquad : ∀ x ∈ U, ∀ v : TangentSpace I x,
      h.inner x v v ≤ c * g.inner x v v)
    {γ : ℝ → M} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b)) (hmap : MapsTo γ (Icc a b) U) :
    riemannianCurveVariation h γ a b ≤
      ENNReal.ofReal (Real.sqrt c) * riemannianCurveVariation g γ a b := by
  by_cases hab : a ≤ b
  swap
  · have hz : riemannianCurveVariation h γ a b = 0 := by
      apply le_antisymm _ bot_le
      unfold riemannianCurveVariation
      apply iSup_le
      intro p
      exact False.elim (hab ((p.2.2.2 0).1.trans (p.2.2.2 0).2))
    rw [hz]
    exact bot_le
  let δ : ℝ → U := fun t => ⟨γ (projIcc a b hab t), hmap (projIcc a b hab t).property⟩
  have hδ : Continuous δ :=
    (hγ.domRestrict.subtype_mk (fun t => hmap t.property)).comp continuous_projIcc
  have heq : EqOn (Subtype.val ∘ δ) γ (Icc a b) := by
    intro t ht
    simp only [Function.comp_apply, δ, projIcc_of_mem, ht]
  have hδh := (riemannianCurveVariation_restrictOpen h U δ a b hδ.continuousOn).trans
    (riemannianCurveVariation_congr h heq)
  have hδg := (riemannianCurveVariation_restrictOpen g U δ a b hδ.continuousOn).trans
    (riemannianCurveVariation_congr g heq)
  rw [← hδh, ← hδg]
  let L : ℝ≥0 := ⟨Real.sqrt c, Real.sqrt_nonneg c⟩
  have hL : (L : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt c) := by
    exact (ENNReal.ofReal_coe_nnreal (p := L)).symm
  have hbound := riemannianCurveVariation_comp_le (g.restrictOpen U) (h.restrictOpen U)
    id L (fun x y => ?_) δ a b
  · simpa only [Function.id_comp, hL] using hbound
  · rw [hL]
    apply edistOf_le_of_quad _ _ hc
    intro z v
    exact hquad z z.property v

end DifferentialGeometry.Geometry
