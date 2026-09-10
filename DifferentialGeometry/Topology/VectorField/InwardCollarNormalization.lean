import DifferentialGeometry.Topology.VectorField.ClosedCollarNormalization
import DifferentialGeometry.Topology.Manifold.Interval.TangentLift

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold TopologicalSpace
open scoped ContDiff Topology
namespace Poincare.VectorField


def inwardNormalizationTime (η r : ℝ) : ℝ := -collarNormalizationTime η (-r)


theorem inwardNormalizationTime_mem_Icc (η : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    inwardNormalizationTime η r ∈ Icc 0 r := by
  obtain ⟨h0, h1⟩ := collarTransition_mem_Icc (1 + -r / η)
  dsimp [inwardNormalizationTime, collarNormalizationTime]
  constructor <;> nlinarith [mul_nonneg hr h0, mul_nonneg hr (sub_nonneg.mpr h1)]


theorem contDiff_inwardNormalizationTime (η : ℝ) : ContDiff ℝ ∞ (inwardNormalizationTime η) :=
  ((contDiff_collarNormalizationTime η).comp contDiff_neg).neg


theorem inwardNormalizationTime_eq_zero {η r : ℝ} (hη : 0 < η) (hr : r ≤ η / 3) :
    inwardNormalizationTime η r = 0 := by
  rw [inwardNormalizationTime, collarNormalizationTime_eq_zero hη (by linarith), neg_zero]


theorem inwardNormalizationTime_eq_self {η r : ℝ} (hη : 0 < η) (hr : 2 * η / 3 ≤ r) :
    inwardNormalizationTime η r = r := by
  rw [inwardNormalizationTime, collarNormalizationTime_eq_self hη (by linarith), neg_neg]

theorem exists_inward_closedCollarNormalization
    {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    {J : ModelWithCorners ℝ E H} [IsManifold J 1 B]
    {ε δ η : ℝ} [Fact ((0 : ℝ) < ε)] (hη : 0 < η)
    (W : ∀ q : (⟨{q : B × Icc (0 : ℝ) ε | q.2.val < δ},
      isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const⟩ : Opens (B × Icc (0 : ℝ) ε)),
      TangentSpace (J.prod (𝓡∂ 1)) q)
    (hW : ContMDiff (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)).tangent ∞
      (fun q => (⟨q, W q⟩ : TangentBundle (J.prod (𝓡∂ 1)) _))) :
    let S : Opens (B × Icc (0 : ℝ) ε) :=
      ⟨{q | q.2.val < δ}, isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const⟩
    ∃ κ : S → S, ContMDiff (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)) ∞ κ ∧
      (∀ q : S, (κ q).val.1 = q.val.1 ∧
        (κ q).val.2.val = inwardNormalizationTime η q.val.2.val) ∧
      ∃ N : ∀ q : S, TangentSpace (J.prod (𝓡∂ 1)) q,
        ContMDiff (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)).tangent ∞
          (fun q => (⟨q, N q⟩ : TangentBundle (J.prod (𝓡∂ 1)) S)) ∧
        (∀ q : S, N q = ((W (κ q)).1, (Poincare.Manifold.Interval.tangentCoordinateIcc q.val.2).symm
          (Poincare.Manifold.Interval.tangentCoordinateIcc (κ q).val.2 (W (κ q)).2))) ∧
        (∀ q : S, N q = 0 ↔ W (κ q) = 0) ∧
        (∀ q : S, 2 * η / 3 ≤ q.val.2.val → N q = W q) ∧
        ∀ q : S, q.val.2.val ≤ η / 3 →
          (κ q).val = (q.val.1, ⟨0, ⟨le_rfl, (Fact.out : (0 : ℝ) < ε).le⟩⟩) := by
  intro S
  let κ : S → S := fun q =>
    ⟨(q.val.1, ⟨inwardNormalizationTime η q.val.2.val,
      (inwardNormalizationTime_mem_Icc η q.val.2.property.1).1,
      (inwardNormalizationTime_mem_Icc η q.val.2.property.1).2.trans q.val.2.property.2⟩),
      (inwardNormalizationTime_mem_Icc η q.val.2.property.1).2.trans_lt q.property⟩
  have hκ : ContMDiff (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)) ∞ κ := by
    apply (ContMDiff.subtypeVal_comp_iff S κ).mp
    apply ContMDiff.prodMk
    · exact contMDiff_fst.comp contMDiff_subtype_val
    · apply contMDiff_iff_comp_subtypeVal_Icc.mpr
      have hh := (contDiff_inwardNormalizationTime η).contMDiff.comp
        (contMDiff_subtypeVal_Icc.comp ((contMDiff_snd (I := J) (J := 𝓡∂ 1)).comp
          (contMDiff_subtype_val (I := J.prod (𝓡∂ 1)) (U := S))))
      exact ⟨hh.continuous.subtype_mk _, hh⟩
  let N : ∀ q : S, TangentSpace (J.prod (𝓡∂ 1)) q := fun q =>
    ((W (κ q)).1, (Poincare.Manifold.Interval.tangentCoordinateIcc q.val.2).symm
      (Poincare.Manifold.Interval.tangentCoordinateIcc (κ q).val.2 (W (κ q)).2))
  have hN : ContMDiff (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)).tangent ∞
      (fun q => (⟨q, N q⟩ : TangentBundle (J.prod (𝓡∂ 1)) S)) := by
    apply (contMDiff_tangentSection_opens_iff S N).mpr
    have hc := contMDiff_equivTangentBundleProd.comp
      (((contMDiff_tangentSection_opens_iff S W).mp hW).comp hκ)
    have hb := Poincare.Manifold.Interval.contMDiff_tangentCoordinateIcc.comp hc.snd
    have hR := Poincare.Manifold.Interval.contMDiff_tangentCoordinateIcc_symm.comp
      ((contMDiff_snd.comp (contMDiff_subtype_val (U := S))).prodMk hb)
    exact contMDiff_equivTangentBundleProd_symm.comp (hc.fst.prodMk hR)
  refine ⟨κ, hκ, fun _ => ⟨rfl, rfl⟩, N, hN, fun _ => rfl, ?_, ?_, ?_⟩
  · intro q
    change ((W (κ q)).1, (Poincare.Manifold.Interval.tangentCoordinateIcc q.val.2).symm
      (Poincare.Manifold.Interval.tangentCoordinateIcc (κ q).val.2 (W (κ q)).2)) = 0 ↔ _
    rw [Prod.mk_eq_zero]
    have he : (Poincare.Manifold.Interval.tangentCoordinateIcc q.val.2).symm
        (Poincare.Manifold.Interval.tangentCoordinateIcc (κ q).val.2 (W (κ q)).2) = 0 ↔
        (W (κ q)).2 = 0 :=
      ((Poincare.Manifold.Interval.tangentCoordinateIcc q.val.2).symm.map_eq_zero_iff).trans
        (Poincare.Manifold.Interval.tangentCoordinateIcc (κ q).val.2).map_eq_zero_iff
    exact (and_congr_right (fun _ => he)).trans Prod.mk_eq_zero.symm
  · intro q hq
    have he : κ q = q := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact Subtype.ext (inwardNormalizationTime_eq_self hη hq)
    change ((W (κ q)).1, (Poincare.Manifold.Interval.tangentCoordinateIcc q.val.2).symm
      (Poincare.Manifold.Interval.tangentCoordinateIcc (κ q).val.2 (W (κ q)).2)) = W q
    rw [he]
    exact Prod.ext rfl ((Poincare.Manifold.Interval.tangentCoordinateIcc q.val.2).symm_apply_apply _)
  · intro q hq
    exact Prod.ext rfl (Subtype.ext (inwardNormalizationTime_eq_zero hη hq))

end Poincare.VectorField
