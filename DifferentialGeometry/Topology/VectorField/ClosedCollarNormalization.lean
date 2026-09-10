import DifferentialGeometry.Topology.VectorField.CollarNormalization
import DifferentialGeometry.Topology.VectorField.OpenRestriction
import DifferentialGeometry.Topology.Manifold.Interval.Tangent

set_option autoImplicit false
open Set Function Bundle Manifold TopologicalSpace
open scoped ContDiff Topology
noncomputable section
namespace Poincare.VectorField

theorem exists_closedCollarNormalization
    {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    {J : ModelWithCorners ℝ E H} [IsManifold J 1 B]
    {ε η : ℝ} [Fact ((0 : ℝ) < ε)] (hη : 0 < η)
    (a : Icc (0 : ℝ) ε) (ha : 0 < a.val)
    (U : Opens (B × ℝ)) (hU : ∀ q : U, -1 ≤ q.val.2)
    (S : Opens (B × Icc (0 : ℝ) ε))
    (hcore : {q : B × Icc (0 : ℝ) ε | q.2.val ≤ a.val} ⊆ S)
    (W : ∀ q : S, TangentSpace (J.prod (𝓡∂ 1)) q)
    (hW : ContMDiff (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)).tangent ∞
      (fun q => (⟨q, W q⟩ : TangentBundle (J.prod (𝓡∂ 1)) S))) :
    ∃ κ : U → S, ContMDiff (J.prod 𝓘(ℝ, ℝ)) (J.prod (𝓡∂ 1)) ∞ κ ∧
      (∀ q : U, (κ q).val.1 = q.val.1 ∧
        (κ q).val.2.val = -a.val * collarNormalizationTime η q.val.2) ∧
      (∀ q : U, (κ q).val.2.val ≤ a.val) ∧
      ∃ N : ∀ q : U, TangentSpace (J.prod 𝓘(ℝ, ℝ)) q,
        ContMDiff (J.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)).tangent ∞
          (fun q => (⟨q, N q⟩ : TangentBundle (J.prod 𝓘(ℝ, ℝ)) U)) ∧
        (∀ q : U, N q = ((W (κ q)).1,
          -(Poincare.Manifold.Interval.tangentCoordinateIcc (κ q).val.2 (W (κ q)).2) / a.val)) ∧
        ∀ q : U, N q = 0 ↔ W (κ q) = 0 := by
  have htime (q : U) : -a.val * collarNormalizationTime η q.val.2 ∈ Icc (0 : ℝ) a.val := by
    by_cases hq : q.val.2 ≤ 0
    · obtain ⟨hρ0, hρ1⟩ := collarTransition_mem_Icc (1 + q.val.2 / η)
      have hφlo : q.val.2 ≤ collarNormalizationTime η q.val.2 := by
        dsimp [collarNormalizationTime]
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hρ0 hq]
      have hφhi : collarNormalizationTime η q.val.2 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) hq
      have hφ1 : 0 ≤ collarNormalizationTime η q.val.2 + 1 := by linarith [hU q]
      constructor
      · exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr ha.le) hφhi
      · nlinarith [mul_nonneg ha.le hφ1]
    · rw [collarNormalizationTime_eq_zero hη (by linarith)]
      simpa using ha.le
  let κ : U → S := fun q =>
    ⟨(q.val.1, ⟨-a.val * collarNormalizationTime η q.val.2,
      (htime q).1, (htime q).2.trans a.property.2⟩), hcore (htime q).2⟩
  have hκ : ContMDiff (J.prod 𝓘(ℝ, ℝ)) (J.prod (𝓡∂ 1)) ∞ κ := by
    apply (ContMDiff.subtypeVal_comp_iff S κ).mp
    apply ContMDiff.prodMk
    · exact contMDiff_fst.comp contMDiff_subtype_val
    · apply contMDiff_iff_comp_subtypeVal_Icc.mpr
      have hh : ContDiff ℝ ∞ (fun t : ℝ => -a.val * collarNormalizationTime η t) :=
        contDiff_const.mul (contDiff_collarNormalizationTime η)
      exact ⟨(hh.continuous.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _,
        hh.contMDiff.comp (contMDiff_snd.comp contMDiff_subtype_val)⟩
  let N : ∀ q : U, TangentSpace (J.prod 𝓘(ℝ, ℝ)) q := fun q =>
    ((W (κ q)).1, -(Poincare.Manifold.Interval.tangentCoordinateIcc (κ q).val.2 (W (κ q)).2) / a.val)
  have hN : ContMDiff (J.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun q => (⟨q, N q⟩ : TangentBundle (J.prod 𝓘(ℝ, ℝ)) U)) := by
    apply (contMDiff_tangentSection_opens_iff U N).mpr
    have hWa := (contMDiff_tangentSection_opens_iff S W).mp hW
    have hc := contMDiff_equivTangentBundleProd.comp (hWa.comp hκ)
    have hb := Poincare.Manifold.Interval.contMDiff_tangentCoordinateIcc.comp hc.snd
    have hlin : ContDiff ℝ ∞ (fun t : ℝ => -t / a.val) := by fun_prop
    have hnormal := hlin.contMDiff.comp hb
    have hR : ContMDiff (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ).tangent ∞
        (fun q : U => (⟨q.val.2,
          -(Poincare.Manifold.Interval.tangentCoordinateIcc (κ q).val.2 (W (κ q)).2) / a.val⟩ :
            TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
      intro q
      apply Bundle.contMDiffAt_totalSpace.mpr
      refine ⟨(contMDiff_snd.comp contMDiff_subtype_val) q, ?_⟩
      convert hnormal q using 1
      simp only [mfld_simps]
      rfl
    exact contMDiff_equivTangentBundleProd_symm.comp (hc.fst.prodMk hR)
  refine ⟨κ, hκ, (fun _ => ⟨rfl, rfl⟩), (fun q => (htime q).2), N, hN, (fun _ => rfl), ?_⟩
  intro q
  constructor
  · intro hz
    have hT := congrArg Prod.fst hz
    have hb := congrArg Prod.snd hz
    change -(Poincare.Manifold.Interval.tangentCoordinateIcc (κ q).val.2 (W (κ q)).2) / a.val = 0 at hb
    have hc : Poincare.Manifold.Interval.tangentCoordinateIcc (κ q).val.2 (W (κ q)).2 = 0 := by
      exact neg_eq_zero.mp ((div_eq_zero_iff.mp hb).resolve_right ha.ne')
    exact Prod.ext hT ((Poincare.Manifold.Interval.tangentCoordinateIcc (κ q).val.2).map_eq_zero_iff.mp hc)
  · intro hz
    change ((W (κ q)).1, -(Poincare.Manifold.Interval.tangentCoordinateIcc (κ q).val.2 (W (κ q)).2) / a.val) = 0
    rw [hz]
    change ((0 : E), -(Poincare.Manifold.Interval.tangentCoordinateIcc (κ q).val.2
      (0 : TangentSpace (𝓡∂ 1) (κ q).val.2)) / a.val) = ((0 : E), (0 : ℝ))
    rw [map_zero]
    simp

end Poincare.VectorField
