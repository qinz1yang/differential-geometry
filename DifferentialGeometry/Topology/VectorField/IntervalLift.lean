import DifferentialGeometry.Topology.Manifold.Interval.TangentLift
import DifferentialGeometry.Topology.VectorField.OpenRestriction

set_option autoImplicit false
open Set Function Bundle Manifold TopologicalSpace
open scoped ContDiff Topology
noncomputable section
namespace DifferentialGeometry.VectorField

theorem mpullback_intervalInclusion
    {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    {J : ModelWithCorners ℝ E H} [IsManifold J 1 B]
    {a b : ℝ} [Fact (a < b)]
    (U : Opens (B × ℝ)) (S : Opens (B × Icc a b))
    (hSU : ∀ q : S, (q.val.1, q.val.2.val) ∈ U)
    (W : ∀ q : U, TangentSpace (J.prod 𝓘(ℝ, ℝ)) q)
    (hW : ContMDiff (J.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun q => (⟨q, W q⟩ : TangentBundle (J.prod 𝓘(ℝ, ℝ)) U))) :
    let κ : S → U := fun q => ⟨(q.val.1, q.val.2.val), hSU q⟩
    let V := _root_.VectorField.mpullback (J.prod (𝓡∂ 1)) (J.prod 𝓘(ℝ, ℝ)) κ W
    ContMDiff (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)).tangent ∞
      (fun q => (⟨q, V q⟩ : TangentBundle (J.prod (𝓡∂ 1)) S)) ∧
      (∀ q : S, V q = ((W (κ q)).1,
        (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc q.val.2).symm (W (κ q)).2)) ∧
      (∀ q : S, mfderiv (J.prod (𝓡∂ 1)) (J.prod 𝓘(ℝ, ℝ)) κ q (V q) = W (κ q)) ∧
      ∀ q : S, V q = 0 ↔ W (κ q) = 0 := by
  intro κ V
  have hκ : ContMDiff (J.prod (𝓡∂ 1)) (J.prod 𝓘(ℝ, ℝ)) ∞ κ := by
    apply (ContMDiff.subtypeVal_comp_iff U κ).mp
    exact (contMDiff_id.prodMap contMDiff_subtypeVal_Icc).comp contMDiff_subtype_val
  let L (q : S) : TangentSpace (J.prod (𝓡∂ 1)) q ≃L[ℝ]
      TangentSpace (J.prod 𝓘(ℝ, ℝ)) (κ q) :=
    (ContinuousLinearEquiv.refl ℝ (TangentSpace J q.val.1)).prodCongr
      ((DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc q.val.2).trans
        (NormedSpace.fromTangentSpace q.val.2.val).symm)
  have hderiv (q : S) : mfderiv (J.prod (𝓡∂ 1)) (J.prod 𝓘(ℝ, ℝ)) κ q = (L q).toContinuousLinearMap := by
    have hh := mfderiv_comp q
      ((contMDiff_subtype_val (I := J.prod 𝓘(ℝ, ℝ)) (U := U) (n := ∞)).mdifferentiableAt (by simp))
      (hκ.mdifferentiableAt (by simp))
    rw [DifferentialGeometry.mfderiv_subtype_val] at hh
    have hinc : (Subtype.val : U → B × ℝ) ∘ κ =
        (Prod.map id (Subtype.val : Icc a b → ℝ)) ∘ (Subtype.val : S → B × Icc a b) := rfl
    rw [hinc, mfderiv_comp _
      ((mdifferentiableAt_id).prodMap' ((contMDiff_subtypeVal_Icc (n := ∞)).mdifferentiableAt (by simp)))
      ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp)), DifferentialGeometry.mfderiv_subtype_val,
      mfderiv_prodMap mdifferentiableAt_id ((contMDiff_subtypeVal_Icc (n := ∞)).mdifferentiableAt (by simp)),
      mfderiv_id] at hh
    ext v
    have hhv := congrArg (fun A => A v) hh
    exact hhv.symm
  have hformula (q : S) : V q = ((W (κ q)).1,
      (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc q.val.2).symm (W (κ q)).2) := by
    change (mfderiv (J.prod (𝓡∂ 1)) (J.prod 𝓘(ℝ, ℝ)) κ q).inverse (W (κ q)) = _
    rw [hderiv, ContinuousLinearMap.inverse_equiv]
    rfl
  have hVs : ContMDiff (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)).tangent ∞
      (fun q => (⟨q, V q⟩ : TangentBundle (J.prod (𝓡∂ 1)) S)) := by
    apply (contMDiff_tangentSection_opens_iff S V).mpr
    have hc := contMDiff_equivTangentBundleProd.comp
      (((contMDiff_tangentSection_opens_iff U W).mp hW).comp hκ)
    have hb := (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).comp hc.snd
    have hR := DifferentialGeometry.Manifold.Interval.contMDiff_tangentCoordinateIcc_symm.comp
      ((contMDiff_snd.comp (contMDiff_subtype_val (U := S))).prodMk hb)
    exact (contMDiff_equivTangentBundleProd_symm.comp (hc.fst.prodMk hR)).congr (fun q =>
      congrArg (fun v : TangentSpace (J.prod (𝓡∂ 1)) q.val =>
        (⟨q.val, v⟩ : TangentBundle (J.prod (𝓡∂ 1)) (B × Icc a b))) (hformula q))
  refine ⟨hVs, hformula, ?_, ?_⟩
  · intro q
    change mfderiv (J.prod (𝓡∂ 1)) (J.prod 𝓘(ℝ, ℝ)) κ q
      ((mfderiv (J.prod (𝓡∂ 1)) (J.prod 𝓘(ℝ, ℝ)) κ q).inverse (W (κ q))) = _
    rw [hderiv, ContinuousLinearMap.inverse_equiv]
    exact (L q).apply_symm_apply (W (κ q))
  · intro q
    change (mfderiv (J.prod (𝓡∂ 1)) (J.prod 𝓘(ℝ, ℝ)) κ q).inverse (W (κ q)) = 0 ↔ _
    rw [hderiv, ContinuousLinearMap.inverse_equiv]
    exact (L q).symm.map_eq_zero_iff

end DifferentialGeometry.VectorField
