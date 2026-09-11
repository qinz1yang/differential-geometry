import DifferentialGeometry.Topology.VectorField.ClosedCollarNormalization

set_option autoImplicit false
open Set Function Bundle Manifold TopologicalSpace
open scoped ContDiff Topology
noncomputable section
namespace DifferentialGeometry.VectorField

theorem exists_closedCollarGluing
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
      (fun q => (⟨q, W q⟩ : TangentBundle (J.prod (𝓡∂ 1)) S)))
    (hnonzero : ∀ q : S, W q ≠ 0) :
    let z : B → S := fun p =>
      ⟨(p, ⟨0, ⟨le_rfl, (Fact.out : (0 : ℝ) < ε).le⟩⟩), hcore ha.le⟩
    let T : ∀ p : B, TangentSpace J p := fun p => (W (z p)).1
    let b : B → ℝ := fun p =>
      -(DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc (z p).val.2 (W (z p)).2) / a.val
    ∃ κ : U → S, ContMDiff (J.prod 𝓘(ℝ, ℝ)) (J.prod (𝓡∂ 1)) ∞ κ ∧
      (∀ q : U, (κ q).val.1 = q.val.1 ∧
        (κ q).val.2.val = -a.val * collarNormalizationTime η q.val.2) ∧
      (∀ q : U, (κ q).val.2.val ≤ a.val) ∧
      ∃ G : ∀ q : U, TangentSpace (J.prod 𝓘(ℝ, ℝ)) q,
        ContMDiff (J.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)).tangent ∞
          (fun q => (⟨q, G q⟩ : TangentBundle (J.prod 𝓘(ℝ, ℝ)) U)) ∧
        (∀ q : U, q.val.2 ≤ 0 → G q = ((W (κ q)).1,
          -(DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc (κ q).val.2 (W (κ q)).2) / a.val)) ∧
        (∀ q : U, 0 < q.val.2 → G q = collarExtension T b collarTransition q.val) ∧
        (∀ q : U, q.val.2 = 0 → G q = (T q.val.1, b q.val.1)) ∧
        (∀ q : U, 2 / 3 ≤ q.val.2 → G q = (T q.val.1, (1 : ℝ))) ∧
        ∀ q : U, G q = 0 ↔ 0 < q.val.2 ∧ T q.val.1 = 0 ∧ b q.val.1 < 0 ∧
          collarTransition q.val.2 = -b q.val.1 / (1 - b q.val.1) := by
  intro z T b
  obtain ⟨κ, hκ, hκeq, hκbound, N, hN, hNeq, hNz⟩ :=
    exists_closedCollarNormalization hη a ha U hU S hcore W hW
  have hz : ContMDiff J (J.prod (𝓡∂ 1)) ∞ z := by
    apply (ContMDiff.subtypeVal_comp_iff S z).mp
    exact contMDiff_id.prodMk contMDiff_const
  have hcomponents := contMDiff_equivTangentBundleProd.comp
    (((contMDiff_tangentSection_opens_iff S W).mp hW).comp hz)
  have hT : ContMDiff J J.tangent ∞ (fun p => (⟨p, T p⟩ : TangentBundle J B)) := hcomponents.fst
  have hb : ContMDiff J 𝓘(ℝ, ℝ) ∞ b := by
    have hscalar := DifferentialGeometry.Manifold.Interval.contMDiff_tangentCoordinateIcc.comp hcomponents.snd
    have hlin : ContDiff ℝ ∞ (fun r : ℝ => -r / a.val) := by fun_prop
    exact hlin.contMDiff.comp hscalar
  have hboundary (p : B) (hTp : T p = 0) : b p ≠ 0 := by
    intro hbp
    have hv : DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc (z p).val.2 (W (z p)).2 = 0 :=
      neg_eq_zero.mp ((div_eq_zero_iff.mp hbp).resolve_right ha.ne')
    exact hnonzero (z p) (Prod.ext hTp
      ((DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc (z p).val.2).map_eq_zero_iff.mp hv))
  have hNboundary (q : U) (hq : -η / 3 ≤ q.val.2) : N q = (T q.val.1, b q.val.1) := by
    have hk : κ q = z q.val.1 := by
      apply Subtype.ext
      apply Prod.ext (hκeq q).1
      apply Subtype.ext
      change (κ q).val.2.val = 0
      rw [(hκeq q).2, collarNormalizationTime_eq_zero hη hq, mul_zero]
    rw [hNeq q]
    change ((W (κ q)).1, -(DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc (κ q).val.2
      (W (κ q)).2) / a.val) = ((W (z q.val.1)).1,
        -(DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc (z q.val.1).val.2 (W (z q.val.1)).2) / a.val)
    rw [hk]
  let G : ∀ q : U, TangentSpace (J.prod 𝓘(ℝ, ℝ)) q := fun q =>
    if q.val.2 ≤ 0 then N q else collarExtension T b collarTransition q.val
  have hGs : ContMDiff (J.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun q => (⟨q, G q⟩ : TangentBundle (J.prod 𝓘(ℝ, ℝ)) U)) := by
    apply (contMDiff_tangentSection_opens_iff U G).mpr
    have hNa := (contMDiff_tangentSection_opens_iff U N).mp hN
    have hEa := (contMDiff_collarExtension hT hb contDiff_collarTransition).comp (contMDiff_subtype_val (U := U))
    have h := hNa.piecewise (s := {q : U | q.val.2 ≤ 0}) hEa (fun q hq => by
      have ht : q.val.2 = 0 := by
        have hh := (continuous_snd.comp continuous_subtype_val).frontier_preimage_subset (Iic (0 : ℝ)) hq
        simpa using hh
      have hnear : ∀ᶠ r : U in 𝓝 q, -η / 3 < r.val.2 ∧ r.val.2 < 1 / 3 :=
        ((isOpen_lt continuous_const (continuous_snd.comp continuous_subtype_val)).inter
          (isOpen_lt (continuous_snd.comp continuous_subtype_val) continuous_const)).mem_nhds (by
            change -η / 3 < q.val.2 ∧ q.val.2 < 1 / 3
            rw [ht]
            constructor <;> linarith)
      filter_upwards [hnear] with r hr
      exact congrArg (fun v : TangentSpace (J.prod 𝓘(ℝ, ℝ)) r.val =>
        (⟨r.val, v⟩ : TangentBundle (J.prod 𝓘(ℝ, ℝ)) (B × ℝ)))
        ((hNboundary r hr.1.le).trans (collarExtension_eq_boundaryPair T b hr.2.le).symm))
    convert h using 1
    funext q
    by_cases hq : q.val.2 ≤ 0 <;> simp [G, Set.piecewise, hq]
  have hGneg (q : U) (hq : q.val.2 ≤ 0) : G q = N q := if_pos hq
  have hGpos (q : U) (hq : 0 < q.val.2) : G q = collarExtension T b collarTransition q.val :=
    if_neg hq.not_ge
  refine ⟨κ, hκ, hκeq, hκbound, G, hGs, (fun q hq => (hGneg q hq).trans (hNeq q)),
    hGpos, ?_, ?_, ?_⟩
  · intro q hq
    exact (hGneg q hq.le).trans (hNboundary q (by linarith))
  · intro q hq
    exact (hGpos q (by linarith)).trans (collarExtension_eq_outwardPair T b hq)
  · intro q
    by_cases hq : q.val.2 ≤ 0
    · have hn : G q ≠ 0 := fun hh => hnonzero (κ q) ((hNz q).mp ((hGneg q hq).symm.trans hh))
      simp only [hn, false_iff, not_and]
      exact fun h => (not_lt_of_ge hq h).elim
    · rw [hGpos q (lt_of_not_ge hq)]
      exact (collarExtension_eq_zero_iff (hboundary q.val.1) (collarTransition_mem_Icc q.val.2)).trans
        (by simp only [lt_of_not_ge hq, true_and])

end DifferentialGeometry.VectorField
