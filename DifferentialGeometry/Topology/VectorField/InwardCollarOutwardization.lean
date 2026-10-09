import DifferentialGeometry.Topology.VectorField.InwardCollarNormalization

set_option autoImplicit false
noncomputable section
open Set Function Filter Bundle Manifold TopologicalSpace
open scoped ContDiff Topology
namespace DifferentialGeometry.VectorField

theorem exists_inwardCollar_outwardization
    {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    {J : ModelWithCorners ℝ E H} [IsManifold J 1 B]
    {ε δ a : ℝ} [Fact ((0 : ℝ) < ε)] (hδ : 0 < δ) (ha : 0 < a) :
    let S : Opens (B × Icc (0 : ℝ) ε) :=
      ⟨{q | q.2.val < δ}, isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const⟩
    ∀ W : ∀ q : S, TangentSpace (J.prod (𝓡∂ 1)) q,
      ContMDiff (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)).tangent ∞
        (fun q => (⟨q, W q⟩ : TangentBundle (J.prod (𝓡∂ 1)) S)) →
      (∀ q : S, W q ≠ 0) →
    let z : B → S := fun p => ⟨(p, ⟨0, ⟨le_rfl, (Fact.out : (0 : ℝ) < ε).le⟩⟩), hδ⟩
    let T : ∀ p : B, TangentSpace J p := fun p => (W (z p)).1
    let b : B → ℝ := fun p =>
      -(DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc (z p).val.2 (W (z p)).2) / a
    ∃ G : ∀ q : S, TangentSpace (J.prod (𝓡∂ 1)) q,
      ContMDiff (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)).tangent ∞
        (fun q => (⟨q, G q⟩ : TangentBundle (J.prod (𝓡∂ 1)) S)) ∧
      (∀ q : S, q.val.2.val ≤ a → G q =
        (T q.val.1, (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc q.val.2).symm
          (-a * (collarExtension T b collarTransition (q.val.1, 1 - q.val.2.val / a)).2))) ∧
      (∀ q : S, 4 * a ≤ q.val.2.val → G q = W q) ∧
      (∀ q : S, q.val.2.val = 0 →
        DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc q.val.2 (G q).2 = -a) ∧
      ∀ q : S, G q = 0 ↔ q.val.2.val ≤ a ∧
        collarExtension T b collarTransition (q.val.1, 1 - q.val.2.val / a) = 0 := by
  intro S W hW hn z T b
  have hη : 0 < 6 * a := by positivity
  obtain ⟨κ, _, hκeq, N, hN, hNeq, hNz, hNself, hκzero⟩ :=
    exists_inward_closedCollarNormalization (η := 6 * a) hη W hW
  have hz : ContMDiff J (J.prod (𝓡∂ 1)) ∞ z := by
    apply (ContMDiff.subtypeVal_comp_iff S z).mp
    exact contMDiff_id.prodMk contMDiff_const
  have hcomponents := contMDiff_equivTangentBundleProd.comp
    (((contMDiff_tangentSection_opens_iff S W).mp hW).comp hz)
  have hT : ContMDiff J J.tangent ∞ (fun p => (⟨p, T p⟩ : TangentBundle J B)) := hcomponents.fst
  have hb : ContMDiff J 𝓘(ℝ, ℝ) ∞ b := by
    have hs := DifferentialGeometry.Manifold.Interval.contMDiff_tangentCoordinateIcc.comp hcomponents.snd
    have hl : ContDiff ℝ ∞ (fun t : ℝ => -t / a) := by fun_prop
    exact hl.contMDiff.comp hs
  let L (q : S) := collarExtension T b collarTransition (q.val.1, 1 - q.val.2.val / a)
  let R : ∀ q : S, TangentSpace (J.prod (𝓡∂ 1)) q := fun q =>
    (T q.val.1, (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc q.val.2).symm (-a * (L q).2))
  have hR : ContMDiff (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)).tangent ∞
      (fun q => (⟨q, R q⟩ : TangentBundle (J.prod (𝓡∂ 1)) S)) := by
    apply (contMDiff_tangentSection_opens_iff S R).mpr
    have ht : ContMDiff (J.prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞ (fun q : S => 1 - q.val.2.val / a) :=
      contMDiff_const.sub ((contMDiff_subtypeVal_Icc.comp
        ((contMDiff_snd (I := J) (J := 𝓡∂ 1)).comp contMDiff_subtype_val)).div_const a)
    have hp := (contMDiff_fst.comp (contMDiff_subtype_val (I := J.prod (𝓡∂ 1)) (U := S))).prodMk ht
    have hc := contMDiff_equivTangentBundleProd.comp
      ((contMDiff_collarExtension hT hb contDiff_collarTransition).comp hp)
    have hb' := (contMDiff_const (c := -a)).mul
      ((contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).comp hc.snd)
    have hnormal := DifferentialGeometry.Manifold.Interval.contMDiff_tangentCoordinateIcc_symm.comp
      (((contMDiff_snd (I := J) (J := 𝓡∂ 1)).comp (contMDiff_subtype_val (U := S))).prodMk hb')
    exact contMDiff_equivTangentBundleProd_symm.comp (hc.fst.prodMk hnormal)
  have hcommon (q : S) (hlo : 2 * a / 3 ≤ q.val.2.val) (hhi : q.val.2.val ≤ 2 * a) :
      R q = N q := by
    have hk : κ q = z q.val.1 := by
      apply Subtype.ext
      exact hκzero q (by linarith)
    have hs : 1 - q.val.2.val / a ≤ 1 / 3 := by
      have hh : 2 / 3 ≤ q.val.2.val / a := (le_div_iff₀ ha).mpr (by linarith)
      linarith
    rw [hNeq q, hk]
    change (T q.val.1, (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc q.val.2).symm
      (-a * (L q).2)) = _
    have hL : L q = (T q.val.1, b q.val.1) := collarExtension_eq_boundaryPair T b hs
    rw [hL]
    apply Prod.ext
    · rfl
    · apply congrArg (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc q.val.2).symm
      change -a * (-((DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc (z q.val.1).val.2)
        (W (z q.val.1)).2) / a) = _
      field_simp
  let G : ∀ q : S, TangentSpace (J.prod (𝓡∂ 1)) q := fun q =>
    if q.val.2.val ≤ a then R q else N q
  have hG : ContMDiff (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)).tangent ∞
      (fun q => (⟨q, G q⟩ : TangentBundle (J.prod (𝓡∂ 1)) S)) := by
    have hp := hR.piecewise (s := {q : S | q.val.2.val ≤ a}) hN (fun q hq => by
      have htime : q.val.2.val = a := by
        have hh := (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).frontier_preimage_subset
          (Iic a) hq
        simpa using hh
      have hnear : ∀ᶠ p : S in 𝓝 q, 2 * a / 3 < p.val.2.val ∧ p.val.2.val < 2 * a :=
        ((isOpen_lt continuous_const (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val))).inter
          (isOpen_lt (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)) continuous_const)).mem_nhds
            (by change 2 * a / 3 < q.val.2.val ∧ q.val.2.val < 2 * a; rw [htime]; constructor <;> linarith)
      filter_upwards [hnear] with p hp
      exact congrArg (fun v => (⟨p, v⟩ : TangentBundle (J.prod (𝓡∂ 1)) S)) (hcommon p hp.1.le hp.2.le))
    convert hp using 1
    funext q
    by_cases hq : q.val.2.val ≤ a <;> simp [G, Set.piecewise, hq]
  have hRzero (q : S) : R q = 0 ↔ L q = 0 := by
    constructor
    · intro hz
      have hTz := congrArg Prod.fst hz
      have hNz := congrArg Prod.snd hz
      have hs : -a * (L q).2 = 0 :=
        (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc q.val.2).symm.map_eq_zero_iff.mp hNz
      exact Prod.ext hTz ((mul_eq_zero.mp hs).resolve_left (neg_ne_zero.mpr ha.ne'))
    · intro hz
      have hTz := congrArg Prod.fst hz
      have hNz := congrArg Prod.snd hz
      change (L q).2 = (0 : ℝ) at hNz
      change (T q.val.1, (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc q.val.2).symm (-a * (L q).2)) = 0
      rw [show T q.val.1 = 0 from hTz, hNz, mul_zero, map_zero]
      rfl
  refine ⟨G, hG, fun q hq => ite_eq_left hq, ?_, ?_, ?_⟩
  · intro q hq
    rw [show G q = N q from ite_eq_right (by linarith)]
    exact hNself q (by linarith)
  · intro q hq
    rw [show G q = R q from ite_eq_left (by linarith)]
    change (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc q.val.2)
      ((DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc q.val.2).symm (-a * (L q).2)) = -a
    rw [ContinuousLinearEquiv.apply_symm_apply]
    have hs : 2 / 3 ≤ 1 - q.val.2.val / a := by rw [hq]; norm_num
    have hL : L q = (T q.val.1, (1 : ℝ)) := collarExtension_eq_outwardPair T b hs
    rw [hL, mul_one]
  · intro q
    by_cases hq : q.val.2.val ≤ a
    · rw [show G q = R q from ite_eq_left hq, hRzero q]
      simp only [hq, true_and]
      rfl
    · have hnonzero : N q ≠ 0 := fun h => hn (κ q) ((hNz q).mp h)
      rw [show G q = N q from ite_eq_right hq]
      simp only [hnonzero, hq, false_and]

end DifferentialGeometry.VectorField
