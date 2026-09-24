import DifferentialGeometry.Analysis.Calculus.SmoothTransition
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Fiberwise
import DifferentialGeometry.Topology.Embedding.Graph
import DifferentialGeometry.Topology.Homeomorph.SupportedLocalEmbedding
import Mathlib.Order.Hom.Set
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Homeomorph.Lemmas

open Set
open scoped ContDiff Manifold

namespace Real.smoothAbs

noncomputable def homeomorphIci {ε : ℝ} (hε : 0 < ε) :
    Ici (0 : ℝ) ≃ₜ Ici (Real.smoothAbs ε 0) :=
  ((StrictMonoOn.orderIso (Real.smoothAbs ε) (Ici 0) (strictMonoOn_Ici hε)).trans
    (OrderIso.setCongr _ _ (image_Ici hε))).toHomeomorph

@[simp] theorem homeomorphIci_apply {ε : ℝ} (hε : 0 < ε) (x : Ici (0 : ℝ)) :
    (homeomorphIci hε x).val = Real.smoothAbs ε x.val := rfl

end Real.smoothAbs

namespace Homeomorph

noncomputable def smoothAbsEpigraph {ε : ℝ} (hε : 0 < ε) :
    {p : ℝ × ℝ | |p.1| ≤ p.2} ≃ₜ {p : ℝ × ℝ | Real.smoothAbs ε p.1 ≤ p.2} := by
  let η := Real.smoothAbs.homeomorphIci hε
  have hη (x : Ici (0 : ℝ)) : (η x).val = Real.smoothAbs ε x.val := rfl
  have hinv (q : {p : ℝ × ℝ | Real.smoothAbs ε p.1 ≤ p.2}) :
      Real.smoothAbs ε 0 ≤ q.val.2 :=
    (Real.smoothAbs.apply_zero_le hε q.val.1).trans q.property
  let inv (q : {p : ℝ × ℝ | Real.smoothAbs ε p.1 ≤ p.2}) : ℝ :=
    (η.symm ⟨q.val.2, hinv q⟩).val
  have hinvval (q : {p : ℝ × ℝ | Real.smoothAbs ε p.1 ≤ p.2}) :
      Real.smoothAbs ε (inv q) = q.val.2 :=
    congrArg Subtype.val (η.apply_symm_apply ⟨q.val.2, hinv q⟩)
  have hinvpos (q : {p : ℝ × ℝ | Real.smoothAbs ε p.1 ≤ p.2}) : 0 ≤ inv q :=
    (η.symm ⟨q.val.2, hinv q⟩).property
  refine
    { toFun := fun p => ⟨(p.val.1, Real.smoothAbs ε p.val.2), ?_⟩
      invFun := fun q => ⟨(q.val.1, inv q), ?_⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · change Real.smoothAbs ε p.val.1 ≤ Real.smoothAbs ε p.val.2
    rw [← Real.smoothAbs.abs hε.ne' p.val.1]
    exact (Real.smoothAbs.strictMonoOn_Ici hε).monotoneOn (abs_nonneg p.val.1)
      ((abs_nonneg p.val.1).trans p.property) p.property
  · apply (Real.smoothAbs.strictMonoOn_Ici hε).le_iff_le
      (show |q.val.1| ∈ Ici 0 by exact abs_nonneg q.val.1) (show inv q ∈ Ici 0 from hinvpos q) |>.mp
    rw [Real.smoothAbs.abs hε.ne', hinvval]
    exact q.property
  · intro p
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply (Real.smoothAbs.strictMonoOn_Ici hε).injOn (hinvpos _)
        ((abs_nonneg p.val.1).trans p.property)
      exact hinvval _
  · intro q
    apply Subtype.ext
    exact Prod.ext rfl (hinvval q)
  · exact (continuous_subtype_val.fst.prodMk
      ((Real.smoothAbs.contDiff ε).continuous.comp continuous_subtype_val.snd)).subtype_mk _
  · have hc : Continuous inv :=
      (η.symm.continuous.comp (continuous_subtype_val.snd.subtype_mk hinv)).subtype_val
    exact (continuous_subtype_val.fst.prodMk hc).subtype_mk _

@[simp] theorem smoothAbsEpigraph_apply {ε : ℝ} (hε : 0 < ε)
    (p : {p : ℝ × ℝ | |p.1| ≤ p.2}) :
    (smoothAbsEpigraph hε p).val = (p.val.1, Real.smoothAbs ε p.val.2) := rfl

theorem smoothAbsEpigraph_apply_eq_self {ε : ℝ} (hε : 0 < ε)
    (p : {p : ℝ × ℝ | |p.1| ≤ p.2}) (hp : ε ≤ p.val.2) :
    (smoothAbsEpigraph hε p).val = p.val := by
  rw [smoothAbsEpigraph_apply, Real.smoothAbs.eq_self_of_le hε hp]

theorem smoothAbsEpigraph_snd_le {ε : ℝ} (hε : 0 < ε)
    (p : {p : ℝ × ℝ | |p.1| ≤ p.2}) (hp : p.val.2 ≤ ε) :
    (smoothAbsEpigraph hε p).val.2 ≤ ε := by
  change Real.smoothAbs ε p.val.2 ≤ ε
  calc
    Real.smoothAbs ε p.val.2 ≤ Real.smoothAbs ε ε :=
      (Real.smoothAbs.strictMonoOn_Ici hε).monotoneOn
        ((abs_nonneg p.val.1).trans p.property) hε.le hp
    _ = ε := Real.smoothAbs.eq_self_of_le hε le_rfl

theorem smoothAbsEpigraph_image_boundary {ε : ℝ} (hε : 0 < ε) :
    smoothAbsEpigraph hε '' {p | p.val.2 = |p.val.1|} =
      {p | p.val.2 = Real.smoothAbs ε p.val.1} := by
  let R := smoothAbsEpigraph hε
  have hR (p : {p : ℝ × ℝ | |p.1| ≤ p.2}) :
      (R p).val = (p.val.1, Real.smoothAbs ε p.val.2) := rfl
  have hiff (p : {p : ℝ × ℝ | |p.1| ≤ p.2}) :
      (R p).val.2 = Real.smoothAbs ε (R p).val.1 ↔ p.val.2 = |p.val.1| := by
    rw [hR]
    change Real.smoothAbs ε p.val.2 = Real.smoothAbs ε p.val.1 ↔ _
    rw [← Real.smoothAbs.abs hε.ne' p.val.1]
    exact (Real.smoothAbs.strictMonoOn_Ici hε).injOn.eq_iff
      ((abs_nonneg p.val.1).trans p.property) (abs_nonneg p.val.1)
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (hiff q).mpr hq
  · intro hp
    refine ⟨R.symm p, (hiff _).mp ?_, R.apply_symm_apply p⟩
    rwa [R.apply_symm_apply]

end Homeomorph


namespace DifferentialGeometry.Topology.Manifold

theorem isLocalDiffeomorphAt_prod_smoothAbs {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {ε : ℝ} (hε : 0 < ε) {p : P × ℝ} (hp : 0 < p.2) :
    IsLocalDiffeomorphAt 𝓘(ℝ, P × ℝ) 𝓘(ℝ, P × ℝ) ∞
      (fun z : P × ℝ => (z.1, Real.smoothAbs ε z.2)) p := by
  apply isLocalDiffeomorphAt_prod_of_injective_fderiv isOpen_univ
    ((Real.smoothAbs.contDiff ε).comp contDiff_snd).contDiffOn (mem_univ p)
  intro x y hxy
  simp only [fderiv_eq_smul_deriv, smul_eq_mul] at hxy
  exact mul_right_cancel₀ (Real.smoothAbs.deriv_pos hε hp).ne' hxy

theorem isSmoothEmbedding_smoothAbs_graph (ε : ℝ) :
    _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun r : ℝ => (r, Real.smoothAbs ε r)) :=
  _root_.Manifold.IsSmoothEmbedding.id.graph (Real.smoothAbs.contDiff ε)

theorem isSmoothEmbedding_neg_smoothAbs_graph (ε : ℝ) :
    _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun r : ℝ => (-r, Real.smoothAbs ε r)) := by
  have h := (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ).toDiffeomorph.isSmoothEmbedding.graph
    ((Real.smoothAbs.contDiff ε).comp contDiff_neg)
  simpa only [ContinuousLinearEquiv.coe_toDiffeomorph, ContinuousLinearEquiv.neg_apply, Function.comp_def, neg_neg] using h

end DifferentialGeometry.Topology.Manifold

namespace Homeomorph

private noncomputable def cornerCoordinates : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) where
  toFun p := (p.1 - p.2, p.1 + p.2)
  invFun p := ((p.1 + p.2) / 2, (p.2 - p.1) / 2)
  map_add' := by intro p q; ext <;> dsimp <;> ring
  map_smul' := by intro c p; ext <;> dsimp <;> ring
  left_inv := by intro p; ext <;> dsimp <;> ring
  right_inv := by intro p; ext <;> dsimp <;> ring
  continuous_toFun := (continuous_fst.sub continuous_snd).prodMk (continuous_fst.add continuous_snd)
  continuous_invFun := ((continuous_fst.add continuous_snd).div_const 2).prodMk
    ((continuous_snd.sub continuous_fst).div_const 2)

private noncomputable def quadrantCoordinates : {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} ≃ₜ
    {p : ℝ × ℝ | |p.1| ≤ p.2} :=
  cornerCoordinates.toHomeomorph.subtype (by
    intro p
    change (0 ≤ p.1 ∧ 0 ≤ p.2) ↔ |p.1 - p.2| ≤ p.1 + p.2
    rw [abs_le]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2])

private noncomputable def roundedQuadrantCoordinates (ε : ℝ) :
    {p : ℝ × ℝ | Real.smoothAbs ε (p.1 - p.2) ≤ p.1 + p.2} ≃ₜ
      {p : ℝ × ℝ | Real.smoothAbs ε p.1 ≤ p.2} :=
  cornerCoordinates.toHomeomorph.subtype (fun _ => Iff.rfl)

noncomputable def smoothAbsQuadrant {ε : ℝ} (hε : 0 < ε) :
    {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} ≃ₜ
      {p : ℝ × ℝ | Real.smoothAbs ε (p.1 - p.2) ≤ p.1 + p.2} :=
  (quadrantCoordinates.trans (smoothAbsEpigraph hε)).trans (roundedQuadrantCoordinates ε).symm

@[simp] theorem smoothAbsQuadrant_apply {ε : ℝ} (hε : 0 < ε)
    (p : {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}) :
    (smoothAbsQuadrant hε p).val =
      ((p.val.1 - p.val.2 + Real.smoothAbs ε (p.val.1 + p.val.2)) / 2,
        (Real.smoothAbs ε (p.val.1 + p.val.2) - (p.val.1 - p.val.2)) / 2) := rfl

theorem smoothAbsQuadrant_apply_eq_self {ε : ℝ} (hε : 0 < ε)
    (p : {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}) (hp : ε ≤ p.val.1 + p.val.2) :
    (smoothAbsQuadrant hε p).val = p.val := by
  rw [smoothAbsQuadrant_apply, Real.smoothAbs.eq_self_of_le hε hp]
  ext <;> dsimp <;> ring

theorem smoothAbsQuadrant_sum_le {ε : ℝ} (hε : 0 < ε)
    (p : {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}) (hp : p.val.1 + p.val.2 ≤ ε) :
    (smoothAbsQuadrant hε p).val.1 + (smoothAbsQuadrant hε p).val.2 ≤ ε := by
  rw [smoothAbsQuadrant_apply]
  have h := (Real.smoothAbs.strictMonoOn_Ici hε).monotoneOn
    (show p.val.1 + p.val.2 ∈ Ici 0 from add_nonneg p.property.1 p.property.2) hε.le hp
  rw [Real.smoothAbs.eq_self_of_le hε le_rfl] at h
  dsimp
  linarith

theorem smoothAbsQuadrant_nonneg {ε : ℝ} (hε : 0 < ε)
    (p : {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}) :
    0 ≤ (smoothAbsQuadrant hε p).val.1 ∧ 0 ≤ (smoothAbsQuadrant hε p).val.2 := by
  let q := (smoothAbsQuadrant hε p).val
  have hs : Real.smoothAbs ε (q.1 - q.2) ≤ q.1 + q.2 := (smoothAbsQuadrant hε p).property
  have ha := (Real.smoothAbs.sub_abs_mem_Icc hε (q.1 - q.2)).1
  have hl := neg_abs_le (q.1 - q.2)
  have hr := le_abs_self (q.1 - q.2)
  constructor <;> linarith

end Homeomorph

namespace OpenPartialHomeomorph

theorem exists_homeomorph_smoothAbs_quadrant_of_isClosed {X P : Type*}
    [TopologicalSpace X] [T2Space X] [TopologicalSpace P] [CompactSpace P]
    (e : OpenPartialHomeomorph X (P × (ℝ × ℝ)))
    {A : Set X} (hA : IsClosed A) {ε : ℝ} (hε : 0 < ε)
    (hraw : ∀ p ∈ e.target, e.symm p ∈ A ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2)
    (hstrip : {p : P × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆
      e.target) :
    ∃ H : A ≃ₜ ↥((A \ e.source) ∪ e.symm ''
      (e.target ∩ {p | Real.smoothAbs ε (p.2.1 - p.2.2) ≤ p.2.1 + p.2.2})),
      (∀ x : A, x.val ∈ e.source → (H x).val = e.symm
        ((e x.val).1,
          (((e x.val).2.1 - (e x.val).2.2 +
            Real.smoothAbs ε ((e x.val).2.1 + (e x.val).2.2)) / 2,
          (Real.smoothAbs ε ((e x.val).2.1 + (e x.val).2.2) -
            ((e x.val).2.1 - (e x.val).2.2)) / 2))) ∧
      ∀ x : A, x.val ∉ e.symm ''
        {p : P × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} →
        (H x).val = x.val := by
  let Q : Set (P × (ℝ × ℝ)) := {p | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2}
  let K : Set (P × (ℝ × ℝ)) := {p | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε}
  let F : P × (ℝ × ℝ) → P × (ℝ × ℝ) := fun p =>
    (p.1, ((p.2.1 - p.2.2 + Real.smoothAbs ε (p.2.1 + p.2.2)) / 2,
      (Real.smoothAbs ε (p.2.1 + p.2.2) - (p.2.1 - p.2.2)) / 2))
  let R := Homeomorph.smoothAbsQuadrant hε
  have hF (p : P × (ℝ × ℝ)) (hp : p ∈ Q) : F p = (p.1, (R ⟨p.2, hp⟩).val) := rfl
  have hFid (p : P × (ℝ × ℝ)) (hp : p ∈ Q) (hεp : ε ≤ p.2.1 + p.2.2) : F p = p := by
    rw [hF p hp, Homeomorph.smoothAbsQuadrant_apply_eq_self hε _ hεp]
  have hFK (p : P × (ℝ × ℝ)) (hp : p ∈ K) : F p ∈ K := by
    have hn := Homeomorph.smoothAbsQuadrant_nonneg hε ⟨p.2, hp.1, hp.2.1⟩
    have hs := Homeomorph.smoothAbsQuadrant_sum_le hε ⟨p.2, hp.1, hp.2.1⟩ hp.2.2
    exact ⟨hn.1, hn.2, hs⟩
  have hK : IsCompact K := by
    have hc := (isCompact_univ (X := P)).prod ((isCompact_Icc (a := (0 : ℝ)) (b := ε)).prod
      (isCompact_Icc (a := (0 : ℝ)) (b := ε)))
    have hclosed : IsClosed K := (isClosed_le continuous_const continuous_snd.fst).inter
      ((isClosed_le continuous_const continuous_snd.snd).inter
        (isClosed_le (continuous_snd.fst.add continuous_snd.snd) continuous_const))
    apply hc.of_isClosed_subset hclosed
    intro p hp
    exact ⟨mem_univ _, ⟨hp.1, by linarith [hp.2.1, hp.2.2]⟩,
      ⟨hp.2.1, by linarith [hp.1, hp.2.2]⟩⟩
  have hsource : e '' (A ∩ e.source) = e.target ∩ Q := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨e.map_source hx.2, (hraw _ (e.map_source hx.2)).mp ?_⟩
      rw [e.left_inv hx.2]
      exact hx.1
    · intro hp
      exact ⟨e.symm p, ⟨(hraw p hp.1).mpr hp.2, e.map_target hp.1⟩, e.right_inv hp.1⟩
  have hcont : Continuous F := by
    have hf := (Real.smoothAbs.contDiff ε).continuous.comp
      (continuous_snd.fst.add continuous_snd.snd : Continuous (fun p : P × (ℝ × ℝ) => p.2.1 + p.2.2))
    exact continuous_fst.prodMk
      (((continuous_snd.fst.sub continuous_snd.snd).add hf).div_const 2 |>.prodMk
        ((hf.sub (continuous_snd.fst.sub continuous_snd.snd)).div_const 2))
  have hinj : InjOn F Q := by
    intro p hp q hq heq
    have heq1 := congrArg Prod.fst heq
    have heq2 : R ⟨p.2, hp⟩ = R ⟨q.2, hq⟩ := Subtype.ext (congrArg Prod.snd heq)
    exact Prod.ext heq1 (congrArg Subtype.val (R.injective heq2))
  have hmap : MapsTo F (e.target ∩ Q) e.target := by
    intro p hp
    by_cases hεp : ε ≤ p.2.1 + p.2.2
    · rw [hFid p hp.2 hεp]
      exact hp.1
    · exact hstrip (hFK p ⟨hp.2.1, hp.2.2, (lt_of_not_ge hεp).le⟩)
  have hfixed : EqOn F id ((e.target ∩ Q) \ K) := by
    intro p hp
    apply hFid p hp.1.2
    by_contra h
    exact hp.2 ⟨hp.1.2.1, hp.1.2.2, (lt_of_not_ge h).le⟩
  have himage : F '' (e.target ∩ Q) =
      e.target ∩ {p | Real.smoothAbs ε (p.2.1 - p.2.2) ≤ p.2.1 + p.2.2} := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨hmap hq, (R ⟨q.2, hq.2⟩).property⟩
    · intro hp
      let q : P × (ℝ × ℝ) := (p.1, (R.symm ⟨p.2, hp.2⟩).val)
      have hq : q ∈ Q := (R.symm ⟨p.2, hp.2⟩).property
      have hFq : F q = p := by
        rw [hF q hq]
        have hr : R ⟨q.2, hq⟩ = ⟨p.2, hp.2⟩ := R.apply_symm_apply ⟨p.2, hp.2⟩
        rw [hr]
      have hqt : q ∈ e.target := by
        by_cases hεq : ε ≤ q.2.1 + q.2.2
        · have hqp : q = p := (hFid q hq hεq).symm.trans hFq
          rw [hqp]
          exact hp.1
        · exact hstrip ⟨hq.1, hq.2, (lt_of_not_ge hεq).le⟩
      exact ⟨q, ⟨hqt, hq⟩, hFq⟩
  obtain ⟨H, hH, hHfix⟩ := e.exists_homeomorph_eqOn_of_isClosed hA hcont.continuousOn
    (by rw [hsource]; exact hinj.mono inter_subset_right)
    (by rw [hsource]; exact hmap) hK hstrip (by rwa [hsource])
  have heq : (A \ e.source) ∪ e.symm '' (F '' (e '' (A ∩ e.source))) =
      (A \ e.source) ∪ e.symm ''
        (e.target ∩ {p | Real.smoothAbs ε (p.2.1 - p.2.2) ≤ p.2.1 + p.2.2}) := by
    rw [hsource, himage]
  exact ⟨H.trans (Homeomorph.setCongr heq), hH, hHfix⟩

theorem exists_homeomorph_smoothAbs_quadrant {X P : Type*}
    [TopologicalSpace X] [T2Space X] [TopologicalSpace P] [CompactSpace P]
    (e : OpenPartialHomeomorph X (P × (ℝ × ℝ)))
    {A : Set X} (hA : IsCompact A) {ε : ℝ} (hε : 0 < ε)
    (hraw : ∀ p ∈ e.target, e.symm p ∈ A ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2)
    (hstrip : {p : P × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆
      e.target) :
    ∃ H : A ≃ₜ ↥((A \ e.source) ∪ e.symm ''
      (e.target ∩ {p | Real.smoothAbs ε (p.2.1 - p.2.2) ≤ p.2.1 + p.2.2})),
      (∀ x : A, x.val ∈ e.source → (H x).val = e.symm
        ((e x.val).1,
          (((e x.val).2.1 - (e x.val).2.2 +
            Real.smoothAbs ε ((e x.val).2.1 + (e x.val).2.2)) / 2,
          (Real.smoothAbs ε ((e x.val).2.1 + (e x.val).2.2) -
            ((e x.val).2.1 - (e x.val).2.2)) / 2))) ∧
      ∀ x : A, x.val ∉ e.symm ''
        {p : P × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} →
        (H x).val = x.val := by
  exact e.exists_homeomorph_smoothAbs_quadrant_of_isClosed hA.isClosed hε hraw hstrip

end OpenPartialHomeomorph

namespace DifferentialGeometry.Topology.Manifold

theorem isLocalDiffeomorphAt_smoothAbs_quadrant {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {ε : ℝ} (hε : 0 < ε) {p : P × (ℝ × ℝ)} (hp : 0 < p.2.1 + p.2.2) :
    IsLocalDiffeomorphAt 𝓘(ℝ, P × (ℝ × ℝ)) 𝓘(ℝ, P × (ℝ × ℝ)) ∞
      (fun z : P × (ℝ × ℝ) => (z.1,
        ((z.2.1 - z.2.2 + Real.smoothAbs ε (z.2.1 + z.2.2)) / 2,
        (Real.smoothAbs ε (z.2.1 + z.2.2) - (z.2.1 - z.2.2)) / 2))) p := by
  let c : (P × (ℝ × ℝ)) ≃L[ℝ] ((P × ℝ) × ℝ) :=
    ((ContinuousLinearEquiv.refl ℝ P).prodCongr Homeomorph.cornerCoordinates).trans
      (ContinuousLinearEquiv.prodAssoc ℝ P ℝ ℝ).symm
  have h := (c.toDiffeomorph.isLocalDiffeomorph p).comp
    𝓘(ℝ, (P × ℝ) × ℝ) ((P × ℝ) × ℝ)
    (isLocalDiffeomorphAt_prod_smoothAbs hε (p := c p) hp)
  have h' := h.comp 𝓘(ℝ, P × (ℝ × ℝ)) (P × (ℝ × ℝ))
    (c.symm.toDiffeomorph.isLocalDiffeomorph _)
  exact h'

theorem isSmoothEmbedding_smoothAbs_quadrant_boundary (ε : ℝ) :
    _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun r : ℝ => ((r + Real.smoothAbs ε r) / 2, (Real.smoothAbs ε r - r) / 2)) :=
  (isSmoothEmbedding_smoothAbs_graph ε).diffeomorph_comp
    Homeomorph.cornerCoordinates.symm.toDiffeomorph

end DifferentialGeometry.Topology.Manifold

namespace Homeomorph

theorem smoothAbsQuadrant_sub {ε : ℝ} (hε : 0 < ε)
    (p : {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}) :
    (smoothAbsQuadrant hε p).val.1 - (smoothAbsQuadrant hε p).val.2 = p.val.1 - p.val.2 := by
  rw [smoothAbsQuadrant_apply]
  dsimp
  ring

theorem smoothAbsQuadrant_sum {ε : ℝ} (hε : 0 < ε)
    (p : {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}) :
    (smoothAbsQuadrant hε p).val.1 + (smoothAbsQuadrant hε p).val.2 =
      Real.smoothAbs ε (p.val.1 + p.val.2) := by
  rw [smoothAbsQuadrant_apply]
  dsimp
  ring

theorem smoothAbsQuadrant_image_horizontal_axis {ε : ℝ} (hε : 0 < ε) :
    smoothAbsQuadrant hε '' {p | p.val.2 = 0} =
      {p | p.val.1 + p.val.2 = Real.smoothAbs ε (p.val.1 - p.val.2) ∧
        0 ≤ p.val.1 - p.val.2} := by
  let R := smoothAbsQuadrant hε
  have hiff (p : {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}) :
      (R p).val.1 + (R p).val.2 = Real.smoothAbs ε ((R p).val.1 - (R p).val.2) ∧
        0 ≤ (R p).val.1 - (R p).val.2 ↔ p.val.2 = 0 := by
    rw [smoothAbsQuadrant_sub hε p, smoothAbsQuadrant_sum hε p]
    constructor
    · intro h
      have he := (Real.smoothAbs.strictMonoOn_Ici hε).injOn
        (add_nonneg p.property.1 p.property.2) h.2 h.1
      linarith
    · intro hp
      simp only [hp, add_zero, sub_zero, true_and]
      exact p.property.1
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (hiff q).mpr hq
  · intro hp
    refine ⟨R.symm p, (hiff _).mp ?_, R.apply_symm_apply p⟩
    rwa [R.apply_symm_apply]

theorem smoothAbsQuadrant_image_vertical_axis {ε : ℝ} (hε : 0 < ε) :
    smoothAbsQuadrant hε '' {p | p.val.1 = 0} =
      {p | p.val.1 + p.val.2 = Real.smoothAbs ε (p.val.1 - p.val.2) ∧
        p.val.1 - p.val.2 ≤ 0} := by
  let R := smoothAbsQuadrant hε
  have hiff (p : {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}) :
      (R p).val.1 + (R p).val.2 = Real.smoothAbs ε ((R p).val.1 - (R p).val.2) ∧
        (R p).val.1 - (R p).val.2 ≤ 0 ↔ p.val.1 = 0 := by
    rw [smoothAbsQuadrant_sub hε p, smoothAbsQuadrant_sum hε p, ← Real.smoothAbs.neg hε.ne' (p.val.1 - p.val.2)]
    constructor
    · intro h
      have he := (Real.smoothAbs.strictMonoOn_Ici hε).injOn
        (add_nonneg p.property.1 p.property.2) (neg_nonneg.mpr h.2) h.1
      linarith
    · intro hp
      rw [hp]
      simp only [zero_add, zero_sub, neg_neg]
      exact ⟨trivial, neg_nonpos.mpr p.property.2⟩
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (hiff q).mpr hq
  · intro hp
    refine ⟨R.symm p, (hiff _).mp ?_, R.apply_symm_apply p⟩
    rwa [R.apply_symm_apply]

end Homeomorph
