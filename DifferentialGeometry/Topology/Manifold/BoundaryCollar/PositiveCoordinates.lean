import DifferentialGeometry.Topology.Manifold.Interval.Interior
import DifferentialGeometry.Topology.Manifold.Diffeomorph.Restriction

set_option autoImplicit false
noncomputable section
open Set Function Manifold TopologicalSpace
open scoped ContDiff Topology
namespace Poincare.Manifold.BoundaryCollar

theorem exists_positiveCoordinates_diffeomorph
    {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    {F G M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] [TopologicalSpace M] [ChartedSpace G M]
    (J : ModelWithCorners ℝ E H) (I : ModelWithCorners ℝ F G)
    {a : ℝ} [Fact ((0 : ℝ) < a)] (r : C(M, ℝ))
    (c : C(B × Icc (0 : ℝ) a, M)) (hheight : ∀ q, r (c q) = q.2.val)
    (Y : Opens M) (hY : (Y : Set M) = {x | r x < a})
    (d : Diffeomorph (J.prod (𝓡∂ 1)) I
      (⟨{q : B × Icc (0 : ℝ) a | q.2.val < a},
        isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const⟩ :
          Opens (B × Icc (0 : ℝ) a)) Y ∞)
    (hd : ∀ q, (d q).val = c q.val) :
    let P : Opens (B × ℝ) :=
      ⟨{q | 0 < q.2 ∧ q.2 < a},
        (isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const)⟩
    let V : Opens M := ⟨{x | 0 < r x ∧ r x < a},
      (isOpen_lt continuous_const r.continuous).inter (isOpen_lt r.continuous continuous_const)⟩
    ∃ e : Diffeomorph (J.prod 𝓘(ℝ, ℝ)) I P V ∞,
      ∀ q : P, (e q).val = c (q.val.1, ⟨q.val.2, q.property.1.le, q.property.2.le⟩) := by
  intro P V
  let S : Opens (B × Icc (0 : ℝ) a) :=
    ⟨{q | 0 < q.2.val ∧ q.2.val < a},
      (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)).inter
        (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)⟩
  obtain ⟨Z, _, _, d', hd', _⟩ := Diffeomorph.exists_restrict_opens d S (fun _ hq => hq.2)
  have hZ : Z = V := by
    apply SetLike.coe_injective
    ext x
    constructor
    · intro hx
      let q := d'.symm ⟨x, hx⟩
      have hqx : (d' q).val = x := congrArg Subtype.val (d'.apply_symm_apply ⟨x, hx⟩)
      have hqt : r x = q.val.2.val := by rw [← hqx, hd', hd, hheight]
      change 0 < r x ∧ r x < a
      rw [hqt]
      exact q.property
    · intro hx
      have hxY : x ∈ Y := by change x ∈ (Y : Set M); rw [hY]; exact hx.2
      let q := d.symm ⟨x, hxY⟩
      have hqx : (d q).val = x := congrArg Subtype.val (d.apply_symm_apply ⟨x, hxY⟩)
      have hqt : r x = q.val.2.val := by rw [← hqx, hd, hheight]
      have hqS : q.val ∈ S := ⟨hqt ▸ hx.1, q.property⟩
      have hval : (d' ⟨q.val, hqS⟩).val = x := (hd' _).trans hqx
      exact hval ▸ (d' ⟨q.val, hqS⟩).property
  subst Z
  obtain ⟨s, _, hs⟩ := Interval.exists_iccInteriorStrip_diffeomorph (B := B) J ∞
    (a := (0 : ℝ)) (b := a)
  refine ⟨s.symm.trans d', ?_⟩
  intro q
  change (d' (s.symm q)).val = _
  rw [hd', hd]
  apply congrArg c
  have hh := hs q
  have hb : (s.symm q).val.1 = q.val.1 := congrArg Prod.fst hh
  have ht : (s.symm q).val.2.val = q.val.2 := congrArg Prod.snd hh
  exact Prod.ext hb (Subtype.ext ht)

end Poincare.Manifold.BoundaryCollar
