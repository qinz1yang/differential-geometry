import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Order.IntermediateValue

noncomputable section

open Set Topology Function

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private def bicollarPhase (z : ℝ) : ℝ := min 1 (max 0 ((z + 1) / 2))

private theorem bicollarPhase_continuous : Continuous bicollarPhase :=
  continuous_const.min (continuous_const.max ((continuous_id.add continuous_const).div_const 2))

private theorem bicollarPhase_zero (z : ℝ) (hz : z ≤ -1) : bicollarPhase z = 0 := by
  have h : (z + 1) / 2 ≤ 0 := by linarith
  simp [bicollarPhase, max_eq_left h]

private theorem bicollarPhase_one (z : ℝ) (hz : 1 ≤ z) : bicollarPhase z = 1 := by
  have h : 1 ≤ (z + 1) / 2 := by linarith
  exact min_eq_left (h.trans (le_max_right _ _))

private theorem bicollarPhase_lt_half_iff (z : ℝ) : bicollarPhase z < 1 / 2 ↔ z < 0 := by
  constructor
  · intro h
    rcases min_lt_iff.mp h with h | h
    · norm_num at h
    · have h' := (max_lt_iff.mp h).2
      linarith
  · intro h
    exact min_lt_iff.mpr (Or.inr (max_lt_iff.mpr ⟨by norm_num, by linarith⟩))

private theorem half_lt_bicollarPhase_iff (z : ℝ) : 1 / 2 < bicollarPhase z ↔ 0 < z := by
  constructor
  · intro h
    rcases lt_max_iff.mp (lt_min_iff.mp h).2 with h | h
    · norm_num at h
    · linarith
  · intro h
    exact lt_min_iff.mpr ⟨by norm_num, lt_max_iff.mpr (Or.inr (by linarith))⟩

private theorem bicollarPhase_eq_half_iff (z : ℝ) : bicollarPhase z = 1 / 2 ↔ z = 0 := by
  constructor
  · intro h
    rcases lt_trichotomy z 0 with hz | hz | hz
    · have := (bicollarPhase_lt_half_iff z).mpr hz
      linarith
    · exact hz
    · have := (half_lt_bicollarPhase_iff z).mpr hz
      linarith
  · rintro rfl
    norm_num [bicollarPhase]

private theorem bicollar_circle_hasCompactSupport
    {A : Type*} [TopologicalSpace A] [T2Space A] [CompactSpace A] :
    HasCompactSupport (fun p : A × ℝ => (bicollarPhase p.2 : AddCircle (1 : ℝ))) := by
  apply HasCompactSupport.of_support_subset_isCompact
    ((isCompact_univ : IsCompact (univ : Set A)).prod (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)))
  intro p hp
  refine ⟨mem_univ _, ?_⟩
  by_contra h
  have hne : (bicollarPhase p.2 : AddCircle (1 : ℝ)) ≠ 0 := hp
  rcases not_and_or.mp h with h | h
  · rw [bicollarPhase_zero p.2 (le_of_lt (lt_of_not_ge h)), AddCircle.coe_zero] at hne
    exact hne rfl
  · rw [bicollarPhase_one p.2 (le_of_lt (lt_of_not_ge h)), AddCircle.coe_period] at hne
    exact hne rfl

private theorem exists_bicollar_circle_map
    {A M : Type*} [TopologicalSpace A] [T2Space A] [CompactSpace A]
    [TopologicalSpace M] [T2Space M]
    (φ : A × ℝ → M) (hφ : IsOpenEmbedding φ) :
    ∃ q : C(M, AddCircle (1 : ℝ)),
      (∀ p, q (φ p) = (bicollarPhase p.2 : AddCircle (1 : ℝ))) ∧
      ∀ x, x ∉ range φ → q x = 0 := by
  classical
  let e := hφ.isEmbedding.toHomeomorph
  let f : range φ → AddCircle (1 : ℝ) :=
    fun x => (bicollarPhase (e.symm x).2 : AddCircle (1 : ℝ))
  have hf : Continuous f := (AddCircle.continuous_mk' (1 : ℝ)).comp
    (bicollarPhase_continuous.comp (continuous_snd.comp e.symm.continuous))
  have hs : HasCompactSupport f := bicollar_circle_hasCompactSupport.comp_homeomorph e.symm
  let q : C(M, AddCircle (1 : ℝ)) :=
    ⟨Subtype.val.extend f 0, HasCompactSupport.continuous_extend_zero hφ.isOpen_range hf hs⟩
  refine ⟨q, ?_, ?_⟩
  · intro p
    change Subtype.val.extend f 0 ((⟨φ p, ⟨p, rfl⟩⟩ : range φ) : M) = _
    rw [Subtype.val_injective.extend_apply]
    simp [f, e]
  · intro x hx
    change Subtype.val.extend f 0 x = 0
    exact Function.extend_apply' (f := (Subtype.val : range φ → M)) f (fun _ : M => 0) x (by
      rintro ⟨y, rfl⟩
      exact hx y.property)

private theorem bicollar_half_ne_zero :
    ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) ≠ 0 := by
  have : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  intro h
  have hz := (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (p := (1 : ℝ)) (a := 0)
    (x := (1 / 2 : ℝ)) (y := (0 : ℝ)) (by norm_num) (by norm_num)).mp h
  norm_num at hz

private theorem bicollarPhase_coe_eq_half_iff (z : ℝ) :
    (bicollarPhase z : AddCircle (1 : ℝ)) = ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) ↔
      z = 0 := by
  have : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  constructor
  · intro h
    have hnonneg : 0 ≤ bicollarPhase z :=
      le_min (by norm_num) (le_max_left _ _)
    have hle : bicollarPhase z ≤ 1 := min_le_left _ _
    have hlt : bicollarPhase z < 1 := by
      by_contra hnot
      have heq : bicollarPhase z = 1 := le_antisymm hle (le_of_not_gt hnot)
      rw [heq, AddCircle.coe_period] at h
      exact bicollar_half_ne_zero h.symm
    apply (bicollarPhase_eq_half_iff z).mp
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (p := (1 : ℝ)) (a := 0)
      (x := bicollarPhase z) (y := (1 / 2 : ℝ))
      ⟨hnonneg, by simpa only [zero_add] using hlt⟩ (by norm_num)).mp h
  · rintro rfl
    norm_num [bicollarPhase]

private theorem bicollar_circle_eq_half_iff
    {A M : Type*} [TopologicalSpace M]
    (φ : A × ℝ → M) (q : C(M, AddCircle (1 : ℝ)))
    (hq : ∀ p, q (φ p) = (bicollarPhase p.2 : AddCircle (1 : ℝ)))
    (hq_out : ∀ x, x ∉ range φ → q x = 0) (x : M) :
    q x = ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) ↔
      x ∈ range (fun y => φ (y, 0)) := by
  classical
  constructor
  · intro hx
    by_cases hxr : x ∈ range φ
    · obtain ⟨⟨y, z⟩, rfl⟩ := hxr
      rw [hq] at hx
      have hz : z = 0 := (bicollarPhase_coe_eq_half_iff z).mp hx
      exact ⟨y, by rw [hz]⟩
    · exact False.elim (bicollar_half_ne_zero (hx.symm.trans (hq_out x hxr)))
  · rintro ⟨y, rfl⟩
    rw [hq]
    norm_num [bicollarPhase]

private theorem exists_bicollar_separating_function_of_lift
    {A M : Type*} [TopologicalSpace A] [ConnectedSpace A] [TopologicalSpace M]
    (φ : A × ℝ → M) (hφ : Continuous φ)
    (q : C(M, AddCircle (1 : ℝ)))
    (hq : ∀ p, q (φ p) = (bicollarPhase p.2 : AddCircle (1 : ℝ)))
    (hq_out : ∀ x, x ∉ range φ → q x = 0)
    (a₀ : A) (θ : C(M, ℝ)) (hθ_base : θ (φ (a₀, 0)) = 1 / 2)
    (hθq : ((↑) : ℝ → AddCircle (1 : ℝ)) ∘ θ = q) :
    ∃ f : C(M, ℝ),
      (∀ y z, f (φ (y, z)) = min 1 (max 0 ((z + 1) / 2)) - 1 / 2) ∧
      ∀ x, f x = 0 ↔ x ∈ range (fun y => φ (y, 0)) := by
  classical
  have hθφ : (fun p : A × ℝ => θ (φ p)) = fun p => bicollarPhase p.2 := by
    refine (AddCircle.isCoveringMap_coe (1 : ℝ)).eq_of_comp_eq
      (θ.continuous.comp hφ) (bicollarPhase_continuous.comp continuous_snd)
      ?_ (a₀, 0) ?_
    · funext p
      exact (congr_fun hθq (φ p)).trans (hq p)
    · have hphase : bicollarPhase 0 = 1 / 2 := by norm_num [bicollarPhase]
      simpa only [hphase] using hθ_base
  let f : C(M, ℝ) := ⟨fun x => θ x - 1 / 2, θ.continuous.sub continuous_const⟩
  refine ⟨f, ?_, ?_⟩
  · intro y z
    change θ (φ (y, z)) - 1 / 2 = _
    rw [congr_fun hθφ (y, z)]
    rfl
  · intro x
    constructor
    · intro hx
      have hθx : θ x = 1 / 2 := sub_eq_zero.mp hx
      by_cases hxr : x ∈ range φ
      · obtain ⟨⟨y, z⟩, rfl⟩ := hxr
        have hz : z = 0 := (bicollarPhase_eq_half_iff z).mp
          ((congr_fun hθφ (y, z)).symm.trans hθx)
        exact ⟨y, by rw [hz]⟩
      · have h := congr_fun hθq x
        change ((θ x : ℝ) : AddCircle (1 : ℝ)) = q x at h
        rw [hθx, hq_out x hxr] at h
        exact False.elim (bicollar_half_ne_zero h)
    · rintro ⟨y, rfl⟩
      change θ (φ (y, 0)) - 1 / 2 = 0
      rw [congr_fun hθφ (y, 0)]
      norm_num [bicollarPhase]

theorem exists_bicollar_separating_function
    {A M : Type*} [TopologicalSpace A] [T2Space A] [CompactSpace A] [ConnectedSpace A]
    [TopologicalSpace M] [T2Space M] [SimplyConnectedSpace M] [LocallyPathConnectedSpace M]
    (φ : A × ℝ → M) (hφ : IsOpenEmbedding φ) :
    ∃ f : C(M, ℝ),
      (∀ y z, f (φ (y, z)) = min 1 (max 0 ((z + 1) / 2)) - 1 / 2) ∧
      ∀ x, f x = 0 ↔ x ∈ range (fun y => φ (y, 0)) := by
  classical
  obtain ⟨q, hq, hq_out⟩ := exists_bicollar_circle_map φ hφ
  let a₀ : A := Classical.arbitrary A
  have hbase : ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) = q (φ (a₀, 0)) := by
    rw [hq]
    norm_num [bicollarPhase]
  obtain ⟨θ, ⟨hθ_base, hθq⟩, _⟩ :=
    (AddCircle.isCoveringMap_coe (1 : ℝ)).existsUnique_continuousMap_lifts
      q (φ (a₀, 0)) (1 / 2) hbase
  exact exists_bicollar_separating_function_of_lift φ hφ.continuous q hq hq_out
    a₀ θ hθ_base hθq

theorem exists_bicollar_separating_function_of_homotopic_disjoint
    {A M : Type*} [TopologicalSpace A] [T2Space A] [CompactSpace A] [ConnectedSpace A]
    [TopologicalSpace M] [T2Space M]
    (φ : A × ℝ → M) (hφ : IsOpenEmbedding φ)
    (r : C(M, M)) (hr : ContinuousMap.Homotopic r (ContinuousMap.id M))
    (hdisjoint : Disjoint (range r) (range (fun y => φ (y, 0)))) :
    ∃ f : C(M, ℝ),
      (∀ y z, f (φ (y, z)) = min 1 (max 0 ((z + 1) / 2)) - 1 / 2) ∧
      ∀ x, f x = 0 ↔ x ∈ range (fun y => φ (y, 0)) := by
  classical
  let : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨q, hq, hq_out⟩ := exists_bicollar_circle_map φ hφ
  have havoid (x : M) : q (r x) ≠ ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) := by
    intro hx
    exact Set.disjoint_left.mp hdisjoint ⟨x, rfl⟩
      ((bicollar_circle_eq_half_iff φ q hq hq_out (r x)).mp hx)
  let θ₀ : C(M, ℝ) :=
    ⟨fun x => (AddCircle.equivIco (1 : ℝ) (1 / 2) (q (r x)) : ℝ), by
      rw [continuous_iff_continuousAt]
      intro x
      exact continuousAt_subtype_val.comp
        ((AddCircle.continuousAt_equivIco (1 : ℝ) (1 / 2) (havoid x)).comp
          (f := fun y : M => q (r y)) (x := x)
          (q.continuous.comp r.continuous).continuousAt)⟩
  have hθ₀ (x : M) : ((θ₀ x : ℝ) : AddCircle (1 : ℝ)) = q (r x) :=
    AddCircle.coe_equivIco (p := (1 : ℝ)) (a := (1 / 2 : ℝ)) (y := q (r x))
  obtain ⟨H⟩ := hr
  let Hq : C(unitInterval × M, AddCircle (1 : ℝ)) := q.comp H.toContinuousMap
  have hHq₀ (x : M) : Hq (0, x) = ((θ₀ x : ℝ) : AddCircle (1 : ℝ)) := by
    change q (H (0, x)) = ((θ₀ x : ℝ) : AddCircle (1 : ℝ))
    rw [H.apply_zero]
    exact (hθ₀ x).symm
  let Θ : C(unitInterval × M, ℝ) :=
    (AddCircle.isCoveringMap_coe (1 : ℝ)).liftHomotopy Hq θ₀ hHq₀
  let θ : C(M, ℝ) :=
    ⟨fun x => Θ (1, x), Θ.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hθq : ((↑) : ℝ → AddCircle (1 : ℝ)) ∘ θ = q := by
    funext x
    have hx := congr_fun
      ((AddCircle.isCoveringMap_coe (1 : ℝ)).liftHomotopy_lifts Hq θ₀ hHq₀) (1, x)
    change ((θ x : ℝ) : AddCircle (1 : ℝ)) = q (H (1, x)) at hx
    simpa only [Function.comp_apply, H.apply_one, ContinuousMap.id_apply] using hx
  let a₀ : A := Classical.arbitrary A
  let θ' : C(M, ℝ) :=
    ⟨fun x => θ x - (θ (φ (a₀, 0)) - 1 / 2), θ.continuous.sub continuous_const⟩
  have hθ'_base : θ' (φ (a₀, 0)) = 1 / 2 := by
    change θ (φ (a₀, 0)) - (θ (φ (a₀, 0)) - 1 / 2) = 1 / 2
    linarith
  have hshift : ((θ (φ (a₀, 0)) - 1 / 2 : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    have hbase : ((θ (φ (a₀, 0)) : ℝ) : AddCircle (1 : ℝ)) = q (φ (a₀, 0)) :=
      congr_fun hθq (φ (a₀, 0))
    rw [AddCircle.coe_sub, hbase, hq]
    norm_num [bicollarPhase]
  have hθ'q : ((↑) : ℝ → AddCircle (1 : ℝ)) ∘ θ' = q := by
    funext x
    change ((θ x - (θ (φ (a₀, 0)) - 1 / 2) : ℝ) : AddCircle (1 : ℝ)) = q x
    rw [AddCircle.coe_sub, hshift, sub_zero]
    exact congr_fun hθq x
  exact exists_bicollar_separating_function_of_lift φ hφ.continuous q hq hq_out
    a₀ θ' hθ'_base hθ'q

theorem path_meets_bicollar_center
    {A M : Type*} [TopologicalSpace A] [T2Space A] [CompactSpace A] [ConnectedSpace A]
    [TopologicalSpace M] [T2Space M] [SimplyConnectedSpace M] [LocallyPathConnectedSpace M]
    (φ : A × ℝ → M) (hφ : IsOpenEmbedding φ)
    (yNeg yPos : A) (zNeg zPos : ℝ) (hzNeg : zNeg < 0) (hzPos : 0 < zPos)
    (γ : Path (φ (yNeg, zNeg)) (φ (yPos, zPos))) :
    ∃ t, γ t ∈ range (fun y => φ (y, 0)) := by
  obtain ⟨f, hfφ, hfzero⟩ := exists_bicollar_separating_function φ hφ
  have hneg : f (γ 0) < 0 := by
    rw [γ.source, hfφ]
    exact sub_neg.mpr ((bicollarPhase_lt_half_iff zNeg).mpr hzNeg)
  have hpos : 0 < f (γ 1) := by
    rw [γ.target, hfφ]
    exact sub_pos.mpr ((half_lt_bicollarPhase_iff zPos).mpr hzPos)
  obtain ⟨t, ht⟩ := intermediate_value_univ (0 : unitInterval) 1
    (f.continuous.comp γ.continuous) ⟨le_of_lt hneg, le_of_lt hpos⟩
  exact ⟨t, (hfzero (γ t)).mp ht⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
