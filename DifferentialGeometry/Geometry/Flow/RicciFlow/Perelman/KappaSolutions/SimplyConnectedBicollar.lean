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
  have hθφ : (fun p : A × ℝ => θ (φ p)) = fun p => bicollarPhase p.2 := by
    refine (AddCircle.isCoveringMap_coe (1 : ℝ)).eq_of_comp_eq
      (θ.continuous.comp hφ.continuous) (bicollarPhase_continuous.comp continuous_snd)
      ?_ (a₀, 0) ?_
    · funext p
      exact (congr_fun hθq (φ p)).trans (hq p)
    · have hphase : bicollarPhase 0 = 1 / 2 := by norm_num [bicollarPhase]
      simpa only [hphase] using hθ_base
  have hhalf : ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) ≠ 0 := by
    have : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
    intro h
    have hz := (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (p := (1 : ℝ)) (a := 0)
      (x := (1 / 2 : ℝ)) (y := (0 : ℝ)) (by norm_num) (by norm_num)).mp h
    norm_num at hz
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
        exact False.elim (hhalf h)
    · rintro ⟨y, rfl⟩
      change θ (φ (y, 0)) - 1 / 2 = 0
      rw [congr_fun hθφ (y, 0)]
      norm_num [bicollarPhase]

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
