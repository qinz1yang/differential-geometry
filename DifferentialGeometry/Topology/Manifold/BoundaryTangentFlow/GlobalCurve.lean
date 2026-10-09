import DifferentialGeometry.Topology.Manifold.BoundaryIntegralCurve
import Mathlib.Geometry.Manifold.IntegralCurve.Transform

/-!
# Uniform time lemma for integral curves on manifolds with boundary

Mathlib's `exists_isMIntegralCurve_of_isMIntegralCurveOn` (`IntegralCurve/UniformTime.lean`) assumes
`[BoundarylessManifold I M]` only to use uniqueness of integral curves. The tree proves that
uniqueness for manifolds with boundary (`Topology/Manifold/BoundaryIntegralCurve.lean:133`,
`isMIntegralCurveOn_Ioo_eqOn`); this file repeats Mathlib's argument (Lee, Lemma 9.15) with it:
if every point has an integral curve on a common interval `(-ε, ε)`, every point has a global
integral curve (`exists_isMIntegralCurve_of_uniform_Ioo`), and global integral curves through the
same point agree (`isMIntegralCurve_eq_of_eq`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Topology Manifold

namespace DifferentialGeometry.Manifold.BoundaryTangentFlow

open DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [T2Space M]
  {γ γ' : ℝ → M} {v : (x : M) → TangentSpace I x} {t₀ : ℝ}

/-- Uniqueness for a family of integral curves with a common starting point. -/
theorem eqOn_family_of_isMIntegralCurveOn_Ioo
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) {x : M}
    (γ : ℝ → ℝ → M) (hγx : ∀ a, γ a 0 = x)
    (hγ : ∀ a > 0, IsMIntegralCurveOn (γ a) v (Ioo (-a) a))
    {a a' : ℝ} (hpos : 0 < a') (hle : a' ≤ a) :
    EqOn (γ a') (γ a) (Ioo (-a') a') := by
  apply isMIntegralCurveOn_Ioo_eqOn _ hv
    (hγ a' (by positivity)) ((hγ a (lt_of_lt_of_le hpos hle)).mono _)
    (by rw [hγx a, hγx a'])
  · rw [mem_Ioo]
    exact ⟨neg_lt_zero.mpr hpos, by positivity⟩
  · apply Ioo_subset_Ioo <;> linarith

/-- The diagonal curve `t ↦ γ (|t| + 1) t` agrees with each member of the family. -/
theorem eqOn_abs_add_one_family
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) {x : M}
    (γ : ℝ → ℝ → M) (hγx : ∀ a, γ a 0 = x)
    (hγ : ∀ a > 0, IsMIntegralCurveOn (γ a) v (Ioo (-a) a))
    {a : ℝ} : EqOn (fun t ↦ γ (|t| + 1) t) (γ a) (Ioo (-a) a) := by
  intro t ht
  by_cases! hlt : |t| + 1 < a
  · exact eqOn_family_of_isMIntegralCurveOn_Ioo hv γ hγx hγ
      (by positivity) hlt.le (abs_lt.mp <| lt_add_one _)
  · exact eqOn_family_of_isMIntegralCurveOn_Ioo hv γ hγx hγ
      (neg_lt_self_iff.mp <| lt_trans ht.1 ht.2) hlt ht |>.symm

/-- The diagonal curve of a family of local integral curves is a global integral curve. -/
theorem isMIntegralCurve_abs_add_one_family
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) {x : M}
    (γ : ℝ → ℝ → M) (hγx : ∀ a, γ a 0 = x)
    (hγ : ∀ a > 0, IsMIntegralCurveOn (γ a) v (Ioo (-a) a)) :
    IsMIntegralCurve (fun t ↦ γ (|t| + 1) t) v := by
  intro t
  have ht : t ∈ Ioo (-(|t| + 1)) (|t| + 1) := by
    rw [mem_Ioo, ← abs_lt]
    exact lt_add_one _
  apply HasMFDerivAt.congr_of_eventuallyEq_abuse (f := γ (|t| + 1))
  · exact hγ (|t| + 1) (by positivity) _ ht |>.hasMFDerivAt (Ioo_mem_nhds ht.1 ht.2)
  · rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Ioo (-(|t| + 1)) (|t| + 1), ?_,
      eqOn_abs_add_one_family hv γ hγx hγ⟩
    have : |t| < |t| + 1 := lt_add_of_pos_right |t| zero_lt_one
    rw [abs_lt] at this
    exact Ioo_mem_nhds this.1 this.2

/-- Global integral curves exist iff integral curves on every symmetric interval exist. -/
theorem exists_isMIntegralCurve_iff_forall_Ioo
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) {x : M} :
    (∃ γ, γ 0 = x ∧ IsMIntegralCurve γ v) ↔
      ∀ a, ∃ γ, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-a) a) := by
  refine ⟨fun ⟨γ, h1, h2⟩ _ ↦ ⟨γ, h1, h2.isMIntegralCurveOn _⟩, fun h ↦ ?_⟩
  choose γ hγx hγ using h
  exact ⟨fun t ↦ γ (|t| + 1) t, hγx (|0| + 1),
    isMIntegralCurve_abs_add_one_family hv γ hγx (fun a _ ↦ hγ a)⟩

/-- A piecewise combination of two overlapping integral curves agrees with the second one on its
interval. -/
theorem eqOn_piecewise_Ioo
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    {a b a' b' : ℝ} (hγ : IsMIntegralCurveOn γ v (Ioo a b))
    (hγ' : IsMIntegralCurveOn γ' v (Ioo a' b'))
    (ht₀ : t₀ ∈ Ioo a b ∩ Ioo a' b') (h : γ t₀ = γ' t₀) :
    EqOn (piecewise (Ioo a b) γ γ') γ' (Ioo a' b') := by
  intro t ht
  suffices H : EqOn γ γ' (Ioo (max a a') (min b b')) by
    by_cases hmem : t ∈ Ioo a b
    · rw [piecewise, ite_eq_left hmem]
      apply H
      simp [ht.1, ht.2, hmem.1, hmem.2]
    · rw [piecewise, ite_eq_right hmem]
  apply isMIntegralCurveOn_Ioo_eqOn _ hv
    (hγ.mono (Ioo_subset_Ioo (le_max_left ..) (min_le_left ..)))
    (hγ'.mono (Ioo_subset_Ioo (le_max_right ..) (min_le_right ..))) h
  exact ⟨max_lt ht₀.1.1 ht₀.2.1, lt_min ht₀.1.2 ht₀.2.2⟩

/-- Two overlapping integral curves agreeing at a point glue to an integral curve. -/
theorem isMIntegralCurveOn_piecewise_Ioo
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    {a b a' b' : ℝ} (hγ : IsMIntegralCurveOn γ v (Ioo a b))
    (hγ' : IsMIntegralCurveOn γ' v (Ioo a' b'))
    (ht₀ : t₀ ∈ Ioo a b ∩ Ioo a' b') (h : γ t₀ = γ' t₀) :
    IsMIntegralCurveOn (piecewise (Ioo a b) γ γ') v (Ioo a b ∪ Ioo a' b') := by
  intro t ht
  by_cases hmem : t ∈ Ioo a b
  · rw [piecewise, ite_eq_left hmem]
    apply hγ t hmem |>.hasMFDerivAt (Ioo_mem_nhds hmem.1 hmem.2) |>.hasMFDerivWithinAt
      (s := Ioo a b ∪ Ioo a' b') |>.congr_of_eventuallyEq _ (by rw [piecewise, ite_eq_left hmem])
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Ioo a b, ?_, fun _ ht' ↦ by rw [piecewise, ite_eq_left ht']⟩
    rw [(isOpen_Ioo.union isOpen_Ioo).nhdsWithin_eq ht]
    exact Ioo_mem_nhds hmem.1 hmem.2
  · have ht' := ht
    rw [mem_union, or_iff_not_imp_left] at ht
    rw [piecewise, ite_eq_right hmem]
    apply hγ' t (ht hmem) |>.hasMFDerivAt (Ioo_mem_nhds (ht hmem).1 (ht hmem).2)
      |>.hasMFDerivWithinAt (s := Ioo a b ∪ Ioo a' b')
      |>.congr_of_eventuallyEq _ (by rw [piecewise, ite_eq_right hmem])
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Ioo a' b', ?_, eqOn_piecewise_Ioo hv hγ hγ' ht₀ h⟩
    rw [(isOpen_Ioo.union isOpen_Ioo).nhdsWithin_eq ht']
    exact Ioo_mem_nhds (ht hmem).1 (ht hmem).2

/-- **Uniform time lemma with boundary.** If every point has an integral curve on `(-ε, ε)`, every
point has a global integral curve. -/
theorem exists_isMIntegralCurve_of_uniform_Ioo
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    {ε : ℝ} (hε : 0 < ε)
    (h : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-ε) ε))
    (x : M) : ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v := by
  let s := { a | ∃ γ, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-a) a) }
  suffices hbdd : ¬BddAbove s by
    rw [not_bddAbove_iff] at hbdd
    rw [exists_isMIntegralCurve_iff_forall_Ioo hv]
    intro a
    obtain ⟨y, ⟨γ, hγ1, hγ2⟩, hlt⟩ := hbdd a
    exact ⟨γ, hγ1, hγ2.mono <| Ioo_subset_Ioo (neg_le_neg hlt.le) hlt.le⟩
  intro hbdd
  set asup := sSup s with hasup
  obtain ⟨a, ha, hlt⟩ := Real.add_neg_lt_sSup (⟨ε, h x⟩ : Set.Nonempty s) (ε := - (ε / 2))
    (by rw [neg_lt, neg_zero]; exact half_pos hε)
  rw [mem_ofPred] at ha
  rw [← hasup, ← sub_eq_add_neg] at hlt
  obtain ⟨γ, h0, hγ⟩ := ha
  obtain ⟨γ1_aux, h1_aux, hγ1⟩ := h (γ (-(asup - ε / 2)))
  rw [← isMIntegralCurveOn_comp_add (dt := asup - ε / 2)] at hγ1
  set γ1 := γ1_aux ∘ (· + (asup - ε / 2)) with γ1_def
  have heq1 : γ1 (-(asup - ε / 2)) = γ (-(asup - ε / 2)) := by simp [γ1_def, h1_aux]
  obtain ⟨γ2_aux, h2_aux, hγ2⟩ := h (γ (asup - ε / 2))
  rw [← isMIntegralCurveOn_comp_sub (dt := asup - ε / 2)] at hγ2
  set γ2 := γ2_aux ∘ (· - (asup - ε / 2)) with γ2_def
  have heq2 : γ2 (asup - ε / 2) = γ (asup - ε / 2) := by simp [γ2_def, h2_aux]
  simp_rw [Set.mem_Ioo, ← sub_lt_iff_lt_add, ← lt_sub_iff_add_lt, ← Set.mem_Ioo] at hγ1
  simp_rw [Set.mem_Ioo, lt_sub_iff_add_lt, sub_lt_iff_lt_add, ← Set.mem_Ioo] at hγ2
  have hεle : ε ≤ asup := le_csSup hbdd (h x)
  set γ_ext : ℝ → M := piecewise (Ioo (-(asup + ε / 2)) a)
    (piecewise (Ioo (-a) a) γ γ1) γ2 with γ_ext_def
  have heq_ext : γ_ext 0 = x := by
    rw [γ_ext_def, piecewise, ite_eq_left ⟨by linarith, by linarith⟩, piecewise,
      ite_eq_left ⟨by linarith, by linarith⟩, h0]
  suffices hext : IsMIntegralCurveOn γ_ext v (Ioo (-(asup + ε / 2)) (asup + ε / 2)) from
    (not_lt.mpr <| le_csSup hbdd ⟨γ_ext, heq_ext, hext⟩) <| lt_add_of_pos_right asup (half_pos hε)
  apply (isMIntegralCurveOn_piecewise_Ioo (t₀ := asup - ε / 2) hv _ hγ2
      ⟨⟨by linarith, hlt⟩, ⟨by linarith, by linarith⟩⟩
      (by rw [piecewise, ite_eq_left ⟨by linarith, hlt⟩, ← heq2])).mono
    (Ioo_subset_Ioo_union_Ioo le_rfl (by linarith) (by linarith))
  exact (isMIntegralCurveOn_piecewise_Ioo (t₀ := -(asup - ε / 2)) hv hγ hγ1
      ⟨⟨neg_lt_neg hlt, by linarith⟩, ⟨by linarith, by linarith⟩⟩ heq1.symm).mono
    (union_comm _ _ ▸ Ioo_subset_Ioo_union_Ioo (by linarith) (by linarith) le_rfl)

/-- Two global integral curves agreeing at one time agree everywhere. -/
theorem isMIntegralCurve_eq_of_eq
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsMIntegralCurve γ v) (hγ' : IsMIntegralCurve γ' v) (h : γ t₀ = γ' t₀) :
    γ = γ' := by
  funext t
  have hR : t₀ ∈ Ioo (-(|t| + |t₀| + 1)) (|t| + |t₀| + 1) := by
    rw [mem_Ioo, ← abs_lt]
    linarith [abs_nonneg t]
  have ht : t ∈ Ioo (-(|t| + |t₀| + 1)) (|t| + |t₀| + 1) := by
    rw [mem_Ioo, ← abs_lt]
    linarith [abs_nonneg t₀]
  exact isMIntegralCurveOn_Ioo_eqOn hR hv (hγ.isMIntegralCurveOn _) (hγ'.isMIntegralCurveOn _) h ht

end DifferentialGeometry.Manifold.BoundaryTangentFlow
