import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.FamilyIsotopyFlow

/-!
# CP1-D5: isotopy extension for a smooth family of embeddings of a compact set (main theorem)
-/

set_option autoImplicit false
open scoped Manifold ContDiff Topology
open Set Function Filter Bundle
noncomputable section
namespace GC.LongTime.CuspP1

theorem exists_thickening_Icc_subset_CPD5 {J : Set ℝ} (hJ : IsOpen J) {a b : ℝ} (hab : a ≤ b)
    (hJab : Icc a b ⊆ J) : ∃ δ : ℝ, 0 < δ ∧ Icc (a - 2 * δ) (b + 2 * δ) ⊆ J := by
  obtain ⟨ε, hε, hsub⟩ := isCompact_Icc.exists_cthickening_subset_open hJ hJab
  refine ⟨ε / 2, by positivity, fun y hy => hsub ?_⟩
  have h1 := hy.1
  have h2 := hy.2
  refine Metric.mem_cthickening_of_dist_le y (max a (min y b)) ε _
    ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩ ?_
  rw [Real.dist_eq, abs_le]
  constructor <;> rcases le_total y b with h | h <;> rcases le_total a y with h' | h' <;>
    simp [*] <;> linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Isotopy extension for a smooth family of embeddings of a compact set.** -/
theorem exists_ambient_isotopy_of_smooth_family_CPD5 [T2Space M] [SigmaCompactSpace M]
    {F : ℝ × N → M} {J : Set ℝ} {U : Set N} (hJ : IsOpen J) (hU : IsOpen U)
    {K : Set N} (hK : IsCompact K) (hKU : K ⊆ U) {a b : ℝ} (hab : a ≤ b)
    (hJab : Icc a b ⊆ J)
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ F (J ×ˢ U))
    (himm : ∀ t ∈ J, ∀ x ∈ U, Function.Injective (mfderiv I I (fun y => F (t, y)) x))
    (hinj : ∀ t ∈ J, InjOn (fun y => F (t, y)) K) :
    ∃ (Φ : ℝ → ℝ → M → M) (C : Set M), IsCompact C ∧
      ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I ∞
        (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2) ∧
      (∀ s y, Φ s s y = y) ∧ (∀ s t u y, Φ t u (Φ s t y) = Φ s u y) ∧
      (∀ s t y, y ∉ C → Φ s t y = y) ∧
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ x ∈ K, Φ s t (F (s, x)) = F (t, x) := by
  obtain ⟨δ, hδ, hJ2⟩ := exists_thickening_Icc_subset_CPD5 hJ hab hJab
  obtain ⟨W, C, hCc, hWsm, hWsupp, hWF⟩ := exists_field_CPD5 hJ hU hK hKU
    (c := a - 2 * δ) (d := b + 2 * δ) hJ2 hF himm hinj
  obtain ⟨Φ, h1, h2, h3, h4, h5⟩ := exists_ambient_isotopy_of_field_CPD5 hJ hU hKU hδ hab hJ2 hF
    W hCc hWsm hWsupp hWF
  exact ⟨Φ, C, hCc, h1, h2, h3, h4, h5⟩

/-- the homeomorphisms of an isotopy -/
def isotopyHomeo_CPD5 {M : Type*} [TopologicalSpace M] (Φ : ℝ → ℝ → M → M)
    (hc : Continuous fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2)
    (hself : ∀ s y, Φ s s y = y) (hcoc : ∀ s t u y, Φ t u (Φ s t y) = Φ s u y) (s t : ℝ) :
    M ≃ₜ M where
  toFun := Φ s t
  invFun := Φ t s
  left_inv y := by rw [hcoc, hself]
  right_inv y := by rw [hcoc, hself]
  continuous_toFun := hc.comp (f := fun y : M => ((s, t), y)) (by fun_prop)
  continuous_invFun := hc.comp (f := fun y : M => ((t, s), y)) (by fun_prop)

@[simp] theorem isotopyHomeo_apply_CPD5 {M : Type*} [TopologicalSpace M] (Φ : ℝ → ℝ → M → M)
    (hc : Continuous fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2)
    (hself : ∀ s y, Φ s s y = y) (hcoc : ∀ s t u y, Φ t u (Φ s t y) = Φ s u y) (s t : ℝ) (y : M) :
    isotopyHomeo_CPD5 Φ hc hself hcoc s t y = Φ s t y := rfl

end GC.LongTime.CuspP1
