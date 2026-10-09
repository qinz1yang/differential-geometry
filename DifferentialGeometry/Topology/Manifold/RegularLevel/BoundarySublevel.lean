import DifferentialGeometry.Topology.Manifold.RegularLevel.HalfSpaceSliceCharts
import DifferentialGeometry.Topology.Manifold.MFDeriv.Affine

/-!
# Regular sublevels of a manifold with boundary

For `M` modelled on `𝓡∂ (m + 1)`, `f` smooth with regular level `f = r` contained in the interior,
`{f ≤ r}` is a manifold with boundary modelled on `𝓡∂ (m + 1)` with boundary
`(∂M ∩ {f ≤ r}) ∪ {f = r}`; the inclusion is smooth with bijective differential.
-/

set_option autoImplicit false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

open DifferentialGeometry.Manifold.RegularLevel

section ZeroProd

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- A real function with nonzero differential, paired with the zero map to `ℝ⁰`, has
surjective differential. -/
theorem surjective_mfderiv_zero_prod {B : M → ℝ} {x : M}
    (hB : MDifferentiableAt I 𝓘(ℝ, ℝ) B x) (hne : mfderiv I 𝓘(ℝ, ℝ) B x ≠ 0) :
    Surjective (mfderiv I 𝓘(ℝ, (Fin 0 → ℝ) × ℝ) (fun y => ((0 : Fin 0 → ℝ), B y)) x) := by
  let Lm : ℝ →L[ℝ] (Fin 0 → ℝ) × ℝ := ContinuousLinearMap.inr ℝ (Fin 0 → ℝ) ℝ
  let L : E →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) B x
  intro q
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, L v₀ ≠ 0 := by
    by_contra h
    apply hne
    ext v
    by_contra hv
    exact h ⟨v, hv⟩
  let s : ℝ := (q : (Fin 0 → ℝ) × ℝ).2
  refine ⟨(s / L v₀) • v₀, ?_⟩
  have hv : L ((s / L v₀) • v₀) = s := by
    rw [map_smul, smul_eq_mul]
    field_simp
  have hLmc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, (Fin 0 → ℝ) × ℝ) ∞ Lm := Lm.contMDiff
  have hLm : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, (Fin 0 → ℝ) × ℝ) Lm (B x) :=
    hLmc.contMDiffAt.mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp x hLm hB
  have hfun : (fun y => ((0 : Fin 0 → ℝ), B y)) = Lm ∘ B := rfl
  rw [hfun, hcomp, mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
  exact Prod.ext (Subsingleton.elim _ _) hv

end ZeroProd

section BoundarySublevel

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (m + 1)) M]
  [IsManifold (𝓡∂ (m + 1)) ∞ M]

theorem boundarySublevel_sliceCharts (f : M → ℝ) (r : ℝ)
    (hf : ContMDiff (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = r → mfderiv (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
    (hint : ∀ x : M, f x = r → (𝓡∂ (m + 1)).IsInteriorPoint x) :
    ∀ x, f x ≤ r → ∃ p : PartialDiffeomorph (𝓡∂ (m + 1)) ((𝓡∂ (m + 1)).prod 𝓘(ℝ, Fin 0 → ℝ)) M
        (EuclideanHalfSpace (m + 1) × (Fin 0 → ℝ)) ∞ × ℝ,
      0 ≤ p.2 ∧ x ∈ p.1.source ∧
      (∀ y ∈ p.1.source, f y ≤ r ↔ ((p.1 y).2 = 0 ∧ p.2 ≤ (p.1 y).1.1 0)) ∧
      ((p.1 x).1.1 0 = p.2 ↔ ((𝓡∂ (m + 1)).IsBoundaryPoint x ∨ f x = r)) := by
  intro x hx
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) =
      m + 1 + Module.finrank ℝ (Fin 0 → ℝ) := by
    simp
  have hΨ : ContMDiff (𝓡∂ (m + 1)) 𝓘(ℝ, Fin 0 → ℝ) ∞ (fun _ : M => (0 : Fin 0 → ℝ)) :=
    contMDiff_const
  have hB : ContMDiff (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) ∞ (fun y => r - f y) :=
    (contDiff_const.sub contDiff_id).contMDiff.comp hf
  have hiff : ∀ y, ((0 : Fin 0 → ℝ) = 0 ∧ 0 ≤ r - f y) ↔ f y ≤ r := fun y => by
    simp [sub_nonneg]
  by_cases hxr : f x = r
  · have hne : mfderiv (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) (fun y => r - f y) x ≠ 0 := by
      intro h0
      apply hreg x hxr
      have h := DifferentialGeometry.Manifold.mfderiv_const_sub_real
        ((hf x).mdifferentiableAt (by simp)) r
      have h' : -(show EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] ℝ from
          mfderiv (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) f x) = 0 := h.symm.trans h0
      exact neg_eq_zero.mp h'
    obtain ⟨Φ, hxΦ, hΦ1, hΦ⟩ := exists_sliceChart_of_zero hdim hΨ hB (hint x hxr)
      (by rw [hxr, sub_self]) (surjective_mfderiv_zero_prod ((hB x).mdifferentiableAt (by simp)) hne)
    refine ⟨(Φ, 1), zero_le_one, hxΦ, fun y hy => (hiff y).symm.trans (hΦ y hy), ?_⟩
    exact iff_of_true hΦ1 (Or.inr hxr)
  · have hlt : f x < r := lt_of_le_of_ne hx hxr
    by_cases hb : (𝓡∂ (m + 1)).IsBoundaryPoint x
    · obtain ⟨Φ, hxΦ, hsub, hbd⟩ := exists_sliceChart_restrict (m := m) x
        (isOpen_lt hf.continuous continuous_const) hlt
      refine ⟨(Φ, 0), le_rfl, hxΦ, fun y hy => ?_, ?_⟩
      · exact iff_of_true (le_of_lt (hsub hy)) ⟨Subsingleton.elim _ _, (Φ y).1.2⟩
      · exact hbd.trans (or_iff_left hxr).symm
    · have hint' : (𝓡∂ (m + 1)).IsInteriorPoint x :=
        ((𝓡∂ (m + 1)).isInteriorPoint_iff_not_isBoundaryPoint x).mpr hb
      obtain ⟨Φ, hxΦ, hΦpos, hΦ⟩ := exists_sliceChart_of_pos hdim hΨ hB hint' (sub_pos.mpr hlt)
        (fun q => ⟨0, Subsingleton.elim (α := Fin 0 → ℝ) _ _⟩)
      refine ⟨(Φ, 0), le_rfl, hxΦ, fun y hy => (hiff y).symm.trans (hΦ y hy), ?_⟩
      exact iff_of_false (hΦpos x hxΦ).ne' (fun h => h.elim hb hxr)

/-- The manifold-with-boundary structure on `{f ≤ r}` (ambient with boundary, regular level
`f = r` inside the interior). -/
@[reducible]
def boundarySublevelChartedSpace (f : M → ℝ) (r : ℝ)
    (hf : ContMDiff (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = r → mfderiv (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
    (hint : ∀ x : M, f x = r → (𝓡∂ (m + 1)).IsInteriorPoint x) :
    ChartedSpace (EuclideanHalfSpace (m + 1)) {x : M // f x ≤ r} :=
  sliceChartedSpace (fun x => f x ≤ r) (fun x => (𝓡∂ (m + 1)).IsBoundaryPoint x ∨ f x = r)
    (boundarySublevel_sliceCharts f r hf hreg hint)

variable (f : M → ℝ) (r : ℝ) (hf : ContMDiff (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) ∞ f)
  (hreg : ∀ x : M, f x = r → mfderiv (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
  (hint : ∀ x : M, f x = r → (𝓡∂ (m + 1)).IsInteriorPoint x)

theorem boundarySublevel_isManifold :
    letI := boundarySublevelChartedSpace f r hf hreg hint
    IsManifold (𝓡∂ (m + 1)) ∞ {x : M // f x ≤ r} :=
  slice_isManifold _ _ (boundarySublevel_sliceCharts f r hf hreg hint)

variable {f r} in
theorem boundarySublevel_isBoundaryPoint_iff {x : {x : M // f x ≤ r}} :
    letI := boundarySublevelChartedSpace f r hf hreg hint
    (𝓡∂ (m + 1)).IsBoundaryPoint x ↔ ((𝓡∂ (m + 1)).IsBoundaryPoint x.1 ∨ f x.1 = r) :=
  slice_isBoundaryPoint_iff (boundarySublevel_sliceCharts f r hf hreg hint)

theorem boundarySublevel_contMDiff_val :
    letI := boundarySublevelChartedSpace f r hf hreg hint
    ContMDiff (𝓡∂ (m + 1)) (𝓡∂ (m + 1)) ∞ (fun x : {x : M // f x ≤ r} => x.1) :=
  slice_contMDiff_val _ _ (boundarySublevel_sliceCharts f r hf hreg hint)

theorem boundarySublevel_mfderiv_val_bijective (x : {x : M // f x ≤ r}) :
    letI := boundarySublevelChartedSpace f r hf hreg hint
    Bijective (mfderiv (𝓡∂ (m + 1)) (𝓡∂ (m + 1)) (fun y : {x : M // f x ≤ r} => y.1) x) :=
  slice_mfderiv_val_bijective _ _ (boundarySublevel_sliceCharts f r hf hreg hint) (by simp) x

variable {f r} in
theorem boundarySublevel_contMDiff_iff {F' G' N : Type*} [NormedAddCommGroup F']
    [NormedSpace ℝ F'] [TopologicalSpace G'] {J : ModelWithCorners ℝ F' G'} [TopologicalSpace N]
    [ChartedSpace G' N] {n : ℕ∞} {g : N → {x : M // f x ≤ r}} :
    letI := boundarySublevelChartedSpace f r hf hreg hint
    ContMDiff J (𝓡∂ (m + 1)) n g ↔ ContMDiff J (𝓡∂ (m + 1)) n (fun z => (g z : M)) :=
  slice_contMDiff_iff (boundarySublevel_sliceCharts f r hf hreg hint)
    (WithTop.coe_le_coe.mpr le_top)

omit [IsManifold (𝓡∂ (m + 1)) ∞ M] in
/-- Row E6(ii) of lane B-3b, in the requested existential form. -/
theorem exists_isManifold_sublevel_of_boundary
    {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (m + 1)) M]
    [IsManifold (𝓡∂ (m + 1)) ∞ M]
    (f : M → ℝ) (r : ℝ) (hf : ContMDiff (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = r → mfderiv (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
    (hint : ∀ x : M, f x = r → (𝓡∂ (m + 1)).IsInteriorPoint x) :
    ∃ cs : ChartedSpace (EuclideanHalfSpace (m + 1)) {x : M // f x ≤ r},
      letI := cs
      IsManifold (𝓡∂ (m + 1)) ∞ {x : M // f x ≤ r} ∧
      ContMDiff (𝓡∂ (m + 1)) (𝓡∂ (m + 1)) ∞ (fun x : {x : M // f x ≤ r} => x.1) ∧
      (∀ x : {x : M // f x ≤ r}, Function.Bijective
        (mfderiv (𝓡∂ (m + 1)) (𝓡∂ (m + 1)) (fun y : {x : M // f x ≤ r} => y.1) x)) ∧
      (∀ x : {x : M // f x ≤ r}, (𝓡∂ (m + 1)).IsBoundaryPoint x ↔
        ((𝓡∂ (m + 1)).IsBoundaryPoint x.1 ∨ f x.1 = r)) :=
  ⟨boundarySublevelChartedSpace f r hf hreg hint, boundarySublevel_isManifold f r hf hreg hint,
    boundarySublevel_contMDiff_val f r hf hreg hint,
    boundarySublevel_mfderiv_val_bijective f r hf hreg hint,
    fun x => boundarySublevel_isBoundaryPoint_iff hf hreg hint (x := x)⟩

end BoundarySublevel

end DifferentialGeometry.Topology.Manifold
