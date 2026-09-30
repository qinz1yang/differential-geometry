import DifferentialGeometry.Topology.PiecewiseLinear.Section34ActualSeamCorrection
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FillingCollarRibbonTraces
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CollaredFillingCylinderSquare

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem image_cylinder_region_of_circle_reparametrization
    {A B E : Type*} {F : A × ℝ → E} {f : B × ℝ → E} {η : ℝ → A} {v : ℝ → B}
    {ν : (Fin 3 → ℝ) → (Fin 3 → ℝ)}
    (hν : BijOn ν (stdSimplexBoundary 2) (stdSimplexBoundary 2)) {T : Set ℝ}
    (hformula : ∀ r ∈ T, ∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
      ν (stdTriangleLoop s) = stdTriangleLoop q → F (η r, s) = f (v r, q)) :
    F '' ((η '' T) ×ˢ Icc (0 : ℝ) 1) = f '' ((v '' T) ×ˢ Icc (0 : ℝ) 1) := by
  apply Subset.antisymm
  · rintro y ⟨⟨p, s⟩, ⟨⟨r, hr, rfl⟩, hs⟩, rfl⟩
    have hz := hν.mapsTo (stdTriangleLoop_image.subset (mem_image_of_mem stdTriangleLoop hs))
    obtain ⟨q, hq, heq⟩ := stdTriangleLoop_image.symm.subset hz
    exact ⟨(v r, q), ⟨mem_image_of_mem v hr, hq⟩, (hformula r hr s hs q hq heq.symm).symm⟩
  · rintro y ⟨⟨p, q⟩, ⟨⟨r, hr, rfl⟩, hq⟩, rfl⟩
    obtain ⟨z, hz, hzq⟩ :=
      hν.surjOn (stdTriangleLoop_image.subset (mem_image_of_mem stdTriangleLoop hq))
    obtain ⟨s, hs, rfl⟩ := stdTriangleLoop_image.symm.subset hz
    exact ⟨(η r, s), ⟨mem_image_of_mem η hr, hs⟩, hformula r hr s hs q hq hzq⟩

theorem synchronized_exterior_shell_ribbon_formulas
    {E : Type*} {g H f : (ℝ × ℝ) × ℝ → E} {ρ : E × ℝ → E}
    {γ : ℝ → ℝ × ℝ} {ν : (Fin 3 → ℝ) → (Fin 3 → ℝ)}
    {L : Set E} {c e : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) (hce : c / 2 ≤ e)
    (a b : Bool)
    (hγ : MapsTo γ (Icc (-e) e) (frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)))
    (hshell : ∀ p ∈ frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1),
      ∀ r ∈ Icc (0 : ℝ) c, ∀ s ∈ Icc (0 : ℝ) 1,
        H (section34SquareShellFlatten c (p, r), s) = ρ (g (p, s), r))
    (hpos : ∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
      ν (stdTriangleLoop s) = stdTriangleLoop q →
      ∀ t ∈ Icc (0 : ℝ) e, g (γ t, s) = f (t • fourSpokeModelLeaf (if a then 0 else 2), q))
    (hneg : ∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
      ν (stdTriangleLoop s) = stdTriangleLoop q → ∀ t ∈ Icc (-e) 0,
        g (γ t, s) = f ((-t) • fourSpokeModelLeaf (if b then 1 else 3), q))
    (hfeet : ∀ r ∈ Icc (0 : ℝ) c, ∀ q ∈ Icc (0 : ℝ) 1,
      f ((0, if b then r / 2 else -r / 2), q) ∈ L ∧
        f ((if a then r / 2 else -r / 2, 0), q) ∈ L)
    (hread : ∀ p ∈ section34CornerBase a b, ∀ q ∈ Icc (0 : ℝ) 1,
      f (p, q) ∈ L → ∀ r ∈ Icc (0 : ℝ) c,
        ρ (f (p, q), r) = f (section34CornerExteriorPush a b (p, r), q)) :
    ∀ r ∈ Icc (0 : ℝ) c, ∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
      ν (stdTriangleLoop s) = stdTriangleLoop q →
      H (section34SquareShellFlatten c (γ (-r / 2), r), s) =
        f ((if a then -r / 2 else r / 2, 0), q) ∧
      H (section34SquareShellFlatten c (γ (r / 2), r), s) =
        f ((0, if b then -r / 2 else r / 2), q) := by
  intro r hr s hs q hq heq
  have he : 0 ≤ e := (div_nonneg hc (by norm_num)).trans hce
  have htp : r / 2 ∈ Icc (0 : ℝ) e := ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have htn : -r / 2 ∈ Icc (-e) 0 := ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have hp : (0, if b then r / 2 else -r / 2) ∈ section34CornerBase a b := by
    right
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, mem_prod,
      mem_singleton_iff, mem_Icc, true_and] <;> constructor <;> linarith [hr.1, hr.2]
  have hn : (if a then r / 2 else -r / 2, 0) ∈ section34CornerBase a b := by
    left
    cases a <;> simp only [Bool.false_eq_true, ↓reduceIte, mem_prod,
      mem_singleton_iff, mem_Icc, and_true] <;> constructor <;> linarith [hr.1, hr.2]
  have hnegFoot : (-(-r / 2)) • fourSpokeModelLeaf (if b then 1 else 3) =
      (0, if b then r / 2 else -r / 2) := by
    cases b <;> simp [fourSpokeModelLeaf]
    ring
  have hposFoot : (r / 2) • fourSpokeModelLeaf (if a then 0 else 2) =
      (if a then r / 2 else -r / 2, 0) := by
    cases a <;> simp [fourSpokeModelLeaf]
    ring
  constructor
  · rw [hshell _ (hγ ⟨htn.1, htn.2.trans he⟩) r hr s hs,
      hneg s hs q hq heq _ htn, hnegFoot, hread _ hp q hq (hfeet r hr q hq).1 r hr]
    congr 1
    apply Prod.ext
    · apply Prod.ext <;> cases a <;> cases b <;>
        simp [section34CornerExteriorPush, section34CornerPush] <;> ring
    · rfl
  · rw [hshell _ (hγ ⟨(neg_nonpos.mpr he).trans htp.1, htp.2⟩) r hr s hs,
      hpos s hs q hq heq _ htp, hposFoot, hread _ hn q hq (hfeet r hr q hq).2 r hr]
    congr 1
    apply Prod.ext
    · apply Prod.ext <;> cases a <;> cases b <;>
        simp [section34CornerExteriorPush, section34CornerPush] <;> ring
    · rfl

end DifferentialGeometry.Topology.PiecewiseLinear
