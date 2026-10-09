import DifferentialGeometry.Topology.Surface.Recognition.DiskParamOfFibreBCF
import DifferentialGeometry.Topology.Surface.Recognition.BaseCurvePiecesBCF

/-!
# The horizontal disks and their rims over the base curve (lane S-BCF03b; BCF03 G7, P4 / P5)

Abstract kernel: `Bd = ∂M₂`, `Rc = R_c`, `He = Bd ∩ X₂` the horizontal face, `fib₁ y = X₂ ∩ f₂⁻¹{y}`
the edge fibres (whole closed disks with the unit circle onto the rim `{T = c}`),
`fib₀ b = X₁ ∩ f₁⁻¹{b}` the circle fibres. From the F1 identity (the rim of an edge disk is ONE
whole circle fibre) and the face partition `P_e ∩ R_c = V_e` one gets, for every horizontal
disk over `y`:

* `exists_rimBase_BCF`: the rim is nonempty, lies in `Bd ∩ Rc`, and equals the circle fibre over a
  point `b` of the base curve (`rim_eq_fibre`, `f₁ = b` on it);
* `isCompact_edgeDisk_BCF`: the disk is compact (hence closed);
* `rimBase_injOn_BCF`: distinct horizontal disks have distinct rim base points.
-/

set_option autoImplicit false

open Set Function Topology

noncomputable section

namespace DifferentialGeometry.Topology.Surface

open DifferentialGeometry.Topology

section Disks

variable {Wt H : Type*} [TopologicalSpace Wt] {fib₀ fib₁ : H → Set Wt} {f₁ f₂ : Wt → H}
  {T : Wt → ℝ} {c : ℝ} {X₁ X₂ Bd Rc : Set Wt}

/-- The rim of the edge disk over `y`. -/
def rim_BCF (fib₁ : H → Set Wt) (T : Wt → ℝ) (c : ℝ) (y : H) : Set Wt :=
  fib₁ y ∩ {q | T q = c}

/-- A closed `2`-cell has a point of norm `1`. -/
theorem exists_norm_one_closedCell_BCF : ∃ x : ClosedCell 2, ‖x.1‖ = 1 :=
  ⟨⟨EuclideanSpace.single 0 1, by simp⟩, by simp⟩

theorem isCompact_edgeDisk_BCF
    (hdisk : ∀ p ∈ Bd ∩ X₂, ∃ ed : fib₁ (f₂ p) ≃ₜ ClosedCell 2,
      Subtype.val '' (ed ⁻¹' {x : ClosedCell 2 | ‖x.1‖ = 1}) = rim_BCF fib₁ T c (f₂ p))
    {y : H} (hy : y ∈ f₂ '' (Bd ∩ X₂)) : IsCompact (fib₁ y) := by
  obtain ⟨p, hp, rfl⟩ := hy
  obtain ⟨ed, -⟩ := hdisk p hp
  exact isCompact_of_homeomorph_closedCell_BCF ed

theorem isPreconnected_edgeDisk_BCF
    (hdisk : ∀ p ∈ Bd ∩ X₂, ∃ ed : fib₁ (f₂ p) ≃ₜ ClosedCell 2,
      Subtype.val '' (ed ⁻¹' {x : ClosedCell 2 | ‖x.1‖ = 1}) = rim_BCF fib₁ T c (f₂ p))
    {y : H} (hy : y ∈ f₂ '' (Bd ∩ X₂)) : IsPreconnected (fib₁ y) := by
  obtain ⟨p, hp, rfl⟩ := hy
  obtain ⟨h, hc, -, hr, -⟩ := exists_diskParam_of_fibre_BCF (hdisk p hp).choose
    (hdisk p hp).choose_spec
  rw [← hr]
  have : PreconnectedSpace (Disk 2) := by
    have hconv : Convex ℝ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      convex_closedBall _ _
    exact Subtype.preconnectedSpace hconv.isPreconnected
  exact isPreconnected_range hc

/-- **The rim of a horizontal disk is one whole circle fibre over a point of the base curve.** -/
theorem exists_rimBase_BCF (hfib₀ : ∀ y, fib₀ y = X₁ ∩ f₁ ⁻¹' {y})
    (hdisk : ∀ p ∈ Bd ∩ X₂, ∃ ed : fib₁ (f₂ p) ≃ₜ ClosedCell 2,
      Subtype.val '' (ed ⁻¹' {x : ClosedCell 2 | ‖x.1‖ = 1}) = rim_BCF fib₁ T c (f₂ p))
    (hF1 : ∀ p ∈ Bd ∩ X₂, T p = c → rim_BCF fib₁ T c (f₂ p) = fib₀ (f₁ p))
    (hrim : ∀ p ∈ Bd ∩ X₂, p ∈ Rc ↔ T p = c)
    (hHe : ∀ p ∈ Bd ∩ X₂, ∀ q ∈ X₂, f₂ q = f₂ p → q ∈ Bd ∩ X₂)
    (hfib₁ : ∀ y, fib₁ y = X₂ ∩ f₂ ⁻¹' {y}) {y : H} (hy : y ∈ f₂ '' (Bd ∩ X₂)) :
    ∃ b : H, rim_BCF fib₁ T c y = fib₀ b ∧ (rim_BCF fib₁ T c y).Nonempty ∧
      rim_BCF fib₁ T c y ⊆ Bd ∩ Rc ∧ ∀ q ∈ rim_BCF fib₁ T c y, f₁ q = b := by
  obtain ⟨p, hp, rfl⟩ := hy
  obtain ⟨ed, hed⟩ := hdisk p hp
  obtain ⟨x, hx⟩ := exists_norm_one_closedCell_BCF
  have hq₀ : ((ed.symm x : fib₁ (f₂ p)) : Wt) ∈ rim_BCF fib₁ T c (f₂ p) := by
    rw [← hed]
    exact ⟨ed.symm x, by simpa using hx, rfl⟩
  have hsub : rim_BCF fib₁ T c (f₂ p) ⊆ Bd ∩ Rc := by
    intro q hq
    have hq1 : q ∈ fib₁ (f₂ p) := hq.1
    rw [hfib₁] at hq1
    have hqHe : q ∈ Bd ∩ X₂ := hHe p hp q hq1.1 hq1.2
    exact ⟨hqHe.1, (hrim q hqHe).mpr hq.2⟩
  set q₀ : Wt := ((ed.symm x : fib₁ (f₂ p)) : Wt) with hq₀def
  have hq₀He : q₀ ∈ Bd ∩ X₂ := by
    have hq1 : q₀ ∈ fib₁ (f₂ p) := hq₀.1
    rw [hfib₁] at hq1
    exact hHe p hp q₀ hq1.1 hq1.2
  have hf2 : f₂ q₀ = f₂ p := by
    have hq1 : q₀ ∈ fib₁ (f₂ p) := hq₀.1
    rw [hfib₁] at hq1
    exact hq1.2
  have hF := hF1 q₀ hq₀He hq₀.2
  rw [hf2] at hF
  refine ⟨f₁ q₀, hF, ⟨q₀, hq₀⟩, hsub, fun q hq => ?_⟩
  have : q ∈ fib₀ (f₁ q₀) := hF ▸ hq
  rw [hfib₀] at this
  exact this.2

omit [TopologicalSpace Wt] in
/-- Distinct horizontal disks have distinct rim base points. -/
theorem rimBase_injOn_BCF {y y' b : H} (hfib₁ : ∀ y, fib₁ y = X₂ ∩ f₂ ⁻¹' {y})
    (hy : rim_BCF fib₁ T c y = fib₀ b) (hy' : rim_BCF fib₁ T c y' = fib₀ b)
    (hne : (rim_BCF fib₁ T c y).Nonempty) : y = y' := by
  obtain ⟨q, hq⟩ := hne
  have hq' : q ∈ rim_BCF fib₁ T c y' := hy' ▸ hy ▸ hq
  have h1 : q ∈ fib₁ y := hq.1
  have h2 : q ∈ fib₁ y' := hq'.1
  rw [hfib₁] at h1 h2
  exact h1.2.symm.trans h2.2

end Disks

end DifferentialGeometry.Topology.Surface
