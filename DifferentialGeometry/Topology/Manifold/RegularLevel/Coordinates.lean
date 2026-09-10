import DifferentialGeometry.Topology.Morse.RegularLevel.LevelSet
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

open Set DifferentialGeometry.Topology.Morse
open scoped Manifold ContDiff Topology
set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Manifold.RegularLevel

private theorem exists_euclidean_regular_coordinates {m : ℕ}
    {g : MorseModel (m + 1) → ℝ} {s : Set (MorseModel (m + 1))}
    (hs : IsOpen s) (hg : ContDiffOn ℝ ∞ g s) {x : MorseModel (m + 1)}
    (hx : x ∈ s) (hreg : fderiv ℝ g x ≠ 0) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, MorseModel (m + 1))
      𝓘(ℝ, ℝ × MorseModel m) (MorseModel (m + 1)) (ℝ × MorseModel m) ∞,
      x ∈ Φ.source ∧ Φ.source ⊆ s ∧ ∀ y ∈ Φ.source, (Φ y).1 = g y := by
  classical
  obtain ⟨i, hi⟩ := exists_coord_of_fderiv_ne_zero g x hreg
  let e := Equiv.swap i (Fin.last m)
  let R := (levelSetReindex e).toContinuousLinearEquiv
  let x₁ := R x
  have hRR (y : MorseModel (m + 1)) : R (R y) = y := levelSetReindex_swap_swap i y
  have hxg : ContDiffAt ℝ ∞ g x := hg.contDiffAt (hs.mem_nhds hx)
  have hgx₁ : ContDiffAt ℝ ∞ g (R x₁) := by rw [hRR]; exact hxg
  have hc : (fderiv ℝ (fun v => g (R v)) x₁) levelSetLastBasis ≠ 0 :=
    levelSetReindex_lastDeriv_ne_zero g x hxg i hi
  have hG : ContDiffAt ℝ ∞ (levelSetChartMap g e) x₁ :=
    contDiffAt_levelSetChartMap g e x₁ hgx₁
  have hD := hasFDerivAt_levelSetChartMap g e x₁ hgx₁ hc
  let ψ := hG.toOpenPartialHomeomorph (levelSetChartMap g e) hD (by simp)
  have hψx : x₁ ∈ ψ.source := hG.mem_toOpenPartialHomeomorph_source hD (by simp)
  have hR : ContDiffAt ℝ ∞ (fun v => g (R v)) x₁ := hgx₁.comp x₁ R.contDiff.contDiffAt
  have hcont : ContinuousAt
      (fun v => (fderiv ℝ (fun w => g (R w)) v) levelSetLastBasis) x₁ :=
    (hR.continuousAt_fderiv (by simp)).clm_apply continuousAt_const
  have hgood : {v | (fderiv ℝ (fun w => g (R w)) v) levelSetLastBasis ≠ 0} ∈ 𝓝 x₁ :=
    hcont.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hc)
  have hsR : R ⁻¹' s ∈ 𝓝 x₁ := R.continuous.continuousAt.preimage_mem_nhds
    (hs.mem_nhds (by rw [hRR]; exact hx))
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp (Filter.inter_mem hgood hsR)
  let ψ' := ψ.restrOpen U hU
  have hUg {w : MorseModel (m + 1)} (hw : w ∈ ψ'.source) : ContDiffAt ℝ ∞ g (R w) :=
    hg.contDiffAt (hs.mem_nhds (hUsub hw.2).2)
  let Ψ : PartialDiffeomorph 𝓘(ℝ, MorseModel (m + 1)) 𝓘(ℝ, ℝ × MorseModel m)
      (MorseModel (m + 1)) (ℝ × MorseModel m) ∞ := {
    toPartialEquiv := ψ'.toPartialEquiv
    open_source := ψ'.open_source
    open_target := ψ'.open_target
    contMDiffOn_toFun := by
      intro w hw
      exact (contDiffAt_levelSetChartMap g e w (hUg hw)).contMDiffAt.contMDiffWithinAt
    contMDiffOn_invFun := by
      intro z hz
      have hw := ψ'.map_target hz
      have hc' := (hUsub hw.2).1
      have hd' := hasFDerivAt_levelSetChartMap g e (ψ'.symm z) (hUg hw) hc'
      have hg' := contDiffAt_levelSetChartMap g e (ψ'.symm z) (hUg hw)
      exact (ψ'.contDiffAt_symm hz hd' hg').contMDiffAt.contMDiffWithinAt }
  let Φ := R.toDiffeomorph.toPartialDiffeomorph.trans Ψ
  refine ⟨Φ, ⟨mem_univ _, hψx, hxU⟩, ?_, ?_⟩
  · intro y hy
    have hh : R (R y) ∈ s := (hUsub hy.2.2).2
    rwa [hRR] at hh
  · intro y _
    change g (R (R y)) = g y
    rw [hRR]

private def heightSplitDiffeomorph (m : ℕ) (a : ℝ) :
    (ℝ × MorseModel m) ≃ₘ[ℝ] MorseModel (m + 1) where
  toEquiv := (((Equiv.subLeft a).prodCongr (Equiv.refl (MorseModel m))).trans
    (Equiv.prodComm ℝ (MorseModel m))).trans (levelSetSplit m)
  contMDiff_toFun :=
    ((levelSetSplit m).toContinuousLinearEquiv.contDiff.comp
      (contDiff_snd.prodMk (contDiff_const.sub contDiff_fst))).contMDiff
  contMDiff_invFun := by
    change ContMDiff 𝓘(ℝ, MorseModel (m + 1)) 𝓘(ℝ, ℝ × MorseModel m) ∞
      (fun v => (-v (Fin.last m) + a, levelSetSplitFst m v))
    exact (((contDiff_apply ℝ ℝ (Fin.last m)).neg.add contDiff_const).prodMk
      (levelSetSplitFst m).contDiff).contMDiff

private theorem heightSplitDiffeomorph_last (m : ℕ) (a : ℝ) (z : ℝ × MorseModel m) :
    heightSplitDiffeomorph m a z (Fin.last m) = a - z.1 := by
  change levelSetSplit m (z.2, a - z.1) (Fin.last m) = a - z.1
  simp [levelSetSplit]

variable {m : ℕ} {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)
  [I.Boundaryless] [IsManifold I ∞ M]

private def ambientChart (x : M) :
    PartialDiffeomorph I 𝓘(ℝ, MorseModel (m + 1)) M (MorseModel (m + 1)) ∞ where
  toPartialEquiv := extChartAt I x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target x
  contMDiffOn_toFun := by simpa only [extChartAt_source] using (contMDiffOn_extChartAt (I := I) (x := x) (n := ∞))
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm x

theorem exists_coordinates_of_contMDiffOn {f : M → ℝ} {s : Set M}
    (hs : IsOpen s) (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f s)
    {x : M} (hx : x ∈ s) (hreg : mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) (a : ℝ) :
    ∃ Φ : PartialDiffeomorph I 𝓘(ℝ, MorseModel (m + 1)) M (MorseModel (m + 1)) ∞,
      x ∈ Φ.source ∧ Φ.source ⊆ s ∧
      ∀ y ∈ Φ.source, Φ y (Fin.last m) = a - f y := by
  let c := ambientChart I x
  let e := c.toOpenPartialHomeomorph.restrOpen s hs
  let σ : PartialDiffeomorph I 𝓘(ℝ, MorseModel (m + 1)) M (MorseModel (m + 1)) ∞ := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := c.contMDiffOn.mono inter_subset_left
    contMDiffOn_invFun := c.symm.contMDiffOn.mono inter_subset_left }
  have hxσ : x ∈ σ.source := ⟨mem_extChartAt_source x, hx⟩
  let g : MorseModel (m + 1) → ℝ := f ∘ σ.symm
  have hg : ContDiffOn ℝ ∞ g σ.target :=
    contMDiffOn_iff_contDiffOn.mp
      (hf.comp σ.symm.contMDiffOn (fun y hy => (σ.map_target hy).2))
  have hgx : ContDiffAt ℝ ∞ g (σ x) := hg.contDiffAt (σ.open_target.mem_nhds (σ.map_source hxσ))
  have hgreg : fderiv ℝ g (σ x) ≠ 0 := by
    intro hzero
    have heq : g ∘ σ =ᶠ[𝓝 x] f :=
      Filter.eventuallyEq_of_mem (σ.open_source.mem_nhds hxσ)
        (fun y hy => congrArg f (σ.left_inv hy))
    have hh := mfderiv_comp x (hgx.contMDiffAt.mdifferentiableAt (by simp))
      (σ.mdifferentiableAt (by simp) hxσ)
    erw [heq.mfderiv_eq, mfderiv_eq_fderiv, hzero, ContinuousLinearMap.zero_comp] at hh
    exact hreg hh
  obtain ⟨Ψ, hxΨ, _, hΨcoord⟩ :=
    exists_euclidean_regular_coordinates σ.open_target hg (σ.map_source hxσ) hgreg
  let Φ := (σ.trans Ψ).trans (heightSplitDiffeomorph m a).toPartialDiffeomorph
  refine ⟨Φ, ⟨⟨hxσ, hxΨ⟩, mem_univ _⟩, ?_, ?_⟩
  · intro y hy
    exact hy.1.1.2
  · intro y hy
    change heightSplitDiffeomorph m a (Ψ (σ y)) (Fin.last m) = a - f y
    rw [heightSplitDiffeomorph_last, hΨcoord (σ y) hy.1.2]
    change a - f (σ.symm (σ y)) = a - f y
    exact congrArg (fun z => a - f z) (σ.left_inv hy.1.1)

theorem exists_level_coordinates {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {x : M} {a : ℝ} (hlevel : f x = a) (hreg : mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    ∃ Φ : PartialDiffeomorph I 𝓘(ℝ, MorseModel (m + 1)) M (MorseModel (m + 1)) ∞,
      x ∈ Φ.source ∧ Φ x (Fin.last m) = 0 ∧
      (∀ y ∈ Φ.source, Φ y (Fin.last m) = a - f y) ∧
      Φ '' (Φ.source ∩ {y | f y ≤ a}) = Φ.target ∩ {z | 0 ≤ z (Fin.last m)} ∧
      Φ '' (Φ.source ∩ {y | f y = a}) = Φ.target ∩ {z | z (Fin.last m) = 0} := by
  obtain ⟨Φ, hx, _, hcoord⟩ := exists_coordinates_of_contMDiffOn I isOpen_univ
    hf.contMDiffOn (mem_univ x) hreg a
  refine ⟨Φ, hx, ?_, hcoord, ?_, ?_⟩
  · rw [hcoord x hx, hlevel, sub_self]
  · ext z
    constructor
    · rintro ⟨y, ⟨hy, hfya⟩, rfl⟩
      refine ⟨Φ.map_source hy, ?_⟩
      change 0 ≤ Φ y (Fin.last m)
      rw [hcoord y hy]
      exact sub_nonneg.mpr hfya
    · rintro ⟨hz, hpos⟩
      change 0 ≤ z (Fin.last m) at hpos
      have hsrc := Φ.map_target hz
      have hval : Φ (Φ.symm z) (Fin.last m) = z (Fin.last m) :=
        congrArg (fun w : MorseModel (m + 1) => w (Fin.last m)) (Φ.right_inv hz)
      have hh := hcoord (Φ.symm z) hsrc
      have hfya : f (Φ.symm z) ≤ a := by rw [hval] at hh; linarith
      exact ⟨Φ.symm z, ⟨hsrc, hfya⟩, Φ.right_inv hz⟩
  · ext z
    constructor
    · rintro ⟨y, ⟨hy, hfya⟩, rfl⟩
      refine ⟨Φ.map_source hy, ?_⟩
      change Φ y (Fin.last m) = 0
      change f y = a at hfya
      rw [hcoord y hy, hfya, sub_self]
    · rintro ⟨hz, hzero⟩
      change z (Fin.last m) = 0 at hzero
      have hsrc := Φ.map_target hz
      have hval : Φ (Φ.symm z) (Fin.last m) = z (Fin.last m) :=
        congrArg (fun w : MorseModel (m + 1) => w (Fin.last m)) (Φ.right_inv hz)
      have hh := hcoord (Φ.symm z) hsrc
      have hfya : f (Φ.symm z) = a := by rw [hval, hzero] at hh; linarith
      exact ⟨Φ.symm z, ⟨hsrc, hfya⟩, Φ.right_inv hz⟩

omit [I.Boundaryless] [IsManifold I ∞ M] in
theorem coordinate_change {f : M → ℝ} {a : ℝ}
    (Φ Ψ : PartialDiffeomorph I 𝓘(ℝ, MorseModel (m + 1)) M (MorseModel (m + 1)) ∞)
    (hΦ : ∀ y ∈ Φ.source, Φ y (Fin.last m) = a - f y)
    (hΨ : ∀ y ∈ Ψ.source, Ψ y (Fin.last m) = a - f y) :
    ContDiffOn ℝ ∞ (Ψ ∘ Φ.symm) (Φ.target ∩ Φ.symm ⁻¹' Ψ.source) ∧
    ∀ z ∈ Φ.target ∩ Φ.symm ⁻¹' Ψ.source,
      Ψ (Φ.symm z) (Fin.last m) = z (Fin.last m) := by
  refine ⟨contMDiffOn_iff_contDiffOn.mp (Φ.symm.trans Ψ).contMDiffOn, ?_⟩
  intro z hz
  calc
    Ψ (Φ.symm z) (Fin.last m) = a - f (Φ.symm z) := hΨ _ hz.2
    _ = Φ (Φ.symm z) (Fin.last m) := (hΦ _ (Φ.map_target hz.1)).symm
    _ = z (Fin.last m) := congrArg (fun w : MorseModel (m + 1) => w (Fin.last m))
      (Φ.right_inv hz.1)

end DifferentialGeometry.Manifold.RegularLevel
