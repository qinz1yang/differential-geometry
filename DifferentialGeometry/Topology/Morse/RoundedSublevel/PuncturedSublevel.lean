import DifferentialGeometry.Topology.Manifold.ChartDisk.Localization
import DifferentialGeometry.Topology.Morse.RoundedSublevel.SublevelProfile
import DifferentialGeometry.Topology.Morse.Rearrangement.MonotoneShift
import DifferentialGeometry.Topology.Morse.Strip.ModelTransport

namespace DifferentialGeometry.Topology

open Set _root_.Topology
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [T2Space M] in
private theorem critical_postcomp_iff {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) {x : M} (hρ' : deriv ρ (f x) ≠ 0) :
    DifferentialGeometry.Topology.Morse.IsCriticalPointAt (𝓡 n) (ρ ∘ f) x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt (𝓡 n) f x := by
  rw [← isCriticalPointAt_morseModelI_iff (hρ.contMDiff.comp hf),
    ← isCriticalPointAt_morseModelI_iff hf]
  exact MonotoneShift.isCriticalPointAt_comp_iff (contMDiff_morseModelI_iff.mpr hf) hρ hρ'

theorem exists_punctured_sublevel_strip (hn : 1 ≤ n) {G : M → ℝ}
    (hG : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ G) (hne : (G ⁻¹' Iio 0).Nonempty)
    (hreg : ∀ x, G x = 0 → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt (𝓡 n) G x) :
    ∃ (e : Disk n → M) (F : M → ℝ), isChartDisk e ∧
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ F ∧
      F ⁻¹' Iic (-5/8) = range e ∧
      F ⁻¹' Iio (-5/8) = e '' diskInterior n ∧
      F ⁻¹' {-5/8} = e '' diskSphere n ∧
      F ⁻¹' Iic 0 = G ⁻¹' Iic 0 ∧ F ⁻¹' {0} = G ⁻¹' {0} ∧
      (∀ x, F x = -5/8 ∨ F x = 0 → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt (𝓡 n) F x) ∧
      range e ⊆ G ⁻¹' Iio 0 := by
  obtain ⟨p, hp⟩ := hne
  have hp' : G p < 0 := hp
  let δ := -G p / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let U : Set M := G ⁻¹' Iio (-δ)
  have hU : IsOpen U := isOpen_Iio.preimage hG.continuous
  have hUe : U.Nonempty := ⟨p, by change G p < -δ; dsimp [δ]; linarith⟩
  obtain ⟨e, e₁, f, he, -, -, hf, hfle, -, hflt, -, hfeq, -, hfreg, hfs, hfb⟩ :=
    exists_chartDisks_and_strip_supported hn hU hUe
  let ρ := sublevelProfile δ
  have hρ : ContDiff ℝ ∞ ρ := sublevelProfile_contDiff δ
  let F : M → ℝ := fun x => ρ (G x) + f x / 4
  have hF : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ F :=
    (hρ.contMDiff.comp hG).add (hf.div_const 4)
  have hsupport (x : M) (hx : f x ≠ 0) : G x < -δ :=
    hfs (subset_closure (show x ∈ Function.support f from hx))
  have hflat (x : M) (hx : G x < -δ) : ρ (G x) = -1 / 2 :=
    sublevelProfile_eq_neg_half hδ (by linarith)
  have hnegative (x : M) (hx : f x ≠ 0) : F x ≤ -1 / 4 := by
    dsimp [F]
    rw [hflat x (hsupport x hx)]
    linarith [(hfb x).2]
  have hle (x : M) : F x ≤ -5 / 8 ↔ f x ≤ -1 / 2 := by
    by_cases hx : f x = 0
    · have hb := (sublevelProfile_bounds δ (G x)).1
      dsimp [F, ρ]
      rw [hx]
      constructor <;> intro h <;> linarith
    · dsimp [F]
      rw [hflat x (hsupport x hx)]
      constructor <;> intro h <;> linarith
  have hlt (x : M) : F x < -5 / 8 ↔ f x < -1 / 2 := by
    by_cases hx : f x = 0
    · have hb := (sublevelProfile_bounds δ (G x)).1
      dsimp [F, ρ]
      rw [hx]
      constructor <;> intro h <;> linarith
    · dsimp [F]
      rw [hflat x (hsupport x hx)]
      constructor <;> intro h <;> linarith
  have heq (x : M) : F x = -5 / 8 ↔ f x = -1 / 2 := by
    constructor
    · intro hx
      have h₁ := (hle x).mp hx.le
      have h₂ : ¬ f x < -1 / 2 := by rw [← hlt x, hx]; exact lt_irrefl _
      exact le_antisymm h₁ (not_lt.mp h₂)
    · intro hx
      have h₁ := (hle x).mpr hx.le
      have h₂ : ¬ F x < -5 / 8 := by rw [hlt x, hx]; exact lt_irrefl _
      exact le_antisymm h₁ (not_lt.mp h₂)
  have hzero (x : M) : F x = 0 ↔ G x = 0 := by
    by_cases hx : f x = 0
    · simpa only [F, hx, zero_div, add_zero] using sublevelProfile_eq_zero_iff (s := G x) hδ
    · have h₁ := hnegative x hx
      have h₂ := hsupport x hx
      constructor <;> intro h <;> linarith
  have hnonpos (x : M) : F x ≤ 0 ↔ G x ≤ 0 := by
    by_cases hx : f x = 0
    · simpa only [F, hx, zero_div, add_zero] using sublevelProfile_le_zero_iff (s := G x) hδ
    · have h₁ := hnegative x hx
      have h₂ := hsupport x hx
      exact ⟨fun _ => by linarith, fun _ => by linarith⟩
  refine ⟨e, F, he, hF, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Set.ext fun x => hle x).trans hfle
  · exact (Set.ext fun x => hlt x).trans hflt
  · exact (Set.ext fun x => heq x).trans hfeq
  · exact Set.ext fun x => hnonpos x
  · exact Set.ext fun x => hzero x
  · intro x hx
    rcases hx with hx | hx
    · have hfx := (heq x).mp hx
      have hxU : x ∈ U := hsupport x (by rw [hfx]; norm_num)
      have hev : F =ᶠ[𝓝 x] (fun s : ℝ => -1 / 2 + s / 4) ∘ f := by
        filter_upwards [hU.mem_nhds hxU] with y hy
        change ρ (G y) + f y / 4 = -1 / 2 + f y / 4
        rw [hflat y hy]
      rw [MonotoneShift.isCriticalPointAt_congr_nhds hev]
      rw [critical_postcomp_iff hf (by fun_prop) (by
        have hd : HasDerivAt (fun s : ℝ => -1 / 2 + s / 4) (1 / 4) (f x) := by
          convert ((hasDerivAt_id (f x)).div_const 4).const_add (-1 / 2) using 1
          norm_num
        rw [hd.deriv]
        norm_num)]
      exact hfreg x (Or.inl hfx)
    · have hxG := (hzero x).mp hx
      have hxout : x ∉ tsupport f := by
        intro hxs
        have := hfs hxs
        change G x < -δ at this
        rw [hxG] at this
        linarith
      have hev : F =ᶠ[𝓝 x] ρ ∘ G := by
        filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hxout] with y hy
        have hfy : f y = 0 := by
          by_contra hne
          exact hy (subset_closure (show y ∈ Function.support f from hne))
        simp only [F, hfy, zero_div, add_zero, Function.comp_apply]
      rw [MonotoneShift.isCriticalPointAt_congr_nhds hev]
      rw [critical_postcomp_iff hG hρ (by
        obtain ⟨d, hd, hder⟩ := sublevelProfile_hasDerivAt_pos hδ
        change deriv (sublevelProfile δ) (G x) ≠ 0
        rw [hxG, hder.deriv]
        exact hd.ne')]
      exact hreg x hxG
  · intro x hx
    have hfx : f x ≤ -1 / 2 := by
      change x ∈ f ⁻¹' Iic (-1 / 2)
      rwa [hfle]
    have hx' := hsupport x (by linarith)
    change G x < 0
    linarith

end DifferentialGeometry.Topology
