import DifferentialGeometry.Topology.Collar.VerticalChartLevel
import DifferentialGeometry.Topology.Manifold.InteriorAtlas
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import DifferentialGeometry.Topology.Manifold.MFDeriv.ModelTransport
import DifferentialGeometry.Topology.Manifold.Homeomorph.Transport

/-!
# Levels crossed once by a vertical chart in a manifold with boundary (F-e, E4)

`exists_diffeomorph_level_of_vertical_chart`: let `M` be a manifold modelled on any
finite-dimensional `E` (corners and boundary allowed), `f : M → ℝ` smooth, and
`j : S × (a, b) → M` a `C^k` injective immersion with values in the intrinsic interior, `S` compact
boundaryless of dimension
`finrank E - 1`. If `s ↦ f (j (x, s))` has positive derivative, every vertical line meets the level
`f⁻¹(c)` and the level lies in the image of `j`, then the level `{x : M // f x = c}` carries a
smooth structure (model `MorseModel m`) with smooth inclusion into `M`, and it is smoothly
diffeomorphic to `S`.

The structure is the Morse regular-level structure of `f` restricted to the intrinsic interior
with its interior atlas (model `𝓘(ℝ, E)` transported to `MorseModel (m + 1)`), pulled back to the
subtype of `M` (pattern of `Manifold/RegularLevel/InteriorSublevel.lean`). Regularity of the level
comes from the vertical derivative, so it is not a hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Manifold DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Topology

variable {m : ℕ} {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {S : Type} [TopologicalSpace S] [ChartedSpace G S] [IsManifold J ∞ S]

/-- **E4 in a manifold with boundary.** The level of a smooth function crossed exactly once by
every vertical line of an interior `C^k` vertical chart over a compact `S` is a smooth manifold,
smoothly embedded in `M`, and smoothly diffeomorphic to `S`. -/
theorem exists_diffeomorph_level_of_vertical_chart [Nonempty S] [CompactSpace S] [T2Space S]
    (e : E ≃L[ℝ] MorseModel (m + 1)) (hdim : Module.finrank ℝ F = m) {f : M → ℝ} {c : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {k : ℕ} (hk : 1 ≤ k) {a b : ℝ} {j : S × ℝ → M}
    (hj : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) I k j (univ ×ˢ Ioo a b))
    (hjinj : InjOn j (univ ×ˢ Ioo a b))
    (hjd : ∀ p ∈ (univ : Set S) ×ˢ Ioo a b, Injective (mfderiv (J.prod 𝓘(ℝ, ℝ)) I j p))
    (hjint : ∀ p ∈ (univ : Set S) ×ˢ Ioo a b, I.IsInteriorPoint (j p))
    (hvert : ∀ x : S, ∀ s ∈ Ioo a b, 0 < deriv (fun s : ℝ => f (j (x, s))) s)
    (hcross : ∀ x : S, ∃ s ∈ Ioo a b, f (j (x, s)) = c)
    (hlevel : ∀ z, f z = c → z ∈ j '' (univ ×ˢ Ioo a b)) :
    ∃ cs : ChartedSpace (MorseModel m) {x : M // f x = c},
      letI := cs
      IsManifold 𝓘(ℝ, MorseModel m) ∞ {x : M // f x = c} ∧
      ContMDiff 𝓘(ℝ, MorseModel m) I ∞ (Subtype.val : {x : M // f x = c} → M) ∧
      Nonempty ({x : M // f x = c} ≃ₘ⟮𝓘(ℝ, MorseModel m), J⟯ S) := by
  classical
  have hk0 : (k : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hk)
  have hD : IsOpen ((univ : Set S) ×ˢ Ioo a b) := isOpen_univ.prod isOpen_Ioo
  -- the intrinsic interior with its interior atlas, transported to `MorseModel (m + 1)`
  let U := intrinsicInterior I ∞ (by simp) (M := M)
  let _ := interiorChartedSpace I ∞ (M := U)
  let _ : IsManifold 𝓘(ℝ, E) ∞ U := interiorIsManifold I ∞
  let IJ := (𝓘(ℝ, E)).transContinuousLinearEquiv e
  have _ : IJ.Boundaryless := by
    refine ⟨?_⟩
    rw [ModelWithCorners.transContinuousLinearEquiv_range, ModelWithCorners.range_eq_univ,
      image_univ]
    exact e.surjective.range_eq
  have hval₀ : ContMDiff 𝓘(ℝ, E) I ∞ (Subtype.val : U → M) :=
    contMDiff_intrinsicInterior_val I ∞ (show (∞ : ℕ∞ω) ≠ 0 from by simp)
  have hval : ContMDiff IJ I ∞ (Subtype.val : U → M) := by
    simpa only [IJ, ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left] using hval₀
  -- the differential of the inclusion of the interior is bijective
  have hvalbij : ∀ y : U, Bijective (mfderiv IJ I (Subtype.val : U → M) y) := by
    intro y
    have hmd₀ : MDifferentiableAt 𝓘(ℝ, E) I (Subtype.val : U → M) y :=
      (hval₀ y).mdifferentiableAt (by simp)
    rw [mfderiv_transContinuousLinearEquiv 𝓘(ℝ, E) e hmd₀]
    let D := interiorAtlasDiffeomorph I ∞ (M := U)
    have hDs : MDifferentiableAt 𝓘(ℝ, E) I D.symm y :=
      D.symm.mdifferentiable (by simp : (∞ : WithTop ℕ∞) ≠ 0) y
    have hsub : MDifferentiableAt I I (Subtype.val : U → M) (D.symm y) :=
      (hasMFDerivAt_subtype_val (I := I) U (D.symm y)).mdifferentiableAt
    have hcomp := mfderiv_comp y hsub hDs
    have hcomp' : mfderiv 𝓘(ℝ, E) I (Subtype.val : U → M) y =
        (mfderiv I I (Subtype.val : U → M) (D.symm y)).comp
          (mfderiv 𝓘(ℝ, E) I D.symm y) := hcomp
    rw [hcomp', mfderiv_subtype_val (I := I) U (D.symm y)]
    obtain ⟨φ, hφ⟩ := (D.symm.isLocalDiffeomorph y).isInvertible_mfderiv (by simp)
    have hb : Bijective (mfderiv 𝓘(ℝ, E) I D.symm y) := by
      rw [← hφ]
      exact φ.bijective
    exact hb.comp e.symm.bijective
  -- the restricted function and its regular level
  let f' : U → ℝ := fun y => f y
  have hf' : ContMDiff IJ 𝓘(ℝ, ℝ) ∞ f' := hf.comp hval
  have hreg' : ∀ y : U, f' y = c → ¬ IsCriticalPointAt IJ f' y := by
    intro y hy hcrit
    obtain ⟨p, hp, hjp⟩ := hlevel (y : M) hy
    have hjdiff : MDifferentiableAt (J.prod 𝓘(ℝ, ℝ)) I j p :=
      (hj.contMDiffAt (hD.mem_nhds hp)).mdifferentiableAt hk0
    have hne := mfderiv_ne_zero_of_deriv_vertical_pos ((hf (j p)).mdifferentiableAt (by simp))
      hjdiff (hvert p.1 p.2 hp.2)
    rw [hjp] at hne
    apply hne
    have hchain := mfderiv_comp y ((hf (y : M)).mdifferentiableAt (by simp))
      ((hval y).mdifferentiableAt (by simp))
    change mfderiv IJ 𝓘(ℝ, ℝ) f' y = 0 at hcrit
    have h0 : (mfderiv I 𝓘(ℝ, ℝ) f (y : M)).comp (mfderiv IJ I (Subtype.val : U → M) y) = 0 :=
      hchain.symm.trans hcrit
    apply ContinuousLinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := (hvalbij y).2 w
    exact DFunLike.congr_fun h0 v
  let _ := manifoldLevelSetChartedSpace IJ f' c hf' hreg'
  have _ := manifoldLevelSetIsManifold IJ f' c hf' hreg'
  -- the kernel, with `ι = val ∘ val`
  have hι : ContMDiff 𝓘(ℝ, MorseModel m) I ∞ (fun y : LevelSetSpace f' c => (y.1 : M)) :=
    hval.comp (contMDiff_levelSetInclusion IJ f' c hf' hreg')
  have hιd : ∀ y : LevelSetSpace f' c,
      Injective (mfderiv 𝓘(ℝ, MorseModel m) I (fun y : LevelSetSpace f' c => (y.1 : M)) y) := by
    intro y
    have hinc := ((contMDiff_levelSetInclusion IJ f' c hf' hreg') y).mdifferentiableAt
      (by simp)
    have hchain := mfderiv_comp y ((hval y.1).mdifferentiableAt (by simp)) hinc
    have hchain' : mfderiv 𝓘(ℝ, MorseModel m) I (fun y : LevelSetSpace f' c => (y.1 : M)) y =
        (mfderiv IJ I (Subtype.val : U → M) y.1).comp
          (mfderiv 𝓘(ℝ, MorseModel m) IJ (fun y : LevelSetSpace f' c => y.1) y) := hchain
    rw [hchain']
    exact (hvalbij y.1).1.comp (mfderiv_manifoldLevelSetInclusion_injective IJ f' c hf' hreg' y)
  have hint : ∀ z : M, f z = c → z ∈ (U : Set M) := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := hlevel z hz
    exact hjint p hp
  have hdimL : Module.finrank ℝ (MorseModel m) = Module.finrank ℝ F := by
    rw [Module.finrank_fin_fun, hdim]
  have hdimM : Module.finrank ℝ (F × ℝ) = Module.finrank ℝ E := by
    rw [e.finrank_eq, Module.finrank_prod, Module.finrank_fin_fun, hdim, Module.finrank_self]
  obtain ⟨d₀⟩ := nonempty_diffeomorph_of_vertical_chart hdimL hdimM hι hιd
    (fun y₁ y₂ h => Subtype.ext (Subtype.ext h)) (fun y => y.2)
    (fun z hz => ⟨⟨⟨z, hint z hz⟩, hz⟩, rfl⟩)
    (fun z _ => (hf z).mdifferentiableAt (by simp)) hk hj hjinj hjd hjint hvert hcross hlevel
  -- pull the structure back to the subtype of `M`
  let hlev : {x : M // f x = c} ≃ₜ LevelSetSpace f' c :=
    { toFun := fun x => ⟨⟨x.1, hint x.1 x.2⟩, x.2⟩
      invFun := fun y => ⟨y.1.1, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let cs := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := MorseModel m) hlev
  let d₁ := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := 𝓘(ℝ, MorseModel m)) (n := ∞) hlev
  refine ⟨cs, DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback
    (I := 𝓘(ℝ, MorseModel m)) (n := ∞) hlev, hι.comp d₁.contMDiff, ⟨d₁.trans d₀⟩⟩

end DifferentialGeometry.Topology
