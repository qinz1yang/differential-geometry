import DifferentialGeometry.Geometry.Collapse.SublevelCore.FieldBandSmooth
import DifferentialGeometry.Topology.Collar.VerticalChartLevel

/-!
# A regular band crossed by a vertical chart is a product with the base (F-e, E5)

Let `f` be smooth on a boundaryless manifold modelled on `MorseModel (m + 1)`, with compact band
`K = f⁻¹[a, b]` (`a < b`), and let `Y` be a smooth vector field with `df(Y) > 0` on `K`. If the
bottom level `f⁻¹(a)` is crossed exactly once by every vertical line of a `C^k` vertical chart
`j : S × (a₀, b₀) → M` (`S` compact of dimension `m`) and lies in its image, then `K`, with the
regular-sublevel structure of `(f - a)(f - b)` (a manifold with boundary `f⁻¹{a, b}`), is
diffeomorphic to `S × [a, b]` by a diffeomorphism carrying the second coordinate to `f`.

The flow `Φ` of `Y / df(Y)` (LC46, `exists_field_band_product_of_contMDiffOn`) gives
`f⁻¹(a) × [a, b] ≅ K`, `(x, u) ↦ Φ (u - a) x`, for the EXPLICIT regular-level and regular-sublevel
structures of the Morse library (the product of `FieldBandSmooth.lean` is the same map, but its
structures are existential); the level is identified with `S` by E4
(`Morse.nonempty_diffeomorph_levelSet_of_vertical_chart`), for the same level structure.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology.Morse

variable {m : ℕ} {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ (MorseModel (m + 1)) H}
  [I.Boundaryless] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {S : Type} [TopologicalSpace S] [ChartedSpace G S] [IsManifold J ∞ S]

/-- **E5 (band product over the base of a vertical chart).** The compact regular band
`f⁻¹[a, b]`, with its regular-sublevel structure (boundary `f⁻¹{a, b}`), is diffeomorphic to
`S × [a, b]` preserving the height, when a field `Y` with `df(Y) > 0` lives on the band and the
bottom level is crossed once by each vertical line of a `C^k` vertical chart over `S`. -/
theorem exists_band_diffeomorph_of_vertical_chart [Nonempty S] [CompactSpace S] [T2Space S]
    (hdim : Module.finrank ℝ F = m) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (hab : a < b) (hK : IsCompact (f ⁻¹' Icc a b)) (Y : (x : M) → TangentSpace I x)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x => (⟨x, Y x⟩ : TangentBundle I M)))
    (hpos : ∀ x ∈ f ⁻¹' Icc a b, 0 < mvfderiv (I := I) f x (Y x))
    {k : ℕ} (hk : 1 ≤ k) {a₀ b₀ : ℝ} {j : S × ℝ → M}
    (hj : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) I k j (univ ×ˢ Ioo a₀ b₀))
    (hjinj : InjOn j (univ ×ˢ Ioo a₀ b₀))
    (hjd : ∀ p ∈ (univ : Set S) ×ˢ Ioo a₀ b₀, Injective (mfderiv (J.prod 𝓘(ℝ, ℝ)) I j p))
    (hvert : ∀ x : S, ∀ s ∈ Ioo a₀ b₀, 0 < deriv (fun s : ℝ => f (j (x, s))) s)
    (hcross : ∀ x : S, ∃ s ∈ Ioo a₀ b₀, f (j (x, s)) = a)
    (hlevel : ∀ z, f z = a → z ∈ j '' (univ ×ˢ Ioo a₀ b₀)) :
    haveI : Fact (a < b) := ⟨hab⟩
    ∃ cs : ChartedSpace (MorseHalfSpace m) ↥(f ⁻¹' Icc a b),
      letI := cs
      IsManifold (morseModelWithCornersHalfSpace m) ∞ ↥(f ⁻¹' Icc a b) ∧
      ContMDiff (morseModelWithCornersHalfSpace m) I ∞ (fun y : ↥(f ⁻¹' Icc a b) => (y : M)) ∧
      (∀ y : ↥(f ⁻¹' Icc a b), (morseModelWithCornersHalfSpace m).IsBoundaryPoint y ↔
        f (y : M) = a ∨ f (y : M) = b) ∧
      ∃ D : Diffeomorph (J.prod (𝓡∂ 1)) (morseModelWithCornersHalfSpace m)
          (S × Icc a b) ↥(f ⁻¹' Icc a b) ∞,
        ∀ p, f (D p : M) = (p.2 : ℝ) := by
  have : Fact (a < b) := ⟨hab⟩
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  -- the flow of `Y / df(Y)`
  obtain ⟨Φ, hΦ0, hΦc, -, hΦadd, hval, -⟩ :=
    exists_field_band_product_of_contMDiffOn hf.continuous isOpen_univ hf.contMDiffOn hab ha
      hK (subset_univ _) Y hY.contMDiffOn hpos
  have hΦ0' : ∀ x, Φ 0 x = x := fun x => by rw [hΦ0]; rfl
  -- regularity
  have hrega : ∀ x, f x = a → ¬ IsCriticalPointAt I f x :=
    not_isCriticalPointAt_of_vertical_chart hf hk hj hvert hlevel
  have hregband : ∀ x, f x ∈ Icc a b → ¬ IsCriticalPointAt I f x := by
    intro x hx hcrit
    have h := hpos x hx
    change mfderiv I 𝓘(ℝ, ℝ) f x = 0 at hcrit
    have hz : mvfderiv (I := I) f x (Y x) = 0 := by
      change NormedSpace.fromTangentSpace (f x) (mfderiv I 𝓘(ℝ, ℝ) f x (Y x)) = 0
      rw [hcrit]
      rfl
    linarith
  set g : M → ℝ := fun x => (f x - a) * (f x - b) with hgdef
  have hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g := (hf.sub contMDiff_const).mul (hf.sub contMDiff_const)
  have hgband : ∀ x, g x ≤ 0 ↔ f x ∈ Icc a b := fun x => by
    have h := congrArg (fun s : Set M => x ∈ s) (sublevel_bandDefiningFunction f hab.le)
    exact iff_of_eq h
  have hregg : ∀ x, g x = 0 → ¬ IsCriticalPointAt I g x := fun x hx =>
    bandDefiningFunction_regular hab ((hf x).mdifferentiableAt (by simp)) hx
      (hregband x ((hgband x).mp hx.le))
  -- the level is the base
  obtain ⟨σ⟩ := nonempty_diffeomorph_levelSet_of_vertical_chart hdim hf hrega hk hj hjinj hjd
    hvert hcross hlevel
  rw [← sublevel_bandDefiningFunction f hab.le]
  let _ : ChartedSpace (MorseModel m) (LevelSetSpace f a) :=
    manifoldLevelSetChartedSpace I f a hf hrega
  have _ := manifoldLevelSetIsManifold I f a hf hrega
  let cs : ChartedSpace (MorseHalfSpace m) (SublevelSpace g 0) :=
    manifoldSublevelChartedSpace I g 0 hg hregg
  have hmK : IsManifold (morseModelWithCornersHalfSpace m) ∞ (SublevelSpace g 0) :=
    manifoldSublevelIsManifold I g 0 hg hregg
  have hincL : ContMDiff 𝓘(ℝ, MorseModel m) I ∞ (fun x : LevelSetSpace f a => (x : M)) :=
    contMDiff_levelSetInclusion I f a hf hrega
  have hincK : ContMDiff (morseModelWithCornersHalfSpace m) I ∞
      (fun y : SublevelSpace g 0 => (y : M)) :=
    contMDiff_manifoldSublevelInclusion (I := I) g 0 hg hregg
  have hlev : ∀ x : LevelSetSpace f a, f x = a := fun x => x.2
  have hfwd : ∀ p : LevelSetSpace f a × Icc a b, g (Φ ((p.2 : ℝ) - a) p.1) ≤ 0 := by
    intro p
    have h := hval p.1 (by rw [hlev p.1]; exact ha) p.2 p.2.2
    rw [hlev p.1] at h
    rw [hgband, h]
    exact p.2.2
  have hbwd : ∀ y : SublevelSpace g 0, f (Φ (a - f y) y) = a := fun y =>
    hval y ((hgband y).mp y.2) a ha
  let eqv : (LevelSetSpace f a × Icc a b) ≃ SublevelSpace g 0 :=
    { toFun := fun p => ⟨Φ ((p.2 : ℝ) - a) p.1, hfwd p⟩
      invFun := fun y => (⟨Φ (a - f y) y, hbwd y⟩, ⟨f y, (hgband y).mp y.2⟩)
      left_inv := by
        intro p
        have h := hval p.1 (by rw [hlev p.1]; exact ha) p.2 p.2.2
        rw [hlev p.1] at h
        apply Prod.ext
        · apply Subtype.ext
          change Φ (a - f (Φ ((p.2 : ℝ) - a) p.1)) (Φ ((p.2 : ℝ) - a) p.1) = p.1
          rw [h, ← hΦadd, sub_add_sub_cancel, sub_self, hΦ0']
        · apply Subtype.ext
          exact h
      right_inv := by
        intro y
        apply Subtype.ext
        change Φ (f y - a) (Φ (a - f y) y) = y
        rw [← hΦadd, sub_add_sub_cancel, sub_self, hΦ0'] }
  have hamb : ContMDiff ((𝓘(ℝ, MorseModel m)).prod (𝓡∂ 1)) I ∞
      (fun p : LevelSetSpace f a × Icc a b => Φ ((p.2 : ℝ) - a) p.1) :=
    hΦc.comp (((contMDiff_subtypeVal_Icc.comp contMDiff_snd).sub contMDiff_const).prodMk
      (hincL.comp contMDiff_fst))
  have hto : ContMDiff ((𝓘(ℝ, MorseModel m)).prod (𝓡∂ 1)) (morseModelWithCornersHalfSpace m) ∞
      eqv :=
    contMDiff_sublevelCorestrict (I := I) g 0 hg hregg _ hamb hfwd
  have hheight : ContMDiff (morseModelWithCornersHalfSpace m) 𝓘(ℝ, ℝ) ∞
      (fun y : SublevelSpace g 0 => f y) := hf.comp hincK
  have hamb' : ContMDiff (morseModelWithCornersHalfSpace m) I ∞
      (fun y : SublevelSpace g 0 => Φ (a - f y) y) :=
    hΦc.comp ((contMDiff_const.sub hheight).prodMk hincK)
  have hfirst : ContMDiff (morseModelWithCornersHalfSpace m) 𝓘(ℝ, MorseModel m) ∞
      (fun y : SublevelSpace g 0 => (⟨Φ (a - f y) y, hbwd y⟩ : LevelSetSpace f a)) :=
    contMDiff_levelSet_factor I f a hf hrega _ hamb' hbwd
  have hsecond : ContMDiff (morseModelWithCornersHalfSpace m) (𝓡∂ 1) ∞
      (fun y : SublevelSpace g 0 => (⟨f y, (hgband y).mp y.2⟩ : Icc a b)) := by
    rw [contMDiff_iff_comp_subtypeVal_Icc]
    exact ⟨hheight.continuous.subtype_mk _, hheight⟩
  have hinv : ContMDiff (morseModelWithCornersHalfSpace m)
      ((𝓘(ℝ, MorseModel m)).prod (𝓡∂ 1)) ∞ eqv.symm := hfirst.prodMk hsecond
  let d : Diffeomorph ((𝓘(ℝ, MorseModel m)).prod (𝓡∂ 1)) (morseModelWithCornersHalfSpace m)
      (LevelSetSpace f a × Icc a b) (SublevelSpace g 0) ∞ :=
    { toEquiv := eqv, contMDiff_toFun := hto, contMDiff_invFun := hinv }
  let D := (σ.symm.prodCongr (Diffeomorph.refl (𝓡∂ 1) (Icc a b) ∞)).trans d
  refine ⟨cs, hmK, hincK, fun y => ?_, D, fun p => ?_⟩
  · rw [manifoldSublevel_isBoundaryPoint_iff I g 0 hg hregg y]
    exact mul_eq_zero.trans (or_congr sub_eq_zero sub_eq_zero)
  · change f (Φ ((p.2 : ℝ) - a) (σ.symm p.1)) = p.2
    have h := hval (σ.symm p.1) (by rw [hlev (σ.symm p.1)]; exact ha) p.2 p.2.2
    rw [hlev (σ.symm p.1)] at h
    exact h

end DifferentialGeometry.Geometry.Collapse
