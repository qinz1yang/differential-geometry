import DifferentialGeometry.Geometry.Collapse.SublevelCore.GradientBand
import DifferentialGeometry.Topology.Morse.RegularSublevelBoundary
import DifferentialGeometry.Topology.Morse.SublevelInclusion
import DifferentialGeometry.Topology.Morse.CriticalPoint
import Mathlib.Geometry.Manifold.Instances.Icc

/-!
# LC33 and LC46 in the smooth category: a diffeomorphism of manifolds with boundary

Blueprint LC33 (`master207A.tex:21422`) and LC46 (`:22259`) state that the product coordinates
`Σ × [a, b] → K` of the band `K = η⁻¹[a, b]` over a level `Σ = η⁻¹(c)` form a DIFFEOMORPHISM of
manifolds with boundary. The accepted modules export a jointly smooth ambient flow and a
HOMEOMORPHISM of subtypes (`exists_field_band_product`, `radialBand_gradient_product`). This file
installs the smooth structures and exports the diffeomorphism (review of the wave-3 sheets):

* the level `Σ` carries the regular-level structure of the Morse library
  (`Morse.manifoldLevelSetChartedSpace`, model `MorseModel m`, no boundary);
* the band `K` carries the regular-sublevel structure of `(f - a)(f - b) ≤ 0`
  (`Morse.manifoldSublevelChartedSpace`, model `MorseHalfSpace m`), whose boundary points are
  exactly the two levels `a`, `b` (`a < b` is required, so `a = b` is excluded);
* `Icc a b` carries Mathlib's structure (`Fact (a < b)`).

All three are embedded: their inclusions into `M` are smooth, and smooth maps into them are the
ambient smooth maps landing in them (`Morse.contMDiff_levelSet_factor`,
`Morse.contMDiff_sublevelCorestrict`, `contMDiff_iff_comp_subtypeVal_Icc`). The diffeomorphism
`(x, u) ↦ Φ (u - c) x`, inverse `y ↦ (Φ (c - η y) y, η y)`, is smooth in both directions because
the flow `Φ` is jointly smooth. The model space `E` is arbitrary (`finrank ℝ E = m + 1`): the Morse
library is applied to the model `I.transContinuousLinearEquiv e`, `e : E ≃L[ℝ] MorseModel (m + 1)`.

* `exists_flowBand_diffeomorph` (kernel): a globally smooth `f`, regular on its band, and any
  jointly smooth flow with the band value property.
* `exists_field_band_diffeomorph` (LC46): `η` smooth near its band, a field `Y` with
  `dη(Y) > 0` on the band; the LC46 flow clauses and the smooth product for the same flow.
* `radialBand_gradient_diffeomorph` (LC33, PC Riemannian setting): every clause of
  `radialBand_gradient_product` (speed bound, track estimate) and the smooth product for the same flow.

The Morse library is stated in universe `0`, hence `E H M : Type`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Bundle
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology.Morse

section DefiningFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

omit [TopologicalSpace M] in
/-- The band `f⁻¹[a, b]` is the sublevel `(f - a)(f - b) ≤ 0`. -/
theorem sublevel_bandDefiningFunction (f : M → ℝ) {a b : ℝ} (hab : a ≤ b) :
    sublevel (fun x => (f x - a) * (f x - b)) 0 = f ⁻¹' Icc a b := by
  ext x
  change (f x - a) * (f x - b) ≤ 0 ↔ a ≤ f x ∧ f x ≤ b
  rw [mul_nonpos_iff]
  constructor
  · rintro (h | h) <;> constructor <;> linarith
  · intro h
    exact Or.inl ⟨sub_nonneg.mpr h.1, sub_nonpos.mpr h.2⟩

/-- The defining function `(f - a)(f - b)` of the band is regular at `0` when `f` is regular at
the levels `a ≠ b`. -/
theorem bandDefiningFunction_regular {f : M → ℝ} {a b : ℝ} (hab : a < b) {x : M}
    (hfx : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (hx : (f x - a) * (f x - b) = 0)
    (hreg : ¬ IsCriticalPointAt I f x) :
    ¬ IsCriticalPointAt I (fun y => (f y - a) * (f y - b)) x := by
  have hend : f x = a ∨ f x = b := by
    simpa only [mul_eq_zero, sub_eq_zero] using hx
  have hd : HasDerivAt (fun t : ℝ => (t - a) * (t - b)) ((f x - b) + (f x - a)) (f x) := by
    convert ((hasDerivAt_id (f x)).sub_const a).mul ((hasDerivAt_id (f x)).sub_const b)
      using 1 <;> first | rfl | simp
  have hcomp := hd.hasFDerivAt.hasMFDerivAt.comp x hfx.hasMFDerivAt
  have hder : mfderiv I 𝓘(ℝ, ℝ) (fun y => (f y - a) * (f y - b)) x =
      ((f x - b) + (f x - a)) • mfderiv I 𝓘(ℝ, ℝ) f x := by
    change mfderiv I 𝓘(ℝ, ℝ) ((fun t : ℝ => (t - a) * (t - b)) ∘ f) x = _
    rw [hcomp.mfderiv]
    ext v
    change (show ℝ from (mfderiv I 𝓘(ℝ, ℝ) f x) v) * ((f x - b) + (f x - a)) =
      ((f x - b) + (f x - a)) * (show ℝ from (mfderiv I 𝓘(ℝ, ℝ) f x) v)
    exact mul_comm _ _
  intro hz
  change mfderiv I 𝓘(ℝ, ℝ) (fun y => (f y - a) * (f y - b)) x = 0 at hz
  have he : (((f x - b) + (f x - a)) • mfderiv I 𝓘(ℝ, ℝ) f x :
      TangentSpace I x →L[ℝ] ℝ) = 0 := hder.symm.trans hz
  rcases smul_eq_zero.mp he with hzero | hzero
  · rcases hend with ha | hb
    · rw [ha] at hzero
      linarith
    · rw [hb] at hzero
      linarith
  · exact hreg hzero

end DefiningFunction

section Kernel

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The smooth product with the level and the band given as arbitrary sets equal to the regular
level and to the regular sublevel of the defining function. -/
private theorem flowBand_aux {m : ℕ} (hdim : Module.finrank ℝ E = m + 1) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b c : ℝ} (hab : a < b) (hc : c ∈ Icc a b)
    (hreg : ∀ x, f x ∈ Icc a b → ¬ IsCriticalPointAt I f x) {Φ : ℝ → M → M}
    (hΦc : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2))
    (hΦadd : ∀ s t x, Φ (s + t) x = Φ t (Φ s x)) (hΦ0 : ∀ x, Φ 0 x = x)
    (hval : ∀ x, f x ∈ Icc a b → ∀ s ∈ Icc a b, f (Φ (s - f x) x) = s)
    {L K : Set M} (hL : {x | f x = c} = L)
    (hK : sublevel (fun x => (f x - a) * (f x - b)) 0 = K) :
    haveI : Fact (a < b) := ⟨hab⟩
    ∃ (cs₁ : ChartedSpace (MorseModel m) L) (cs₂ : ChartedSpace (MorseHalfSpace m) K),
      letI := cs₁
      letI := cs₂
      IsManifold 𝓘(ℝ, MorseModel m) ∞ L ∧ IsManifold (morseModelWithCornersHalfSpace m) ∞ K ∧
      ContMDiff 𝓘(ℝ, MorseModel m) I ∞ (fun x : L => (x : M)) ∧
      ContMDiff (morseModelWithCornersHalfSpace m) I ∞ (fun y : K => (y : M)) ∧
      (∀ y : K, (morseModelWithCornersHalfSpace m).IsBoundaryPoint y ↔
        f (y : M) = a ∨ f (y : M) = b) ∧
      ∃ d : Diffeomorph ((𝓘(ℝ, MorseModel m)).prod (𝓡∂ 1)) (morseModelWithCornersHalfSpace m)
          (L × Icc a b) K ∞,
        (∀ p, (d p : M) = Φ ((p.2 : ℝ) - c) p.1) ∧
        (∀ y, ((d.symm y).1 : M) = Φ (c - f y) y) ∧
        (∀ y, ((d.symm y).2 : ℝ) = f y) := by
  subst hL hK
  have : Fact (a < b) := ⟨hab⟩
  let e : E ≃L[ℝ] MorseModel (m + 1) :=
    ContinuousLinearEquiv.ofFinrankEq (hdim.trans (Module.finrank_fin_fun ℝ).symm)
  let J := I.transContinuousLinearEquiv e
  have hfJ : ContMDiff J 𝓘(ℝ, ℝ) ∞ f := (e.contMDiff_transContinuousLinearEquiv_left).mpr hf
  have hregJ : ∀ x, f x ∈ Icc a b → ¬ IsCriticalPointAt J f x := fun x hx hcr =>
    hreg x hx ((isCriticalPointAt_transContinuousLinearEquiv_iff I e f x).mp hcr)
  have hregc : ∀ x, f x = c → ¬ IsCriticalPointAt J f x := fun x hx =>
    hregJ x (by rw [hx]; exact hc)
  set g : M → ℝ := fun x => (f x - a) * (f x - b) with hgdef
  have hgJ : ContMDiff J 𝓘(ℝ, ℝ) ∞ g := (hfJ.sub contMDiff_const).mul (hfJ.sub contMDiff_const)
  have hgband : ∀ x, g x ≤ 0 ↔ f x ∈ Icc a b := fun x => by
    have h := congrArg (fun s : Set M => x ∈ s) (sublevel_bandDefiningFunction f hab.le)
    exact iff_of_eq h
  have hregg : ∀ x, g x = 0 → ¬ IsCriticalPointAt J g x := fun x hx =>
    bandDefiningFunction_regular hab ((hfJ x).mdifferentiableAt (by simp)) hx
      (hregJ x ((hgband x).mp hx.le))
  let T : M ≃ₘ⟮I, J⟯ M := ContinuousLinearEquiv.toTransContinuousLinearEquiv I M e
  have hΦJ : ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ (fun q : ℝ × M => Φ q.1 q.2) :=
    (e.contMDiff_transContinuousLinearEquiv_right.mpr hΦc).comp
      (contMDiff_fst.prodMk (T.symm.contMDiff.comp contMDiff_snd))
  let cs₁ : ChartedSpace (MorseModel m) ↥({x | f x = c} : Set M) :=
    manifoldLevelSetChartedSpace J f c hfJ hregc
  let cs₂ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g 0) :=
    manifoldSublevelChartedSpace J g 0 hgJ hregg
  have hm₁ : IsManifold 𝓘(ℝ, MorseModel m) ∞ ↥({x | f x = c} : Set M) :=
    manifoldLevelSetIsManifold J f c hfJ hregc
  have hm₂ : IsManifold (morseModelWithCornersHalfSpace m) ∞ (SublevelSpace g 0) :=
    manifoldSublevelIsManifold J g 0 hgJ hregg
  have hincA : ContMDiff 𝓘(ℝ, MorseModel m) J ∞
      (fun x : ↥({x | f x = c} : Set M) => (x : M)) :=
    contMDiff_levelSetInclusion J f c hfJ hregc
  have hincB : ContMDiff (morseModelWithCornersHalfSpace m) J ∞
      (fun y : SublevelSpace g 0 => (y : M)) :=
    contMDiff_manifoldSublevelInclusion (I := J) g 0 hgJ hregg
  -- the two maps
  have hlev : ∀ x : ↥({x | f x = c} : Set M), f x = c := fun x => x.2
  have hfwd : ∀ p : ↥({x | f x = c} : Set M) × Icc a b, g (Φ ((p.2 : ℝ) - c) p.1) ≤ 0 := by
    intro p
    have h := hval p.1 (by rw [hlev p.1]; exact hc) p.2 p.2.2
    rw [hlev p.1] at h
    rw [hgband, h]
    exact p.2.2
  have hbwd : ∀ y : SublevelSpace g 0, f (Φ (c - f y) y) = c := fun y =>
    hval y ((hgband y).mp y.2) c hc
  let eqv : (↥({x | f x = c} : Set M) × Icc a b) ≃ SublevelSpace g 0 :=
    { toFun := fun p => ⟨Φ ((p.2 : ℝ) - c) p.1, hfwd p⟩
      invFun := fun y => (⟨Φ (c - f y) y, hbwd y⟩, ⟨f y, (hgband y).mp y.2⟩)
      left_inv := by
        intro p
        have h := hval p.1 (by rw [hlev p.1]; exact hc) p.2 p.2.2
        rw [hlev p.1] at h
        apply Prod.ext
        · apply Subtype.ext
          change Φ (c - f (Φ ((p.2 : ℝ) - c) p.1)) (Φ ((p.2 : ℝ) - c) p.1) = p.1
          rw [h, ← hΦadd, sub_add_sub_cancel, sub_self, hΦ0]
        · apply Subtype.ext
          exact h
      right_inv := by
        intro y
        apply Subtype.ext
        change Φ (f y - c) (Φ (c - f y) y) = y
        rw [← hΦadd, sub_add_sub_cancel, sub_self, hΦ0] }
  have hamb : ContMDiff ((𝓘(ℝ, MorseModel m)).prod (𝓡∂ 1)) J ∞
      (fun p : ↥({x | f x = c} : Set M) × Icc a b => Φ ((p.2 : ℝ) - c) p.1) :=
    hΦJ.comp (((contMDiff_subtypeVal_Icc.comp contMDiff_snd).sub contMDiff_const).prodMk
      (hincA.comp contMDiff_fst))
  have hto : ContMDiff ((𝓘(ℝ, MorseModel m)).prod (𝓡∂ 1)) (morseModelWithCornersHalfSpace m) ∞
      eqv :=
    contMDiff_sublevelCorestrict (I := J) g 0 hgJ hregg _ hamb hfwd
  have hheight : ContMDiff (morseModelWithCornersHalfSpace m) 𝓘(ℝ, ℝ) ∞
      (fun y : SublevelSpace g 0 => f y) := hfJ.comp hincB
  have hamb' : ContMDiff (morseModelWithCornersHalfSpace m) J ∞
      (fun y : SublevelSpace g 0 => Φ (c - f y) y) :=
    hΦJ.comp ((contMDiff_const.sub hheight).prodMk hincB)
  have hfirst : ContMDiff (morseModelWithCornersHalfSpace m) 𝓘(ℝ, MorseModel m) ∞
      (fun y : SublevelSpace g 0 => (⟨Φ (c - f y) y, hbwd y⟩ : ↥({x | f x = c} : Set M))) :=
    contMDiff_levelSet_factor J f c hfJ hregc _ hamb' hbwd
  have hsecond : ContMDiff (morseModelWithCornersHalfSpace m) (𝓡∂ 1) ∞
      (fun y : SublevelSpace g 0 => (⟨f y, (hgband y).mp y.2⟩ : Icc a b)) := by
    rw [contMDiff_iff_comp_subtypeVal_Icc]
    exact ⟨hheight.continuous.subtype_mk _, hheight⟩
  have hinv : ContMDiff (morseModelWithCornersHalfSpace m) ((𝓘(ℝ, MorseModel m)).prod (𝓡∂ 1)) ∞
      eqv.symm := hfirst.prodMk hsecond
  refine ⟨cs₁, cs₂, hm₁, hm₂, e.contMDiff_transContinuousLinearEquiv_right.mp hincA,
    e.contMDiff_transContinuousLinearEquiv_right.mp hincB, ?_,
    ⟨{ toEquiv := eqv, contMDiff_toFun := hto, contMDiff_invFun := hinv },
      fun _ => rfl, fun _ => rfl, fun _ => rfl⟩⟩
  intro y
  rw [manifoldSublevel_isBoundaryPoint_iff J g 0 hgJ hregg y]
  exact mul_eq_zero.trans (or_congr sub_eq_zero sub_eq_zero)

/-- **Smooth product of a regular band along a flow (kernel).** Let `f` be smooth, regular on
its band `f⁻¹[a, b]` (`a < b`), `c ∈ [a, b]`, and let `Φ` be a jointly smooth flow with
`f (Φ (s - f x) x) = s` for `x` in the band and `s ∈ [a, b]`. The level `f⁻¹(c)` (a manifold),
the band (a manifold with boundary `f⁻¹{a, b}`) and `Icc a b` carry embedded smooth structures,
and `(x, u) ↦ Φ (u - c) x` is a diffeomorphism `f⁻¹(c) × [a, b] ≅ f⁻¹[a, b]`. -/
theorem exists_flowBand_diffeomorph {m : ℕ} (hdim : Module.finrank ℝ E = m + 1) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b c : ℝ} (hab : a < b) (hc : c ∈ Icc a b)
    (hreg : ∀ x, f x ∈ Icc a b → ¬ IsCriticalPointAt I f x) {Φ : ℝ → M → M}
    (hΦc : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2))
    (hΦadd : ∀ s t x, Φ (s + t) x = Φ t (Φ s x)) (hΦ0 : ∀ x, Φ 0 x = x)
    (hval : ∀ x, f x ∈ Icc a b → ∀ s ∈ Icc a b, f (Φ (s - f x) x) = s) :
    haveI : Fact (a < b) := ⟨hab⟩
    ∃ (cs₁ : ChartedSpace (MorseModel m) ↥({x | f x = c} : Set M))
      (cs₂ : ChartedSpace (MorseHalfSpace m) ↥(f ⁻¹' Icc a b)),
      letI := cs₁
      letI := cs₂
      IsManifold 𝓘(ℝ, MorseModel m) ∞ ↥({x | f x = c} : Set M) ∧
      IsManifold (morseModelWithCornersHalfSpace m) ∞ ↥(f ⁻¹' Icc a b) ∧
      ContMDiff 𝓘(ℝ, MorseModel m) I ∞ (fun x : ↥({x | f x = c} : Set M) => (x : M)) ∧
      ContMDiff (morseModelWithCornersHalfSpace m) I ∞ (fun y : ↥(f ⁻¹' Icc a b) => (y : M)) ∧
      (∀ y : ↥(f ⁻¹' Icc a b), (morseModelWithCornersHalfSpace m).IsBoundaryPoint y ↔
        f (y : M) = a ∨ f (y : M) = b) ∧
      ∃ d : Diffeomorph ((𝓘(ℝ, MorseModel m)).prod (𝓡∂ 1)) (morseModelWithCornersHalfSpace m)
          (↥({x | f x = c} : Set M) × Icc a b) ↥(f ⁻¹' Icc a b) ∞,
        (∀ p, (d p : M) = Φ ((p.2 : ℝ) - c) p.1) ∧
        (∀ y, ((d.symm y).1 : M) = Φ (c - f y) y) ∧
        (∀ y, ((d.symm y).2 : ℝ) = f y) :=
  flowBand_aux hdim hf hab hc hreg hΦc hΦadd hΦ0 hval rfl
    (sublevel_bandDefiningFunction f hab.le)

end Kernel

section Binding

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- **Smooth product for a function smooth only near its band.** `η` continuous, smooth on an
open `W` containing its compact band `η⁻¹[a, b]` (`a < b`), with nonzero differential on the band,
and a jointly smooth flow `Φ` with `η (Φ (s - η x) x) = s` on the band: the level `η⁻¹(c)`, the band
and `Icc a b` carry embedded smooth structures (boundary of the band = levels `a`, `b`), and
`(x, u) ↦ Φ (u - c) x` is a diffeomorphism `η⁻¹(c) × [a, b] ≅ η⁻¹[a, b]`. -/
theorem exists_flowBand_diffeomorph_of_contMDiffOn {m : ℕ} (hdim : Module.finrank ℝ E = m + 1)
    {η : M → ℝ} (hη : Continuous η) {W : Set M} (hW : IsOpen W)
    (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W) {a b c : ℝ} (hab : a < b) (hc : c ∈ Icc a b)
    (hK : IsCompact (η ⁻¹' Icc a b)) (hKW : η ⁻¹' Icc a b ⊆ W)
    (hregη : ∀ x ∈ η ⁻¹' Icc a b, mfderiv I 𝓘(ℝ, ℝ) η x ≠ 0) {Φ : ℝ → M → M}
    (hΦc : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2))
    (hΦadd : ∀ s t x, Φ (s + t) x = Φ t (Φ s x)) (hΦ0 : ∀ x, Φ 0 x = x)
    (hval : ∀ x, η x ∈ Icc a b → ∀ s ∈ Icc a b, η (Φ (s - η x) x) = s) :
    haveI : Fact (a < b) := ⟨hab⟩
    ∃ (cs₁ : ChartedSpace (MorseModel m) ↥({x | η x = c} : Set M))
      (cs₂ : ChartedSpace (MorseHalfSpace m) ↥(η ⁻¹' Icc a b)),
      letI := cs₁
      letI := cs₂
      IsManifold 𝓘(ℝ, MorseModel m) ∞ ↥({x | η x = c} : Set M) ∧
      IsManifold (morseModelWithCornersHalfSpace m) ∞ ↥(η ⁻¹' Icc a b) ∧
      ContMDiff 𝓘(ℝ, MorseModel m) I ∞ (fun x : ↥({x | η x = c} : Set M) => (x : M)) ∧
      ContMDiff (morseModelWithCornersHalfSpace m) I ∞ (fun y : ↥(η ⁻¹' Icc a b) => (y : M)) ∧
      (∀ y : ↥(η ⁻¹' Icc a b), (morseModelWithCornersHalfSpace m).IsBoundaryPoint y ↔
        η (y : M) = a ∨ η (y : M) = b) ∧
      ∃ d : Diffeomorph ((𝓘(ℝ, MorseModel m)).prod (𝓡∂ 1)) (morseModelWithCornersHalfSpace m)
          (↥({x | η x = c} : Set M) × Icc a b) ↥(η ⁻¹' Icc a b) ∞,
        (∀ p, (d p : M) = Φ ((p.2 : ℝ) - c) p.1) ∧
        (∀ y, ((d.symm y).1 : M) = Φ (c - η y) y) ∧
        (∀ y, ((d.symm y).2 : ℝ) = η y) := by
  obtain ⟨f, hf, ⟨O, hOo, hKO, -, hEq⟩, hlo, hhi⟩ :=
    exists_contMDiff_eqOn_band hη hW hηW hab hK hKW
  have hband : ∀ x, f x ∈ Icc a b ↔ η x ∈ Icc a b := fun x =>
    band_mem_Icc_iff hEq hKO hlo hhi
  have hfη : ∀ x ∈ η ⁻¹' Icc a b, f x = η x := fun x hx => hEq (hKO hx)
  have hreg : ∀ x, f x ∈ Icc a b → ¬ IsCriticalPointAt I f x := by
    intro x hx hcrit
    have hx' : x ∈ η ⁻¹' Icc a b := (hband x).mp hx
    have hloc : f =ᶠ[𝓝 x] η := Filter.eventuallyEq_of_mem (hOo.mem_nhds (hKO hx')) hEq
    apply hregη x hx'
    change mfderiv I 𝓘(ℝ, ℝ) f x = 0 at hcrit
    rw [hloc.symm.mfderiv_eq, hcrit]
    exact ContinuousLinearMap.comp_zero _
  have hvalf : ∀ x, f x ∈ Icc a b → ∀ s ∈ Icc a b, f (Φ (s - f x) x) = s := by
    intro x hx s hs
    have hx' : x ∈ η ⁻¹' Icc a b := (hband x).mp hx
    have h := hval x hx' s hs
    rw [hfη x hx']
    have hin : Φ (s - η x) x ∈ η ⁻¹' Icc a b := by
      change η (Φ (s - η x) x) ∈ Icc a b
      rw [h]
      exact hs
    rw [hfη _ hin]
    exact h
  have hL : {x | f x = c} = {x | η x = c} := Set.ext fun x => band_eq_iff hEq hKO hlo hhi hc
  have hKs : sublevel (fun x => (f x - a) * (f x - b)) 0 = η ⁻¹' Icc a b :=
    (sublevel_bandDefiningFunction f hab.le).trans (Set.ext fun x => hband x)
  obtain ⟨cs₁, cs₂, hm₁, hm₂, hinc₁, hinc₂, hbdry, d, hd, hds₁, hds₂⟩ :=
    flowBand_aux hdim hf hab hc hreg hΦc hΦadd hΦ0 hvalf hL hKs
  refine ⟨cs₁, cs₂, hm₁, hm₂, hinc₁, hinc₂, fun y => ?_, d, hd, fun y => ?_, fun y => ?_⟩
  · rw [hbdry y, hfη y y.2]
  · rw [hds₁ y, hfη y y.2]
  · rw [hds₂ y, hfη y y.2]

omit [I.Boundaryless] [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] in
private theorem mfderiv_ne_zero_of_mvfderiv_pos {η : M → ℝ} {x : M}
    {v : TangentSpace I x} (h : 0 < mvfderiv (I := I) η x v) : mfderiv I 𝓘(ℝ, ℝ) η x ≠ 0 := by
  intro h0
  have hz : mvfderiv (I := I) η x v = 0 := by
    change NormedSpace.fromTangentSpace (η x) (mfderiv I 𝓘(ℝ, ℝ) η x v) = 0
    rw [h0]
    rfl
  linarith

/-- **LC46 in the smooth category.** For `η` smooth on an open `W` containing its compact band
`K = η⁻¹[a, b]` (`a < b`), and a field `Y` smooth on `W` with `dη(Y) > 0` on `K`: the flow `Φ` of
LC46 (all clauses of `exists_field_band_product_of_contMDiffOn`) and, for this same flow, the
diffeomorphism of manifolds with boundary `η⁻¹(c) × [a, b] ≅ K`, `(x, s) ↦ Φ (s - c) x`. -/
theorem exists_field_band_diffeomorph {m : ℕ} (hdim : Module.finrank ℝ E = m + 1) {η : M → ℝ}
    (hη : Continuous η) {W : Set M} (hW : IsOpen W) (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W)
    {a b c : ℝ} (hab : a < b) (hc : c ∈ Icc a b) (hK : IsCompact (η ⁻¹' Icc a b))
    (hKW : η ⁻¹' Icc a b ⊆ W) (Y : (x : M) → TangentSpace I x)
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun x => (⟨x, Y x⟩ : TangentBundle I M)) W)
    (hpos : ∀ x ∈ η ⁻¹' Icc a b, 0 < mvfderiv (I := I) η x (Y x)) :
    haveI : Fact (a < b) := ⟨hab⟩
    ∃ Φ : ℝ → Diffeomorph I I M M ∞,
      Φ 0 = Diffeomorph.refl I M ∞ ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => Φ p.1 p.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => (Φ p.1).symm p.2) ∧
      (∀ s t x, Φ (s + t) x = Φ t (Φ s x)) ∧
      (∀ x, η x ∈ Icc a b → ∀ s ∈ Icc a b, η (Φ (s - η x) x) = s) ∧
      (∃ S : Set M, IsCompact S ∧ S ⊆ W ∧ ∀ t x, x ∉ S → Φ t x = x ∧ (Φ t).symm x = x) ∧
      (∀ x t, η (Φ t x) ∈ Icc a b →
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) t ((1 : ℝ →L[ℝ] ℝ).smulRight
          ((mvfderiv (I := I) η (Φ t x) (Y (Φ t x)))⁻¹ • Y (Φ t x)))) ∧
      ∃ (cs₁ : ChartedSpace (MorseModel m) ↥({x | η x = c} : Set M))
        (cs₂ : ChartedSpace (MorseHalfSpace m) ↥(η ⁻¹' Icc a b)),
        letI := cs₁
        letI := cs₂
        IsManifold 𝓘(ℝ, MorseModel m) ∞ ↥({x | η x = c} : Set M) ∧
        IsManifold (morseModelWithCornersHalfSpace m) ∞ ↥(η ⁻¹' Icc a b) ∧
        ContMDiff 𝓘(ℝ, MorseModel m) I ∞ (fun x : ↥({x | η x = c} : Set M) => (x : M)) ∧
        ContMDiff (morseModelWithCornersHalfSpace m) I ∞ (fun y : ↥(η ⁻¹' Icc a b) => (y : M)) ∧
        (∀ y : ↥(η ⁻¹' Icc a b), (morseModelWithCornersHalfSpace m).IsBoundaryPoint y ↔
          η (y : M) = a ∨ η (y : M) = b) ∧
        ∃ d : Diffeomorph ((𝓘(ℝ, MorseModel m)).prod (𝓡∂ 1)) (morseModelWithCornersHalfSpace m)
            (↥({x | η x = c} : Set M) × Icc a b) ↥(η ⁻¹' Icc a b) ∞,
          (∀ p, (d p : M) = Φ ((p.2 : ℝ) - c) p.1) ∧
          (∀ y, ((d.symm y).1 : M) = Φ (c - η y) y) ∧
          (∀ y, ((d.symm y).2 : ℝ) = η y) := by
  obtain ⟨Φ, hΦ0, hΦc, hΦs, hΦadd, hval, hsupp, hvel, -⟩ :=
    exists_field_band_product_of_contMDiffOn hη hW hηW hab hc hK hKW Y hY hpos
  have hΦ0' : ∀ x, Φ 0 x = x := fun x => by rw [hΦ0]; rfl
  exact ⟨Φ, hΦ0, hΦc, hΦs, hΦadd, hval, hsupp, hvel,
    exists_flowBand_diffeomorph_of_contMDiffOn (Φ := fun t x => Φ t x) hdim hη hW hηW hab hc hK
      hKW (fun x hx => mfderiv_ne_zero_of_mvfderiv_pos (hpos x hx)) hΦc hΦadd hΦ0' hval⟩

end Binding

section Riemannian

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **LC33 in the smooth category** (PC Riemannian setting, LC30 radial function `η`). The flow `Φ`
of `X = ∇η / |∇η|²` of `radialBand_gradient_product`, with its velocity, speed bound
`|X| ≤ (1-ε)⁻¹` and track estimate `c_ε = (1-2ε)/(1-ε)`, and, for this same flow, the
diffeomorphism of manifolds with boundary `F : η⁻¹(1) × [1/8, 3] ≅ η⁻¹[1/8, 3]`,
`F (x, u) = Φ (u - 1) x`, `F⁻¹ y = (Φ (1 - η y) y, η y)`; the level `η⁻¹(1)` carries its regular-level
structure, the band its regular-domain structure with boundary `η⁻¹{1/8, 3}`. -/
theorem radialBand_gradient_diffeomorph {m : ℕ} (hdim : Module.finrank ℝ E = m + 1)
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g) {p : M}
    {η : M → ℝ} {ε : ℝ≥0} {e : ℝ} (hε1 : (ε : ℝ) < 1) (he : e < 1 / 40)
    (hclose : ∀ x, |η x - dist p x| < e) (hlip : LipschitzWith ε (fun x => η x - dist p x))
    {W : Set M} (hW : IsOpen W) (hCW : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 → x ∈ W)
    (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W)
    (hgrad : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 →
      (1 - (ε : ℝ)) ^ 2 ≤
        g.inner x (gradientFun (I := I) g η x) (gradientFun (I := I) g η x)) :
    haveI : Fact ((1 / 8 : ℝ) < 3) := ⟨by norm_num⟩
    ∃ Φ : ℝ → Diffeomorph I I M M ∞,
      Φ 0 = Diffeomorph.refl I M ∞ ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => (Φ q.1).symm q.2) ∧
      (∀ s t x, Φ (s + t) x = Φ t (Φ s x)) ∧
      (∀ x, η x ∈ Icc (1 / 8 : ℝ) 3 → ∀ s ∈ Icc (1 / 8 : ℝ) 3, η (Φ (s - η x) x) = s) ∧
      (∃ S : Set M, IsCompact S ∧ S ⊆ W ∧ ∀ t x, x ∉ S → Φ t x = x ∧ (Φ t).symm x = x) ∧
      (∀ x t, η (Φ t x) ∈ Icc (1 / 8 : ℝ) 3 →
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) t ((1 : ℝ →L[ℝ] ℝ).smulRight
          ((g.inner (Φ t x) (gradientFun (I := I) g η (Φ t x))
            (gradientFun (I := I) g η (Φ t x)))⁻¹ • gradientFun (I := I) g η (Φ t x)))) ∧
      (∀ y, η y ∈ Icc (1 / 8 : ℝ) 3 →
        √(g.inner y ((g.inner y (gradientFun (I := I) g η y) (gradientFun (I := I) g η y))⁻¹ •
            gradientFun (I := I) g η y)
          ((g.inner y (gradientFun (I := I) g η y) (gradientFun (I := I) g η y))⁻¹ •
            gradientFun (I := I) g η y)) ≤ (1 - (ε : ℝ))⁻¹) ∧
      (∀ x, η x = 1 → ∀ s t, 1 / 8 ≤ s → s ≤ t → t ≤ 3 →
        (1 - 2 * (ε : ℝ)) / (1 - ε) * (t - s) ≤
          dist p (Φ (t - 1) x) - dist p (Φ (s - 1) x)) ∧
      ∃ (cs₁ : ChartedSpace (MorseModel m) ↥({x | η x = 1} : Set M))
        (cs₂ : ChartedSpace (MorseHalfSpace m) ↥(η ⁻¹' Icc (1 / 8 : ℝ) 3)),
        letI := cs₁
        letI := cs₂
        IsManifold 𝓘(ℝ, MorseModel m) ∞ ↥({x | η x = 1} : Set M) ∧
        IsManifold (morseModelWithCornersHalfSpace m) ∞ ↥(η ⁻¹' Icc (1 / 8 : ℝ) 3) ∧
        ContMDiff 𝓘(ℝ, MorseModel m) I ∞ (fun x : ↥({x | η x = 1} : Set M) => (x : M)) ∧
        ContMDiff (morseModelWithCornersHalfSpace m) I ∞
          (fun y : ↥(η ⁻¹' Icc (1 / 8 : ℝ) 3) => (y : M)) ∧
        (∀ y : ↥(η ⁻¹' Icc (1 / 8 : ℝ) 3), (morseModelWithCornersHalfSpace m).IsBoundaryPoint y ↔
          η (y : M) = 1 / 8 ∨ η (y : M) = 3) ∧
        ∃ d : Diffeomorph ((𝓘(ℝ, MorseModel m)).prod (𝓡∂ 1)) (morseModelWithCornersHalfSpace m)
            (↥({x | η x = 1} : Set M) × Icc (1 / 8 : ℝ) 3) ↥(η ⁻¹' Icc (1 / 8 : ℝ) 3) ∞,
          (∀ q, (d q : M) = Φ ((q.2 : ℝ) - 1) q.1) ∧
          (∀ y, ((d.symm y).1 : M) = Φ (1 - η y) y) ∧
          (∀ y, ((d.symm y).2 : ℝ) = η y) := by
  have : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  obtain ⟨Φ, hΦ0, hΦc, hΦs, hΦadd, hval, hsupp, hvel, hspeed, htrack, -⟩ :=
    radialBand_gradient_product g hEnorm hε1 he hclose hlip hW hCW hηW hgrad
  have hη : Continuous η :=
    (hlip.continuous.add (continuous_const.dist continuous_id)).congr
      (fun x => sub_add_cancel (η x) (dist p x))
  have : ProperSpace M :=
    ⟨fun x r => DifferentialGeometry.Geometry.Topology.soul_isCompact_closedBall
      (I := I) g hEnorm x r⟩
  have hK : IsCompact (η ⁻¹' Icc (1 / 8 : ℝ) 3) :=
    isCompact_preimage_of_abs_sub_dist_lt hη hclose isCompact_Icc
  have hKann := radialBand_subset_annulus hclose he
  have hKW : η ⁻¹' Icc (1 / 8 : ℝ) 3 ⊆ W := fun x hx =>
    hCW x (hKann hx).1.le (hKann hx).2.le
  have hregη : ∀ x ∈ η ⁻¹' Icc (1 / 8 : ℝ) 3, mfderiv I 𝓘(ℝ, ℝ) η x ≠ 0 := by
    intro x hx
    apply mfderiv_ne_zero_of_mvfderiv_pos (v := gradientFun (I := I) g η x)
    rw [← inner_gradientFun (I := I) g η x]
    have hm : 0 < 1 - (ε : ℝ) := by linarith
    exact lt_of_lt_of_le (by positivity) (hgrad x (hKann hx).1.le (hKann hx).2.le)
  have hΦ0' : ∀ x, Φ 0 x = x := fun x => by rw [hΦ0]; rfl
  exact ⟨Φ, hΦ0, hΦc, hΦs, hΦadd, hval, hsupp, hvel, hspeed, htrack,
    exists_flowBand_diffeomorph_of_contMDiffOn (Φ := fun t x => Φ t x) hdim hη hW hηW
      (by norm_num) ⟨by norm_num, by norm_num⟩ hK hKW hregη hΦc hΦadd hΦ0' hval⟩

end Riemannian

end DifferentialGeometry.Geometry.Collapse
