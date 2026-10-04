import DifferentialGeometry.Geometry.Collapse.SublevelCore.FieldBandVerticalChart
import DifferentialGeometry.Topology.Collar.InteriorLevelChart
import DifferentialGeometry.Topology.SigmaCompactOpen
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Band products over a vertical chart without a given field, and inside the interior (F-e, E3)

Row E3 of the F-e sheet: the band product of E5 (`exists_band_diffeomorph_of_vertical_chart`)
took the field `Y` with `df(Y) > 0` as data. Here the field is produced, and the ambient may have
boundary.

* `exists_contMDiff_field_mvfderiv_pos`: a smooth function without critical points on a closed set
  `K` has a smooth vector field `Y` with `df(Y) > 0` on `K` (convex local-to-global principle for
  sections; no metric, so any model, e.g. the sup-norm `MorseModel`).
* `exists_band_diffeomorph_of_vertical_chart_of_band`: if the whole band `f⁻¹[a, b]` lies in the
  image of the vertical chart, `f` is regular there (vertical derivative), and the field above is
  the field of E5.
* `exists_band_diffeomorph_of_interior_vertical_chart`: the same for any ambient manifold `M`
  (boundary or corners allowed; model on `E`, `E ≃L MorseModel (m + 1)`) when the vertical chart
  takes values in the interior. E5 is applied on the intrinsic interior with its interior atlas
  transported to `MorseModel (m + 1)` (pattern of `Topology/Collar/InteriorLevelChart.lean`), and
  the structure is pulled back to the band of `M`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Manifold DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Geometry.Collapse

section Field

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- A smooth function without critical points on a closed set `K` has a smooth vector field on
which its derivative is positive along `K`. -/
theorem exists_contMDiff_field_mvfderiv_pos [T2Space M] [SigmaCompactSpace M] {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {K : Set M} (hK : IsClosed K)
    (hreg : ∀ x ∈ K, mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    ∃ Y : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x => (⟨x, Y x⟩ : TangentBundle I M)) ∧
        ∀ x ∈ K, 0 < mvfderiv I f x (Y x) := by
  classical
  have hloc : ∀ x₀ : M, ∃ U ∈ 𝓝 x₀, ∃ sl : (x : M) → TangentSpace I x,
      ContMDiffOn I I.tangent ∞ (fun y => (⟨y, sl y⟩ : TangentBundle I M)) U ∧
      ∀ y ∈ U, sl y ∈ {w : TangentSpace I y | y ∈ K → 0 < mvfderiv I f y w} := by
    intro x₀
    by_cases hx₀ : x₀ ∈ K
    · -- a direction with positive derivative at `x₀`, extended constantly in a trivialization
      obtain ⟨w₀, hw₀⟩ : ∃ w₀ : TangentSpace I x₀, 0 < mvfderiv I f x₀ w₀ := by
        by_contra hneg
        push Not at hneg
        apply hreg x₀ hx₀
        apply ContinuousLinearMap.ext
        intro v
        have h1 := hneg v
        have h2 := hneg (-v)
        rw [map_neg] at h2
        have h3 : mvfderiv I f x₀ v = 0 := le_antisymm h1 (by linarith)
        exact h3
      let t := trivializationAt E (TangentSpace I : M → Type _) x₀
      have hxt : x₀ ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
      let v₀ : E := t.continuousLinearEquivAt ℝ x₀ hxt w₀
      let sl : (y : M) → TangentSpace I y := fun y => t.symmL ℝ y v₀
      have hon : ContMDiffOn I I.tangent ∞ (fun y => (⟨y, sl y⟩ : TangentBundle I M))
          t.baseSet := by
        rw [t.contMDiffOn_section_baseSet_iff]
        refine (contMDiffOn_const (c := v₀)).congr fun y hy => ?_
        change (t ⟨y, t.symmL ℝ y v₀⟩).2 = v₀
        rw [t.symmL_apply (R := ℝ) hy, t.apply_mk_symm hy]
      have hsl0 : sl x₀ = w₀ := by
        change t.symmL ℝ x₀ v₀ = w₀
        rw [← t.symm_continuousLinearEquivAt_eq (R := ℝ) hxt]
        exact (t.continuousLinearEquivAt ℝ x₀ hxt).symm_apply_apply w₀
      have hcont : ContinuousAt (fun y => mvfderiv I f y (sl y)) x₀ := by
        have ht := (hf.contMDiff_tangentMap (m := ∞) (by simp)).contMDiffAt.comp x₀
          (hon.contMDiffAt (t.open_baseSet.mem_nhds hxt))
        exact ((contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).contMDiffAt.comp x₀
          ht).continuousAt
      have hpos0 : 0 < mvfderiv I f x₀ (sl x₀) := by rw [hsl0]; exact hw₀
      refine ⟨t.baseSet ∩ {y | 0 < mvfderiv I f y (sl y)},
        Filter.inter_mem (t.open_baseSet.mem_nhds hxt)
          (hcont.preimage_mem_nhds (Ioi_mem_nhds hpos0)), sl,
        hon.mono inter_subset_left, fun y hy _ => hy.2⟩
    · refine ⟨Kᶜ, hK.isOpen_compl.mem_nhds hx₀, fun y => 0, ?_, fun y hy hyK => (hy hyK).elim⟩
      exact (Bundle.contMDiff_zeroSection ℝ (TangentSpace I : M → Type _) (F := E)
        (IB := I)).contMDiffOn
  obtain ⟨s, hs⟩ := exists_contMDiffSection_forall_mem_convex_of_local I (n := ⊤)
    (F_fiber := E) (TangentSpace I : M → Type _)
    (fun y => {w : TangentSpace I y | y ∈ K → 0 < mvfderiv I f y w})
    (fun y => by
      by_cases hy : y ∈ K
      · have h : {w : TangentSpace I y | y ∈ K → 0 < mvfderiv I f y w} =
            (mvfderiv I f y).toLinearMap ⁻¹' Ioi 0 := by
          ext w
          simp only [mem_ofPred_eq, hy, true_implies, mem_preimage, mem_Ioi]
          rfl
        rw [h]
        exact (convex_Ioi 0).linear_preimage _
      · have h : {w : TangentSpace I y | y ∈ K → 0 < mvfderiv I f y w} = univ := by
          ext w
          simp only [mem_ofPred_eq, hy, false_implies, mem_univ]
        rw [h]
        exact convex_univ)
    hloc
  exact ⟨fun x => s x, s.contMDiff, fun x hx => hs x hx⟩

end Field

section Morse

variable {m : ℕ} {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ (MorseModel (m + 1)) H}
  [I.Boundaryless] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {S : Type} [TopologicalSpace S] [ChartedSpace G S] [IsManifold J ∞ S]

/-- **E5 without a field.** If the compact band `f⁻¹[a, b]` lies in the image of a `C^k` vertical
chart over a compact `S` with positive vertical derivative, and the bottom level is crossed by
every vertical, then the band (regular-sublevel structure, boundary `f⁻¹{a, b}`) is
diffeomorphic to `S × [a, b]` carrying the second coordinate to `f`. -/
theorem exists_band_diffeomorph_of_vertical_chart_of_band [Nonempty S] [CompactSpace S]
    [T2Space S] (hdim : Module.finrank ℝ F = m) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} (hab : a < b) (hK : IsCompact (f ⁻¹' Icc a b)) {k : ℕ} (hk : 1 ≤ k)
    {a₀ b₀ : ℝ} {j : S × ℝ → M}
    (hj : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) I k j (univ ×ˢ Ioo a₀ b₀))
    (hjinj : InjOn j (univ ×ˢ Ioo a₀ b₀))
    (hjd : ∀ p ∈ (univ : Set S) ×ˢ Ioo a₀ b₀, Injective (mfderiv (J.prod 𝓘(ℝ, ℝ)) I j p))
    (hvert : ∀ x : S, ∀ s ∈ Ioo a₀ b₀, 0 < deriv (fun s : ℝ => f (j (x, s))) s)
    (hcross : ∀ x : S, ∃ s ∈ Ioo a₀ b₀, f (j (x, s)) = a)
    (hband : ∀ z, f z ∈ Icc a b → z ∈ j '' (univ ×ˢ Ioo a₀ b₀)) :
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
  have hk0 : (k : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hk)
  have hD : IsOpen ((univ : Set S) ×ˢ Ioo a₀ b₀) := isOpen_univ.prod isOpen_Ioo
  have hreg : ∀ x ∈ f ⁻¹' Icc a b, mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0 := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := hband x hx
    exact Topology.mfderiv_ne_zero_of_deriv_vertical_pos ((hf (j p)).mdifferentiableAt (by simp))
      ((hj.contMDiffAt (hD.mem_nhds hp)).mdifferentiableAt hk0) (hvert p.1 p.2 hp.2)
  obtain ⟨Y, hY, hpos⟩ :=
    exists_contMDiff_field_mvfderiv_pos hf (isClosed_Icc.preimage hf.continuous) hreg
  exact exists_band_diffeomorph_of_vertical_chart hdim hf hab hK Y hY hpos hk hj
    hjinj hjd hvert hcross
    (fun z hz => hband z (by rw [hz]; exact ⟨le_rfl, hab.le⟩))

end Morse

section Interior

variable {m : ℕ} {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {S : Type} [TopologicalSpace S] [ChartedSpace G S] [IsManifold J ∞ S]

/-- **E3 (band product in a manifold with boundary).** A compact band `f⁻¹[a, b]` inside the
image of an interior `C^k` vertical chart over a compact `S`, with positive vertical derivative
and bottom level crossed by every vertical, carries a manifold-with-boundary structure (boundary
`f⁻¹{a, b}`, smooth inclusion into `M`) for which it is diffeomorphic to `S × [a, b]`, carrying
the second coordinate to `f`. -/
theorem exists_band_diffeomorph_of_interior_vertical_chart [T2Space M] [SigmaCompactSpace M]
    [Nonempty S] [CompactSpace S] [T2Space S] (e : E ≃L[ℝ] MorseModel (m + 1))
    (hdim : Module.finrank ℝ F = m) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (hab : a < b) (hK : IsCompact (f ⁻¹' Icc a b)) {k : ℕ} (hk : 1 ≤ k) {a₀ b₀ : ℝ}
    {j : S × ℝ → M} (hj : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) I k j (univ ×ˢ Ioo a₀ b₀))
    (hjinj : InjOn j (univ ×ˢ Ioo a₀ b₀))
    (hjd : ∀ p ∈ (univ : Set S) ×ˢ Ioo a₀ b₀, Injective (mfderiv (J.prod 𝓘(ℝ, ℝ)) I j p))
    (hjint : ∀ p ∈ (univ : Set S) ×ˢ Ioo a₀ b₀, I.IsInteriorPoint (j p))
    (hvert : ∀ x : S, ∀ s ∈ Ioo a₀ b₀, 0 < deriv (fun s : ℝ => f (j (x, s))) s)
    (hcross : ∀ x : S, ∃ s ∈ Ioo a₀ b₀, f (j (x, s)) = a)
    (hband : ∀ z, f z ∈ Icc a b → z ∈ j '' (univ ×ˢ Ioo a₀ b₀)) :
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
  classical
  have : Fact (a < b) := ⟨hab⟩
  have hk0 : (k : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hk)
  set D : Set (S × ℝ) := univ ×ˢ Ioo a₀ b₀ with hDdef
  have hDo : IsOpen D := isOpen_univ.prod isOpen_Ioo
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
  have : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  have hval₀ : ContMDiff 𝓘(ℝ, E) I ∞ (Subtype.val : U → M) :=
    contMDiff_intrinsicInterior_val I ∞ (show (∞ : ℕ∞ω) ≠ 0 from by simp)
  have hval : ContMDiff IJ I ∞ (Subtype.val : U → M) := by
    simpa only [IJ, ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left] using hval₀
  -- the vertical chart, corestricted to the interior
  obtain ⟨x₀⟩ := (inferInstance : Nonempty S)
  obtain ⟨s₀, hs₀, -⟩ := hcross x₀
  let u₀ : U := ⟨j (x₀, s₀), hjint (x₀, s₀) ⟨mem_univ _, hs₀⟩⟩
  let j' : S × ℝ → U := fun p => if h : p ∈ D then ⟨j p, hjint p h⟩ else u₀
  have hj'eq : ∀ p ∈ D, (j' p : M) = j p := fun p hp => by simp only [j', dite_eq_left hp]
  have hj'I : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) I k j' D := by
    intro p hp
    have h : ContMDiffWithinAt (J.prod 𝓘(ℝ, ℝ)) I k (Subtype.val ∘ j') D p :=
      (hj p hp).congr (fun q hq => hj'eq q hq) (hj'eq p hp)
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff (U := U) j' D p).mp h
  have hj' : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) IJ k j' D := by
    rw [ContinuousLinearEquiv.contMDiffOn_transContinuousLinearEquiv_right]
    exact ((contMDiff_id_interiorAtlas I ∞ (M := U)).of_le
      (by exact_mod_cast le_top)).comp_contMDiffOn hj'I
  have hjinj' : InjOn j' D := fun p hp q hq h => hjinj hp hq (by
    rw [← hj'eq p hp, ← hj'eq q hq, h])
  have hjd' : ∀ p ∈ D, Injective (mfderiv (J.prod 𝓘(ℝ, ℝ)) IJ j' p) := by
    intro p hp v w hvw
    apply hjd p hp
    have hev : j =ᶠ[𝓝 p] Subtype.val ∘ j' :=
      Filter.eventuallyEq_of_mem (hDo.mem_nhds hp) fun q hq => (hj'eq q hq).symm
    have hcomp : mfderiv (J.prod 𝓘(ℝ, ℝ)) I j p =
        (mfderiv IJ I (Subtype.val : U → M) (j' p)).comp
          (mfderiv (J.prod 𝓘(ℝ, ℝ)) IJ j' p) :=
      ((((hval (j' p)).mdifferentiableAt (by simp)).hasMFDerivAt.comp p
        ((hj'.contMDiffAt (hDo.mem_nhds hp)).mdifferentiableAt hk0).hasMFDerivAt)
        |>.congr_of_eventuallyEq_abuse hev).mfderiv
    rw [hcomp]
    exact congrArg (mfderiv IJ I (Subtype.val : U → M) (j' p)) hvw
  -- the restricted function
  let f' : U → ℝ := fun y => f y
  have hf' : ContMDiff IJ 𝓘(ℝ, ℝ) ∞ f' := hf.comp hval
  have hvert' : ∀ x : S, ∀ s ∈ Ioo a₀ b₀, 0 < deriv (fun s : ℝ => f' (j' (x, s))) s := by
    intro x s hs
    have hev : (fun s : ℝ => f' (j' (x, s))) =ᶠ[𝓝 s] fun s : ℝ => f (j (x, s)) :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hs) fun t ht => by
        change f (j' (x, t) : M) = f (j (x, t))
        rw [hj'eq (x, t) ⟨mem_univ _, ht⟩]
    rw [hev.deriv_eq]
    exact hvert x s hs
  have hcross' : ∀ x : S, ∃ s ∈ Ioo a₀ b₀, f' (j' (x, s)) = a := by
    intro x
    obtain ⟨s, hs, hfs⟩ := hcross x
    refine ⟨s, hs, ?_⟩
    change f (j' (x, s) : M) = a
    rw [hj'eq (x, s) ⟨mem_univ _, hs⟩, hfs]
  have hint : ∀ z : M, f z ∈ Icc a b → z ∈ (U : Set M) := fun z hz => by
    obtain ⟨p, hp, rfl⟩ := hband z hz
    exact hjint p hp
  have hband' : ∀ z : U, f' z ∈ Icc a b → z ∈ j' '' D := by
    intro z hz
    obtain ⟨p, hp, hpz⟩ := hband z hz
    exact ⟨p, hp, Subtype.ext ((hj'eq p hp).trans hpz)⟩
  have hK' : IsCompact (f' ⁻¹' Icc a b) := by
    rw [Topology.IsInducing.subtypeVal.isCompact_iff]
    convert hK using 1
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hz
      exact ⟨⟨z, hint z hz⟩, hz, rfl⟩
  obtain ⟨cs', hm', hinc', hbd', D', hD'⟩ :=
    exists_band_diffeomorph_of_vertical_chart_of_band (I := IJ) (M := U) hdim hf' hab hK' hk
      hj' hjinj' hjd' hvert' hcross' hband'
  -- pull the structure back to the band of `M`
  let hlev : ↥(f ⁻¹' Icc a b) ≃ₜ ↥(f' ⁻¹' Icc a b) :=
    { toFun := fun y => ⟨⟨y.1, hint y.1 y.2⟩, y.2⟩
      invFun := fun z => ⟨z.1.1, z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let cs := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := MorseHalfSpace m) hlev
  have hm := DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback
    (I := morseModelWithCornersHalfSpace m) (n := ∞) hlev
  let d₁ := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := morseModelWithCornersHalfSpace m) (n := ∞) hlev
  refine ⟨cs, hm, hval.comp (hinc'.comp d₁.contMDiff), fun y => ?_, D'.trans d₁.symm,
    fun p => hD' p⟩
  rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint,
    ((d₁.isLocalDiffeomorph y).isInteriorPoint_iff (by simp)),
    ← ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint]
  exact hbd' (d₁ y)

end Interior

end DifferentialGeometry.Geometry.Collapse
