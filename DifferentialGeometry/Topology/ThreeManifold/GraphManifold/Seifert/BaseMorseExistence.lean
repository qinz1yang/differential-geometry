import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BaseMorse
import DifferentialGeometry.Topology.Morse.RegularLevel.VectorField
import DifferentialGeometry.Topology.Morse.InteriorRestriction
import DifferentialGeometry.Topology.Morse.ExtremumChart
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph
import DifferentialGeometry.Topology.Morse.BoundaryExcellent
import DifferentialGeometry.Topology.Morse.Existence
import DifferentialGeometry.Topology.Morse.CriticalFinite
import DifferentialGeometry.Topology.Morse.Naturality
import DifferentialGeometry.Topology.Manifold.Small
import DifferentialGeometry.Topology.Manifold.Homeomorph.Transport
import Mathlib.Topology.Instances.Shrink
import DifferentialGeometry.Topology.Manifold.OneManifold.CircleClassification

/-!
# Existence of Morse data on the base surface

Lane MD1 of the P1 Morse-decomposition plan, the tiers after T0 (`Seifert/BaseMorse.lean`).

* `circleClassification`: the named Prop `CircleClassification`, from lane CC's classification of
  compact connected one-manifolds.
* `exists_unitField_of_isCompact`: a smooth vector field `V` with `df V = 1` on a compact set of
  interior regular points of `f`; the unit-speed field of the boundaryless interior, extended by
  zero.
* `exists_baseMorseData_of_small`: for a surface in `Type`, an excellent Morse function (the
  boundary defining function of `MO/BoundaryExcellent`, or a positive excellent Morse function on
  a closed surface), levels `a < c₁ - ε < c₁ + ε < ⋯` around the critical values, discs of the
  extrema from the quadratic charts of the interior, and the field.
* `exists_baseMorseData`: any universe, through `Shrink.{0}` with the pulled-back atlas; chart
  expressions agree definitionally, so Hessians and indices transfer unchanged.
* `BaseMorseData.exists_level_zero_eq`: lowering `level 0` to any `a ∈ (0, level 0)` with the same
  function and critical points, by inserting a new bottom level.
-/

set_option autoImplicit false

noncomputable section
open Set Metric Function Bundle
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Morse
open scoped Manifold ContDiff Topology

universe u uE uH uM

namespace GC.Seifert

theorem circleClassification : CircleClassification.{uE, uH, uM} := by
  intro E H F _ _ _ _ _ _ J _ _ _ _ _ hdim
  exact
    DifferentialGeometry.Topology.Manifold.OneManifold.nonempty_circle_diffeomorph_of_finrank_eq_one
      E H F J hdim

section Field

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SecondCountableTopology M]

theorem exists_unitField_of_isCompact {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {K : Set M} (hK : IsCompact K) (hint : ∀ x ∈ K, I.IsInteriorPoint x)
    (hreg : ∀ x ∈ K, mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    ∃ V : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) ∧
      ∀ x ∈ K, mfderiv I 𝓘(ℝ, ℝ) f x (V x) = 1 := by
  classical
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞ (by simp) (M := M)
  let _ : ChartedSpace E U := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  have _ : IsManifold 𝓘(ℝ, E) ∞ U := DifferentialGeometry.Manifold.interiorIsManifold I ∞
  have : LocallyCompactSpace U := ChartedSpace.locallyCompactSpace E U
  let g : U → ℝ := fun y => f y
  have hval : ContMDiff 𝓘(ℝ, E) I ∞ (Subtype.val : U → M) :=
    DifferentialGeometry.Manifold.contMDiff_intrinsicInterior_val I ∞ (by simp)
  have hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g := hf.comp hval
  have hgold : ContMDiff I 𝓘(ℝ, ℝ) ∞ g := hf.comp contMDiff_subtype_val
  let K' : Set U := Subtype.val ⁻¹' K
  have hKU : K ⊆ Subtype.val '' K' := fun x hx => ⟨⟨x, hint x hx⟩, hx, rfl⟩
  have hK' : IsCompact K' := by
    refine Subtype.isCompact_iff.mpr ?_
    rw [subset_antisymm (image_preimage_subset _ _) hKU]
    exact hK
  have hgreg : ∀ y ∈ K', ¬ IsCriticalPointAt 𝓘(ℝ, E) g y := by
    intro y hy hcrit
    have ho : (show E →L[ℝ] ℝ from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g y) =
        (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) g y) :=
      DifferentialGeometry.Manifold.mfderiv_interiorAtlas I hgold y
    have hu := DifferentialGeometry.Manifold.mfderiv_openRestriction I hf y y.2
    exact hreg y hy (hu.symm.trans (ho.symm.trans hcrit))
  obtain ⟨V, hV, hVc, hVK, -⟩ :=
    exists_unitSpeedVectorField_on_compact 𝓘(ℝ, E) g hg K' hK' hgreg
  let W : (x : M) → TangentSpace I x := fun x =>
    if hx : x ∈ U then mfderiv 𝓘(ℝ, E) I (Subtype.val : U → M) ⟨x, hx⟩ (-V ⟨x, hx⟩) else 0
  refine ⟨W, fun x => ?_, fun x hx => ?_⟩
  · by_cases hxU : x ∈ U
    · have hT : ContMDiff 𝓘(ℝ, E).tangent I.tangent ∞
          (tangentMap 𝓘(ℝ, E) I (Subtype.val : U → M)) :=
        hval.contMDiff_tangentMap (by simp)
      have hneg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
          (fun y : U => (⟨y, -V y⟩ : TangentBundle 𝓘(ℝ, E) U)) := hV.neg_section
      have hid : ContMDiff I 𝓘(ℝ, E) ∞ (id : U → U) :=
        DifferentialGeometry.Manifold.contMDiff_id_interiorAtlas I ∞ (M := U)
      have hcomp : ContMDiff I I.tangent ∞
          (fun y : U => (⟨(y : M), W y⟩ : TangentBundle I M)) := by
        have h := (hT.comp hneg).comp hid
        convert h using 1
        funext y
        simp only [W, y.2, ↓reduceDIte]
        rfl
      exact (contMDiffAt_subtype_iff (f := fun y => (⟨y, W y⟩ : TangentBundle I M))).mp
        (hcomp ⟨x, hxU⟩)
    · let C : Set M := Subtype.val '' tsupport V
      have hC : IsClosed C := (hVc.image continuous_subtype_val).isClosed
      have hxC : x ∉ C := fun ⟨y, _, hy⟩ => hxU (hy ▸ y.2)
      have hzero : (fun y => (⟨y, W y⟩ : TangentBundle I M)) =ᶠ[𝓝 x]
          zeroSection E (TangentSpace I) := by
        filter_upwards [hC.isOpen_compl.mem_nhds hxC] with y hy
        by_cases hyU : y ∈ U
        · have hV0 : V ⟨y, hyU⟩ = 0 :=
            image_eq_zero_of_notMem_tsupport fun h => hy ⟨⟨y, hyU⟩, h, rfl⟩
          simp only [W, hyU, ↓reduceDIte, hV0, neg_zero, map_zero]
          rfl
        · simp only [W, hyU, ↓reduceDIte]
          rfl
      exact (contMDiff_zeroSection ℝ (TangentSpace I) x).congr_of_eventuallyEq hzero
  · have hxU : x ∈ U := hint x hx
    have hchain : mfderiv I 𝓘(ℝ, ℝ) f x
        (mfderiv 𝓘(ℝ, E) I (Subtype.val : U → M) ⟨x, hxU⟩ (-V ⟨x, hxU⟩)) =
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g ⟨x, hxU⟩ (-V ⟨x, hxU⟩) := by
      have h := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := I) (I'' := 𝓘(ℝ, ℝ)) (x := ⟨x, hxU⟩)
        (g := f) (f := (Subtype.val : U → M)) (hf.mdifferentiableAt (by simp))
        (hval.mdifferentiableAt (by simp))
      exact (congrArg (fun L => L (-V ⟨x, hxU⟩)) h).symm
    have h1 := hVK ⟨x, hxU⟩ hx
    change mfderiv I 𝓘(ℝ, ℝ) f x (W x) = 1
    simp only [W, hxU, ↓reduceDIte]
    rw [hchain, map_neg]
    have h1' : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g ⟨x, hxU⟩ (V ⟨x, hxU⟩) = (-1 : ℝ) := h1
    rw [h1']
    exact neg_neg _

end Field

section Thin

private theorem image_closedBall_eq_connectedComponentIn {X : Type*} [TopologicalSpace X]
    [T2Space X] (χ : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) X) {R ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρR : ρ < R) (hsrc : ball 0 R ⊆ χ.source) {f : X → ℝ} {c l : ℝ} (hl : l ≤ c)
    (hf : ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) R, f (χ y) = c + ‖y‖ ^ 2 / 2) :
    χ '' closedBall 0 ρ = connectedComponentIn (f ⁻¹' Icc l (c + ρ ^ 2 / 2)) (χ 0) := by
  set S := χ '' closedBall 0 ρ
  set O := χ '' ball 0 R
  set F := f ⁻¹' Icc l (c + ρ ^ 2 / 2)
  have hcb : closedBall (0 : EuclideanSpace ℝ (Fin 2)) ρ ⊆ ball 0 R := closedBall_subset_ball hρR
  have hO : IsOpen O := χ.isOpen_image_of_subset_source isOpen_ball hsrc
  have hSO : S ⊆ O := image_mono hcb
  have hSF : S ⊆ F := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : ‖y‖ ≤ ρ := by simpa using hy
    have h0 : 0 ≤ ‖y‖ := norm_nonneg y
    have hsq : ‖y‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ h0 hy' 2
    change f (χ y) ∈ Icc l (c + ρ ^ 2 / 2)
    rw [hf y (hcb hy)]
    constructor <;> nlinarith [sq_nonneg ‖y‖]
  have hFO : F ∩ O ⊆ S := by
    rintro _ ⟨hz, ⟨y, hy, rfl⟩⟩
    have hz' : f (χ y) ≤ c + ρ ^ 2 / 2 := hz.2
    rw [hf y hy] at hz'
    refine ⟨y, ?_, rfl⟩
    rw [mem_closedBall, dist_zero_right]
    exact (pow_le_pow_iff_left₀ (norm_nonneg y) hρ0 two_ne_zero).mp (by linarith)
  have hSc : IsClosed S :=
    ((isCompact_closedBall 0 ρ).image_of_continuousOn
      (χ.continuousOn.mono (hcb.trans hsrc))).isClosed
  have hSp : IsPreconnected S :=
    ((convex_closedBall 0 ρ).isPreconnected).image _ (χ.continuousOn.mono (hcb.trans hsrc))
  have h0S : χ 0 ∈ S := ⟨0, mem_closedBall_self hρ0, rfl⟩
  refine subset_antisymm (hSp.subset_connectedComponentIn h0S hSF) ?_
  have hC := (isPreconnected_iff_subset_of_disjoint.mp
    (isPreconnected_connectedComponentIn (F := F) (x := χ 0))) O Sᶜ hO hSc.isOpen_compl
    (fun z _ => by by_cases hz : z ∈ S; exacts [Or.inl (hSO hz), Or.inr hz]) (by
      ext z
      simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and,
        not_not]
      intro hz hzO
      exact hFO ⟨connectedComponentIn_subset _ _ hz, hzO⟩)
  rcases hC with hC | hC
  · exact fun z hz => hFO ⟨connectedComponentIn_subset _ _ hz, hC hz⟩
  · exact absurd h0S (hC (mem_connectedComponentIn (hSF h0S)))

private theorem exists_quadratic_chart_of_isInteriorPoint {H : Type} [TopologicalSpace H]
    {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2)) H} {M : Type} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p : M}
    (hp : I.IsInteriorPoint p) (hnd : IsNondegenerateCriticalPointAt I f p)
    (hidx : sigNeg (chartHessianAt (fun y => f ((extChartAt I p).symm y))
      (extChartAt I p p)) ≠ 1) :
    ∃ R : ℝ, 0 < R ∧ ∃ χ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I
        (EuclideanSpace ℝ (Fin 2)) M ∞, χ 0 = p ∧ ball 0 R ⊆ χ.source ∧
      ((∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) R, f (χ y) = f p + ‖y‖ ^ 2 / 2) ∨
        (∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) R, f (χ y) = f p - ‖y‖ ^ 2 / 2)) := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞ (by simp) (M := M)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) U :=
    DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  have _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ U :=
    DifferentialGeometry.Manifold.interiorIsManifold I ∞
  let g : U → ℝ := fun y => f y
  have hval : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I ∞ (Subtype.val : U → M) :=
    DifferentialGeometry.Manifold.contMDiff_intrinsicInterior_val I ∞ (by simp)
  have hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ) ∞ g := hf.comp hval
  have hgold : ContMDiff I 𝓘(ℝ, ℝ) ∞ g := hf.comp contMDiff_subtype_val
  let q : U := ⟨p, hp⟩
  have hndU : IsNondegenerateCriticalPointAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) g q :=
    (DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_interiorAtlas I hgold q).mpr
      ((DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_openRestriction I hf q hp).mpr
        hnd)
  have hhess : chartHessianAt (fun y => g ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) q).symm y))
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) q q) =
      chartHessianAt (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p) :=
    DifferentialGeometry.Morse.chartHessianAt_openRestriction I U f q
  have hsum := sigPos_add_sigNeg_eq_finrank _ hndU.2
  rw [hhess, finrank_euclideanSpace_fin] at hsum
  have hU : Nonempty U := ⟨q⟩
  let ι : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I U M ∞ :=
    ((DifferentialGeometry.Manifold.interiorAtlasDiffeomorph I ∞ (M := U)).symm
      ).toPartialDiffeomorph.trans
      (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph I U hU)
  have hιs (z : U) : z ∈ ι.source := ⟨mem_univ _, mem_univ _⟩
  rcases Nat.lt_or_ge (sigNeg (chartHessianAt (fun y => f ((extChartAt I p).symm y))
      (extChartAt I p p))) 1 with h0 | h2
  · have hidx0 : sigNeg (chartHessianAt
        (fun y => g ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) q).symm y))
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) q q)) = 0 := by
      rw [hhess]; omega
    have hmin := (isLocalMin_iff_morse_index_eq_zero hg hndU).mpr hidx0
    have h := exists_quadratic_chart_of_isLocalMin hg hndU hmin
    rw [finrank_euclideanSpace_fin] at h
    obtain ⟨R, hR, Φ, hsrc, hΦ0, hΦ⟩ := h
    refine ⟨R, hR, Φ.trans ι, ?_, ?_, Or.inl fun y hy => ?_⟩
    · change ι (Φ 0) = p
      rw [hΦ0]
      rfl
    · intro y hy
      refine ⟨?_, hιs _⟩
      change y ∈ Φ.source
      rw [hsrc]
      exact hy
    · exact hΦ y (hsrc ▸ hy)
  · have hidx2 : sigNeg (chartHessianAt
        (fun y => g ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) q).symm y))
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) q q)) =
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) := by
      rw [hhess, finrank_euclideanSpace_fin]
      omega
    have hmax := (isLocalMax_iff_morse_index_eq_finrank hg hndU).mpr hidx2
    have h := exists_quadratic_chart_of_isLocalMax hg hndU hmax
    rw [finrank_euclideanSpace_fin] at h
    obtain ⟨R, hR, Φ, hsrc, hΦ0, hΦ⟩ := h
    refine ⟨R, hR, Φ.trans ι, ?_, ?_, Or.inr fun y hy => ?_⟩
    · change ι (Φ 0) = p
      rw [hΦ0]
      rfl
    · intro y hy
      refine ⟨?_, hιs _⟩
      change y ∈ Φ.source
      rw [hsrc]
      exact hy
    · exact hΦ y (hsrc ▸ hy)

end Thin

section Levels

private theorem exists_pos_lt_of_finset {ι : Type*} (s : Finset ι) (g : ι → ℝ)
    (hg : ∀ i ∈ s, 0 < g i) : ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, δ < g i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s ha ih =>
    obtain ⟨δ, hδ, hδs⟩ := ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    have ha' := hg a (Finset.mem_insert_self a s)
    refine ⟨min δ (g a / 2), lt_min hδ (half_pos ha'), fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact (min_le_right _ _).trans_lt (half_lt_self ha')
    · exact (min_le_left _ _).trans_lt (hδs i hi)

private theorem exists_levels (C : Finset ℝ) {ε : ℝ} (hε : 0 < ε)
    (hεC : ∀ c ∈ C, ε < c) (hgap : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → 2 * ε < |c - c'|) :
    ∃ (m : ℕ) (level : Fin (m + 1) → ℝ), StrictMono level ∧ 0 < level 0 ∧
      (∀ c ∈ C, c + ε ≤ level (Fin.last m)) ∧
      (∀ j c, c ∈ C → ε ≤ |level j - c|) ∧
      (∀ c ∈ C, ∃ i : Fin m, level i.castSucc = c - ε ∧ level i.succ = c + ε) ∧
      (∀ c ∈ C, ∀ i : Fin m, c ∈ Ioo (level i.castSucc) (level i.succ) →
        level i.castSucc = c - ε ∧ level i.succ = c + ε) := by
  classical
  obtain ⟨a, ha, haC⟩ := exists_pos_lt_of_finset C (fun c => c - ε)
    (fun c hc => sub_pos.mpr (hεC c hc))
  set S : Finset ℝ := insert a (C.image (· - ε) ∪ C.image (· + ε))
  have haS : a ∈ S := Finset.mem_insert_self _ _
  have hcard : S.card = (S.card - 1) + 1 :=
    (Nat.sub_add_cancel (Finset.card_pos.mpr ⟨a, haS⟩)).symm
  set m := S.card - 1
  let L := S.orderEmbOfFin hcard
  have hLS (j : Fin (m + 1)) : L j ∈ S := Finset.orderEmbOfFin_mem S hcard j
  have hSL (s : ℝ) (hs : s ∈ S) : ∃ j, L j = s := by
    have : s ∈ Set.range L := by rw [Finset.range_orderEmbOfFin]; exact hs
    exact this
  have hmono : StrictMono L := L.strictMono
  have hQ (s : ℝ) (hs : s ∈ S) (c : ℝ) (hc : c ∈ C) : s ≤ c - ε ∨ c + ε ≤ s := by
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact Or.inl (haC c hc).le
    rcases Finset.mem_union.mp hs with hs | hs
    · obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hs
      rcases eq_or_ne c c' with rfl | hne
      · exact Or.inl le_rfl
      · have h := hgap c hc c' hc' hne
        rcases le_or_gt c c' with hle | hlt
        · rw [abs_of_nonpos (by linarith)] at h
          exact Or.inr (by linarith)
        · rw [abs_of_pos (by linarith)] at h
          exact Or.inl (by linarith)
    · obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hs
      rcases eq_or_ne c c' with rfl | hne
      · exact Or.inr le_rfl
      · have h := hgap c hc c' hc' hne
        rcases le_or_gt c c' with hle | hlt
        · rw [abs_of_nonpos (by linarith)] at h
          exact Or.inr (by linarith)
        · rw [abs_of_pos (by linarith)] at h
          exact Or.inl (by linarith)
  have hpos (s : ℝ) (hs : s ∈ S) : 0 < s := by
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact ha
    rcases Finset.mem_union.mp hs with hs | hs
    · obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hs
      exact sub_pos.mpr (hεC c' hc')
    · obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hs
      linarith [hεC c' hc']
  have hminus (c : ℝ) (hc : c ∈ C) : c - ε ∈ S :=
    Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hc))
  have hplus (c : ℝ) (hc : c ∈ C) : c + ε ∈ S :=
    Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hc))
  refine ⟨m, L, hmono, hpos _ (hLS 0), fun c hc => ?_, fun j c hc => ?_, fun c hc => ?_,
    fun c hc i hi => ?_⟩
  · obtain ⟨j, hj⟩ := hSL _ (hplus c hc)
    rw [← hj]
    exact hmono.monotone (Fin.le_last j)
  · rcases hQ _ (hLS j) c hc with h | h
    · rw [abs_of_nonpos (by linarith)]
      linarith
    · rw [abs_of_nonneg (by linarith)]
      linarith
  · obtain ⟨j, hj⟩ := hSL _ (hminus c hc)
    obtain ⟨j', hj'⟩ := hSL _ (hplus c hc)
    have hjj : j < j' := hmono.lt_iff_lt.mp (by rw [hj, hj']; linarith)
    have hjm : (j : ℕ) < m := lt_of_lt_of_le hjj (Fin.le_last j')
    let i : Fin m := ⟨j, hjm⟩
    have hi1 : i.castSucc = j := Fin.ext rfl
    refine ⟨i, by rw [hi1, hj], ?_⟩
    have hle : i.succ ≤ j' := by
      rw [Fin.le_def]
      simp only [Fin.val_succ]
      exact hjj
    have hgt : j < i.succ := by
      rw [Fin.lt_def]
      simp [i]
    have hge : c + ε ≤ L i.succ := by
      rcases hQ _ (hLS i.succ) c hc with h | h
      · have := hmono hgt
        rw [hj] at this
        linarith
      · exact h
    rw [← hj'] at hge ⊢
    exact le_antisymm (hmono.monotone hle) hge
  · obtain ⟨j, hj⟩ := hSL _ (hminus c hc)
    obtain ⟨j', hj'⟩ := hSL _ (hplus c hc)
    have h1 : L i.castSucc ≤ c - ε := by
      rcases hQ _ (hLS i.castSucc) c hc with h | h
      · exact h
      · linarith [hi.1]
    have h2 : c + ε ≤ L i.succ := by
      rcases hQ _ (hLS i.succ) c hc with h | h
      · linarith [hi.2]
      · exact h
    constructor
    · rw [← hj] at h1 ⊢
      rcases (hmono.le_iff_le.mp h1).lt_or_eq with hlt | heq
      · have hsucc : i.succ ≤ j := by
          rw [Fin.le_def]
          rw [Fin.lt_def] at hlt
          simp only [Fin.val_succ, Fin.val_castSucc] at hlt ⊢
          omega
        have := hmono.monotone hsucc
        rw [hj] at this
        linarith [hi.2]
      · rw [heq]
    · rw [← hj'] at h2 ⊢
      rcases (hmono.le_iff_le.mp h2).lt_or_eq with hlt | heq
      · have hcast : j' ≤ i.castSucc := by
          rw [Fin.le_def]
          rw [Fin.lt_def] at hlt
          simp only [Fin.val_succ, Fin.val_castSucc] at hlt ⊢
          omega
        have := hmono.monotone hcast
        rw [hj'] at this
        linarith [hi.1]
      · rw [heq]

end Levels

section Assembly

private theorem exists_baseMorseData_of_morse {B : CompactSurface.{0}} {r : B.Carrier → ℝ}
    (hr : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ r) (hnonneg : ∀ x, 0 ≤ r x)
    (hzero : ∀ x, r x = 0 ↔ (SurfaceModel.model B.kind).IsBoundaryPoint x)
    (hcrit : ∀ x, IsCriticalPointAt (SurfaceModel.model B.kind) r x →
      (SurfaceModel.model B.kind).IsInteriorPoint x ∧
        IsNondegenerateCriticalPointAt (SurfaceModel.model B.kind) r x)
    (hfin : {x | IsCriticalPointAt (SurfaceModel.model B.kind) r x}.Finite)
    (hinj : InjOn r {x | IsCriticalPointAt (SurfaceModel.model B.kind) r x}) :
    Nonempty (BaseMorseData B) := by
  classical
  set I := SurfaceModel.model B.kind
  set Cs := hfin.toFinset
  set Cv := Cs.image r
  have hmemCs (x : B.Carrier) : x ∈ Cs ↔ IsCriticalPointAt I r x := hfin.mem_toFinset
  have hint_pos (x : B.Carrier) (hx : I.IsInteriorPoint x) : 0 < r x :=
    lt_of_le_of_ne (hnonneg x) fun h =>
      (I.isInteriorPoint_iff_not_isBoundaryPoint x).mp hx ((hzero x).mp h.symm)
  have hpos_int (x : B.Carrier) (hx : 0 < r x) : I.IsInteriorPoint x :=
    (I.isInteriorPoint_iff_not_isBoundaryPoint x).mpr fun hb => hx.ne' ((hzero x).mpr hb)
  have hCvpos : ∀ c ∈ Cv, 0 < c := by
    intro c hc
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
    exact hint_pos p (hcrit p ((hmemCs p).mp hp)).1
  have hext : ∀ p ∈ Cs, ∃ R : ℝ, 0 < R ∧
      (sigNeg (chartHessianAt (fun y => r ((extChartAt I p).symm y)) (extChartAt I p p)) ≠ 1 →
        ∃ χ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I
          (EuclideanSpace ℝ (Fin 2)) B.Carrier ∞, χ 0 = p ∧ ball 0 R ⊆ χ.source ∧
          ((∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) R, r (χ y) = r p + ‖y‖ ^ 2 / 2) ∨
            (∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) R, r (χ y) = r p - ‖y‖ ^ 2 / 2))) := by
    intro p hp
    have hc := hcrit p ((hmemCs p).mp hp)
    by_cases hidx : sigNeg (chartHessianAt (fun y => r ((extChartAt I p).symm y))
      (extChartAt I p p)) = 1
    · exact ⟨1, one_pos, fun h => absurd hidx h⟩
    · obtain ⟨R, hR, χ, h⟩ := exists_quadratic_chart_of_isInteriorPoint hr hc.1 hc.2 hidx
      exact ⟨R, hR, fun _ => ⟨χ, h⟩⟩
  choose! R hRpos hRchart using hext
  obtain ⟨δ₁, hδ₁, hδ₁C⟩ := exists_pos_lt_of_finset Cv id hCvpos
  obtain ⟨δ₂, hδ₂, hδ₂C⟩ := exists_pos_lt_of_finset ((Cv ×ˢ Cv).filter fun q => q.1 ≠ q.2)
    (fun q => |q.1 - q.2| / 2) (by
      intro q hq
      have hne := (Finset.mem_filter.mp hq).2
      exact half_pos (abs_pos.mpr (sub_ne_zero.mpr hne)))
  obtain ⟨δ₃, hδ₃, hδ₃C⟩ := exists_pos_lt_of_finset Cs (fun p => R p ^ 2 / 2)
    (fun p hp => half_pos (pow_pos (hRpos p hp) 2))
  set ε := min δ₁ (min δ₂ δ₃)
  have hε : 0 < ε := lt_min hδ₁ (lt_min hδ₂ hδ₃)
  have hε₁ : ε ≤ δ₁ := min_le_left _ _
  have hε₂ : ε ≤ δ₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hε₃ : ε ≤ δ₃ := (min_le_right _ _).trans (min_le_right _ _)
  have hεC : ∀ c ∈ Cv, ε < c := fun c hc => hε₁.trans_lt (hδ₁C c hc)
  have hgap : ∀ c ∈ Cv, ∀ c' ∈ Cv, c ≠ c' → 2 * ε < |c - c'| := by
    intro c hc c' hc' hne
    have h := hδ₂C (c, c') (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hc, hc'⟩, hne⟩)
    change δ₂ < |c - c'| / 2 at h
    linarith
  obtain ⟨m, level, hmono, hlevel0, hlast, hdist, hslab1, hslab2⟩ :=
    exists_levels Cv hε hεC hgap
  set κ := min ε (level 0) / 4
  have hκ : 0 < κ := by positivity
  have hκε : 2 * κ < ε := by
    have : min ε (level 0) ≤ ε := min_le_left _ _
    change 2 * (min ε (level 0) / 4) < ε
    linarith
  have hκl : 2 * κ < level 0 := by
    have : min ε (level 0) ≤ level 0 := min_le_right _ _
    change 2 * (min ε (level 0) / 4) < level 0
    linarith
  set K : Set B.Carrier := ⋃ i : Fin (m + 1), r ⁻¹' Icc (level i - 2 * κ) (level i + 2 * κ)
  have hK : IsCompact K :=
    (isClosed_iUnion_of_finite fun i => isClosed_Icc.preimage hr.continuous).isCompact
  have hKint : ∀ x ∈ K, I.IsInteriorPoint x := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    have h0 : level 0 ≤ level i := hmono.monotone (Fin.zero_le i)
    exact hpos_int x (by linarith [hi.1])
  have hKreg : ∀ x ∈ K, mfderiv I 𝓘(ℝ, ℝ) r x ≠ 0 := by
    intro x hx hcx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    have hxv : r x ∈ Cv := Finset.mem_image_of_mem r ((hmemCs x).mpr hcx)
    have h := hdist i (r x) hxv
    have h1 : |level i - r x| ≤ 2 * κ := abs_le.mpr ⟨by linarith [hi.2], by linarith [hi.1]⟩
    linarith
  obtain ⟨V, hV, hVK⟩ := exists_unitField_of_isCompact hr hK hKint hKreg
  obtain ⟨y₀, hy₀⟩ := (DifferentialGeometry.Topology.Manifold.dense_manifold_interior
    (I := I) (M := B.Carrier)).nonempty
  obtain ⟨p₀, -, hp₀⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hr.continuous.continuousOn
  have hp₀pos : 0 < r p₀ := (hint_pos y₀ hy₀).trans_le (hp₀ (mem_univ y₀))
  have hp₀crit : IsCriticalPointAt I r p₀ := by
    by_contra h
    exact hp₀pos.ne' ((hzero p₀).mpr
      (DifferentialGeometry.Topology.Manifold.isBoundaryPoint_of_isLocalMax_of_mfderiv_ne_zero
        (hp₀.isLocalMax Filter.univ_mem) h))
  have hp₀v : r p₀ ∈ Cv := Finset.mem_image_of_mem r ((hmemCs p₀).mpr hp₀crit)
  refine ⟨{
    f := r
    smooth := hr
    nonneg := hnonneg
    eq_zero_iff := hzero
    crit := Cs
    mem_crit := hmemCs
    nondegenerate := fun p hp => (hcrit p ((hmemCs p).mp hp)).2
    m := m
    level := level
    level_strictMono := hmono
    κ := κ
    κ_pos := hκ
    two_κ_lt_level := hκl
    lt_level_last := fun x => (hp₀ (mem_univ x)).trans_lt
      ((lt_add_of_pos_right _ hε).trans_le (hlast _ hp₀v))
    slab := ?_
    thin := ?_
    field := V
    field_smooth := hV
    field_unit := fun i x hx => hVK x (mem_iUnion.mpr ⟨i,
      ⟨by linarith [(abs_lt.mp hx).1], by linarith [(abs_lt.mp hx).2]⟩⟩) }⟩
  · intro p hp
    have hpv : r p ∈ Cv := Finset.mem_image_of_mem r hp
    obtain ⟨i, hi1, hi2⟩ := hslab1 _ hpv
    refine ⟨i, by rw [hi1, hi2]; constructor <;> linarith, fun q hq hqI => ?_⟩
    rw [hi1, hi2] at hqI
    have hqv : r q ∈ Cv := Finset.mem_image_of_mem r hq
    by_contra hne
    have hrne : r q ≠ r p := fun h => hne (hinj ((hmemCs q).mp hq) ((hmemCs p).mp hp) h)
    have h := hgap _ hqv _ hpv hrne
    have h' : |r q - r p| ≤ ε := abs_le.mpr ⟨by linarith [hqI.1], by linarith [hqI.2]⟩
    linarith
  · intro p hp hidx i hi
    have hpv : r p ∈ Cv := Finset.mem_image_of_mem r hp
    obtain ⟨hi1, hi2⟩ := hslab2 _ hpv i hi
    obtain ⟨χ, hχ0, hsrc, hform⟩ := hRchart p hp hidx
    set ρ := Real.sqrt (2 * ε)
    have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
    have hρsq : ρ ^ 2 / 2 = ε := by
      rw [Real.sq_sqrt (by linarith)]
      ring
    have hρR : ρ < R p := by
      have h3 : ε < R p ^ 2 / 2 := hε₃.trans_lt (hδ₃C p hp)
      rw [show R p = Real.sqrt (R p ^ 2) from (Real.sqrt_sq (hRpos p hp).le).symm]
      exact Real.sqrt_lt_sqrt (by linarith) (by linarith)
    refine ⟨ρ, χ, hχ0, (closedBall_subset_ball hρR).trans hsrc, ?_⟩
    rw [hi1, hi2]
    rcases hform with hmin | hmax
    · have h := image_closedBall_eq_connectedComponentIn χ.toOpenPartialHomeomorph hρ0 hρR hsrc
        (f := r) (c := r p) (l := r p - ε) (by linarith) hmin
      rw [hρsq, show χ.toOpenPartialHomeomorph 0 = p from hχ0] at h
      exact h
    · have h := image_closedBall_eq_connectedComponentIn χ.toOpenPartialHomeomorph hρ0 hρR hsrc
        (f := fun x => -r x) (c := -r p) (l := -(r p + ε)) (by linarith)
        (fun y hy => by
          change -r (χ y) = _
          rw [hmax y hy]
          ring)
      rw [hρsq] at h
      have hset : (fun x => -r x) ⁻¹' Icc (-(r p + ε)) (-r p + ε) =
          r ⁻¹' Icc (r p - ε) (r p + ε) := by
        ext x
        simp only [mem_preimage, mem_Icc]
        constructor <;> intro hx <;> constructor <;> linarith [hx.1, hx.2]
      rw [hset, show χ.toOpenPartialHomeomorph 0 = p from hχ0] at h
      exact h

private theorem exists_excellent (B : CompactSurface.{0}) :
    ∃ r : B.Carrier → ℝ, ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ r ∧
      (∀ x, 0 ≤ r x) ∧ (∀ x, r x = 0 ↔ (SurfaceModel.model B.kind).IsBoundaryPoint x) ∧
      (∀ x, IsCriticalPointAt (SurfaceModel.model B.kind) r x →
        (SurfaceModel.model B.kind).IsInteriorPoint x ∧
          IsNondegenerateCriticalPointAt (SurfaceModel.model B.kind) r x) ∧
      {x | IsCriticalPointAt (SurfaceModel.model B.kind) r x}.Finite ∧
      InjOn r {x | IsCriticalPointAt (SurfaceModel.model B.kind) r x} := by
  obtain ⟨⟨k, C, top, charts, smooth, t2, compact, sc⟩, conn⟩ := B
  cases k with
  | withBoundary =>
    obtain ⟨r, -, hr, hnn, hzero, -, -, hcrit, hfin, hinj, -⟩ :=
      DifferentialGeometry.Morse.exists_excellent_morse_boundary_definingFunction
        (n := 2) (M := C)
    exact ⟨r, hr, hnn, hzero, hcrit, hfin, hinj⟩
  | closed =>
    change ∃ r : C → ℝ, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ r ∧ (∀ x, 0 ≤ r x) ∧
      (∀ x, r x = 0 ↔ (𝓡 2).IsBoundaryPoint x) ∧
      (∀ x, IsCriticalPointAt (𝓡 2) r x →
        (𝓡 2).IsInteriorPoint x ∧ IsNondegenerateCriticalPointAt (𝓡 2) r x) ∧
      {x | IsCriticalPointAt (𝓡 2) r x}.Finite ∧ InjOn r {x | IsCriticalPointAt (𝓡 2) r x}
    obtain ⟨f, hf, hnd⟩ := exists_morse_function (I := 𝓡 2) (M := C)
    have hint (x : C) : (𝓡 2).IsInteriorPoint x := BoundarylessManifold.isInteriorPoint
    obtain ⟨p, -, hp⟩ := isCompact_univ.exists_isMinOn univ_nonempty hf.continuous.continuousOn
    let f' : C → ℝ := fun y => f y + (1 - f p)
    have hf' : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f' := hf.add contMDiff_const
    have hcrit' (x : C) : IsCriticalPointAt (𝓡 2) f' x ↔ IsCriticalPointAt (𝓡 2) f x :=
      isCriticalPointAt_add_const_iff f _ x
    have hnd' (x : C) (hx : IsCriticalPointAt (𝓡 2) f' x) :
        IsNondegenerateCriticalPointAt (𝓡 2) f' x :=
      (isNondegenerateCriticalPointAt_add_const_iff f _ x).mpr (hnd x ((hcrit' x).mp hx))
    have hfin' : {x | IsCriticalPointAt (𝓡 2) f' x}.Finite :=
      DifferentialGeometry.Morse.finite_criticalPoints_of_isCompact hf' isCompact_univ
        (fun x _ => hint x) (fun _ _ => mem_univ _) hnd'
    have hpos' (x : C) (_ : x ∈ univ) : 0 < f' x := by
      have : f p ≤ f x := hp (mem_univ x)
      change 0 < f x + (1 - f p)
      linarith
    obtain ⟨g, hg, -, hgpos, hgcrit, hginj, hgnd, -⟩ :=
      DifferentialGeometry.Morse.exists_positive_relative_excellent_morse hf' hfin' hnd'
        isOpen_univ (subset_univ _) (fun x _ => hint x) (subset_univ _) hpos'
    refine ⟨g, hg, fun x => (hgpos x (mem_univ x)).le, fun x => ?_, fun x hx => ⟨hint x, hgnd x hx⟩,
      hgcrit ▸ hfin', hginj⟩
    exact iff_of_false (hgpos x (mem_univ x)).ne'
      (((𝓡 2).isInteriorPoint_iff_not_isBoundaryPoint x).mp (hint x))


theorem exists_baseMorseData_of_small (B : CompactSurface.{0}) : Nonempty (BaseMorseData B) := by
  obtain ⟨r, hr, hnn, hzero, hcrit, hfin, hinj⟩ := exists_excellent B
  exact exists_baseMorseData_of_morse hr hnn hzero hcrit hfin hinj

end Assembly

section Shrink

private theorem isCriticalPointAt_comp_diffeomorph_iff' {E H M E' H' N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
    [TopologicalSpace N] [ChartedSpace H' N]
    (c : Diffeomorph I J M N ∞) {f : N → ℝ} {x : M} :
    IsCriticalPointAt I (f ∘ c) x ↔ IsCriticalPointAt J f (c x) := by
  by_cases hf : MDifferentiableAt J 𝓘(ℝ, ℝ) f (c x)
  · have hsurj : Function.Surjective (mfderiv I J c x) :=
      (c.mfderivToContinuousLinearEquiv (by simp) x).surjective
    rw [IsCriticalPointAt, IsCriticalPointAt,
      mfderiv_comp x hf (c.mdifferentiable (by simp) x)]
    constructor
    · intro h
      apply ContinuousLinearMap.ext
      intro v
      obtain ⟨w, rfl⟩ := hsurj v
      exact congrArg (fun A => A w) h
    · intro h
      rw [h, ContinuousLinearMap.zero_comp]
  · have hfc : ¬MDifferentiableAt I 𝓘(ℝ, ℝ) (f ∘ c) x := by
      intro h
      apply hf
      have h' := h.comp_of_eq (c x) (c.symm.mdifferentiable (by simp) (c x))
        (c.symm_apply_apply x)
      simpa only [Function.comp_def, c.apply_symm_apply] using h'
    simp only [IsCriticalPointAt, mfderiv_zero_of_not_mdifferentiableAt hf,
      mfderiv_zero_of_not_mdifferentiableAt hfc]

private def shrinkSurface (B : CompactSurface.{u}) : CompactSurface.{0} :=
  letI : Small.{0} B.Carrier :=
    ChartedSpace.small_of_compactSpace (SurfaceModel.Space B.kind) B.Carrier
  let h : Shrink.{0} B.Carrier ≃ₜ B.Carrier := (Shrink.homeomorph B.Carrier).symm
  letI := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := SurfaceModel.Space B.kind) h
  { kind := B.kind
    Carrier := Shrink.{0} B.Carrier
    charts := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace h
    smooth := DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback
      (I := SurfaceModel.model B.kind) h
    hausdorff := h.isEmbedding.t2Space
    compact := h.symm.compactSpace
    secondCountable := h.isInducing.secondCountableTopology
    connected := h.symm.surjective.connectedSpace h.symm.continuous }

private instance instChartedSpaceShrink (B : CompactSurface.{u}) :
    ChartedSpace (SurfaceModel.Space B.kind) (shrinkSurface B).Carrier :=
  (shrinkSurface B).charts

private instance instIsManifoldShrink (B : CompactSurface.{u}) :
    IsManifold (SurfaceModel.model B.kind) ∞ (shrinkSurface B).Carrier :=
  (shrinkSurface B).smooth

private def shrinkHomeomorph (B : CompactSurface.{u}) :
    (shrinkSurface B).Carrier ≃ₜ B.Carrier :=
  letI : Small.{0} B.Carrier :=
    ChartedSpace.small_of_compactSpace (SurfaceModel.Space B.kind) B.Carrier
  (Shrink.homeomorph B.Carrier).symm

private def shrinkDiffeomorph (B : CompactSurface.{u}) :
    Diffeomorph (SurfaceModel.model B.kind) (SurfaceModel.model B.kind)
      (shrinkSurface B).Carrier B.Carrier ∞ :=
  DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph (shrinkHomeomorph B)

theorem exists_baseMorseData (B : CompactSurface.{u}) : Nonempty (BaseMorseData B) := by
  classical
  obtain ⟨D₀⟩ := exists_baseMorseData_of_small (shrinkSurface B)
  let I := SurfaceModel.model B.kind
  let h := shrinkHomeomorph B
  let Φ := shrinkDiffeomorph B
  let f : B.Carrier → ℝ := fun x => D₀.f (h.symm x)
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := D₀.smooth.comp Φ.symm.contMDiff
  have hfΦ : f ∘ Φ = D₀.f := funext fun y => congrArg D₀.f (h.symm_apply_apply y)
  have hcrit (y : (shrinkSurface B).Carrier) :
      IsCriticalPointAt I f (h y) ↔ IsCriticalPointAt I D₀.f y := by
    rw [← hfΦ]
    exact (isCriticalPointAt_comp_diffeomorph_iff' Φ).symm
  have hcrit' (x : B.Carrier) :
      IsCriticalPointAt I f x ↔ IsCriticalPointAt I D₀.f (h.symm x) := by
    rw [← hcrit, h.apply_symm_apply]
  have hbdry (x : B.Carrier) : I.IsBoundaryPoint x ↔ I.IsBoundaryPoint (h.symm x) :=
    (Φ.symm.isLocalDiffeomorph x).isBoundaryPoint_iff (by simp)
  have hhess (y : (shrinkSurface B).Carrier) :
      chartHessianAt (fun z => f ((extChartAt I (h y)).symm z)) (extChartAt I (h y) (h y)) =
        chartHessianAt (fun z => D₀.f ((extChartAt I y).symm z)) (extChartAt I y y) := rfl
  let crit : Finset B.Carrier := D₀.crit.map h.toEquiv.toEmbedding
  have hmem (x : B.Carrier) : x ∈ crit ↔ h.symm x ∈ D₀.crit := Finset.mem_map_equiv
  have hmem' (y : (shrinkSurface B).Carrier) : h y ∈ crit ↔ y ∈ D₀.crit := by
    rw [hmem, h.symm_apply_apply]
  have hfh (y : (shrinkSurface B).Carrier) : f (h y) = D₀.f y :=
    congrArg D₀.f (h.symm_apply_apply y)
  let K : Set B.Carrier :=
    ⋃ i : Fin (D₀.m + 1), f ⁻¹' Icc (D₀.level i - D₀.κ) (D₀.level i + D₀.κ)
  have hK : IsCompact K :=
    (isClosed_iUnion_of_finite fun i => isClosed_Icc.preimage hf.continuous).isCompact
  have hlev0 : 2 * D₀.κ < D₀.level 0 := D₀.two_κ_lt_level
  have hKint : ∀ x ∈ K, I.IsInteriorPoint x := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    have h0 : D₀.level 0 ≤ D₀.level i := D₀.level_strictMono.monotone (Fin.zero_le i)
    have hpos : 0 < f x := by linarith [hi.1, D₀.κ_pos]
    refine (I.isInteriorPoint_iff_not_isBoundaryPoint x).mpr fun hb => hpos.ne' ?_
    exact (D₀.eq_zero_iff (h.symm x)).mpr ((hbdry x).mp hb)
  have hKreg : ∀ x ∈ K, mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0 := by
    intro x hx hcx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    have hc : IsCriticalPointAt I D₀.f (h.symm x) := (hcrit' x).mp hcx
    have hu := D₀.field_unit i (h.symm x) (abs_lt.mpr
      ⟨by linarith [hi.1, D₀.κ_pos], by linarith [hi.2, D₀.κ_pos]⟩)
    have hz : mfderiv (SurfaceModel.model (shrinkSurface B).kind) 𝓘(ℝ, ℝ) D₀.f (h.symm x) = 0 :=
      hc
    rw [hz] at hu
    have h01 : (0 : ℝ) = 1 := hu
    norm_num at h01
  obtain ⟨V, hV, hVK⟩ := exists_unitField_of_isCompact (E := EuclideanSpace ℝ (Fin 2))
    (H := SurfaceModel.Space B.kind) (I := SurfaceModel.model B.kind) (M := B.Carrier)
    hf hK hKint hKreg
  refine ⟨{
    f := f
    smooth := hf
    nonneg := fun x => D₀.nonneg _
    eq_zero_iff := fun x => (D₀.eq_zero_iff (h.symm x)).trans (hbdry x).symm
    crit := crit
    mem_crit := fun x => (hmem x).trans ((D₀.mem_crit _).trans (hcrit' x).symm)
    nondegenerate := ?_
    m := D₀.m
    level := D₀.level
    level_strictMono := D₀.level_strictMono
    κ := D₀.κ / 2
    κ_pos := half_pos D₀.κ_pos
    two_κ_lt_level := by linarith [D₀.κ_pos]
    lt_level_last := fun x => D₀.lt_level_last _
    slab := ?_
    thin := ?_
    field := V
    field_smooth := hV
    field_unit := fun i x hx => hVK x (mem_iUnion.mpr ⟨i,
      ⟨by linarith [(abs_lt.mp hx).1], by linarith [(abs_lt.mp hx).2]⟩⟩) }⟩
  · intro p hp
    obtain ⟨y, rfl⟩ := h.surjective p
    have hy : y ∈ D₀.crit := (hmem' y).mp hp
    have hnd := D₀.nondegenerate y hy
    exact ⟨(hcrit y).mpr hnd.1, hnd.2⟩
  · intro p hp
    obtain ⟨y, rfl⟩ := h.surjective p
    have hy : y ∈ D₀.crit := (hmem' y).mp hp
    obtain ⟨i, hi, huniq⟩ := D₀.slab y hy
    refine ⟨i, by rw [hfh]; exact hi, fun q hq hqI => ?_⟩
    obtain ⟨z, rfl⟩ := h.surjective q
    rw [hfh] at hqI
    rw [huniq z ((hmem' z).mp hq) hqI]
  · intro p hp hidx i hi
    obtain ⟨y, rfl⟩ := h.surjective p
    have hy : y ∈ D₀.crit := (hmem' y).mp hp
    rw [hhess] at hidx
    rw [hfh] at hi
    obtain ⟨R, χ₀, hχ0, hsrc, himg⟩ := D₀.thin y hy hidx i hi
    refine ⟨R, χ₀.trans Φ.toPartialDiffeomorph, ?_, fun z hz => ⟨hsrc hz, mem_univ _⟩, ?_⟩
    · change h (χ₀ 0) = h y
      rw [hχ0]
    · have himg' : (χ₀.trans Φ.toPartialDiffeomorph) '' closedBall 0 R =
          h '' (χ₀ '' closedBall 0 R) := by
        rw [image_image]
        rfl
      rw [himg', himg, h.image_connectedComponentIn]
      · congr 1
        ext x
        simp only [mem_image, mem_preimage]
        constructor
        · rintro ⟨z, hz, rfl⟩
          rw [hfh]
          exact hz
        · intro hx
          exact ⟨h.symm x, hx, h.apply_symm_apply x⟩
      · change D₀.f y ∈ Icc _ _
        exact ⟨hi.1.le, hi.2.le⟩

end Shrink

namespace BaseMorseData

variable {B : CompactSurface.{u}}

theorem exists_level_zero_eq (D : BaseMorseData B) {a : ℝ} (ha : 0 < a) (haD : a < D.level 0) :
    ∃ D' : BaseMorseData B, D'.f = D.f ∧ D'.crit = D.crit ∧ D'.level 0 = a ∧
      ∀ i, ∃ j, D'.level j = D.level i := by
  classical
  let I := SurfaceModel.model B.kind
  let level' : Fin (D.m + 1 + 1) → ℝ := Fin.cons a D.level
  have hmono : StrictMono level' := Fin.strictMono_cons.mpr
    ⟨fun j => haD.trans_le (D.level_strictMono.monotone (Fin.zero_le j)), D.level_strictMono⟩
  let κ' : ℝ := min (D.κ / 2) (min (a / 4) ((D.level 0 - a) / 4))
  have hκ' : 0 < κ' := lt_min (half_pos D.κ_pos) (lt_min (by linarith) (by linarith))
  have hκ'1 : κ' ≤ D.κ / 2 := min_le_left _ _
  have hκ'2 : κ' ≤ a / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hκ'3 : κ' ≤ (D.level 0 - a) / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hlev0 := D.two_κ_lt_level
  let K : Set B.Carrier := ⋃ i, D.f ⁻¹' Icc (level' i - 2 * κ') (level' i + 2 * κ')
  have hK : IsCompact K :=
    (isClosed_iUnion_of_finite fun i => isClosed_Icc.preimage D.smooth.continuous).isCompact
  have hcases (i : Fin (D.m + 1 + 1)) : level' i = a ∨ ∃ j, level' i = D.level j := by
    refine Fin.cases (Or.inl rfl) (fun j => Or.inr ⟨j, rfl⟩) i
  have hKint : ∀ x ∈ K, I.IsInteriorPoint x := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    refine D.isInteriorPoint_of_pos ?_
    rcases hcases i with h | ⟨j, h⟩
    · rw [h] at hi
      linarith [hi.1]
    · rw [h] at hi
      have h0 : D.level 0 ≤ D.level j := D.level_strictMono.monotone (Fin.zero_le j)
      linarith [hi.1, D.κ_pos]
  have hKreg : ∀ x ∈ K, mfderiv I 𝓘(ℝ, ℝ) D.f x ≠ 0 := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rcases hcases i with h | ⟨j, h⟩
    · rw [h] at hi
      exact D.mfderiv_ne_zero_of_le (by linarith [hi.2])
    · rw [h] at hi
      intro hz
      have hu := D.field_unit j x (abs_lt.mpr ⟨by linarith [hi.1], by linarith [hi.2]⟩)
      rw [hz] at hu
      have h01 : (0 : ℝ) = 1 := hu
      norm_num at h01
  obtain ⟨V, hV, hVK⟩ := exists_unitField_of_isCompact (E := EuclideanSpace ℝ (Fin 2))
    (H := SurfaceModel.Space B.kind) (I := SurfaceModel.model B.kind) (M := B.Carrier)
    D.smooth hK hKint hKreg
  refine ⟨{
    f := D.f
    smooth := D.smooth
    nonneg := D.nonneg
    eq_zero_iff := D.eq_zero_iff
    crit := D.crit
    mem_crit := D.mem_crit
    nondegenerate := D.nondegenerate
    m := D.m + 1
    level := level'
    level_strictMono := hmono
    κ := κ'
    κ_pos := hκ'
    two_κ_lt_level := by
      change 2 * κ' < a
      linarith
    lt_level_last := fun x => by
      rw [← Fin.succ_last]
      exact D.lt_level_last x
    slab := ?_
    thin := ?_
    field := V
    field_smooth := hV
    field_unit := fun i x hx => hVK x (mem_iUnion.mpr ⟨i,
      ⟨by linarith [(abs_lt.mp hx).1], by linarith [(abs_lt.mp hx).2]⟩⟩) }, rfl, rfl,
    ?_, fun i => ⟨i.succ, ?_⟩⟩
  · intro p hp
    obtain ⟨i, hi, huniq⟩ := D.slab p hp
    refine ⟨i.succ, ?_, ?_⟩
    · rw [← Fin.succ_castSucc]
      exact hi
    · intro q hq hqI
      change D.f q ∈ Icc (level' i.succ.castSucc) (level' i.succ.succ) at hqI
      rw [← Fin.succ_castSucc] at hqI
      exact huniq q hq hqI
  · intro p hp hidx i hi
    change D.f p ∈ Ioo (level' i.castSucc) (level' i.succ) at hi
    induction i using Fin.cases with
    | zero =>
      exfalso
      have h1 : level' (Fin.succ 0) = D.level 0 := rfl
      have h2 := D.level_zero_lt_of_mem_crit hp
      rw [h1] at hi
      exact absurd hi.2 (not_lt.mpr h2.le)
    | succ j =>
      rw [← Fin.succ_castSucc] at hi ⊢
      exact D.thin p hp hidx j hi
  · exact Fin.cons_zero (α := fun _ => ℝ) a D.level
  · exact Fin.cons_succ (α := fun _ => ℝ) a D.level i

end BaseMorseData

end GC.Seifert
