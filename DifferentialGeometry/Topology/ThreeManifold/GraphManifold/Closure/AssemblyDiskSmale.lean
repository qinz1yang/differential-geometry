import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateParts
import DifferentialGeometry.Topology.Manifold.ChartSupportedIsotopy
import DifferentialGeometry.Topology.Manifold.ClosedBall
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Chapter-14 assembly, SM-D: the disk case of Smale / Munkres

The corrected frozen statement V2 (`build-logs/scratch/ASM-FIX/AssemblyInterfacesV2.lean:819`,
review item 1, disposition D1) of `π₀ Diff(D² rel ∂) = 0`: a diffeomorphism of the closed disk that
is the identity on an open neighbourhood `N` of the rim is smoothly isotopic to the identity through
diffeomorphisms fixing some open `N' ⊆ N` containing the rim, with the time parameter flattened near
`0` and `1`.

Route (sheet `build-logs/resume/sheet-ASM-D2S1.md`): the disk case is already in the tree in planar
form. `Nᶜ` is a compact subset of the open unit ball; the open ball is carried onto `ℂ` by the smooth
chart `closedDiskPlanarChart` (Mathlib's `univUnitBall` followed by the isometry `ℝ² ≃ ℂ`), and
`exists_isotopy_of_support_in_planar_chart` (`Topology/Manifold/ChartSupportedIsotopy.lean`, built on
`exists_relative_square_isotopy`) returns an isotopy every stage of which fixes the complement of a
compact `C` inside the open ball. Then `N' := N ∩ Cᶜ`, and the time is flattened by
`isotopyFlatten` (`smoothTransition (3 t − 1)`, as in `SphereMappingTorusSmooth.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

local instance diskCharts_ASMD2S1 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmooth_ASMD2S1 : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

attribute [local instance] DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc
  DifferentialGeometry.Topology.Handle.closedCellIsManifold

/-! ## Time flattening -/

/-- Reparametrize a time-dependent family by `smoothTransition (3 t − 1)`: it equals the time-`0`
member for `t ≤ 1/3` and the time-`1` member for `t ≥ 2/3`. -/
def isotopyFlatten {α : Type*} (J : ℝ → α) (t : ℝ) : α :=
  J (Real.smoothTransition (3 * t - 1))

theorem isotopyFlatten_of_le {α : Type*} (J : ℝ → α) {t : ℝ} (ht : t ≤ 1 / 3) :
    isotopyFlatten J t = J 0 := by
  unfold isotopyFlatten
  rw [Real.smoothTransition.zero_of_nonpos (by linarith)]

theorem isotopyFlatten_of_ge {α : Type*} (J : ℝ → α) {t : ℝ} (ht : 2 / 3 ≤ t) :
    isotopyFlatten J t = J 1 := by
  unfold isotopyFlatten
  rw [Real.smoothTransition.one_of_one_le (by linarith)]

theorem isotopyFlatten_zero {α : Type*} (J : ℝ → α) : isotopyFlatten J 0 = J 0 :=
  isotopyFlatten_of_le J (by norm_num)

theorem isotopyFlatten_one {α : Type*} (J : ℝ → α) : isotopyFlatten J 1 = J 1 :=
  isotopyFlatten_of_ge J (by norm_num)

/-- Flattening keeps joint smoothness (state-first convention `(x, t)`). -/
theorem contMDiff_isotopyFlatten {E H X F G Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G] {I' : ModelWithCorners ℝ F G}
    [TopologicalSpace Y] [ChartedSpace G Y] {G₀ : X × ℝ → Y}
    (hG : ContMDiff (I.prod 𝓘(ℝ, ℝ)) I' ∞ G₀) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) I' ∞
      (fun p : X × ℝ => G₀ (p.1, Real.smoothTransition (3 * p.2 - 1))) := by
  have hτ : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : X × ℝ => Real.smoothTransition (3 * p.2 - 1)) :=
    (Real.smoothTransition.contDiff (n := ⊤)).contMDiff.comp
      ((contMDiff_const.mul contMDiff_snd).sub contMDiff_const)
  exact hG.comp (contMDiff_fst.prodMk hτ)

/-! ## The rim and the open ball -/

theorem mem_diskRim_iff {x : ClosedCell 2} : x ∈ diskRim ↔ ‖x.val‖ = 1 := by
  have h := congrArg (x ∈ ·) (DifferentialGeometry.Topology.Manifold.closedCell_boundary_eq_sphere 1)
  exact Iff.of_eq h

theorem norm_lt_one_of_notMem_diskRim {x : ClosedCell 2} (hx : x ∉ diskRim) : ‖x.val‖ < 1 :=
  lt_of_le_of_ne x.property fun h => hx (mem_diskRim_iff.mpr h)

theorem notMem_diskRim_of_norm_lt_one {x : ClosedCell 2} (hx : ‖x.val‖ < 1) : x ∉ diskRim :=
  fun h => (ne_of_lt hx) (mem_diskRim_iff.mp h)

/-! ## The planar chart of the open disk -/

private theorem norm_univUnitBall_lt_one (w : EuclideanSpace ℝ (Fin 2)) :
    ‖OpenPartialHomeomorph.univUnitBall w‖ < 1 :=
  mem_ball_zero_iff.mp (OpenPartialHomeomorph.univUnitBall.map_source (mem_univ w))

/-- The smooth chart of the closed disk carrying the open unit ball onto `ℂ`. -/
def closedDiskPlanarChart : OpenPartialHomeomorph (ClosedCell 2) ℂ where
  toFun x := Complex.orthonormalBasisOneI.repr.symm (OpenPartialHomeomorph.univUnitBall.symm x.val)
  invFun z := ⟨OpenPartialHomeomorph.univUnitBall (Complex.orthonormalBasisOneI.repr z),
    (norm_univUnitBall_lt_one _).le⟩
  source := {x | ‖x.val‖ < 1}
  target := univ
  map_source' _ _ := mem_univ _
  map_target' z _ := norm_univUnitBall_lt_one (Complex.orthonormalBasisOneI.repr z)
  left_inv' x hx := by
    apply Subtype.ext
    change OpenPartialHomeomorph.univUnitBall (Complex.orthonormalBasisOneI.repr
      (Complex.orthonormalBasisOneI.repr.symm (OpenPartialHomeomorph.univUnitBall.symm x.val))) =
      x.val
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact OpenPartialHomeomorph.univUnitBall.right_inv (mem_ball_zero_iff.mpr hx)
  right_inv' z _ := by
    change Complex.orthonormalBasisOneI.repr.symm (OpenPartialHomeomorph.univUnitBall.symm
      (OpenPartialHomeomorph.univUnitBall (Complex.orthonormalBasisOneI.repr z))) = z
    rw [OpenPartialHomeomorph.univUnitBall.left_inv (mem_univ _),
      LinearIsometryEquiv.symm_apply_apply]
  open_source := isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const
  open_target := isOpen_univ
  continuousOn_toFun := by
    have h := OpenPartialHomeomorph.univUnitBall.continuousOn_symm.comp
      (continuous_subtype_val.continuousOn (s := {x : ClosedCell 2 | ‖x.val‖ < 1}))
      (fun x hx => mem_ball_zero_iff.mpr hx)
    exact Complex.orthonormalBasisOneI.repr.symm.continuous.comp_continuousOn h
  continuousOn_invFun := by
    refine Continuous.continuousOn ?_
    exact ((OpenPartialHomeomorph.contDiff_univUnitBall (n := ⊤)).continuous.comp
      Complex.orthonormalBasisOneI.repr.continuous).subtype_mk _

theorem closedDiskPlanarChart_source :
    closedDiskPlanarChart.source = {x : ClosedCell 2 | ‖x.val‖ < 1} := rfl

theorem closedDiskPlanarChart_target : closedDiskPlanarChart.target = univ := rfl

theorem contMDiffOn_closedDiskPlanarChart :
    ContMDiffOn (𝓡∂ 2) 𝓘(ℝ, ℂ) ∞ closedDiskPlanarChart closedDiskPlanarChart.source := by
  have hval : ContMDiff (𝓡∂ 2) (𝓡 2) ∞ (Subtype.val : ClosedCell 2 → EuclideanSpace ℝ (Fin 2)) :=
    (DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_closedCell_inclusion 1).contMDiff
  have hball : ContMDiffOn (𝓡 2) (𝓡 2) ∞
      (OpenPartialHomeomorph.univUnitBall.symm : EuclideanSpace ℝ (Fin 2) → _)
      (ball (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    (OpenPartialHomeomorph.contDiffOn_univUnitBall_symm (n := ⊤)).contMDiffOn
  have hcomp := hball.comp hval.contMDiffOn
    (fun x (hx : ‖x.val‖ < 1) => mem_ball_zero_iff.mpr hx)
  exact Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv.contDiff.contMDiff.comp_contMDiffOn
    hcomp

theorem contMDiff_closedDiskPlanarChart_symm :
    ContMDiff 𝓘(ℝ, ℂ) (𝓡∂ 2) ∞ closedDiskPlanarChart.symm := by
  refine (ContMDiff.iff_comp_isImmersion
    (DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_closedCell_inclusion 1).isImmersion).mpr
    ⟨?_, ?_⟩
  · exact ((OpenPartialHomeomorph.contDiff_univUnitBall (n := ⊤)).continuous.comp
      Complex.orthonormalBasisOneI.repr.continuous).subtype_mk _
  · change ContMDiff 𝓘(ℝ, ℂ) (𝓡 2) ∞
      (fun z : ℂ => OpenPartialHomeomorph.univUnitBall (Complex.orthonormalBasisOneI.repr z))
    exact ((OpenPartialHomeomorph.contDiff_univUnitBall (n := ⊤)).comp
      Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv.contDiff).contMDiff

theorem contMDiffOn_closedDiskPlanarChart_symm :
    ContMDiffOn 𝓘(ℝ, ℂ) (𝓡∂ 2) ∞ closedDiskPlanarChart.symm closedDiskPlanarChart.target :=
  contMDiff_closedDiskPlanarChart_symm.contMDiffOn

/-! ## SM-D -/

/-- **SM-D, strong form.** The frozen SM-D together with the joint smoothness of the inverses
`(J t).symm` (needed to descend an isotopy to a mapping torus). -/
theorem exists_diskIsotopy_rel_boundary
    (φ : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2) (N : Set (ClosedCell 2)) (hN : IsOpen N)
    (hrim : diskRim ⊆ N) (hφ : ∀ x ∈ N, φ x = x) :
    ∃ N' : Set (ClosedCell 2), IsOpen N' ∧ diskRim ⊆ N' ∧ N' ⊆ N ∧
      ∃ J : ℝ → (ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2),
        ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞ (fun p : ClosedCell 2 × ℝ => J p.2 p.1) ∧
        ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞ (fun p : ClosedCell 2 × ℝ => (J p.2).symm p.1) ∧
        (∀ x, J 0 x = φ x) ∧ (∀ x, J 1 x = x) ∧ (∀ t, ∀ x ∈ N', J t x = x) ∧
        ∃ ε : ℝ, 0 < ε ∧ (∀ t x, t < ε → J t x = φ x) ∧ (∀ t x, 1 - ε < t → J t x = x) := by
  have hK : IsCompact Nᶜ := hN.isClosed_compl.isCompact
  have hKs : Nᶜ ⊆ closedDiskPlanarChart.source := fun x hx =>
    norm_lt_one_of_notMem_diskRim fun hr => hx (hrim hr)
  obtain ⟨H, hH, hHi, hH0, hH1, C, hC, hCs, hHfix⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_isotopy_of_support_in_planar_chart
      closedDiskPlanarChart closedDiskPlanarChart_target contMDiffOn_closedDiskPlanarChart
      contMDiffOn_closedDiskPlanarChart_symm φ hK hKs (fun x hx => hφ x (not_not.mp hx))
  refine ⟨N ∩ Cᶜ, hN.inter hC.isClosed.isOpen_compl, fun x hx => ⟨hrim hx, fun hxC =>
    notMem_diskRim_of_norm_lt_one (hCs hxC) hx⟩, inter_subset_left, ?_⟩
  have hH' : ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞
      (fun p : ClosedCell 2 × ℝ => H p.2 p.1) :=
    hH.comp (contMDiff_snd.prodMk contMDiff_fst)
  have hHi' : ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞
      (fun p : ClosedCell 2 × ℝ => (H p.2).symm p.1) :=
    hHi.comp (contMDiff_snd.prodMk contMDiff_fst)
  refine ⟨isotopyFlatten H, contMDiff_isotopyFlatten hH', contMDiff_isotopyFlatten hHi', ?_, ?_,
    ?_, 1 / 3, by norm_num, ?_, ?_⟩
  · intro x
    rw [isotopyFlatten_zero, hH0]
  · intro x
    rw [isotopyFlatten_one, hH1]
    rfl
  · intro t x hx
    exact (hHfix _ x hx.2).1
  · intro t x ht
    rw [isotopyFlatten_of_le H ht.le, hH0]
  · intro t x ht
    rw [isotopyFlatten_of_ge H (by linarith), hH1]
    rfl

/-- **SM-D (V2, review item 1, D1).** A diffeomorphism of the closed disk that is the identity on an
open neighbourhood `N` of the rim is isotopic to the identity through diffeomorphisms fixing an open
`N' ⊆ N` containing the rim; the isotopy is jointly smooth, goes from `φ` (time `0`) to the identity
(time `1`) and is constant for `t < ε` and for `t > 1 − ε`. The frozen V2 text verbatim. -/
theorem diskDiffeomorph_isotopic_refl_rel_boundary
    (φ : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2) (N : Set (ClosedCell 2)) (hN : IsOpen N)
    (hrim : diskRim ⊆ N) (hφ : ∀ x ∈ N, φ x = x) :
    ∃ N' : Set (ClosedCell 2), IsOpen N' ∧ diskRim ⊆ N' ∧ N' ⊆ N ∧
      ∃ J : ℝ → (ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2),
        ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞ (fun p : ClosedCell 2 × ℝ => J p.2 p.1) ∧
        (∀ x, J 0 x = φ x) ∧ (∀ x, J 1 x = x) ∧ (∀ t, ∀ x ∈ N', J t x = x) ∧
        ∃ ε : ℝ, 0 < ε ∧ (∀ t x, t < ε → J t x = φ x) ∧ (∀ t x, 1 - ε < t → J t x = x) := by
  obtain ⟨N', hN', hrim', hN'N, J, hJ, -, hJ0, hJ1, hJfix, hflat⟩ :=
    exists_diskIsotopy_rel_boundary φ N hN hrim hφ
  exact ⟨N', hN', hrim', hN'N, J, hJ, hJ0, hJ1, hJfix, hflat⟩

end GC.GraphManifold.Assembly
