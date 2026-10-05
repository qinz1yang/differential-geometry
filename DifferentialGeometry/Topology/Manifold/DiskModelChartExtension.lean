import DifferentialGeometry.Topology.Manifold.DiskPolarCollarTwoSided
import DifferentialGeometry.Topology.Manifold.SmoothExtension
import DifferentialGeometry.Topology.Manifold.InverseFunction
import DifferentialGeometry.Topology.Manifold.ClosedBall
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Topology.Embedding.Extension
import DifferentialGeometry.Topology.Handle.Embedding

/-!
# A disk model extended across the rim: the chart of the fibre in the slice

Lane POLAR-2 (the row-side input of the both-sides polar collar of lane POLAR-1). Let `S` be a
manifold with boundary with a disk model `D₀ : ClosedCell (m + 1) ≃ₘ S`, and `ι : S → N` an
injective immersion into a boundaryless `(m + 1)`-manifold `N` (e.g. the fibre of an edge disk
packet inside the slice `{η_p = 0}` of its slab). Then:

* `exists_contMDiffOn_extension_of_closedCell`: every smooth map out of the closed cell into a
  boundaryless manifold extends smoothly to an open neighbourhood of the closed ball (local
  half-space extensions in a chart of the target, glued by
  `DifferentialGeometry.Topology.exists_contMDiffOn_extension_closedBall`);
* `exists_partialDiffeomorph_extend_diskModel`: a partial diffeomorphism `j` from an open
  neighbourhood of the closed unit ball into `N` with `j = ι ∘ D₀` on the cell (the extension of
  `ι ∘ D₀` has bijective differential on the closed ball because `ι` is an immersion and `D₀` a
  diffeomorphism; inverse function theorem and injectivity on the compact ball);
* `exists_diskModel_polar_twoSided_of_immersion`: with this `j`, POLAR-1's
  `exists_diskModel_polar_twoSided`, the hypotheses stated on `∂S` instead of on `j`;
* `exists_partialDiffeomorph_extend_closedCell_inclusion`: compiled inhabitant (`S` = cell,
  `N = ℝᵐ⁺¹`, `ι` = inclusion).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Function Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

/-- Local step of `exists_contMDiffOn_extension_of_closedCell`: near every point of the closed ball
the map extends smoothly (a cut-off chart expression extended along the cell inclusion). -/
private theorem local_extension_closedCell_POLAR2 {m : ℕ} {E' H' N : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E'] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E' H'} [I.Boundaryless] [TopologicalSpace N] [ChartedSpace H' N]
    [IsManifold I ∞ N] {h : ClosedCell (m + 1) → N}
    (hh : ContMDiff (𝓡∂ (m + 1)) I ∞ h) (x : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    ∃ U : EuclideanSpace ℝ (Fin (m + 1)) → N, ∃ V : Set (EuclideanSpace ℝ (Fin (m + 1))),
      IsOpen V ∧ (x : EuclideanSpace ℝ (Fin (m + 1))) ∈ V ∧ ContMDiffOn (𝓡 (m + 1)) I ∞ U V ∧
      ∀ y : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
        (y : EuclideanSpace ℝ (Fin (m + 1))) ∈ V → U y = h ⟨y, mem_closedBall_zero_iff.mp y.2⟩ := by
  have hval : ContMDiff (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞
      (Subtype.val : ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) :=
    Handle.closedCellInclusion_contMDiff m
  -- the chart of `N` at `h x` and a ball of the cell mapped into its source
  let xc : ClosedCell (m + 1) := ⟨x, mem_closedBall_zero_iff.mp x.2⟩
  let p : N := h xc
  have hW : IsOpen (h ⁻¹' (chartAt H' p).source) :=
    (chartAt H' p).open_source.preimage hh.continuous
  obtain ⟨O', hO'o, hO'⟩ := isOpen_induced_iff.mp hW
  have hxO' : (x : EuclideanSpace ℝ (Fin (m + 1))) ∈ O' := by
    have hxc : xc ∈ h ⁻¹' (chartAt H' p).source := mem_chart_source H' p
    rw [← hO'] at hxc
    exact hxc
  obtain ⟨r, hr, hrO'⟩ := Metric.isOpen_iff.mp hO'o _ hxO'
  have hsrc : ∀ y : ClosedCell (m + 1),
      dist (y : EuclideanSpace ℝ (Fin (m + 1))) x < r → h y ∈ (chartAt H' p).source := by
    intro y hy
    have hy' : y ∈ Subtype.val ⁻¹' O' := hrO' (mem_ball.mpr hy)
    rw [hO'] at hy'
    exact hy'
  -- the cut-off chart expression of `h`
  let χ : ContDiffBump (x : EuclideanSpace ℝ (Fin (m + 1))) :=
    ⟨r / 4, r / 2, by positivity, by linarith⟩
  let gl : ClosedCell (m + 1) → E' :=
    fun y => χ (y : EuclideanSpace ℝ (Fin (m + 1))) • extChartAt I p (h y)
  have hgl : ContMDiff (𝓡∂ (m + 1)) 𝓘(ℝ, E') ∞ gl := by
    intro y
    by_cases hy : dist (y : EuclideanSpace ℝ (Fin (m + 1))) x < r
    · have hχ : ContMDiffAt (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) ∞
          (fun y : ClosedCell (m + 1) => χ (y : EuclideanSpace ℝ (Fin (m + 1)))) y :=
        (χ.contDiff.contMDiff.comp hval) y
      have he : ContMDiffAt (𝓡∂ (m + 1)) 𝓘(ℝ, E') ∞ (fun y => extChartAt I p (h y)) y :=
        (contMDiffAt_extChartAt' (hsrc y hy)).comp y (hh y)
      exact hχ.smul he
    · have hop : IsOpen
          {w : ClosedCell (m + 1) | r / 2 < dist (w : EuclideanSpace ℝ (Fin (m + 1))) x} :=
        isOpen_lt continuous_const (continuous_subtype_val.dist continuous_const)
      have hyr : r / 2 < dist (y : EuclideanSpace ℝ (Fin (m + 1))) x := by
        push Not at hy
        linarith
      have hev : gl =ᶠ[𝓝 y] fun _ => (0 : E') := by
        filter_upwards [hop.mem_nhds hyr] with w hw
        change χ (w : EuclideanSpace ℝ (Fin (m + 1))) • _ = 0
        rw [χ.zero_of_le_dist hw.le, zero_smul]
      exact contMDiffAt_const.congr_of_eventuallyEq hev
  obtain ⟨U, hU, hxU, G₀, hG₀, hG₀g⟩ :=
    Manifold.IsSmoothEmbedding.exists_contDiffOn_local_extension_halfspace
      (Handle.closedCellInclusion_isSmoothEmbedding (m := m)) hgl xc
  have hG₀x : G₀ x = extChartAt I p p := by
    have h1 := hG₀g xc hxU
    change G₀ x = χ x • extChartAt I p (h xc) at h1
    rw [h1, χ.one_of_mem_closedBall (mem_closedBall_self (by positivity)), one_smul]
  -- the local extension `e.symm ∘ G₀`
  refine ⟨fun y => (extChartAt I p).symm (G₀ y),
    (U ∩ ball (x : EuclideanSpace ℝ (Fin (m + 1))) (r / 4)) ∩ G₀ ⁻¹' (extChartAt I p).target,
    ?_, ?_, ?_, ?_⟩
  · exact (hG₀.mono inter_subset_left).continuousOn.isOpen_inter_preimage (hU.inter isOpen_ball)
      (isOpen_extChartAt_target p)
  · refine ⟨⟨hxU, mem_ball_self (by positivity)⟩, ?_⟩
    change G₀ x ∈ (extChartAt I p).target
    rw [hG₀x]
    exact mem_extChartAt_target p
  · exact (contMDiffOn_extChartAt_symm p).comp
      ((hG₀.mono (inter_subset_left.trans inter_subset_left)).contMDiffOn) (fun y hy => hy.2)
  · intro y hy
    let yc : ClosedCell (m + 1) := ⟨y, mem_closedBall_zero_iff.mp y.2⟩
    have hyd : dist (y : EuclideanSpace ℝ (Fin (m + 1))) x < r / 4 := mem_ball.mp hy.1.2
    have h1 := hG₀g yc hy.1.1
    change G₀ y = χ y • extChartAt I p (h yc) at h1
    rw [χ.one_of_mem_closedBall (mem_closedBall.mpr hyd.le), one_smul] at h1
    change (extChartAt I p).symm (G₀ y) = h yc
    rw [h1]
    exact (extChartAt I p).left_inv (by
      rw [extChartAt_source]
      exact hsrc yc (by linarith))

/-- **Smooth maps out of the closed cell extend across the rim.** A smooth map from the closed cell
into a boundaryless manifold is the restriction of a map that is smooth on an open neighbourhood of
the closed unit ball. -/
theorem exists_contMDiffOn_extension_of_closedCell {m : ℕ} {E' H' N : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E'] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E' H'} [I.Boundaryless] [TopologicalSpace N] [ChartedSpace H' N]
    [IsManifold I ∞ N] {h : ClosedCell (m + 1) → N}
    (hh : ContMDiff (𝓡∂ (m + 1)) I ∞ h) :
    ∃ G : EuclideanSpace ℝ (Fin (m + 1)) → N,
      (∀ z : ClosedCell (m + 1), G (z : EuclideanSpace ℝ (Fin (m + 1))) = h z) ∧
      ∃ O : Set (EuclideanSpace ℝ (Fin (m + 1))), IsOpen O ∧
        closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ⊆ O ∧
        ContMDiffOn (𝓡 (m + 1)) I ∞ G O := by
  let u : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 → N :=
    fun y => h ⟨y, mem_closedBall_zero_iff.mp y.2⟩
  have hloc : ∀ x : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
      ∃ U : EuclideanSpace ℝ (Fin (m + 1)) → N, ∃ V : Set (EuclideanSpace ℝ (Fin (m + 1))),
        IsOpen V ∧ (x : EuclideanSpace ℝ (Fin (m + 1))) ∈ V ∧ ContMDiffOn (𝓡 (m + 1)) I ∞ U V ∧
        ∀ y : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
          (y : EuclideanSpace ℝ (Fin (m + 1))) ∈ V → U y = u y := by
    intro x
    exact local_extension_closedCell_POLAR2 hh x
  obtain ⟨G, -, hGu, O, hO, hBO, hGO⟩ :=
    DifferentialGeometry.Topology.exists_contMDiffOn_extension_closedBall (I := I) (n := ⊤)
      (0 : EuclideanSpace ℝ (Fin (m + 1))) zero_le_one u hloc
  exact ⟨G, fun z => hGu ⟨z, mem_closedBall_zero_iff.mpr z.2⟩, O, hO, hBO, hGO⟩

/-- **The chart of a disk model extended across the rim.** Let `D₀ : ClosedCell (m + 1) ≃ₘ S` be
a disk model and `ι : S → N` an injective immersion into a boundaryless `(m + 1)`-manifold. Then a
partial diffeomorphism `j` of `ℝᵐ⁺¹` into `N`, defined on an open neighbourhood of the closed unit
ball, extends `ι ∘ D₀`. -/
theorem exists_partialDiffeomorph_extend_diskModel {m : ℕ} {N S : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) N] [IsManifold (𝓡 (m + 1)) ∞ N] [T2Space N]
    [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace (m + 1)) S]
    (D₀ : ClosedCell (m + 1) ≃ₘ⟮𝓡∂ (m + 1), 𝓡∂ (m + 1)⟯ S) (ι : S → N)
    (hι : ContMDiff (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ ι) (hιinj : Injective ι)
    (hιimm : ∀ y : S, Injective (mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1)) ι y)) :
    ∃ j : PartialDiffeomorph (𝓡 (m + 1)) (𝓡 (m + 1)) (EuclideanSpace ℝ (Fin (m + 1))) N ∞,
      closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ⊆ j.source ∧
      ∀ z : ClosedCell (m + 1), j (z : EuclideanSpace ℝ (Fin (m + 1))) = ι (D₀ z) := by
  have hh : ContMDiff (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ (ι ∘ D₀) := hι.comp D₀.contMDiff
  obtain ⟨G, hG, O, hO, hBO, hGO⟩ := exists_contMDiffOn_extension_of_closedCell hh
  have hval : ContMDiff (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞
      (Subtype.val : ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) :=
    Handle.closedCellInclusion_contMDiff m
  have hGval : G ∘ (Subtype.val : ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) =
      ι ∘ D₀ := funext hG
  have hGd : ∀ x ∈ O, MDifferentiableAt (𝓡 (m + 1)) (𝓡 (m + 1)) G x := fun x hx =>
    ((hGO x hx).contMDiffAt (hO.mem_nhds hx)).mdifferentiableAt (by simp)
  -- 1. the differential of `G` is bijective on the closed ball
  have hbij : ∀ x : EuclideanSpace ℝ (Fin (m + 1)), ‖x‖ ≤ 1 →
      Bijective (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) G x) := by
    intro x hx
    let xc : ClosedCell (m + 1) := ⟨x, hx⟩
    have hxO : x ∈ O := hBO (mem_closedBall_zero_iff.mpr hx)
    have hvd : MDifferentiableAt (𝓡∂ (m + 1)) (𝓡 (m + 1))
        (Subtype.val : ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) xc :=
      (hval xc).mdifferentiableAt (by simp)
    have hιd : MDifferentiableAt (𝓡∂ (m + 1)) (𝓡 (m + 1)) ι (D₀ xc) :=
      (hι _).mdifferentiableAt (by simp)
    have hDd : MDifferentiableAt (𝓡∂ (m + 1)) (𝓡∂ (m + 1)) D₀ xc :=
      D₀.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
    have hinjD : Injective (mfderiv (𝓡∂ (m + 1)) (𝓡∂ (m + 1)) D₀ xc) := by
      obtain ⟨e, he⟩ := (D₀.isLocalDiffeomorph xc).isInvertible_mfderiv (by simp)
      rw [← he]
      exact e.injective
    have hi : Injective ((mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) G x).comp
        (mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1))
          (Subtype.val : ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) xc)) := by
      have h1 := mfderiv_comp xc (hGd x hxO) hvd
      have h2 := mfderiv_comp xc hιd hDd
      rw [← h1, hGval, h2]
      exact (hιimm _).comp hinjD
    have hs : Surjective ((mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) G x).comp
        (mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1))
          (Subtype.val : ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) xc)) :=
      LinearMap.surjective_of_injective
        (f := ((mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) G x).comp
          (mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1))
            (Subtype.val : ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) xc)).toLinearMap)
        hi
    have hGs : Surjective (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) G x) :=
      Surjective.of_comp (f := mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) G x)
        (g := mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1))
          (Subtype.val : ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) xc) hs
    exact ⟨(LinearMap.injective_iff_surjective
      (f := (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) G x).toLinearMap)).mpr hGs, hGs⟩
  -- 2. inverse function theorem on the closed ball, injectivity, compactness
  have hloc : IsLocalDiffeomorphOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ G
      (closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) := by
    intro x
    have hx : ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ ≤ 1 := mem_closedBall_zero_iff.mp x.2
    have hb : Bijective (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) G x) := hbij x hx
    let A : EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
      ContinuousLinearEquiv.ofBijective (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) G x)
        (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
    exact isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv G hGO hO x (hBO x.2) A
      (hGd x (hBO x.2)).hasMFDerivAt
  have hinj : InjOn G (closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) := by
    intro x hx y hy hxy
    have hx' : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
    have hy' : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.mp hy
    have h1 : ι (D₀ ⟨x, hx'⟩) = ι (D₀ ⟨y, hy'⟩) :=
      (hG ⟨x, hx'⟩).symm.trans (hxy.trans (hG ⟨y, hy'⟩))
    exact congrArg Subtype.val (D₀.injective (hιinj h1))
  obtain ⟨φ, hφs, hφG⟩ :=
    DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_isCompact hloc
      (isCompact_closedBall _ _) ⟨0, mem_closedBall_self zero_le_one⟩ hinj
  refine ⟨φ, hφs, fun z => ?_⟩
  have h1 : φ (z : EuclideanSpace ℝ (Fin (m + 1))) = G z := congrFun hφG z
  rw [h1, hG]
  rfl

/-- **The both-sides polar collar of an immersed disk.** For a disk model `D₀ : ClosedCell ≃ₘ S`
and an injective immersion `ι : S → N` into a boundaryless manifold, and `T : N → ℝ` smooth on an
open `V ⊇ ι (∂S)` with `T ∘ ι = c` on `∂S`, `T ∘ ι ≤ c` on `ι⁻¹ V` and `dT ≠ 0` on `ι (∂S)`: one
construction gives the re-modelled disk model `D` (equal to `D₀` on the rim and on `‖z‖ ≤ 1 - η`)
and the both-sides polar collar `C` of `exists_diskDiffeomorph_polar_twoSided` in `N`, with
`C = ι ∘ D₀` on the sphere and `ι ∘ D = C` on the inner side `1 - δ < ‖z‖`. -/
theorem exists_diskModel_polar_twoSided_of_immersion {m : ℕ} {N S : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) N] [IsManifold (𝓡 (m + 1)) ∞ N] [T2Space N]
    [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace (m + 1)) S]
    (D₀ : ClosedCell (m + 1) ≃ₘ⟮𝓡∂ (m + 1), 𝓡∂ (m + 1)⟯ S) (ι : S → N)
    (hι : ContMDiff (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ ι) (hιinj : Injective ι)
    (hιimm : ∀ y : S, Injective (mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1)) ι y))
    {T : N → ℝ} {V : Set N} (hV : IsOpen V)
    (hbV : ∀ y : S, (𝓡∂ (m + 1)).IsBoundaryPoint y → ι y ∈ V)
    (hT : ContMDiffOn (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ T V) {c : ℝ}
    (hTc : ∀ y : S, (𝓡∂ (m + 1)).IsBoundaryPoint y → T (ι y) = c)
    (hTle : ∀ y : S, ι y ∈ V → T (ι y) ≤ c)
    (hreg : ∀ y : S, (𝓡∂ (m + 1)).IsBoundaryPoint y → mfderiv (𝓡 (m + 1)) 𝓘(ℝ, ℝ) T (ι y) ≠ 0)
    {κ : ℝ} (hκ : 0 < κ) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < η ∧
      ∃ D : ClosedCell (m + 1) ≃ₘ⟮𝓡∂ (m + 1), 𝓡∂ (m + 1)⟯ S,
      ∃ C : PartialDiffeomorph (𝓡 (m + 1)) (𝓡 (m + 1)) (EuclideanSpace ℝ (Fin (m + 1))) N ∞,
        C.source = {z : EuclideanSpace ℝ (Fin (m + 1)) | |‖z‖ - 1| < δ} ∧
        (∀ z ∈ C.source, C z ∈ V ∧ T (C z) = c + κ * (‖z‖ - 1)) ∧
        (∀ z : ClosedCell (m + 1), ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 →
          C (z : EuclideanSpace ℝ (Fin (m + 1))) = ι (D₀ z)) ∧
        (∀ z : ClosedCell (m + 1), 1 - δ < ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ →
          ι (D z) = C (z : EuclideanSpace ℝ (Fin (m + 1)))) ∧
        (∀ z : ClosedCell (m + 1), ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 → D z = D₀ z) ∧
        (∀ z : ClosedCell (m + 1), ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ ≤ 1 - η →
          D z = D₀ z) := by
  obtain ⟨j, hjs, hjD⟩ := exists_partialDiffeomorph_extend_diskModel D₀ ι hι hιinj hιimm
  have hbd : ∀ z : ClosedCell (m + 1),
      (𝓡∂ (m + 1)).IsBoundaryPoint z ↔ ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 :=
    fun z => Set.ext_iff.mp (closedCell_boundary_eq_sphere m) z
  have hbdD : ∀ y : EuclideanSpace ℝ (Fin (m + 1)), ∀ hy : ‖y‖ = 1,
      (𝓡∂ (m + 1)).IsBoundaryPoint (D₀ ⟨y, hy.le⟩) := fun y hy =>
    ((D₀.isLocalDiffeomorph _).isBoundaryPoint_iff (by simp)).mp ((hbd ⟨y, hy.le⟩).mpr hy)
  have hjy : ∀ y : EuclideanSpace ℝ (Fin (m + 1)), ∀ hy : ‖y‖ ≤ 1, j y = ι (D₀ ⟨y, hy⟩) :=
    fun y hy => hjD ⟨y, hy⟩
  obtain ⟨δ, hδ0, hδη, D, C, hCs, hCT, hCS, hCD, hDS, hDη⟩ :=
    exists_diskModel_polar_twoSided D₀ ι j
      (fun y hy => hjs (mem_closedBall_zero_iff.mpr hy.le)) (fun z => hjD z) hV
      (fun y hy => by rw [hjy y hy.le]; exact hbV _ (hbdD y hy)) hT
      (fun y hy => by rw [hjy y hy.le]; exact hTc _ (hbdD y hy))
      (fun y hy hyV => by rw [hjy y hy] at hyV ⊢; exact hTle _ hyV)
      (fun y hy => by rw [hjy y hy.le]; exact hreg _ (hbdD y hy)) hκ hη0 hη1
  refine ⟨δ, hδ0, hδη, D, C, hCs, hCT, fun z hz => ?_, hCD, hDS, hDη⟩
  rw [hCS z hz, hjD]

/-- **Compiled inhabitant: the closed cell in `ℝᵐ⁺¹`.** For `S` the closed cell, `D₀ = id` and
`ι` the inclusion into `N = ℝᵐ⁺¹` all hypotheses of `exists_partialDiffeomorph_extend_diskModel`
hold: there is a chart `j` on a neighbourhood of the closed ball with `j = id` on the cell. -/
theorem exists_partialDiffeomorph_extend_closedCell_inclusion (m : ℕ) :
    ∃ j : PartialDiffeomorph (𝓡 (m + 1)) (𝓡 (m + 1)) (EuclideanSpace ℝ (Fin (m + 1)))
        (EuclideanSpace ℝ (Fin (m + 1))) ∞,
      closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ⊆ j.source ∧
      ∀ z : ClosedCell (m + 1), j (z : EuclideanSpace ℝ (Fin (m + 1))) = z :=
  exists_partialDiffeomorph_extend_diskModel (Diffeomorph.refl (𝓡∂ (m + 1)) (ClosedCell (m + 1)) ∞)
    Subtype.val (Handle.closedCellInclusion_contMDiff m) Subtype.val_injective
    (fun y => injective_mfderiv_of_isImmersionAt (𝓡∂ (m + 1)) (𝓡 (m + 1)) Subtype.val y
      ((Handle.closedCellInclusion_isSmoothEmbedding (m := m)).isImmersion.isImmersionAt y))

end DifferentialGeometry.Topology.Manifold
