import DifferentialGeometry.Topology.Manifold.DiskPolarRemodel

/-!
# The both-sides polar collar of a disk fibre

Lane POLAR-1 (the outer side of the polar re-modelling of review 44 item (3); review 46 §2.1:
"build the radial germ so that the new and the old boundary labels coincide pointwise, then extend
to the whole disk"). Let `N` be a boundaryless `(m + 1)`-manifold, `j` a chart of `N` (a partial
diffeomorphism from `ℝᵐ⁺¹`) whose source contains the unit sphere — e.g. the end slice of an edge
bundle with the fibre's disk model extended across the rim — and `T : N → ℝ` smooth on an open `V`
containing `j (sphere)`, with `T ∘ j = c` on the sphere, `T ∘ j ≤ c` on the inner side (in `V`) and
`dT ≠ 0` on `j (sphere)`. Then `exists_diskDiffeomorph_polar_twoSided` gives `δ ∈ (0, η)`, a
diffeomorphism `ψ` of the closed cell and a partial diffeomorphism `C` from the open annulus
`{|‖z‖ - 1| < δ}` (BOTH sides of the sphere) into `N` with

* `T (C z) = c + κ (‖z‖ - 1)` on the whole annulus (the collar is polar for `T` on both sides),
* `C = j` on the sphere (pointwise boundary labels),
* `C z = j (ψ z)` on the inner side `1 - δ < ‖z‖ ≤ 1` (the same germ re-models the disk),
* `ψ = id` on the sphere and on `‖z‖ ≤ 1 - η`.

`exists_diskModel_polar_twoSided` is the disk-model form (a fibre `S` with `D₀ : ClosedCell ≃ₘ S`
and `ι : S → N`, `ι ∘ D₀ = j` on the cell): one construction gives the new disk model `D` and the
collar `C` with `ι ∘ D = C` near the rim. `exists_polarCollar_twoSided_normSq` is a compiled
inhabitant (`N = ℝᵐ⁺¹`, `j = id`, `T = ‖·‖²`).

Construction. The kernel `exists_planePolarGerm` is steps 4–6 of
`exists_closedCellDiffeomorph_polar` on the whole plane, for a function `G` smooth only on an open
`W ⊇ sphere`: the radial normalization `boundaryPolarMap G c κ` is a partial diffeomorphism near the
sphere; its inverse `F` on a thin annulus where `|G - c| < κ / 2` satisfies
`G (F w) = c + κ (‖w‖ - 1)` on its whole (two-sided) source and maps the outside of the ball to the
outside (by `G ≤ c` inside and injectivity). In the main theorem `G = T ∘ j`, the sphere-germ
isotopy realizes `F` near the sphere by a diffeomorphism `Φ 1` of the plane preserving the ball,
`ψ` is its restriction to the cell and `C` is `j ∘ F` restricted to the annulus.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Function Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace DifferentialGeometry.Topology.Manifold

section Plane

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The radial normalization is smooth wherever `G` is smooth, away from the origin. -/
theorem contDiffOn_boundaryPolarMap_of_contDiffOn {G : E → ℝ} {W : Set E} (hW : IsOpen W)
    (hG : ContDiffOn ℝ ∞ G W) (c κ : ℝ) :
    ContDiffOn ℝ ∞ (boundaryPolarMap G c κ) (W ∩ {z | z ≠ 0}) := by
  intro z hz
  apply ContDiffAt.contDiffWithinAt
  exact (contDiffAt_const.add (contDiffAt_const.mul
    ((hG.contDiffAt (hW.mem_nhds hz.1)).sub contDiffAt_const))).smul
    (((contDiffAt_norm ℝ hz.2).inv (norm_ne_zero_iff.mpr hz.2)).smul contDiffAt_id)

variable [FiniteDimensional ℝ E] [Nontrivial E]

/-- **Two-sided polar germ on the plane.** Let `G` be smooth on an open `W ⊇ sphere`, equal to `c`
on the unit sphere, `≤ c` on the inner part of `W` and regular on the sphere. Then a partial
diffeomorphism `F` of the plane, defined near the sphere and fixing it pointwise, makes `G` radial
on its whole source (both sides of the sphere): `G (F w) = c + κ (‖w‖ - 1)`; `F` maps the outside of
the ball to the outside. -/
theorem exists_planePolarGerm {G : E → ℝ} {W : Set E} (hW : IsOpen W)
    (hSW : sphere (0 : E) 1 ⊆ W) (hG : ContDiffOn ℝ ∞ G W) {c : ℝ}
    (hGc : ∀ y : E, ‖y‖ = 1 → G y = c) (hle : ∀ y ∈ W, ‖y‖ ≤ 1 → G y ≤ c)
    (hreg : ∀ y : E, ‖y‖ = 1 → fderiv ℝ G y ≠ 0) {κ : ℝ} (hκ : 0 < κ) :
    ∃ F : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞, sphere (0 : E) 1 ⊆ F.source ∧
      EqOn F id (sphere (0 : E) 1) ∧
      (∀ w ∈ F.source, F w ∈ W ∧ G (F w) = c + κ * (‖w‖ - 1)) ∧
      MapsTo F ((ball (0 : E) 1)ᶜ ∩ F.source) (ball (0 : E) 1)ᶜ := by
  -- 1. the radial normalization is a local diffeomorphism at the sphere
  let h := boundaryPolarMap G c κ
  have hW0 : IsOpen (W ∩ {z : E | z ≠ 0}) := hW.inter isOpen_ne
  have hhd : ContDiffOn ℝ ∞ h (W ∩ {z : E | z ≠ 0}) :=
    contDiffOn_boundaryPolarMap_of_contDiffOn hW hG c κ
  have hhs : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ h (W ∩ {z : E | z ≠ 0}) := hhd.contMDiffOn
  have hGd : ∀ x ∈ W, DifferentiableAt ℝ G x := fun x hx =>
    (hG.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp)
  have hloc : IsLocalDiffeomorphOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ h (sphere (0 : E) 1) := by
    intro x
    have hx : ‖(x : E)‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
    have hx0 : (x : E) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hx
      exact zero_ne_one hx
    have hxW : (x : E) ∈ W := hSW x.2
    have hbij := bijective_fderiv_boundaryPolarMap hGc hx (hGd x hxW) (hreg x hx) hκ.ne'
    let A := ContinuousLinearEquiv.ofBijective (fderiv ℝ h x)
      (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
    have hd : DifferentiableAt ℝ h x :=
      (hhd.contDiffAt (hW0.mem_nhds ⟨hxW, hx0⟩)).differentiableAt (by simp)
    exact isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv h hhs hW0 x ⟨hxW, hx0⟩ A
      hd.hasFDerivAt.hasMFDerivAt
  have hhS : ∀ x : E, ‖x‖ = 1 → h x = x :=
    fun x hx => boundaryPolarMap_of_norm_eq_one hx (hGc x hx)
  have hinjS : InjOn h (sphere (0 : E) 1) := by
    intro x hx y hy hxy
    rwa [hhS x (mem_sphere_zero_iff_norm.mp hx), hhS y (mem_sphere_zero_iff_norm.mp hy)] at hxy
  obtain ⟨φ, hφs, hφh⟩ :=
    DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_isCompact
      hloc (isCompact_sphere _ _) (NormedSpace.sphere_nonempty.mpr zero_le_one) hinjS
  -- 2. the annulus where `|G - c| < κ / 2`, inside `W`
  have hO₁ : IsOpen (W ∩ G ⁻¹' ball c (κ / 2)) :=
    hG.continuousOn.isOpen_inter_preimage hW isOpen_ball
  have hSO₁ : sphere (0 : E) 1 ⊆ W ∩ G ⁻¹' ball c (κ / 2) := by
    intro x hx
    refine ⟨hSW hx, ?_⟩
    change dist (G x) c < κ / 2
    rw [hGc x (mem_sphere_zero_iff_norm.mp hx), dist_self]
    linarith
  obtain ⟨δ₁', hδ₁', hthick₁⟩ :=
    (isCompact_sphere (0 : E) 1).exists_thickening_subset_open hO₁ hSO₁
  set δ₁ := min δ₁' (1 / 2) with hδ₁def
  have hδ₁ : 0 < δ₁ := lt_min hδ₁' (by norm_num)
  let Ann : Set E := {z | |‖z‖ - 1| < δ₁}
  have hAnn : IsOpen Ann :=
    isOpen_lt ((continuous_norm.sub continuous_const).abs) continuous_const
  have hAnnp : ∀ z ∈ Ann, z ≠ 0 ∧ z ∈ W ∧ |G z - c| < κ / 2 := by
    intro z hz
    have hz' : |‖z‖ - 1| < δ₁ := hz
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hz'
      norm_num at hz'
      linarith [min_le_right δ₁' (1 / 2)]
    have hmem := hthick₁ (mem_thickening_sphere_of_abs_norm_sub_one_lt hz0
      (hz'.trans_le (min_le_left _ _)))
    refine ⟨hz0, hmem.1, ?_⟩
    have h2 : dist (G z) c < κ / 2 := hmem.2
    rwa [Real.dist_eq] at h2
  have hSAnn : sphere (0 : E) 1 ⊆ Ann := by
    intro x hx
    change |‖x‖ - 1| < δ₁
    rw [mem_sphere_zero_iff_norm.mp hx, sub_self, abs_zero]
    exact hδ₁
  have hpos : ∀ z ∈ Ann, 0 ≤ 1 + κ⁻¹ * (G z - c) := by
    intro z hz
    have h1 := (abs_lt.mp (hAnnp z hz).2.2).1
    have h2 : -(κ / 2) * κ⁻¹ ≤ (G z - c) * κ⁻¹ :=
      mul_le_mul_of_nonneg_right h1.le (inv_pos.mpr hκ).le
    have h3 : -(κ / 2) * κ⁻¹ = -(1 / 2) := by field_simp
    rw [h3] at h2
    linarith [mul_comm (G z - c) κ⁻¹]
  -- 3. the inverse germ `F`
  let φA := DifferentialGeometry.Topology.PartialDiffeomorph.restrict φ Ann hAnn
  have hφAapp : ∀ z, φA z = h z := fun z => congrFun hφh z
  let F := φA.symm
  have hSsrc : ∀ x ∈ sphere (0 : E) 1, x ∈ φA.source :=
    fun x hx => ⟨hφs hx, hSAnn hx⟩
  have hSF : sphere (0 : E) 1 ⊆ F.source := by
    intro x hx
    have h1 := φA.toPartialEquiv.map_source (hSsrc x hx)
    change φA x ∈ φA.target at h1
    rw [hφAapp, hhS x (mem_sphere_zero_iff_norm.mp hx)] at h1
    exact h1
  have hFfix : EqOn F id (sphere (0 : E) 1) := by
    intro x hx
    have h1 := φA.toPartialEquiv.left_inv (hSsrc x hx)
    change φA.symm (φA x) = x at h1
    rw [hφAapp, hhS x (mem_sphere_zero_iff_norm.mp hx)] at h1
    exact h1
  have hFspec : ∀ w ∈ F.source, F w ∈ φ.source ∧ F w ∈ Ann ∧ h (F w) = w := by
    intro w hw
    have h1 := φA.toPartialEquiv.map_target hw
    have h2 := φA.toPartialEquiv.right_inv hw
    change φA (F w) = w at h2
    rw [hφAapp] at h2
    exact ⟨h1.1, h1.2, h2⟩
  have hnorm : ∀ w ∈ F.source, ‖w‖ = 1 + κ⁻¹ * (G (F w) - c) := by
    intro w hw
    obtain ⟨-, hzA, hhz⟩ := hFspec w hw
    have h1 := norm_boundaryPolarMap (κ := κ) (hAnnp _ hzA).1 (hpos _ hzA)
    change ‖h (F w)‖ = _ at h1
    rw [hhz] at h1
    exact h1
  refine ⟨F, hSF, hFfix, ?_, ?_⟩
  · intro w hw
    refine ⟨(hAnnp _ (hFspec w hw).2.1).2.1, ?_⟩
    rw [hnorm w hw]
    field_simp
    ring
  · rintro w ⟨hw1, hws⟩
    obtain ⟨hzφ, hzA, -⟩ := hFspec w hws
    intro hzb
    have hz1 : ‖F w‖ < 1 := mem_ball_zero_iff.mp hzb
    have hw1' : 1 ≤ ‖w‖ := by
      by_contra hcon
      exact hw1 (mem_ball_zero_iff.mpr (lt_of_not_ge hcon))
    obtain ⟨hz0, hzW, -⟩ := hAnnp _ hzA
    have hGz : G (F w) ≤ c := hle _ hzW hz1.le
    have hnw := hnorm w hws
    have hGz' : G (F w) = c := by
      have hk : 0 < κ⁻¹ := inv_pos.mpr hκ
      have h1 : 0 ≤ κ⁻¹ * (G (F w) - c) := by linarith
      have h2 : 0 ≤ G (F w) - c :=
        nonneg_of_mul_nonneg_right (by linarith [mul_comm κ⁻¹ (G (F w) - c)]) hk
      linarith
    set n := ‖F w‖⁻¹ • F w with hndef
    have hn1 : ‖n‖ = 1 := by
      rw [hndef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz0)]
    have hhz' : h (F w) = n := by
      change boundaryPolarMap G c κ (F w) = n
      rw [boundaryPolarMap, hGz', sub_self, mul_zero, add_zero, one_smul]
    have hnφ : n ∈ φ.source := hφs (mem_sphere_zero_iff_norm.mpr hn1)
    have heq : F w = n := by
      apply φ.toPartialEquiv.injOn hzφ hnφ
      rw [hφh, hhz', hhS n hn1]
    have : ‖F w‖ = 1 := by rw [heq, hn1]
    linarith

end Plane

section Disk

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

/-- **The both-sides polar collar.** Let `j` be a chart of a boundaryless manifold `N` whose source
contains the unit sphere, and `T : N → ℝ` smooth on an open `V ⊇ j (sphere)` with `T ∘ j = c` on the
sphere, `T ∘ j ≤ c` on the inner side (in `V`) and `dT ≠ 0` on `j (sphere)`. For every `κ > 0` and
`0 < η < 1` there are `δ ∈ (0, η)`, a diffeomorphism `ψ` of the closed cell and a partial
diffeomorphism `C` from the open annulus `{|‖z‖ - 1| < δ}` into `V` with `T (C z) = c + κ (‖z‖ - 1)`
on BOTH sides of the sphere, `C = j` on the sphere, `C = j ∘ ψ` on the inner side, and `ψ = id` on
the sphere and on `‖z‖ ≤ 1 - η`. -/
theorem exists_diskDiffeomorph_polar_twoSided {m : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) N]
    (j : PartialDiffeomorph (𝓡 (m + 1)) (𝓡 (m + 1)) (EuclideanSpace ℝ (Fin (m + 1))) N ∞)
    (hj : ∀ y : EuclideanSpace ℝ (Fin (m + 1)), ‖y‖ = 1 → y ∈ j.source)
    {T : N → ℝ} {V : Set N} (hV : IsOpen V)
    (hjV : ∀ y : EuclideanSpace ℝ (Fin (m + 1)), ‖y‖ = 1 → j y ∈ V)
    (hT : ContMDiffOn (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ T V) {c : ℝ}
    (hTc : ∀ y : EuclideanSpace ℝ (Fin (m + 1)), ‖y‖ = 1 → T (j y) = c)
    (hTle : ∀ y : EuclideanSpace ℝ (Fin (m + 1)), ‖y‖ ≤ 1 → j y ∈ V → T (j y) ≤ c)
    (hreg : ∀ y : EuclideanSpace ℝ (Fin (m + 1)), ‖y‖ = 1 →
      mfderiv (𝓡 (m + 1)) 𝓘(ℝ, ℝ) T (j y) ≠ 0)
    {κ : ℝ} (hκ : 0 < κ) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < η ∧
      ∃ ψ : ClosedCell (m + 1) ≃ₘ⟮𝓡∂ (m + 1), 𝓡∂ (m + 1)⟯ ClosedCell (m + 1),
      ∃ C : PartialDiffeomorph (𝓡 (m + 1)) (𝓡 (m + 1)) (EuclideanSpace ℝ (Fin (m + 1))) N ∞,
        C.source = {z : EuclideanSpace ℝ (Fin (m + 1)) | |‖z‖ - 1| < δ} ∧
        (∀ z ∈ C.source, C z ∈ V ∧ T (C z) = c + κ * (‖z‖ - 1)) ∧
        (∀ z : EuclideanSpace ℝ (Fin (m + 1)), ‖z‖ = 1 → C z = j z) ∧
        (∀ z : ClosedCell (m + 1), 1 - δ < ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ →
          C (z : EuclideanSpace ℝ (Fin (m + 1))) =
            j ((ψ z : ClosedCell (m + 1)) : EuclideanSpace ℝ (Fin (m + 1)))) ∧
        (∀ z : ClosedCell (m + 1), ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 → ψ z = z) ∧
        (∀ z : ClosedCell (m + 1), ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ ≤ 1 - η →
          ψ z = z) := by
  -- 1. `G = T ∘ j` on `W = j.source ∩ j⁻¹ V`
  set W : Set (EuclideanSpace ℝ (Fin (m + 1))) := j.source ∩ j ⁻¹' V with hWdef
  have hW : IsOpen W := j.contMDiffOn.continuousOn.isOpen_inter_preimage j.open_source hV
  have hSW : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ⊆ W := fun y hy =>
    ⟨hj y (mem_sphere_zero_iff_norm.mp hy), hjV y (mem_sphere_zero_iff_norm.mp hy)⟩
  have hu : ContMDiffOn (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ (T ∘ j) W :=
    hT.comp (j.contMDiffOn.mono inter_subset_left) (fun y hy => hy.2)
  have hud : ContDiffOn ℝ ∞ (T ∘ j) W := contMDiffOn_iff_contDiffOn.mp hu
  have hureg : ∀ y : EuclideanSpace ℝ (Fin (m + 1)), ‖y‖ = 1 → fderiv ℝ (T ∘ j) y ≠ 0 := by
    intro y hy h0
    have hys := hj y hy
    have hTd : MDifferentiableAt (𝓡 (m + 1)) 𝓘(ℝ, ℝ) T (j y) :=
      ((hT _ (hjV y hy)).contMDiffAt (hV.mem_nhds (hjV y hy))).mdifferentiableAt (by simp)
    have hjd : MDifferentiableAt (𝓡 (m + 1)) (𝓡 (m + 1)) j y := j.mdifferentiableAt (by simp) hys
    have h0' : mfderiv (𝓡 (m + 1)) 𝓘(ℝ, ℝ) (T ∘ j) y = 0 := by
      rw [mfderiv_eq_fderiv]
      exact h0
    rw [mfderiv_comp y hTd hjd] at h0'
    obtain ⟨e, he⟩ :=
      (PartialDiffeomorph.isLocalDiffeomorphAt _ _ _ j hys).isInvertible_mfderiv (by simp)
    apply hreg y hy
    ext v
    have h1 := congrArg (fun L => L (e.symm v)) h0'
    simp only [ContinuousLinearMap.comp_apply, zero_apply] at h1
    rw [← he, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] at h1
    rw [h1, zero_apply]
  -- 2. the two-sided germ
  obtain ⟨F, hSF, hFfix, hFval, hFmap⟩ := exists_planePolarGerm hW hSW hud hTc
    (fun y hy hy1 => hTle y hy1 hy.2) hureg hκ
  -- 3. the ambient isotopy and the cell diffeomorphism
  have hOo : IsOpen {x : EuclideanSpace ℝ (Fin (m + 1)) | 1 - η < ‖x‖} :=
    isOpen_lt continuous_const continuous_norm
  have hSO : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ⊆
      {x : EuclideanSpace ℝ (Fin (m + 1)) | 1 - η < ‖x‖} := fun x hx => by
    change 1 - η < ‖x‖
    rw [mem_sphere_zero_iff_norm.mp hx]
    linarith
  obtain ⟨V', hV'o, hSV', hV'F, Φ, -, -, -, hΦ1, hfixΦ, hball, L, -, hLO, hLid⟩ :=
    F.exists_contDiff_compact_isotopy_eqOn_sphere_neighborhood_of_mapsTo_compl_ball one_pos hSF
      hFfix hFmap hOo hSO
  obtain ⟨δ₂, hδ₂, hthickV⟩ :=
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1).exists_thickening_subset_open hV'o
      hSV'
  let ψ := closedCellDiffeomorph (m := m) (Φ 1) (hball 1 ⟨zero_le_one, le_rfl⟩)
  set δ : ℝ := min δ₂ (η / 2) with hδdef
  have hδ0 : 0 < δ := lt_min hδ₂ (by positivity)
  have hδη : δ < η := (min_le_right _ _).trans_lt (by linarith)
  let A : Set (EuclideanSpace ℝ (Fin (m + 1))) := {z | |‖z‖ - 1| < δ}
  have hAo : IsOpen A := isOpen_lt ((continuous_norm.sub continuous_const).abs) continuous_const
  have hAV' : ∀ z ∈ A, z ∈ V' := by
    intro z hz
    have hz' : |‖z‖ - 1| < δ := hz
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hz'
      norm_num at hz'
      linarith [min_le_right δ₂ (η / 2)]
    exact hthickV (mem_thickening_sphere_of_abs_norm_sub_one_lt hz0
      (hz'.trans_le (min_le_left _ _)))
  -- 4. the collar `C = j ∘ F` on the annulus
  let C := (DifferentialGeometry.Topology.PartialDiffeomorph.restrict F A hAo).trans j
  have hCapp : ∀ z, C z = j (F z) := fun _ => rfl
  have hCsrc : C.source = A := by
    ext z
    change z ∈ (F.source ∩ A) ∩ F ⁻¹' j.source ↔ z ∈ A
    constructor
    · intro hz
      exact hz.1.2
    · intro hz
      exact ⟨⟨hV'F (hAV' z hz), hz⟩, (hFval z (hV'F (hAV' z hz))).1.1⟩
  refine ⟨δ, hδ0, hδη, ψ, C, hCsrc, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rw [hCsrc] at hz
    obtain ⟨hFW, hFT⟩ := hFval z (hV'F (hAV' z hz))
    exact ⟨hFW.2, hFT⟩
  · intro z hz
    rw [hCapp, hFfix (mem_sphere_zero_iff_norm.mpr hz)]
    rfl
  · intro z hz
    have hz1 : ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ ≤ 1 := z.2
    have hzA : (z : EuclideanSpace ℝ (Fin (m + 1))) ∈ A := by
      change |‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ - 1| < δ
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    have hψz : ((ψ z : ClosedCell (m + 1)) : EuclideanSpace ℝ (Fin (m + 1))) = F z :=
      hΦ1 (hAV' _ hzA)
    rw [hCapp, hψz]
  · intro z hz
    apply Subtype.ext
    exact (hfixΦ 1).1 (mem_sphere_zero_iff_norm.mpr hz)
  · intro z hz
    apply Subtype.ext
    have hzL : (z : EuclideanSpace ℝ (Fin (m + 1))) ∈ Lᶜ := fun hL => by
      have := hLO hL
      change 1 - η < ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ at this
      linarith
    exact (hLid 1).1 hzL

/-- **Disk-model form (consumer).** A fibre `S` with a disk model `D₀ : ClosedCell (m + 1) ≃ₘ S`
and a map `ι : S → N` with `ι ∘ D₀ = j` on the cell (`j` the chart of `N` extending the disk model
across the rim): ONE construction gives the re-modelled disk model `D` (equal to `D₀` on the rim and
on `‖z‖ ≤ 1 - η`) and the both-sides polar collar `C` of `exists_diskDiffeomorph_polar_twoSided`,
with `ι ∘ D = C` on the inner side `1 - δ < ‖z‖` — the handle side and the rim side share the
germ. -/
theorem exists_diskModel_polar_twoSided {m : ℕ} {N S : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) N] [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace (m + 1)) S]
    (D₀ : ClosedCell (m + 1) ≃ₘ⟮𝓡∂ (m + 1), 𝓡∂ (m + 1)⟯ S) (ι : S → N)
    (j : PartialDiffeomorph (𝓡 (m + 1)) (𝓡 (m + 1)) (EuclideanSpace ℝ (Fin (m + 1))) N ∞)
    (hj : ∀ y : EuclideanSpace ℝ (Fin (m + 1)), ‖y‖ = 1 → y ∈ j.source)
    (hjD : ∀ z : ClosedCell (m + 1), j (z : EuclideanSpace ℝ (Fin (m + 1))) = ι (D₀ z))
    {T : N → ℝ} {V : Set N} (hV : IsOpen V)
    (hjV : ∀ y : EuclideanSpace ℝ (Fin (m + 1)), ‖y‖ = 1 → j y ∈ V)
    (hT : ContMDiffOn (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ T V) {c : ℝ}
    (hTc : ∀ y : EuclideanSpace ℝ (Fin (m + 1)), ‖y‖ = 1 → T (j y) = c)
    (hTle : ∀ y : EuclideanSpace ℝ (Fin (m + 1)), ‖y‖ ≤ 1 → j y ∈ V → T (j y) ≤ c)
    (hreg : ∀ y : EuclideanSpace ℝ (Fin (m + 1)), ‖y‖ = 1 →
      mfderiv (𝓡 (m + 1)) 𝓘(ℝ, ℝ) T (j y) ≠ 0)
    {κ : ℝ} (hκ : 0 < κ) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < η ∧
      ∃ D : ClosedCell (m + 1) ≃ₘ⟮𝓡∂ (m + 1), 𝓡∂ (m + 1)⟯ S,
      ∃ C : PartialDiffeomorph (𝓡 (m + 1)) (𝓡 (m + 1)) (EuclideanSpace ℝ (Fin (m + 1))) N ∞,
        C.source = {z : EuclideanSpace ℝ (Fin (m + 1)) | |‖z‖ - 1| < δ} ∧
        (∀ z ∈ C.source, C z ∈ V ∧ T (C z) = c + κ * (‖z‖ - 1)) ∧
        (∀ z : EuclideanSpace ℝ (Fin (m + 1)), ‖z‖ = 1 → C z = j z) ∧
        (∀ z : ClosedCell (m + 1), 1 - δ < ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ →
          ι (D z) = C (z : EuclideanSpace ℝ (Fin (m + 1)))) ∧
        (∀ z : ClosedCell (m + 1), ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 → D z = D₀ z) ∧
        (∀ z : ClosedCell (m + 1), ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ ≤ 1 - η →
          D z = D₀ z) := by
  obtain ⟨δ, hδ0, hδη, ψ, C, hCs, hCT, hCS, hCψ, hψS, hψη⟩ :=
    exists_diskDiffeomorph_polar_twoSided j hj hV hjV hT hTc hTle hreg hκ hη0 hη1
  refine ⟨δ, hδ0, hδη, ψ.trans D₀, C, hCs, hCT, hCS, ?_, ?_, ?_⟩
  · intro z hz
    change ι (D₀ (ψ z)) = C (z : EuclideanSpace ℝ (Fin (m + 1)))
    rw [← hjD, hCψ z hz]
  · intro z hz
    change D₀ (ψ z) = D₀ z
    rw [hψS z hz]
  · intro z hz
    change D₀ (ψ z) = D₀ z
    rw [hψη z hz]

/-- **Compiled inhabitant (consumer): the round sphere.** For `N = ℝᵐ⁺¹`, `j = id` and
`T = ‖·‖²` (`c = 1`) all hypotheses of `exists_diskDiffeomorph_polar_twoSided` hold, so there is a
both-sides collar `C` with `‖C z‖² = 1 + κ (‖z‖ - 1)` on the annulus, `C = id` on the sphere and
`C = ψ` on the inner side. -/
theorem exists_polarCollar_twoSided_normSq (m : ℕ) {κ : ℝ} (hκ : 0 < κ) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η < 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < η ∧
      ∃ ψ : ClosedCell (m + 1) ≃ₘ⟮𝓡∂ (m + 1), 𝓡∂ (m + 1)⟯ ClosedCell (m + 1),
      ∃ C : PartialDiffeomorph (𝓡 (m + 1)) (𝓡 (m + 1)) (EuclideanSpace ℝ (Fin (m + 1)))
          (EuclideanSpace ℝ (Fin (m + 1))) ∞,
        C.source = {z : EuclideanSpace ℝ (Fin (m + 1)) | |‖z‖ - 1| < δ} ∧
        (∀ z ∈ C.source, ‖C z‖ ^ 2 = 1 + κ * (‖z‖ - 1)) ∧
        (∀ z : EuclideanSpace ℝ (Fin (m + 1)), ‖z‖ = 1 → C z = z) ∧
        (∀ z : ClosedCell (m + 1), 1 - δ < ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ →
          C (z : EuclideanSpace ℝ (Fin (m + 1))) =
            ((ψ z : ClosedCell (m + 1)) : EuclideanSpace ℝ (Fin (m + 1)))) ∧
        (∀ z : ClosedCell (m + 1), ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 → ψ z = z) ∧
        (∀ z : ClosedCell (m + 1), ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ ≤ 1 - η →
          ψ z = z) := by
  let j := (Diffeomorph.refl (𝓡 (m + 1)) (EuclideanSpace ℝ (Fin (m + 1))) ∞).toPartialDiffeomorph
  have hjapp : ∀ y : EuclideanSpace ℝ (Fin (m + 1)), j y = y := fun _ => rfl
  have hreg : ∀ y : EuclideanSpace ℝ (Fin (m + 1)), ‖y‖ = 1 →
      mfderiv (𝓡 (m + 1)) 𝓘(ℝ, ℝ) (fun x : EuclideanSpace ℝ (Fin (m + 1)) => ‖x‖ ^ 2) (j y) ≠
        0 := by
    intro y hy h0
    rw [hjapp] at h0
    have h2 : fderiv ℝ (fun x : EuclideanSpace ℝ (Fin (m + 1)) => ‖x‖ ^ 2) y = 0 := by
      rw [mfderiv_eq_fderiv] at h0
      exact h0
    rw [fderiv_norm_sq_apply] at h2
    have h1 := DFunLike.congr_fun h2 y
    simp [hy] at h1
  obtain ⟨δ, hδ0, hδη, ψ, C, hCs, hCT, hCS, hCψ, hψS, hψη⟩ :=
    exists_diskDiffeomorph_polar_twoSided j (fun y _ => mem_univ y) isOpen_univ
      (fun y _ => mem_univ (j y)) (contDiff_norm_sq ℝ).contMDiff.contMDiffOn (c := 1)
      (fun y hy => by rw [hjapp, hy, one_pow])
      (fun y hy _ => by rw [hjapp]; exact pow_le_one₀ (norm_nonneg y) hy) hreg hκ hη0 hη1
  exact ⟨δ, hδ0, hδη, ψ, C, hCs, fun z hz => (hCT z hz).2, hCS, hCψ, hψS, hψη⟩

end Disk

end DifferentialGeometry.Topology.Manifold
