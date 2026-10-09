import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1WSideRadial
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1WSideBallGerm

/-!
# Chapter-14 assembly, item L1, group G3b, step T3: the balls

`PieceEmbedding.exists_ballReparam_eq_necks` (sub-statement T3′ of lane ASM-L1b): a ball with two
necks (ball side `{τ ≤ 0}`, disjoint targets, opposite chart-free relative signs `ballNeckDetAmb`) is
reparametrized, after compressing the ball sides of both necks by one profile `compress l a`, to
agree with the compressed necks on the two cap regions, with the same image.

Route: the germs `F_b = φ_b⁻¹ ∘ capMap b` (`exists_ballGerm`: the neck read in the ball, extended
across the sphere) satisfy the hypotheses of the two-disk normalization G2
(`exists_closedCell_diffeomorph_eqOn_two_boundary_disks`) with the stereographic disk charts from
the opposite poles; G2 gives `D` with `D = F_b` near the two caps; the radial compression `T`
(`radialCompressDiffeo`) moves the fixed-depth cap regions into that neighbourhood, and
`β = ballCell ∘ D ∘ T`. The sign hypothesis of G2 is the product of the two `ballNeckDetAmb`
times `-det(J⁻¹ ∘ d capMap false)²` (the cap `true` is the mirror image of the cap `false`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology InnerProductSpace

universe u

namespace GC.GraphManifold.Assembly

local instance ballCharts_ASML1bT : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmooth_ASML1bT : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

local instance fact_finrank_three_ASML1bT :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

/-! ## Stereographic disks and the caps -/

/-- The height of the inverse stereographic projection from the north pole, against the south pole. -/
theorem inner_stereoNorth_symm_south (x : EuclideanSpace ℝ (Fin 2)) :
    ⟪((DifferentialGeometry.Topology.Handle.stereoChart northPole).symm x :
        EuclideanSpace ℝ (Fin 3)),
      ((southPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : EuclideanSpace ℝ (Fin 3))⟫_ℝ =
      (4 - ‖x‖ ^ 2) / (‖x‖ ^ 2 + 4) := by
  rw [inner_south_eq_neg_inner_north, DifferentialGeometry.Topology.Handle.inner_stereoChart_symm]
  have hpos : (0 : ℝ) < ‖x‖ ^ 2 + 4 := by positivity
  field_simp
  ring

theorem inner_stereoSouth_symm_south (x : EuclideanSpace ℝ (Fin 2)) :
    ⟪((DifferentialGeometry.Topology.Handle.stereoChart southPole).symm x :
        EuclideanSpace ℝ (Fin 3)),
      ((southPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : EuclideanSpace ℝ (Fin 3))⟫_ℝ =
      (‖x‖ ^ 2 - 4) / (‖x‖ ^ 2 + 4) :=
  DifferentialGeometry.Topology.Handle.inner_stereoChart_symm southPole x

theorem stereoHeight_lt_iff {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (4 - t ^ 2) / (t ^ 2 + 4) < (4 - s ^ 2) / (s ^ 2 + 4) ↔ s < t := by
  have h1 : (0 : ℝ) < t ^ 2 + 4 := by positivity
  have h2 : (0 : ℝ) < s ^ 2 + 4 := by positivity
  rw [div_lt_div_iff₀ h1 h2]
  constructor
  · intro h
    by_contra hst
    have hst' : t ≤ s := not_lt.mp hst
    nlinarith [mul_le_mul hst' hst' ht hs]
  · intro h
    nlinarith [mul_lt_mul'' h h hs hs]

/-- The cap chart `false` of an inverse stereographic point from the north pole. -/
theorem capMap_false_stereoNorth_symm (x : EuclideanSpace ℝ (Fin 2)) :
    capMap false ((DifferentialGeometry.Topology.Handle.stereoChart northPole).symm x :
      EuclideanSpace ℝ (Fin 3)) = (x, 0) := by
  set θ := (DifferentialGeometry.Topology.Handle.stereoChart northPole).symm x
  have hθ0 : (θ : EuclideanSpace ℝ (Fin 3)) ≠ 0 := ne_zero_of_mem_unit_sphere θ
  have hdir : DifferentialGeometry.Topology.Manifold.sphereDirection southPole
      (θ : EuclideanSpace ℝ (Fin 3)) = θ := by
    apply Subtype.ext
    rw [DifferentialGeometry.Topology.Manifold.coe_sphereDirection _ hθ0, norm_eq_of_mem_sphere,
      inv_one, one_smul]
  have hr : DifferentialGeometry.Topology.Handle.stereoChart northPole θ = x :=
    (DifferentialGeometry.Topology.Handle.stereoChart northPole).right_inv
      (by rw [DifferentialGeometry.Topology.Handle.stereoChart_target]; exact mem_univ _)
  change southCapMap (θ : EuclideanSpace ℝ (Fin 3)) = (x, 0)
  rw [southCapMap_apply, hdir, norm_eq_of_mem_sphere, sub_self]
  erw [hr]

theorem mem_capSource_false_stereoNorth_symm {x : EuclideanSpace ℝ (Fin 2)} (hx : ‖x‖ < 2) :
    ((DifferentialGeometry.Topology.Handle.stereoChart northPole).symm x :
      EuclideanSpace ℝ (Fin 3)) ∈ capSource false := by
  change 0 < ⟪_, ((southPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    EuclideanSpace ℝ (Fin 3))⟫_ℝ
  rw [inner_stereoNorth_symm_south]
  have h1 : (0 : ℝ) < ‖x‖ ^ 2 + 4 := by positivity
  have h2 : ‖x‖ ^ 2 < 4 := by nlinarith [norm_nonneg x]
  exact div_pos (by linarith) h1

theorem stereoHeight_injective {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (h : (s ^ 2 - 4) / (s ^ 2 + 4) = (t ^ 2 - 4) / (t ^ 2 + 4)) : s = t := by
  have h1 : (0 : ℝ) < t ^ 2 + 4 := by positivity
  have h2 : (0 : ℝ) < s ^ 2 + 4 := by positivity
  rw [div_eq_div_iff h2.ne' h1.ne'] at h
  have hsq : s ^ 2 = t ^ 2 := by nlinarith
  nlinarith [sq_nonneg (s - t), sq_nonneg (s + t)]

/-- The north pole, as the inverse stereographic image of `0` from the south pole. -/
theorem stereoSouth_symm_zero :
    (DifferentialGeometry.Topology.Handle.stereoChart southPole).symm 0 = northPole := by
  apply Subtype.ext
  rw [DifferentialGeometry.Topology.Handle.stereoChart_symm_apply, stereographic'_symm_apply]
  simp only [map_zero, ZeroMemClass.coe_zero, norm_zero, smul_zero, zero_add]
  rw [southPole_val, northPole_val]
  norm_num
  rw [smul_smul]
  norm_num

theorem stereoNorth_symm_zero :
    (DifferentialGeometry.Topology.Handle.stereoChart northPole).symm 0 = southPole := by
  apply Subtype.ext
  rw [DifferentialGeometry.Topology.Handle.stereoChart_symm_apply, stereographic'_symm_apply]
  simp only [map_zero, ZeroMemClass.coe_zero, norm_zero, smul_zero, zero_add]
  rw [southPole_val, northPole_val]
  norm_num
  rw [smul_smul]
  norm_num

theorem mem_capSource_true_stereoSouth_symm {x : EuclideanSpace ℝ (Fin 2)} (hx : ‖x‖ < 2) :
    ((DifferentialGeometry.Topology.Handle.stereoChart southPole).symm x :
      EuclideanSpace ℝ (Fin 3)) ∈ capSource true := by
  change 0 < ⟪_, ((northPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    EuclideanSpace ℝ (Fin 3))⟫_ℝ
  have h := inner_stereoSouth_symm_south x
  rw [inner_south_eq_neg_inner_north] at h
  have h1 : (0 : ℝ) < ‖x‖ ^ 2 + 4 := by positivity
  have h2 : ‖x‖ ^ 2 < 4 := by nlinarith [norm_nonneg x]
  have h3 : (‖x‖ ^ 2 - 4) / (‖x‖ ^ 2 + 4) < 0 := div_neg_of_neg_of_pos (by linarith) h1
  linarith

/-- The cap chart `true` of an inverse stereographic point from the south pole lies on the sphere
level and has the same stereographic radius. -/
theorem capMap_true_stereoSouth_symm (x : EuclideanSpace ℝ (Fin 2)) :
    (capMap true ((DifferentialGeometry.Topology.Handle.stereoChart southPole).symm x :
      EuclideanSpace ℝ (Fin 3))).2 = 0 ∧
    ‖(capMap true ((DifferentialGeometry.Topology.Handle.stereoChart southPole).symm x :
      EuclideanSpace ℝ (Fin 3))).1‖ = ‖x‖ := by
  set θ := (DifferentialGeometry.Topology.Handle.stereoChart southPole).symm x
  have hθs : θ ≠ southPole := by
    have h := (DifferentialGeometry.Topology.Handle.stereoChart southPole).map_target
      (x := x) (by rw [DifferentialGeometry.Topology.Handle.stereoChart_target]; exact mem_univ _)
    rw [DifferentialGeometry.Topology.Handle.stereoChart_source] at h
    exact h
  let ρθ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    ⟨reflectThree (θ : EuclideanSpace ℝ (Fin 3)), by simp⟩
  have hρ0 : reflectThree (θ : EuclideanSpace ℝ (Fin 3)) ≠ 0 := ne_zero_of_mem_unit_sphere ρθ
  have hdir : DifferentialGeometry.Topology.Manifold.sphereDirection southPole
      (reflectThree (θ : EuclideanSpace ℝ (Fin 3))) = ρθ := by
    apply Subtype.ext
    rw [DifferentialGeometry.Topology.Manifold.coe_sphereDirection _ hρ0, norm_reflectThree,
      norm_eq_of_mem_sphere, inv_one, one_smul]
  have hρn : ρθ ≠ northPole := by
    intro h
    apply hθs
    apply Subtype.ext
    have h' := congrArg (fun w : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
      reflectThree (w : EuclideanSpace ℝ (Fin 3))) h
    simp only [ρθ, reflectThree_reflectThree] at h'
    rw [h', reflectThree_north]
  refine ⟨?_, ?_⟩
  · change ‖reflectThree (θ : EuclideanSpace ℝ (Fin 3))‖ - 1 = 0
    rw [norm_reflectThree, norm_eq_of_mem_sphere, sub_self]
  · change ‖DifferentialGeometry.Topology.Handle.stereoChart northPole
      (DifferentialGeometry.Topology.Manifold.sphereDirection southPole
        (reflectThree (θ : EuclideanSpace ℝ (Fin 3))))‖ = ‖x‖
    rw [hdir]
    set y := DifferentialGeometry.Topology.Handle.stereoChart northPole ρθ
    have hl : (DifferentialGeometry.Topology.Handle.stereoChart northPole).symm y = ρθ :=
      (DifferentialGeometry.Topology.Handle.stereoChart northPole).left_inv
        (by rw [DifferentialGeometry.Topology.Handle.stereoChart_source]; exact hρn)
    have h1 := DifferentialGeometry.Topology.Handle.inner_stereoChart_symm northPole y
    rw [hl] at h1
    have h2 := inner_stereoSouth_symm_south x
    have h3 : ⟪((ρθ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : EuclideanSpace ℝ (Fin 3)),
        ((northPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : EuclideanSpace ℝ (Fin 3))⟫_ℝ =
        ⟪(θ : EuclideanSpace ℝ (Fin 3)),
          ((southPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : EuclideanSpace ℝ (Fin 3))⟫_ℝ := by
      change ⟪reflectThree (θ : EuclideanSpace ℝ (Fin 3)), _⟫_ℝ = _
      rw [inner_reflectThree, reflectThree_north]
    rw [h3, h2] at h1
    exact stereoHeight_injective (norm_nonneg _) (norm_nonneg _) h1.symm

/-! ## Determinants -/

theorem det_reflectThree :
    LinearMap.det (reflectThree.toLinearEquiv : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin 3)) = -1 := by
  have h := Submodule.det_reflection (ℝ ∙ (EuclideanSpace.single 2 1 : EuclideanSpace ℝ (Fin 3)))ᗮ
  rw [Submodule.orthogonal_orthogonal, finrank_span_singleton (by simp), pow_one] at h
  exact h

theorem hasFDerivAt_capMap (b : Bool) {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ capSource b) :
    HasFDerivAt (capMap b) (fderiv ℝ (capMap b) x) x :=
  (((contDiffOn_capMap b).contDiffAt ((isOpen_capSource b).mem_nhds hx)).differentiableAt
    (by simp)).hasFDerivAt

theorem southPole_mem_capSource : ((southPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    EuclideanSpace ℝ (Fin 3)) ∈ capSource false := by
  change 0 < ⟪_, ((southPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    EuclideanSpace ℝ (Fin 3))⟫_ℝ
  rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere]
  norm_num

theorem northPole_mem_capSource : ((northPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    EuclideanSpace ℝ (Fin 3)) ∈ capSource true := by
  change 0 < ⟪_, ((northPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    EuclideanSpace ℝ (Fin 3))⟫_ℝ
  rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere]
  norm_num

/-- The derivative of the cap chart `true` at the north pole is that of the cap chart `false` at
the south pole after the reflection. -/
theorem fderiv_capMap_true_north :
    fderiv ℝ (capMap true) ((northPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3)) =
    (fderiv ℝ (capMap false) ((southPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3))).comp reflectThree.toContinuousLinearEquiv.toContinuousLinearMap := by
  have h1 := hasFDerivAt_capMap false southPole_mem_capSource
  have h2 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 3) => reflectThree x)
      reflectThree.toContinuousLinearEquiv.toContinuousLinearMap
      ((northPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : EuclideanSpace ℝ (Fin 3)) :=
    reflectThree.toContinuousLinearEquiv.hasFDerivAt
  rw [← reflectThree_north] at h1
  have h := (h1.comp _ h2).fderiv
  rw [reflectThree_north] at h
  rw [capMap_true_eq_comp]
  exact h

/-- The derivative of the cap chart `false` at the south pole is invertible. -/
theorem bijective_fderiv_capMap_south :
    Bijective (fderiv ℝ (capMap false) ((southPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3))) := by
  set p := ((southPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : EuclideanSpace ℝ (Fin 3))
  have h1 := hasFDerivAt_capMap false southPole_mem_capSource
  have h2 : HasFDerivAt (capInv false) (fderiv ℝ (capInv false) (capMap false p)) (capMap false p) :=
    ((contDiff_capInv false).differentiable (by simp) _).hasFDerivAt
  have h3 := h2.comp p h1
  have hev : (capInv false ∘ capMap false) =ᶠ[𝓝 p] id := by
    filter_upwards [(isOpen_capSource false).mem_nhds southPole_mem_capSource] with x hx
    exact capInv_capMap hx
  have h4 := (h3.congr_of_eventuallyEq hev.symm).unique (hasFDerivAt_id p)
  have hinj : Injective (fderiv ℝ (capMap false) p) := by
    intro v w hvw
    have := congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) => L v) h4
    have h' := congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) => L w) h4
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this h'
    rw [← this, ← h', hvw]
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) := by simp
  exact ⟨hinj, ((fderiv ℝ (capMap false) p).toLinearMap.injective_iff_surjective_of_finrank_eq_finrank
    hdim).mp hinj⟩

section GermDet

variable {W : CompactCarrier.{u}} (B : PieceEmbedding W) (e : B.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3)
  (N : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
    (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞)

theorem mfderiv_symm_comp_mfderiv_e (p : B.Piece) (w : TangentSpace (𝓡∂ 3) p) :
    mfderiv (𝓡∂ 3) (𝓡∂ 3) e.symm (e p) (mfderiv (𝓡∂ 3) (𝓡∂ 3) e p w) = w := by
  have h : e.symm ∘ e = id := funext fun y => e.symm_apply_apply y
  have hc := mfderiv_comp p (e.symm.contMDiff.mdifferentiable (by simp) (e p))
    (e.contMDiff.mdifferentiable (by simp) p)
  rw [h, mfderiv_id] at hc
  exact (congrArg (fun L => L w) hc).symm

theorem mfderiv_neckSymm_comp {q : EuclideanSpace ℝ (Fin 2) × ℝ} (hq : q ∈ N.source)
    (v : EuclideanSpace ℝ (Fin 2) × ℝ) :
    mfderiv W.model 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) N.symm (N q)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model N q v) = v := by
  have hc := mfderiv_comp q (N.symm.mdifferentiableAt (by simp) (N.map_source hq))
    (N.mdifferentiableAt (by simp) hq)
  have hev : (N.symm ∘ N) =ᶠ[𝓝 q] id := by
    filter_upwards [N.open_source.mem_nhds hq] with x hx
    exact N.left_inv hx
  rw [hev.mfderiv_eq, mfderiv_id] at hc
  exact (congrArg (fun L => L v) hc).symm

/-- **The derivative of the ball germ.** If `φ` is the neck read in the ball near `q`
(`exists_ballGerm`), the determinant of `d(φ⁻¹)_q ∘ D` is `ballNeckDetAmb` times
`det (J⁻¹ ∘ D)`. -/
theorem det_fderiv_germSymm_comp
    (φ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ)
      (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 2) × ℝ) ∞)
    {q : EuclideanSpace ℝ (Fin 2) × ℝ} (hqt : q ∈ φ.target) (hqN : q ∈ N.source)
    {y : ClosedCell 3} (hy : φ.symm q = y.val)
    (hrel : (fderiv ℝ φ y.val).comp (mfderiv (𝓡∂ 3) (𝓡 3)
        (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) y) =
      (mfderiv W.model 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) N.symm (N q)).comp
        (mfderiv (𝓡∂ 3) W.model (ballCell B e) y))
    (D : EuclideanSpace ℝ (Fin 3) →L[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ)) :
    LinearMap.det (((fderiv ℝ φ.symm q).comp D : EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) =
      ballNeckDetAmb B e y (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model N q) *
        LinearMap.det (neckSpaceEquiv.symm.toLinearMap ∘ₗ D.toLinearMap) := by
  set M := fderiv ℝ φ.symm q
  set A := fderiv ℝ φ y.val
  have hys : (y : EuclideanSpace ℝ (Fin 3)) ∈ φ.source := by
    rw [← hy]
    exact φ.map_target hqt
  have hM : HasFDerivAt φ.symm M q :=
    ((φ.symm.contMDiffOn_toFun.contDiffOn.contDiffAt (φ.open_target.mem_nhds hqt)).differentiableAt
      (by simp)).hasFDerivAt
  have hA : HasFDerivAt φ A y.val :=
    ((φ.contMDiffOn_toFun.contDiffOn.contDiffAt (φ.open_source.mem_nhds hys)).differentiableAt
      (by simp)).hasFDerivAt
  rw [← hy] at hA
  have hAM : A.comp M = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) := by
    have hev : (φ ∘ φ.symm) =ᶠ[𝓝 q] id := by
      filter_upwards [φ.open_target.mem_nhds hqt] with x hx
      exact φ.right_inv hx
    exact ((hA.comp q hM).congr_of_eventuallyEq hev.symm).unique (hasFDerivAt_id q)
  -- the explicit inverse
  let DB := LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) W.model B.map (e.symm y)).toLinearMap
    (B.mfderiv_bijective (e.symm y))
  let L₀ : (EuclideanSpace ℝ (Fin 2) × ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) y).toLinearMap ∘ₗ
      (mfderiv (𝓡∂ 3) (𝓡∂ 3) e (e.symm y)).toLinearMap ∘ₗ DB.symm.toLinearMap ∘ₗ
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model N q).toLinearMap
  have hAL : ∀ v, A (L₀ v) = v := by
    intro v
    set u := (mfderiv (𝓡∂ 3) (𝓡∂ 3) e (e.symm y))
      (DB.symm ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model N q) v))
    have h1 : A ((mfderiv (𝓡∂ 3) (𝓡 3)
        (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) y) u) =
        (mfderiv W.model 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) N.symm (N q))
          ((mfderiv (𝓡∂ 3) W.model (ballCell B e) y) u) :=
      congrArg (fun L => L u) hrel
    have h4 : (mfderiv (𝓡∂ 3) W.model (ballCell B e) y) u =
        (mfderiv (𝓡∂ 3) W.model B.map (e.symm y)) ((mfderiv (𝓡∂ 3) (𝓡∂ 3) e.symm y) u) := by
      rw [mfderiv_ballCell]
      rfl
    have h2 : (mfderiv (𝓡∂ 3) (𝓡∂ 3) e.symm y) u =
        DB.symm ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model N q) v) := by
      have h := mfderiv_symm_comp_mfderiv_e B e (e.symm y)
        (DB.symm ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model N q) v))
      rw [e.apply_symm_apply] at h
      exact h
    have h3 : (mfderiv (𝓡∂ 3) W.model B.map (e.symm y))
        (DB.symm ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model N q) v)) =
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model N q) v :=
      DB.apply_symm_apply _
    change A ((mfderiv (𝓡∂ 3) (𝓡 3)
        (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) y) u) = v
    rw [h1, h4, h2, h3]
    exact mfderiv_neckSymm_comp N hqN v
  have hAsurj : Surjective A := fun v => ⟨M v, by
    simpa using congrArg (fun L => L v) hAM⟩
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) := by simp
  have hAinj : Injective A :=
    (A.toLinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hAsurj
  have hML : (M : (EuclideanSpace ℝ (Fin 2) × ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) = L₀ := by
    apply LinearMap.ext
    intro v
    apply hAinj
    rw [hAL v]
    simpa using congrArg (fun L => L v) hAM
  have hfac : ((M.comp D : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
      EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) =
      (L₀ ∘ₗ neckSpaceEquiv.toLinearMap) ∘ₗ (neckSpaceEquiv.symm.toLinearMap ∘ₗ D.toLinearMap) := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rw [← hML]
    rfl
  rw [hfac, LinearMap.det_comp]
  rfl

end GermDet

/-! ## Geometry of the cap regions -/

theorem mem_thickening_ballSideBox {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : ‖x‖ ≤ 1 + 2 * ε + δ / 2) :
    (x, (0 : ℝ)) ∈ thickening δ (closedNeckDomain ε ∩ {q | q.2 ≤ 0}) := by
  rw [mem_thickening_iff]
  by_cases hx1 : ‖x‖ ≤ 1 + 2 * ε
  · exact ⟨(x, 0), ⟨⟨hx1, by simp only [abs_zero, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]; positivity⟩, show (0 : ℝ) ≤ 0 from le_rfl⟩, by simp [hδ]⟩
  · have hn : 0 < ‖x‖ := by linarith
    set c := (1 + 2 * ε) / ‖x‖
    have hc0 : 0 ≤ c := div_nonneg (by linarith) hn.le
    have hcx : ‖c • x‖ = 1 + 2 * ε := by
      rw [norm_smul, Real.norm_of_nonneg hc0, div_mul_cancel₀ _ hn.ne']
    refine ⟨(c • x, 0), ⟨⟨hcx.le, by simp only [abs_zero, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]; positivity⟩, show (0 : ℝ) ≤ 0 from le_rfl⟩, ?_⟩
    rw [Prod.dist_eq, dist_self, dist_eq_norm]
    have h1 : x - c • x = (1 - c) • x := by rw [sub_smul, one_smul]
    have hc1 : c ≤ 1 := (div_le_one hn).mpr (by linarith)
    rw [h1, norm_smul, Real.norm_of_nonneg (by linarith), sub_mul, one_mul,
      div_mul_cancel₀ _ hn.ne']
    exact max_lt (by linarith) hδ

/-- A point of the cap region `b` is a positive multiple of a unit vector whose height against the
pole `b` is the stereographic height of its cap coordinate. -/
theorem exists_dir_of_mem_neckCapRegion {ε : ℝ} {b : Bool} {x : ClosedCell 3}
    (hx : x ∈ neckCapRegion ε b) :
    ∃ θ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      (x : EuclideanSpace ℝ (Fin 3)) = ‖(x : EuclideanSpace ℝ (Fin 3))‖ • (θ : EuclideanSpace ℝ (Fin 3)) ∧
      ⟪(θ : EuclideanSpace ℝ (Fin 3)), ((capPole b : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3))⟫_ℝ =
        (4 - ‖(capMap b (x : EuclideanSpace ℝ (Fin 3))).1‖ ^ 2) /
          (‖(capMap b (x : EuclideanSpace ℝ (Fin 3))).1‖ ^ 2 + 4) := by
  have hxs := val_mem_capSource_of_mem_neckCapRegion hx
  cases b
  · have hx0 := ne_zero_of_mem_capSource hxs
    set θ := DifferentialGeometry.Topology.Manifold.sphereDirection southPole
      (x : EuclideanSpace ℝ (Fin 3))
    refine ⟨θ, (DifferentialGeometry.Topology.Manifold.norm_smul_sphereDirection _ hx0).symm, ?_⟩
    have hl : (DifferentialGeometry.Topology.Handle.stereoChart northPole).symm
        (DifferentialGeometry.Topology.Handle.stereoChart northPole θ) = θ :=
      (DifferentialGeometry.Topology.Handle.stereoChart northPole).left_inv
        (sphereDirection_mem_stereoChart_source hxs)
    have h := inner_stereoNorth_symm_south (DifferentialGeometry.Topology.Handle.stereoChart
      northPole θ)
    rw [hl] at h
    exact h
  · have hrs := mem_capSource_true_iff.mp hxs
    have hr0 := ne_zero_of_mem_capSource hrs
    set θ' := DifferentialGeometry.Topology.Manifold.sphereDirection southPole
      (reflectThree (x : EuclideanSpace ℝ (Fin 3)))
    let θ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
      ⟨reflectThree (θ' : EuclideanSpace ℝ (Fin 3)), by simp⟩
    refine ⟨θ, ?_, ?_⟩
    · have h := DifferentialGeometry.Topology.Manifold.norm_smul_sphereDirection southPole hr0
      rw [norm_reflectThree] at h
      have h' := congrArg reflectThree h
      rw [LinearIsometryEquiv.map_smul, reflectThree_reflectThree] at h'
      exact h'.symm
    · have hl : (DifferentialGeometry.Topology.Handle.stereoChart northPole).symm
          (DifferentialGeometry.Topology.Handle.stereoChart northPole θ') = θ' :=
        (DifferentialGeometry.Topology.Handle.stereoChart northPole).left_inv
          (sphereDirection_mem_stereoChart_source hrs)
      have h := inner_stereoNorth_symm_south (DifferentialGeometry.Topology.Handle.stereoChart
        northPole θ')
      rw [hl] at h
      change ⟪reflectThree (θ' : EuclideanSpace ℝ (Fin 3)),
        ((northPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : EuclideanSpace ℝ (Fin 3))⟫_ℝ = _
      rw [inner_reflectThree, reflectThree_north]
      exact h

theorem capMap_snd (b : Bool) (x : EuclideanSpace ℝ (Fin 3)) : (capMap b x).2 = ‖x‖ - 1 := by
  cases b
  · rfl
  · change ‖reflectThree x‖ - 1 = ‖x‖ - 1
    rw [norm_reflectThree]

theorem stereoHeight_gt_neg_one (r : ℝ) : -1 < (4 - r ^ 2) / (r ^ 2 + 4) := by
  have h : (0 : ℝ) < r ^ 2 + 4 := by positivity
  rw [lt_div_iff₀ h]
  linarith

theorem stereoHeight_lt_one {r : ℝ} (hr : 0 < r) : (4 - r ^ 2) / (r ^ 2 + 4) < 1 := by
  have h : (0 : ℝ) < r ^ 2 + 4 := by positivity
  rw [div_lt_iff₀ h]
  nlinarith

theorem stereoHeight_pos {r : ℝ} (hr : 0 ≤ r) (hr2 : r < 2) : 0 < (4 - r ^ 2) / (r ^ 2 + 4) :=
  div_pos (by nlinarith) (by positivity)

/-- Points of the closed south cap `{a ≤ ⟪θ, south⟫}` are inverse stereographic images (from the
north pole) of the closed disk of radius `r`, `a = (4 - r²)/(r² + 4)`. -/
theorem exists_stereoNorth_of_cap {r : ℝ} (hr : 0 ≤ r) (θ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hθ : (4 - r ^ 2) / (r ^ 2 + 4) ≤ ⟪(θ : EuclideanSpace ℝ (Fin 3)),
      ((southPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : EuclideanSpace ℝ (Fin 3))⟫_ℝ) :
    ∃ x : EuclideanSpace ℝ (Fin 2), ‖x‖ ≤ r ∧
      (DifferentialGeometry.Topology.Handle.stereoChart northPole).symm x = θ := by
  have hθn : θ ≠ northPole := by
    rintro rfl
    rw [inner_north_south] at hθ
    linarith [stereoHeight_gt_neg_one r]
  set x := DifferentialGeometry.Topology.Handle.stereoChart northPole θ
  have hl : (DifferentialGeometry.Topology.Handle.stereoChart northPole).symm x = θ :=
    (DifferentialGeometry.Topology.Handle.stereoChart northPole).left_inv
      (by rw [DifferentialGeometry.Topology.Handle.stereoChart_source]; exact hθn)
  refine ⟨x, ?_, hl⟩
  have h := inner_stereoNorth_symm_south x
  rw [hl] at h
  rw [h] at hθ
  by_contra hlt
  exact (not_lt.mpr hθ) ((stereoHeight_lt_iff hr (norm_nonneg x)).mpr (not_le.mp hlt))

theorem exists_stereoSouth_of_cap {r : ℝ} (hr : 0 ≤ r) (θ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hθ : (4 - r ^ 2) / (r ^ 2 + 4) ≤ ⟪(θ : EuclideanSpace ℝ (Fin 3)),
      ((northPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : EuclideanSpace ℝ (Fin 3))⟫_ℝ) :
    ∃ x : EuclideanSpace ℝ (Fin 2), ‖x‖ ≤ r ∧
      (DifferentialGeometry.Topology.Handle.stereoChart southPole).symm x = θ := by
  have hθs : θ ≠ southPole := by
    rintro rfl
    have h1 : ⟪((southPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : EuclideanSpace ℝ (Fin 3)),
        ((northPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
          EuclideanSpace ℝ (Fin 3))⟫_ℝ = -1 := by
      rw [real_inner_comm, inner_north_south]
    rw [h1] at hθ
    linarith [stereoHeight_gt_neg_one r]
  set x := DifferentialGeometry.Topology.Handle.stereoChart southPole θ
  have hl : (DifferentialGeometry.Topology.Handle.stereoChart southPole).symm x = θ :=
    (DifferentialGeometry.Topology.Handle.stereoChart southPole).left_inv
      (by rw [DifferentialGeometry.Topology.Handle.stereoChart_source]; exact hθs)
  refine ⟨x, ?_, hl⟩
  have h := inner_stereoSouth_symm_south x
  rw [hl, inner_south_eq_neg_inner_north] at h
  have h' : ⟪(θ : EuclideanSpace ℝ (Fin 3)), ((northPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3))⟫_ℝ = (4 - ‖x‖ ^ 2) / (‖x‖ ^ 2 + 4) := by
    have hpos : (0 : ℝ) < ‖x‖ ^ 2 + 4 := by positivity
    rw [neg_eq_iff_eq_neg] at h
    rw [h]
    field_simp
    ring
  rw [h'] at hθ
  by_contra hlt
  exact (not_lt.mpr hθ) ((stereoHeight_lt_iff hr (norm_nonneg x)).mpr (not_le.mp hlt))

/-! ## T3′ -/

theorem monotone_compress {l a : ℝ} (hl : 0 < l) (ha : 0 ≤ a) : Monotone (compress l ha) := by
  apply StrictMono.monotone
  apply strictMono_of_deriv_pos
  intro τ
  obtain ⟨d, hd, hD⟩ := hasDerivAt_compress hl ha τ
  rw [hD.deriv]
  exact hd

/-- After the radial compression with `compress l a (-2ε) = -δ/2`, a point of the cap region `b`
lies within `δ` of the closed spherical cap `{a' ≤ ⟪θ, capPole b⟫}` (`a'` the stereographic height
of a radius `≥ 1 + 2ε`). -/
theorem radialCompress_mem_thickening_cap {ε l a r δ : ℝ} (hε' : ε ≤ 1 / 8) (hl : 0 < l)
    (ha : 0 ≤ a) (hla : l * (1 / 2 + a) ≤ 3 / 4) (hr : 1 + 2 * ε ≤ r) (hδ : 0 < δ)
    (hc : -(δ / 2) ≤ compress l ha (-(2 * ε))) {b : Bool} {x : ClosedCell 3}
    (hx : x ∈ neckCapRegion ε b) :
    radialCompressDiffeo hl ha hla (x : EuclideanSpace ℝ (Fin 3)) ∈
      thickening δ (Subtype.val '' {θ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 |
        (4 - r ^ 2) / (r ^ 2 + 4) ≤ ⟪(θ : EuclideanSpace ℝ (Fin 3)),
          ((capPole b : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : EuclideanSpace ℝ (Fin 3))⟫_ℝ}) := by
  obtain ⟨θ, hxθ, hθin⟩ := exists_dir_of_mem_neckCapRegion hx
  have hxn1 : ‖(x : EuclideanSpace ℝ (Fin 3))‖ ≤ 1 := x.2
  have hxn2 : 1 - 2 * ε < ‖(x : EuclideanSpace ℝ (Fin 3))‖ := hx.1
  have hs : ‖(capMap b (x : EuclideanSpace ℝ (Fin 3))).1‖ < 1 + 2 * ε := hx.2.2
  have hx0 : (x : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hxn2
    linarith
  have hθa : (4 - r ^ 2) / (r ^ 2 + 4) ≤ ⟪(θ : EuclideanSpace ℝ (Fin 3)),
      ((capPole b : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : EuclideanSpace ℝ (Fin 3))⟫_ℝ := by
    rw [hθin]
    exact ((stereoHeight_lt_iff (norm_nonneg _) (by linarith)).mpr (by linarith)).le
  set ρ := radialCompress l ha ‖(x : EuclideanSpace ℝ (Fin 3))‖
  have hρ : ρ = 1 + compress l ha (‖(x : EuclideanSpace ℝ (Fin 3))‖ - 1) :=
    radialCompress_of_quarter_le ha (by linarith)
  have hc1 : compress l ha (‖(x : EuclideanSpace ℝ (Fin 3))‖ - 1) ≤ 0 :=
    compress_nonpos hl ha (by linarith)
  have hc2 : compress l ha (-(2 * ε)) ≤ compress l ha (‖(x : EuclideanSpace ℝ (Fin 3))‖ - 1) :=
    monotone_compress hl ha (by linarith)
  have hT : radialCompressDiffeo hl ha hla (x : EuclideanSpace ℝ (Fin 3)) =
      ρ • (θ : EuclideanSpace ℝ (Fin 3)) := by
    rw [radialCompressDiffeo_apply, radialScaleMap_eq_smul _ hx0]
    conv_lhs => arg 2; rw [hxθ]
    rw [smul_smul, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx0)]
  rw [mem_thickening_iff]
  refine ⟨θ, ⟨θ, hθa, rfl⟩, ?_⟩
  rw [hT, dist_eq_norm]
  have h1 : ρ • (θ : EuclideanSpace ℝ (Fin 3)) - (θ : EuclideanSpace ℝ (Fin 3)) =
      (ρ - 1) • (θ : EuclideanSpace ℝ (Fin 3)) := by rw [sub_smul, one_smul]
  rw [h1, norm_smul, norm_eq_of_mem_sphere, mul_one, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  linarith

/-- **T3′ (balls).** A ball with two necks (ball side `{τ ≤ 0}`, disjoint targets, opposite
chart-free relative signs) is reparametrized, after compressing the ball sides of the necks by the
profile `compress l a`, to agree with the compressed necks on the two cap regions, with the same
image. (The interior hypothesis `hint` of the frozen draft is not needed.) -/
theorem PieceEmbedding.exists_ballReparam_eq_necks {W : CompactCarrier.{u}} (B : PieceEmbedding W)
    (e : B.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3) {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 8)
    (N : Bool → PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
      (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞)
    (hsrc : ∀ b, closedNeckDomain ε ⊆ (N b).source)
    (hdisj : Disjoint (N false).target (N true).target)
    (hside : ∀ b {q}, q ∈ (N b).source → (N b q ∈ range B.map ↔ q.2 ≤ 0))
    (hsign : ∀ x₀ x₁, B.map (e.symm x₀) = N false 0 → B.map (e.symm x₁) = N true 0 →
      ballNeckDetAmb B e x₀ (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model (N false) 0) *
      ballNeckDetAmb B e x₁ (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model (N true) 0) < 0) :
    ∃ l a : ℝ, 0 < l ∧ ∃ ha : 0 ≤ a, l * (1 / 2 + a) ≤ 3 / 4 ∧
    ∃ β : ClosedCell 3 → W.Carrier,
      ContMDiff (𝓡∂ 3) W.model ∞ β ∧ (∀ x, Bijective (mfderiv (𝓡∂ 3) W.model β x)) ∧
      Injective β ∧ range β = range B.map ∧
      ∀ b x, x ∈ neckCapRegion ε b →
        β x = N b ((capMap b (x : EuclideanSpace ℝ (Fin 3))).1,
          compress l ha (capMap b (x : EuclideanSpace ℝ (Fin 3))).2) := by
  classical
  -- the ball side of the closed neck box
  set C : Set (EuclideanSpace ℝ (Fin 2) × ℝ) := closedNeckDomain ε ∩ {q | q.2 ≤ 0} with hCdef
  have hCc : IsCompact C :=
    (isCompact_closedNeckDomain ε).inter_right (isClosed_le continuous_snd continuous_const)
  have hC0 : (0 : EuclideanSpace ℝ (Fin 2) × ℝ) ∈ C :=
    ⟨⟨by simp only [Prod.fst_zero, norm_zero]; positivity, by simp only [Prod.snd_zero, abs_zero, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]; positivity⟩, show (0 : ℝ) ≤ 0 from le_rfl⟩
  have hgerm : ∀ b, ∃ φ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
        𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (EuclideanSpace ℝ (Fin 3))
        (EuclideanSpace ℝ (Fin 2) × ℝ) ∞,
      ∃ Ω : Set (EuclideanSpace ℝ (Fin 2) × ℝ), IsOpen Ω ∧ C ⊆ Ω ∧ Ω ⊆ φ.target ∧
        Ω ⊆ (N b).source ∧
        (∀ q ∈ Ω, q.2 ≤ 0 → ∃ y : ClosedCell 3, φ.symm q = y.val ∧ ballCell B e y = N b q) ∧
        (∀ q ∈ Ω, q.2 = 0 → ‖φ.symm q‖ = 1) ∧
        (∀ q ∈ Ω, ∀ y : ClosedCell 3, φ.symm q = y.val → ballCell B e y = N b q →
          (fderiv ℝ φ y.val).comp (mfderiv (𝓡∂ 3) (𝓡 3)
            (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) y) =
          (mfderiv W.model 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (N b).symm (N b q)).comp
            (mfderiv (𝓡∂ 3) W.model (ballCell B e) y)) := fun b =>
    exists_ballGerm B e (N b) (hside b) hCc ⟨0, hC0⟩ (fun q hq => hsrc b hq.1) (fun q hq => hq.2)
  choose φ Ω hΩ hCΩ hΩt hΩN hG2 hG3 hG4 using hgerm
  have hδex : ∀ b, ∃ δ, 0 < δ ∧ thickening δ C ⊆ Ω b := fun b =>
    hCc.exists_thickening_subset_open (hΩ b) (hCΩ b)
  choose δb hδb hδbΩ using hδex
  set δ := min (min (δb false) (δb true)) (1 / 4) with hδdef
  have hδpos : 0 < δ := lt_min (lt_min (hδb false) (hδb true)) (by norm_num)
  have hδq : δ ≤ 1 / 4 := min_le_right _ _
  have hthick : ∀ b, thickening δ C ⊆ Ω b := by
    intro b
    refine (thickening_mono ?_ C).trans (hδbΩ b)
    cases b
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact (min_le_left _ _).trans (min_le_right _ _)
  set R := 1 + 2 * ε + δ / 2 with hRdef
  set r₀ := 1 + 2 * ε + δ / 4 with hr₀def
  have hR2 : R < 2 := by rw [hRdef]; linarith
  have hr₀R : r₀ < R := by rw [hRdef, hr₀def]; linarith
  have hr₀pos : 0 < r₀ := by rw [hr₀def]; linarith
  have hkey : ∀ b (x : EuclideanSpace ℝ (Fin 2)), ‖x‖ ≤ R → (x, (0 : ℝ)) ∈ Ω b := fun b x hx =>
    hthick b (mem_thickening_ballSideBox hε.le hδpos hx)
  -- the germs of the two caps
  let F : Bool → PartialDiffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3))
      (EuclideanSpace ℝ (Fin 3)) ∞ := fun b =>
    (capPD b).trans (restrictNeck (φ b).symm (Ω b) (hΩ b))
  have hFapp : ∀ b p, F b p = (φ b).symm (capMap b p) := fun _ _ => rfl
  have hFsrc : ∀ b p, p ∈ (F b).source ↔ p ∈ capSource b ∧ capMap b p ∈ Ω b := by
    intro b p
    constructor
    · rintro ⟨hp, hq⟩
      exact ⟨hp, hq.2⟩
    · rintro ⟨hp, hq⟩
      exact ⟨hp, hΩt b hq, hq⟩
  -- the disk charts of the sphere and the caps
  set a := (4 - r₀ ^ 2) / (r₀ ^ 2 + 4) with hadef
  have ha1 : -1 < a := stereoHeight_gt_neg_one r₀
  have ha2 : a < 1 := stereoHeight_lt_one hr₀pos
  have ha0 : 0 < a := stereoHeight_pos hr₀pos.le (by linarith)
  let φ₀ := (DifferentialGeometry.Topology.Handle.stereoChart northPole).symm
  let φ₁ := (DifferentialGeometry.Topology.Handle.stereoChart southPole).symm
  have hφ₀src : closedBall (0 : EuclideanSpace ℝ (Fin 2)) R ⊆ φ₀.source := by
    intro x _
    change x ∈ (DifferentialGeometry.Topology.Handle.stereoChart northPole).target
    rw [DifferentialGeometry.Topology.Handle.stereoChart_target]
    exact mem_univ _
  have hφ₁src : closedBall (0 : EuclideanSpace ℝ (Fin 2)) R ⊆ φ₁.source := by
    intro x _
    change x ∈ (DifferentialGeometry.Topology.Handle.stereoChart southPole).target
    rw [DifferentialGeometry.Topology.Handle.stereoChart_target]
    exact mem_univ _
  have hF₀ : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) R,
      (φ₀ x : EuclideanSpace ℝ (Fin 3)) ∈ (F false).source := by
    intro x hx
    have hxR : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp hx
    refine (hFsrc false _).mpr ⟨mem_capSource_false_stereoNorth_symm (by linarith), ?_⟩
    change capMap false ((DifferentialGeometry.Topology.Handle.stereoChart northPole).symm x :
      EuclideanSpace ℝ (Fin 3)) ∈ Ω false
    rw [capMap_false_stereoNorth_symm]
    exact hkey false x hxR
  have hF₁ : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) R,
      (φ₁ x : EuclideanSpace ℝ (Fin 3)) ∈ (F true).source := by
    intro x hx
    have hxR : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp hx
    refine (hFsrc true _).mpr ⟨mem_capSource_true_stereoSouth_symm (by linarith), ?_⟩
    obtain ⟨h2, h1⟩ := capMap_true_stereoSouth_symm x
    have heq : capMap true ((DifferentialGeometry.Topology.Handle.stereoChart southPole).symm x :
        EuclideanSpace ℝ (Fin 3)) = ((capMap true ((DifferentialGeometry.Topology.Handle.stereoChart
          southPole).symm x : EuclideanSpace ℝ (Fin 3))).1, 0) := Prod.ext rfl h2
    change capMap true _ ∈ Ω true
    rw [heq]
    exact hkey true _ (h1.le.trans hxR)
  have hbd : ∀ b, MapsTo (F b) (sphere 0 1 ∩ (F b).source) (sphere 0 1) := by
    rintro b p ⟨hp1, hp2⟩
    obtain ⟨-, hq⟩ := (hFsrc b p).mp hp2
    have hq0 : (capMap b p).2 = 0 := by
      rw [capMap_snd, mem_sphere_zero_iff_norm.mp hp1, sub_self]
    rw [hFapp]
    exact mem_sphere_zero_iff_norm.mpr (hG3 b _ hq hq0)
  have hsd : ∀ b, MapsTo (F b) (closedBall 0 1 ∩ (F b).source) (closedBall 0 1) := by
    rintro b p ⟨hp1, hp2⟩
    obtain ⟨-, hq⟩ := (hFsrc b p).mp hp2
    have hq0 : (capMap b p).2 ≤ 0 := by
      rw [capMap_snd]
      linarith [mem_closedBall_zero_iff.mp hp1]
    obtain ⟨y, hy, -⟩ := hG2 b _ hq hq0
    rw [hFapp, hy]
    exact mem_closedBall_zero_iff.mpr y.2
  have hcap : {θ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 |
      a ≤ ⟪(θ : EuclideanSpace ℝ (Fin 3)),
        ((southPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : EuclideanSpace ℝ (Fin 3))⟫_ℝ} ⊆
      φ₀ '' ball 0 R := by
    intro θ hθ
    obtain ⟨x, hx, hxθ⟩ := exists_stereoNorth_of_cap hr₀pos.le θ hθ
    exact ⟨x, mem_ball_zero_iff.mpr (lt_of_le_of_lt hx hr₀R), hxθ⟩
  have hφ₁cap : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) R,
      ⟪(φ₁ x : EuclideanSpace ℝ (Fin 3)),
        ((southPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
          EuclideanSpace ℝ (Fin 3))⟫_ℝ < a := by
    intro x hx
    have hxR : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp hx
    change ⟪((DifferentialGeometry.Topology.Handle.stereoChart southPole).symm x :
      EuclideanSpace ℝ (Fin 3)), _⟫_ℝ < a
    rw [inner_stereoSouth_symm_south]
    have h1 : (0 : ℝ) < ‖x‖ ^ 2 + 4 := by positivity
    have h2 : ‖x‖ ^ 2 < 4 := by nlinarith [norm_nonneg x]
    have h3 : (‖x‖ ^ 2 - 4) / (‖x‖ ^ 2 + 4) < 0 := div_neg_of_neg_of_pos (by linarith) h1
    linarith
  -- the end-disk points read in the cell
  have hcell : ∀ b p, p ∈ (F b).source → p ∈ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 →
      ∃ y : ClosedCell 3, F b p = y.val ∧ ballCell B e y ∈ (N b).target := by
    intro b p hp hp1
    obtain ⟨-, hq⟩ := (hFsrc b p).mp hp
    have hq0 : (capMap b p).2 ≤ 0 := by
      rw [capMap_snd, mem_sphere_zero_iff_norm.mp hp1, sub_self]
    obtain ⟨y, hy, hBy⟩ := hG2 b _ hq hq0
    refine ⟨y, by rw [hFapp, hy], ?_⟩
    rw [hBy]
    exact (N b).map_source (hΩN b hq)
  have hdisj' : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) R,
      ∀ θ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        a ≤ ⟪(θ : EuclideanSpace ℝ (Fin 3)),
          ((southPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : EuclideanSpace ℝ (Fin 3))⟫_ℝ →
          F true (φ₁ x : EuclideanSpace ℝ (Fin 3)) ≠ F false (θ : EuclideanSpace ℝ (Fin 3)) := by
    intro x hx θ hθ heq
    obtain ⟨x', hx', hx'θ⟩ := exists_stereoNorth_of_cap hr₀pos.le θ hθ
    have hθs : (θ : EuclideanSpace ℝ (Fin 3)) ∈ (F false).source := by
      rw [← hx'θ]
      exact hF₀ x' (mem_closedBall_zero_iff.mpr (hx'.trans hr₀R.le))
    obtain ⟨y₀, hy₀, hN₀⟩ := hcell false _ hθs θ.2
    obtain ⟨y₁, hy₁, hN₁⟩ := hcell true _ (hF₁ x hx) (φ₁ x).2
    have hyy : y₁ = y₀ := Subtype.ext (by rw [← hy₀, ← hy₁, heq])
    rw [hyy] at hN₁
    exact Set.disjoint_left.mp hdisj hN₀ hN₁
  -- the orientation hypothesis of G2
  have hcap0 : capMap false ((southPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3)) = 0 := by
    rw [← stereoNorth_symm_zero, capMap_false_stereoNorth_symm]
    rfl
  have hcap1 : capMap true ((northPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3)) = 0 := by
    rw [← stereoSouth_symm_zero]
    obtain ⟨h2, h1⟩ := capMap_true_stereoSouth_symm 0
    rw [norm_zero, norm_eq_zero] at h1
    exact Prod.ext h1 h2
  have hpoleSrc : ∀ b, (if b then (northPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) else
      southPole : EuclideanSpace ℝ (Fin 3)) ∈ capSource b := by
    intro b
    cases b
    · exact southPole_mem_capSource
    · exact northPole_mem_capSource
  have hdetF : ∀ b, ∃ y : ClosedCell 3, B.map (e.symm y) = N b 0 ∧
      (fderiv ℝ (F b) (if b then (northPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) else
        southPole : EuclideanSpace ℝ (Fin 3))).det =
      ballNeckDetAmb B e y (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model (N b) 0) *
        LinearMap.det (neckSpaceEquiv.symm.toLinearMap ∘ₗ (fderiv ℝ (capMap b)
          (if b then (northPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) else
            southPole : EuclideanSpace ℝ (Fin 3))).toLinearMap) := by
    intro b
    set p : EuclideanSpace ℝ (Fin 3) := (if b then (northPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      else southPole : EuclideanSpace ℝ (Fin 3)) with hpdef
    have hp0 : capMap b p = 0 := by
      cases b
      · exact hcap0
      · exact hcap1
    have h0Ω : (0 : EuclideanSpace ℝ (Fin 2) × ℝ) ∈ Ω b := hCΩ b hC0
    obtain ⟨y, hy, hBy⟩ := hG2 b 0 h0Ω (le_refl (0 : ℝ))
    refine ⟨y, hBy, ?_⟩
    have hd1 : DifferentiableAt ℝ (φ b).symm (capMap b p) := by
      rw [hp0]
      exact ((φ b).symm.contMDiffOn_toFun.contDiffOn.contDiffAt
        ((φ b).open_target.mem_nhds (hΩt b h0Ω))).differentiableAt (by simp)
    have hd2 : DifferentiableAt ℝ (capMap b) p :=
      (hasFDerivAt_capMap b (hpoleSrc b)).differentiableAt
    have hfd : fderiv ℝ (F b) p = (fderiv ℝ (φ b).symm 0).comp (fderiv ℝ (capMap b) p) := by
      change fderiv ℝ ((φ b).symm ∘ capMap b) p = _
      rw [fderiv_comp p hd1 hd2, hp0]
    rw [hfd]
    exact det_fderiv_germSymm_comp B e (N b) (φ b) (hΩt b h0Ω) (hΩN b h0Ω) hy
      (hG4 b 0 h0Ω y hy hBy) _
  have hori : 0 < (fderiv ℝ (F false) ((southPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3))).det *
      (fderiv ℝ (F true) (φ₁ 0 : EuclideanSpace ℝ (Fin 3))).det := by
    have hφ10 : (φ₁ 0 : EuclideanSpace ℝ (Fin 3)) =
        ((northPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : EuclideanSpace ℝ (Fin 3)) := by
      change ((DifferentialGeometry.Topology.Handle.stereoChart southPole).symm 0 :
        EuclideanSpace ℝ (Fin 3)) = _
      rw [stereoSouth_symm_zero]
    rw [hφ10]
    obtain ⟨y₀, hy₀, hd₀⟩ := hdetF false
    obtain ⟨y₁, hy₁, hd₁⟩ := hdetF true
    simp only [Bool.false_eq_true, ite_false, ite_true] at hd₀ hd₁
    rw [hd₀, hd₁, fderiv_capMap_true_north]
    set D₀ := fderiv ℝ (capMap false) ((southPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3))
    have hcomp : neckSpaceEquiv.symm.toLinearMap ∘ₗ
        (D₀.comp reflectThree.toContinuousLinearEquiv.toContinuousLinearMap).toLinearMap =
        (neckSpaceEquiv.symm.toLinearMap ∘ₗ D₀.toLinearMap) ∘ₗ
          (reflectThree.toLinearEquiv : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) :=
      LinearMap.ext fun _ => rfl
    rw [hcomp, LinearMap.det_comp, det_reflectThree]
    have hbij : Bijective (neckSpaceEquiv.symm.toLinearMap ∘ₗ D₀.toLinearMap) :=
      neckSpaceEquiv.symm.bijective.comp bijective_fderiv_capMap_south
    have hd : LinearMap.det (neckSpaceEquiv.symm.toLinearMap ∘ₗ D₀.toLinearMap) ≠ 0 :=
      (LinearEquiv.ofBijective _ hbij).isUnit_det'.ne_zero
    have hs := hsign y₀ y₁ hy₀ hy₁
    have hsq := sq_pos_of_ne_zero hd
    nlinarith
  set K₁ : Set (EuclideanSpace ℝ (Fin 3)) := Subtype.val '' {θ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 |
      a ≤ ⟪(θ : EuclideanSpace ℝ (Fin 3)),
        ((northPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : EuclideanSpace ℝ (Fin 3))⟫_ℝ}
    with hK₁def
  have hK₁c : IsCompact K₁ :=
    (isClosed_le continuous_const (continuous_subtype_val.inner continuous_const)).isCompact.image
      continuous_subtype_val
  have hK₁φ : K₁ ⊆ Subtype.val '' (φ₁ '' ball 0 R) := by
    rintro _ ⟨θ, hθ, rfl⟩
    obtain ⟨x, hx, hxθ⟩ := exists_stereoSouth_of_cap hr₀pos.le θ hθ
    exact ⟨θ, ⟨x, mem_ball_zero_iff.mpr (lt_of_le_of_lt hx hr₀R), hxθ⟩, rfl⟩
  obtain ⟨D, ⟨V₀, hV₀o, hσV₀, hV₀F, hDV₀⟩, ⟨V₁, hV₁o, hKV₁, hV₁F, hDV₁⟩⟩ :=
    DifferentialGeometry.Topology.Handle.exists_closedCell_diffeomorph_eqOn_two_boundary_disks
      (F false) (F true) φ₀ φ₁ (R := R) (by rw [hRdef]; linarith) hφ₀src hφ₁src hF₀ hF₁
      (hbd false) (hbd true) (hsd false) (hsd true) southPole ha1 ha2 hcap hφ₁cap hdisj' hori
      hK₁c hK₁φ
  -- the compression
  set σ₀ : Set (EuclideanSpace ℝ (Fin 3)) := Subtype.val '' {θ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 |
      a ≤ ⟪(θ : EuclideanSpace ℝ (Fin 3)),
        ((southPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : EuclideanSpace ℝ (Fin 3))⟫_ℝ}
    with hσ₀def
  have hσ₀c : IsCompact σ₀ :=
    (isClosed_le continuous_const (continuous_subtype_val.inner continuous_const)).isCompact.image
      continuous_subtype_val
  obtain ⟨δ₀, hδ₀, hδ₀V⟩ := hσ₀c.exists_thickening_subset_open hV₀o hσV₀
  obtain ⟨δ₁, hδ₁, hδ₁V⟩ := hK₁c.exists_thickening_subset_open hV₁o hKV₁
  set δc := min (min δ₀ δ₁) ε with hδcdef
  have hδc : 0 < δc := lt_min (lt_min hδ₀ hδ₁) hε
  have hδc0 : δc ≤ δ₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hδc1 : δc ≤ δ₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hδcε : δc ≤ ε := min_le_right _ _
  set a' := (2 * ε - δc / 2) / δc with ha'def
  have ha' : 0 ≤ a' := div_nonneg (by linarith) hδc.le
  have hla' : δc * (1 / 2 + a') = 2 * ε := by
    rw [ha'def]
    field_simp
    ring
  have hla : δc * (1 / 2 + a') ≤ 3 / 4 := by rw [hla']; linarith
  have hc2 : -(δc / 2) ≤ compress δc ha' (-(2 * ε)) := by
    rw [compress_eq_add hδc ha' (by rw [neg_mul, hla'])]
    have : δc * a' = 2 * ε - δc / 2 := by
      rw [ha'def]
      field_simp
    rw [this]
    linarith
  let Tℝ := radialCompressDiffeo hδc ha' hla
  let T := DifferentialGeometry.Topology.Handle.closedCellDiffeomorphOfImageEq Tℝ
    (radialCompressDiffeo_image_closedBall hδc ha' hla)
  have hTval : ∀ x : ClosedCell 3, (T x : EuclideanSpace ℝ (Fin 3)) = Tℝ x := fun x =>
    DifferentialGeometry.Topology.Handle.closedCellDiffeomorphOfImageEq_val _ _ x
  refine ⟨δc, a', hδc, ha', hla, ballCell B e ∘ D ∘ T, ?_, ?_, ?_, ?_, ?_⟩
  · exact (contMDiff_ballCell B e).comp (D.contMDiff.comp T.contMDiff)
  · intro x
    rw [mfderiv_comp x ((contMDiff_ballCell B e).mdifferentiable (by simp) _)
      ((D.contMDiff.comp T.contMDiff).mdifferentiable (by simp) x),
      mfderiv_comp x (D.contMDiff.mdifferentiable (by simp) _)
        (T.contMDiff.mdifferentiable (by simp) x)]
    exact (bijective_mfderiv_ballCell B e _).comp
      ((D.isInvertible_mfderiv (by simp)).bijective.comp (T.isInvertible_mfderiv (by simp)).bijective)
  · exact (injective_ballCell B e).comp (D.injective.comp T.injective)
  · rw [← range_ballCell B e]
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨T.symm (D.symm y), by simp⟩
  · intro b x hx
    have hxn1 : ‖(x : EuclideanSpace ℝ (Fin 3))‖ ≤ 1 := x.2
    have hxn2 : 1 - 2 * ε < ‖(x : EuclideanSpace ℝ (Fin 3))‖ := hx.1
    have hthk := radialCompress_mem_thickening_cap hε' hδc ha' hla
      (show 1 + 2 * ε ≤ r₀ by rw [hr₀def]; linarith) hδc hc2 hx
    -- `T x` lies in the open set where `D` is the germ
    have hgerm : (T x : EuclideanSpace ℝ (Fin 3)) ∈ (F b).source ∧
        ((D (T x) : ClosedCell 3) : EuclideanSpace ℝ (Fin 3)) = F b (T x) := by
      cases b
      · have hV : (T x : EuclideanSpace ℝ (Fin 3)) ∈ V₀ := by
          rw [hTval]
          exact hδ₀V (thickening_mono hδc0 _ hthk)
        exact ⟨hV₀F hV, hDV₀ (T x) hV⟩
      · have hV : (T x : EuclideanSpace ℝ (Fin 3)) ∈ V₁ := by
          rw [hTval]
          exact hδ₁V (thickening_mono hδc1 _ hthk)
        exact ⟨hV₁F hV, hDV₁ (T x) hV⟩
    obtain ⟨hTs, hDT⟩ := hgerm
    have hcapT : capMap b (T x : EuclideanSpace ℝ (Fin 3)) =
        ((capMap b (x : EuclideanSpace ℝ (Fin 3))).1,
          compress δc ha' (capMap b (x : EuclideanSpace ℝ (Fin 3))).2) := by
      rw [hTval]
      exact capMap_radialCompressDiffeo hδc ha' hla b (by linarith)
    obtain ⟨-, hq⟩ := (hFsrc b _).mp hTs
    rw [hcapT] at hq
    have hq0 : (((capMap b (x : EuclideanSpace ℝ (Fin 3))).1,
        compress δc ha' (capMap b (x : EuclideanSpace ℝ (Fin 3))).2) :
          EuclideanSpace ℝ (Fin 2) × ℝ).2 ≤ 0 :=
      compress_nonpos hδc ha' (by rw [capMap_snd]; linarith)
    obtain ⟨y, hy, hBy⟩ := hG2 b _ hq hq0
    have hDy : D (T x) = y := by
      apply Subtype.ext
      rw [hDT, hFapp, hcapT, hy]
    change ballCell B e (D (T x)) = _
    rw [hDy, hBy]

end GC.GraphManifold.Assembly
