import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PlanarModels

/-!
# The filling disc and the filling solid torus

Chapter 6, packet K06c, first part. For `p ≥ 1` the seam profile
`seamRadius p s = 3 (1 + s/2)^(1/p)` is inverted by `seamDepth p r = 2 ((r/3)^p - 1)`
(`seamDepth_seamRadius`, `seamRadius_seamDepth`).
The closed disc `discSet` of radius `3` in `PlaneLift` is the regular sublevel set of `sqDist 0 3`;
its collar `discCollar p` is `(t, σ) ↦ seamRadius p (-σ) t`, inverted by `unitOf` and `seamDepth`,
equal to `3 t` at height `0`. This gives `discPlanarBase p : PlanarBase 1` over the K06 model
`planarModel 1 = closedBall 0 3`. The filling solid torus `solidSet ⊆ PlaneLift × S¹` is the
regular sublevel set of the same function, `solidDiffeomorph` identifies it with `discSet × S¹`,
and `solidCollar p` is `discCollar p × id` through it; its boundary is the range of the collar at
height `0` (`solidSet_boundary_eq`). The profile is chosen so that the collar of the solid torus
continues the outward collar of the filled hole of the pants smoothly across the seam torus.
-/

set_option autoImplicit false

noncomputable section
open Set Metric Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

def seamRadius (p : ℕ) (s : ℝ) : ℝ := 3 * (1 + s / 2) ^ ((p : ℝ)⁻¹)

def seamDepth (p : ℕ) (r : ℝ) : ℝ := 2 * ((r / 3) ^ p - 1)

theorem seamRadius_pos (p : ℕ) {s : ℝ} (hs : -2 < s) : 0 < seamRadius p s := by
  unfold seamRadius
  have : 0 < 1 + s / 2 := by linarith
  positivity

theorem seamRadius_zero (p : ℕ) : seamRadius p 0 = 3 := by
  simp [seamRadius]

theorem div_three_pow_seamRadius (p : ℕ) [NeZero p] {s : ℝ} (hs : -2 < s) :
    (seamRadius p s / 3) ^ p = 1 + s / 2 := by
  unfold seamRadius
  rw [mul_div_cancel_left₀ _ (by norm_num : (3 : ℝ) ≠ 0)]
  exact Real.rpow_inv_natCast_pow (by linarith) (NeZero.ne p)

theorem seamDepth_seamRadius (p : ℕ) [NeZero p] {s : ℝ} (hs : -2 < s) :
    seamDepth p (seamRadius p s) = s := by
  rw [seamDepth, div_three_pow_seamRadius p hs]
  ring

theorem seamRadius_seamDepth (p : ℕ) [NeZero p] {r : ℝ} (hr : 0 ≤ r) :
    seamRadius p (seamDepth p r) = r := by
  unfold seamRadius seamDepth
  rw [show 1 + 2 * ((r / 3) ^ p - 1) / 2 = (r / 3) ^ p by ring,
    Real.pow_rpow_inv_natCast (by positivity) (NeZero.ne p)]
  ring

theorem seamRadius_le_three (p : ℕ) {s : ℝ} (hs : -2 ≤ s) (hs0 : s ≤ 0) : seamRadius p s ≤ 3 := by
  unfold seamRadius
  have h := Real.rpow_le_one (x := 1 + s / 2) (z := (p : ℝ)⁻¹) (by linarith) (by linarith)
    (by positivity)
  linarith

theorem contDiffAt_seamRadius (p : ℕ) {s : ℝ} (hs : -2 < s) :
    ContDiffAt ℝ ∞ (seamRadius p) s :=
  contDiffAt_const.mul ((Real.contDiffAt_rpow_const_of_ne (p := (p : ℝ)⁻¹)
    (by linarith : 1 + s / 2 ≠ 0)).comp s (contDiffAt_const.add (contDiffAt_id.div_const 2)))

theorem contDiff_seamDepth (p : ℕ) : ContDiff ℝ ∞ (seamDepth p) :=
  contDiff_const.mul (((contDiff_id.div_const 3).pow p).sub contDiff_const)

theorem seamDepth_nonpos (p : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 3) : seamDepth p r ≤ 0 := by
  unfold seamDepth
  have : (r / 3) ^ p ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
  linarith

theorem ne_zero_of_neg_seamDepth_lt (p : ℕ) [NeZero p] {r : ℝ} (h : -seamDepth p r < 1) :
    r ≠ 0 := by
  rintro rfl
  simp [seamDepth, NeZero.ne p] at h

theorem sqDist_nonpos_iff (c : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (z : ℂ) :
    sqDist c ρ z ≤ 0 ↔ ‖z - c‖ ≤ ρ := by
  rw [sqDist, sub_nonpos]
  exact pow_le_pow_iff_left₀ (norm_nonneg _) hρ two_ne_zero

theorem sqDist_eq_zero_iff (c : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (z : ℂ) :
    sqDist c ρ z = 0 ↔ ‖z - c‖ = ρ := by
  rw [sqDist]
  exact sq_sub_sq_eq_zero_iff (norm_nonneg _) hρ

theorem sqDist_neg_iff (c : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (z : ℂ) :
    sqDist c ρ z < 0 ↔ ‖z - c‖ < ρ := by
  rw [sqDist, sub_neg]
  exact pow_lt_pow_iff_left₀ (norm_nonneg _) hρ two_ne_zero

theorem fderiv_sqDist_ne_zero {c : ℂ} {ρ : ℝ} (hρ : ρ ≠ 0) {z : ℂ} (hz : sqDist c ρ z = 0) :
    fderiv ℝ (sqDist c ρ) z ≠ 0 := by
  have h := fderiv_sqDist_mul_ne_zero (R := fun _ => (1 : ℝ)) (differentiableAt_const _) hz
    one_ne_zero hρ
  simpa only [mul_one] using h

def discSet : Set PlaneLift.{u} := {w | sqDist 0 3 w.down ≤ 0}

theorem mem_discSet_iff (w : PlaneLift.{u}) : w ∈ discSet ↔ ‖w.down‖ ≤ 3 := by
  change sqDist 0 3 w.down ≤ 0 ↔ _
  rw [sqDist_nonpos_iff 0 (by norm_num), sub_zero]

theorem contMDiff_discFunction :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ (fun w : PlaneLift.{u} => sqDist 0 3 w.down) :=
  (contDiff_sqDist 0 3).contMDiff.comp contMDiff_planeLift_down

theorem discFunction_regular (w : PlaneLift.{u}) (hw : sqDist 0 3 w.down = 0) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (fun w : PlaneLift.{u} => sqDist 0 3 w.down) w ≠ 0 := by
  refine mfderiv_ne_zero_of_comp (J := 𝓘(ℝ, ℂ)) (s := ULift.up) (y := w.down)
    (contMDiff_discFunction.mdifferentiableAt (by simp))
    (contMDiff_planeLift_up.mdifferentiableAt (by simp)) ?_
  change mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (sqDist 0 3) w.down ≠ 0
  rw [mfderiv_eq_fderiv]
  exact fderiv_sqDist_ne_zero (by norm_num) hw

def discAtlas : SmoothBoundaryAtlas 𝓘(ℝ, ℂ) 2 discSet.{u} :=
  SmoothBoundaryAtlas.regularSublevel 𝓘(ℝ, ℂ) (n := 1) Complex.finrank_real_complex
    contMDiff_discFunction.{u} 0 discFunction_regular

instance : ChartedSpace (EuclideanHalfSpace 2) discSet.{u} := discAtlas.toChartedSpace

instance : IsManifold (𝓡∂ 2) ∞ discSet.{u} := discAtlas.isManifold

theorem discSet_isBoundaryPoint_iff (x : discSet.{u}) :
    (𝓡∂ 2).IsBoundaryPoint x ↔ ‖x.val.down‖ = 3 :=
  (SmoothBoundaryAtlas.regularSublevel_isBoundaryPoint_iff 𝓘(ℝ, ℂ) (n := 1)
    Complex.finrank_real_complex contMDiff_discFunction 0 discFunction_regular x).trans (by
      rw [sqDist_eq_zero_iff 0 (by norm_num), sub_zero])

theorem contMDiff_discSet_down :
    ContMDiff (𝓡∂ 2) 𝓘(ℝ, ℂ) ∞ (fun x : discSet.{u} => x.val.down) :=
  contMDiff_planeLift_down.comp discAtlas.contMDiff_subtype_val

theorem discSet_eq_preimage :
    discSet.{u} = (Homeomorph.ulift : PlaneLift.{u} ≃ₜ ℂ) ⁻¹' closedBall 0 3 := by
  ext w
  rw [mem_discSet_iff]
  exact mem_closedBall_zero_iff.symm

theorem isCompact_discSet : IsCompact discSet.{u} := by
  rw [discSet_eq_preimage]
  exact Homeomorph.ulift.isCompact_preimage.mpr (isCompact_closedBall 0 3)

def discSurface : CompactSurface.{u} where
  kind := .withBoundary
  Carrier := discSet.{u}
  charts := (inferInstance : ChartedSpace (EuclideanHalfSpace 2) discSet.{u})
  smooth := (inferInstance : IsManifold (𝓡∂ 2) ∞ discSet.{u})
  compact := isCompact_iff_compactSpace.mp isCompact_discSet
  connected := isConnected_iff_connectedSpace.mp (by
    rw [discSet_eq_preimage]
    exact Homeomorph.ulift.isConnected_preimage.mpr
      ((convex_closedBall (0 : ℂ) 3).isConnected (nonempty_closedBall.mpr (by norm_num))))

theorem norm_seamRadius_smul (p : ℕ) {s : ℝ} (hs : -2 < s) (t : Circle) :
    ‖seamRadius p s • (t : ℂ)‖ = seamRadius p s := by
  rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg (seamRadius_pos p hs).le]

theorem seamRadius_neg_min_mem (h : EuclideanHalfSpace 1) :
    -2 < -min (h.val 0) 1 ∧ -min (h.val 0) 1 ≤ 0 := by
  have h0 : 0 ≤ h.val 0 := h.2
  constructor
  · have := min_le_right (h.val 0) 1
    linarith
  · exact neg_nonpos.mpr (le_min h0 zero_le_one)

def discCollarMap (p : ℕ) (q : Circle × EuclideanHalfSpace 1) : discSet.{u} :=
  ⟨ULift.up (seamRadius p (-min (q.2.val 0) 1) • (q.1 : ℂ)), by
    have hm := seamRadius_neg_min_mem q.2
    rw [mem_discSet_iff]
    change ‖seamRadius p (-min (q.2.val 0) 1) • (q.1 : ℂ)‖ ≤ 3
    rw [norm_seamRadius_smul p hm.1]
    exact seamRadius_le_three p hm.1.le hm.2⟩

def discCollarInv (p : ℕ) (x : discSet.{u}) : Circle × EuclideanHalfSpace 1 :=
  (unitOf x.val.down, Manifold.halfSpaceOneLift (-seamDepth p ‖x.val.down‖))

def discCollarTarget (p : ℕ) : Set discSet.{u} := {x | -seamDepth p ‖x.val.down‖ < 1}

theorem discCollarMap_val (p : ℕ) {q : Circle × EuclideanHalfSpace 1}
    (hq : q ∈ circleCollarSource) :
    (discCollarMap.{u} p q).val.down = seamRadius p (-q.2.val 0) • (q.1 : ℂ) := by
  have hq' : q.2.val 0 < 1 := hq
  change seamRadius p (-min (q.2.val 0) 1) • (q.1 : ℂ) = _
  rw [min_eq_left hq'.le]

theorem neg_seamDepth_nonneg (p : ℕ) (x : discSet.{u}) : 0 ≤ -seamDepth p ‖x.val.down‖ :=
  neg_nonneg.mpr (seamDepth_nonpos p (norm_nonneg _) ((mem_discSet_iff x.val).mp x.2))

def discCollar (p : ℕ) [NeZero p] :
    PartialDiffeomorph circleCollarModel (𝓡∂ 2) (Circle × EuclideanHalfSpace 1) discSet.{u} ∞ where
  toFun := discCollarMap.{u} p
  invFun := discCollarInv.{u} p
  source := circleCollarSource
  target := discCollarTarget p
  map_source' := by
    intro q hq
    have hq' : q.2.val 0 < 1 := hq
    have h0 : 0 ≤ q.2.val 0 := q.2.2
    change -seamDepth p ‖(discCollarMap.{u} p q).val.down‖ < 1
    rw [discCollarMap_val p hq, norm_seamRadius_smul p (by linarith),
      seamDepth_seamRadius p (by linarith), neg_neg]
    exact hq'
  map_target' := by
    intro x hx
    have hx' : -seamDepth p ‖x.val.down‖ < 1 := hx
    change max (-seamDepth p ‖x.val.down‖) 0 < 1
    exact max_lt hx' one_pos
  left_inv' := by
    intro q hq
    have hq' : q.2.val 0 < 1 := hq
    have h0 : 0 ≤ q.2.val 0 := q.2.2
    change discCollarInv.{u} p (discCollarMap.{u} p q) = q
    unfold discCollarInv
    rw [discCollarMap_val p hq, norm_seamRadius_smul p (by linarith),
      seamDepth_seamRadius p (by linarith), neg_neg, unitOf_smul (seamRadius_pos p (by linarith)),
      halfSpaceOneLift_coord]
  right_inv' := by
    intro x hx
    have hx' : -seamDepth p ‖x.val.down‖ < 1 := hx
    have hv0 := neg_seamDepth_nonneg.{u} p x
    have hsrc : discCollarInv.{u} p x ∈ circleCollarSource := by
      change max (-seamDepth p ‖x.val.down‖) 0 < 1
      exact max_lt hx' one_pos
    apply Subtype.ext
    apply ULift.ext
    rw [discCollarMap_val p hsrc]
    change seamRadius p (-max (-seamDepth p ‖x.val.down‖) 0) •
      (unitOf x.val.down : ℂ) = x.val.down
    rw [max_eq_left hv0, neg_neg, seamRadius_seamDepth p (norm_nonneg _), norm_smul_unitOf]
  open_source := isOpen_lt
    ((EuclideanSpace.proj 0).continuous.comp (continuous_subtype_val.comp continuous_snd))
    continuous_const
  open_target := isOpen_lt (continuous_neg.comp ((contDiff_seamDepth p).continuous.comp
    (continuous_norm.comp contMDiff_discSet_down.continuous))) continuous_const
  contMDiffOn_toFun := by
    refine (discAtlas.contMDiffOn_iff_subtype_val _ _).mpr ?_
    have hpair : ContMDiff circleCollarModel 𝓘(ℝ, ℂ × ℝ) ∞
        (fun q : Circle × EuclideanHalfSpace 1 => ((q.1 : ℂ), q.2.val 0)) :=
      (contMDiff_circle_coe.comp contMDiff_fst).prodMk_space
        (Manifold.contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd)
    have hF : ∀ q ∈ circleCollarSource, ContMDiffAt circleCollarModel 𝓘(ℝ, ℂ) ∞
        (fun q : Circle × EuclideanHalfSpace 1 => seamRadius p (-q.2.val 0) • (q.1 : ℂ)) q := by
      intro q hq
      have hq' : q.2.val 0 < 1 := hq
      have hR : ContDiffAt ℝ ∞ (fun y : ℂ × ℝ => seamRadius p (-y.2))
          ((q.1 : ℂ), q.2.val 0) :=
        ContDiffAt.comp (g := seamRadius p) (f := fun y : ℂ × ℝ => -y.2) ((q.1 : ℂ), q.2.val 0)
          (contDiffAt_seamRadius p (by linarith : -2 < -q.2.val 0)) contDiffAt_snd.neg
      have hG : ContDiffAt ℝ ∞ (fun y : ℂ × ℝ => seamRadius p (-y.2) • y.1)
          ((q.1 : ℂ), q.2.val 0) := hR.smul contDiffAt_fst
      exact hG.contMDiffAt.comp q (hpair q)
    intro q hq
    have h := (contMDiff_planeLift_up.{u}.contMDiffAt.comp q (hF q hq)).contMDiffWithinAt
      (s := circleCollarSource)
    refine h.congr (fun q' hq' => ?_) ?_
    · change ULift.up (discCollarMap.{u} p q').val.down = _
      rw [discCollarMap_val p hq']
      rfl
    · change ULift.up (discCollarMap.{u} p q).val.down = _
      rw [discCollarMap_val p hq]
      rfl
  contMDiffOn_invFun := by
    have hne : ∀ x ∈ discCollarTarget.{u} p, x.val.down ≠ 0 := fun x hx =>
      norm_ne_zero_iff.mp (ne_zero_of_neg_seamDepth_lt p hx)
    have hfirst : ContMDiffOn (𝓡∂ 2) (𝓡 1) ∞ (fun x : discSet.{u} => unitOf x.val.down)
        (discCollarTarget p) :=
      contMDiffOn_unitOf.comp contMDiff_discSet_down.contMDiffOn fun x hx => hne x hx
    have hnorm : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ, ℝ) ∞
        (fun x : discSet.{u} => -seamDepth p ‖x.val.down‖) (discCollarTarget p) := by
      intro x hx
      have hn : ContMDiffAt (𝓡∂ 2) 𝓘(ℝ, ℝ) ∞ (fun x : discSet.{u} => ‖x.val.down‖) x :=
        (contDiffAt_norm ℝ (hne x hx)).contMDiffAt.comp x (contMDiff_discSet_down x)
      exact ((contDiff_seamDepth p).neg.contMDiff.contMDiffAt.comp x hn).contMDiffWithinAt
    have hsecond : ContMDiffOn (𝓡∂ 2) (𝓡∂ 1) ∞
        (fun x : discSet.{u} => Manifold.halfSpaceOneLift (-seamDepth p ‖x.val.down‖))
        (discCollarTarget p) :=
      Manifold.contMDiffOn_halfSpaceOneLift.comp hnorm fun x _ => neg_seamDepth_nonneg p x
    exact hfirst.prodMk hsecond

theorem discCollar_apply_val (p : ℕ) [NeZero p] {q : Circle × EuclideanHalfSpace 1}
    (hq : q ∈ circleCollarSource) :
    (discCollar.{u} p q).val.down = seamRadius p (-q.2.val 0) • (q.1 : ℂ) :=
  discCollarMap_val p hq

theorem discCollar_zero_val (p : ℕ) [NeZero p] (t : Circle) :
    (discCollar.{u} p (t, halfZero)).val.down = (3 : ℝ) • (t : ℂ) := by
  rw [discCollar_apply_val p (halfZero_mem_circleCollarSource t)]
  change seamRadius p (-(0 : ℝ)) • (t : ℂ) = _
  rw [neg_zero, seamRadius_zero]

theorem discSet_boundary_eq (p : ℕ) [NeZero p] :
    (𝓡∂ 2).boundary discSet.{u} = ⋃ _ : Fin 1, range fun t => discCollar.{u} p (t, halfZero) := by
  rw [iUnion_const]
  ext x
  change (𝓡∂ 2).IsBoundaryPoint x ↔ _
  rw [discSet_isBoundaryPoint_iff]
  constructor
  · intro hx
    refine ⟨unitOf x.val.down, ?_⟩
    apply Subtype.ext
    apply ULift.ext
    change (discCollar.{u} p (unitOf x.val.down, halfZero)).val.down = x.val.down
    rw [discCollar_zero_val, ← hx, norm_smul_unitOf]
  · rintro ⟨t, rfl⟩
    rw [discCollar_zero_val, norm_smul, Circle.norm_coe, mul_one]
    norm_num

def discPlanarBase (p : ℕ) [NeZero p] : PlanarBase.{u} 1 where
  surface := discSurface
  collar _ := discCollar p
  source_eq _ := rfl
  boundary_zero _ t := by
    have h := (discSet_boundary_eq.{u} p).symm ▸
      (mem_iUnion.mpr ⟨0, t, rfl⟩ : discCollar.{u} p (t, halfZero) ∈
        ⋃ _ : Fin 1, range fun t => discCollar.{u} p (t, halfZero))
    exact h
  disjoint i j hij := (hij (Subsingleton.elim i j)).elim
  boundary_exhausted := discSet_boundary_eq p
  embedding x := x.val.down
  isSmoothEmbedding :=
    ⟨(discAtlas.{u}.isSmoothEmbedding_subtype_val.isImmersion.comp_diffeomorph
      (uliftDiffeomorph 𝓘(ℝ, ℂ) ℂ).symm),
    (Homeomorph.ulift : PlaneLift.{u} ≃ₜ ℂ).isEmbedding.comp
      _root_.Topology.IsEmbedding.subtypeVal⟩
  range_embedding := by
    rw [planarModel_one]
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact mem_closedBall_zero_iff.mpr ((mem_discSet_iff x.val).mp x.2)
    · intro hz
      exact ⟨⟨ULift.up z, (mem_discSet_iff (ULift.up z)).mpr (mem_closedBall_zero_iff.mp hz)⟩,
        rfl⟩
  embedding_collar j t := by
    rw [Subsingleton.elim j 0]
    change (discCollar.{u} p (t, halfZero)).val.down = _
    rw [discCollar_zero_val]
    simp [planarCircleMap, planarCenter, planarRadius, Complex.real_smul]

def solidSet : Set (PlaneLift.{u} × Circle) := {x | sqDist 0 3 x.1.down ≤ 0}

theorem mem_solidSet_iff (x : PlaneLift.{u} × Circle) : x ∈ solidSet ↔ ‖x.1.down‖ ≤ 3 :=
  mem_discSet_iff x.1

theorem contMDiff_solidFunction : ContMDiff (𝓘(ℝ, ℂ).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞
    (fun x : PlaneLift.{u} × Circle => sqDist 0 3 x.1.down) :=
  contMDiff_discFunction.comp contMDiff_fst

theorem solidFunction_regular (x : PlaneLift.{u} × Circle) (hx : sqDist 0 3 x.1.down = 0) :
    mfderiv (𝓘(ℝ, ℂ).prod (𝓡 1)) 𝓘(ℝ, ℝ)
      (fun x : PlaneLift.{u} × Circle => sqDist 0 3 x.1.down) x ≠ 0 := by
  refine mfderiv_ne_zero_of_comp (J := 𝓘(ℝ, ℂ))
    (s := fun w : ℂ => ((ULift.up w : PlaneLift.{u}), x.2)) (y := x.1.down)
    (contMDiff_solidFunction.mdifferentiableAt (by simp))
    ((contMDiff_planeLift_up.prodMk contMDiff_const).mdifferentiableAt (by simp)) ?_
  change mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (sqDist 0 3) x.1.down ≠ 0
  rw [mfderiv_eq_fderiv]
  exact fderiv_sqDist_ne_zero (by norm_num) hx

def solidAtlas : SmoothBoundaryAtlas (𝓘(ℝ, ℂ).prod (𝓡 1)) 3 solidSet.{u} :=
  SmoothBoundaryAtlas.regularSublevel (𝓘(ℝ, ℂ).prod (𝓡 1)) (n := 2) finrank_planeCircleModel
    contMDiff_solidFunction.{u} 0 solidFunction_regular

instance : ChartedSpace (EuclideanHalfSpace 3) solidSet.{u} := solidAtlas.toChartedSpace

instance : IsManifold (𝓡∂ 3) ∞ solidSet.{u} := solidAtlas.isManifold

theorem solidSet_isBoundaryPoint_iff (x : solidSet.{u}) :
    (𝓡∂ 3).IsBoundaryPoint x ↔ ‖x.val.1.down‖ = 3 :=
  (SmoothBoundaryAtlas.regularSublevel_isBoundaryPoint_iff (𝓘(ℝ, ℂ).prod (𝓡 1)) (n := 2)
    finrank_planeCircleModel contMDiff_solidFunction 0 solidFunction_regular x).trans (by
      rw [sqDist_eq_zero_iff 0 (by norm_num), sub_zero])

theorem solidSet_isInteriorPoint_iff (x : solidSet.{u}) :
    (𝓡∂ 3).IsInteriorPoint x ↔ ‖x.val.1.down‖ < 3 :=
  (SmoothBoundaryAtlas.regularSublevel_isInteriorPoint_iff (𝓘(ℝ, ℂ).prod (𝓡 1)) (n := 2)
    finrank_planeCircleModel contMDiff_solidFunction 0 solidFunction_regular x).trans (by
      rw [sqDist_neg_iff 0 (by norm_num), sub_zero])

theorem solidSet_eq_prod : solidSet.{u} = discSet ×ˢ univ := by
  ext x
  simp [solidSet, discSet]

instance : CompactSpace solidSet.{u} :=
  isCompact_iff_compactSpace.mp (by
    rw [solidSet_eq_prod]
    exact isCompact_discSet.prod isCompact_univ)

def solidDiffeomorph :
    (discSet.{u} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), 𝓡∂ 3⟯ solidSet.{u} where
  toFun q := ⟨(q.1.val, q.2), q.1.2⟩
  invFun x := (⟨x.val.1, x.2⟩, x.val.2)
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := (solidAtlas.contMDiff_iff_subtype_val _).mpr
    ((discAtlas.contMDiff_subtype_val.comp contMDiff_fst).prodMk contMDiff_snd)
  contMDiff_invFun :=
    ((discAtlas.contMDiff_iff_subtype_val _).mpr
      (contMDiff_fst.comp solidAtlas.contMDiff_subtype_val)).prodMk
      (contMDiff_snd.comp solidAtlas.contMDiff_subtype_val)

instance : ConnectedSpace solidSet.{u} := by
  have : ConnectedSpace discSet.{u} := discSurface.{u}.connected
  exact solidDiffeomorph.{u}.toHomeomorph.connectedSpace_iff.mp inferInstance

instance : Nonempty solidSet.{u} := ⟨solidDiffeomorph (⟨ULift.up 0, by
  rw [mem_discSet_iff]
  norm_num⟩, 1)⟩

def solidCollarMap (p : ℕ) [NeZero p] (q : Torus × EuclideanHalfSpace 1) : solidSet.{u} :=
  solidDiffeomorph (discCollar p (q.1.1, q.2), q.1.2)

def solidCollarInv (p : ℕ) [NeZero p] (x : solidSet.{u}) : Torus × EuclideanHalfSpace 1 :=
  ((((discCollar p).symm (solidDiffeomorph.symm x).1).1, (solidDiffeomorph.symm x).2),
    ((discCollar p).symm (solidDiffeomorph.symm x).1).2)

def solidCollar (p : ℕ) [NeZero p] :
    PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1) solidSet.{u} ∞ where
  toFun := solidCollarMap p
  invFun := solidCollarInv p
  source := halfCollarSource
  target := {x | (solidDiffeomorph.{u}.symm x).1 ∈ (discCollar.{u} p).target}
  map_source' q hq := (discCollar.{u} p).map_source' hq
  map_target' x hx := (discCollar.{u} p).map_target' hx
  left_inv' q hq := by
    have h : (discCollar.{u} p).symm (discCollar.{u} p (q.1.1, q.2)) = (q.1.1, q.2) :=
      (discCollar.{u} p).left_inv hq
    change ((((discCollar.{u} p).symm (discCollar.{u} p (q.1.1, q.2))).1, q.1.2),
      ((discCollar.{u} p).symm (discCollar.{u} p (q.1.1, q.2))).2) = q
    rw [h]
  right_inv' x hx := by
    have h : discCollar.{u} p ((discCollar.{u} p).symm (solidDiffeomorph.{u}.symm x).1) =
        (solidDiffeomorph.{u}.symm x).1 := (discCollar.{u} p).right_inv hx
    change solidDiffeomorph.{u} (discCollar.{u} p
      ((discCollar.{u} p).symm (solidDiffeomorph.{u}.symm x).1),
      (solidDiffeomorph.{u}.symm x).2) = x
    rw [h]
    exact solidDiffeomorph.{u}.apply_symm_apply x
  open_source := isOpen_lt
    ((EuclideanSpace.proj 0).continuous.comp (continuous_subtype_val.comp continuous_snd))
    continuous_const
  open_target := (discCollar.{u} p).open_target.preimage
    (continuous_fst.comp solidDiffeomorph.{u}.symm.continuous)
  contMDiffOn_toFun := by
    have hr : ContMDiff halfCollarModel circleCollarModel ∞
        (fun q : Torus × EuclideanHalfSpace 1 => (q.1.1, q.2)) :=
      (contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd
    exact solidDiffeomorph.{u}.contMDiff.comp_contMDiffOn
      (((discCollar.{u} p).contMDiffOn.comp hr.contMDiffOn fun q hq => hq).prodMk
        (contMDiff_snd.comp contMDiff_fst).contMDiffOn)
  contMDiffOn_invFun := by
    have hg : ContMDiffOn (𝓡∂ 3) circleCollarModel ∞
        (fun x => (discCollar.{u} p).symm (solidDiffeomorph.{u}.symm x).1)
        {x | (solidDiffeomorph.{u}.symm x).1 ∈ (discCollar.{u} p).target} :=
      (discCollar.{u} p).contMDiffOn_invFun.comp
        (contMDiff_fst.comp solidDiffeomorph.{u}.symm.contMDiff).contMDiffOn fun x hx => hx
    exact ((contMDiff_fst.comp_contMDiffOn hg).prodMk
      (contMDiff_snd.comp solidDiffeomorph.{u}.symm.contMDiff).contMDiffOn).prodMk
      (contMDiff_snd.comp_contMDiffOn hg)

theorem solidCollar_apply (p : ℕ) [NeZero p] (q : Torus × EuclideanHalfSpace 1) :
    solidCollar.{u} p q = solidDiffeomorph (discCollar p (q.1.1, q.2), q.1.2) :=
  rfl

theorem solidCollar_apply_val (p : ℕ) [NeZero p] {q : Torus × EuclideanHalfSpace 1}
    (hq : q ∈ halfCollarSource) :
    (solidCollar.{u} p q).val = (ULift.up (seamRadius p (-q.2.val 0) • (q.1.1 : ℂ)), q.1.2) := by
  change ((discCollar.{u} p (q.1.1, q.2)).val, q.1.2) = _
  rw [Prod.ext_iff]
  exact ⟨ULift.ext (discCollar_apply_val p hq), rfl⟩

theorem solidCollar_zero_val (p : ℕ) [NeZero p] (t : Torus) :
    (solidCollar.{u} p (t, halfZero)).val = (ULift.up ((3 : ℝ) • (t.1 : ℂ)), t.2) := by
  rw [solidCollar_apply_val p (zero_mem_halfCollarSource t)]
  change (ULift.up (seamRadius p (-(0 : ℝ)) • (t.1 : ℂ)), t.2) = _
  rw [neg_zero, seamRadius_zero]

theorem solidSet_boundary_eq (p : ℕ) [NeZero p] :
    (𝓡∂ 3).boundary solidSet.{u} = range fun t => solidCollar.{u} p (t, halfZero) := by
  ext x
  change (𝓡∂ 3).IsBoundaryPoint x ↔ _
  rw [solidSet_isBoundaryPoint_iff]
  constructor
  · intro hx
    refine ⟨(unitOf x.val.1.down, x.val.2), ?_⟩
    apply Subtype.ext
    rw [solidCollar_zero_val]
    refine Prod.ext (ULift.ext ?_) rfl
    change (3 : ℝ) • (unitOf x.val.1.down : ℂ) = x.val.1.down
    rw [← hx, norm_smul_unitOf]
  · rintro ⟨t, rfl⟩
    rw [solidCollar_zero_val]
    change ‖(3 : ℝ) • (t.1 : ℂ)‖ = 3
    rw [norm_smul, Circle.norm_coe, mul_one]
    norm_num

end GC.Seifert
