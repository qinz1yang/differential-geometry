import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.LensSolidTorus

/-!
# The seam of a twisted cover

For a twisted cover `T : TwistedCover p e W`, the Clifford collar
`(u, v, s) ↦ (u v'^e √((1 + s) / 2), v' √((1 - s) / 2))`, with `v'` any `p`-th root of `v`,
descends to a partial diffeomorphism `T.seam` from `Torus × (-1, 1)` onto `{-1 < T.height < 1}`
with `T.height (T.seam (t, s)) = s`. Its negative half is the half collar `T.collar` of the boundary
of the solid torus `T.pieceSet`, and the boundary torus `T.torusPoint t = T.collar (t, 0)` has disc
and circle coordinates `t` under `T.pieceDiffeo` (`T.pieceDiffeo_torusPoint`). The interior of the
piece is connected.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold

attribute [local instance] fact_finrank_euclideanSpace_four finrank_real_complex_fact'

theorem cliffordSeamMap_circle_mul (u v a b : Circle) (s : ℝ) :
    cliffordSeamMap.{0} ((u * a, v * b), s) = circlePairAct u v (cliffordSeamMap ((a, b), s)) := by
  apply sphere_ext
  · rw [sphereFirst_cliffordSeamMap, sphereFirst_circlePairAct, sphereFirst_cliffordSeamMap,
      Circle.coe_mul, mul_smul_comm]
  · rw [sphereSecond_cliffordSeamMap, sphereSecond_circlePairAct, sphereSecond_cliffordSeamMap,
      Circle.coe_mul, mul_smul_comm]

def twistSeamPoint (e : ℤ) (y : Torus × ℝ) (v : Circle) : LensSphere :=
  cliffordSeamMap ((y.1.1 * v ^ e, v), y.2)

theorem twistSeamPoint_toCircle_mul {p : ℕ} [NeZero p] (e : ℤ) (y : Torus × ℝ) (v : Circle)
    (j : ZMod p) :
    twistSeamPoint e y (ZMod.toCircle j * v) = lensTwist p e j (twistSeamPoint e y v) := by
  rw [twistSeamPoint, twistSeamPoint, lensTwist, ← cliffordSeamMap_circle_mul,
    toCircle_mul_eq_zpow, mul_zpow, mul_left_comm]

def twistSeamInv (p : ℕ) (e : ℤ) (x : LensSphere) : Torus × ℝ :=
  ((unitOf (sphereFirst x) * unitOf (sphereSecond x) ^ (-e), unitOf (sphereSecond x) ^ p),
    cliffordHeight x)

theorem twistSeamInv_lensTwist {p : ℕ} [NeZero p] {e : ℤ} {x : LensSphere}
    (h₁ : sphereFirst x ≠ 0) (h₂ : sphereSecond x ≠ 0) (j : ZMod p) :
    twistSeamInv p e (lensTwist p e j x) = twistSeamInv p e x := by
  have hh : cliffordHeight (lensTwist p e j x) = cliffordHeight x :=
    cliffordHeight_circlePairAct _ _ x
  rw [twistSeamInv, twistSeamInv, unitOf_sphereFirst_lensTwist h₁, unitOf_sphereSecond_lensTwist h₂,
    hh, mul_zpow, mul_pow, toCircle_pow_self, one_mul, mul_comm (ZMod.toCircle j ^ e),
    mul_assoc, zpow_neg (ZMod.toCircle j) e, mul_inv_cancel_left]

theorem contMDiffAt_twistSeamInv (p : ℕ) (e : ℤ) {x : LensSphere} (h₁ : sphereFirst x ≠ 0)
    (h₂ : sphereSecond x ≠ 0) :
    ContMDiffAt (𝓡 3) signedCollarModel ∞ (twistSeamInv p e) x :=
  (((contMDiffAt_unitOf_sphereFirst h₁).mul
    ((GC.Seifert.contMDiff_circle_zpow (-e)).contMDiffAt.comp x
      (contMDiffAt_unitOf_sphereSecond h₂))).prodMk
    ((contMDiff_pow p).contMDiffAt.comp x (contMDiffAt_unitOf_sphereSecond h₂))).prodMk
    contMDiff_cliffordHeight.contMDiffAt

theorem contMDiffAt_twistSeamPoint (e : ℤ) {y : Torus × ℝ} (hy : y ∈ signedCollarSource)
    (v : Circle) :
    ContMDiffAt (signedCollarModel.prod (𝓡 1)) (𝓡 3) ∞
      (fun z : (Torus × ℝ) × Circle => twistSeamPoint e z.1 z.2) (y, v) := by
  have hg : ContMDiff (signedCollarModel.prod (𝓡 1)) signedCollarModel ∞
      (fun z : (Torus × ℝ) × Circle => ((z.1.1.1 * z.2 ^ e, z.2), z.1.2)) :=
    (((contMDiff_fst.comp (contMDiff_fst.comp contMDiff_fst)).mul
      ((GC.Seifert.contMDiff_circle_zpow e).comp contMDiff_snd)).prodMk contMDiff_snd).prodMk
      (contMDiff_snd.comp contMDiff_fst)
  have hmem : ((y.1.1 * v ^ e, v), y.2) ∈ cliffordSeam.{0}.source := hy
  exact (cliffordSeam.{0}.contMDiffOn.contMDiffAt
    (cliffordSeam.{0}.open_source.mem_nhds hmem)).comp (y, v) hg.contMDiffAt

theorem mem_cliffordSeamTarget_of_height {x : LensSphere}
    (h : -1 < cliffordHeight x ∧ cliffordHeight x < 1) : x ∈ cliffordSeamTarget.{0} := by
  have h₁ := norm_sphereFirst_sq_eq x
  have h₂ := norm_sphereSecond_sq_eq x
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · rw [h0, norm_zero] at h₁
    linarith [h.1]
  · rw [h0, norm_zero] at h₂
    linarith [h.2]

theorem sqrt_two_mul_seamFirst_zero' : (√2 : ℝ) * seamFirst 0 = 1 := by
  rw [seamFirst, seamClamp_of_mem (by norm_num) (by norm_num), ← Real.sqrt_mul (by norm_num)]
  norm_num

theorem halfPoint_congr {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a = b) :
    halfPoint a ha = halfPoint b hb := by
  subst h
  rfl

namespace TwistedCover

variable {p : ℕ} [NeZero p] {e : ℤ} {W : Type} [TopologicalSpace W]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) W] (T : TwistedCover p e W)

def seamMap (y : Torus × ℝ) : W := T.cover (twistSeamPoint e y (circleRootOf p y.1.2))

def seamInv : W → Torus × ℝ := T.descend (twistSeamInv p e)

def seamTarget : Set W := {w | -1 < T.height w ∧ T.height w < 1}

theorem height_seamMap (y : Torus × ℝ) : T.height (T.seamMap y) = seamClamp y.2 := by
  rw [seamMap, height_cover, twistSeamPoint, cliffordHeight_cliffordSeamMap]

theorem seamInv_snd (w : W) : (T.seamInv w).2 = T.height w := rfl

theorem seamInv_cover {x : LensSphere} (h₁ : sphereFirst x ≠ 0) (h₂ : sphereSecond x ≠ 0) :
    T.seamInv (T.cover x) = twistSeamInv p e x :=
  T.descend_cover (twistSeamInv_lensTwist h₁ h₂)

theorem seamMap_eq_cover {y : Torus × ℝ} {v : Circle} (hv : v ^ p = y.1.2) :
    T.seamMap y = T.cover (twistSeamPoint e y v) :=
  T.cover_root_eq_of_pow (fun v j => twistSeamPoint_toCircle_mul e y v j) hv

theorem seamInv_seamMap {y : Torus × ℝ} (hy : y ∈ signedCollarSource) :
    T.seamInv (T.seamMap y) = y := by
  obtain ⟨⟨a, b⟩, s⟩ := y
  have hmem : ((a * circleRootOf p b ^ e, circleRootOf p b), s) ∈ cliffordSeam.{0}.source := hy
  have hl : cliffordSeamInv (cliffordSeamMap ((a * circleRootOf p b ^ e, circleRootOf p b), s)) =
      ((a * circleRootOf p b ^ e, circleRootOf p b), s) := cliffordSeam.{0}.left_inv hmem
  have hx : cliffordSeamMap ((a * circleRootOf p b ^ e, circleRootOf p b), s) ∈
      cliffordSeamTarget := cliffordSeam.{0}.map_source hmem
  have hpt : T.seamMap ((a, b), s) =
      T.cover (cliffordSeamMap ((a * circleRootOf p b ^ e, circleRootOf p b), s)) := rfl
  rw [hpt, seamInv_cover T hx.1 hx.2, twistSeamInv]
  simp only [cliffordSeamInv, Prod.mk.injEq] at hl
  obtain ⟨⟨h1, h2⟩, h3⟩ := hl
  rw [h1, h2, h3, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one, circleRootOf_pow]

theorem seamMap_seamInv {w : W} (hw : w ∈ T.seamTarget) : T.seamMap (T.seamInv w) = w := by
  have hx : T.lift w ∈ cliffordSeamTarget.{0} := mem_cliffordSeamTarget_of_height hw
  have hr := cliffordSeam.{0}.right_inv hx
  change cliffordSeamMap (cliffordSeamInv (T.lift w)) = T.lift w at hr
  have hv : unitOf (sphereSecond (T.lift w)) ^ p = (T.seamInv w).1.2 := rfl
  rw [T.seamMap_eq_cover hv]
  conv_rhs => rw [← T.cover_lift w, ← hr]
  congr 1
  change cliffordSeamMap (((unitOf (sphereFirst (T.lift w)) *
    unitOf (sphereSecond (T.lift w)) ^ (-e)) * unitOf (sphereSecond (T.lift w)) ^ e,
    unitOf (sphereSecond (T.lift w))), cliffordHeight (T.lift w)) = _
  rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  rfl

theorem isOpen_seamTarget : IsOpen T.seamTarget :=
  (isOpen_lt continuous_const T.contMDiff_height.continuous).inter
    (isOpen_lt T.contMDiff_height.continuous continuous_const)

def seam : PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) W ∞ where
  toFun := T.seamMap
  invFun := T.seamInv
  source := signedCollarSource
  target := T.seamTarget
  map_source' y hy := by
    change -1 < T.height (T.seamMap y) ∧ T.height (T.seamMap y) < 1
    rw [height_seamMap, seamClamp_of_mem hy.1.le hy.2.le]
    exact hy
  map_target' _ hw := hw
  left_inv' _ hy := T.seamInv_seamMap hy
  right_inv' _ hw := T.seamMap_seamInv hw
  open_source := isOpen_signedCollarSource
  open_target := T.isOpen_seamTarget
  contMDiffOn_toFun y hy :=
    (T.contMDiffAt_cover_root (f := fun y : Torus × ℝ => y.1.2)
      (contMDiff_snd.comp contMDiff_fst).contMDiffAt (Ψ := twistSeamPoint e)
      (contMDiffAt_twistSeamPoint e hy)
      (fun y v j => twistSeamPoint_toCircle_mul e y v j)).contMDiffWithinAt
  contMDiffOn_invFun w hw := by
    have hx : T.lift w ∈ cliffordSeamTarget.{0} := mem_cliffordSeamTarget_of_height hw
    have hev : ∀ᶠ y in 𝓝 (T.lift w), ∀ j, twistSeamInv p e (lensTwist p e j y) =
        twistSeamInv p e y := by
      filter_upwards [isOpen_cliffordSeamTarget.{0}.mem_nhds hx] with y hy j
      exact twistSeamInv_lensTwist hy.1 hy.2 j
    have h := T.contMDiffAt_descend hev (contMDiffAt_twistSeamInv p e hx.1 hx.2)
    rw [T.cover_lift] at h
    exact h.contMDiffWithinAt

theorem seam_apply (y : Torus × ℝ) : T.seam y = T.seamMap y := rfl

theorem seam_symm_apply (w : W) : T.seam.symm w = T.seamInv w := rfl

theorem seam_source : T.seam.source = signedCollarSource := rfl

theorem seam_target : T.seam.target = T.seamTarget := rfl

theorem height_seamMap_of_mem {y : Torus × ℝ} (hy : y ∈ signedCollarSource) :
    T.height (T.seamMap y) = y.2 := by
  rw [height_seamMap, seamClamp_of_mem hy.1.le hy.2.le]

variable [IsManifold (𝓡 3) ∞ W]

def collarMap (y : Torus × EuclideanHalfSpace 1) : T.pieceSet :=
  ⟨T.seamMap (y.1, -y.2.val 0), by
    change T.height _ ≤ 0
    rw [height_seamMap]
    exact seamClamp_neg_nonpos y.2.2⟩

def collarInv (w : T.pieceSet) : Torus × EuclideanHalfSpace 1 :=
  ((T.seamInv w.val).1, halfPoint (-T.height w.val) (neg_nonneg.mpr w.2))

theorem neg_halfCoord_mem {y : Torus × EuclideanHalfSpace 1} (hy : y ∈ halfCollarSource) :
    (y.1, -y.2.val 0) ∈ signedCollarSource := by
  have h1 : y.2.val 0 < 1 := hy
  have h0 : 0 ≤ y.2.val 0 := y.2.2
  exact ⟨by linarith, by linarith⟩

def collar :
    PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1) T.pieceSet ∞ where
  toFun := T.collarMap
  invFun := T.collarInv
  source := halfCollarSource
  target := {w | -1 < T.height w.val}
  map_source' y hy := by
    change -1 < T.height (T.seamMap (y.1, -y.2.val 0))
    rw [T.height_seamMap_of_mem (neg_halfCoord_mem hy)]
    exact (neg_halfCoord_mem hy).1
  map_target' w hw := by
    change -T.height w.val < 1
    have hw' : -1 < T.height w.val := hw
    linarith
  left_inv' y hy := by
    have hs := neg_halfCoord_mem hy
    have hl := T.seamInv_seamMap hs
    have h1 := congrArg Prod.fst hl
    refine Prod.ext h1 ?_
    change halfPoint (-T.height (T.seamMap (y.1, -y.2.val 0))) _ = y.2
    exact (halfPoint_congr _ y.2.2 (by rw [T.height_seamMap_of_mem hs, neg_neg])).trans
      (halfPoint_coord_eq y.2)
  right_inv' w hw := by
    apply Subtype.ext
    change T.seamMap ((T.seamInv w.val).1, -(halfPoint (-T.height w.val) _).val 0) = w.val
    rw [halfPoint_val_zero, neg_neg]
    have hw' : -1 < T.height w.val := hw
    exact T.seamMap_seamInv ⟨hw', by linarith [show T.height w.val ≤ 0 from w.2]⟩
  open_source := isOpen_lt
    ((EuclideanSpace.proj 0).continuous.comp (continuous_subtype_val.comp continuous_snd))
    continuous_const
  open_target := isOpen_lt continuous_const
    (T.contMDiff_height.continuous.comp continuous_subtype_val)
  contMDiffOn_toFun := by
    rw [T.contMDiffOn_piece_iff]
    have hmap : ContMDiff halfCollarModel signedCollarModel ∞
        (fun q : Torus × EuclideanHalfSpace 1 => (q.1, -q.2.val 0)) :=
      contMDiff_fst.prodMk (Manifold.contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd).neg
    exact T.seam.contMDiffOn.comp hmap.contMDiffOn (fun q hq => neg_halfCoord_mem hq)
  contMDiffOn_invFun := by
    have hval := T.contMDiff_piece_val
    have htorus : ContMDiffOn (𝓡∂ 3) torusModel ∞ (fun w : T.pieceSet => (T.seamInv w.val).1)
        {w | -1 < T.height w.val} := by
      have h := T.seam.symm.contMDiffOn.comp hval.contMDiffOn (fun w (hw : -1 < T.height w.val) =>
        (⟨hw, by linarith [show T.height w.val ≤ 0 from w.2]⟩ : w.val ∈ T.seamTarget))
      exact contMDiff_fst.comp_contMDiffOn h
    have hheight : ContMDiff (𝓡∂ 3) (𝓡∂ 1) ∞
        (fun w : T.pieceSet => halfPoint (-T.height w.val) (neg_nonneg.mpr w.2)) := by
      have heq : (fun w : T.pieceSet => halfPoint (-T.height w.val) (neg_nonneg.mpr w.2)) =
          fun w => Manifold.halfSpaceOneLift (-T.height w.val) := by
        funext w
        exact halfPoint_eq_halfSpaceOneLift _ _
      rw [heq]
      intro w
      exact (Manifold.contMDiffOn_halfSpaceOneLift.comp
        (T.contMDiff_height.comp hval).neg.contMDiffOn
        (fun v _ => show (0 : ℝ) ≤ -T.height v.val from neg_nonneg.mpr v.2)) w trivial
    exact htorus.prodMk hheight.contMDiffOn

theorem collar_apply_val (y : Torus × EuclideanHalfSpace 1) :
    (T.collar y).val = T.seam (y.1, -y.2.val 0) := rfl

theorem collar_source : T.collar.source = halfCollarSource := rfl

def torusPoint (t : Torus) : T.pieceSet := T.collar (t, halfZero)

theorem torusPoint_val (t : Torus) : (T.torusPoint t).val = T.seam (t, 0) := by
  change T.seamMap (t, -halfZero.val 0) = T.seamMap (t, 0)
  rw [show halfZero.val 0 = 0 from rfl, neg_zero]

theorem zero_mem_signedCollarSource (t : Torus) : ((t, 0) : Torus × ℝ) ∈ signedCollarSource :=
  ⟨by norm_num, by norm_num⟩

theorem height_torusPoint (t : Torus) : T.height (T.torusPoint t).val = 0 := by
  rw [torusPoint_val]
  exact T.height_seamMap_of_mem (zero_mem_signedCollarSource t)

theorem continuous_torusPoint : Continuous T.torusPoint := by
  have hs : ContMDiff torusModel (𝓡∂ 3) ∞ (fun t : Torus => T.collar (t, halfZero)) :=
    T.collar.contMDiffOn.comp_contMDiff (contMDiff_id.prodMk contMDiff_const)
      halfZero_mem_halfCollarSource
  exact hs.continuous

theorem torusPoint_injective : Injective T.torusPoint := by
  intro t s h
  exact congrArg Prod.fst (T.collar.toOpenPartialHomeomorph.injOn
    (halfZero_mem_halfCollarSource t) (halfZero_mem_halfCollarSource s) h)

theorem exists_torusPoint_eq {w : T.pieceSet} (hw : T.height w.val = 0) :
    ∃ t, T.torusPoint t = w := by
  have hmem : w ∈ T.collar.target := by
    change -1 < T.height w.val
    rw [hw]
    norm_num
  refine ⟨(T.collar.symm w).1, ?_⟩
  have hinv : T.collar.symm w = ((T.collar.symm w).1, halfZero) := by
    refine Prod.ext rfl ?_
    change halfPoint (-T.height w.val) _ = halfZero
    exact halfPoint_congr _ le_rfl (by rw [hw, neg_zero])
  rw [torusPoint, ← hinv]
  exact T.collar.right_inv hmem

theorem pieceDiffeo_torusPoint (t : Torus) :
    (T.pieceDiffeo (T.torusPoint t)).1.down.val = t.1 ∧
      (T.pieceDiffeo (T.torusPoint t)).2 = t.2 := by
  have hval : (T.torusPoint t).val =
      T.cover (cliffordSeamMap ((t.1 * circleRootOf p t.2 ^ e, circleRootOf p t.2), 0)) :=
    T.torusPoint_val t
  have hmem : ((t.1 * circleRootOf p t.2 ^ e, circleRootOf p t.2), (0 : ℝ)) ∈
      cliffordSeam.{0}.source := zero_mem_signedCollarSource _
  have hl : cliffordSeamInv (cliffordSeamMap ((t.1 * circleRootOf p t.2 ^ e,
      circleRootOf p t.2), 0)) = ((t.1 * circleRootOf p t.2 ^ e, circleRootOf p t.2), 0) :=
    cliffordSeam.{0}.left_inv hmem
  simp only [cliffordSeamInv, Prod.mk.injEq] at hl
  obtain ⟨⟨-, h2⟩, -⟩ := hl
  have hne : sphereSecond (cliffordSeamMap.{0}
      ((t.1 * circleRootOf p t.2 ^ e, circleRootOf p t.2), 0)) ≠ 0 :=
    (cliffordSeam.{0}.map_source hmem).2
  constructor
  · change T.discValue (T.torusPoint t).val = t.1
    have hsf : (√2 : ℝ) * seamFirst (((t.1 * circleRootOf p t.2 ^ e, circleRootOf p t.2),
        (0 : ℝ)) : Torus × ℝ).2 = 1 := sqrt_two_mul_seamFirst_zero'
    rw [hval, T.discValue_cover hne, twistDiscValue, h2, sphereFirst_cliffordSeamMap, smul_smul,
      hsf, one_smul, Circle.coe_mul, mul_left_comm, circle_zpow_neg_mul_cancel, mul_one]
  · change T.fiberValue (T.torusPoint t).val = t.2
    rw [hval, T.fiberValue_cover hne, twistFiberValue, h2, circleRootOf_pow]

omit [IsManifold (𝓡 3) ∞ W] in
theorem norm_toDiscCircle_sq (w : T.pieceSet) :
    ‖(T.toDiscCircle w).1.down.val‖ ^ 2 = 1 + T.height w.val :=
  norm_twistDiscValue_sq e (T.lift w.val)

theorem piece_interior_eq_image :
    {w : T.pieceSet | T.height w.val < 0} =
      T.pieceDiffeo.symm '' ({d : UnitDisc.{0} | ‖d.down.val‖ ^ 2 < 1} ×ˢ univ) := by
  rw [show T.pieceDiffeo.symm '' ({d : UnitDisc.{0} | ‖d.down.val‖ ^ 2 < 1} ×ˢ univ)
      = T.pieceDiffeo ⁻¹' ({d : UnitDisc.{0} | ‖d.down.val‖ ^ 2 < 1} ×ˢ univ) from
    congrFun (T.pieceDiffeo.toHomeomorph.image_symm) _]
  ext w
  change T.height w.val < 0 ↔ ‖(T.toDiscCircle w).1.down.val‖ ^ 2 < 1 ∧ True
  rw [norm_toDiscCircle_sq, and_true]
  constructor <;> intro h <;> linarith

theorem isConnected_piece_interior : IsConnected {w : T.pieceSet | T.height w.val < 0} := by
  rw [piece_interior_eq_image]
  exact (isConnected_unitDisc_interior.prod isConnected_univ).image _
    T.pieceDiffeo.symm.continuous.continuousOn

instance instConnectedSpacePiece : ConnectedSpace T.pieceSet :=
  T.pieceDiffeo.toHomeomorph.connectedSpace_iff.mpr inferInstance

instance instNonemptyPiece : Nonempty T.pieceSet := ⟨T.torusPoint 1⟩

end TwistedCover

end GC.GraphManifold
