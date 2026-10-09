import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.LensCover
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClassicalInputs

/-!
# Solid tori in quotients of the three-sphere

Let `T : TwistedCover p e W` be a twisted cover. The Clifford height `‖z₁‖² - ‖z₂‖²` is invariant
under the twisted action, so it descends to a function `T.height` on `W` which is regular on its
zero level. Its sublevel set `T.pieceSet = {T.height ≤ 0}`, the image of the solid torus
`‖z₁‖ ≤ ‖z₂‖`, is a compact manifold with boundary. The invariants
`w = √2 z₁ (z₂ / ‖z₂‖)^{-e}` and `t = (z₂ / ‖z₂‖)^p` identify it with the closed disc times the
circle (`T.pieceDiffeo`); the inverse sends `(w, t)` to the class of
`(w v^e / √2, √(1 - ‖w‖² / 2) v)` for any `p`-th root `v` of `t`.

The map `(u, v, s) ↦ (u v'^e √((1 + s) / 2), v' √((1 - s) / 2))` with `v'^p = v` descends to a
signed collar `T.seam` of the torus `{T.height = 0}`, with inverse given by
`(z₁, z₂) ↦ ((z₁/‖z₁‖) (z₂/‖z₂‖)^{-e}, (z₂/‖z₂‖)^p, ‖z₁‖² - ‖z₂‖²)`. Its negative half is the
half collar `T.collar` of the boundary of the piece, whose boundary torus `T.torusPoint` has disc
and circle coordinates `(t.1, t.2)` (`T.pieceDiffeo_torusPoint`).
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold

attribute [local instance] fact_finrank_euclideanSpace_four finrank_real_complex_fact'

def discRotate (u : Circle) (w : UnitDisc.{0}) : UnitDisc.{0} :=
  ULift.up ⟨(u : ℂ) * w.down.val, by
    change ‖(u : ℂ) * w.down.val‖ ^ 2 ≤ 1
    rw [norm_circle_mul]
    exact w.down.2⟩

theorem discRotate_val (u : Circle) (w : UnitDisc.{0}) :
    (discRotate u w).down.val = (u : ℂ) * w.down.val := rfl

theorem discRotate_discRotate (u v : Circle) (w : UnitDisc.{0}) :
    discRotate u (discRotate v w) = discRotate (u * v) w := by
  apply ULift.ext
  apply Subtype.ext
  rw [discRotate_val, discRotate_val, discRotate_val, Circle.coe_mul, mul_assoc]

theorem discRotate_one (w : UnitDisc.{0}) : discRotate 1 w = w := by
  apply ULift.ext
  apply Subtype.ext
  rw [discRotate_val, Circle.coe_one, one_mul]

theorem contMDiff_discRotate :
    ContMDiff ((𝓡 1).prod (𝓡∂ 2)) (𝓡∂ 2) ∞
      (fun q : Circle × UnitDisc.{0} => discRotate q.1 q.2) := by
  have hval : ContMDiff ((𝓡 1).prod (𝓡∂ 2)) 𝓘(ℝ, ℂ) ∞
      (fun q : Circle × UnitDisc.{0} => (q.1 : ℂ) * q.2.down.val) :=
    (contDiff_mul (𝕜 := ℝ)).contMDiff.comp
      ((contMDiff_circle_coe.comp contMDiff_fst).prodMk_space
        (contMDiff_disc_val.comp contMDiff_snd))
  have h : ContMDiff ((𝓡 1).prod (𝓡∂ 2)) (𝓡∂ 2) ∞
      (fun q : Circle × UnitDisc.{0} => (discRotate q.1 q.2).down) :=
    (unitDiscAtlas.contMDiff_iff_subtype_val _).mpr hval
  exact (uliftDiffeomorph (𝓡∂ 2) unitDiscSet).contMDiff.comp h

theorem toCircle_pow_self {p : ℕ} [NeZero p] (j : ZMod p) : ZMod.toCircle j ^ p = 1 := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
    AddChar.map_zero_eq_one]

theorem toCircle_mul_eq_zpow {p : ℕ} [NeZero p] (e : ℤ) (j : ZMod p) :
    ZMod.toCircle ((e : ZMod p) * j) = ZMod.toCircle j ^ e := by
  rw [← zsmul_eq_mul, AddChar.map_zsmul_eq_zpow]

theorem unitOf_sphereSecond_lensTwist {p : ℕ} [NeZero p] {e : ℤ} {x : LensSphere}
    (hx : sphereSecond x ≠ 0) (j : ZMod p) :
    unitOf (sphereSecond (lensTwist p e j x)) = ZMod.toCircle j * unitOf (sphereSecond x) := by
  rw [lensTwist, sphereSecond_circlePairAct, unitOf_circle_mul _ hx]

theorem unitOf_sphereFirst_lensTwist {p : ℕ} [NeZero p] {e : ℤ} {x : LensSphere}
    (hx : sphereFirst x ≠ 0) (j : ZMod p) :
    unitOf (sphereFirst (lensTwist p e j x)) = ZMod.toCircle j ^ e * unitOf (sphereFirst x) := by
  rw [lensTwist, sphereFirst_circlePairAct, unitOf_circle_mul _ hx, toCircle_mul_eq_zpow]

theorem circle_zpow_neg_mul_cancel (c : Circle) (e : ℤ) :
    ((c ^ (-e) : Circle) : ℂ) * ((c ^ e : Circle) : ℂ) = 1 := by
  rw [← Circle.coe_mul, ← zpow_add, neg_add_cancel, zpow_zero, Circle.coe_one]

def twistDiscValue (e : ℤ) (x : LensSphere) : ℂ :=
  ((unitOf (sphereSecond x) ^ (-e) : Circle) : ℂ) * ((√2 : ℝ) • sphereFirst x)

def twistFiberValue (p : ℕ) (x : LensSphere) : Circle := unitOf (sphereSecond x) ^ p

theorem twistDiscValue_lensTwist {p : ℕ} [NeZero p] {e : ℤ} {x : LensSphere}
    (hx : sphereSecond x ≠ 0) (j : ZMod p) :
    twistDiscValue e (lensTwist p e j x) = twistDiscValue e x := by
  have hc := circle_zpow_neg_mul_cancel (ZMod.toCircle j) e
  rw [twistDiscValue, twistDiscValue, unitOf_sphereSecond_lensTwist hx]
  rw [lensTwist, sphereFirst_circlePairAct, toCircle_mul_eq_zpow, mul_zpow, Circle.coe_mul,
    Complex.real_smul, Complex.real_smul]
  linear_combination ((unitOf (sphereSecond x) ^ (-e) : Circle) : ℂ) * (√2 : ℝ) *
    sphereFirst x * hc

theorem twistFiberValue_lensTwist {p : ℕ} [NeZero p] {e : ℤ} {x : LensSphere}
    (hx : sphereSecond x ≠ 0) (j : ZMod p) :
    twistFiberValue p (lensTwist p e j x) = twistFiberValue p x := by
  rw [twistFiberValue, twistFiberValue, unitOf_sphereSecond_lensTwist hx, mul_pow,
    toCircle_pow_self, one_mul]

theorem norm_twistDiscValue_sq (e : ℤ) (x : LensSphere) :
    ‖twistDiscValue e x‖ ^ 2 = 1 + cliffordHeight x := by
  rw [twistDiscValue, norm_circle_mul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    sqrt_two_sq, norm_sphereFirst_sq_eq]
  ring

theorem contMDiffAt_unitOf_sphereSecond {x : LensSphere} (hx : sphereSecond x ≠ 0) :
    ContMDiffAt (𝓡 3) (𝓡 1) ∞ (fun y : LensSphere => unitOf (sphereSecond y)) x :=
  (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hx)).comp x
    contMDiff_sphereSecond.contMDiffAt

theorem contMDiffAt_unitOf_sphereFirst {x : LensSphere} (hx : sphereFirst x ≠ 0) :
    ContMDiffAt (𝓡 3) (𝓡 1) ∞ (fun y : LensSphere => unitOf (sphereFirst y)) x :=
  (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hx)).comp x
    contMDiff_sphereFirst.contMDiffAt

theorem contMDiffAt_twistDiscValue (e : ℤ) {x : LensSphere} (hx : sphereSecond x ≠ 0) :
    ContMDiffAt (𝓡 3) 𝓘(ℝ, ℂ) ∞ (twistDiscValue e) x :=
  (contDiff_mul (𝕜 := ℝ)).contMDiff.contMDiffAt.comp x
    ((contMDiff_circle_coe.contMDiffAt.comp x
      ((GC.Seifert.contMDiff_circle_zpow (-e)).contMDiffAt.comp x
        (contMDiffAt_unitOf_sphereSecond hx))).prodMk_space
      ((contDiff_const_smul (√2 : ℝ)).contMDiff.contMDiffAt.comp x
        contMDiff_sphereFirst.contMDiffAt))

theorem contMDiffAt_twistFiberValue (p : ℕ) {x : LensSphere} (hx : sphereSecond x ≠ 0) :
    ContMDiffAt (𝓡 3) (𝓡 1) ∞ (twistFiberValue p) x :=
  ((contMDiff_pow p).contMDiffAt.comp x (contMDiffAt_unitOf_sphereSecond hx))

def sectionPoint (e : ℤ) (w : UnitDisc.{0}) (v : Circle) : LensSphere :=
  (solidTorusDiscCircle.{0}.symm (discRotate (v ^ e) w, v)).val

theorem sphereFirst_sectionPoint (e : ℤ) (w : UnitDisc.{0}) (v : Circle) :
    sphereFirst (sectionPoint e w v) = (√2 : ℝ)⁻¹ • (((v ^ e : Circle) : ℂ) * w.down.val) :=
  sphereFirst_sphereOfPair _ _ (norm_discCircle_sq (discRotate (v ^ e) w).down.2 v)

theorem sphereSecond_sectionPoint (e : ℤ) (w : UnitDisc.{0}) (v : Circle) :
    sphereSecond (sectionPoint e w v) = discCircleSecond w.down.val • (v : ℂ) := by
  have h : sphereSecond (sectionPoint e w v) =
      discCircleSecond (discRotate (v ^ e) w).down.val • (v : ℂ) :=
    sphereSecond_sphereOfPair _ _ (norm_discCircle_sq (discRotate (v ^ e) w).down.2 v)
  rw [h, discRotate_val, discCircleSecond, discCircleSecond, norm_circle_mul]

theorem sectionPoint_toCircle_mul {p : ℕ} [NeZero p] (e : ℤ) (w : UnitDisc.{0}) (v : Circle)
    (j : ZMod p) :
    sectionPoint e w (ZMod.toCircle j * v) = lensTwist p e j (sectionPoint e w v) := by
  apply sphere_ext
  · rw [lensTwist, sphereFirst_circlePairAct, sphereFirst_sectionPoint, sphereFirst_sectionPoint,
      toCircle_mul_eq_zpow, mul_zpow, Circle.coe_mul, mul_assoc, mul_smul_comm]
  · rw [lensTwist, sphereSecond_circlePairAct, sphereSecond_sectionPoint,
      sphereSecond_sectionPoint, Circle.coe_mul, mul_smul_comm]

theorem contMDiff_sectionPoint (e : ℤ) :
    ContMDiff ((𝓡∂ 2).prod (𝓡 1)) (𝓡 3) ∞
      (fun y : UnitDisc.{0} × Circle => sectionPoint e y.1 y.2) :=
  contMDiff_solidTorus_val.comp (solidTorusDiscCircle.symm.contMDiff.comp
    ((contMDiff_discRotate.comp (((GC.Seifert.contMDiff_circle_zpow e).comp contMDiff_snd).prodMk
      contMDiff_fst)).prodMk contMDiff_snd))

namespace TwistedCover

variable {p : ℕ} [NeZero p] {e : ℤ} {W : Type} [TopologicalSpace W]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) W] (T : TwistedCover p e W)

def height : W → ℝ := T.descend cliffordHeight

theorem height_cover (x : LensSphere) : T.height (T.cover x) = cliffordHeight x :=
  T.descend_cover fun _ => cliffordHeight_circlePairAct _ _ x

theorem height_lift (w : W) : cliffordHeight (T.lift w) = T.height w := rfl

theorem contMDiff_height : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ T.height := by
  intro w
  obtain ⟨x, rfl⟩ := T.surjective w
  exact T.contMDiffAt_descend (Eventually.of_forall fun y _ => cliffordHeight_circlePairAct _ _ y)
    contMDiff_cliffordHeight.contMDiffAt

theorem height_regular (w : W) (hw : T.height w = 0) :
    mfderiv (𝓡 3) 𝓘(ℝ, ℝ) T.height w ≠ 0 := by
  obtain ⟨x, rfl⟩ := T.surjective w
  rw [height_cover] at hw
  intro h0
  apply cliffordHeight_regular x hw
  have hcomp : T.height ∘ T.cover = cliffordHeight := funext T.height_cover
  rw [← hcomp, mfderiv_comp x (T.contMDiff_height.mdifferentiableAt (by simp))
    (T.contMDiff_cover.mdifferentiableAt (by simp)), h0, ContinuousLinearMap.zero_comp]

def pieceSet : Set W := {w | T.height w ≤ 0}

theorem isClosed_pieceSet : IsClosed T.pieceSet :=
  isClosed_le T.contMDiff_height.continuous continuous_const

theorem lift_mem_solidTorus {w : W} (hw : w ∈ T.pieceSet) : T.lift w ∈ solidTorusSet.{0} := hw

theorem sphereSecond_lift_ne_zero {w : W} (hw : w ∈ T.pieceSet) : sphereSecond (T.lift w) ≠ 0 :=
  sphereSecond_ne_zero_of_mem (T.lift_mem_solidTorus hw)

def discValue : W → ℂ := T.descend (twistDiscValue e)

def fiberValue : W → Circle := T.descend (twistFiberValue p)

theorem discValue_cover {x : LensSphere} (hx : sphereSecond x ≠ 0) :
    T.discValue (T.cover x) = twistDiscValue e x :=
  T.descend_cover (twistDiscValue_lensTwist hx)

theorem fiberValue_cover {x : LensSphere} (hx : sphereSecond x ≠ 0) :
    T.fiberValue (T.cover x) = twistFiberValue p x :=
  T.descend_cover (twistFiberValue_lensTwist hx)

theorem eventually_sphereSecond_ne_zero {x : LensSphere} (hx : sphereSecond x ≠ 0) :
    ∀ᶠ y in 𝓝 x, sphereSecond y ≠ 0 :=
  (isOpen_ne_fun contMDiff_sphereSecond.continuous continuous_const).mem_nhds hx

theorem contMDiffAt_discValue {w : W} (hw : w ∈ T.pieceSet) :
    ContMDiffAt (𝓡 3) 𝓘(ℝ, ℂ) ∞ T.discValue w := by
  have hx := T.sphereSecond_lift_ne_zero hw
  have h := T.contMDiffAt_descend (f := twistDiscValue e)
    ((eventually_sphereSecond_ne_zero hx).mono fun y hy j => twistDiscValue_lensTwist hy j)
    (contMDiffAt_twistDiscValue e hx)
  rwa [T.cover_lift] at h

theorem contMDiffAt_fiberValue {w : W} (hw : w ∈ T.pieceSet) :
    ContMDiffAt (𝓡 3) (𝓡 1) ∞ T.fiberValue w := by
  have hx := T.sphereSecond_lift_ne_zero hw
  have h := T.contMDiffAt_descend (f := twistFiberValue p)
    ((eventually_sphereSecond_ne_zero hx).mono fun y hy j => twistFiberValue_lensTwist hy j)
    (contMDiffAt_twistFiberValue p hx)
  rwa [T.cover_lift] at h

def toDiscCircle (w : T.pieceSet) : UnitDisc.{0} × Circle :=
  (ULift.up ⟨T.discValue w.val, by
    change ‖twistDiscValue e (T.lift w.val)‖ ^ 2 ≤ 1
    rw [norm_twistDiscValue_sq, height_lift]
    linarith [show T.height w.val ≤ 0 from w.2]⟩, T.fiberValue w.val)

def ofDiscCircle (q : UnitDisc.{0} × Circle) : T.pieceSet :=
  ⟨T.cover (sectionPoint e q.1 (circleRootOf p q.2)), by
    change T.height _ ≤ 0
    rw [height_cover]
    exact (solidTorusDiscCircle.{0}.symm _).2⟩

theorem toDiscCircle_of_mem (w : T.pieceSet) :
    T.toDiscCircle w =
      (discRotate ((solidTorusDiscCircle ⟨T.lift w.val, T.lift_mem_solidTorus w.2⟩).2 ^ (-e))
        (solidTorusDiscCircle ⟨T.lift w.val, T.lift_mem_solidTorus w.2⟩).1,
        (solidTorusDiscCircle ⟨T.lift w.val, T.lift_mem_solidTorus w.2⟩).2 ^ p) := rfl

variable [IsManifold (𝓡 3) ∞ W]

def pieceAtlas : SmoothBoundaryAtlas (𝓡 3) 3 T.pieceSet :=
  SmoothBoundaryAtlas.regularSublevel (𝓡 3) (n := 2) finrank_euclideanSpace_fin
    T.contMDiff_height 0 T.height_regular

instance instChartedSpacePiece : ChartedSpace (EuclideanHalfSpace 3) T.pieceSet :=
  T.pieceAtlas.toChartedSpace

instance instIsManifoldPiece : IsManifold (𝓡∂ 3) ∞ T.pieceSet := T.pieceAtlas.isManifold

theorem contMDiff_piece_val : ContMDiff (𝓡∂ 3) (𝓡 3) ∞ (Subtype.val : T.pieceSet → W) :=
  T.pieceAtlas.contMDiff_subtype_val

theorem contMDiff_piece_iff {F G X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [TopologicalSpace X] [ChartedSpace G X]
    (f : X → T.pieceSet) :
    ContMDiff J (𝓡∂ 3) ∞ f ↔ ContMDiff J (𝓡 3) ∞ (Subtype.val ∘ f) :=
  T.pieceAtlas.contMDiff_iff_subtype_val f

theorem contMDiffOn_piece_iff {F G X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [TopologicalSpace X] [ChartedSpace G X]
    (f : X → T.pieceSet) (s : Set X) :
    ContMDiffOn J (𝓡∂ 3) ∞ f s ↔ ContMDiffOn J (𝓡 3) ∞ (Subtype.val ∘ f) s :=
  T.pieceAtlas.contMDiffOn_iff_subtype_val f s

theorem piece_isBoundaryPoint_iff (w : T.pieceSet) :
    (𝓡∂ 3).IsBoundaryPoint w ↔ T.height w.val = 0 :=
  SmoothBoundaryAtlas.regularSublevel_isBoundaryPoint_iff (𝓡 3) (n := 2)
    finrank_euclideanSpace_fin T.contMDiff_height 0 T.height_regular w

theorem piece_isInteriorPoint_iff (w : T.pieceSet) :
    (𝓡∂ 3).IsInteriorPoint w ↔ T.height w.val < 0 :=
  SmoothBoundaryAtlas.regularSublevel_isInteriorPoint_iff (𝓡 3) (n := 2)
    finrank_euclideanSpace_fin T.contMDiff_height 0 T.height_regular w

theorem mfderiv_piece_val_bijective (w : T.pieceSet) :
    Bijective (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : T.pieceSet → W) w) :=
  T.pieceAtlas.mfderiv_subtypeVal_bijective w

def pieceDiffeo : T.pieceSet ≃ₘ⟮𝓡∂ 3, (𝓡∂ 2).prod (𝓡 1)⟯ UnitDisc.{0} × Circle where
  toFun := T.toDiscCircle
  invFun := T.ofDiscCircle
  left_inv w := by
    apply Subtype.ext
    change T.cover (sectionPoint e (T.toDiscCircle w).1 (circleRootOf p (T.toDiscCircle w).2)) =
      w.val
    rw [toDiscCircle_of_mem, T.cover_root_eq_of_pow (fun v j => sectionPoint_toCircle_mul e _ v j)
      rfl, sectionPoint, discRotate_discRotate, ← zpow_add, add_neg_cancel, zpow_zero,
      discRotate_one, Prod.mk.eta, Diffeomorph.symm_apply_apply]
    exact T.cover_lift w.val
  right_inv q := by
    obtain ⟨d, t⟩ := q
    have hz : solidTorusDiscCircle (solidTorusDiscCircle.{0}.symm
        (discRotate (circleRootOf p t ^ e) d, circleRootOf p t)) =
        (discRotate (circleRootOf p t ^ e) d, circleRootOf p t) :=
      Diffeomorph.apply_symm_apply _ _
    have h1 : (√2 : ℝ) • sphereFirst (sectionPoint e d (circleRootOf p t)) =
        (discRotate (circleRootOf p t ^ e) d).down.val :=
      congrArg (fun q : UnitDisc.{0} × Circle => q.1.down.val) hz
    have h2 : unitOf (sphereSecond (sectionPoint e d (circleRootOf p t))) = circleRootOf p t :=
      congrArg Prod.snd hz
    have hne : sphereSecond (sectionPoint e d (circleRootOf p t)) ≠ 0 :=
      sphereSecond_ne_zero_of_mem (solidTorusDiscCircle.{0}.symm _).2
    refine Prod.ext ?_ ?_
    · apply ULift.ext
      apply Subtype.ext
      change T.discValue (T.cover (sectionPoint e d (circleRootOf p t))) = d.down.val
      rw [T.discValue_cover hne, twistDiscValue, h2, h1, discRotate_val, ← mul_assoc,
        circle_zpow_neg_mul_cancel, one_mul]
    · change T.fiberValue (T.cover (sectionPoint e d (circleRootOf p t))) = t
      rw [T.fiberValue_cover hne, twistFiberValue, h2, circleRootOf_pow]
  contMDiff_toFun := by
    refine ContMDiff.prodMk ?_ ?_
    · have h : ContMDiff (𝓡∂ 3) (𝓡∂ 2) ∞ (fun w : T.pieceSet => (T.toDiscCircle w).1.down) := by
        apply (unitDiscAtlas.contMDiff_iff_subtype_val _).mpr
        intro w
        exact (T.contMDiffAt_discValue w.2).comp w (T.contMDiff_piece_val w)
      exact (uliftDiffeomorph (𝓡∂ 2) unitDiscSet).contMDiff.comp h
    · intro w
      exact (T.contMDiffAt_fiberValue w.2).comp w (T.contMDiff_piece_val w)
  contMDiff_invFun := by
    rw [T.contMDiff_piece_iff]
    intro q
    exact T.contMDiffAt_cover_root (f := Prod.snd) contMDiff_snd.contMDiffAt
      (Ψ := fun y v => sectionPoint e y.1 v)
      (fun v => ((contMDiff_sectionPoint e).comp
        ((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd)).contMDiffAt)
      (fun y v j => sectionPoint_toCircle_mul e y.1 v j)

theorem pieceDiffeo_apply (w : T.pieceSet) : T.pieceDiffeo w = T.toDiscCircle w := rfl

theorem pieceDiffeo_symm_apply_val (q : UnitDisc.{0} × Circle) :
    (T.pieceDiffeo.symm q).val = T.cover (sectionPoint e q.1 (circleRootOf p q.2)) := rfl

end TwistedCover

end GC.GraphManifold
