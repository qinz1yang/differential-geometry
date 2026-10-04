import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSideModelTube
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSideModelBallFill

/-!
# The shell of the fake ball

Lane N2d, side model, step 4 (shell). The model solid torus `ℂ × S¹` sits in `ℝ³` as a torus of
revolution (`torusPD`). On the side domain the lift is an injective local diffeomorphism, so its
inverse `liftInv` is a local diffeomorphism on the image (`isLocalDiffeomorphAt_invFunOn`). The
shell map `shellMap t x = torusPD (liftInv (tubeMap (dir x, 2 sgnR(t) ‖x‖)))` is an injective local
diffeomorphism on `3/4 < ‖x‖ < 6/5`, sending the unit sphere onto the model level set
`sgnR(t) · level = 2` (`shellPD`, `shellMap_spec`).
-/

set_option autoImplicit false

noncomputable section
open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

namespace GC.Seifert

theorem isLocalDiffeomorphAt_invFunOn {E F H H' M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace H M] [ChartedSpace H' N] [Nonempty M]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    {f : M → N} {W : Set M} (hW : IsOpen W) (hinj : InjOn f W) {x : M} (hx : x ∈ W)
    (hf : IsLocalDiffeomorphAt I J ∞ f x) :
    IsLocalDiffeomorphAt J I ∞ (invFunOn f W) (f x) := by
  obtain ⟨Φ, hxΦ, hEq⟩ := hf
  have hS : IsOpen (Φ.source ∩ W) := Φ.open_source.inter hW
  have hT : IsOpen (Φ '' (Φ.source ∩ W)) :=
    Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source hS inter_subset_left
  have hfx : f x = Φ x := hEq hxΦ
  have hmem : f x ∈ Φ '' (Φ.source ∩ W) := ⟨x, ⟨hxΦ, hx⟩, hfx.symm⟩
  refine IsLocalDiffeomorphAt.of_eventuallyEq ?_
    (Φ.symm.isLocalDiffeomorphAt _ _ ∞ (show f x ∈ Φ.target from hfx ▸ Φ.map_source hxΦ))
  filter_upwards [hT.mem_nhds hmem] with y hy
  obtain ⟨a, ⟨ha, haW⟩, rfl⟩ := hy
  have e1 : invFunOn f W (Φ a) = a := by
    rw [← hEq ha]
    exact hinj.leftInvOn_invFunOn haW
  rw [e1]
  exact (Φ.left_inv ha).symm

namespace SplitTube

def torusVal (q : ℂ × Circle) : ℂ × ℝ := ((4 + q.1.re) • (q.2 : ℂ), q.1.im)

def torusCoord (x : E3) : ℂ × Circle :=
  ((((‖(splitCoords x).1‖ - 4 : ℝ)) : ℂ) + (splitCoords x).2 • Complex.I,
    unitOf (splitCoords x).1)

theorem four_add_re_pos {ζ : ℂ} (h : ‖ζ‖ < 4) : 0 < 4 + ζ.re := by
  have := Complex.abs_re_le_norm ζ
  have := (abs_le.mp this).1
  linarith

theorem norm_torusVal_fst {q : ℂ × Circle} (h : ‖q.1‖ < 4) : ‖(torusVal q).1‖ = 4 + q.1.re := by
  rw [torusVal, norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg (four_add_re_pos h).le]

theorem torusCoord_torusVal {q : ℂ × Circle} (h : ‖q.1‖ < 4) :
    torusCoord (splitCoords.symm (torusVal q)) = q := by
  rw [torusCoord, ContinuousLinearEquiv.apply_symm_apply, norm_torusVal_fst h]
  refine Prod.ext ?_ ?_
  · change ((4 + q.1.re - 4 : ℝ) : ℂ) + q.1.im • Complex.I = q.1
    rw [show (4 + q.1.re - 4 : ℝ) = q.1.re by ring, Complex.real_smul]
    exact Complex.re_add_im q.1
  · exact unitOf_smul (four_add_re_pos h) q.2

theorem torusVal_torusCoord (x : E3) :
    splitCoords.symm (torusVal (torusCoord x)) = x := by
  apply splitCoords.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  refine Prod.ext ?_ ?_
  · have hre : ((((‖(splitCoords x).1‖ - 4 : ℝ)) : ℂ) + (splitCoords x).2 • Complex.I).re =
        ‖(splitCoords x).1‖ - 4 := by simp
    change (4 + ((((‖(splitCoords x).1‖ - 4 : ℝ)) : ℂ) +
      (splitCoords x).2 • Complex.I).re) • (unitOf (splitCoords x).1 : ℂ) = _
    rw [hre, show (4 + (‖(splitCoords x).1‖ - 4) : ℝ) = ‖(splitCoords x).1‖ by ring]
    exact norm_smul_unitOf _
  · change ((((‖(splitCoords x).1‖ - 4 : ℝ)) : ℂ) + (splitCoords x).2 • Complex.I).im = _
    rw [Complex.real_smul]
    simp

theorem continuousOn_torusCoord : ContinuousOn torusCoord {x : E3 | (splitCoords x).1 ≠ 0} := by
  have hs : Continuous fun x : E3 => splitCoords x := splitCoords.continuous
  refine ContinuousOn.prodMk ?_ ?_
  · exact ((Complex.continuous_ofReal.comp ((continuous_norm.comp
      (continuous_fst.comp hs)).sub continuous_const)).add
      ((continuous_snd.comp hs).smul continuous_const)).continuousOn
  · exact contMDiffOn_unitOf.continuousOn.comp (continuous_fst.comp hs).continuousOn
      fun x hx => hx

def torusPD : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3) (ℂ × Circle) E3 ∞ where
  toFun q := splitCoords.symm (torusVal q)
  invFun := torusCoord
  source := {q | ‖q.1‖ < 4}
  target := {x | (splitCoords x).1 ≠ 0 ∧ ‖(torusCoord x).1‖ < 4}
  map_source' q hq := by
    have hq' : ‖q.1‖ < 4 := hq
    refine ⟨?_, ?_⟩
    · rw [ContinuousLinearEquiv.apply_symm_apply]
      intro h0
      have := norm_torusVal_fst hq'
      rw [h0, norm_zero] at this
      linarith [four_add_re_pos hq']
    · rw [torusCoord_torusVal hq']
      exact hq'
  map_target' x hx := hx.2
  left_inv' q hq := torusCoord_torusVal hq
  right_inv' x _ := torusVal_torusCoord x
  open_source := isOpen_lt (continuous_norm.comp continuous_fst) continuous_const
  open_target := by
    have h1 : IsOpen {x : E3 | (splitCoords x).1 ≠ 0} :=
      isOpen_ne_fun (continuous_fst.comp splitCoords.continuous) continuous_const
    exact continuousOn_torusCoord.isOpen_inter_preimage h1
      (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const)
  contMDiffOn_toFun := by
    have h1 : ContMDiff (𝓘(ℝ, ℂ).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
        (fun q : ℂ × Circle => (4 + q.1.re) • (q.2 : ℂ)) := by
      have ha : ContMDiff (𝓘(ℝ, ℂ).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞
          (fun q : ℂ × Circle => 4 + q.1.re) :=
        (contDiff_const.add Complex.reCLM.contDiff).contMDiff.comp contMDiff_fst
      exact ha.smul (contMDiff_circle_coe.comp contMDiff_snd)
    have h2 : ContMDiff (𝓘(ℝ, ℂ).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞ (fun q : ℂ × Circle => q.1.im) :=
      Complex.imCLM.contDiff.contMDiff.comp contMDiff_fst
    exact (splitCoords.symm.contDiff.contMDiff.comp (h1.prodMk_space h2)).contMDiffOn
  contMDiffOn_invFun := by
    intro x hx
    have hx0 : (splitCoords x).1 ≠ 0 := hx.1
    have hs : ContMDiff (𝓡 3) 𝓘(ℝ, ℂ) ∞ fun x : E3 => (splitCoords x).1 :=
      (ContinuousLinearMap.fst ℝ ℂ ℝ ∘L (splitCoords : E3 →L[ℝ] ℂ × ℝ)).contDiff.contMDiff
    have hh : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ fun x : E3 => (splitCoords x).2 :=
      (ContinuousLinearMap.snd ℝ ℂ ℝ ∘L (splitCoords : E3 →L[ℝ] ℂ × ℝ)).contDiff.contMDiff
    refine ContMDiffWithinAt.prodMk ?_ ?_
    · have hn : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun x : E3 => ‖(splitCoords x).1‖) x :=
        (contDiffAt_norm ℝ hx0).contMDiffAt.comp x hs.contMDiffAt
      have e1 : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℂ) ∞
          (fun x : E3 => (((‖(splitCoords x).1‖ - 4 : ℝ)) : ℂ)) x :=
        Complex.ofRealCLM.contDiff.contMDiff.contMDiffAt.comp x (hn.sub contMDiffAt_const)
      have e2 : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℂ) ∞
          (fun x : E3 => (splitCoords x).2 • Complex.I) x :=
        hh.contMDiffAt.smul contMDiffAt_const
      exact (e1.add e2).contMDiffWithinAt
    · exact ((contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hx0)).comp x
        hs.contMDiffAt).contMDiffWithinAt

theorem torusPD_apply (q : ℂ × Circle) : torusPD q = splitCoords.symm (torusVal q) := rfl

theorem torusPD_injOn : InjOn torusPD {q : ℂ × Circle | ‖q.1‖ < 4} :=
  torusPD.toPartialEquiv.injOn

theorem isLocalDiffeomorphAt_torusPD {q : ℂ × Circle} (h : ‖q.1‖ < 4) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3) ∞ torusPD q :=
  torusPD.isLocalDiffeomorphAt _ _ ∞ h

theorem norm_torusPD_le {q : ℂ × Circle} (h : ‖q.1‖ ≤ 3) : ‖torusPD q‖ ≤ 10 := by
  have h4 : ‖q.1‖ < 4 := by linarith
  have e := norm_sq_splitCoords_symm (torusVal q)
  rw [← torusPD_apply, norm_torusVal_fst h4] at e
  have hre := (abs_le.mp (Complex.abs_re_le_norm q.1))
  have him := (abs_le.mp (Complex.abs_im_le_norm q.1))
  change ‖torusPD q‖ ^ 2 = (4 + q.1.re) ^ 2 + q.1.im ^ 2 at e
  have : ‖torusPD q‖ ^ 2 ≤ 10 ^ 2 := by rw [e]; nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp this

private local instance shellFact : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

def shellScale (t : Bool) : (S2 × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), (𝓡 2).prod 𝓘(ℝ, ℝ)⟯ (S2 × ℝ) :=
  (Diffeomorph.refl (𝓡 2) S2 ∞).prodCongr (LinearEquiv.smulOfUnit
    (Units.mk0 (2 * sgnR t) (mul_ne_zero two_ne_zero
      (SplitCharts.sgnR_ne_zero t)))).toContinuousLinearEquiv.toDiffeomorph

def shellDir (t : Bool) (x : E3) : S2 × ℝ := (Manifold.sphereDirection poleS2 x, 2 * sgnR t * ‖x‖)

def shellSet : Set E3 := {x | 3 / 4 < ‖x‖ ∧ ‖x‖ < 6 / 5}

theorem isOpen_shellSet : IsOpen shellSet :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

theorem sphere_subset_shellSet : sphere (0 : E3) 1 ⊆ shellSet := fun x hx => by
  have : ‖x‖ = 1 := by simpa using hx
  exact ⟨by rw [this]; norm_num, by rw [this]; norm_num⟩

theorem isLocalDiffeomorphAt_shellDir (t : Bool) {x : E3} (hx : x ≠ 0) :
    IsLocalDiffeomorphAt (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (shellDir t) x := by
  have h1 : IsLocalDiffeomorphAt (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (Manifold.spherePolarChart (n := 2) poleS2).symm x :=
    (Manifold.spherePolarChart (n := 2) poleS2).symm.isLocalDiffeomorphAt _ _ ∞
      (show x ∈ ({0}ᶜ : Set E3) from hx)
  have h2 := h1.comp ((𝓡 2).prod 𝓘(ℝ, ℝ)) (S2 × ℝ) ((shellScale t).isLocalDiffeomorph _)
  refine IsLocalDiffeomorphAt.of_eventuallyEq (Eventually.of_forall fun y => ?_) h2
  rfl

theorem abs_shellDir_snd (t : Bool) (x : E3) : |(shellDir t x).2| = 2 * ‖x‖ := by
  change |2 * sgnR t * ‖x‖| = _
  rw [mul_comm 2 (sgnR t), mul_assoc, SplitCharts.abs_sgnR_mul, abs_of_nonneg (by positivity)]

theorem abs_shellDir_lt (t : Bool) {x : E3} (hx : x ∈ shellSet) : |(shellDir t x).2| < 3 := by
  rw [abs_shellDir_snd]
  linarith [hx.2]

end SplitTube

namespace ElementaryPresentation

open SplitTube

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (E : ElementaryPresentation (NoCuts.carrier Q))
  {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b)

section Lift

variable (hlin : E.IsLinearSeam j)

def liftDom (t : Bool) : Set (ℂ × Circle) :=
  {q | ‖q.1‖ < 3 ∧ -3 < sgnR t * E.sideLevel h t q}

theorem isOpen_liftDom (t : Bool) : IsOpen (E.liftDom h t) :=
  E.isOpen_sideDom_interior h t

theorem sideDom_of_mem_liftDom {t : Bool} {q : ℂ × Circle} (hq : q ∈ E.liftDom h t) :
    E.sideDom h t q :=
  ⟨hq.1.le, hq.2⟩

theorem liftMap_injOn_liftDom (t : Bool) :
    InjOn ((E.splitCharts h hlin).liftMap t) (E.liftDom h t) := fun _ hq _ hq' he =>
  E.liftMap_injOn h hlin t (E.sideDom_of_mem_liftDom h hq) (E.sideDom_of_mem_liftDom h hq') he

theorem isLocalDiffeomorphAt_liftMap_of_mem {t : Bool} {q : ℂ × Circle}
    (hq : q ∈ E.liftDom h t) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3) ∞ ((E.splitCharts h hlin).liftMap t) q :=
  (E.splitCharts h hlin).isLocalDiffeomorphAt_liftMap (E.splitCharts_seam_zero h hlin) t hq.1
    fun h32 => ⟨E.hostChart_point_mem_pantsInterior h (E.sideDom_of_mem_liftDom h hq) h32 hq.1,
      E.point_ne_zero h (E.sideDom_of_mem_liftDom h hq)⟩

def liftInv (t : Bool) : Q.Carrier → ℂ × Circle :=
  invFunOn ((E.splitCharts h hlin).liftMap t) (E.liftDom h t)

theorem liftInv_liftMap {t : Bool} {q : ℂ × Circle} (hq : q ∈ E.liftDom h t) :
    E.liftInv h hlin t ((E.splitCharts h hlin).liftMap t q) = q :=
  (E.liftMap_injOn_liftDom h hlin t).leftInvOn_invFunOn hq

theorem liftInv_tubeMap (t : Bool) (p : S2) {lv : ℝ} (hlv : |lv| < 3) :
    E.liftInv h hlin t ((E.splitCharts h hlin).tubeMap (p, lv)) ∈ E.liftDom h t ∧
      (E.splitCharts h hlin).liftMap t (E.liftInv h hlin t
        ((E.splitCharts h hlin).tubeMap (p, lv))) = (E.splitCharts h hlin).tubeMap (p, lv) ∧
      E.sideLevel h t (E.liftInv h hlin t ((E.splitCharts h hlin).tubeMap (p, lv))) = lv := by
  obtain ⟨q, hq, hq3, hlev, he⟩ := E.exists_liftMap_eq_tubeMap h hlin t p hlv
  have hqd : q ∈ E.liftDom h t := ⟨hq3, hq.2⟩
  rw [← he, E.liftInv_liftMap h hlin hqd]
  exact ⟨hqd, rfl, hlev⟩

def shellMap (t : Bool) (x : E3) : E3 :=
  torusPD (E.liftInv h hlin t ((E.splitCharts h hlin).tubeMap (shellDir t x)))

theorem shellMap_spec (t : Bool) {x : E3} (hx : x ∈ shellSet) :
    E.liftInv h hlin t ((E.splitCharts h hlin).tubeMap (shellDir t x)) ∈ E.liftDom h t ∧
      (E.splitCharts h hlin).liftMap t (E.liftInv h hlin t
        ((E.splitCharts h hlin).tubeMap (shellDir t x))) =
        (E.splitCharts h hlin).tubeMap (shellDir t x) ∧
      sgnR t * E.sideLevel h t (E.liftInv h hlin t
        ((E.splitCharts h hlin).tubeMap (shellDir t x))) = 2 * ‖x‖ := by
  obtain ⟨h1, h2, h3⟩ := E.liftInv_tubeMap h hlin t (shellDir t x).1 (abs_shellDir_lt t hx)
  refine ⟨h1, h2, ?_⟩
  rw [h3]
  change sgnR t * (2 * sgnR t * ‖x‖) = _
  have := sgnR_mul_self t
  linear_combination (2 * ‖x‖) * this

theorem isLocalDiffeomorphAt_shellMap (t : Bool) {x : E3} (hx : x ∈ shellSet) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (E.shellMap h hlin t) x := by
  obtain ⟨h1, h2, -⟩ := E.shellMap_spec h hlin t hx
  have hx0 : x ≠ 0 := fun h0 => by have := hx.1; rw [h0, norm_zero] at this; linarith
  have a1 := isLocalDiffeomorphAt_shellDir t hx0
  have a2 := (E.splitCharts h hlin).isLocalDiffeomorphAt_tubeMap (abs_shellDir_lt t hx)
  have a3 := isLocalDiffeomorphAt_invFunOn (E.isOpen_liftDom h t)
    (E.liftMap_injOn_liftDom h hlin t) h1 (E.isLocalDiffeomorphAt_liftMap_of_mem h hlin h1)
  rw [h2] at a3
  have a4 := isLocalDiffeomorphAt_torusPD (q := E.liftInv h hlin t
    ((E.splitCharts h hlin).tubeMap (shellDir t x))) (by linarith [h1.1])
  exact ((a1.comp (𝓡 3) Q.Carrier a2).comp (𝓘(ℝ, ℂ).prod (𝓡 1)) (ℂ × Circle) a3).comp
    (𝓡 3) E3 a4

theorem shellMap_injOn (t : Bool) : InjOn (E.shellMap h hlin t) shellSet := by
  intro x hx y hy he
  obtain ⟨hx1, hx2, -⟩ := E.shellMap_spec h hlin t hx
  obtain ⟨hy1, hy2, -⟩ := E.shellMap_spec h hlin t hy
  have hx4 : ‖(E.liftInv h hlin t ((E.splitCharts h hlin).tubeMap (shellDir t x))).1‖ < 4 := by
    linarith [hx1.1]
  have hy4 : ‖(E.liftInv h hlin t ((E.splitCharts h hlin).tubeMap (shellDir t y))).1‖ < 4 := by
    linarith [hy1.1]
  have e1 := torusPD_injOn hx4 hy4 he
  have e2 := congrArg ((E.splitCharts h hlin).liftMap t) e1
  rw [hx2, hy2] at e2
  have e3 := (E.splitCharts h hlin).tubeMap_injOn (abs_shellDir_lt t hx) (abs_shellDir_lt t hy) e2
  have hn : ‖x‖ = ‖y‖ := by
    have := congrArg (fun p : S2 × ℝ => |p.2|) e3
    simp only [abs_shellDir_snd] at this
    linarith
  have hd : Manifold.sphereDirection poleS2 x = Manifold.sphereDirection poleS2 y :=
    congrArg Prod.fst e3
  have hx0 : x ≠ 0 := fun h0 => by have := hx.1; rw [h0, norm_zero] at this; linarith
  have hy0 : y ≠ 0 := fun h0 => by have := hy.1; rw [h0, norm_zero] at this; linarith
  rw [← Manifold.norm_smul_sphereDirection poleS2 hx0, ← Manifold.norm_smul_sphereDirection
    poleS2 hy0, hn, hd]

theorem exists_shellPD (t : Bool) :
    ∃ F : PartialDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
      F.toPartialEquiv.source = shellSet ∧ ∀ x, F x = E.shellMap h hlin t x := by
  obtain ⟨F, hs, -, hf⟩ := IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
    (fun x => E.isLocalDiffeomorphAt_shellMap h hlin t x.2) isOpen_shellSet
    ⟨(EuclideanSpace.single 0 1 : E3), by simp [shellSet]; norm_num⟩ (E.shellMap_injOn h hlin t)
  exact ⟨F, hs, fun x => congrFun hf x⟩

end Lift

end ElementaryPresentation

end GC.Seifert
