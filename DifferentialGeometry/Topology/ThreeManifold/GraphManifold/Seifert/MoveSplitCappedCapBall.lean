import DifferentialGeometry.Topology.ThreeManifold.CapCollarMatching
import DifferentialGeometry.Topology.ThreeManifold.CapBallChart
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import DifferentialGeometry.Topology.ThreeManifold.RadialTube
import DifferentialGeometry.Topology.Manifold.SphereDegreeReflection
import DifferentialGeometry.Topology.Manifold.SpherePolarCoordinates

/-!
# Cap balls of a spherical capping

Lane N2c, tier 2 (caps). For a spherical capping `C` of `M` along a tube system `T` and a
boundary sphere `b`, the cap `C.cap b` and the shell of the tube next to it form one smooth ball
chart of the capped manifold (`exists_capBall`): a map `Φ` from the Euclidean ball of radius
`1 + r` which is a local diffeomorphism and injective there, sends the closed unit ball onto the
cap, and on the shell `1 ≤ ‖x‖ < 1 + r` reads the core through the tube,
`Φ x = coreInclusion (radialTube x) = coreInclusion (tube (attaching (x/‖x‖), ±‖x‖))`.

It is assembled from the collar matching `exists_cap_core_collar_matching`: inside, the cap
composed with the ambient diffeomorphism `D` (a local diffeomorphism through the cap ball chart);
near and beyond the unit sphere, the radial collar coordinates of the core half collar, which agree
with the cap side through `D` on a neighbourhood of the sphere.
-/

set_option autoImplicit false

noncomputable section
open Set Function Metric Manifold
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace GC.Seifert.SplitTube

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private local instance capBallFact : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance capBallFact2 : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
private local instance capBallCellCharts : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2
private local instance capBallCellSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

theorem norm_lt_one_of_diffeo {D : E3 ≃ₘ[ℝ] E3} (hfix : EqOn D id (sphere (0 : E3) 1))
    (hball : D '' closedBall (0 : E3) 1 = closedBall (0 : E3) 1) {x : E3} (hx : ‖x‖ < 1) :
    ‖D x‖ < 1 := by
  have hle : ‖D x‖ ≤ 1 := by
    have : D x ∈ D '' closedBall (0 : E3) 1 := ⟨x, mem_closedBall_zero_iff.mpr hx.le, rfl⟩
    rw [hball] at this
    exact mem_closedBall_zero_iff.mp this
  refine lt_of_le_of_ne hle fun h1 => ?_
  have hs : D x ∈ sphere (0 : E3) 1 := mem_sphere_zero_iff_norm.mpr h1
  have h2 : D (D x) = D x := hfix hs
  have h3 := D.injective h2
  rw [h3] at h1
  exact absurd h1 (ne_of_lt hx)

def poleS2 : S2 := ⟨EuclideanSpace.single 0 1, by simp⟩

theorem cap_eq_radial (b : T.Boundary)
    {d : SmoothTwoSidedCollar (𝓡 2) (𝓡 3) (C.cap b ∘ sphereToClosedCell)}
    (hdin : ∀ (p : S2 × symmetricOpenInterval d.radius), 0 ≤ p.2.val →
      ∃ x : ClosedCell 3, x.val = (1 - p.2.val) • p.1.val ∧ d.toFun p = C.cap b x)
    (v : S2) {y : E3} (hy : y ∈ (d.radialPartialDiffeomorph v).source) (hy1 : ‖y‖ ≤ 1) :
    d.radialPartialDiffeomorph v y = C.cap b ⟨y, hy1⟩ := by
  obtain ⟨hy0, ht⟩ := (d.mem_radialPartialDiffeomorph_source_iff v y).mp hy
  set z := Manifold.sphereDirection v y with hz
  have hyz : ‖y‖ • (z : E3) = y := Manifold.norm_smul_sphereDirection v hy0
  have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have h1 := d.radialPartialDiffeomorph_apply v z ‖y‖ hpos ht
  rw [hyz] at h1
  obtain ⟨w, hw, hdw⟩ := hdin (z, ⟨1 - ‖y‖, ht⟩) (by simp only; linarith)
  rw [h1, hdw]
  congr 1
  apply Subtype.ext
  rw [hw]
  simp only [sub_sub_cancel]
  exact hyz

theorem core_eq_radial (b : T.Boundary)
    {e : SmoothTwoSidedCollar (𝓡 2) (𝓡 3) (C.cap b ∘ sphereToClosedCell)} (he : e.radius ≤ 1 / 2)
    (heq : ∀ (p : S2 × symmetricOpenInterval e.radius) (hp : 0 ≤ p.2.val),
      e.toFun p = C.coreInclusionHalfCollar b (p.1, ⟨p.2.val, hp, p.2.property.2.trans_le he⟩))
    (v : S2) {x : E3} (hx1 : 1 ≤ ‖x‖) (hx2 : ‖x‖ < 1 + e.radius) :
    x ∈ (e.reverse.radialPartialDiffeomorph v).source ∧
    ∃ y : T.core, (y : M.Carrier) = T.radialTube b.1 (C.attaching b) b.2 v x ∧
      e.reverse.radialPartialDiffeomorph v x = C.coreInclusion y := by
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (by linarith)
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hr := e.radius_pos
  have ht : 1 - ‖x‖ ∈ Ioo (-e.reverse.radius) e.reverse.radius := by
    rw [SmoothTwoSidedCollar.reverse_radius]
    constructor <;> linarith
  refine ⟨(e.reverse.mem_radialPartialDiffeomorph_source_iff v x).mpr ⟨hx0, ht⟩, ?_⟩
  set z := Manifold.sphereDirection v x with hz
  have hxz : ‖x‖ • (z : E3) = x := Manifold.norm_smul_sphereDirection v hx0
  have h1 := e.reverse.radialPartialDiffeomorph_apply v z ‖x‖ hpos ht
  rw [hxz] at h1
  have hp : (0 : ℝ) ≤ ‖x‖ - 1 := by linarith
  have hlt : ‖x‖ - 1 < 1 / 2 := by linarith
  refine ⟨C.coreBoundaryHalfCollar b (z, ⟨‖x‖ - 1, hp, hlt⟩), ?_, ?_⟩
  · rw [SphericalCapping.coreBoundaryHalfCollar_val,
      T.radialTube_apply b.1 (C.attaching b) b.2 v (by linarith : ‖x‖ < 2)]
    congr 2
    apply Subtype.ext
    rw [SphericalTubeSystem.coreCollarParameter_val]
    cases b.2
    · simp [SphericalTubeSystem.boundaryLevel]
      ring
    · simp [SphericalTubeSystem.boundaryLevel]
  · rw [h1]
    have e2 := heq (z, ⟨-(1 - ‖x‖), by constructor <;> linarith⟩) (by simp only; linarith)
    refine Eq.trans (b := e.toFun (z, ⟨-(1 - ‖x‖), by constructor <;> linarith⟩)) rfl ?_
    rw [e2]
    change C.coreInclusion (C.coreBoundaryHalfCollar b _) = _
    congr 3
    simp only
    ring_nf

theorem exists_capBall_twisted (b : T.Boundary) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 2 ∧ ∃ Φ : E3 → N.Carrier,
      (∀ x, ‖x‖ < 1 + r → IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ Φ x) ∧
      InjOn Φ (ball 0 (1 + r)) ∧
      (∀ x, ‖x‖ ≤ 1 → ∃ w : ClosedCell 3, Φ x = C.cap b w) ∧
      (∀ w : ClosedCell 3, ∃ x, ‖x‖ ≤ 1 ∧ Φ x = C.cap b w) ∧
      ∀ (v : S2) (x : E3), 1 ≤ ‖x‖ → ‖x‖ < 1 + r → ∃ y : T.core,
        (y : M.Carrier) = T.radialTube b.1 (C.attaching b) b.2 v x ∧ Φ x = C.coreInclusion y := by
  classical
  obtain ⟨d, e, hd, he, hdin, heq, D, V, hV, hSV, hdom, hmatch, hfixS, hball, hfix, -⟩ :=
    C.exists_cap_core_collar_matching b poleS2
  have hDle : ∀ x : E3, ‖x‖ ≤ 1 → ‖D x‖ ≤ 1 := fun x hx => by
    have : D x ∈ D '' closedBall (0 : E3) 1 := ⟨x, mem_closedBall_zero_iff.mpr hx, rfl⟩
    rw [hball] at this
    exact mem_closedBall_zero_iff.mp this
  let P := e.reverse.radialPartialDiffeomorph poleS2
  let Φ : E3 → N.Carrier := fun x =>
    if hx : ‖x‖ ≤ 1 then C.cap b ⟨D x, hDle x hx⟩ else P x
  have hr := e.radius_pos
  have hΦin : ∀ x (hx : ‖x‖ ≤ 1), Φ x = C.cap b ⟨D x, hDle x hx⟩ := fun x hx => by
    simp only [Φ, dite_eq_left hx]
  have hΦout : ∀ x, 1 < ‖x‖ → Φ x = P x := fun x hx => by
    simp only [Φ, dite_eq_right (not_le.mpr hx)]
  have hcap : ∀ x, x ∈ V → ‖x‖ ≤ 1 → Φ x = P x := by
    intro x hxV hx1
    rw [hΦin x hx1, ← hmatch x hxV]
    exact (cap_eq_radial C b hdin poleS2 (hdom x hxV).2 (hDle x hx1)).symm
  have hcore : ∀ (v : S2) (x : E3), 1 ≤ ‖x‖ → ‖x‖ < 1 + e.radius → ∃ y : T.core,
      (y : M.Carrier) = T.radialTube b.1 (C.attaching b) b.2 v x ∧ Φ x = C.coreInclusion y := by
    intro v x hx1 hx2
    have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (by linarith)
    obtain ⟨-, y, hy, hPy⟩ := core_eq_radial C b he heq poleS2 hx1 hx2
    have hv : T.radialTube b.1 (C.attaching b) b.2 v x =
        T.radialTube b.1 (C.attaching b) b.2 poleS2 x := by
      have hdir : Manifold.sphereDirection v x = Manifold.sphereDirection poleS2 x :=
        Subtype.ext ((Manifold.coe_sphereDirection v hx0).trans
          (Manifold.coe_sphereDirection poleS2 hx0).symm)
      simp only [SphericalTubeSystem.radialTube, hdir]
    refine ⟨y, hy.trans hv.symm, ?_⟩
    rcases eq_or_lt_of_le hx1 with h1 | h1
    · have hs : x ∈ sphere (0 : E3) 1 := mem_sphere_zero_iff_norm.mpr h1.symm
      rw [hcap x (hSV hs) h1.symm.le, hPy]
    · rw [hΦout x h1, hPy]
  have hsign : ∀ x : E3, (if b.2 then (1 / 4 : ℝ) else -(1 / 4 : ℝ)) •
      ((if b.2 then (4 : ℝ) else -4) • x) = x := fun x => by
    rw [smul_smul]
    cases b.2 <;> norm_num
  have hc0 : (if b.2 then (4 : ℝ) else -4) ≠ 0 := by cases b.2 <;> norm_num
  let S : E3 ≃ₘ[ℝ] E3 :=
    (LinearEquiv.smulOfUnit (Units.mk0 _ hc0)).toContinuousLinearEquiv.toDiffeomorph
  have hS : ∀ x, S x = (if b.2 then (4 : ℝ) else -4) • x := fun x => rfl
  refine ⟨e.radius, hr, he, Φ, ?_, ?_, fun x hx => ⟨_, hΦin x hx⟩, ?_, hcore⟩
  · intro x hx
    by_cases hx1 : ‖x‖ < 1
    · have heqΦ : Φ =ᶠ[𝓝 x] (C.capBallChart b).chart ∘ (S ∘ D) := by
        refine Filter.eventuallyEq_of_mem
          ((isOpen_lt continuous_norm continuous_const).mem_nhds hx1)
          fun y hy => ?_
        have hy1 : ‖y‖ < 1 := hy
        have hDy := norm_lt_one_of_diffeo hfixS hball hy1
        have hn : ‖(if b.2 then (1 / 4 : ℝ) else -(1 / 4 : ℝ)) • S (D y)‖ < 1 := by
          rw [hS, hsign]
          exact hDy
        rw [Function.comp_apply, Function.comp_apply, C.capBallChart_apply b _ hn, hΦin y hy1.le]
        congr 1
        apply Subtype.ext
        simp only
        rw [hS, hsign]
      refine IsLocalDiffeomorphAt.of_eventuallyEq heqΦ ?_
      have hsrc : S (D x) ∈ (C.capBallChart b).chart.source := by
        rw [C.capBallChart_source, mem_ball_zero_iff, hS, norm_smul]
        have hDx := norm_lt_one_of_diffeo hfixS hball hx1
        cases b.2 <;> norm_num <;> linarith
      exact ((D.isLocalDiffeomorph x).comp _ _ (S.isLocalDiffeomorph _)).comp _ _
        ((C.capBallChart b).chart.isLocalDiffeomorphAt _ _ ∞ hsrc)
    · push Not at hx1
      have hxP : x ∈ P.source := (core_eq_radial C b he heq poleS2 hx1 hx).1
      have heqΦ : Φ =ᶠ[𝓝 x] P := by
        rcases eq_or_lt_of_le hx1 with h1 | h1
        · have hs : x ∈ sphere (0 : E3) 1 := mem_sphere_zero_iff_norm.mpr h1.symm
          refine Filter.eventuallyEq_of_mem (hV.mem_nhds (hSV hs)) fun y hy => ?_
          by_cases hy1 : ‖y‖ ≤ 1
          · exact hcap y hy hy1
          · exact hΦout y (not_le.mp hy1)
        · exact Filter.eventuallyEq_of_mem
            ((isOpen_lt continuous_const continuous_norm).mem_nhds h1) fun y hy => hΦout y hy
      exact IsLocalDiffeomorphAt.of_eventuallyEq heqΦ (P.isLocalDiffeomorphAt _ _ ∞ hxP)
  · intro x hx y hy hxy
    have hx' : ‖x‖ < 1 + e.radius := mem_ball_zero_iff.mp hx
    have hy' : ‖y‖ < 1 + e.radius := mem_ball_zero_iff.mp hy
    have hcapinj := (C.cap_embedding b).isEmbedding.injective
    let _ := C.coreCharts
    let _ := C.coreSmooth
    have hcoreinj := C.core_embedding.isEmbedding.injective
    have htubeinj := (T.smooth b.1).isEmbedding.injective
    have hmixed : ∀ x' y' : E3, ‖x'‖ ≤ 1 → 1 < ‖y'‖ → ‖y'‖ < 1 + e.radius → Φ x' ≠ Φ y' := by
      intro x' y' hx1 hy1 hy2 hne
      obtain ⟨z, hz, hΦz⟩ := hcore poleS2 y' hy1.le hy2
      rw [hΦin x' hx1, hΦz] at hne
      have hmem : C.cap b ⟨D x', hDle x' hx1⟩ ∈ range C.coreInclusion ∩ range (C.cap b) :=
        ⟨⟨z, hne.symm⟩, ⟨_, rfl⟩⟩
      rw [C.core_cap_intersection b] at hmem
      obtain ⟨w, hw⟩ := hmem
      rw [hne] at hw
      have hzw := hcoreinj hw
      have hval := congrArg Subtype.val hzw
      change T.boundarySphere b w = (z : M.Carrier) at hval
      rw [hz, T.radialTube_apply b.1 (C.attaching b) b.2 poleS2 (by linarith)] at hval
      have h2 := congrArg (fun q : S2 × Icc (-2 : ℝ) 2 => (q.2 : ℝ)) (htubeinj hval)
      simp only [SphericalTubeSystem.boundaryLevel] at h2
      rcases Bool.eq_false_or_eq_true b.2 with hb | hb <;> simp [hb] at h2 <;> linarith
    by_cases hx1 : ‖x‖ ≤ 1 <;> by_cases hy1 : ‖y‖ ≤ 1
    · rw [hΦin x hx1, hΦin y hy1] at hxy
      have := congrArg Subtype.val (hcapinj hxy)
      exact D.injective this
    · exact absurd hxy (hmixed x y hx1 (not_le.mp hy1) hy')
    · exact absurd hxy.symm (hmixed y x hy1 (not_le.mp hx1) hx')
    · push Not at hx1 hy1
      obtain ⟨z, hz, hΦz⟩ := hcore poleS2 x hx1.le hx'
      obtain ⟨z', hz', hΦz'⟩ := hcore poleS2 y hy1.le hy'
      rw [hΦz, hΦz'] at hxy
      have hval := congrArg Subtype.val (hcoreinj hxy)
      rw [hz, hz', T.radialTube_apply b.1 (C.attaching b) b.2 poleS2 (by linarith),
        T.radialTube_apply b.1 (C.attaching b) b.2 poleS2 (by linarith)] at hval
      have hq := htubeinj hval
      simp only [Prod.mk.injEq] at hq
      have hdir := (C.attaching b).injective hq.1
      have hn : ‖x‖ = ‖y‖ := by
        have := congrArg Subtype.val hq.2
        rcases Bool.eq_false_or_eq_true b.2 with hb | hb <;> simp [hb] at this <;> linarith
      rw [← Manifold.norm_smul_sphereDirection poleS2 (norm_ne_zero_iff.mp (by linarith) : x ≠ 0),
        ← Manifold.norm_smul_sphereDirection poleS2 (norm_ne_zero_iff.mp (by linarith) : y ≠ 0),
        hdir, hn]
  · intro w
    have hw : w.val ∈ D '' closedBall (0 : E3) 1 := by
      rw [hball]
      exact mem_closedBall_zero_iff.mpr w.property
    obtain ⟨x, hx, hDx⟩ := hw
    refine ⟨x, mem_closedBall_zero_iff.mp hx, ?_⟩
    rw [hΦin x (mem_closedBall_zero_iff.mp hx)]
    congr 1
    exact Subtype.ext hDx

theorem exists_sphere_isotopy (A : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) :
    ∃ (s : Bool) (J : ℝ → S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2),
      ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun q : ℝ × S2 => J q.1 q.2) ∧
      ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun q : ℝ × S2 => (J q.1).symm q.2) ∧
      (∀ z, J 0 z = A (if s then -z else z)) ∧ J 1 = Diffeomorph.refl (𝓡 2) S2 ∞ := by
  rcases Manifold.sphereDiffeomorphDegree_eq_one_or_neg_one A with h | h
  · obtain ⟨J, hJ, hJi, hJ0, hJ1⟩ := (Manifold.sphereDiffeomorphDegree_eq_one_iff_isotopy A).mp h
    exact ⟨false, J, hJ, hJi, fun z => by rw [hJ0]; rfl, hJ1⟩
  · have h1 := Manifold.sphereDiffeomorphDegree_pre_antipodal_eq_one A h
    obtain ⟨J, hJ, hJi, hJ0, hJ1⟩ := (Manifold.sphereDiffeomorphDegree_eq_one_iff_isotopy _).mp h1
    exact ⟨true, J, hJ, hJi, fun z => by rw [hJ0]; rfl, hJ1⟩

def shellStep (r ρ : ℝ) : ℝ := Real.smoothTransition ((ρ - (1 + r / 4)) / (r / 4))

theorem shellStep_of_le {r ρ : ℝ} (hr : 0 < r) (h : ρ ≤ 1 + r / 4) : shellStep r ρ = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

theorem shellStep_of_ge {r ρ : ℝ} (hr : 0 < r) (h : 1 + r / 2 ≤ ρ) : shellStep r ρ = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem contDiff_shellStep (r : ℝ) : ContDiff ℝ ∞ (shellStep r) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

variable (A : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) (J : ℝ → S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) (r : ℝ)

def shellTwist (x : E3) : E3 :=
  ‖x‖ • ((A.symm (J (shellStep r ‖x‖) (Manifold.sphereDirection poleS2 x)) : S2) : E3)

theorem norm_shellTwist (x : E3) : ‖shellTwist A J r x‖ = ‖x‖ := by
  rw [shellTwist, norm_smul, norm_norm, norm_eq_of_mem_sphere, mul_one]

def shellAngle (q : S2 × ℝ) : S2 × ℝ := (A.symm (J (shellStep r q.2) q.1), q.2)

def shellAngleDiffeo
    (hJ : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun q : ℝ × S2 => J q.1 q.2))
    (hJi : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun q : ℝ × S2 => (J q.1).symm q.2)) :
    (S2 × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ), (𝓡 2).prod 𝓘(ℝ)⟯ (S2 × ℝ) where
  toFun := shellAngle A J r
  invFun q := ((J (shellStep r q.2)).symm (A q.1), q.2)
  left_inv q := by simp [shellAngle]
  right_inv q := by simp [shellAngle]
  contMDiff_toFun := by
    have hs : ContMDiff ((𝓡 2).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ (fun q : S2 × ℝ => shellStep r q.2) :=
      (contDiff_shellStep r).contMDiff.comp contMDiff_snd
    exact (A.symm.contMDiff.comp (hJ.comp (hs.prodMk contMDiff_fst))).prodMk contMDiff_snd
  contMDiff_invFun := by
    have hs : ContMDiff ((𝓡 2).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ (fun q : S2 × ℝ => shellStep r q.2) :=
      (contDiff_shellStep r).contMDiff.comp contMDiff_snd
    exact (hJi.comp (hs.prodMk (A.contMDiff.comp contMDiff_fst))).prodMk contMDiff_snd

theorem shellTwist_of_le {sb : Bool} (hJ0 : ∀ z, J 0 z = A (if sb then -z else z)) (hr : 0 < r)
    {x : E3} (hx : ‖x‖ ≤ 1 + r / 4) : shellTwist A J r x = if sb then -x else x := by
  by_cases h0 : x = 0
  · subst h0
    simp [shellTwist]
  · rw [shellTwist, shellStep_of_le hr hx, hJ0, Diffeomorph.symm_apply_apply]
    have hx' := Manifold.norm_smul_sphereDirection poleS2 h0
    cases sb
    · simpa using hx'
    · simp only [ite_true]
      rw [coe_neg_sphere, smul_neg, hx']

theorem shellTwist_of_ge (hJ1 : J 1 = Diffeomorph.refl (𝓡 2) S2 ∞) (hr : 0 < r) {x : E3}
    (hx : 1 + r / 2 ≤ ‖x‖) :
    shellTwist A J r x = ‖x‖ • ((A.symm (Manifold.sphereDirection poleS2 x) : S2) : E3) := by
  rw [shellTwist, shellStep_of_ge hr hx, hJ1]
  rfl

theorem sphereDirection_shellTwist {x : E3} (hx : x ≠ 0) :
    Manifold.sphereDirection poleS2 (shellTwist A J r x) =
      A.symm (J (shellStep r ‖x‖) (Manifold.sphereDirection poleS2 x)) :=
  Manifold.sphereDirection_pos_smul poleS2 _ (norm_pos_iff.mpr hx)

theorem isLocalDiffeomorphAt_shellTwist
    (hJ : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun q : ℝ × S2 => J q.1 q.2))
    (hJi : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun q : ℝ × S2 => (J q.1).symm q.2))
    {sb : Bool} (hJ0 : ∀ z, J 0 z = A (if sb then -z else z)) (hr : 0 < r) (x : E3) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E3) 𝓘(ℝ, E3) ∞ (shellTwist A J r) x := by
  by_cases hx : ‖x‖ < 1 + r / 4
  · let L : E3 ≃L[ℝ] E3 :=
      if sb then ContinuousLinearEquiv.neg ℝ else ContinuousLinearEquiv.refl ℝ E3
    have heq : shellTwist A J r =ᶠ[𝓝 x] L := by
      refine Filter.eventuallyEq_of_mem ((isOpen_lt continuous_norm continuous_const).mem_nhds hx)
        fun y hy => ?_
      rw [shellTwist_of_le A J r hJ0 hr (le_of_lt hy)]
      cases sb <;> rfl
    exact IsLocalDiffeomorphAt.of_eventuallyEq heq (L.toDiffeomorph.isLocalDiffeomorph x)
  · push Not at hx
    have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (by linarith)
    let P := Manifold.spherePolarChart (n := 2) poleS2
    let G := shellAngleDiffeo A J r hJ hJi
    have heq : shellTwist A J r =ᶠ[𝓝 x] P ∘ G ∘ P.symm := by
      refine Filter.eventuallyEq_of_mem (isOpen_compl_singleton.mem_nhds hx0) fun y _ => ?_
      rfl
    refine IsLocalDiffeomorphAt.of_eventuallyEq heq ?_
    have h1 : IsLocalDiffeomorphAt 𝓘(ℝ, E3) ((𝓡 2).prod 𝓘(ℝ)) ∞ P.symm x :=
      P.symm.isLocalDiffeomorphAt _ _ ∞ (show x ∈ P.target from hx0)
    have h2 := h1.comp _ _ (G.isLocalDiffeomorph _)
    refine h2.comp _ _ (P.isLocalDiffeomorphAt _ _ ∞ ?_)
    change 0 < (G (P.symm x)).2
    exact norm_pos_iff.mpr hx0

theorem shellTwist_injective : Injective (shellTwist A J r) := by
  intro x y h
  have hn : ‖x‖ = ‖y‖ := by
    rw [← norm_shellTwist A J r x, ← norm_shellTwist A J r y, h]
  by_cases hx : x = 0
  · subst hx
    rw [norm_zero] at hn
    exact (norm_eq_zero.mp hn.symm).symm
  · have hy : y ≠ 0 := by
      intro hy0
      rw [hy0, norm_zero] at hn
      exact hx (norm_eq_zero.mp hn)
    have hd := congrArg (Manifold.sphereDirection poleS2) h
    rw [sphereDirection_shellTwist A J r hx, sphereDirection_shellTwist A J r hy, hn] at hd
    have hd' := (J _).injective (A.symm.injective hd)
    rw [← Manifold.norm_smul_sphereDirection poleS2 hx,
      ← Manifold.norm_smul_sphereDirection poleS2 hy,
      hd', hn]

theorem exists_capBall (b : T.Boundary) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 2 ∧ ∃ Φ : E3 → N.Carrier,
      (∀ x, ‖x‖ < 1 + r → IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ Φ x) ∧
      InjOn Φ (ball 0 (1 + r)) ∧
      (∀ x, ‖x‖ ≤ 1 → ∃ w : ClosedCell 3, Φ x = C.cap b w) ∧
      (∀ w : ClosedCell 3, ∃ x, ‖x‖ ≤ 1 ∧ Φ x = C.cap b w) ∧
      (∀ x, 1 ≤ ‖x‖ → ‖x‖ < 1 + r → ∃ (z : S2) (y : T.core),
        (y : M.Carrier) = T.tube b.1 (z, projIcc (-2) 2 (by norm_num)
          (if b.2 then ‖x‖ else -‖x‖)) ∧ Φ x = C.coreInclusion y) ∧
      ∀ x, 1 + r / 2 ≤ ‖x‖ → ‖x‖ < 1 + r → ∃ y : T.core,
        (y : M.Carrier) = T.tube b.1 (Manifold.sphereDirection poleS2 x, projIcc (-2) 2
          (by norm_num) (if b.2 then ‖x‖ else -‖x‖)) ∧ Φ x = C.coreInclusion y := by
  obtain ⟨r, hr, hr2, Φ, hloc, hinj, hcapin, hcapsurj, hcore⟩ := exists_capBall_twisted C b
  obtain ⟨sb, J, hJ, hJi, hJ0, hJ1⟩ := exists_sphere_isotopy (C.attaching b)
  set R := shellTwist (C.attaching b) J r with hRdef
  have hRn : ∀ x, ‖R x‖ = ‖x‖ := norm_shellTwist (C.attaching b) J r
  have hshell : ∀ x : E3, 1 ≤ ‖x‖ → ‖x‖ < 1 + r → ∃ y : T.core,
      (y : M.Carrier) = T.tube b.1 (C.attaching b (Manifold.sphereDirection poleS2 (R x)),
        projIcc (-2) 2 (by norm_num) (if b.2 then ‖x‖ else -‖x‖)) ∧
        Φ (R x) = C.coreInclusion y := by
    intro x hx1 hx2
    obtain ⟨y, hy, hΦy⟩ := hcore poleS2 (R x) (by rw [hRn]; exact hx1) (by rw [hRn]; exact hx2)
    refine ⟨y, ?_, hΦy⟩
    rw [hy, SphericalTubeSystem.radialTube, hRn]
  refine ⟨r, hr, hr2, Φ ∘ R, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (isLocalDiffeomorphAt_shellTwist (C.attaching b) J r hJ hJi hJ0 hr x).comp _ _
      (hloc (R x) (by rw [hRn]; exact hx))
  · intro x hx y hy hxy
    have hx' : R x ∈ ball (0 : E3) (1 + r) := by
      rw [mem_ball_zero_iff, hRn]; exact mem_ball_zero_iff.mp hx
    have hy' : R y ∈ ball (0 : E3) (1 + r) := by
      rw [mem_ball_zero_iff, hRn]; exact mem_ball_zero_iff.mp hy
    exact shellTwist_injective (C.attaching b) J r (hinj hx' hy' hxy)
  · intro x hx
    exact hcapin (R x) (by rw [hRn]; exact hx)
  · intro w
    obtain ⟨x', hx', hΦ⟩ := hcapsurj w
    refine ⟨if sb then -x' else x', by cases sb <;> simpa using hx', ?_⟩
    have hle : ‖(if sb then -x' else x' : E3)‖ ≤ 1 + r / 4 := by
      cases sb <;> simp <;> linarith
    change Φ (R _) = _
    rw [hRdef, shellTwist_of_le (C.attaching b) J r hJ0 hr hle]
    cases sb <;> simpa using hΦ
  · intro x hx1 hx2
    obtain ⟨y, hy, hΦy⟩ := hshell x hx1 hx2
    exact ⟨_, y, hy, hΦy⟩
  · intro x hx1 hx2
    have hx1' : 1 ≤ ‖x‖ := by linarith
    obtain ⟨y, hy, hΦy⟩ := hshell x hx1' hx2
    refine ⟨y, ?_, hΦy⟩
    have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (by linarith)
    rw [hy, hRdef, sphereDirection_shellTwist (C.attaching b) J r hx0, shellStep_of_ge hr hx1, hJ1]
    simp

end GC.Seifert.SplitTube
