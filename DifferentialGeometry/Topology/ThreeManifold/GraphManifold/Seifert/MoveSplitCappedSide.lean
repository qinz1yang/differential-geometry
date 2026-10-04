import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCapped

/-!
# The capped side of the split sphere near the cap

Lane N2c, tier 2 (capped sides, first part). For a spherical capping `K` of `M` along a tube
system `T`, `coreMap K` reads a point of `M` in the core through the core inclusion; it is
injective on the core (`coreMap_injOn`) and a local diffeomorphism at every interior point of the
core (`isLocalDiffeomorphAt_coreMap`), which are the points off the boundary spheres
(`isInteriorPoint_of_forall_ne`).

For the split tube of `SplitCharts` the levels `1 < |h| < 3` of the tube are interior points of
the core (`tubeMap_isInteriorPoint`), and `coreMap K ∘ tubeMap` is a local diffeomorphism there
(`isLocalDiffeomorphAt_coreMap_tubeMap`). The cap of side `t` and the tube on that side form one
ball chart of radius `5/2` of the capped manifold (`exists_sideBall`): a map `Φ` of Euclidean
space, a local diffeomorphism and injective on the open ball of radius `5/2`, sending the closed
unit ball onto the cap, reading the tube level `± ‖x‖` on the shell `1 ≤ ‖x‖ < 5/2`, and the tube
untwisted, `Φ x = coreMap K (tubeMap (x / ‖x‖, ± ‖x‖))`, on `1 + r/2 ≤ ‖x‖ < 5/2`. It extends the
cap ball of `exists_capBall` by the tube itself beyond the collar of the cap.
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

private local instance sideFact : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance sideFact2 : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
private local instance sideCellCharts : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2
private local instance sideCellSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

section CoreMap

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (K : SphericalCapping M N T)

open Classical in
def coreMap (q : M.Carrier) : N.Carrier :=
  if h : q ∈ T.core then K.coreInclusion ⟨q, h⟩ else
    K.cap ((Classical.choose (show ∃ a, q ∈ T.removedBand a by
      simpa [SphericalTubeSystem.core] using h)), true) (sphereToClosedCell poleS2)

theorem coreMap_of_mem {q : M.Carrier} (h : q ∈ T.core) :
    coreMap K q = K.coreInclusion ⟨q, h⟩ :=
  dite_eq_left h

theorem coreMap_val (x : T.core) : coreMap K x.val = K.coreInclusion x :=
  coreMap_of_mem K x.2

theorem coreMap_injOn : InjOn (coreMap K) T.core := by
  intro q hq q' hq' h
  rw [coreMap_of_mem K hq, coreMap_of_mem K hq'] at h
  let _ := K.coreCharts
  let _ := K.coreSmooth
  exact congrArg Subtype.val (K.core_embedding.isEmbedding.injective h)

open DifferentialGeometry.Topology.Manifold in
theorem isLocalDiffeomorphAt_coreMap (x : T.core)
    (hx : letI := K.coreCharts; (𝓡∂ 3).IsInteriorPoint x) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (coreMap K) x.val := by
  let _ := K.coreCharts
  let _ := K.coreSmooth
  have hc : IsLocalDiffeomorphAt (𝓡∂ 3) (𝓡 3) ∞ K.coreInclusion x :=
    isLocalDiffeomorphAt_of_isInteriorPoint_of_injective_mfderiv
      K.core_embedding.contMDiff hx rfl
      ((K.core_embedding.isImmersion.isImmersionAt x).mfderiv_injective (by simp))
  have hs : IsLocalDiffeomorphAt (𝓡∂ 3) (𝓡 3) ∞ (Subtype.val : T.core → M.Carrier) x :=
    isLocalDiffeomorphAt_of_isInteriorPoint_of_injective_mfderiv
      K.core_induced.contMDiff hx rfl
      ((K.core_induced.isImmersion.isImmersionAt x).mfderiv_injective (by simp))
  have heq : coreMap K ∘ (Subtype.val : T.core → M.Carrier) = K.coreInclusion :=
    funext (coreMap_val K)
  have hc' : IsLocalDiffeomorphAt (𝓡∂ 3) (𝓡 3) ∞
      (coreMap K ∘ (Subtype.val : T.core → M.Carrier)) x := by
    rw [heq]
    exact hc
  exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp hc' hs

theorem isInteriorPoint_of_forall_ne (x : T.core)
    (hx : ∀ b z, T.boundarySphere b z ≠ x.val) :
    letI := K.coreCharts; (𝓡∂ 3).IsInteriorPoint x := by
  let _ := K.coreCharts
  rcases (𝓡∂ 3).isInteriorPoint_or_isBoundaryPoint x with h | h
  · exact h
  · have hb : x ∈ (𝓡∂ 3).boundary T.core := h
    rw [K.core_boundary] at hb
    obtain ⟨b, z, hz⟩ := mem_iUnion.mp hb
    exact absurd (congrArg Subtype.val hz) (hx b z)

theorem coreInclusion_ne_cap_of_forall_ne (x : T.core)
    (hx : ∀ b z, T.boundarySphere b z ≠ x.val) (b : T.Boundary) (w : ClosedCell 3) :
    K.coreInclusion x ≠ K.cap b w := by
  intro h
  let _ := K.coreCharts
  let _ := K.coreSmooth
  have hmem : K.coreInclusion x ∈ range K.coreInclusion ∩ range (K.cap b) :=
    ⟨⟨x, rfl⟩, ⟨w, h.symm⟩⟩
  rw [K.core_cap_intersection b] at hmem
  obtain ⟨z, hz⟩ := hmem
  have := congrArg Subtype.val (K.core_embedding.isEmbedding.injective hz)
  exact hx b z this

end CoreMap

namespace SplitCharts

section SideBall

variable {Q : ClosedOrientedManifold.{u} 3} (C : SplitCharts Q.Carrier)

theorem tubeSystem_tube (q : S2 × Icc (-2 : ℝ) 2) :
    C.tubeSystem.tube () q = C.tubeMap (q.1, q.2.val) :=
  rfl

theorem tubeMap_mem_core {q : S2 × ℝ} (h1 : 1 ≤ |q.2|) (h3 : |q.2| < 3) :
    C.tubeMap q ∈ C.tubeSystem.core := by
  intro hq
  simp only [mem_iUnion, SphericalTubeSystem.removedBand, mem_image] at hq
  obtain ⟨a, y, hy, he⟩ := hq
  have hy3 : |y.2.val| < 3 := abs_lt.mpr ⟨by linarith [y.2.2.1], by linarith [y.2.2.2]⟩
  have he' : C.tubeMap (y.1, y.2.val) = C.tubeMap q := he
  have hq' := congrArg Prod.snd (C.tubeMap_injOn hy3 h3 he')
  simp only at hq'
  have : |y.2.val| < 1 := abs_lt.mpr ⟨hy.1, hy.2⟩
  rw [hq'] at this
  linarith

theorem boundarySphere_eq (b : C.tubeSystem.Boundary) (z : S2) :
    C.tubeSystem.boundarySphere b z = C.tubeMap (z, sgnR b.2) := by
  change C.tubeMap (z, (SphericalTubeSystem.boundaryLevel b.2 : ℝ)) = _
  cases b.2 <;> simp [SphericalTubeSystem.boundaryLevel, sgnR]

theorem tubeMap_ne_boundarySphere {q : S2 × ℝ} (h1 : 1 < |q.2|) (h3 : |q.2| < 3)
    (b : C.tubeSystem.Boundary) (z : S2) : C.tubeSystem.boundarySphere b z ≠ C.tubeMap q := by
  rw [boundarySphere_eq]
  intro he
  have hb : |sgnR b.2| < 3 := by rcases sgnR_eq b.2 with h | h <;> rw [h] <;> norm_num
  have hq' := congrArg Prod.snd (C.tubeMap_injOn hb h3 he)
  simp only at hq'
  rw [← hq'] at h1
  rcases sgnR_eq b.2 with h | h <;> rw [h] at h1 <;> norm_num at h1

variable {N : ClosedOrientedManifold.{u} 3} (K : SphericalCapping Q N C.tubeSystem)

theorem tubeMap_isInteriorPoint {q : S2 × ℝ} (h1 : 1 < |q.2|) (h3 : |q.2| < 3) :
    letI := K.coreCharts
    (𝓡∂ 3).IsInteriorPoint
      (⟨C.tubeMap q, C.tubeMap_mem_core h1.le h3⟩ : C.tubeSystem.core) :=
  isInteriorPoint_of_forall_ne K _ fun b z => C.tubeMap_ne_boundarySphere h1 h3 b z

theorem isLocalDiffeomorphAt_coreMap_tubeMap {q : S2 × ℝ} (h1 : 1 < |q.2|) (h3 : |q.2| < 3) :
    IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (coreMap K ∘ C.tubeMap) q :=
  (C.isLocalDiffeomorphAt_tubeMap h3).comp (𝓡 3) N.Carrier
    (isLocalDiffeomorphAt_coreMap K _ (C.tubeMap_isInteriorPoint K h1 h3))

theorem coreMap_tubeMap_inj {q q' : S2 × ℝ} (h1 : 1 ≤ |q.2|) (h3 : |q.2| < 3)
    (h1' : 1 ≤ |q'.2|) (h3' : |q'.2| < 3)
    (he : coreMap K (C.tubeMap q) = coreMap K (C.tubeMap q')) : q = q' :=
  C.tubeMap_injOn h3 h3'
    (coreMap_injOn K (C.tubeMap_mem_core h1 h3) (C.tubeMap_mem_core h1' h3') he)

theorem coreMap_tubeMap_ne_cap {q : S2 × ℝ} (h1 : 1 < |q.2|) (h3 : |q.2| < 3)
    (b : C.tubeSystem.Boundary) (w : ClosedCell 3) :
    coreMap K (C.tubeMap q) ≠ K.cap b w := by
  rw [coreMap_of_mem K (C.tubeMap_mem_core h1.le h3)]
  exact coreInclusion_ne_cap_of_forall_ne K _
    (fun b' z => C.tubeMap_ne_boundarySphere h1 h3 b' z) b w

theorem sgnR_ne_zero (t : Bool) : sgnR t ≠ 0 := by
  rcases sgnR_eq t with h | h <;> rw [h] <;> norm_num

theorem abs_sgnR_mul (t : Bool) (a : ℝ) : |sgnR t * a| = |a| := by
  rcases sgnR_eq t with h | h <;> rw [h] <;> simp

def sideFlip (t : Bool) :
    (S2 × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), (𝓡 2).prod 𝓘(ℝ, ℝ)⟯ (S2 × ℝ) :=
  (Diffeomorph.refl (𝓡 2) S2 ∞).prodCongr (LinearEquiv.smulOfUnit
    (Units.mk0 (sgnR t) (sgnR_ne_zero t))).toContinuousLinearEquiv.toDiffeomorph

theorem sideFlip_apply (t : Bool) (q : S2 × ℝ) : sideFlip t q = (q.1, sgnR t * q.2) :=
  rfl

theorem tube_projIcc (t : Bool) (z : S2) {a : ℝ} (ha : |a| ≤ 2) :
    C.tubeSystem.tube () (z, projIcc (-2) 2 (by norm_num) (if t then a else -a)) =
      C.tubeMap (z, sgnR t * a) := by
  have hmem : (if t then a else -a) ∈ Icc (-2 : ℝ) 2 := by
    have h := abs_le.mp ha
    cases t <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> constructor <;> linarith
  rw [tubeSystem_tube, projIcc_of_mem _ hmem]
  cases t <;> simp [sgnR]

theorem exists_sideBall (t : Bool) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 2 ∧ ∃ Φ : E3 → N.Carrier,
      (∀ x, ‖x‖ < 5 / 2 → IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ Φ x) ∧
      InjOn Φ (ball 0 (5 / 2)) ∧
      (∀ x, ‖x‖ ≤ 1 → ∃ w : ClosedCell 3, Φ x = K.cap ((), t) w) ∧
      (∀ w : ClosedCell 3, ∃ x, ‖x‖ ≤ 1 ∧ Φ x = K.cap ((), t) w) ∧
      (∀ x, 1 ≤ ‖x‖ → ‖x‖ < 5 / 2 → ∃ z : S2, Φ x = coreMap K (C.tubeMap (z, sgnR t * ‖x‖))) ∧
      ∀ x, 1 + r / 2 ≤ ‖x‖ → ‖x‖ < 5 / 2 →
        Φ x = coreMap K (C.tubeMap (Manifold.sphereDirection poleS2 x, sgnR t * ‖x‖)) := by
  obtain ⟨r, hr, hr2, Φ₀, hloc, hinj, hin, hsurj, hshell, hshell'⟩ := exists_capBall K ((), t)
  set G : E3 → N.Carrier := fun x =>
    coreMap K (C.tubeMap (Manifold.sphereDirection poleS2 x, sgnR t * ‖x‖)) with hG
  have hsh : ∀ x : E3, 1 ≤ ‖x‖ → ‖x‖ < 1 + r →
      ∃ z : S2, Φ₀ x = coreMap K (C.tubeMap (z, sgnR t * ‖x‖)) := by
    intro x h1 h2
    obtain ⟨z, y, hy, hΦ⟩ := hshell x h1 h2
    refine ⟨z, ?_⟩
    rw [hΦ, ← coreMap_val, hy]
    exact congrArg (coreMap K)
      (C.tube_projIcc t z (by rw [abs_of_nonneg (norm_nonneg x)]; linarith))
  have hsh' : ∀ x : E3, 1 + r / 2 ≤ ‖x‖ → ‖x‖ < 1 + r → Φ₀ x = G x := by
    intro x h1 h2
    obtain ⟨y, hy, hΦ⟩ := hshell' x h1 h2
    rw [hΦ, ← coreMap_val, hy]
    exact congrArg (coreMap K)
      (C.tube_projIcc t _ (by rw [abs_of_nonneg (norm_nonneg x)]; linarith))
  let Φ : E3 → N.Carrier := fun x => if ‖x‖ < 1 + r then Φ₀ x else G x
  have hΦin : ∀ x : E3, ‖x‖ < 1 + r → Φ x = Φ₀ x := fun x hx => ite_eq_left hx
  have hΦout : ∀ x : E3, 1 + r / 2 ≤ ‖x‖ → Φ x = G x := fun x hx => by
    by_cases h : ‖x‖ < 1 + r
    · rw [hΦin x h, hsh' x hx h]
    · exact ite_eq_right h
  have hlev : ∀ x : E3, 1 ≤ ‖x‖ → ‖x‖ < 3 → 1 ≤ |sgnR t * ‖x‖| ∧ |sgnR t * ‖x‖| < 3 := by
    intro x h1 h3
    rw [abs_sgnR_mul, abs_of_nonneg (norm_nonneg x)]
    exact ⟨h1, h3⟩
  have hGloc : ∀ x : E3, 1 < ‖x‖ → ‖x‖ < 3 → IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ G x := by
    intro x h1 h3
    have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (by linarith)
    have hp : IsLocalDiffeomorphAt (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
        (Manifold.spherePolarChart (n := 2) poleS2).symm x :=
      (Manifold.spherePolarChart (n := 2) poleS2).symm.isLocalDiffeomorphAt _ _ ∞ hx0
    have hf := (sideFlip t).isLocalDiffeomorph
      ((Manifold.spherePolarChart (n := 2) poleS2).symm x)
    have hl1 : 1 < |(sideFlip t ((Manifold.spherePolarChart (n := 2) poleS2).symm x)).2| := by
      rw [sideFlip_apply, Manifold.spherePolarChart_symm_apply, abs_sgnR_mul,
        abs_of_nonneg (norm_nonneg x)]
      exact h1
    have hl3 : |(sideFlip t ((Manifold.spherePolarChart (n := 2) poleS2).symm x)).2| < 3 := by
      rw [sideFlip_apply, Manifold.spherePolarChart_symm_apply, abs_sgnR_mul,
        abs_of_nonneg (norm_nonneg x)]
      exact h3
    have hc := C.isLocalDiffeomorphAt_coreMap_tubeMap K hl1 hl3
    exact (hp.comp _ _ hf).comp _ _ hc
  have hGshell : ∀ x : E3, 1 ≤ ‖x‖ → ‖x‖ < 5 / 2 →
      ∃ z : S2, Φ x = coreMap K (C.tubeMap (z, sgnR t * ‖x‖)) := by
    intro x h1 h2
    by_cases h : ‖x‖ < 1 + r
    · rw [hΦin x h]
      exact hsh x h1 h
    · exact ⟨_, ite_eq_right h⟩
  have hlevinj : ∀ x y : E3, 1 ≤ ‖x‖ → ‖x‖ < 5 / 2 → 1 ≤ ‖y‖ → ‖y‖ < 5 / 2 → ∀ z z' : S2,
      coreMap K (C.tubeMap (z, sgnR t * ‖x‖)) = coreMap K (C.tubeMap (z', sgnR t * ‖y‖)) →
        z = z' ∧ ‖x‖ = ‖y‖ := by
    intro x y hx1 hx2 hy1 hy2 z z' he
    have hx := hlev x hx1 (by linarith)
    have hy := hlev y hy1 (by linarith)
    have hq := C.coreMap_tubeMap_inj K hx.1 hx.2 hy.1 hy.2 he
    simp only [Prod.mk.injEq] at hq
    exact ⟨hq.1, mul_left_cancel₀ (sgnR_ne_zero t) hq.2⟩
  have hmix : ∀ x y : E3, ‖x‖ < 1 + r → 1 + r ≤ ‖y‖ → ‖y‖ < 5 / 2 → Φ x ≠ Φ y := by
    intro x y hx hy1 hy2 he
    obtain ⟨z', hz'⟩ := hGshell y (by linarith) hy2
    by_cases hx1 : 1 ≤ ‖x‖
    · obtain ⟨z, hz⟩ := hGshell x hx1 (by linarith)
      rw [hz, hz'] at he
      have := (hlevinj x y hx1 (by linarith) (by linarith) hy2 z z' he).2
      linarith
    · obtain ⟨w, hw⟩ := hin x (by linarith)
      rw [hΦin x hx, hw, hz'] at he
      have hy := hlev y (by linarith) (by linarith)
      exact C.coreMap_tubeMap_ne_cap K (lt_of_lt_of_le (by
        rw [abs_sgnR_mul, abs_of_nonneg (norm_nonneg y)]; linarith) le_rfl) hy.2 _ _ he.symm
  refine ⟨r, hr, hr2, Φ, ?_, ?_, ?_, ?_, hGshell, fun x h1 h2 => hΦout x h1⟩
  · intro x hx
    by_cases h : ‖x‖ < 1 + r
    · refine IsLocalDiffeomorphAt.of_eventuallyEq ?_ (hloc x h)
      exact Filter.eventuallyEq_of_mem ((isOpen_lt continuous_norm continuous_const).mem_nhds h)
        fun y hy => hΦin y hy
    · have h' : 1 + r / 2 < ‖x‖ := by push Not at h; linarith
      refine IsLocalDiffeomorphAt.of_eventuallyEq ?_ (hGloc x (by linarith) (by linarith))
      exact Filter.eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds h')
        fun y hy => hΦout y (le_of_lt hy)
  · intro x hx y hy hxy
    have hx' : ‖x‖ < 5 / 2 := mem_ball_zero_iff.mp hx
    have hy' : ‖y‖ < 5 / 2 := mem_ball_zero_iff.mp hy
    by_cases h1 : ‖x‖ < 1 + r <;> by_cases h2 : ‖y‖ < 1 + r
    · rw [hΦin x h1, hΦin y h2] at hxy
      exact hinj (mem_ball_zero_iff.mpr h1) (mem_ball_zero_iff.mpr h2) hxy
    · exact absurd hxy (hmix x y h1 (not_lt.mp h2) hy')
    · exact absurd hxy.symm (hmix y x h2 (not_lt.mp h1) hx')
    · push Not at h1 h2
      rw [hΦout x (by linarith), hΦout y (by linarith)] at hxy
      obtain ⟨hd, hn⟩ := hlevinj x y (by linarith) hx' (by linarith) hy' _ _ hxy
      have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (by linarith)
      have hy0 : y ≠ 0 := norm_ne_zero_iff.mp (by linarith)
      rw [← Manifold.norm_smul_sphereDirection poleS2 hx0,
        ← Manifold.norm_smul_sphereDirection poleS2 hy0, hd, hn]
  · intro x hx
    rw [hΦin x (by linarith)]
    exact hin x hx
  · intro w
    obtain ⟨x, hx, hΦ⟩ := hsurj w
    exact ⟨x, hx, by rw [hΦin x (by linarith), hΦ]⟩

end SideBall

end SplitCharts

end GC.Seifert.SplitTube

namespace GC.Seifert.ElementaryPresentation

open GC.Endpoint GC.GraphManifold

universe u

def OnSolidBoundary (q : (discPlanarBase.{u} 1).surface.Carrier × Circle) : Prop :=
  ∃ p : Torus, q = ((discPlanarBase.{u} 1).collar 0 (p.1, halfZero), p.2)

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (E : ElementaryPresentation (NoCuts.carrier Q))
  {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b)
  {T : SphericalTubeSystem Q.toClosedOrientedManifold} {N : ClosedOrientedManifold.{u} 3}
  (K : SphericalCapping Q.toClosedOrientedManifold N T) (a : T.Index)

def InSplitRegion (y : E.toTorus.cutCarrier.Carrier) : Prop :=
  y ∈ E.toTorus.components.piece (E.seamPiece j b) ∨
    y ∈ E.toTorus.components.piece (E.hostPiece j b)

structure SideData (δ₂ : ℝ) where
  port : Bool → Fin 3
  port_ne : ∀ t, port t ≠ E.hostSide h
  port_false_ne_true : port false ≠ port true
  holonomy : Bool → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
  solid : Bool → (discPlanarBase.{u} 1).surface.Carrier × Circle → N.Carrier
  smooth : ∀ t, ContMDiff ((SurfaceModel.model (discPlanarBase.{u} 1).surface.kind).prod (𝓡 1))
    (𝓡 3) ∞ (solid t)
  mfderiv_bijective : ∀ t q, Function.Bijective (mfderiv
    ((SurfaceModel.model (discPlanarBase.{u} 1).surface.kind).prod (𝓡 1)) (𝓡 3) (solid t) q)
  injective : ∀ t, Function.Injective (solid t)
  collar : ∀ t (p : Torus) (s : ℝ) (hs : 0 ≤ s), s < 1 →
    solid t ((discPlanarBase.{u} 1).collar 0 (p.1, halfPoint s hs), p.2) =
      SplitTube.coreMap K (E.hostMap h (planarCollarFormula 3 (port t)
        (((holonomy t p).1 : ℂ), δ₂ * s), (holonomy t p).2))
  cap_mem : ∀ t w, ∃ q, solid t q = K.cap (a, t) w
  core_mem : ∀ y : E.toTorus.cutCarrier.Carrier, E.InSplitRegion (j := j) (b := b) y →
    E.toTorus.cutMap y ∈ T.core → ∃ t q, solid t q = SplitTube.coreMap K (E.toTorus.cutMap y)
  image : ∀ t q, (∃ w, solid t q = K.cap (a, t) w) ∨ ∃ y : E.toTorus.cutCarrier.Carrier,
    E.InSplitRegion (j := j) (b := b) y ∧ E.toTorus.cutMap y ∈ T.core ∧
      solid t q = SplitTube.coreMap K (E.toTorus.cutMap y)
  boundary_of_eq : ∀ q q', solid false q = solid true q' →
    OnSolidBoundary q ∧ OnSolidBoundary q'

end GC.Seifert.ElementaryPresentation
