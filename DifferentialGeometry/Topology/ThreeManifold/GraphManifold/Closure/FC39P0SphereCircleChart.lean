import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereEdgeBase
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.CycleRimCharts
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

/-!
# FC39 producer, packet P0 (gate 1): the S³ circle kind, the global circle chart

Part A of the circle kind of the S³ inhabitant (stereographic convention of
`FC39P0SphereZero.lean`: `x = cycleBallAmbient false y`, radius `r = ‖y‖`, direction
`θ = y / r`, cap coordinate `w = stereo_N θ`, `ψ = ‖w‖`). The circle fibres are the orbits of the
rotation about the axis `N` of `S²`; in the base coordinates `(ψ, r)` the global chart is

  `J((ψ, r), c) = cycleBallAmbient false (r • stereo_N⁻¹ (ψ • planeOfCircle c))`

on the open square `(1/2, 8)²` of the base (`ψ` and `r` both in `(1/2, 8)`).

* `sphereCircleEquiv : ℝ² ≃L ℝ × ℝ` — the base coordinates `c ↦ (ψ, r)`;
* `sphereCirclePolar` — the planar polar chart on the wide annulus `1/2 < ‖w‖ < 8`, times the
  identity in `r` (the pattern of `standardCycleRim`);
* `sphereCircleShell` — `(w, r) ↦ cycleBallAmbient false (r • stereo_N⁻¹ w)` on `r > 0` (the
  pattern of `cycleHandleChart`);
* `sphereCircleChart = sphereCirclePolar.trans sphereCircleShell`, with its source, closed form
  and inverse;
* two small diffeomorphism helpers for open subtypes (`opensDiffeoOfForall_CIRCA`,
  `opensProdDiffeo_CIRCA`). The conversion "partial diffeomorphism → diffeomorphism between an
  open subset of the source and its image" is the tree's `PartialDiffeomorph.toOpensDiffeo`
  (`Topology/Manifold/PartialDiffeomorph/Opens.lean`), reused in `FC39P0SphereCircleBase.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Topology.Manifold Manifold
open scoped Manifold ContDiff Topology InnerProductSpace

namespace GC.GraphManifold.Assembly.FC39P0

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

local instance sphereCircleDim_CIRCA : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

/-! ## Two diffeomorphisms of open subtypes -/

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

/-- An open subset containing every point is diffeomorphic to the whole manifold. -/
def opensDiffeoOfForall_CIRCA (U : TopologicalSpace.Opens M) (hU : ∀ x, x ∈ U) :
    U ≃ₘ⟮I, I⟯ M where
  toFun := Subtype.val
  invFun x := ⟨x, hU x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := contMDiff_subtype_val
  contMDiff_invFun x := codRestr_contMDiffAt (V := U) (f := id) hU (contMDiffAt_id (x := x))

theorem opensDiffeoOfForall_CIRCA_apply (U : TopologicalSpace.Opens M) (hU : ∀ x, x ∈ U)
    (x : U) : opensDiffeoOfForall_CIRCA (I := I) U hU x = x.val :=
  rfl

/-- An open subset of a product cut out by a condition on the first coordinate is diffeomorphic
to the product of the corresponding open subset of the first factor with the second factor. -/
def opensProdDiffeo_CIRCA (U : TopologicalSpace.Opens M) (V : TopologicalSpace.Opens (M × N))
    (hV : ∀ p, p ∈ V ↔ p.1 ∈ U) : V ≃ₘ⟮I.prod J, I.prod J⟯ (U × N) where
  toFun p := (⟨p.1.1, (hV p.1).1 p.2⟩, p.1.2)
  invFun q := ⟨(q.1.1, q.2), (hV _).2 q.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := by
    refine ContMDiff.prodMk (fun p => ?_) (contMDiff_snd.comp contMDiff_subtype_val)
    exact codRestr_contMDiffAt (V := U) (f := fun p : V => p.1.1) (fun p => (hV p.1).1 p.2)
      ((contMDiff_fst.comp contMDiff_subtype_val) p)
  contMDiff_invFun q :=
    codRestr_contMDiffAt (V := V) (f := fun q : U × N => (q.1.1, q.2))
      (fun q => (hV _).2 q.1.2) ((contMDiff_subtype_val.prodMap contMDiff_id) q)

theorem opensProdDiffeo_CIRCA_apply (U : TopologicalSpace.Opens M)
    (V : TopologicalSpace.Opens (M × N)) (hV : ∀ p, p ∈ V ↔ p.1 ∈ U) (p : V) :
    opensProdDiffeo_CIRCA (I := I) (J := J) U V hV p = (⟨p.1.1, (hV p.1).1 p.2⟩, p.1.2) :=
  rfl

end Helpers

/-! ## The base coordinates `(ψ, r)` and the open base square -/

/-- The base coordinates `c ↦ (ψ, r) = (c 0, c 1)` of `ℝ²`. -/
def sphereCircleEquiv : E2 ≃L[ℝ] ℝ × ℝ :=
  (EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)

/-- The open interval `(1/2, 8)` of both base coordinates. -/
def sphereCircleWide : Set ℝ :=
  Ioo (1 / 2) 8

/-- The open base square `{(ψ, r) ∈ (1/2, 8)²}` of `ℝ²`. -/
def sphereCircleBaseSet : Set E2 :=
  sphereCircleEquiv ⁻¹' (sphereCircleWide ×ˢ sphereCircleWide)

/-- The open base square as an open subset of `ℝ²` (the base manifold of the circle bundle). -/
def sphereCircleBaseOpens : TopologicalSpace.Opens E2 :=
  ⟨sphereCircleBaseSet, (isOpen_Ioo.prod isOpen_Ioo).preimage sphereCircleEquiv.continuous⟩

theorem mem_sphereCircleBaseSet {c : E2} :
    c ∈ sphereCircleBaseSet ↔ (sphereCircleEquiv c).1 ∈ sphereCircleWide ∧
      (sphereCircleEquiv c).2 ∈ sphereCircleWide :=
  Iff.rfl

theorem sphereCircleEquiv_symm_mem {a b : ℝ} (ha : a ∈ sphereCircleWide)
    (hb : b ∈ sphereCircleWide) : sphereCircleEquiv.symm (a, b) ∈ sphereCircleBaseSet := by
  change sphereCircleEquiv (sphereCircleEquiv.symm (a, b)) ∈ sphereCircleWide ×ˢ sphereCircleWide
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact ⟨ha, hb⟩

/-! ## The planar polar chart on the wide annulus (times the identity in `r`) -/

theorem planeOfCircle_norm_CIRCA (t : Circle) : ‖planeOfCircle t‖ = 1 := by
  rw [planeOfCircle, LinearIsometryEquiv.norm_map, Circle.norm_coe]

theorem norm_smul_planeOfCircle_CIRCA {a : ℝ} (ha : 0 < a) (t : Circle) :
    ‖a • planeOfCircle t‖ = a := by
  rw [norm_smul, Real.norm_of_nonneg ha.le, planeOfCircle_norm_CIRCA, mul_one]

theorem sphereCircleWide_pos {a : ℝ} (ha : a ∈ sphereCircleWide) : 0 < a := by
  have h := ha.1
  linarith

/-- The polar map `((ψ, r), c) ↦ (ψ • planeOfCircle c, r)`. -/
def sphereCirclePolarMap (p : E2 × Circle) : E2 × ℝ :=
  ((sphereCircleEquiv p.1).1 • planeOfCircle p.2, (sphereCircleEquiv p.1).2)

/-- The inverse polar map `(w, r) ↦ ((‖w‖, r), w / ‖w‖)`. -/
def sphereCirclePolarInv (q : E2 × ℝ) : E2 × Circle :=
  (sphereCircleEquiv.symm (‖q.1‖, q.2), unitOf (Complex.orthonormalBasisOneI.repr.symm q.1))

/-- The target of the polar chart: `1/2 < ‖w‖ < 8`, `1/2 < r < 8`. -/
def sphereCirclePolarTarget : Set (E2 × ℝ) :=
  {q | ‖q.1‖ ∈ sphereCircleWide ∧ q.2 ∈ sphereCircleWide}

theorem isOpen_sphereCirclePolarTarget : IsOpen sphereCirclePolarTarget :=
  (isOpen_Ioo.preimage (continuous_norm.comp continuous_fst)).inter
    (isOpen_Ioo.preimage continuous_snd)

theorem sphereCirclePolarInv_ne_zero {q : E2 × ℝ} (hq : q ∈ sphereCirclePolarTarget) :
    Complex.orthonormalBasisOneI.repr.symm q.1 ≠ 0 := by
  intro hz
  have h := congrArg Complex.orthonormalBasisOneI.repr hz
  have hzero : q.1 = 0 := by
    simpa only [LinearIsometryEquiv.apply_symm_apply, map_zero] using h
  have hlow := hq.1.1
  rw [hzero, norm_zero] at hlow
  norm_num at hlow

/-- **The planar polar chart** on the wide annulus `1/2 < ‖w‖ < 8`, times the identity in the
radius `r ∈ (1/2, 8)`, with the base coordinates `(ψ, r)` read through `sphereCircleEquiv`. -/
def sphereCirclePolar : PartialDiffeomorph ((𝓡 2).prod (𝓡 1)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
    (E2 × Circle) (E2 × ℝ) ∞ where
  toFun := sphereCirclePolarMap
  invFun := sphereCirclePolarInv
  source := sphereCircleBaseSet ×ˢ univ
  target := sphereCirclePolarTarget
  map_source' := by
    intro p hp
    refine ⟨?_, hp.1.2⟩
    change ‖(sphereCircleEquiv p.1).1 • planeOfCircle p.2‖ ∈ sphereCircleWide
    rw [norm_smul_planeOfCircle_CIRCA (sphereCircleWide_pos hp.1.1)]
    exact hp.1.1
  map_target' := by
    intro q hq
    exact ⟨sphereCircleEquiv_symm_mem hq.1 hq.2, mem_univ _⟩
  left_inv' := by
    intro p hp
    apply Prod.ext
    · change sphereCircleEquiv.symm
        (‖(sphereCircleEquiv p.1).1 • planeOfCircle p.2‖, (sphereCircleEquiv p.1).2) = p.1
      rw [norm_smul_planeOfCircle_CIRCA (sphereCircleWide_pos hp.1.1)]
      exact sphereCircleEquiv.symm_apply_apply p.1
    · change unitOf (Complex.orthonormalBasisOneI.repr.symm
        ((sphereCircleEquiv p.1).1 • planeOfCircle p.2)) = p.2
      simp only [planeOfCircle, map_smul, LinearIsometryEquiv.symm_apply_apply]
      exact unitOf_smul (sphereCircleWide_pos hp.1.1) p.2
  right_inv' := by
    intro q hq
    apply Prod.ext
    · change (sphereCircleEquiv (sphereCircleEquiv.symm (‖q.1‖, q.2))).1 •
        planeOfCircle (unitOf (Complex.orthonormalBasisOneI.repr.symm q.1)) = q.1
      rw [ContinuousLinearEquiv.apply_symm_apply]
      have h := congrArg Complex.orthonormalBasisOneI.repr
        (norm_smul_unitOf (Complex.orthonormalBasisOneI.repr.symm q.1))
      simpa only [planeOfCircle, map_smul, LinearIsometryEquiv.norm_map,
        LinearIsometryEquiv.apply_symm_apply] using h
    · change (sphereCircleEquiv (sphereCircleEquiv.symm (‖q.1‖, q.2))).2 = q.2
      rw [ContinuousLinearEquiv.apply_symm_apply]
  open_source := sphereCircleBaseOpens.isOpen.prod isOpen_univ
  open_target := isOpen_sphereCirclePolarTarget
  contMDiffOn_toFun := by
    have hψ : ContMDiff ((𝓡 2).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞
        (fun p : E2 × Circle => (sphereCircleEquiv p.1).1) :=
      (contDiff_fst.comp sphereCircleEquiv.contDiff).contMDiff.comp contMDiff_fst
    have hr : ContMDiff ((𝓡 2).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞
        (fun p : E2 × Circle => (sphereCircleEquiv p.1).2) :=
      (contDiff_snd.comp sphereCircleEquiv.contDiff).contMDiff.comp contMDiff_fst
    have ht : ContMDiff ((𝓡 2).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
        (fun p : E2 × Circle => planeOfCircle p.2) :=
      Complex.orthonormalBasisOneI.repr.contDiff.contMDiff.comp
        (contMDiff_circle_coe.comp contMDiff_snd)
    exact ((hψ.smul ht).prodMk hr).contMDiffOn
  contMDiffOn_invFun := by
    have hn : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun q : E2 × ℝ => ‖q.1‖)
        sphereCirclePolarTarget := by
      intro q hq
      have hz : q.1 ≠ 0 := by
        intro h0
        have hlow := hq.1.1
        rw [h0, norm_zero] at hlow
        norm_num at hlow
      exact ((contDiffAt_norm ℝ hz).contMDiffAt.comp q contMDiffAt_fst).contMDiffWithinAt
    have hb : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E2) ∞
        (fun q : E2 × ℝ => sphereCircleEquiv.symm (‖q.1‖, q.2)) sphereCirclePolarTarget :=
      sphereCircleEquiv.symm.contDiff.contMDiff.comp_contMDiffOn
        (hn.prodMk_space contMDiff_snd.contMDiffOn)
    have hu : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 1) ∞
        (fun q : E2 × ℝ => unitOf (Complex.orthonormalBasisOneI.repr.symm q.1))
        sphereCirclePolarTarget :=
      contMDiffOn_unitOf.comp
        (Complex.orthonormalBasisOneI.repr.symm.contDiff.contMDiff.comp
          contMDiff_fst).contMDiffOn (fun q hq => sphereCirclePolarInv_ne_zero hq)
    exact hb.prodMk hu

theorem sphereCirclePolar_source : sphereCirclePolar.source = sphereCircleBaseSet ×ˢ univ :=
  rfl

theorem sphereCirclePolar_target : sphereCirclePolar.target = sphereCirclePolarTarget :=
  rfl

theorem sphereCirclePolar_apply (p : E2 × Circle) :
    sphereCirclePolar p = ((sphereCircleEquiv p.1).1 • planeOfCircle p.2,
      (sphereCircleEquiv p.1).2) :=
  rfl

theorem sphereCirclePolar_symm_apply (q : E2 × ℝ) :
    sphereCirclePolar.symm q = (sphereCircleEquiv.symm (‖q.1‖, q.2),
      unitOf (Complex.orthonormalBasisOneI.repr.symm q.1)) :=
  rfl

/-! ## The stereographic shell `(w, r) ↦ r • stereo_N⁻¹ w` -/

/-- **The stereographic shell chart** `(w, r) ↦ cycleBallAmbient false (r • stereo_N⁻¹ w)` on
`r > 0` (the pattern of `cycleHandleChart`, with the identity in place of the radius profile). -/
def sphereCircleShell : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (E2 × ℝ)
    sphereW.Carrier ∞ :=
  ((DifferentialGeometry.Topology.PartialDiffeomorph.prod (Handle.stereoChart northPole).symm
    (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞).toPartialDiffeomorph).trans
      (spherePolarChart (n := 2) southPole)).trans (cycleBallAmbient false)

theorem sphereCircleShell_apply (q : E2 × ℝ) :
    sphereCircleShell q =
      cycleBallAmbient false (q.2 • ((Handle.stereoChart northPole).symm q.1 : E3)) :=
  rfl

theorem sphereCircleShell_source : sphereCircleShell.source = {q | 0 < q.2} := by
  ext q
  change ((q.1 ∈ (Handle.stereoChart northPole).target ∧ q.2 ∈ univ) ∧ 0 < q.2) ∧
    q.2 • ((Handle.stereoChart northPole).symm q.1 : E3) ∈ (cycleBallAmbient false).source ↔
      0 < q.2
  rw [cycleBallAmbient_source, Handle.stereoChart_target]
  simp only [mem_univ, and_true, true_and]

/-! ## The global circle chart `J` -/

/-- **The global circle chart** `J((ψ, r), c) = cycleBallAmbient false (r • stereo_N⁻¹ (ψ •
planeOfCircle c))` on `(1/2, 8)² × Circle`. -/
def sphereCircleChart : PartialDiffeomorph ((𝓡 2).prod (𝓡 1)) (𝓡 3) (E2 × Circle)
    sphereW.Carrier ∞ :=
  sphereCirclePolar.trans sphereCircleShell

theorem sphereCircleChart_apply (p : E2 × Circle) :
    sphereCircleChart p = cycleBallAmbient false ((sphereCircleEquiv p.1).2 •
      ((Handle.stereoChart northPole).symm ((sphereCircleEquiv p.1).1 • planeOfCircle p.2) :
        E3)) :=
  rfl

theorem sphereCircleChart_source :
    sphereCircleChart.source = sphereCircleBaseSet ×ˢ univ := by
  ext p
  change p ∈ sphereCirclePolar.source ∧ sphereCirclePolar p ∈ sphereCircleShell.source ↔ _
  rw [sphereCircleShell_source, sphereCirclePolar_source]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, sphereCircleWide_pos h.1.2⟩

theorem sphereCircleChart_symm_apply (x : sphereW.Carrier) :
    sphereCircleChart.symm x = sphereCirclePolar.symm (sphereCircleShell.symm x) :=
  rfl

theorem sphereCircleShell_symm_apply (x : sphereW.Carrier) :
    sphereCircleShell.symm x =
      (Handle.stereoChart northPole (sphereDirection southPole ((cycleBallAmbient false).symm x)),
        ‖(cycleBallAmbient false).symm x‖) :=
  rfl

/-- The chart in the base coordinates `(ψ, r)` given as numbers. -/
theorem sphereCircleChart_equiv_symm (ψ r : ℝ) (c : Circle) :
    sphereCircleChart (sphereCircleEquiv.symm (ψ, r), c) = cycleBallAmbient false
      (r • ((Handle.stereoChart northPole).symm (ψ • planeOfCircle c) : E3)) := by
  rw [sphereCircleChart_apply, ContinuousLinearEquiv.apply_symm_apply]

end GC.GraphManifold.Assembly.FC39P0
