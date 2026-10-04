import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldDescentDomain
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldDescentCarrier
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldTube
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BundleOverAnnulus
import DifferentialGeometry.Topology.Manifold.InverseFunction

/-!
# The cone-fold descent map is a local diffeomorphism

In log coordinates `p = (x, log y, s)` a map `p ↦ (f(z), s - θ(z))`, `z = x + iy`, with `f`, `θ`
smooth and `det Df ≠ 0` has triangular derivative and is a local diffeomorphism into `ℂ × ℝ`
(`isLocalDiffeomorphAt_logLift`, inverse function theorem). The fibre phase has the real lift
`foldLift` (`cexp ∘ foldLift = foldPhase`, smooth where `ω_v` lies in the slit plane), so
`baseMap = (up, cexp) ∘ (f, s - foldLift)` and `liftMap = coneLift ∘ baseMap` are local
diffeomorphisms off the apex (`isLocalDiffeomorphAt_liftMap`); the tube map is one everywhere
(`isLocalDiffeomorphAt_tubeMap`), and on the apex disc `totalMap = tubeMap`. `coneLift`
commutes with the conjugation `conjMap` (`coneLift_conjMap`), which gives the mirror identity
`totalMap = conjMap ∘ totalMap ∘ flipMap` on the band about wall 0 (`totalMap_eq_mirror`). Hence
`mirrorMap` is a local diffeomorphism on `descentDomain` (`isLocalDiffeomorphOn_mirrorMap`), its
values lie over the filled base (`conePoint_mirrorMap_mem`), and the fold
`foldMap : descentDomain → pieceInterior ⊤` is a local diffeomorphism
(`isLocalDiffeomorph_foldMap`).
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped ContDiff ComplexConjugate Manifold

universe u

namespace GC.Seifert

private abbrev coord (i : Fin 3) : ModelCoordinates →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 3 => ℝ) i

private theorem isInvertible_of_injective_of_finrank_eq {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (h : Module.finrank ℝ E = Module.finrank ℝ F) {A : E →L[ℝ] F}
    (hA : Function.Injective A) : A.IsInvertible := by
  have hs : Function.Surjective A :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h (f := (A : E →ₗ[ℝ] F))).1 hA
  exact ⟨(LinearEquiv.ofBijective (A : E →ₗ[ℝ] F) ⟨hA, hs⟩).toContinuousLinearEquiv, by
    ext v
    rfl⟩

private theorem injective_of_det_ne_zero {A : ℂ →L[ℝ] ℂ} (h : A.det ≠ 0) :
    Function.Injective A := by
  have hu : IsUnit (A : ℂ →ₗ[ℝ] ℂ) :=
    (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  exact ((Module.End.isUnit_iff _).1 hu).1

private theorem finrank_complex_prod_real : Module.finrank ℝ (ℂ × ℝ) = 3 := by
  rw [Module.finrank_prod, Complex.finrank_real_complex, Module.finrank_self]

theorem eq_zero_of_logPointDeriv_eq_zero {q v : ModelCoordinates}
    (h : logPointDeriv q v = 0) : v 0 = 0 ∧ v 1 = 0 := by
  rw [logPointDeriv_apply] at h
  have h0 := congrArg Complex.re h
  have h1 := congrArg Complex.im h
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_zero,
    add_zero, zero_re, add_im, mul_im, zero_add, zero_im] at h0 h1
  refine ⟨by simpa using h0, ?_⟩
  have he := Real.exp_pos (q 1)
  have : Real.exp (q 1) * v 1 = 0 := by simpa using h1
  exact (mul_eq_zero.1 this).resolve_left he.ne'

theorem isLocalDiffeomorphAt_logLift {f : ℂ → ℂ} {θ : ℂ → ℝ} {O : Set ℂ} (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O) (hθ : ContDiffOn ℝ ∞ θ O) {p₀ : ModelCoordinates}
    (hp₀ : (logPoint p₀ : ℂ) ∈ O) (hdet : (fderiv ℝ f (logPoint p₀)).det ≠ 0) :
    IsLocalDiffeomorphAt (𝓡 3) 𝓘(ℝ, ℂ × ℝ) ∞
      (fun p : ModelCoordinates => (f (logPoint p), p 2 - θ (logPoint p))) p₀ := by
  set L : ModelCoordinates → ℂ := fun p => (logPoint p : ℂ)
  have hLc : ContDiff ℝ ∞ L := contDiff_coe_logPoint
  set S : Set ModelCoordinates := L ⁻¹' O
  have hS : IsOpen S := hO.preimage hLc.continuous
  have hK : ContDiffOn ℝ ∞ (fun p : ModelCoordinates => (f (L p), p 2 - θ (L p))) S :=
    (hf.comp hLc.contDiffOn (mapsTo_preimage L O)).prodMk
      ((coord 2).contDiff.contDiffOn.sub (hθ.comp hLc.contDiffOn (mapsTo_preimage L O)))
  refine isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible_mfderiv hS hp₀
    (contMDiffOn_iff_contDiffOn.2 hK) ?_
  have hfd : HasFDerivAt f (fderiv ℝ f (L p₀)) (L p₀) :=
    ((hf.contDiffAt (hO.mem_nhds hp₀)).differentiableAt (by simp)).hasFDerivAt
  have hθd : HasFDerivAt θ (fderiv ℝ θ (L p₀)) (L p₀) :=
    ((hθ.contDiffAt (hO.mem_nhds hp₀)).differentiableAt (by simp)).hasFDerivAt
  have hL : HasFDerivAt L (logPointDeriv p₀) p₀ := hasFDerivAt_logPoint p₀
  have h1 := hfd.comp p₀ hL
  have h2 := ((coord 2).hasFDerivAt (x := p₀)).sub (hθd.comp p₀ hL)
  have hK' : HasFDerivAt (fun p : ModelCoordinates => (f (L p), p 2 - θ (L p)))
      ((fderiv ℝ f (L p₀) ∘L logPointDeriv p₀).prod
        (coord 2 - fderiv ℝ θ (L p₀) ∘L logPointDeriv p₀)) p₀ := h1.prodMk h2
  rw [hK'.hasMFDerivAt.mfderiv]
  apply isInvertible_of_injective_of_finrank_eq
    (finrank_euclideanSpace_fin.trans finrank_complex_prod_real.symm)
  refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
  have hv1 : fderiv ℝ f (L p₀) (logPointDeriv p₀ v) = 0 := congrArg Prod.fst hv
  have hv2 : v 2 - fderiv ℝ θ (L p₀) (logPointDeriv p₀ v) = 0 := congrArg Prod.snd hv
  have hdz : logPointDeriv p₀ v = 0 :=
    injective_of_det_ne_zero hdet (hv1.trans (map_zero _).symm)
  obtain ⟨h0, h1'⟩ := eq_zero_of_logPointDeriv_eq_zero hdz
  rw [hdz, map_zero, sub_zero] at hv2
  ext i
  fin_cases i
  · exact h0
  · exact h1'
  · exact hv2

theorem isLocalDiffeomorphAt_logPair (p₀ : ModelCoordinates) :
    IsLocalDiffeomorphAt (𝓡 3) 𝓘(ℝ, ℂ × ℝ) ∞
      (fun p : ModelCoordinates => ((logPoint p : ℂ), p 2)) p₀ := by
  have h := isLocalDiffeomorphAt_logLift (f := id) (θ := fun _ => (0 : ℝ)) (p₀ := p₀) isOpen_univ
    contDiffOn_id contDiffOn_const (mem_univ _) (by
      rw [fderiv_id]
      change LinearMap.det (LinearMap.id : ℂ →ₗ[ℝ] ℂ) ≠ 0
      rw [LinearMap.det_id]
      exact one_ne_zero)
  refine DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq
    (Eventually.of_forall fun p => ?_) h
  simp

def planeCircleUp (y : ℂ × ℝ) : PlaneLift.{u} × Circle :=
  (ULift.up y.1, AnnulusStraightening.cexp y.2)

theorem isLocalDiffeomorph_planeCircleUp :
    IsLocalDiffeomorph 𝓘(ℝ, ℂ × ℝ) PlaneCircleModel ∞ planeCircleUp.{u} := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact (DifferentialGeometry.Topology.uliftDiffeomorph 𝓘(ℝ, ℂ) ℂ).isLocalDiffeomorph.prodMap
    AnnulusStraightening.isLocalDiffeomorph_cexp

private theorem linearTorusMap_inv (A : Matrix (Fin 2) (Fin 2) ℤ) (x : Torus) :
    linearTorusMap A x⁻¹ = (linearTorusMap A x)⁻¹ := by
  refine Prod.ext ?_ ?_ <;> simp [linearTorusMap, mul_comm]

private theorem unitOf_conj' (w : ℂ) : unitOf (conj w) = (unitOf w)⁻¹ := by
  by_cases hw : w = 0
  · simp [hw, unitOf]
  · exact unitOf_conj hw

namespace ConeFilling

variable (c : ConeFilling)

theorem coneLift_conjMap (x : PlaneLift.{u} × Circle) :
    c.coneLift (ConeShape.FoldData.conjMap x) =
      ConeShape.FoldData.conjMap (c.coneLift x) := by
  have hsub : conj x.1.down - ((3 / 2 : ℝ) : ℂ) = conj (x.1.down - ((3 / 2 : ℝ) : ℂ)) := by
    rw [map_sub, Complex.conj_ofReal]
  have hdepth : coneDepth (ConeShape.FoldData.conjMap x) = coneDepth x := by
    simp only [coneDepth, ConeShape.FoldData.conjMap]
    rw [hsub, Complex.norm_conj]
  have htorus : c.coneTorus (ConeShape.FoldData.conjMap x) = (c.coneTorus x)⁻¹ := by
    simp only [coneTorus, ConeShape.FoldData.conjMap]
    rw [hsub, unitOf_conj', ← linearTorusMap_inv]
    rfl
  rw [coneLift, coneLift, hdepth, htorus]
  refine Prod.ext (ULift.ext ?_) rfl
  change seamRadius c.p (coneDepth x) • (((c.coneTorus x)⁻¹).1 : ℂ) =
    conj (seamRadius c.p (coneDepth x) • ((c.coneTorus x).1 : ℂ))
  rw [Prod.fst_inv, Circle.coe_inv_eq_conj, Complex.real_smul, Complex.real_smul, map_mul,
    Complex.conj_ofReal]

end ConeFilling

namespace ConeShape

variable (σ : ConeShape)

def foldLift (q : ℤ) (z : ℂ) : ℝ :=
  q * ((1 - σ.foldChi z) * arg (coneDisc σ.vertexOne z)) / (2 * Real.pi)

theorem cexp_foldLift (q : ℤ) (z : ℂ) :
    AnnulusStraightening.cexp (σ.foldLift q z) = σ.foldPhase q z := by
  rw [AnnulusStraightening.cexp_eq, foldPhase, foldLift]
  congr 1
  field_simp

theorem contDiffAt_foldLift (q : ℤ) {z : ℂ} (hz : 0 < z.im)
    (hs : coneDisc σ.vertexOne z ∈ slitPlane) : ContDiffAt ℝ ∞ (σ.foldLift q) z := by
  have hlog : ContDiffAt ℝ ∞ (fun w => Complex.log (coneDisc σ.vertexOne w)) z :=
    ((Complex.contDiffAt_log hs).comp z
      (contDiffAt_coneDisc σ.vertexOne_im_pos hz)).restrict_scalars ℝ
  have him : ContDiffAt ℝ ∞ (fun w => (Complex.log (coneDisc σ.vertexOne w)).im) z :=
    Complex.imCLM.contDiff.contDiffAt.comp z hlog
  have heq : (fun w => (Complex.log (coneDisc σ.vertexOne w)).im) =
      fun w => arg (coneDisc σ.vertexOne w) := funext fun w => Complex.log_im _
  rw [heq] at him
  have hchi : ContDiffAt ℝ ∞ σ.foldChi z :=
    contDiffAt_const.sub ((contDiff_coneStep _ _).contDiffAt.comp z
      (contDiffAt_foldSplit (ne_zero_of_im_pos hz)))
  exact (contDiffAt_const.mul ((contDiffAt_const.sub hchi).mul him)).div_const _

end ConeShape

namespace ConeShape.FoldData

variable {σ : ConeShape} (D : σ.FoldData) (c : ConeFilling) (hθ : σ.θ₁ * c.p = Real.pi)

def conjDiffeo : (PlaneLift.{u} × Circle) ≃ₘ⟮PlaneCircleModel, PlaneCircleModel⟯
    (PlaneLift.{u} × Circle) where
  toFun := conjMap
  invFun := conjMap
  left_inv := conjMap_conjMap
  right_inv := conjMap_conjMap
  contMDiff_toFun := contMDiff_conjMap
  contMDiff_invFun := contMDiff_conjMap

theorem baseMap_eq_planeCircleUp (p : ModelCoordinates) :
    D.baseMap.{u} c p = planeCircleUp (D.f (logPoint p), p 2 - σ.foldLift c.q (logPoint p)) := by
  refine Prod.ext rfl ?_
  rw [baseMap_snd]
  change _ = AnnulusStraightening.cexp (p 2 - σ.foldLift c.q (logPoint p))
  rw [← σ.cexp_foldLift, AnnulusStraightening.cexp_eq, AnnulusStraightening.cexp_eq,
    ← Circle.exp_neg, ← Circle.exp_add]
  congr 1
  ring

theorem isLocalDiffeomorphAt_baseMap (hσ : σ.θ₂ = 0) {p : ModelCoordinates}
    (hU : (logPoint p : ℂ) ∈ D.U) (hv : (logPoint p : ℂ) ≠ σ.vertexOne)
    (hs : coneDisc σ.vertexOne (logPoint p) ∈ slitPlane) :
    IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞ (D.baseMap.{u} c) p := by
  set O : Set ℂ := {z | z ∈ D.U ∧ 0 < z.im ∧ coneDisc σ.vertexOne z ∈ slitPlane}
  have hO : IsOpen O := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hz1, hz2, hz3⟩
    have e1 : D.U ∈ 𝓝 z := D.isOpen_U.mem_nhds hz1
    have e2 : {w : ℂ | 0 < w.im} ∈ 𝓝 z := (isOpen_lt continuous_const continuous_im).mem_nhds hz2
    have e3 : ∀ᶠ w in 𝓝 z, coneDisc σ.vertexOne w ∈ slitPlane :=
      (contDiffAt_coneDisc σ.vertexOne_im_pos hz2).continuousAt.preimage_mem_nhds
        (Complex.isOpen_slitPlane.mem_nhds hz3)
    filter_upwards [e1, e2, e3] with w hw1 hw2 hw3
    exact ⟨hw1, hw2, hw3⟩
  have hf : ContDiffOn ℝ ∞ D.f O := D.contDiffOn_f.mono fun z hz => hz.1
  have hθl : ContDiffOn ℝ ∞ (σ.foldLift c.q) O := fun z hz =>
    (σ.contDiffAt_foldLift c.q hz.2.1 hz.2.2).contDiffWithinAt
  have hz2 : (logPoint p : ℂ) ≠ σ.vertexTwo := by
    rw [σ.cusp_vertexTwo hσ]
    exact ConeShape.ne_zero_of_im_pos (logPoint_im_pos p)
  have hdet := (D.det_fderiv_pos _ hU hv hz2).ne'
  have hK := isLocalDiffeomorphAt_logLift hO hf hθl ⟨hU, logPoint_im_pos p, hs⟩ hdet
  have hE := isLocalDiffeomorph_planeCircleUp.{u}
    (D.f (logPoint p), p 2 - σ.foldLift c.q (logPoint p))
  refine DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq
    (Eventually.of_forall fun p' => D.baseMap_eq_planeCircleUp c p') (hK.comp _ _ hE)

theorem isLocalDiffeomorphAt_liftMap (hσ : σ.θ₂ = 0) {p : ModelCoordinates}
    (hU : (logPoint p : ℂ) ∈ D.U) (hv : (logPoint p : ℂ) ≠ σ.vertexOne)
    (hs : coneDisc σ.vertexOne (logPoint p) ∈ slitPlane) (hf : D.f (logPoint p) ≠ 3 / 2) :
    IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞ (D.liftMap.{u} c) p := by
  have hsrc : D.baseMap.{u} c p ∈ c.coneLiftPartialDiffeomorph.source := by
    change (D.baseMap.{u} c p).1.down ≠ ((3 / 2 : ℝ) : ℂ)
    rw [baseMap_fst]
    push_cast
    exact hf
  exact (D.isLocalDiffeomorphAt_baseMap c hσ hU hv hs).comp _ _
    (c.coneLiftPartialDiffeomorph.isLocalDiffeomorphAt PlaneCircleModel PlaneCircleModel ∞ hsrc)

theorem tubeMap_eq_coneTube (p : ModelCoordinates) :
    σ.tubeMap.{u} c p = c.coneTube σ.vertexOne (logPoint p) (p 2) :=
  rfl

theorem isLocalDiffeomorphAt_tubeMap (p : ModelCoordinates) :
    IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞ (σ.tubeMap.{u} c) p :=
  (isLocalDiffeomorphAt_logPair p).comp PlaneCircleModel (PlaneLift.{u} × Circle)
    (c.isLocalDiffeomorphAt_coneTube σ.vertexOne_im_pos (logPoint_im_pos p) (p 2))

theorem totalMap_eq_tubeMap_of_mem_patchDisc {p : ModelCoordinates}
    (hp : (logPoint p : ℂ) ∈ D.patchDisc c hθ) : D.totalMap.{u} c p = σ.tubeMap c p := by
  by_cases hv : (logPoint p : ℂ) = σ.vertexOne
  · rw [totalMap, ite_eq_left hv]
  · rw [totalMap, ite_eq_right hv]
    obtain ⟨-, hf, hfar, -⟩ := D.discRadius_spec c hθ hp.1 hp.2
    exact (D.tubeMap_eq_liftMap c hv hfar hf).symm

theorem isOpen_logPoint_preimage {s : Set ℂ} (hs : IsOpen s) :
    IsOpen {p : ModelCoordinates | (logPoint p : ℂ) ∈ s} :=
  hs.preimage contDiff_coe_logPoint.continuous

theorem isLocalDiffeomorphAt_totalMap (hσ : σ.θ₂ = 0) {p : ModelCoordinates}
    (hz : (logPoint p : ℂ) ∈ D.patches c hθ) (hre : 0 ≤ (logPoint p : ℂ).re) :
    IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞ (D.totalMap.{u} c) p := by
  by_cases hd : (logPoint p : ℂ) ∈ D.patchDisc c hθ
  · have hev : D.totalMap.{u} c =ᶠ[𝓝 p] σ.tubeMap c :=
      Filter.eventually_of_mem ((isOpen_logPoint_preimage (D.isOpen_patchDisc c hθ)).mem_nhds hd)
        fun p' hp' => D.totalMap_eq_tubeMap_of_mem_patchDisc c hθ hp'
    exact DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq hev
      (isLocalDiffeomorphAt_tubeMap (σ := σ) c p)
  · obtain ⟨hU, hv, -, hf, hs⟩ := D.patches_good c hθ hσ hz hre hd
    have hev : D.totalMap.{u} c =ᶠ[𝓝 p] D.liftMap c := by
      have ho : IsOpen {p' : ModelCoordinates | (logPoint p' : ℂ) ≠ σ.vertexOne} :=
        isOpen_logPoint_preimage isOpen_ne
      exact Filter.eventually_of_mem (ho.mem_nhds hv) fun p' hp' => ite_eq_right hp'
    exact DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq hev
      (D.isLocalDiffeomorphAt_liftMap c hσ hU hv hs hf)

theorem foldPhase_eq_one_of_mem_patchZero (q : ℤ) {z : ℂ} (hz : z ∈ D.patchZero) :
    σ.foldPhase q z = 1 :=
  σ.foldPhase_eq_one q ⟨hz.1, lt_of_le_of_lt (le_abs_self _) hz.2.2.2.2.2⟩

theorem totalMap_eq_mirror {p : ModelCoordinates} (hz : (logPoint p : ℂ) ∈ D.patchZero) :
    D.totalMap.{u} c p = conjMap (D.totalMap c (flipMap p)) := by
  have hz' : (logPoint (flipMap p) : ℂ) ∈ D.patchZero := by
    rw [coe_logPoint_flipMap]
    exact D.refl_zero_mem_patchZero hz
  rw [totalMap, ite_eq_right (D.ne_vertexOne_of_mem_patchZero hz), totalMap,
    ite_eq_right (D.ne_vertexOne_of_mem_patchZero hz'), liftMap, liftMap, ← c.coneLift_conjMap]
  congr 1
  refine Prod.ext (ULift.ext ?_) ?_
  · change D.f (logPoint p) = conj (D.f (logPoint (flipMap p)))
    rw [coe_logPoint_flipMap]
    exact D.f_refl' hz.2.2.2.2.1
  · change Circle.exp (2 * Real.pi * p 2) * (σ.foldPhase c.q (logPoint p))⁻¹ =
      (Circle.exp (2 * Real.pi * flipMap p 2) * (σ.foldPhase c.q (logPoint (flipMap p)))⁻¹)⁻¹
    rw [D.foldPhase_eq_one_of_mem_patchZero c.q hz, D.foldPhase_eq_one_of_mem_patchZero c.q hz',
      flipMap_two, inv_one, mul_one, mul_one, ← Circle.exp_neg]
    congr 1
    ring

theorem mirrorMap_eq_totalMap_of_mem_patchZero {p : ModelCoordinates}
    (hz : (logPoint p : ℂ) ∈ D.patchZero) : D.mirrorMap.{u} c p = D.totalMap c p := by
  rw [mirrorMap]
  split_ifs with h
  · rw [D.totalMap_eq_mirror c hz]
  · rfl

theorem logPoint_re_eq (p : ModelCoordinates) : (logPoint p : ℂ).re = p 0 := by
  rw [coe_logPoint']

theorem isLocalDiffeomorphOn_mirrorMap (hσ : σ.θ₂ = 0) :
    IsLocalDiffeomorphOn (𝓡 3) PlaneCircleModel ∞ (D.mirrorMap.{u} c) (D.descentDomain c hθ) := by
  rintro ⟨p, hp⟩
  change IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞ (D.mirrorMap.{u} c) p
  replace hp : (logPoint p : ℂ) ∈ D.descentBase c hθ := hp
  rcases lt_trichotomy (p 0) 0 with h | h | h
  · have hev : D.mirrorMap.{u} c =ᶠ[𝓝 p] conjMap ∘ D.totalMap c ∘ flipMap := by
      have ho : IsOpen {p' : ModelCoordinates | p' 0 < 0} :=
        isOpen_lt (coord 0).continuous continuous_const
      exact Filter.eventually_of_mem (ho.mem_nhds h) fun p' hp' => ite_eq_left hp'
    have hz : (logPoint (flipMap p) : ℂ) ∈ D.patches c hθ := by
      rw [coe_logPoint_flipMap]
      refine D.refl_mem_patches_of_mem_descentBase c hθ hp ?_
      rw [logPoint_re_eq]
      exact h.le
    have hre : 0 ≤ (logPoint (flipMap p) : ℂ).re := by
      rw [logPoint_re_eq, flipMap_zero]
      linarith
    have h1 : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ flipMap p := by
      have := (foldFlip 0).isLocalDiffeomorph p
      refine DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq
        (Eventually.of_forall fun p' => ?_) this
      exact (foldFlip_zero_apply p').symm
    have h2 := D.isLocalDiffeomorphAt_totalMap c hθ hσ hz hre
    have h3 := (conjDiffeo.{u}).isLocalDiffeomorph (D.totalMap c (flipMap p))
    exact DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq hev
      (h1.comp _ _ (h2.comp _ _ h3))
  · have hz : (logPoint p : ℂ) ∈ D.patches c hθ :=
      D.mem_patches_of_mem_descentBase c hθ hp (by rw [logPoint_re_eq, h])
    have hz0 : (logPoint p : ℂ) ∈ D.patchZero :=
      D.mem_patchZero_of_re_nonpos c hθ hz (by rw [logPoint_re_eq, h])
    have hev : D.mirrorMap.{u} c =ᶠ[𝓝 p] D.totalMap c :=
      Filter.eventually_of_mem ((isOpen_logPoint_preimage D.isOpen_patchZero).mem_nhds hz0)
        fun p' hp' => D.mirrorMap_eq_totalMap_of_mem_patchZero c hp'
    exact DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq hev
      (D.isLocalDiffeomorphAt_totalMap c hθ hσ hz (by rw [logPoint_re_eq, h]))
  · have hev : D.mirrorMap.{u} c =ᶠ[𝓝 p] D.totalMap c := by
      have ho : IsOpen {p' : ModelCoordinates | 0 < p' 0} :=
        isOpen_lt continuous_const (coord 0).continuous
      exact Filter.eventually_of_mem (ho.mem_nhds h) fun p' hp' => ite_eq_right (not_lt.2 hp'.le)
    have hz : (logPoint p : ℂ) ∈ D.patches c hθ :=
      D.mem_patches_of_mem_descentBase c hθ hp (by rw [logPoint_re_eq]; exact h.le)
    exact DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq hev
      (D.isLocalDiffeomorphAt_totalMap c hθ hσ hz (by rw [logPoint_re_eq]; exact h.le))

theorem conePoint_totalMap_mem (hσ : σ.θ₂ = 0) {p : ModelCoordinates}
    (hz : (logPoint p : ℂ) ∈ D.patches c hθ) (hre : 0 ≤ (logPoint p : ℂ).re) :
    c.conePoint (D.totalMap.{u} c p) ∈ filledBase := by
  by_cases hd : (logPoint p : ℂ) ∈ D.patchDisc c hθ
  · rw [D.totalMap_eq_tubeMap_of_mem_patchDisc c hθ hd, conePoint_tubeMap]
    apply mem_filledBase_of_norm_sub_lt
    rw [coneApexOne, add_sub_cancel_left, norm_div, norm_pow, Complex.norm_ofNat]
    have h1 : ‖coneDisc σ.vertexOne (logPoint p)‖ < 1 :=
      lt_of_lt_of_le hd.2 (D.discRadius_le_one c hθ)
    have h2 : ‖coneDisc σ.vertexOne (logPoint p)‖ ^ c.p < 1 :=
      pow_lt_one₀ (norm_nonneg _) h1 (NeZero.ne c.p)
    linarith
  · obtain ⟨-, hv, hfB, hf, -⟩ := D.patches_good c hθ hσ hz hre hd
    rw [totalMap, ite_eq_right hv, D.conePoint_liftMap c hf]
    exact hfB

theorem conePoint_mirrorMap_mem (hσ : σ.θ₂ = 0) {p : ModelCoordinates}
    (hp : p ∈ D.descentDomain c hθ) : c.conePoint (D.mirrorMap.{u} c p) ∈ filledBase := by
  replace hp : (logPoint p : ℂ) ∈ D.descentBase c hθ := hp
  rw [mirrorMap]
  split_ifs with h
  · rw [conePoint_conjMap]
    apply conj_mem_filledBase
    apply D.conePoint_totalMap_mem c hθ hσ
    · rw [coe_logPoint_flipMap]
      exact D.refl_mem_patches_of_mem_descentBase c hθ hp (by rw [logPoint_re_eq]; exact h.le)
    · rw [logPoint_re_eq, flipMap_zero]
      linarith
  · have h' : 0 ≤ (logPoint p : ℂ).re := by rw [logPoint_re_eq]; exact not_lt.1 h
    exact D.conePoint_totalMap_mem c hθ hσ (D.mem_patches_of_mem_descentBase c hθ hp h') h'

theorem filledFunction_mirrorMap_neg (hσ : σ.θ₂ = 0) {p : ModelCoordinates}
    (hp : p ∈ D.descentDomain c hθ) :
    ConeFilling.filledFunction (c.conePoint (D.mirrorMap.{u} c p)) < 0 :=
  (filledFunction_neg_iff _).2 (D.conePoint_mirrorMap_mem c hθ hσ hp)

def foldMap (hσ : σ.θ₂ = 0) (y : D.descentDomain c hθ) : (descentCarrier.{u} c).pieceInterior ⊤ :=
  c.toDescentInterior (D.filledFunction_mirrorMap_neg c hθ hσ y.2)

theorem descentIncl_foldMap (hσ : σ.θ₂ = 0) (y : D.descentDomain c hθ) :
    c.descentIncl (D.foldMap.{u} c hθ hσ y) = D.mirrorMap c y :=
  rfl

theorem isLocalDiffeomorph_foldMap (hσ : σ.θ₂ = 0) :
    letI := Manifold.interiorChartedSpace (descentCarrier.{u} c).model ∞
      (M := (descentCarrier.{u} c).pieceInterior ⊤)
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (D.foldMap.{u} c hθ hσ) := by
  let _ := Manifold.interiorChartedSpace (descentCarrier.{u} c).model ∞
      (M := (descentCarrier.{u} c).pieceInterior ⊤)
  intro y
  have hloc : IsLocalDiffeomorph (𝓡 3) PlaneCircleModel ∞
      (fun y : D.descentDomain c hθ => D.mirrorMap.{u} c y) :=
    isLocalDiffeomorph_restrict_open _ (D.isLocalDiffeomorphOn_mirrorMap.{u} c hθ hσ)
  have hcont : Continuous (D.foldMap.{u} c hθ hσ) := by
    rw [c.isInducing_descentIncl.continuous_iff]
    exact hloc.contMDiff.continuous
  exact IsLocalDiffeomorphAt.of_comp_left (c.isLocalDiffeomorph_descentIncl _) (hloc y)
    hcont.continuousAt

end ConeShape.FoldData

end GC.Seifert
