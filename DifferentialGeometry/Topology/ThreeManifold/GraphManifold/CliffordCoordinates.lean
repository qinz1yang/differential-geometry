import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.RegularSublevelAtlas
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.TorusGluing
import DifferentialGeometry.Topology.ThreeManifold.StandardSphere

/-!
# Clifford coordinates on the standard three-sphere

We write points of the standard three-sphere as pairs `(z₁, z₂)` of complex numbers with
`‖z₁‖² + ‖z₂‖² = 1`, record the smoothness of these coordinates, the coordinate swap
diffeomorphism, the height function `‖z₁‖² - ‖z₂‖²` and the signed collar of the Clifford torus
`‖z₁‖ = ‖z₂‖`.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold
universe u

theorem contMDiffOn_sphere_of_val {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k : ℕ} [Fact (Module.finrank ℝ E = k + 1)] {F G X : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [TopologicalSpace X]
    [ChartedSpace G X] [IsManifold J ∞ X] {g : X → sphere (0 : E) 1} {s : Set X}
    (hs : IsOpen s) (hg : ContMDiffOn J 𝓘(ℝ, E) ∞ (fun x => (g x : E)) s) :
    ContMDiffOn J (𝓡 k) ∞ g s := by
  intro x hx
  let U : TopologicalSpace.Opens X := ⟨s, hs⟩
  have h₁ : ContMDiff J 𝓘(ℝ, E) ∞ (fun y : U => (g y : E)) := fun y =>
    contMDiffAt_subtype_iff.mpr (hg.contMDiffAt (hs.mem_nhds y.2))
  have h₂ := ContMDiff.codRestrict_sphere (n := k) h₁ (fun y => (g y).2)
  have h₃ : ContMDiffAt J (𝓡 k) ∞ (fun y : U => g y) ⟨x, hx⟩ := h₂ ⟨x, hx⟩
  exact (contMDiffAt_subtype_iff.mp h₃).contMDiffWithinAt

theorem contMDiffOn_smul_of_real {F G X V : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [TopologicalSpace X] [ChartedSpace G X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {r : X → ℝ} {v : X → V} {s : Set X}
    (hr : ContMDiffOn J 𝓘(ℝ, ℝ) ∞ r s) (hv : ContMDiffOn J 𝓘(ℝ, V) ∞ v s) :
    ContMDiffOn J 𝓘(ℝ, V) ∞ (fun x => r x • v x) s :=
  (contDiff_smul (𝕜 := ℝ) (F := V)).contMDiff.comp_contMDiffOn (hr.prodMk_space hv)

def pairCoordinates : EuclideanSpace ℝ (Fin 4) ≃L[ℝ] ℂ × ℂ :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => (⟨x 0, x 1⟩, ⟨x 2, x 3⟩)
      invFun := fun z => !₂[z.1.re, z.1.im, z.2.re, z.2.im]
      map_add' := fun x y => by
        refine Prod.ext (Complex.ext ?_ ?_) (Complex.ext ?_ ?_) <;> simp
      map_smul' := fun c x => by
        refine Prod.ext (Complex.ext ?_ ?_) (Complex.ext ?_ ?_) <;> simp
      left_inv := fun x => by ext i; fin_cases i <;> simp
      right_inv := fun z => by ext <;> simp }

theorem pairCoordinates_apply (x : EuclideanSpace ℝ (Fin 4)) :
    pairCoordinates x = (⟨x 0, x 1⟩, ⟨x 2, x 3⟩) := rfl

theorem norm_sq_eq_pairCoordinates (x : EuclideanSpace ℝ (Fin 4)) :
    ‖x‖ ^ 2 = ‖(pairCoordinates x).1‖ ^ 2 + ‖(pairCoordinates x).2‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_four, Complex.sq_norm, Complex.sq_norm,
    pairCoordinates_apply, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Real.norm_eq_abs, sq_abs]
  ring

abbrev SphereCarrier : Type u := standardThreeSphereLift.{u}.Carrier

def sphereDownPoint (p : SphereCarrier.{u}) : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
  standardThreeSphereLiftDiffeomorph.{u}.symm p

def sphereDown (p : SphereCarrier.{u}) : EuclideanSpace ℝ (Fin 4) := (sphereDownPoint p : _)

theorem norm_sphereDown (p : SphereCarrier.{u}) : ‖sphereDown p‖ = 1 :=
  mem_sphere_zero_iff_norm.mp (sphereDownPoint p).2

theorem sphereDown_injective : Injective sphereDown.{u} := by
  intro p q h
  apply standardThreeSphereLiftDiffeomorph.{u}.symm.injective
  exact Subtype.ext h

def sphereFirst (p : SphereCarrier.{u}) : ℂ := (pairCoordinates (sphereDown p)).1

def sphereSecond (p : SphereCarrier.{u}) : ℂ := (pairCoordinates (sphereDown p)).2

theorem norm_sphereFirst_sq_add (p : SphereCarrier.{u}) :
    ‖sphereFirst p‖ ^ 2 + ‖sphereSecond p‖ ^ 2 = 1 := by
  rw [sphereFirst, sphereSecond, ← norm_sq_eq_pairCoordinates, norm_sphereDown, one_pow]

theorem sphere_ext {p q : SphereCarrier.{u}} (h₁ : sphereFirst p = sphereFirst q)
    (h₂ : sphereSecond p = sphereSecond q) : p = q := by
  apply sphereDown_injective
  apply pairCoordinates.injective
  exact Prod.ext h₁ h₂

theorem pairCoordinates_symm_mem_sphere {z w : ℂ} (h : ‖z‖ ^ 2 + ‖w‖ ^ 2 = 1) :
    pairCoordinates.symm (z, w) ∈ sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have hsq : ‖pairCoordinates.symm (z, w)‖ ^ 2 = 1 := by
    rw [norm_sq_eq_pairCoordinates, ContinuousLinearEquiv.apply_symm_apply]
    exact h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hsq

def sphereOfPair (z w : ℂ) (h : ‖z‖ ^ 2 + ‖w‖ ^ 2 = 1) : SphereCarrier.{u} :=
  standardThreeSphereLiftDiffeomorph.{u}
    (⟨pairCoordinates.symm (z, w), pairCoordinates_symm_mem_sphere h⟩ :
      sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)

theorem sphereDown_sphereOfPair (z w : ℂ) (h : ‖z‖ ^ 2 + ‖w‖ ^ 2 = 1) :
    sphereDown (sphereOfPair.{u} z w h) = pairCoordinates.symm (z, w) := by
  have h' := standardThreeSphereLiftDiffeomorph.{u}.symm_apply_apply
    (⟨pairCoordinates.symm (z, w), pairCoordinates_symm_mem_sphere h⟩ :
      sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
  exact congrArg Subtype.val h'

@[simp] theorem sphereFirst_sphereOfPair (z w : ℂ) (h : ‖z‖ ^ 2 + ‖w‖ ^ 2 = 1) :
    sphereFirst (sphereOfPair.{u} z w h) = z := by
  rw [sphereFirst, sphereDown_sphereOfPair, ContinuousLinearEquiv.apply_symm_apply]

@[simp] theorem sphereSecond_sphereOfPair (z w : ℂ) (h : ‖z‖ ^ 2 + ‖w‖ ^ 2 = 1) :
    sphereSecond (sphereOfPair.{u} z w h) = w := by
  rw [sphereSecond, sphereDown_sphereOfPair, ContinuousLinearEquiv.apply_symm_apply]

theorem fact_finrank_euclideanSpace_four :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

attribute [local instance] fact_finrank_euclideanSpace_four finrank_real_complex_fact'

theorem contMDiff_sphereDown : ContMDiff (𝓡 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) ∞ sphereDown.{u} :=
  contMDiff_coe_sphere.comp (standardThreeSphereLiftDiffeomorph.{u}.symm.contMDiff :
    ContMDiff (𝓡 3) (𝓡 3) ∞ sphereDownPoint.{u})

theorem contMDiff_sphereFirst : ContMDiff (𝓡 3) 𝓘(ℝ, ℂ) ∞ sphereFirst.{u} :=
  ((ContinuousLinearMap.fst ℝ ℂ ℂ).comp
    (pairCoordinates : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℂ × ℂ)).contDiff.contMDiff.comp
    contMDiff_sphereDown

theorem contMDiff_sphereSecond : ContMDiff (𝓡 3) 𝓘(ℝ, ℂ) ∞ sphereSecond.{u} :=
  ((ContinuousLinearMap.snd ℝ ℂ ℂ).comp
    (pairCoordinates : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℂ × ℂ)).contDiff.contMDiff.comp
    contMDiff_sphereDown

theorem contMDiffOn_of_sphereFirst_sphereSecond {F G X : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [TopologicalSpace X]
    [ChartedSpace G X] [IsManifold J ∞ X] {g : X → SphereCarrier.{u}} {s : Set X}
    (hs : IsOpen s) (h₁ : ContMDiffOn J 𝓘(ℝ, ℂ) ∞ (fun x => sphereFirst (g x)) s)
    (h₂ : ContMDiffOn J 𝓘(ℝ, ℂ) ∞ (fun x => sphereSecond (g x)) s) :
    ContMDiffOn J (𝓡 3) ∞ g s := by
  have hval : ContMDiffOn J 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) ∞
      (fun x => (sphereDownPoint (g x) : EuclideanSpace ℝ (Fin 4))) s := by
    have heq : (fun x => (sphereDownPoint (g x) : EuclideanSpace ℝ (Fin 4))) =
        fun x => pairCoordinates.symm (sphereFirst (g x), sphereSecond (g x)) := by
      funext x
      exact (pairCoordinates.symm_apply_apply (sphereDown (g x))).symm
    rw [heq]
    exact pairCoordinates.symm.contDiff.contMDiff.comp_contMDiffOn (h₁.prodMk_space h₂)
  have hs' := contMDiffOn_sphere_of_val (k := 3) hs hval
  have hc := standardThreeSphereLiftDiffeomorph.{u}.contMDiff.comp_contMDiffOn hs'
  simpa only [Function.comp_def, sphereDownPoint, Diffeomorph.apply_symm_apply] using hc

def unitOfNe (z : ℂ) (hz : z ≠ 0) : Circle :=
  ⟨(‖z‖⁻¹ : ℝ) • z, by
    rw [Submonoid.unitSphere, Submonoid.mem_mk, Subsemigroup.mem_mk, mem_sphere_zero_iff_norm,
      norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)⟩

def unitOf (z : ℂ) : Circle := if hz : z = 0 then 1 else unitOfNe z hz

theorem coe_unitOf {z : ℂ} (hz : z ≠ 0) : (unitOf z : ℂ) = (‖z‖⁻¹ : ℝ) • z := by
  simp only [unitOf, hz, ↓reduceDIte]
  rfl

theorem norm_smul_unitOf (z : ℂ) : (‖z‖ : ℝ) • (unitOf z : ℂ) = z := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [coe_unitOf hz, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]

theorem unitOf_smul {r : ℝ} (hr : 0 < r) (v : Circle) : unitOf (r • (v : ℂ)) = v := by
  have hne : r • (v : ℂ) ≠ 0 := smul_ne_zero hr.ne' (Circle.coe_ne_zero v)
  apply Circle.ext
  rw [coe_unitOf hne, norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg hr.le, smul_smul,
    inv_mul_cancel₀ hr.ne', one_smul]

theorem contMDiff_circle_coe : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun v : Circle => (v : ℂ)) :=
  contMDiff_coe_sphere

theorem contMDiffOn_unitOf : ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 1) ∞ unitOf {z | z ≠ 0} := by
  have hopen : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne
  have hval : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun z => (unitOf z : ℂ)) {z | z ≠ 0} := by
    intro z hz
    have hd : ContDiffAt ℝ ∞ (fun w : ℂ => (‖w‖⁻¹ : ℝ) • w) z :=
      ((contDiffAt_norm ℝ hz).inv (norm_ne_zero_iff.mpr hz)).smul contDiffAt_id
    apply (hd.contMDiffAt.contMDiffWithinAt).congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with w hw
      exact coe_unitOf hw
    · exact coe_unitOf hz
  exact contMDiffOn_sphere_of_val (E := ℂ) (k := 1) hopen hval

def cliffordHeight (p : SphereCarrier.{u}) : ℝ := ‖sphereFirst p‖ ^ 2 - ‖sphereSecond p‖ ^ 2

theorem contMDiff_cliffordHeight : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ cliffordHeight.{u} :=
  ((contDiff_norm_sq ℝ).contMDiff.comp contMDiff_sphereFirst).sub
    ((contDiff_norm_sq ℝ).contMDiff.comp contMDiff_sphereSecond)

theorem norm_sphereFirst_sq_eq (p : SphereCarrier.{u}) :
    ‖sphereFirst p‖ ^ 2 = (1 + cliffordHeight p) / 2 := by
  have h := norm_sphereFirst_sq_add p
  rw [cliffordHeight]
  linarith

theorem norm_sphereSecond_sq_eq (p : SphereCarrier.{u}) :
    ‖sphereSecond p‖ ^ 2 = (1 - cliffordHeight p) / 2 := by
  have h := norm_sphereFirst_sq_add p
  rw [cliffordHeight]
  linarith

def sphereSwapMap (p : SphereCarrier.{u}) : SphereCarrier.{u} :=
  sphereOfPair (sphereSecond p) (sphereFirst p) (by rw [add_comm]; exact norm_sphereFirst_sq_add p)

@[simp] theorem sphereFirst_sphereSwapMap (p : SphereCarrier.{u}) :
    sphereFirst (sphereSwapMap p) = sphereSecond p :=
  sphereFirst_sphereOfPair _ _ _

@[simp] theorem sphereSecond_sphereSwapMap (p : SphereCarrier.{u}) :
    sphereSecond (sphereSwapMap p) = sphereFirst p :=
  sphereSecond_sphereOfPair _ _ _

theorem contMDiff_sphereSwapMap : ContMDiff (𝓡 3) (𝓡 3) ∞ sphereSwapMap.{u} := by
  refine contMDiffOn_univ.mp (contMDiffOn_of_sphereFirst_sphereSecond isOpen_univ ?_ ?_)
  · simp only [sphereFirst_sphereSwapMap]
    exact contMDiff_sphereSecond.contMDiffOn
  · simp only [sphereSecond_sphereSwapMap]
    exact contMDiff_sphereFirst.contMDiffOn

def sphereSwap : SphereCarrier.{u} ≃ₘ⟮𝓡 3, 𝓡 3⟯ SphereCarrier.{u} where
  toFun := sphereSwapMap
  invFun := sphereSwapMap
  left_inv p := sphere_ext (by simp) (by simp)
  right_inv p := sphere_ext (by simp) (by simp)
  contMDiff_toFun := contMDiff_sphereSwapMap
  contMDiff_invFun := contMDiff_sphereSwapMap

theorem sphereSwap_apply (p : SphereCarrier.{u}) : sphereSwap p = sphereSwapMap p := rfl

@[simp] theorem sphereFirst_sphereSwap (p : SphereCarrier.{u}) :
    sphereFirst (sphereSwap p) = sphereSecond p :=
  sphereFirst_sphereSwapMap p

@[simp] theorem sphereSecond_sphereSwap (p : SphereCarrier.{u}) :
    sphereSecond (sphereSwap p) = sphereFirst p :=
  sphereSecond_sphereSwapMap p

theorem sphereSwap_sphereSwap (p : SphereCarrier.{u}) : sphereSwap (sphereSwap p) = p :=
  sphere_ext (by rw [sphereFirst_sphereSwap, sphereSecond_sphereSwap])
    (by rw [sphereSecond_sphereSwap, sphereFirst_sphereSwap])

theorem cliffordHeight_sphereSwap (p : SphereCarrier.{u}) :
    cliffordHeight (sphereSwap p) = -cliffordHeight p := by
  rw [cliffordHeight, cliffordHeight, sphereFirst_sphereSwap, sphereSecond_sphereSwap, neg_sub]

def seamClamp (s : ℝ) : ℝ := max (-1) (min 1 s)

theorem seamClamp_of_mem {s : ℝ} (h₁ : -1 ≤ s) (h₂ : s ≤ 1) : seamClamp s = s := by
  rw [seamClamp, min_eq_right h₂, max_eq_right h₁]

theorem neg_one_le_seamClamp (s : ℝ) : -1 ≤ seamClamp s := le_max_left _ _

theorem seamClamp_le_one (s : ℝ) : seamClamp s ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

def seamFirst (s : ℝ) : ℝ := √((1 + seamClamp s) / 2)

def seamSecond (s : ℝ) : ℝ := √((1 - seamClamp s) / 2)

theorem seamFirst_sq (s : ℝ) : seamFirst s ^ 2 = (1 + seamClamp s) / 2 :=
  Real.sq_sqrt (by linarith [neg_one_le_seamClamp s])

theorem seamSecond_sq (s : ℝ) : seamSecond s ^ 2 = (1 - seamClamp s) / 2 :=
  Real.sq_sqrt (by linarith [seamClamp_le_one s])

theorem seamFirst_pos {s : ℝ} (h : -1 < s) : 0 < seamFirst s := by
  apply Real.sqrt_pos.mpr
  have : -1 < seamClamp s := by
    rw [seamClamp]
    exact lt_max_iff.mpr (Or.inr (lt_min (by norm_num) h))
  linarith

theorem seamSecond_pos {s : ℝ} (h : s < 1) : 0 < seamSecond s := by
  apply Real.sqrt_pos.mpr
  have : seamClamp s < 1 := max_lt (by norm_num) (min_lt_iff.mpr (Or.inr h))
  linarith

theorem norm_seam_sq (s : ℝ) (v w : Circle) :
    ‖seamFirst s • (v : ℂ)‖ ^ 2 + ‖seamSecond s • (w : ℂ)‖ ^ 2 = 1 := by
  rw [norm_smul, norm_smul, Circle.norm_coe, Circle.norm_coe, mul_one, mul_one,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, seamFirst_sq, seamSecond_sq]
  ring

def cliffordSeamMap (p : Torus × ℝ) : SphereCarrier.{u} :=
  sphereOfPair (seamFirst p.2 • (p.1.1 : ℂ)) (seamSecond p.2 • (p.1.2 : ℂ))
    (norm_seam_sq p.2 p.1.1 p.1.2)

@[simp] theorem sphereFirst_cliffordSeamMap (p : Torus × ℝ) :
    sphereFirst (cliffordSeamMap.{u} p) = seamFirst p.2 • (p.1.1 : ℂ) :=
  sphereFirst_sphereOfPair _ _ _

@[simp] theorem sphereSecond_cliffordSeamMap (p : Torus × ℝ) :
    sphereSecond (cliffordSeamMap.{u} p) = seamSecond p.2 • (p.1.2 : ℂ) :=
  sphereSecond_sphereOfPair _ _ _

theorem cliffordHeight_cliffordSeamMap (p : Torus × ℝ) :
    cliffordHeight (cliffordSeamMap.{u} p) = seamClamp p.2 := by
  rw [cliffordHeight, sphereFirst_cliffordSeamMap, sphereSecond_cliffordSeamMap, norm_smul,
    norm_smul, Circle.norm_coe, Circle.norm_coe, mul_one, mul_one, Real.norm_eq_abs,
    Real.norm_eq_abs, sq_abs, sq_abs, seamFirst_sq, seamSecond_sq]
  ring

def cliffordSeamInv (p : SphereCarrier.{u}) : Torus × ℝ :=
  ((unitOf (sphereFirst p), unitOf (sphereSecond p)), cliffordHeight p)

def cliffordSeamTarget : Set SphereCarrier.{u} := {p | sphereFirst p ≠ 0 ∧ sphereSecond p ≠ 0}

theorem isOpen_cliffordSeamTarget : IsOpen cliffordSeamTarget.{u} :=
  (isOpen_ne_fun contMDiff_sphereFirst.continuous continuous_const).inter
    (isOpen_ne_fun contMDiff_sphereSecond.continuous continuous_const)

theorem cliffordHeight_mem_Ioo {p : SphereCarrier.{u}} (hp : p ∈ cliffordSeamTarget) :
    -1 < cliffordHeight p ∧ cliffordHeight p < 1 := by
  have h₁ : 0 < ‖sphereFirst p‖ ^ 2 := by positivity [norm_pos_iff.mpr hp.1]
  have h₂ : 0 < ‖sphereSecond p‖ ^ 2 := by positivity [norm_pos_iff.mpr hp.2]
  rw [norm_sphereFirst_sq_eq] at h₁
  rw [norm_sphereSecond_sq_eq] at h₂
  constructor <;> linarith

theorem seamFirst_cliffordHeight {p : SphereCarrier.{u}} (hp : p ∈ cliffordSeamTarget) :
    seamFirst (cliffordHeight p) = ‖sphereFirst p‖ := by
  obtain ⟨h₁, h₂⟩ := cliffordHeight_mem_Ioo hp
  rw [seamFirst, seamClamp_of_mem h₁.le h₂.le, ← norm_sphereFirst_sq_eq,
    Real.sqrt_sq (norm_nonneg _)]

theorem seamSecond_cliffordHeight {p : SphereCarrier.{u}} (hp : p ∈ cliffordSeamTarget) :
    seamSecond (cliffordHeight p) = ‖sphereSecond p‖ := by
  obtain ⟨h₁, h₂⟩ := cliffordHeight_mem_Ioo hp
  rw [seamSecond, seamClamp_of_mem h₁.le h₂.le, ← norm_sphereSecond_sq_eq,
    Real.sqrt_sq (norm_nonneg _)]

theorem contDiffOn_seamFirst : ContDiffOn ℝ ∞ seamFirst (Ioo (-1) 1) := by
  intro s hs
  have hd : ContDiffAt ℝ ∞ (fun t : ℝ => √((1 + t) / 2)) s :=
    (Real.contDiffAt_sqrt (by linarith [hs.1])).comp s
      ((contDiff_const.add contDiff_id).div_const 2).contDiffAt
  apply hd.contDiffWithinAt.congr
  · intro t ht
    rw [seamFirst, seamClamp_of_mem ht.1.le ht.2.le]
  · rw [seamFirst, seamClamp_of_mem hs.1.le hs.2.le]

theorem contDiffOn_seamSecond : ContDiffOn ℝ ∞ seamSecond (Ioo (-1) 1) := by
  intro s hs
  have hd : ContDiffAt ℝ ∞ (fun t : ℝ => √((1 - t) / 2)) s :=
    (Real.contDiffAt_sqrt (by linarith [hs.2])).comp s
      ((contDiff_const.sub contDiff_id).div_const 2).contDiffAt
  apply hd.contDiffWithinAt.congr
  · intro t ht
    rw [seamSecond, seamClamp_of_mem ht.1.le ht.2.le]
  · rw [seamSecond, seamClamp_of_mem hs.1.le hs.2.le]

theorem isOpen_signedCollarSource : IsOpen signedCollarSource :=
  (isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const)

def cliffordSeam : PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) SphereCarrier.{u} ∞ where
  toFun := cliffordSeamMap
  invFun := cliffordSeamInv
  source := signedCollarSource
  target := cliffordSeamTarget
  map_source' := by
    intro p hp
    refine ⟨?_, ?_⟩
    · rw [sphereFirst_cliffordSeamMap]
      exact smul_ne_zero (seamFirst_pos hp.1).ne' (Circle.coe_ne_zero _)
    · rw [sphereSecond_cliffordSeamMap]
      exact smul_ne_zero (seamSecond_pos hp.2).ne' (Circle.coe_ne_zero _)
  map_target' := fun p hp => cliffordHeight_mem_Ioo hp
  left_inv' := by
    intro p hp
    obtain ⟨⟨v, w⟩, s⟩ := p
    have hs : seamClamp s = s := seamClamp_of_mem hp.1.le hp.2.le
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · exact unitOf_smul (seamFirst_pos hp.1) v
    · exact unitOf_smul (seamSecond_pos hp.2) w
    · change cliffordHeight (cliffordSeamMap (((v, w), s) : Torus × ℝ)) = s
      rw [cliffordHeight_cliffordSeamMap, hs]
  right_inv' := by
    intro p hp
    apply sphere_ext
    · change seamFirst (cliffordHeight p) • (unitOf (sphereFirst p) : ℂ) = sphereFirst p
      rw [seamFirst_cliffordHeight hp, norm_smul_unitOf]
    · change seamSecond (cliffordHeight p) • (unitOf (sphereSecond p) : ℂ) = sphereSecond p
      rw [seamSecond_cliffordHeight hp, norm_smul_unitOf]
  open_source := isOpen_signedCollarSource
  open_target := isOpen_cliffordSeamTarget
  contMDiffOn_toFun := by
    have hsnd : ContMDiffOn signedCollarModel 𝓘(ℝ, ℝ) ∞ (fun p : Torus × ℝ => p.2)
        signedCollarSource := contMDiff_snd.contMDiffOn
    refine contMDiffOn_of_sphereFirst_sphereSecond isOpen_signedCollarSource ?_ ?_
    · simp only [sphereFirst_cliffordSeamMap]
      exact contMDiffOn_smul_of_real
        (contDiffOn_seamFirst.contMDiffOn.comp hsnd (fun p hp => hp))
        (contMDiff_circle_coe.comp (contMDiff_fst.comp contMDiff_fst)).contMDiffOn
    · simp only [sphereSecond_cliffordSeamMap]
      exact contMDiffOn_smul_of_real
        (contDiffOn_seamSecond.contMDiffOn.comp hsnd (fun p hp => hp))
        (contMDiff_circle_coe.comp (contMDiff_snd.comp contMDiff_fst)).contMDiffOn
  contMDiffOn_invFun := by
    refine ContMDiffOn.prodMk (ContMDiffOn.prodMk ?_ ?_) contMDiff_cliffordHeight.contMDiffOn
    · exact contMDiffOn_unitOf.comp contMDiff_sphereFirst.contMDiffOn (fun p hp => hp.1)
    · exact contMDiffOn_unitOf.comp contMDiff_sphereSecond.contMDiffOn (fun p hp => hp.2)

theorem cliffordSeam_apply (p : Torus × ℝ) : cliffordSeam.{u} p = cliffordSeamMap p := rfl

theorem cliffordSeam_source : cliffordSeam.{u}.source = signedCollarSource := rfl

theorem cliffordSeam_target : cliffordSeam.{u}.target = cliffordSeamTarget := rfl

theorem cliffordHeight_regular (p : SphereCarrier.{u}) (hp : cliffordHeight p = 0) :
    mfderiv (𝓡 3) 𝓘(ℝ, ℝ) cliffordHeight p ≠ 0 := by
  have hmem : p ∈ cliffordSeamTarget := by
    have h₁ := norm_sphereFirst_sq_eq p
    have h₂ := norm_sphereSecond_sq_eq p
    rw [hp] at h₁ h₂
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h, norm_zero] at h₁
      norm_num at h₁
    · rw [h, norm_zero] at h₂
      norm_num at h₂
  let t := cliffordSeamInv p
  have ht : t ∈ cliffordSeam.{u}.source := cliffordSeam.{u}.map_target hmem
  have hpt : cliffordSeam.{u} t = p := cliffordSeam.{u}.right_inv hmem
  intro hzero
  have heq : (cliffordHeight ∘ cliffordSeam.{u}) =ᶠ[𝓝 t] Prod.snd := by
    filter_upwards [cliffordSeam.{u}.open_source.mem_nhds ht] with q hq
    change cliffordHeight (cliffordSeamMap q) = q.2
    rw [cliffordHeight_cliffordSeamMap, seamClamp_of_mem hq.1.le hq.2.le]
  have hz : mfderiv (𝓡 3) 𝓘(ℝ, ℝ) cliffordHeight (cliffordSeam.{u} t) = 0 := by
    rw [hpt]
    exact hzero
  have hcomp := mfderiv_comp t
    (contMDiff_cliffordHeight.mdifferentiableAt (by simp) : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ)
      cliffordHeight (cliffordSeam.{u} t))
    (cliffordSeam.{u}.mdifferentiableAt (by simp) ht)
  rw [heq.mfderiv_eq, mfderiv_snd, hz, ContinuousLinearMap.zero_comp] at hcomp
  have h1 := DFunLike.congr_fun hcomp ((0 : TangentSpace torusModel t.1), (1 : ℝ))
  have h2 : (1 : ℝ) = 0 := h1
  norm_num at h2

end GC.GraphManifold
