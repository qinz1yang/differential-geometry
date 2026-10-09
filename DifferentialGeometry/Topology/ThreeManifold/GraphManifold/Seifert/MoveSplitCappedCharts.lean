import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedProfile
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.CliffordCoordinates
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Product
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph

/-!
# Charts for the split tube

Lane N2c, tier 1 (charts). Local diffeomorphisms from which the split tube is assembled:
an inverse function theorem in the form "smooth with injective differential between manifolds
without boundary of the same dimension" (`isLocalDiffeomorphAt_of_injective_mfderiv`), the
fibre angles `tubeFibre e s h = exp (i e s (π/2 + arctan (h/1000)))` of the meridian discs at
level `h` (local diffeomorphisms, jointly injective in the side `s` and the level `|h| < 3`),
the hemisphere charts `capChart s` of the round sphere (`p ↦ x₁ + i x₂` on `s x₃ > 0`) and the
band chart `bandChart` (`p ↦ (x₃, (x₁ + i x₂)/|x₁ + i x₂|)` off the poles), both partial
diffeomorphisms with explicit inverses.
-/

set_option autoImplicit false

noncomputable section
open Set Filter Function Metric
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Topology.Manifold
  (isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv)

namespace GC.Seifert.SplitTube

section InverseFunction

variable {E F H H' M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H'] {I : ModelWithCorners ℝ E H}
  {J : ModelWithCorners ℝ F H'} [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

theorem isLocalDiffeomorphAt_of_injective_mfderiv {f : M → N} {U : Set M}
    (hf : ContMDiffOn I J ∞ f U) (hU : IsOpen U) {x : M} (hx : x ∈ U)
    (hrank : Module.finrank ℝ E = Module.finrank ℝ F)
    (hinj : Injective (mfderiv I J f x)) : IsLocalDiffeomorphAt I J ∞ f x := by
  have hd : MDifferentiableAt I J f x :=
    (hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  let D : E →L[ℝ] F := mfderiv I J f x
  have hD : Injective D := hinj
  let A : E ≃L[ℝ] F :=
    (LinearMap.linearEquivOfInjective (D : E →ₗ[ℝ] F) hD hrank).toContinuousLinearEquiv
  refine isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv
    f hf hU x hx A ?_
  have hA : (A : E →L[ℝ] F) = D := by
    ext v
    rfl
  rw [hA]
  exact hd.hasMFDerivAt

end InverseFunction

theorem injective_mfderiv_of_comp {E F G H H' H'' M N P : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'} {K : ModelWithCorners ℝ G H''}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
    [TopologicalSpace P] [ChartedSpace H'' P] {f : M → N} {g : N → P} {x : M}
    (hg : MDifferentiableAt J K g (f x)) (hf : MDifferentiableAt I J f x)
    (h : Injective (mfderiv I K (g ∘ f) x)) : Injective (mfderiv I J f x) := by
  rw [mfderiv_comp x hg hf] at h
  exact Injective.of_comp h

def tubeFibre (e : ℤ) (s : Bool) (h : ℝ) : Circle :=
  Circle.exp (e * (if s then 1 else -1) * hostTheta h)

theorem hasDerivAt_hostTheta (h : ℝ) :
    HasDerivAt hostTheta (tubeSlope / (1 + (tubeSlope * h) ^ 2)) h := by
  have h1 := (Real.hasDerivAt_arctan (tubeSlope * h)).comp h
    ((hasDerivAt_id h).const_mul tubeSlope)
  have h2 : HasDerivAt hostTheta (1 / (1 + (tubeSlope * h) ^ 2) * (tubeSlope * 1)) h :=
    h1.const_add (Real.pi / 2)
  convert h2 using 1
  field_simp

theorem contDiff_hostTheta : ContDiff ℝ ∞ hostTheta :=
  contDiff_const.add (Real.contDiff_arctan.comp (contDiff_const.mul contDiff_id))

theorem contMDiff_tubeFibre (e : ℤ) (s : Bool) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ (tubeFibre e s) :=
  contMDiff_circleExp.comp ((contDiff_const.mul contDiff_hostTheta).contMDiff)

theorem coe_tubeFibre (e : ℤ) (s : Bool) (h : ℝ) :
    (tubeFibre e s h : ℂ) =
      Complex.exp (((e * (if s then 1 else -1) * hostTheta h : ℝ) : ℂ) * Complex.I) :=
  Circle.coe_exp _

theorem isLocalDiffeomorphAt_tubeFibre {e : ℤ} (he : e = 1 ∨ e = -1) (s : Bool) (h : ℝ) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡 1) ∞ (tubeFibre e s) h := by
  refine isLocalDiffeomorphAt_of_injective_mfderiv (contMDiff_tubeFibre e s).contMDiffOn
    isOpen_univ (mem_univ h) (by simp) ?_
  set c : ℝ := e * (if s then 1 else -1) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    rcases he with rfl | rfl <;> split_ifs <;> norm_num
  have hphase : HasDerivAt (fun t : ℝ => c * hostTheta t)
      (c * (tubeSlope / (1 + (tubeSlope * h) ^ 2))) h :=
    (hasDerivAt_hostTheta h).const_mul c
  have hlin : HasDerivAt (fun t : ℝ => (((c * hostTheta t : ℝ)) : ℂ) * Complex.I)
      (((c * (tubeSlope / (1 + (tubeSlope * h) ^ 2)) : ℝ) : ℂ) * Complex.I) h :=
    (hphase.ofReal_comp).mul_const Complex.I
  have hexp := hlin.cexp
  have hcomp : ((fun z : Circle => (z : ℂ)) ∘ tubeFibre e s) =
      fun t : ℝ => Complex.exp ((((c * hostTheta t : ℝ)) : ℂ) * Complex.I) := by
    funext t
    exact coe_tubeFibre e s t
  apply injective_mfderiv_of_comp (g := fun z : Circle => (z : ℂ))
    (GC.GraphManifold.contMDiff_circle_coe.mdifferentiableAt (by simp))
    ((contMDiff_tubeFibre e s).mdifferentiableAt (by simp))
  rw [hcomp, mfderiv_eq_fderiv, hexp.hasFDerivAt.fderiv]
  intro v w hvw
  have hd : (Complex.exp ((((c * hostTheta h : ℝ)) : ℂ) * Complex.I) *
      ((((c * (tubeSlope / (1 + (tubeSlope * h) ^ 2))) : ℝ) : ℂ) * Complex.I)) ≠ 0 := by
    apply mul_ne_zero (Complex.exp_ne_zero _)
    apply mul_ne_zero _ Complex.I_ne_zero
    rw [Complex.ofReal_ne_zero]
    apply mul_ne_zero hc0
    apply div_ne_zero (by norm_num [tubeSlope]) (by positivity)
  exact smul_left_injective ℝ hd hvw

theorem abs_arctan_tubeSlope_lt {h : ℝ} (hh : |h| < 3) :
    |Real.arctan (tubeSlope * h)| < 3 / 1000 := by
  have hA := abs_tubeSlope_mul_lt hh
  rw [abs_lt] at hA ⊢
  constructor
  · have := Real.arctan_strictMono (show -(3 / 1000 : ℝ) < tubeSlope * h from hA.1)
    have h2 : -(3 / 1000 : ℝ) ≤ Real.arctan (-(3 / 1000)) := by
      rw [Real.arctan_neg]
      have := Real.arctan_le_self (show (0 : ℝ) ≤ 3 / 1000 by norm_num)
      linarith
    linarith
  · have := Real.arctan_strictMono (show tubeSlope * h < 3 / 1000 from hA.2)
    have h2 := Real.arctan_le_self (show (0 : ℝ) ≤ 3 / 1000 by norm_num)
    linarith

theorem tubeFibre_injOn {e : ℤ} (he : e = 1 ∨ e = -1) {s s' : Bool} {h h' : ℝ} (hh : |h| < 3)
    (hh' : |h'| < 3) (heq : tubeFibre e s h = tubeFibre e s' h') : s = s' ∧ h = h' := by
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp heq
  have ha := abs_lt.mp (abs_arctan_tubeSlope_lt hh)
  have ha' := abs_lt.mp (abs_arctan_tubeSlope_lt hh')
  have hpi := Real.pi_gt_three
  simp only [hostTheta] at hm
  have hmb : (m : ℝ) * (2 * Real.pi) = 0 ∨ (m : ℝ) * (2 * Real.pi) ≤ -(2 * Real.pi) ∨
      2 * Real.pi ≤ (m : ℝ) * (2 * Real.pi) := by
    rcases lt_trichotomy m 0 with h0 | h0 | h0
    · right; left
      have : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt h0
      nlinarith
    · left; simp [h0]
    · right; right
      have : (1 : ℝ) ≤ m := by exact_mod_cast h0
      nlinarith
  have key : ∀ {c c' : ℝ}, (c = 1 ∨ c = -1) → (c' = 1 ∨ c' = -1) →
      c * (Real.pi / 2 + Real.arctan (tubeSlope * h)) =
        c' * (Real.pi / 2 + Real.arctan (tubeSlope * h')) + m * (2 * Real.pi) →
      c = c' ∧ Real.arctan (tubeSlope * h) = Real.arctan (tubeSlope * h') := by
    intro c c' hc hc' hcm
    rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl <;>
      rcases hmb with hm0 | hm0 | hm0 <;>
      first
        | exact ⟨rfl, by linarith⟩
        | (exfalso; linarith)
  have hcases : ∀ t : Bool, ((e : ℝ) * (if t then 1 else -1) = 1 ∨
      (e : ℝ) * (if t then 1 else -1) = -1) := by
    intro t
    rcases he with rfl | rfl <;> cases t <;> norm_num
  obtain ⟨hcc, harc⟩ := key (hcases s) (hcases s') hm
  refine ⟨?_, ?_⟩
  · have he0 : (e : ℝ) ≠ 0 := by rcases he with rfl | rfl <;> norm_num
    have := mul_left_cancel₀ he0 hcc
    cases s <;> cases s' <;> first | rfl | (norm_num at this)
  · have := Real.arctan_injective harc
    have h0 : tubeSlope ≠ 0 := by norm_num [tubeSlope]
    exact mul_left_cancel₀ h0 this

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

def sgnR (s : Bool) : ℝ := if s then 1 else -1

theorem sgnR_mul_self (s : Bool) : sgnR s * sgnR s = 1 := by
  cases s <;> norm_num [sgnR]

theorem sgnR_eq (s : Bool) : sgnR s = 1 ∨ sgnR s = -1 := by
  cases s <;> simp [sgnR]

def splitCoords : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] ℂ × ℝ :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => (⟨x 0, x 1⟩, x 2)
      invFun := fun z => !₂[z.1.re, z.1.im, z.2]
      map_add' := fun x y => by
        refine Prod.ext (Complex.ext ?_ ?_) ?_ <;> simp
      map_smul' := fun c x => by
        refine Prod.ext (Complex.ext ?_ ?_) ?_ <;> simp
      left_inv := fun x => by ext i; fin_cases i <;> simp
      right_inv := fun z => by ext <;> simp }

theorem splitCoords_apply (x : EuclideanSpace ℝ (Fin 3)) :
    splitCoords x = (⟨x 0, x 1⟩, x 2) := rfl

theorem norm_sq_eq_splitCoords (x : EuclideanSpace ℝ (Fin 3)) :
    ‖x‖ ^ 2 = ‖(splitCoords x).1‖ ^ 2 + (splitCoords x).2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Complex.sq_norm, Complex.normSq_apply]
  simp only [splitCoords_apply, Real.norm_eq_abs, sq_abs]
  ring

theorem norm_sq_splitCoords_symm (z : ℂ × ℝ) :
    ‖splitCoords.symm z‖ ^ 2 = ‖z.1‖ ^ 2 + z.2 ^ 2 := by
  rw [norm_sq_eq_splitCoords, ContinuousLinearEquiv.apply_symm_apply]

def planeOf (p : S2) : ℂ := (splitCoords (p : E3)).1

def heightOf (p : S2) : ℝ := (splitCoords (p : E3)).2

theorem planeOf_sq_add (p : S2) : ‖planeOf p‖ ^ 2 + heightOf p ^ 2 = 1 := by
  have h := norm_sq_eq_splitCoords (p : E3)
  rw [norm_eq_of_mem_sphere p, one_pow] at h
  exact h.symm

theorem abs_heightOf_le (p : S2) : |heightOf p| ≤ 1 := by
  have h := planeOf_sq_add p
  rw [← sq_abs (heightOf p)] at h
  nlinarith [sq_nonneg ‖planeOf p‖, abs_nonneg (heightOf p)]

theorem norm_planeOf (p : S2) : ‖planeOf p‖ = latRadius (heightOf p) := by
  rw [latRadius, ← planeOf_sq_add p, add_sub_cancel_right, Real.sqrt_sq (norm_nonneg _)]

theorem eq_of_planeOf_heightOf {p q : S2} (h1 : planeOf p = planeOf q)
    (h2 : heightOf p = heightOf q) : p = q := by
  apply Subtype.ext
  apply splitCoords.injective
  exact Prod.ext h1 h2

theorem contMDiff_planeOf : ContMDiff (𝓡 2) 𝓘(ℝ, ℂ) ∞ planeOf :=
  ((ContinuousLinearMap.fst ℝ ℂ ℝ).comp
    (splitCoords : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℂ × ℝ)).contDiff.contMDiff.comp
    contMDiff_coe_sphere

theorem contMDiff_heightOf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ heightOf :=
  ((ContinuousLinearMap.snd ℝ ℂ ℝ).comp
    (splitCoords : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℂ × ℝ)).contDiff.contMDiff.comp
    contMDiff_coe_sphere

def northPole : S2 := ⟨splitCoords.symm (0, 1), by
  rw [mem_sphere_zero_iff_norm, ← sq_eq_sq₀ (norm_nonneg _) zero_le_one,
    norm_sq_splitCoords_symm]
  simp⟩

def capPoint (s : Bool) (z : ℂ) : S2 :=
  if hz : ‖z‖ < 1 then ⟨splitCoords.symm (z, sgnR s * Real.sqrt (1 - ‖z‖ ^ 2)), by
    rw [mem_sphere_zero_iff_norm, ← sq_eq_sq₀ (norm_nonneg _) zero_le_one,
      norm_sq_splitCoords_symm, mul_pow, Real.sq_sqrt (by nlinarith [norm_nonneg z]), one_pow]
    have := sgnR_mul_self s
    nlinarith⟩
  else northPole

theorem coe_capPoint (s : Bool) {z : ℂ} (hz : ‖z‖ < 1) :
    (capPoint s z : E3) = splitCoords.symm (z, sgnR s * Real.sqrt (1 - ‖z‖ ^ 2)) := by
  rw [capPoint, dite_eq_left hz]

theorem planeOf_capPoint (s : Bool) {z : ℂ} (hz : ‖z‖ < 1) : planeOf (capPoint s z) = z := by
  rw [planeOf, coe_capPoint s hz, ContinuousLinearEquiv.apply_symm_apply]

theorem heightOf_capPoint (s : Bool) {z : ℂ} (hz : ‖z‖ < 1) :
    heightOf (capPoint s z) = sgnR s * Real.sqrt (1 - ‖z‖ ^ 2) := by
  rw [heightOf, coe_capPoint s hz, ContinuousLinearEquiv.apply_symm_apply]

def capChart (s : Bool) : PartialDiffeomorph (𝓡 2) 𝓘(ℝ, ℂ) S2 ℂ ∞ where
  toFun := planeOf
  invFun := capPoint s
  source := {p | 0 < sgnR s * heightOf p}
  target := ball 0 1
  map_source' := by
    intro p hp
    have hp' : 0 < sgnR s * heightOf p := hp
    rw [mem_ball_zero_iff]
    have h := planeOf_sq_add p
    have hh : 0 < heightOf p ^ 2 := by
      have : heightOf p ≠ 0 := fun h0 => by rw [h0, mul_zero] at hp'; exact lt_irrefl 0 hp'
      positivity
    nlinarith [norm_nonneg (planeOf p)]
  map_target' := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    change 0 < sgnR s * heightOf (capPoint s z)
    rw [heightOf_capPoint s hz, ← mul_assoc, sgnR_mul_self, one_mul]
    apply Real.sqrt_pos.mpr
    nlinarith [norm_nonneg z]
  left_inv' := by
    intro p hp
    have hp' : 0 < sgnR s * heightOf p := hp
    have hz : ‖planeOf p‖ < 1 := by
      have h := planeOf_sq_add p
      have hh : 0 < heightOf p ^ 2 := by
        have : heightOf p ≠ 0 := fun h0 => by rw [h0, mul_zero] at hp'; exact lt_irrefl 0 hp'
        positivity
      nlinarith [norm_nonneg (planeOf p)]
    apply eq_of_planeOf_heightOf (planeOf_capPoint s hz)
    rw [heightOf_capPoint s hz, ← planeOf_sq_add p, add_sub_cancel_left,
      Real.sqrt_sq_eq_abs]
    rcases sgnR_eq s with h1 | h1 <;> rw [h1] at hp' ⊢
    · rw [one_mul, abs_of_pos (by linarith)]
    · rw [abs_of_neg (by linarith)]
      ring
  right_inv' := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    exact planeOf_capPoint s hz
  open_source := isOpen_lt continuous_const (continuous_const.mul contMDiff_heightOf.continuous)
  open_target := isOpen_ball
  contMDiffOn_toFun := contMDiff_planeOf.contMDiffOn
  contMDiffOn_invFun := by
    refine GC.GraphManifold.contMDiffOn_sphere_of_val (k := 2) isOpen_ball ?_
    intro z hz
    have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hpos : (1 : ℝ) - ‖z‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg z]
    have hsmooth : ContDiffAt ℝ ∞
        (fun w : ℂ => splitCoords.symm (w, sgnR s * Real.sqrt (1 - ‖w‖ ^ 2))) z :=
      (splitCoords.symm : ℂ × ℝ →L[ℝ] EuclideanSpace ℝ (Fin 3)).contDiff.contDiffAt.comp
        z (contDiffAt_id.prodMk (contDiffAt_const.mul
          ((contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt).sqrt hpos)))
    exact hsmooth.contMDiffAt.contMDiffWithinAt.congr
      (fun w hw => coe_capPoint s (mem_ball_zero_iff.mp hw)) (coe_capPoint s hz')

def bandPoint (q : ℝ × Circle) : S2 :=
  if hq : |q.1| < 1 then ⟨splitCoords.symm (latRadius q.1 • (q.2 : ℂ), q.1), by
    rw [mem_sphere_zero_iff_norm, ← sq_eq_sq₀ (norm_nonneg _) zero_le_one,
      norm_sq_splitCoords_symm, norm_smul, Circle.norm_coe, mul_one, Real.norm_eq_abs, sq_abs,
      latRadius_sq hq.le]
    ring⟩
  else northPole

theorem coe_bandPoint {q : ℝ × Circle} (hq : |q.1| < 1) :
    (bandPoint q : E3) = splitCoords.symm (latRadius q.1 • (q.2 : ℂ), q.1) := by
  rw [bandPoint, dite_eq_left hq]

theorem heightOf_bandPoint {q : ℝ × Circle} (hq : |q.1| < 1) : heightOf (bandPoint q) = q.1 := by
  rw [heightOf, coe_bandPoint hq, ContinuousLinearEquiv.apply_symm_apply]

theorem planeOf_bandPoint {q : ℝ × Circle} (hq : |q.1| < 1) :
    planeOf (bandPoint q) = latRadius q.1 • (q.2 : ℂ) := by
  rw [planeOf, coe_bandPoint hq, ContinuousLinearEquiv.apply_symm_apply]

theorem planeOf_ne_zero {p : S2} (hp : |heightOf p| < 1) : planeOf p ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_planeOf]
  exact (latRadius_pos hp).ne'

def bandChart : PartialDiffeomorph (𝓡 2) (𝓘(ℝ, ℝ).prod (𝓡 1)) S2 (ℝ × Circle) ∞ where
  toFun p := (heightOf p, GC.GraphManifold.unitOf (planeOf p))
  invFun := bandPoint
  source := {p | |heightOf p| < 1}
  target := {q | |q.1| < 1}
  map_source' := fun _ hp => hp
  map_target' := by
    intro q hq
    change |heightOf (bandPoint q)| < 1
    rw [heightOf_bandPoint hq]
    exact hq
  left_inv' := by
    intro p hp
    have hp' : |heightOf p| < 1 := hp
    apply eq_of_planeOf_heightOf
    · rw [planeOf_bandPoint hp']
      change latRadius (heightOf p) • (GC.GraphManifold.unitOf (planeOf p) : ℂ) = planeOf p
      rw [← norm_planeOf]
      exact GC.GraphManifold.norm_smul_unitOf _
    · exact heightOf_bandPoint hp'
  right_inv' := by
    intro q hq
    have hq' : |q.1| < 1 := hq
    refine Prod.ext (heightOf_bandPoint hq') ?_
    change GC.GraphManifold.unitOf (planeOf (bandPoint q)) = q.2
    rw [planeOf_bandPoint hq']
    exact GC.GraphManifold.unitOf_smul (latRadius_pos hq') q.2
  open_source := isOpen_lt (continuous_abs.comp contMDiff_heightOf.continuous) continuous_const
  open_target := isOpen_lt (continuous_abs.comp continuous_fst) continuous_const
  contMDiffOn_toFun := by
    refine contMDiff_heightOf.contMDiffOn.prodMk ?_
    exact GC.GraphManifold.contMDiffOn_unitOf.comp contMDiff_planeOf.contMDiffOn
      fun p hp => planeOf_ne_zero hp
  contMDiffOn_invFun := by
    have hU : IsOpen {q : ℝ × Circle | |q.1| < 1} :=
      isOpen_lt (continuous_abs.comp continuous_fst) continuous_const
    refine GC.GraphManifold.contMDiffOn_sphere_of_val (k := 2) hU ?_
    intro q hq
    have hq' : |q.1| < 1 := hq
    have hr : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × Circle => latRadius q.1) q :=
      (contDiffAt_latRadius hq').contMDiffAt.comp q contMDiffAt_fst
    have hu : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞ (fun q : ℝ × Circle => (q.2 : ℂ)) q :=
      GC.GraphManifold.contMDiff_circle_coe.contMDiffAt.comp q contMDiffAt_snd
    have hpair : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, ℂ × ℝ) ∞
        (fun q : ℝ × Circle => (latRadius q.1 • (q.2 : ℂ), q.1)) q :=
      (hr.smul hu).prodMk_space contMDiffAt_fst
    have hsm := ((splitCoords.symm : ℂ × ℝ →L[ℝ] EuclideanSpace ℝ (Fin 3)).contDiff.contMDiff
      _).comp q hpair
    exact hsm.contMDiffWithinAt.congr (fun q' hq' => coe_bandPoint hq') (coe_bandPoint hq')

end GC.Seifert.SplitTube
