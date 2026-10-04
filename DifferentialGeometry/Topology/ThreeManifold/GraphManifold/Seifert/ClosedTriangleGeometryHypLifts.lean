import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryHypCover
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryHypPhase
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryHypScrews
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryFlatLifts

/-!
# The model lifts of a hyperbolic closed triangle fold and their apex identities

Lane B3c (design `docs/geometrization/handoffs/20261004-design-b3c-hyperbolic-rows.md`, §3–4, with
review 33 §6.2: ONE common layer for both hyperbolic rows). A `HypDatum` collects a hyperbolic
triangle `σ`, a fold datum `D`, the twists and Bézout columns of the three cones (cone `3` at the
outer hole), a hyperbolic connection model `m` (`H² × ℝ` or `SL₂~`), a nonzero signed fibre step
`ℓ` and two local gauges `ψ₁ ψ₂` on the unit disc with the contract of review 33: the screws about
`v₁`, `v₂` act on the fibre by `t ↦ t - ℓ kⱼ + ψⱼ(new) - ψⱼ(old)` (`two_screwOne`, `two_screwTwo`),
`ψ₂ ∘ conj = -ψ₂`, `ψ₁ ∘ r₁ = -ψ₁`, and the real wall-2 period `(ψ₁ - ψ₂) + (ψ₁ - ψ₂) ∘ r₂ = ℓ e`.
With the base coordinate `hb x` (`ClosedTriangleGeometryHypScrews`) and fibre coordinate `t = x 2`:
* the base lift `liftP x = (f (hb x), e(t/ℓ) e^{-iΘ(hb x, f)})` (phase of `HypPhase`) and its mirror
  `liftM = conjPair ∘ liftP ∘ reflectMap c₀`, `c₀ = ℓ (k₁ + k₂)` (`hb ∘ reflectMap = conj ∘ hb`);
* the tube coordinates `tubeOne x = (rotOne (hb x) e(a₁ s₁), e(p₁ s₁))`, `tubeTwo`, and
  `tubeThree x = (e^{iπ/p₃} hb x e(a₃ s₃), e(p₃ s₃))`, `sⱼ = t/ℓ + βⱼ (hb x)`,
  `β₁ = -ψ₁/ℓ - (k₂ φ_{-3/2}(apexOne) - π e)/2π`, `β₂ = -ψ₂/ℓ - k₁ φ_{3/2}(apexTwo)/2π`,
  `β₃ = k₃ + e/2`.
In the good sector of each vertex the base lift is the seam model of the tube coordinates
(`liftP_eq_seamFwd_tubeOne`, `liftP_eq_seamFwd_tubeTwo`, `liftP_eq_outerFwd_tubeThree`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

namespace GC.Seifert

namespace ClosedTriangle

namespace Hyp

open TwoConeFold

theorem isLocalDiffeomorphAt_hypTubeLift {g : ℂ → ℂ} {O : Set ℂ} (hO : IsOpen O)
    (hg : ContDiffOn ℝ ∞ g O) (a : ℤ) {P : ℕ} (hP : P ≠ 0) {ℓ : ℝ} (hℓ : ℓ ≠ 0) {β : ℂ → ℝ}
    (hβ : ContDiffOn ℝ ∞ β O) {p : ModelCoordinates} (hp : planeOf p ∈ O)
    (hdg : Function.Injective (fderiv ℝ g (planeOf p))) :
    IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞
      (fun x => (g (planeOf x) * (eC (a * (x 2 / ℓ + β (planeOf x))) : ℂ),
        eC (P * (x 2 / ℓ + β (planeOf x))))) p := by
  set U : Set ModelCoordinates := planeOf ⁻¹' O with hUdef
  have hU : IsOpen U := hO.preimage contDiff_planeOf.continuous
  have hmaps : MapsTo planeOf U O := fun x hx => hx
  have hproj : ContDiff ℝ ∞ (fun x : ModelCoordinates => x 2 / ℓ) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).contDiff).div_const ℓ
  have ht : ContDiffOn ℝ ∞ (fun x : ModelCoordinates => x 2 / ℓ + β (planeOf x)) U :=
    hproj.contDiffOn.add (hβ.comp contDiff_planeOf.contDiffOn hmaps)
  have hω : ContDiffOn ℝ ∞ (fun x => g (planeOf x)) U :=
    hg.comp contDiff_planeOf.contDiffOn hmaps
  have hcoe : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun w : Circle => (w : ℂ)) := contMDiff_circle_coe
  have hGs : ContMDiffOn (𝓡 3) PlaneCircleModel ∞
      (fun x => (g (planeOf x) * (eC (a * (x 2 / ℓ + β (planeOf x))) : ℂ),
        eC (P * (x 2 / ℓ + β (planeOf x))))) U := by
    refine ContMDiffOn.prodMk ?_ ?_
    · have h2 : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℂ) ∞
          (fun x => (eC (a * (x 2 / ℓ + β (planeOf x))) : ℂ)) U :=
        hcoe.comp_contMDiffOn (contMDiff_eC.comp_contMDiffOn
          (contDiffOn_const.mul ht).contMDiffOn)
      exact chartContMDiffComplexMul.comp_contMDiffOn (hω.contMDiffOn.prodMk_space h2)
    · exact contMDiff_eC.comp_contMDiffOn (contDiffOn_const.mul ht).contMDiffOn
  have hgd : HasFDerivAt g (fderiv ℝ g (planeOf p)) (planeOf p) :=
    ((hg.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hωf : HasFDerivAt (fun x => g (planeOf x)) (fderiv ℝ g (planeOf p) ∘L planeOfL) p :=
    hgd.comp p (hasFDerivAt_planeOf p)
  have hβd : HasFDerivAt β (fderiv ℝ β (planeOf p)) (planeOf p) :=
    ((hβ.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  set Lt : ModelCoordinates →L[ℝ] ℝ :=
    ℓ⁻¹ • (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)) + fderiv ℝ β (planeOf p) ∘L planeOfL
    with hLt
  have htd : HasFDerivAt (fun x : ModelCoordinates => x 2 / ℓ + β (planeOf x)) Lt p :=
    (hasFDerivAt_div_two p).add (hβd.comp p (hasFDerivAt_planeOf p))
  obtain ⟨L₁, hL₁, hL₁v⟩ := hasFDerivAt_eC_comp (htd.const_mul (a : ℝ))
  obtain ⟨L₂, hL₂, hL₂v⟩ := hasFDerivAt_eC_comp (htd.const_mul (P : ℝ))
  have hf1 := hωf.mul hL₁
  refine isLocalDiffeomorphAt_of_plane hU hp hGs (hf1.prodMk hL₂) ?_
  rw [injective_iff_map_eq_zero]
  intro w hw
  rw [ContinuousLinearMap.prod_apply, Prod.mk_eq_zero] at hw
  obtain ⟨hw1, hw2⟩ := hw
  have h2 : L₂ w = 0 := hw2
  rw [hL₂v] at h2
  have htw0 : Lt w = 0 := by
    have hne : ((2 * Real.pi : ℝ) : ℂ) * I *
        (eC ((P : ℝ) * (p 2 / ℓ + β (planeOf p))) : ℂ) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero ?_ I_ne_zero) (Circle.coe_ne_zero _)
      exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
    have := (mul_eq_zero.mp h2).resolve_left hne
    have e : (((P : ℝ) • Lt) w) = (P : ℝ) * Lt w := rfl
    rw [e] at this
    have hPt : (P : ℝ) * Lt w = 0 := by exact_mod_cast this
    rcases mul_eq_zero.mp hPt with h | h
    · exact absurd h (by exact_mod_cast hP)
    · exact h
  have h1 : g (planeOf p) * L₁ w +
      (eC ((a : ℝ) * (p 2 / ℓ + β (planeOf p))) : ℂ) *
        fderiv ℝ g (planeOf p) (planeOfL w) = 0 := by
    have := hw1
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  rw [hL₁v] at h1
  have hzw : planeOfL w = 0 := by
    have hat : ((((a : ℝ) • Lt) w : ℝ) : ℂ) = 0 := by
      have e : (((a : ℝ) • Lt) w) = (a : ℝ) * Lt w := rfl
      rw [e, htw0, mul_zero, ofReal_zero]
    rw [hat, mul_zero, mul_zero, zero_add] at h1
    have hd0 : fderiv ℝ g (planeOf p) (planeOfL w) = 0 :=
      (mul_eq_zero.mp h1).resolve_left (Circle.coe_ne_zero _)
    exact hdg (hd0.trans (map_zero _).symm)
  have hzw' := hzw
  rw [planeOfL_apply] at hzw'
  obtain ⟨h0, h1'⟩ := planeOf_eq_zero hzw'
  have h2' : w 2 = 0 := by
    have := htw0
    rw [hLt, add_apply, ContinuousLinearMap.comp_apply, hzw, map_zero,
      add_zero] at this
    have h3 : ℓ⁻¹ * w 2 = 0 := by simpa using this
    exact (mul_eq_zero.mp h3).resolve_left (inv_ne_zero hℓ)
  exact eq_zero_of_coords h0 h1' h2'


theorem hyp_base_le {m : ConnectionModel} (hm : m = .hyperbolicProduct ∨ m = .universalSL2) :
    m.baseCurvature ≤ 0 := by
  rcases hm with rfl | rfl <;> norm_num [ConnectionModel.baseCurvature]

def pnatOf {p : ℕ} (h : 2 ≤ p) : ℕ+ := ⟨p, by omega⟩

theorem coe_pnatOf {p : ℕ} (h : 2 ≤ p) : ((pnatOf h : ℕ) : ℝ) = p := rfl

def hypApexOne (σ : CompactShape) (z : ℂ) : ℂ := 3 / 2 + σ.rotOne z ^ σ.p₁ / 2

def hypApexTwo (σ : CompactShape) (z : ℂ) : ℂ := -(3 / 2) + σ.rotTwo z ^ σ.p₂ / 2

structure HypDatum where
  σ : CompactShape
  hσ : σ.curv = .hyperbolic
  D : σ.FoldData
  q₁ : ℤ
  q₂ : ℤ
  q₃ : ℤ
  a₁ : ℤ
  a₂ : ℤ
  a₃ : ℤ
  b₁ : ℤ
  b₂ : ℤ
  b₃ : ℤ
  bez₁ : (σ.p₁ : ℤ) * b₁ - a₁ * q₁ = 1
  bez₂ : (σ.p₂ : ℤ) * b₂ - a₂ * q₂ = 1
  bez₃ : (σ.p₃ : ℤ) * b₃ - a₃ * q₃ = 1
  m : ConnectionModel
  hm : m = .hyperbolicProduct ∨ m = .universalSL2
  ℓ : ℝ
  ℓ_ne : ℓ ≠ 0
  ψ₁ : ℂ → ℝ
  ψ₂ : ℂ → ℝ
  contDiffOn_ψ₁ : ContDiffOn ℝ ∞ ψ₁ (Metric.ball 0 1)
  contDiffOn_ψ₂ : ContDiffOn ℝ ∞ ψ₂ (Metric.ball 0 1)
  two_screwOne : ∀ x : ModelCoordinates,
    screwAt m (hyp_base_le hm) (hypVertex σ.vertexOne) (pnatOf σ.two_le_p₁) q₁ ℓ x 2 =
      x 2 - ℓ * q₁ / (pnatOf σ.two_le_p₁ : ℕ) +
        ψ₁ (hb (screwAt m (hyp_base_le hm) (hypVertex σ.vertexOne) (pnatOf σ.two_le_p₁) q₁ ℓ x)) -
          ψ₁ (hb x)
  two_screwTwo : ∀ x : ModelCoordinates,
    screwAt m (hyp_base_le hm) (hypVertex σ.vertexTwo) (pnatOf σ.two_le_p₂) q₂ ℓ x 2 =
      x 2 - ℓ * q₂ / (pnatOf σ.two_le_p₂ : ℕ) +
        ψ₂ (hb (screwAt m (hyp_base_le hm) (hypVertex σ.vertexTwo) (pnatOf σ.two_le_p₂) q₂ ℓ x)) -
          ψ₂ (hb x)
  ψ₂_conj : ∀ w : ℂ, ‖w‖ < 1 → ψ₂ (conj w) = -ψ₂ w
  ψ₁_refl : ∀ w : ℂ, ‖w‖ < 1 → ψ₁ (σ.refl 1 w) = -ψ₁ w
  wallTwo : ∀ w : ℂ, ‖w‖ < 1 → (ψ₁ w - ψ₂ w) + (ψ₁ (σ.refl 2 w) - ψ₂ (σ.refl 2 w)) =
    ℓ * -((q₁ : ℝ) / σ.p₁ + (q₂ : ℝ) / σ.p₂ + (q₃ : ℝ) / σ.p₃)

namespace HypDatum

variable (K : HypDatum)

def k₁ : ℝ := (K.q₁ : ℝ) / K.σ.p₁

def k₂ : ℝ := (K.q₂ : ℝ) / K.σ.p₂

def k₃ : ℝ := (K.q₃ : ℝ) / K.σ.p₃

def phase : HypPhase := ⟨K.k₁, K.k₂, K.k₃, K.ℓ, K.ψ₁, K.ψ₂⟩

def c₀ : ℝ := K.ℓ * (K.k₁ + K.k₂)

def psiC (z : ℂ) : Circle := Circle.exp (-(K.phase.theta z (K.D.f z)))

def liftP (x : ModelCoordinates) : ℂ × Circle :=
  (K.D.f (hb x), eC (x 2 / K.ℓ) * K.psiC (hb x))

def liftM (x : ModelCoordinates) : ℂ × Circle := conjPair (K.liftP (reflectMap K.c₀ x))

def betaOne (z : ℂ) : ℝ :=
  -(K.ψ₁ z / K.ℓ) -
    (K.k₂ * phaseArg (-(3 / 2)) (hypApexOne K.σ z) - Real.pi * K.phase.e) / (2 * Real.pi)

def betaTwo (z : ℂ) : ℝ :=
  -(K.ψ₂ z / K.ℓ) - K.k₁ * phaseArg (3 / 2) (hypApexTwo K.σ z) / (2 * Real.pi)

def betaThree : ℝ := K.k₃ + K.phase.e / 2

def sOne (x : ModelCoordinates) : ℝ := x 2 / K.ℓ + K.betaOne (hb x)

def sTwo (x : ModelCoordinates) : ℝ := x 2 / K.ℓ + K.betaTwo (hb x)

def sThree (x : ModelCoordinates) : ℝ := x 2 / K.ℓ + K.betaThree

def tubeOne (x : ModelCoordinates) : ℂ × Circle :=
  (K.σ.rotOne (hb x) * (eC (K.a₁ * K.sOne x) : ℂ), eC (K.σ.p₁ * K.sOne x))

def tubeTwo (x : ModelCoordinates) : ℂ × Circle :=
  (K.σ.rotTwo (hb x) * (eC (K.a₂ * K.sTwo x) : ℂ), eC (K.σ.p₂ * K.sTwo x))

def tubeThree (x : ModelCoordinates) : ℂ × Circle :=
  ((Circle.exp (Real.pi / K.σ.p₃) : ℂ) * hb x * (eC (K.a₃ * K.sThree x) : ℂ),
    eC (K.σ.p₃ * K.sThree x))

theorem p₁_pos : 0 < K.σ.p₁ := by have := K.σ.two_le_p₁; omega

theorem p₂_pos : 0 < K.σ.p₂ := by have := K.σ.two_le_p₂; omega

theorem p₃_pos : 0 < K.σ.p₃ := by have := K.σ.two_le_p₃; omega

theorem k₁_mul : K.k₁ * K.σ.p₁ = K.q₁ := by
  rw [k₁, div_mul_cancel₀ _ (by exact_mod_cast K.p₁_pos.ne')]

theorem k₂_mul : K.k₂ * K.σ.p₂ = K.q₂ := by
  rw [k₂, div_mul_cancel₀ _ (by exact_mod_cast K.p₂_pos.ne')]

theorem k₃_mul : K.k₃ * K.σ.p₃ = K.q₃ := by
  rw [k₃, div_mul_cancel₀ _ (by exact_mod_cast K.p₃_pos.ne')]

theorem phase_e : K.phase.e = -(K.k₁ + K.k₂ + K.k₃) := rfl

@[simp] theorem phase_k₁ : K.phase.k₁ = K.k₁ := rfl

@[simp] theorem phase_k₂ : K.phase.k₂ = K.k₂ := rfl

@[simp] theorem phase_k₃ : K.phase.k₃ = K.k₃ := rfl

@[simp] theorem phase_ℓ : K.phase.ℓ = K.ℓ := rfl

@[simp] theorem phase_ψ₁ : K.phase.ψ₁ = K.ψ₁ := rfl

@[simp] theorem phase_ψ₂ : K.phase.ψ₂ = K.ψ₂ := rfl

theorem wallTwo' {w : ℂ} (hw : ‖w‖ < 1) :
    (K.phase.ψ₁ w - K.phase.ψ₂ w) + (K.phase.ψ₁ (K.σ.refl 2 w) - K.phase.ψ₂ (K.σ.refl 2 w)) =
      K.phase.ℓ * K.phase.e := K.wallTwo w hw

theorem norm_rotOne_pow_le {z : ℂ} (hd : z ∈ discOne K.D) : ‖K.σ.rotOne z‖ ^ K.σ.p₁ ≤ 1 :=
  pow_le_one₀ (norm_nonneg _) ((le_of_lt hd.2).trans (by linarith [radOne_le_half K.D]))

theorem norm_rotTwo_pow_le {z : ℂ} (hd : z ∈ discTwo K.D) : ‖K.σ.rotTwo z‖ ^ K.σ.p₂ ≤ 1 :=
  pow_le_one₀ (norm_nonneg _) ((le_of_lt hd.2).trans (by linarith [radTwo_le_half K.D]))

theorem liftP_eq_seamFwd_tubeOne {x : ModelCoordinates} (hd : hb x ∈ discOne K.D)
    (hs : K.σ.rotOne (hb x) ≠ 0 ∧ -(K.σ.θ₁ / 2) < arg (K.σ.rotOne (hb x)) ∧
      arg (K.σ.rotOne (hb x)) < 3 * K.σ.θ₁ / 2) :
    K.liftP x = seamFwd ((3 / 2 : ℝ) : ℂ) K.σ.p₁ K.σ.p₁ K.q₁ K.a₁ K.b₁ (K.tubeOne x) := by
  obtain ⟨hne, h1, h2⟩ := hs
  obtain ⟨b1, b2⟩ := FlatDatum.mul_arg_bounds (HypFold.θ₁_mul K.σ) h1 h2
  set z := hb x with hz
  set η := K.σ.rotOne z with hη
  have hap := seamFwd_apex (c := ((3 / 2 : ℝ) : ℂ)) (P := K.σ.p₁) (p := K.σ.p₁) (q := K.q₁)
    (a := K.a₁) (b := K.b₁) K.bez₁ rfl η hne (K.sOne x)
  have hfz : K.D.f z = 3 / 2 + η ^ K.σ.p₁ / 2 := (f_of_mem_discOne K.hσ hd).2
  have hθ := K.phase.theta_vertexOne (z := z) hfz hne (K.norm_rotOne_pow_le hd) b1 b2.le
  unfold tubeOne
  change _ = seamFwd ((3 / 2 : ℝ) : ℂ) K.σ.p₁ K.σ.p₁ K.q₁ K.a₁ K.b₁
    (η * (Circle.exp (2 * Real.pi * (K.a₁ * K.sOne x)) : ℂ),
      Circle.exp (2 * Real.pi * (K.σ.p₁ * K.sOne x)))
  rw [hap]
  unfold liftP
  rw [← hz]
  congr 1
  · rw [hfz]
    push_cast
    ring
  have hapex : hypApexOne K.σ z = 3 / 2 + η ^ K.σ.p₁ / 2 := rfl
  rw [psiC, hθ, hfz, FlatDatum.circle_exp_arg_zpow hne, eC, ← Circle.exp_add, ← Circle.exp_add]
  congr 1
  have hk := K.k₁_mul
  have hℓ := K.ℓ_ne
  simp only [sOne, betaOne, ← hz, hapex, phase_k₁, phase_k₂, phase_ℓ, phase_ψ₁]
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  push_cast
  field_simp
  linear_combination (-(K.ℓ * arg η)) * hk

theorem liftP_eq_seamFwd_tubeTwo {x : ModelCoordinates} (hd : hb x ∈ discTwo K.D)
    (hs : K.σ.rotTwo (hb x) ≠ 0 ∧ -(K.σ.θ₂ / 2) < arg (K.σ.rotTwo (hb x)) ∧
      arg (K.σ.rotTwo (hb x)) < 3 * K.σ.θ₂ / 2) :
    K.liftP x = seamFwd ((-(3 / 2) : ℝ) : ℂ) K.σ.p₂ K.σ.p₂ K.q₂ K.a₂ K.b₂ (K.tubeTwo x) := by
  obtain ⟨hne, h1, h2⟩ := hs
  obtain ⟨b1, b2⟩ := FlatDatum.mul_arg_bounds (HypFold.θ₂_mul K.σ) h1 h2
  set z := hb x with hz
  set η := K.σ.rotTwo z with hη
  have hap := seamFwd_apex (c := ((-(3 / 2) : ℝ) : ℂ)) (P := K.σ.p₂) (p := K.σ.p₂) (q := K.q₂)
    (a := K.a₂) (b := K.b₂) K.bez₂ rfl η hne (K.sTwo x)
  have hfz : K.D.f z = -(3 / 2) + η ^ K.σ.p₂ / 2 := (f_of_mem_discTwo K.hσ hd).2
  have hθ := K.phase.theta_vertexTwo (z := z) hfz hne (K.norm_rotTwo_pow_le hd) b1 b2.le
  unfold tubeTwo
  change _ = seamFwd ((-(3 / 2) : ℝ) : ℂ) K.σ.p₂ K.σ.p₂ K.q₂ K.a₂ K.b₂
    (η * (Circle.exp (2 * Real.pi * (K.a₂ * K.sTwo x)) : ℂ),
      Circle.exp (2 * Real.pi * (K.σ.p₂ * K.sTwo x)))
  rw [hap]
  unfold liftP
  rw [← hz]
  congr 1
  · rw [hfz]
    push_cast
    ring
  have hapex : hypApexTwo K.σ z = -(3 / 2) + η ^ K.σ.p₂ / 2 := rfl
  rw [psiC, hθ, hfz, FlatDatum.circle_exp_arg_zpow hne, eC, ← Circle.exp_add, ← Circle.exp_add]
  congr 1
  have hk := K.k₂_mul
  have hℓ := K.ℓ_ne
  simp only [sTwo, betaTwo, ← hz, hapex, phase_k₁, phase_k₂, phase_ℓ, phase_ψ₂]
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  push_cast
  field_simp
  linear_combination (-(K.ℓ * arg η)) * hk

theorem normSq_f_of_mem_discThree {z : ℂ} (hd : z ∈ discThree K.D) (h0 : z ≠ 0) :
    9 ≤ normSq (K.D.f z) := by
  have h := norm_f_of_mem_discThree hd h0
  rw [normSq_eq_norm_sq]
  nlinarith

theorem liftP_eq_outerFwd_tubeThree {x : ModelCoordinates} (hd : hb x ∈ discThree K.D)
    (hs : hb x ≠ 0 ∧ -(K.σ.θ₃ / 2) < arg (hb x) ∧ arg (hb x) < 3 * K.σ.θ₃ / 2) :
    K.liftP x = outerFwd K.σ.p₃ K.σ.p₃ K.q₃ K.a₃ K.b₃ (K.tubeThree x) := by
  obtain ⟨hne, h1, h2⟩ := hs
  obtain ⟨b1, b2⟩ := FlatDatum.mul_arg_bounds (HypFold.θ₃_mul K.σ) h1 h2
  set z := hb x with hz
  have hap := outerFwd_apex (P := K.σ.p₃) (p := K.σ.p₃) (q := K.q₃) (a := K.a₃) (b := K.b₃)
    K.bez₃ K.p₃_pos.ne' rfl z hne (K.sThree x)
  have hfz : K.D.f z = compactOuterGerm K.σ.p₃ z := (f_of_mem_discThree hd hne).2
  have hn9 := K.normSq_f_of_mem_discThree hd hne
  have hθ := K.phase.theta_outer (z := z) hn9
  have hzp : ‖z‖ ^ K.σ.p₃ < 7 := by
    have : ‖z‖ ^ K.σ.p₃ ≤ 1 := pow_le_one₀ (norm_nonneg _)
      ((le_of_lt hd).trans (by linarith [radThree_le_half K.D]))
    linarith
  have hφ := phaseArg_compactOuterGerm hne hzp b1.le b2
  unfold tubeThree
  change _ = outerFwd K.σ.p₃ K.σ.p₃ K.q₃ K.a₃ K.b₃
    ((Circle.exp (Real.pi / K.σ.p₃) : ℂ) * z *
      (Circle.exp (2 * Real.pi * (K.a₃ * K.sThree x)) : ℂ),
      Circle.exp (2 * Real.pi * (K.σ.p₃ * K.sThree x)))
  rw [hap]
  unfold liftP
  rw [← hz]
  congr 1
  rw [psiC, hθ, hfz, hφ, FlatDatum.circle_exp_arg_zpow hne, eC, ← Circle.exp_add,
    ← Circle.exp_add, ← Circle.exp_add]
  congr 1
  have hk := K.k₃_mul
  have hℓ := K.ℓ_ne
  have hp3 : (K.σ.p₃ : ℝ) ≠ 0 := by exact_mod_cast K.p₃_pos.ne'
  simp only [sThree, betaThree, phase_k₃, phase_e]
  push_cast
  field_simp
  linear_combination (-(Real.pi * K.ℓ) - K.σ.p₃ * K.ℓ * arg z) * hk

theorem hb_reflectMap (c : ℝ) (x : ModelCoordinates) : hb (reflectMap c x) = conj (hb x) := by
  rw [hb, planeOf_reflectMap, hypDisc_conj]
  rfl

theorem liftM_eq_liftP {x : ModelCoordinates} (hV : hb x ∈ K.D.V 0)
    (hre : (K.D.f (hb x)).re < -(3 / 2)) : K.liftM x = K.liftP x := by
  set z := hb x with hz
  have hz1 : ‖z‖ < 1 := norm_lt_one_of_mem_V K.hσ hV
  have hfl : K.D.f (conj z) = conj (K.D.f z) := K.D.f_refl 0 z hV
  have hθ := K.phase.theta_wallZero (z := z) (z' := conj z) hre (K.ψ₂_conj z hz1)
  unfold liftM liftP conjPair
  rw [hb_reflectMap, ← hz, hfl, Complex.conj_conj, reflectMap_two]
  congr 1
  rw [psiC, hfl, mul_inv, ← Circle.exp_neg, neg_neg, eC, eC, ← Circle.exp_neg, ← Circle.exp_add,
    psiC, ← Circle.exp_add]
  congr 1
  have hℓ := K.ℓ_ne
  simp only [c₀, phase_k₁, phase_k₂] at hθ ⊢
  field_simp
  linear_combination K.ℓ * hθ

theorem apexTwo_conj (z : ℂ) : hypApexTwo K.σ (conj z) = conj (hypApexTwo K.σ z) := by
  have hr : K.σ.rotTwo (conj z) = exp (2 * (K.σ.θ₂ : ℂ) * I) * conj (K.σ.rotTwo z) :=
    HypFold.rotTwo_refl_zero K.hσ z
  simp only [hypApexTwo, hr, mul_pow, EuclidShape.exp_pow_eq_one (HypFold.θ₂_mul K.σ), one_mul,
    map_add, map_div₀, map_pow, map_ofNat, map_neg]

theorem apexOne_refl_one (z : ℂ) :
    hypApexOne K.σ (K.σ.refl 1 z) = conj (hypApexOne K.σ z) := by
  simp only [hypApexOne, HypFold.rotOne_refl_one K.hσ, map_add, map_div₀, map_pow, map_ofNat]

theorem re_apexTwo_lt {z : ℂ} (hd : z ∈ discTwo K.D) : (hypApexTwo K.σ z).re < 3 / 2 := by
  have := re_f_of_mem_discTwo K.hσ hd
  rw [(f_of_mem_discTwo K.hσ hd).2] at this
  change (hypApexTwo K.σ z).re ≤ -1 at this
  linarith

theorem re_apexOne_gt {z : ℂ} (hd : z ∈ discOne K.D) : -(3 / 2) < (hypApexOne K.σ z).re := by
  have := re_f_of_mem_discOne K.hσ hd
  rw [(f_of_mem_discOne K.hσ hd).2] at this
  change 1 ≤ (hypApexOne K.σ z).re at this
  linarith

theorem betaTwo_conj {z : ℂ} (hd : z ∈ discTwo K.D) :
    K.betaTwo (conj z) = -K.betaTwo z - K.k₁ := by
  simp only [betaTwo, K.apexTwo_conj, phaseArg_conj_of_gt (K.re_apexTwo_lt hd),
    K.ψ₂_conj z hd.1]
  have hℓ := K.ℓ_ne
  field_simp
  ring

theorem betaOne_refl_one {z : ℂ} (hd : z ∈ discOne K.D) :
    K.betaOne (K.σ.refl 1 z) = -K.betaOne z + K.phase.e := by
  simp only [betaOne, K.apexOne_refl_one, phaseArg_conj_of_lt (K.re_apexOne_gt hd),
    K.ψ₁_refl z hd.1]
  have hℓ := K.ℓ_ne
  field_simp
  ring

theorem conjPair_tubeTwo_reflect {x : ModelCoordinates} (hd : hb x ∈ discTwo K.D) :
    conjPair (K.tubeTwo (reflectMap K.c₀ x)) = K.tubeTwo x := by
  set z := hb x with hz
  have hβ := K.betaTwo_conj hd
  have hk := K.k₂_mul
  have hℓ := K.ℓ_ne
  have hθp := FlatDatum.p_inv_eq K.p₂_pos (HypFold.θ₂_mul K.σ)
  have hsum : K.sTwo (reflectMap K.c₀ x) = -K.sTwo x + K.k₂ := by
    simp only [sTwo, hb_reflectMap, reflectMap_two, ← hz, hβ, c₀]
    field_simp
    ring
  unfold tubeTwo conjPair
  rw [hsum, hb_reflectMap, ← hz]
  apply Prod.ext
  · change conj (K.σ.rotTwo (conj z) * (eC (K.a₂ * (-K.sTwo x + K.k₂)) : ℂ)) =
      K.σ.rotTwo z * (eC (K.a₂ * K.sTwo x) : ℂ)
    have hr : K.σ.rotTwo (conj z) = exp (2 * (K.σ.θ₂ : ℂ) * I) * conj (K.σ.rotTwo z) :=
      HypFold.rotTwo_refl_zero K.hσ z
    have e1 : conj (exp (2 * (K.σ.θ₂ : ℂ) * I)) = (Circle.exp (-(2 * K.σ.θ₂)) : ℂ) := by
      rw [Circle.coe_exp, ← Complex.exp_conj]
      congr 1
      rw [map_mul, map_mul, conj_I, conj_ofReal, map_ofNat]
      push_cast
      ring
    rw [hr, map_mul, map_mul, Complex.conj_conj, e1, ← Circle.coe_inv_eq_conj, ← eC_neg]
    have key : Circle.exp (-(2 * K.σ.θ₂)) * eC (-(K.a₂ * (-K.sTwo x + K.k₂))) =
        eC (K.a₂ * K.sTwo x) := by
      rw [eC, eC, ← Circle.exp_add]
      have hb : ((K.σ.p₂ : ℝ) * K.b₂ - K.a₂ * K.q₂) = 1 := by exact_mod_cast K.bez₂
      have : -(2 * K.σ.θ₂) + 2 * Real.pi * -(K.a₂ * (-K.sTwo x + K.k₂)) =
          2 * Real.pi * (K.a₂ * K.sTwo x) + ((-K.b₂ : ℤ) : ℝ) * (2 * Real.pi) := by
        rw [hθp, k₂]
        have hp0 : (K.σ.p₂ : ℝ) ≠ 0 := by exact_mod_cast K.p₂_pos.ne'
        push_cast
        field_simp
        linear_combination hb
      rw [this, Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]
    have := congrArg (fun w : Circle => (w : ℂ) * K.σ.rotTwo z) key
    simp only [Circle.coe_mul] at this
    linear_combination this
  · change (eC (K.σ.p₂ * (-K.sTwo x + K.k₂)))⁻¹ = eC (K.σ.p₂ * K.sTwo x)
    rw [← eC_neg]
    have : -(K.σ.p₂ * (-K.sTwo x + K.k₂)) = K.σ.p₂ * K.sTwo x + ((-K.q₂ : ℤ) : ℝ) := by
      push_cast
      linear_combination -hk
    rw [this, eC_add, eC_int, mul_one]

theorem conjPair_tubeThree_reflect (x : ModelCoordinates) :
    conjPair (K.tubeThree (reflectMap K.c₀ x)) = K.tubeThree x := by
  have hk := K.k₃_mul
  have hℓ := K.ℓ_ne
  have hsum : K.sThree (reflectMap K.c₀ x) = -K.sThree x + K.k₃ := by
    simp only [sThree, betaThree, reflectMap_two, c₀, phase_e]
    field_simp
    ring
  unfold tubeThree conjPair
  rw [hsum, hb_reflectMap]
  apply Prod.ext
  · change conj ((Circle.exp (Real.pi / K.σ.p₃) : ℂ) * conj (hb x) *
      (eC (K.a₃ * (-K.sThree x + K.k₃)) : ℂ)) =
      (Circle.exp (Real.pi / K.σ.p₃) : ℂ) * hb x * (eC (K.a₃ * K.sThree x) : ℂ)
    rw [map_mul, map_mul, Complex.conj_conj, ← Circle.coe_inv_eq_conj, ← Circle.coe_inv_eq_conj,
      ← Circle.exp_neg, ← eC_neg]
    have key : Circle.exp (-(Real.pi / K.σ.p₃)) * eC (-(K.a₃ * (-K.sThree x + K.k₃))) =
        Circle.exp (Real.pi / K.σ.p₃) * eC (K.a₃ * K.sThree x) := by
      rw [eC, eC, ← Circle.exp_add, ← Circle.exp_add]
      have hb : ((K.σ.p₃ : ℝ) * K.b₃ - K.a₃ * K.q₃) = 1 := by exact_mod_cast K.bez₃
      have : -(Real.pi / K.σ.p₃) + 2 * Real.pi * -(K.a₃ * (-K.sThree x + K.k₃)) =
          (Real.pi / K.σ.p₃ + 2 * Real.pi * (K.a₃ * K.sThree x)) +
            ((-K.b₃ : ℤ) : ℝ) * (2 * Real.pi) := by
        rw [k₃]
        have hp0 : (K.σ.p₃ : ℝ) ≠ 0 := by exact_mod_cast K.p₃_pos.ne'
        push_cast
        field_simp
        linear_combination 2 * hb
      rw [this, Circle.exp_add _ (((-K.b₃ : ℤ) : ℝ) * (2 * Real.pi)), Circle.exp_int_mul_two_pi,
        mul_one]
    have := congrArg (fun w : Circle => (w : ℂ) * hb x) key
    simp only [Circle.coe_mul] at this
    linear_combination this
  · change (eC (K.σ.p₃ * (-K.sThree x + K.k₃)))⁻¹ = eC (K.σ.p₃ * K.sThree x)
    rw [← eC_neg]
    have : -(K.σ.p₃ * (-K.sThree x + K.k₃)) = K.σ.p₃ * K.sThree x + ((-K.q₃ : ℤ) : ℝ) := by
      push_cast
      linear_combination -hk
    rw [this, eC_add, eC_int, mul_one]

def rotThreeInv (x : ModelCoordinates) : ModelCoordinates :=
  ofPlane ((Circle.exp (2 * K.σ.θ₃) : ℂ) * planeOf x) (x 2 + K.ℓ * K.k₃)

theorem hb_rotThreeInv (x : ModelCoordinates) :
    hb (K.rotThreeInv x) = K.σ.refl 1 (conj (hb x)) := by
  rw [rotThreeInv, hb, planeOf_ofPlane, hypDisc_mul_circle]
  change (Circle.exp (2 * K.σ.θ₃) : ℂ) * hb x = exp (2 * (K.σ.θ₃ : ℂ) * I) * conj (conj (hb x))
  rw [Complex.conj_conj, Circle.coe_exp]
  push_cast
  ring_nf

theorem conjPair_tubeOne_reflect {x : ModelCoordinates} (hd : conj (hb x) ∈ discOne K.D) :
    conjPair (K.tubeOne (reflectMap K.c₀ x)) = K.tubeOne (K.rotThreeInv x) := by
  set w := conj (hb x) with hw
  have hβ := K.betaOne_refl_one hd
  have hℓ := K.ℓ_ne
  have hsum : K.sOne (reflectMap K.c₀ x) = -K.sOne (K.rotThreeInv x) := by
    simp only [sOne, hb_reflectMap, reflectMap_two, K.hb_rotThreeInv, ← hw, hβ, c₀, phase_e]
    simp only [rotThreeInv, ofPlane_apply_two]
    field_simp
    ring
  unfold tubeOne conjPair
  rw [hsum, hb_reflectMap, ← hw]
  apply Prod.ext
  · change conj (K.σ.rotOne w * (eC (K.a₁ * -K.sOne (K.rotThreeInv x)) : ℂ)) =
      K.σ.rotOne (hb (K.rotThreeInv x)) * (eC (K.a₁ * K.sOne (K.rotThreeInv x)) : ℂ)
    rw [map_mul, ← Circle.coe_inv_eq_conj, ← eC_neg, K.hb_rotThreeInv, ← hw,
      HypFold.rotOne_refl_one K.hσ]
    congr 3
    ring
  · change (eC (K.σ.p₁ * -K.sOne (K.rotThreeInv x)))⁻¹ = eC (K.σ.p₁ * K.sOne (K.rotThreeInv x))
    rw [← eC_neg]
    congr 1
    ring

section Smooth

omit K in
theorem mainSet_ne_vertex {σ : CompactShape} (hσ : σ.curv = .hyperbolic) {D : σ.FoldData} {z : ℂ}
    (hm : z ∈ mainSet D) : z ≠ σ.vertexOne ∧ z ≠ σ.vertexTwo := by
  have hk := kap_pos D hσ
  rcases hm with ((h | h) | h) | h
  · exact ⟨(σ.ne_of_mem_openTriangle h).2.1, (σ.ne_of_mem_openTriangle h).2.2⟩
  · obtain ⟨-, -, h2, -⟩ := h
    constructor <;> rintro rfl
    · rw [σ.wallSide_two_vertexOne] at h2; linarith
    · rw [HypFold.wallSide_two_vertexTwo hσ] at h2; linarith
  · obtain ⟨-, h0, h2, -⟩ := h
    constructor <;> rintro rfl
    · rw [σ.wallSide_two_vertexOne] at h2; linarith
    · rw [HypFold.wallSide_zero_vertexTwo] at h0; linarith
  · obtain ⟨-, h0, h1, -⟩ := h
    constructor <;> rintro rfl
    · rw [HypFold.wallSide_one_vertexOne] at h1; linarith
    · rw [HypFold.wallSide_zero_vertexTwo] at h0; linarith

omit K in
theorem mainSet_phase {σ : CompactShape} {D : σ.FoldData} {z : ℂ}
    (hm : z ∈ mainSet D) : D.f z ∈ phaseDomain (3 / 2) ∧ D.f z ∈ phaseDomain (-(3 / 2)) ∧
      (D.f z ∈ phaseDomain 0 ∨ normSq (D.f z) < 121 / 16) := by
  rcases hm with ((h | h) | h) | h
  · have := D.im_f_pos h.1 h.2
    exact ⟨mem_phaseDomain_iff.2 (Or.inl this), mem_phaseDomain_iff.2 (Or.inl this),
      Or.inl (mem_phaseDomain_iff.2 (Or.inl this))⟩
  · have hre := h.2.2.2.2.2.1
    exact ⟨mem_phaseDomain_of_re_ne (by linarith), mem_phaseDomain_of_re_ne (by linarith),
      Or.inl (mem_phaseDomain_of_re_ne (by linarith))⟩
  · have hre := h.2.2.2.2.2.1
    exact ⟨mem_phaseDomain_of_re_ne (by linarith), mem_phaseDomain_of_re_ne (by linarith),
      Or.inl (mem_phaseDomain_of_re_ne (by linarith))⟩
  · have h1 := h.2.2.2.2.2.1
    have h2 := h.2.2.2.2.2.2.1
    have h3 := h.2.2.2.2.2.2.2.1
    exact ⟨mem_phaseDomain_of_re_ne (by linarith), mem_phaseDomain_of_re_ne (by linarith),
      Or.inr (by linarith)⟩

theorem norm_lt_one_of_mem_U {z : ℂ} (hz : z ∈ K.D.U) : ‖z‖ < 1 := by
  have := K.D.U_subset_plane hz
  rw [CompactShape.plane_hyp K.hσ, mem_ball_zero_iff] at this
  exact this

theorem contMDiffOn_psiC : ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 1) ∞ K.psiC (mainSet K.D) := by
  intro z hz
  have hU := mainSet_subset_U K.D hz
  have hb : z ∈ Metric.ball (0 : ℂ) 1 := mem_ball_zero_iff.2 (K.norm_lt_one_of_mem_U hU)
  have hf : ContDiffAt ℝ ∞ K.D.f z := K.D.contDiffOn_f.contDiffAt (K.D.isOpen_U.mem_nhds hU)
  obtain ⟨h1, h2, h3⟩ := mainSet_phase hz
  have hθ := K.phase.contDiffAt_theta (z₀ := z) h1 h2 h3
    (K.contDiffOn_ψ₁.contDiffAt (Metric.isOpen_ball.mem_nhds hb))
    (K.contDiffOn_ψ₂.contDiffAt (Metric.isOpen_ball.mem_nhds hb))
  have hc : ContDiffAt ℝ ∞ (fun w => -(K.phase.theta w (K.D.f w))) z :=
    (hθ.comp z (contDiffAt_id.prodMk hf)).neg
  exact (contMDiff_circleExp.contMDiffAt.comp z hc.contMDiffAt).contMDiffWithinAt

theorem det_fderiv_comp_hypDisc {f : ℂ → ℂ} {p : ℂ} (hf : DifferentiableAt ℝ f (hypDisc p)) :
    (fderiv ℝ (f ∘ hypDisc) p).det = (fderiv ℝ f (hypDisc p)).det * (fderiv ℝ hypDisc p).det := by
  rw [fderiv_comp p hf ((contDiff_hypDisc.differentiable (by simp)) p)]
  exact LinearMap.det_comp _ _

theorem isLocalDiffeomorphAt_liftP {x : ModelCoordinates} (hm : hb x ∈ mainSet K.D) :
    IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞ K.liftP x := by
  obtain ⟨hne1, hne2⟩ := mainSet_ne_vertex K.hσ hm
  have hU := mainSet_subset_U K.D hm
  set O := hypDisc ⁻¹' mainSet K.D with hO
  have hOo : IsOpen O := (isOpen_mainSet K.hσ).preimage contDiff_hypDisc.continuous
  have hmaps : MapsTo hypDisc O (mainSet K.D) := fun p hp => hp
  have hfO : ContDiffOn ℝ ∞ (K.D.f ∘ hypDisc) O :=
    (K.D.contDiffOn_f.mono (mainSet_subset_U K.D)).comp contDiff_hypDisc.contDiffOn hmaps
  have hΨ : ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 1) ∞ (K.psiC ∘ hypDisc) O :=
    K.contMDiffOn_psiC.comp contDiff_hypDisc.contMDiff.contMDiffOn hmaps
  have hfd : DifferentiableAt ℝ K.D.f (hypDisc (planeOf x)) :=
    (K.D.contDiffOn_f.contDiffAt (K.D.isOpen_U.mem_nhds hU)).differentiableAt (by simp)
  have hdet : (fderiv ℝ (K.D.f ∘ hypDisc) (planeOf x)).det ≠ 0 := by
    rw [det_fderiv_comp_hypDisc hfd]
    exact mul_ne_zero (K.D.det_fderiv_pos _ hU hne1 hne2).ne' (det_fderiv_hypDisc_ne_zero _)
  exact isLocalDiffeomorphAt_flatBaseLift hOo hfO hΨ K.ℓ_ne hm hdet

theorem isLocalDiffeomorphAt_liftM {x : ModelCoordinates}
    (hm : conj (hb x) ∈ mainSet K.D) :
    IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞ K.liftM x := by
  have hm' : hb (reflectDiffeo K.c₀ x) ∈ mainSet K.D := by
    rw [reflectDiffeo_apply, hb_reflectMap]; exact hm
  have h1 := IsLocalDiffeomorphAt.comp (hf := (reflectDiffeo K.c₀).isLocalDiffeomorph x)
    (hg := K.isLocalDiffeomorphAt_liftP hm')
  exact IsLocalDiffeomorphAt.comp (hf := h1) (hg := conjPairDiffeo.isLocalDiffeomorph _)

theorem injective_fderiv_of_hasDerivAt {f : ℂ → ℂ} {f' z : ℂ} (h : HasDerivAt f f' z)
    (hne : f' ≠ 0) : Function.Injective (fderiv ℝ f z) := by
  rw [(h.hasFDerivAt.restrictScalars ℝ).fderiv]
  intro u v huv
  have h' : u * f' = v * f' := by simpa using huv
  exact mul_right_cancel₀ hne h'

theorem hasDerivAt_rotOne {z : ℂ} (hz : ‖z‖ < 1) :
    ∃ d : ℂ, d ≠ 0 ∧ HasDerivAt K.σ.rotOne d z := by
  have hd := HypFold.one_sub_conj_vertexOne_mul_ne_zero K.hσ hz
  have hm := HypFold.hasDerivAt_mob hd
  have e : K.σ.rotOne = fun w => -exp (-((K.σ.θ₃ : ℂ) * I)) * HypFold.mob K.σ.vertexOne w :=
    funext (HypFold.rotOne_eq_mul_mob K.hσ)
  refine ⟨_, ?_, e ▸ hm.const_mul (-exp (-((K.σ.θ₃ : ℂ) * I)))⟩
  have hv : (1 : ℂ) - conj K.σ.vertexOne * K.σ.vertexOne ≠ 0 :=
    HypFold.one_sub_conj_mul_self_ne_zero (HypFold.normSq_vertexOne_ne_one K.hσ)
  exact mul_ne_zero (neg_ne_zero.2 (Complex.exp_ne_zero _)) (div_ne_zero hv (pow_ne_zero 2 hd))

theorem hasDerivAt_rotTwo {z : ℂ} (hz : ‖z‖ < 1) :
    ∃ d : ℂ, d ≠ 0 ∧ HasDerivAt K.σ.rotTwo d z := by
  have hd : 1 - conj K.σ.vertexTwo * z ≠ 0 := by
    rw [HypFold.conj_vertexTwo (σ := K.σ)]
    exact HypFold.one_sub_vertexTwo_mul_ne_zero K.hσ hz
  have hm := HypFold.hasDerivAt_mob hd
  have e : K.σ.rotTwo = fun w => -exp ((K.σ.θ₂ : ℂ) * I) * HypFold.mob K.σ.vertexTwo w :=
    funext (HypFold.rotTwo_eq_mul_mob K.hσ)
  refine ⟨_, ?_, e ▸ hm.const_mul (-exp ((K.σ.θ₂ : ℂ) * I))⟩
  have hv : (1 : ℂ) - conj K.σ.vertexTwo * K.σ.vertexTwo ≠ 0 :=
    HypFold.one_sub_conj_mul_self_ne_zero (HypFold.normSq_vertexTwo_ne_one K.hσ)
  exact mul_ne_zero (neg_ne_zero.2 (Complex.exp_ne_zero _)) (div_ne_zero hv (pow_ne_zero 2 hd))

theorem contDiffOn_rotOne : ContDiffOn ℝ ∞ K.σ.rotOne (Metric.ball 0 1) := by
  intro z hz
  rw [mem_ball_zero_iff] at hz
  have hm := HypFold.contDiffAt_mob (HypFold.one_sub_conj_vertexOne_mul_ne_zero K.hσ hz)
  have e : K.σ.rotOne = fun w => -exp (-((K.σ.θ₃ : ℂ) * I)) * HypFold.mob K.σ.vertexOne w :=
    funext (HypFold.rotOne_eq_mul_mob K.hσ)
  rw [e]
  exact (contDiffAt_const.mul hm).contDiffWithinAt

theorem contDiffOn_rotTwo : ContDiffOn ℝ ∞ K.σ.rotTwo (Metric.ball 0 1) := by
  intro z hz
  rw [mem_ball_zero_iff] at hz
  have hd : 1 - conj K.σ.vertexTwo * z ≠ 0 := by
    rw [HypFold.conj_vertexTwo (σ := K.σ)]
    exact HypFold.one_sub_vertexTwo_mul_ne_zero K.hσ hz
  have hm := HypFold.contDiffAt_mob hd
  have e : K.σ.rotTwo = fun w => -exp ((K.σ.θ₂ : ℂ) * I) * HypFold.mob K.σ.vertexTwo w :=
    funext (HypFold.rotTwo_eq_mul_mob K.hσ)
  rw [e]
  exact (contDiffAt_const.mul hm).contDiffWithinAt

theorem contDiffOn_betaOne : ContDiffOn ℝ ∞ K.betaOne (discOne K.D) := by
  intro z hz
  have hb : z ∈ Metric.ball (0 : ℂ) 1 := mem_ball_zero_iff.2 hz.1
  have hr : ContDiffAt ℝ ∞ K.σ.rotOne z :=
    K.contDiffOn_rotOne.contDiffAt (Metric.isOpen_ball.mem_nhds hb)
  have ha : ContDiffAt ℝ ∞ (hypApexOne K.σ) z :=
    contDiffAt_const.add ((hr.pow _).div_const _)
  have hph := contDiffAt_phaseArg (c := -(3 / 2)) (mem_phaseDomain_of_re_ne
    (ne_of_gt (K.re_apexOne_gt hz)))
  have h := hph.comp z ha
  have hψ := K.contDiffOn_ψ₁.contDiffAt (Metric.isOpen_ball.mem_nhds hb)
  exact (((hψ.div_const _).neg).sub
    (((contDiffAt_const.mul h).sub contDiffAt_const).div_const _)).contDiffWithinAt

theorem contDiffOn_betaTwo : ContDiffOn ℝ ∞ K.betaTwo (discTwo K.D) := by
  intro z hz
  have hb : z ∈ Metric.ball (0 : ℂ) 1 := mem_ball_zero_iff.2 hz.1
  have hr : ContDiffAt ℝ ∞ K.σ.rotTwo z :=
    K.contDiffOn_rotTwo.contDiffAt (Metric.isOpen_ball.mem_nhds hb)
  have ha : ContDiffAt ℝ ∞ (hypApexTwo K.σ) z :=
    contDiffAt_const.add ((hr.pow _).div_const _)
  have hph := contDiffAt_phaseArg (c := 3 / 2) (mem_phaseDomain_of_re_ne
    (ne_of_lt (K.re_apexTwo_lt hz)))
  have h := hph.comp z ha
  have hψ := K.contDiffOn_ψ₂.contDiffAt (Metric.isOpen_ball.mem_nhds hb)
  exact (((hψ.div_const _).neg).sub
    ((contDiffAt_const.mul h).div_const _)).contDiffWithinAt

theorem injective_fderiv_comp_hypDisc {g : ℂ → ℂ} {p : ℂ} {d : ℂ} (hd : d ≠ 0)
    (hg : HasDerivAt g d (hypDisc p)) : Function.Injective (fderiv ℝ (g ∘ hypDisc) p) := by
  rw [fderiv_comp p (hg.hasFDerivAt.restrictScalars ℝ).differentiableAt
    ((contDiff_hypDisc.differentiable (by simp)) p)]
  exact (injective_fderiv_of_hasDerivAt hg hd).comp (fderiv_hypDisc_injective p)

theorem isLocalDiffeomorphAt_tubeOne {x : ModelCoordinates} (hd : hb x ∈ discOne K.D) :
    IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞ K.tubeOne x := by
  set O := hypDisc ⁻¹' discOne K.D with hO
  have hOo : IsOpen O := (isOpen_discOne K.hσ).preimage contDiff_hypDisc.continuous
  have hmaps : MapsTo hypDisc O (Metric.ball 0 1) := fun p hp => mem_ball_zero_iff.2 hp.1
  have hg : ContDiffOn ℝ ∞ (K.σ.rotOne ∘ hypDisc) O :=
    K.contDiffOn_rotOne.comp contDiff_hypDisc.contDiffOn hmaps
  have hβ : ContDiffOn ℝ ∞ (K.betaOne ∘ hypDisc) O :=
    K.contDiffOn_betaOne.comp contDiff_hypDisc.contDiffOn (fun p hp => hp)
  obtain ⟨d, hd0, hdd⟩ := K.hasDerivAt_rotOne hd.1
  exact isLocalDiffeomorphAt_hypTubeLift hOo hg K.a₁ K.p₁_pos.ne' K.ℓ_ne hβ hd
    (injective_fderiv_comp_hypDisc hd0 hdd)

theorem isLocalDiffeomorphAt_tubeTwo {x : ModelCoordinates} (hd : hb x ∈ discTwo K.D) :
    IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞ K.tubeTwo x := by
  set O := hypDisc ⁻¹' discTwo K.D with hO
  have hOo : IsOpen O := (isOpen_discTwo K.hσ).preimage contDiff_hypDisc.continuous
  have hmaps : MapsTo hypDisc O (Metric.ball 0 1) := fun p hp => mem_ball_zero_iff.2 hp.1
  have hg : ContDiffOn ℝ ∞ (K.σ.rotTwo ∘ hypDisc) O :=
    K.contDiffOn_rotTwo.comp contDiff_hypDisc.contDiffOn hmaps
  have hβ : ContDiffOn ℝ ∞ (K.betaTwo ∘ hypDisc) O :=
    K.contDiffOn_betaTwo.comp contDiff_hypDisc.contDiffOn (fun p hp => hp)
  obtain ⟨d, hd0, hdd⟩ := K.hasDerivAt_rotTwo hd.1
  exact isLocalDiffeomorphAt_hypTubeLift hOo hg K.a₂ K.p₂_pos.ne' K.ℓ_ne hβ hd
    (injective_fderiv_comp_hypDisc hd0 hdd)

theorem isLocalDiffeomorphAt_tubeThree (x : ModelCoordinates) :
    IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞ K.tubeThree x := by
  have hg : ContDiffOn ℝ ∞ ((fun w => (Circle.exp (Real.pi / K.σ.p₃) : ℂ) * w) ∘ hypDisc)
      univ := (contDiff_const.mul contDiff_id).comp contDiff_hypDisc |>.contDiffOn
  have hdd : HasDerivAt (fun w => (Circle.exp (Real.pi / K.σ.p₃) : ℂ) * w)
      (Circle.exp (Real.pi / K.σ.p₃) : ℂ) (hypDisc (planeOf x)) := by
    simpa using (hasDerivAt_id (hypDisc (planeOf x))).const_mul
      ((Circle.exp (Real.pi / K.σ.p₃) : ℂ))
  have h := isLocalDiffeomorphAt_hypTubeLift isOpen_univ hg K.a₃ K.p₃_pos.ne' K.ℓ_ne
    (β := fun _ => K.betaThree) contDiffOn_const (mem_univ (planeOf x))
    (injective_fderiv_comp_hypDisc (Circle.coe_ne_zero _) hdd)
  refine IsLocalDiffeomorphAt.of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_) h
  rfl

end Smooth

section Screws

theorem base_le : K.m.baseCurvature ≤ 0 := hyp_base_le K.hm

def pOne : ℕ+ := pnatOf K.σ.two_le_p₁

def pTwo : ℕ+ := pnatOf K.σ.two_le_p₂

def pThree : ℕ+ := pnatOf K.σ.two_le_p₃

theorem coe_pOne : ((K.pOne : ℕ) : ℝ) = K.σ.p₁ := rfl

theorem coe_pTwo : ((K.pTwo : ℕ) : ℝ) = K.σ.p₂ := rfl

theorem coe_pThree : ((K.pThree : ℕ) : ℝ) = K.σ.p₃ := rfl

def screwOne : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates :=
  screwAt K.m K.base_le (hypVertex K.σ.vertexOne) K.pOne K.q₁ K.ℓ

def screwTwo : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates :=
  screwAt K.m K.base_le (hypVertex K.σ.vertexTwo) K.pTwo K.q₂ K.ℓ

def screwThree : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates :=
  screwAt K.m K.base_le 0 K.pThree K.q₃ K.ℓ

theorem metric_screwOne :
    Diffeomorph.pullbackMetric K.m.coneProfile.metric K.screwOne = K.m.coneProfile.metric :=
  screwAt_isometry _ _ _ _ _ _

theorem metric_screwTwo :
    Diffeomorph.pullbackMetric K.m.coneProfile.metric K.screwTwo = K.m.coneProfile.metric :=
  screwAt_isometry _ _ _ _ _ _

theorem metric_screwThree :
    Diffeomorph.pullbackMetric K.m.coneProfile.metric K.screwThree = K.m.coneProfile.metric :=
  screwAt_isometry _ _ _ _ _ _

theorem two_screwOne' (x : ModelCoordinates) :
    K.screwOne x 2 = x 2 - K.ℓ * K.k₁ + K.ψ₁ (hb (K.screwOne x)) - K.ψ₁ (hb x) := by
  have h := K.two_screwOne x
  rw [show K.ℓ * K.q₁ / ((pnatOf K.σ.two_le_p₁ : ℕ) : ℝ) = K.ℓ * K.k₁ by
    rw [coe_pnatOf, k₁]; ring] at h
  exact h

theorem two_screwTwo' (x : ModelCoordinates) :
    K.screwTwo x 2 = x 2 - K.ℓ * K.k₂ + K.ψ₂ (hb (K.screwTwo x)) - K.ψ₂ (hb x) := by
  have h := K.two_screwTwo x
  rw [show K.ℓ * K.q₂ / ((pnatOf K.σ.two_le_p₂ : ℕ) : ℝ) = K.ℓ * K.k₂ by
    rw [coe_pnatOf, k₂]; ring] at h
  exact h

theorem rotOne_screwOne (x : ModelCoordinates) : K.σ.rotOne (hb (K.screwOne x)) =
    (Circle.exp (-2 * Real.pi / K.σ.p₁) : ℂ) * K.σ.rotOne (hb x) := by
  have h := mob_hb_screwAt K.m K.base_le K.hm (hypVertex K.σ.vertexOne) K.pOne K.q₁ K.ℓ x
  rw [hb_hypVertex (HypFold.norm_vertexOne_lt_one K.hσ)] at h
  rw [HypFold.rotOne_eq_mul_mob K.hσ, HypFold.rotOne_eq_mul_mob K.hσ]
  change _ * HypFold.mob _ (hb (screwAt K.m K.base_le (hypVertex K.σ.vertexOne) K.pOne K.q₁ K.ℓ
    x)) = _
  rw [h, coe_pOne]
  ring

theorem rotTwo_screwTwo (x : ModelCoordinates) : K.σ.rotTwo (hb (K.screwTwo x)) =
    (Circle.exp (-2 * Real.pi / K.σ.p₂) : ℂ) * K.σ.rotTwo (hb x) := by
  have h := mob_hb_screwAt K.m K.base_le K.hm (hypVertex K.σ.vertexTwo) K.pTwo K.q₂ K.ℓ x
  rw [hb_hypVertex (HypFold.norm_vertexTwo_lt_one K.hσ)] at h
  rw [HypFold.rotTwo_eq_mul_mob K.hσ, HypFold.rotTwo_eq_mul_mob K.hσ]
  change _ * HypFold.mob _ (hb (screwAt K.m K.base_le (hypVertex K.σ.vertexTwo) K.pTwo K.q₂ K.ℓ
    x)) = _
  rw [h, coe_pTwo]
  ring

omit K in
theorem coordinateShift_same (k : CoordinateModel)
    (hk : k = .hyperbolicProduct ∨ k = .universalSL2) (a y : ModelCoordinates) :
    coordinateShift k a a y = y := by
  rcases hk with rfl | rfl <;> ext i <;> fin_cases i <;>
    simp [coordinateShift, coordinateShiftLinear]

omit K in
theorem recentre_hyp_zero_apply (m : ConnectionModel) (hm : m.baseCurvature ≤ 0)
    (hmm : m = .hyperbolicProduct ∨ m = .universalSL2) (x : ModelCoordinates) :
    recentre m hm 0 x = x := by
  rcases hmm with rfl | rfl
  · rw [recentre_hyperbolicProduct_apply, coordinateShift_same _ (Or.inl rfl),
      hyperboloidMap_hyperboloidInv]
  · rw [recentre_universalSL2_apply, coordinateShift_same _ (Or.inr rfl),
      hyperboloidMap_hyperboloidInv]

theorem recentre_zero_apply (x : ModelCoordinates) : recentre K.m K.base_le 0 x = x :=
  recentre_hyp_zero_apply K.m K.base_le K.hm x

theorem recentre_zero_symm_apply (x : ModelCoordinates) :
    (recentre K.m K.base_le 0).symm x = x := by
  conv_lhs => rw [← K.recentre_zero_apply x]
  exact (recentre K.m K.base_le 0).symm_apply_apply x

theorem screwThree_apply (x : ModelCoordinates) :
    K.screwThree x = screwDiffeomorph (-2 * Real.pi / K.pThree) (-K.ℓ * K.q₃ / K.pThree) x := by
  change recentre K.m K.base_le 0 (screwDiffeomorph _ _ ((recentre K.m K.base_le 0).symm x)) = _
  rw [K.recentre_zero_apply, K.recentre_zero_symm_apply]

theorem hb_screwThree (x : ModelCoordinates) :
    hb (K.screwThree x) = (Circle.exp (-2 * Real.pi / K.σ.p₃) : ℂ) * hb x := by
  rw [K.screwThree_apply, hb_screwDiffeomorph, coe_pThree]

theorem planeOf_screwThree (x : ModelCoordinates) :
    planeOf (K.screwThree x) = (Circle.exp (-2 * Real.pi / K.σ.p₃) : ℂ) * planeOf x := by
  rw [K.screwThree_apply, screwDiffeomorph_apply', planeOf_add_fibreShift, planeOf_planeRotation,
    coe_pThree]

theorem two_screwThree (x : ModelCoordinates) : K.screwThree x 2 = x 2 - K.ℓ * K.k₃ := by
  rw [K.screwThree_apply, screwDiffeomorph_apply']
  simp only [PiLp.add_apply, planeRotation_apply_two, fibreShift_apply_two, coe_pThree, k₃]
  ring

theorem screwThree_rotThreeInv (x : ModelCoordinates) : K.screwThree (K.rotThreeInv x) = x := by
  apply modelCoordinates_ext
  · rw [planeOf_screwThree, rotThreeInv, planeOf_ofPlane, ← mul_assoc, ← Circle.coe_mul,
      ← Circle.exp_add]
    have hθ := FlatDatum.p_inv_eq K.p₃_pos (HypFold.θ₃_mul K.σ)
    rw [show -2 * Real.pi / K.σ.p₃ + 2 * K.σ.θ₃ = 0 by rw [hθ]; ring, Circle.exp_zero,
      Circle.coe_one, one_mul]
  · rw [two_screwThree, rotThreeInv, ofPlane_apply_two]
    ring

theorem screwThree_symm (x : ModelCoordinates) : K.screwThree.symm x = K.rotThreeInv x := by
  conv_lhs => rw [← K.screwThree_rotThreeInv x]
  exact K.screwThree.symm_apply_apply _

end Screws

end HypDatum

end Hyp

end ClosedTriangle

end GC.Seifert
