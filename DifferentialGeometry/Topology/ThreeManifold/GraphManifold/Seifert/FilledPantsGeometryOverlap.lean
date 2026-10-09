import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryLift

/-!
# The model maps of the two-cone fold and their overlap identities

Lane A5 (design `docs/geometrization/handoffs/20261004-design-a5-filled-pants-assembly.md`, §3.1,
with review 21 §4.1, §5.5). For the cones `(p₁, q₁)` at `3/2` and `(p₂, q₂)` at `-3/2`, with
Bézout columns `(aᵢ, bᵢ)`, `kᵢ = qᵢ/pᵢ` and `c₀ = k₁ + k₂`:
`liftT p = (f z, e(s) basePhase(f z))` on the triangle side, `liftS = conjPair ∘ liftT ∘ flip_{c₀}`
on the mirrored side, and the tube coordinates `tubeOne p = (ω₁ e(a₁(s + β₁)), e(p₁(s + β₁)))`,
`tubeTwo p = (ξ e(a₂(s + β₂)), e(p₂(s + β₂)))` with `ξ = e^{iθ₂} ω₂` and the smooth fibre shifts
`β₁ = -k₂ phaseArg(-3/2)(f z)/2π`, `β₂ = -k₁ phaseArg(3/2)(f z)/2π` (the second-cone constant of
review 21 §5.5 is the value of `β₂` at `v₂`; it rotates both tube coordinates). On the overlaps the
base lift is the inner seam model of the tube coordinates: `liftT = seamFwd(tubeOne)` on
`mainSet ∩ discOne` (`liftT_eq_seamFwd_tubeOne`), `liftT = seamFwd(tubeTwo)` on `mainSet ∩ discTwo`
(`liftT_eq_seamFwd_tubeTwo`), `liftT = liftS` on `patchZero` (`liftT_eq_liftS`), and `tubeTwo` is
mirror symmetric on `discTwo` (`conjPair_tubeTwo_flip`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

namespace GC.Seifert

namespace TwoConeFold

namespace Fold

open ConeShape

structure Numbers where
  p₁ : ℕ
  p₂ : ℕ
  q₁ : ℤ
  q₂ : ℤ
  a₁ : ℤ
  a₂ : ℤ
  b₁ : ℤ
  b₂ : ℤ

variable {σ : ConeShape} (D : σ.FoldData) (n : Numbers)

def Numbers.k₁ : ℝ := (n.q₁ : ℝ) / n.p₁

def Numbers.k₂ : ℝ := (n.q₂ : ℝ) / n.p₂

def Numbers.c₀ : ℝ := n.k₁ + n.k₂

def liftT (p : ModelCoordinates) : ℂ × Circle :=
  (D.f (zOf p), eC (p 2) * basePhase n.k₁ n.k₂ (D.f (zOf p)))

def liftS (p : ModelCoordinates) : ℂ × Circle := conjPair (liftT D n (flipMap n.c₀ p))

def betaOne (z : ℂ) : ℝ := -n.k₂ * phaseArg (-(3 / 2)) (D.f z) / (2 * Real.pi)

def betaTwo (z : ℂ) : ℝ := -n.k₁ * phaseArg (3 / 2) (D.f z) / (2 * Real.pi)

def tubeOne (p : ModelCoordinates) : ℂ × Circle :=
  (coneDisc σ.vertexOne (zOf p) * (eC (n.a₁ * (p 2 + betaOne D n (zOf p))) : ℂ),
    eC (n.p₁ * (p 2 + betaOne D n (zOf p))))

def tubeTwo (p : ModelCoordinates) : ℂ × Circle :=
  (exp (σ.θ₂ * I) * coneDisc σ.vertexTwo (zOf p) * (eC (n.a₂ * (p 2 + betaTwo D n (zOf p))) : ℂ),
    eC (n.p₂ * (p 2 + betaTwo D n (zOf p))))

def tubeOneS (p : ModelCoordinates) : ℂ × Circle := conjPair (tubeOne D n (flipMap n.c₀ p))

variable {n} (hθ₁ : σ.θ₁ * n.p₁ = Real.pi) (hθ₂ : σ.θ₂ * n.p₂ = Real.pi)

theorem refl_zero_zOf_flip (c : ℝ) (p : ModelCoordinates) :
    zOf (flipMap c p) = σ.refl 0 (zOf p) := by
  rw [coe_logPoint_flipMap]
  rfl

include hθ₁ in
theorem kOne_mul : n.k₁ * n.p₁ = n.q₁ := by
  rw [Numbers.k₁, div_mul_cancel₀ _ (by exact_mod_cast p₁_ne_zero hθ₁)]

include hθ₂ in
theorem kTwo_mul : n.k₂ * n.p₂ = n.q₂ := by
  rw [Numbers.k₂, div_mul_cancel₀ _ (by exact_mod_cast p₂_ne_zero hθ₂)]

theorem circle_exp_arg_zpow {w : ℂ} (hw : w ≠ 0) (n : ℤ) :
    unitOf w ^ n = Circle.exp (n * arg w) := by
  rw [unitOf_eq_exp_arg hw, Circle.exp_intCast_mul]

include hθ₁ hθ₂ in
theorem liftT_eq_seamFwd_tubeOne (hb₁ : (n.p₁ : ℤ) * n.b₁ - n.a₁ * n.q₁ = 1)
    {p : ModelCoordinates} (hm : zOf p ∈ mainSet D hθ₁ hθ₂) (hd : zOf p ∈ discOne D hθ₁) :
    liftT D n p = seamFwd ((3 / 2 : ℝ) : ℂ) n.p₁ n.p₁ n.q₁ n.a₁ n.b₁ (tubeOne D n p) := by
  obtain ⟨hne, h1, h2⟩ := sector_one D hθ₁ hθ₂ hm hd
  have hf := (radiusOne_spec D hθ₁ hd.1 hd.2).2.1
  set η := coneDisc σ.vertexOne (zOf p) with hη
  have hap := seamFwd_apex (c := ((3 / 2 : ℝ) : ℂ)) (P := n.p₁) (p := n.p₁) (q := n.q₁)
    (a := n.a₁) (b := n.b₁) hb₁ rfl η hne (p 2 + betaOne D n (zOf p))
  have hfz : D.f (zOf p) = ((3 / 2 : ℝ) : ℂ) + η ^ n.p₁ / 2 := by
    rw [hf, coneApexOne, ← hη]
    push_cast
    ring
  unfold tubeOne
  change _ = seamFwd ((3 / 2 : ℝ) : ℂ) n.p₁ n.p₁ n.q₁ n.a₁ n.b₁
    (η * (Circle.exp (2 * Real.pi * (n.a₁ * (p 2 + betaOne D n (zOf p)))) : ℂ),
      Circle.exp (2 * Real.pi * (n.p₁ * (p 2 + betaOne D n (zOf p)))))
  rw [hap]
  unfold liftT
  rw [hfz]
  congr 1
  have hpa : phaseArg (3 / 2) (((3 / 2 : ℝ) : ℂ) + η ^ n.p₁ / 2) = n.p₁ * arg η :=
    phaseArg_apex (3 / 2) hne h1 h2.le
  have hβ : betaOne D n (zOf p) =
      -n.k₂ * phaseArg (-(3 / 2)) (((3 / 2 : ℝ) : ℂ) + η ^ n.p₁ / 2) / (2 * Real.pi) := by
    rw [betaOne, hfz]
  rw [basePhase, hpa, circle_exp_arg_zpow hne, hβ, eC, ← Circle.exp_add, ← Circle.exp_add]
  congr 1
  have hk := kOne_mul hθ₁
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  field_simp
  push_cast
  linear_combination (-arg η) * hk

include hθ₂ in
theorem f_eq_apexTwo_xi {z : ℂ} (hd : z ∈ discTwo D hθ₂) :
    D.f z = ((-(3 / 2) : ℝ) : ℂ) + (exp (σ.θ₂ * I) * coneDisc σ.vertexTwo z) ^ n.p₂ / 2 := by
  rw [(radiusTwo_spec D hθ₂ hd.1 hd.2).2.1, coneApexTwo, mul_pow, ← exp_nat_mul]
  have : (n.p₂ : ℂ) * ((σ.θ₂ : ℂ) * I) = ((σ.θ₂ * n.p₂ : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, hθ₂, exp_pi_mul_I]
  push_cast
  ring

include hθ₁ hθ₂ in
theorem liftT_eq_seamFwd_tubeTwo (hb₂ : (n.p₂ : ℤ) * n.b₂ - n.a₂ * n.q₂ = 1)
    {p : ModelCoordinates} (hm : zOf p ∈ mainSet D hθ₁ hθ₂) (hd : zOf p ∈ discTwo D hθ₂) :
    liftT D n p = seamFwd ((-(3 / 2) : ℝ) : ℂ) n.p₂ n.p₂ n.q₂ n.a₂ n.b₂ (tubeTwo D n p) := by
  obtain ⟨hne, h1, h2⟩ := sector_two D hθ₁ hθ₂ hm hd
  set η := exp (σ.θ₂ * I) * coneDisc σ.vertexTwo (zOf p) with hη
  have hap := seamFwd_apex (c := ((-(3 / 2) : ℝ) : ℂ)) (P := n.p₂) (p := n.p₂) (q := n.q₂)
    (a := n.a₂) (b := n.b₂) hb₂ rfl η hne (p 2 + betaTwo D n (zOf p))
  have hfz : D.f (zOf p) = ((-(3 / 2) : ℝ) : ℂ) + η ^ n.p₂ / 2 := f_eq_apexTwo_xi D hθ₂ hd
  unfold tubeTwo
  change _ = seamFwd ((-(3 / 2) : ℝ) : ℂ) n.p₂ n.p₂ n.q₂ n.a₂ n.b₂
    (η * (Circle.exp (2 * Real.pi * (n.a₂ * (p 2 + betaTwo D n (zOf p)))) : ℂ),
      Circle.exp (2 * Real.pi * (n.p₂ * (p 2 + betaTwo D n (zOf p)))))
  rw [hap]
  unfold liftT
  rw [hfz]
  congr 1
  have hpa : phaseArg (-(3 / 2)) (((-(3 / 2) : ℝ) : ℂ) + η ^ n.p₂ / 2) = n.p₂ * arg η :=
    phaseArg_apex (-(3 / 2)) hne h1 h2.le
  have hβ : betaTwo D n (zOf p) =
      -n.k₁ * phaseArg (3 / 2) (((-(3 / 2) : ℝ) : ℂ) + η ^ n.p₂ / 2) / (2 * Real.pi) := by
    rw [betaTwo, hfz]
  rw [basePhase, hpa, circle_exp_arg_zpow hne, hβ, eC, ← Circle.exp_add, ← Circle.exp_add]
  congr 1
  have hk := kTwo_mul hθ₂
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  field_simp
  push_cast
  linear_combination (-arg η) * hk

theorem liftT_eq_liftS {p : ModelCoordinates} (hz : zOf p ∈ patchZero D hθ₂) :
    liftT D n p = liftS D n p := by
  obtain ⟨-, hV, -, -, -, hre, -⟩ := hz
  have hfl : D.f (zOf (flipMap n.c₀ p)) = conj (D.f (zOf p)) := by
    rw [refl_zero_zOf_flip]
    exact D.f_refl 0 _ hV
  unfold liftS liftT conjPair
  rw [hfl, Complex.conj_conj, flipMap_two, basePhase_conj_of_lt _ _ hre]
  congr 1
  rw [eC, eC, Numbers.c₀, mul_inv, mul_inv, inv_inv, ← Circle.exp_neg, ← Circle.exp_neg,
    ← mul_assoc, ← Circle.exp_add]
  congr 2
  ring

include hθ₂ in
theorem conjPair_tubeTwo_flip (hb₂ : (n.p₂ : ℤ) * n.b₂ - n.a₂ * n.q₂ = 1) {p : ModelCoordinates}
    (hd : zOf p ∈ discTwo D hθ₂) : conjPair (tubeTwo D n (flipMap n.c₀ p)) = tubeTwo D n p := by
  have hspec := radiusTwo_spec D hθ₂ hd.1 hd.2
  have hV := hspec.2.2.2.1
  set z := zOf p with hz
  have hzf : zOf (flipMap n.c₀ p) = σ.refl 0 z := refl_zero_zOf_flip n.c₀ p
  have hω : coneDisc σ.vertexTwo (σ.refl 0 z) = conj (coneDisc σ.vertexTwo z) :=
    σ.coneDisc_vertexTwo_refl_zero z
  have hre : (D.f z).re < 3 / 2 := by
    rw [f_eq_apexTwo_xi D hθ₂ hd]
    have hlt : ‖coneDisc σ.vertexTwo z‖ < 1 := lt_of_lt_of_le hd.2 (radiusTwo_le D hθ₂)
    have hb : ‖(exp (σ.θ₂ * I) * coneDisc σ.vertexTwo z) ^ n.p₂ / 2‖ < 1 := by
      rw [norm_div, norm_pow, norm_mul, norm_exp_ofReal_mul_I, one_mul, Complex.norm_ofNat]
      have := pow_le_one₀ (norm_nonneg _) hlt.le (n := n.p₂)
      linarith
    have := Complex.re_le_norm ((exp (σ.θ₂ * I) * coneDisc σ.vertexTwo z) ^ n.p₂ / 2)
    simp only [add_re, ofReal_re]
    linarith
  have hβ : betaTwo D n (σ.refl 0 z) = -n.k₁ - betaTwo D n z := by
    rw [betaTwo, betaTwo, D.f_refl 0 z hV, phaseArg_conj_of_gt hre]
    field_simp
    ring
  unfold tubeTwo conjPair
  rw [hzf, hω, hβ, flipMap_two]
  have hk := kTwo_mul hθ₂
  have hθp : σ.θ₂ = Real.pi / n.p₂ := by
    rw [← hθ₂, mul_div_cancel_right₀ _ (by exact_mod_cast p₂_ne_zero hθ₂)]
  apply Prod.ext
  · have e1 : exp (σ.θ₂ * I) = (Circle.exp σ.θ₂ : ℂ) := (Circle.coe_exp _).symm
    have e2 : conj (exp (σ.θ₂ * I)) = (Circle.exp (-σ.θ₂) : ℂ) := by
      rw [e1, ← Circle.coe_inv_eq_conj, Circle.exp_neg]
    change conj (exp (σ.θ₂ * I) * conj (coneDisc σ.vertexTwo z) *
      (eC (n.a₂ * (n.c₀ - p 2 + (-n.k₁ - betaTwo D n z))) : ℂ)) = _
    rw [map_mul, map_mul, Complex.conj_conj, e2, ← Circle.coe_inv_eq_conj, ← eC_neg, e1]
    have key : Circle.exp (-σ.θ₂) * eC (-(n.a₂ * (n.c₀ - p 2 + (-n.k₁ - betaTwo D n z)))) =
        Circle.exp σ.θ₂ * eC (n.a₂ * (p 2 + betaTwo D n z)) := by
      rw [eC, eC, ← Circle.exp_add, ← Circle.exp_add]
      have hb' : ((n.p₂ : ℝ) * n.b₂ - n.a₂ * n.q₂) = 1 := by exact_mod_cast hb₂
      have : σ.θ₂ + 2 * Real.pi * (n.a₂ * (p 2 + betaTwo D n z)) =
          (-σ.θ₂ + 2 * Real.pi * -(n.a₂ * (n.c₀ - p 2 + (-n.k₁ - betaTwo D n z)))) +
            (n.b₂ : ℝ) * (2 * Real.pi) := by
        rw [Numbers.c₀, hθp]
        have hp0 : (n.p₂ : ℝ) ≠ 0 := by exact_mod_cast p₂_ne_zero hθ₂
        rw [Numbers.k₂]
        field_simp
        linear_combination (-2 : ℝ) * hb'
      rw [this, Circle.exp_add _ ((n.b₂ : ℝ) * (2 * Real.pi)), Circle.exp_int_mul_two_pi,
        mul_one]
    have := congrArg (fun w : Circle => (w : ℂ) * coneDisc σ.vertexTwo z) key
    simp only [Circle.coe_mul] at this
    linear_combination this
  · rw [← eC_neg]
    have : -(n.p₂ * (n.c₀ - p 2 + (-n.k₁ - betaTwo D n z))) =
        n.p₂ * (p 2 + betaTwo D n z) + ((-n.q₂ : ℤ) : ℝ) := by
      rw [Numbers.c₀]
      push_cast
      linear_combination -hk
    rw [this, eC_add, eC_int, mul_one]

section Smooth

def conjPairDiffeo : (ℂ × Circle) ≃ₘ⟮PlaneCircleModel, PlaneCircleModel⟯ (ℂ × Circle) where
  toFun := conjPair
  invFun := conjPair
  left_inv := conjPair_conjPair
  right_inv := conjPair_conjPair
  contMDiff_toFun := (Complex.conjCLE.contDiff.contMDiff.comp contMDiff_fst).prodMk
    (contMDiff_snd.inv)
  contMDiff_invFun := (Complex.conjCLE.contDiff.contMDiff.comp contMDiff_fst).prodMk
    (contMDiff_snd.inv)

include hθ₁ in
theorem re_f_of_mem_discOne {z : ℂ} (hd : z ∈ discOne D hθ₁) : 1 < (D.f z).re := by
  rw [(radiusOne_spec D hθ₁ hd.1 hd.2).2.1, coneApexOne]
  have hlt : ‖coneDisc σ.vertexOne z‖ < 1 := lt_of_lt_of_le hd.2 (radiusOne_le D hθ₁)
  have hb : ‖coneDisc σ.vertexOne z ^ n.p₁ / 2‖ < 1 / 2 := by
    rw [norm_div, norm_pow, Complex.norm_ofNat]
    have := pow_lt_one₀ (norm_nonneg _) hlt (p₁_ne_zero hθ₁)
    linarith
  have := Complex.abs_re_le_norm (coneDisc σ.vertexOne z ^ n.p₁ / 2)
  rw [abs_le] at this
  rw [show ((3 : ℂ) / 2 + coneDisc σ.vertexOne z ^ n.p₁ / 2).re =
    3 / 2 + (coneDisc σ.vertexOne z ^ n.p₁ / 2).re by norm_num]
  linarith [this.1]

include hθ₂ in
theorem re_f_of_mem_discTwo {z : ℂ} (hd : z ∈ discTwo D hθ₂) : (D.f z).re < -1 := by
  rw [(radiusTwo_spec D hθ₂ hd.1 hd.2).2.1, coneApexTwo]
  have hlt : ‖coneDisc σ.vertexTwo z‖ < 1 := lt_of_lt_of_le hd.2 (radiusTwo_le D hθ₂)
  have hb : ‖coneDisc σ.vertexTwo z ^ n.p₂ / 2‖ < 1 / 2 := by
    rw [norm_div, norm_pow, Complex.norm_ofNat]
    have := pow_lt_one₀ (norm_nonneg _) hlt (p₂_ne_zero hθ₂)
    linarith
  have := Complex.abs_re_le_norm (coneDisc σ.vertexTwo z ^ n.p₂ / 2)
  rw [abs_le] at this
  rw [show (-((3 : ℂ) / 2) - coneDisc σ.vertexTwo z ^ n.p₂ / 2).re =
    -(3 / 2) - (coneDisc σ.vertexTwo z ^ n.p₂ / 2).re by norm_num]
  linarith [this.1]

include hθ₁ hθ₂ in
theorem mainSet_props {z : ℂ} (hz : z ∈ mainSet D hθ₁ hθ₂) :
    z ∈ D.U ∧ z ≠ σ.vertexOne ∧ z ≠ σ.vertexTwo ∧ D.f z ∈ phaseDomain (3 / 2) ∧
      D.f z ∈ phaseDomain (-(3 / 2)) := by
  have hv1f := f_vertexOne D hθ₁
  have hv2f := f_vertexTwo D hθ₂
  have hv1w : σ.wallSide 2 σ.vertexOne = 0 := wallSide_two_vertexOne' σ
  have hv2w : σ.wallSide 2 σ.vertexTwo = 0 := by
    change (σ.vertexTwo.re - σ.centre) ^ 2 + σ.vertexTwo.im ^ 2 - 1 / 16 = 0
    rw [vertexTwo_re, vertexTwo_im]
    unfold centre
    nlinarith [Real.sin_sq_add_cos_sq σ.θ₂]
  rcases hz with ((h | h) | h) | h
  · obtain ⟨h0, hw⟩ := h
    have hT : z ∈ σ.triangle := ⟨h0, fun i => (hw i).le⟩
    have him := im_f_pos_of_interior D hT hw
    refine ⟨D.triangle_subset_U hT, fun he => ?_, fun he => ?_,
      mem_phaseDomain_iff.2 (Or.inl him), mem_phaseDomain_iff.2 (Or.inl him)⟩
    · have := hw 2; rw [he, hv1w] at this; exact lt_irrefl _ this
    · have := hw 2; rw [he, hv2w] at this; exact lt_irrefl _ this
  · obtain ⟨-, hV, -, hw2, -, hre, -⟩ := h
    refine ⟨D.V_subset_U 0 hV, fun he => ?_, fun he => ?_,
      mem_phaseDomain_of_re_ne (by linarith), mem_phaseDomain_of_re_ne (by linarith)⟩
    · rw [he, hv1f] at hre; norm_num at hre
    · rw [he, hv2w] at hw2; exact lt_irrefl _ hw2
  · obtain ⟨-, hV, -, -, hw2, -, hre, -⟩ := h
    refine ⟨D.V_subset_U 1 hV, fun he => ?_, fun he => ?_,
      mem_phaseDomain_of_re_ne (by linarith), mem_phaseDomain_of_re_ne (by linarith)⟩
    · rw [he, hv1w] at hw2; exact lt_irrefl _ hw2
    · rw [he, hv2w] at hw2; exact lt_irrefl _ hw2
  · obtain ⟨-, hV, -, -, -, -, hre1, hre2, -⟩ := h
    refine ⟨D.V_subset_U 2 hV, fun he => ?_, fun he => ?_,
      mem_phaseDomain_of_re_ne (by linarith), mem_phaseDomain_of_re_ne (by linarith)⟩
    · rw [he, hv1f] at hre2; norm_num at hre2
    · rw [he, hv2f] at hre1; norm_num at hre1

def liftDomain : Set ℂ :=
  {z | z ∈ D.U ∧ D.f z ∈ phaseDomain (3 / 2) ∧ D.f z ∈ phaseDomain (-(3 / 2))}

theorem isOpen_liftDomain : IsOpen (liftDomain D) :=
  D.contDiffOn_f.continuousOn.isOpen_inter_preimage D.isOpen_U
    ((isOpen_phaseDomain _).inter (isOpen_phaseDomain _))

include hθ₁ hθ₂ in
theorem isLocalDiffeomorphAt_liftT {p : ModelCoordinates} (hm : zOf p ∈ mainSet D hθ₁ hθ₂) :
    IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞ (liftT D n) p := by
  obtain ⟨hU, hne1, hne2, hd1, hd2⟩ := mainSet_props D hθ₁ hθ₂ hm
  have hf : ContDiffOn ℝ ∞ D.f (liftDomain D) := D.contDiffOn_f.mono fun z hz => hz.1
  have hΨ : ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 1) ∞ (fun z => basePhase n.k₁ n.k₂ (D.f z))
      (liftDomain D) := fun z hz =>
    ((contMDiffAt_basePhase n.k₁ n.k₂ hz.2.1 hz.2.2).comp z
      ((D.contDiffOn_f.contDiffAt (D.isOpen_U.mem_nhds hz.1)).contMDiffAt)).contMDiffWithinAt
  exact isLocalDiffeomorphAt_baseLift (isOpen_liftDomain D) hf hΨ ⟨hU, hd1, hd2⟩
    (det_ne_zero D hU hne1 hne2)

include hθ₁ hθ₂ in
theorem isLocalDiffeomorphAt_liftS {p : ModelCoordinates}
    (hm : zOf p ∈ mirrorSet σ (mainSet D hθ₁ hθ₂)) :
    IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞ (liftS D n) p := by
  have hm' : zOf (flipMap n.c₀ p) ∈ mainSet D hθ₁ hθ₂ := by
    rw [refl_zero_zOf_flip]; exact hm.2
  have h1 := IsLocalDiffeomorphAt.comp (hf := (foldFlip n.c₀).isLocalDiffeomorph p)
    (hg := isLocalDiffeomorphAt_liftT D hθ₁ hθ₂ hm' (n := n))
  exact IsLocalDiffeomorphAt.comp (hf := h1) (hg := conjPairDiffeo.isLocalDiffeomorph _)

include hθ₁ in
theorem isLocalDiffeomorphAt_tubeOne {p : ModelCoordinates} (hd : zOf p ∈ discOne D hθ₁) :
    IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞ (tubeOne D n) p := by
  have hβ : ContDiffOn ℝ ∞ (betaOne D n) (discOne D hθ₁) := by
    intro z hz
    have hfz := (D.contDiffOn_f.contDiffAt (D.isOpen_U.mem_nhds
      (radiusOne_spec D hθ₁ hz.1 hz.2).1))
    have hph := contDiffAt_phaseArg (c := -(3 / 2)) (mem_phaseDomain_of_re_ne
      (by linarith [re_f_of_mem_discOne D hθ₁ hz (n := n)] : (D.f z).re ≠ -(3 / 2)))
    exact ((contDiffAt_const.mul (hph.comp z hfz)).div_const _).contDiffWithinAt
  have h := isLocalDiffeomorphAt_tubeLift σ.vertexOne_im_pos one_ne_zero n.a₁
    (p₁_ne_zero hθ₁) (isOpen_discOne D hθ₁) (fun z hz => hz.1) hβ hd
  refine IsLocalDiffeomorphAt.of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_) h
  simp [tubeOne]

include hθ₂ in
theorem isLocalDiffeomorphAt_tubeTwo {p : ModelCoordinates} (hd : zOf p ∈ discTwo D hθ₂) :
    IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞ (tubeTwo D n) p := by
  have hβ : ContDiffOn ℝ ∞ (betaTwo D n) (discTwo D hθ₂) := by
    intro z hz
    have hfz := (D.contDiffOn_f.contDiffAt (D.isOpen_U.mem_nhds
      (radiusTwo_spec D hθ₂ hz.1 hz.2).1))
    have hph := contDiffAt_phaseArg (c := 3 / 2) (mem_phaseDomain_of_re_ne
      (by linarith [re_f_of_mem_discTwo D hθ₂ hz (n := n)] : (D.f z).re ≠ 3 / 2))
    exact ((contDiffAt_const.mul (hph.comp z hfz)).div_const _).contDiffWithinAt
  exact isLocalDiffeomorphAt_tubeLift (vertexTwo_im_pos' hθ₂) (exp_ne_zero _) n.a₂
    (p₂_ne_zero hθ₂) (isOpen_discTwo D hθ₂) (fun z hz => hz.1) hβ hd

include hθ₁ in
theorem isLocalDiffeomorphAt_tubeOneS {p : ModelCoordinates}
    (hd : zOf p ∈ mirrorSet σ (discOne D hθ₁)) :
    IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞ (tubeOneS D n) p := by
  have hd' : zOf (flipMap n.c₀ p) ∈ discOne D hθ₁ := by
    rw [refl_zero_zOf_flip]; exact hd.2
  have h1 := IsLocalDiffeomorphAt.comp (hf := (foldFlip n.c₀).isLocalDiffeomorph p)
    (hg := isLocalDiffeomorphAt_tubeOne D hθ₁ hd' (n := n))
  exact IsLocalDiffeomorphAt.comp (hf := h1) (hg := conjPairDiffeo.isLocalDiffeomorph _)

end Smooth

end Fold

end TwoConeFold

end GC.Seifert
