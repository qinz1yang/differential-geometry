import DifferentialGeometry.Topology.Manifold.Quotient

/-!
# The normal line bundle of a closed curve as a quotient manifold (S-TUBE, D3)

Package CM-S (finite soul), lane CMS-T. Disposition D3 of the finite-soul review: the normal tube
of a closed geodesic is modelled on the quotient line bundle
`(ℝ × ℝ) / ((t + 1, h) ∼ (t, σ h))`, `σ ∈ {±1} = ℤˣ` (the period is normalised to `1`).

* `NormalCover σ`: the plane `ℝ × ℝ` with the deck action of `Multiplicative ℤ`,
  `n • (t, h) = (t + n, σ^n h)`; the action is free, properly discontinuous and smooth.
* `NormalLineBundle σ`: the orbit space. Its charted space is Mathlib's
  `MulAction.instChartedSpaceQuotient`, its manifold structure the tree's
  `MulAction.isManifold_quotient_of_contMDiffConstSMul`, and the projection is a local
  diffeomorphism (`isLocalDiffeomorph_mk`).
* `NormalLineBundle.fiberAbs`: the fibre norm `|h|` (well defined since `|σ^n| = 1`); the open
  `ε`-tube is `{q | fiberAbs q < ε}`; the zero section `t ↦ mk σ t 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

/-- The real number `σ^k` for `σ ∈ ℤˣ`. -/
def holonomyPow (σ : ℤˣ) (k : ℤ) : ℝ := (((σ ^ k : ℤˣ) : ℤ) : ℝ)

theorem holonomyPow_zero (σ : ℤˣ) : holonomyPow σ 0 = 1 := by
  simp [holonomyPow]

theorem holonomyPow_one (σ : ℤˣ) : holonomyPow σ 1 = ((σ : ℤ) : ℝ) := by
  simp [holonomyPow]

theorem holonomyPow_add (σ : ℤˣ) (a b : ℤ) :
    holonomyPow σ (a + b) = holonomyPow σ a * holonomyPow σ b := by
  simp [holonomyPow, zpow_add]

theorem abs_holonomyPow (σ : ℤˣ) (k : ℤ) : |holonomyPow σ k| = 1 := by
  unfold holonomyPow
  rcases Int.units_eq_one_or (σ ^ k) with h | h <;> rw [h] <;> simp

theorem holonomyPow_mul_self (σ : ℤˣ) (k : ℤ) : holonomyPow σ k * holonomyPow σ k = 1 := by
  have h := abs_holonomyPow σ k
  rcases abs_eq (zero_le_one) |>.mp h with h' | h' <;> rw [h'] <;> norm_num

/-- The cover of the normal line bundle with holonomy `σ`: the plane `ℝ × ℝ` (coordinates
`(t, h)`) carrying the deck action `n • (t, h) = (t + n, σ^n h)`. -/
def NormalCover : ℤˣ → Type := fun _ => ℝ × ℝ

namespace NormalCover

variable (σ : ℤˣ)

instance : TopologicalSpace (NormalCover σ) := inferInstanceAs (TopologicalSpace (ℝ × ℝ))

instance : T2Space (NormalCover σ) := inferInstanceAs (T2Space (ℝ × ℝ))

instance : LocallyCompactSpace (NormalCover σ) := inferInstanceAs (LocallyCompactSpace (ℝ × ℝ))

instance : ChartedSpace (ℝ × ℝ) (NormalCover σ) := inferInstanceAs (ChartedSpace (ℝ × ℝ) (ℝ × ℝ))

instance (n : WithTop ℕ∞) : IsManifold 𝓘(ℝ, ℝ × ℝ) n (NormalCover σ) :=
  inferInstanceAs (IsManifold 𝓘(ℝ, ℝ × ℝ) n (ℝ × ℝ))

/-- A point of the cover from its coordinates. -/
def mk (t h : ℝ) : NormalCover σ := (t, h)

/-- The time coordinate. -/
def time (z : NormalCover σ) : ℝ := (show ℝ × ℝ from z).1

/-- The fibre coordinate. -/
def fiber (z : NormalCover σ) : ℝ := (show ℝ × ℝ from z).2

instance : SMul (Multiplicative ℤ) (NormalCover σ) where
  smul n z := mk σ (time σ z + ((Multiplicative.toAdd n : ℤ) : ℝ))
    (holonomyPow σ (Multiplicative.toAdd n) * fiber σ z)

theorem smul_def (n : Multiplicative ℤ) (z : NormalCover σ) :
    n • z = mk σ (time σ z + ((Multiplicative.toAdd n : ℤ) : ℝ))
      (holonomyPow σ (Multiplicative.toAdd n) * fiber σ z) := rfl

@[simp] theorem time_mk (t h : ℝ) : time σ (mk σ t h) = t := rfl

@[simp] theorem fiber_mk (t h : ℝ) : fiber σ (mk σ t h) = h := rfl

theorem mk_time_fiber (z : NormalCover σ) : mk σ (time σ z) (fiber σ z) = z := rfl

variable {σ} in
theorem ext_iff' {z w : NormalCover σ} : z = w ↔ time σ z = time σ w ∧ fiber σ z = fiber σ w :=
  Prod.ext_iff

instance : MulAction (Multiplicative ℤ) (NormalCover σ) where
  one_smul z := by
    rw [smul_def, toAdd_one, Int.cast_zero, add_zero, holonomyPow_zero, one_mul, mk_time_fiber]
  mul_smul a b z := by
    rw [smul_def, smul_def, smul_def, time_mk, fiber_mk, toAdd_mul, holonomyPow_add, Int.cast_add]
    congr 1
    · ring
    · ring

theorem continuous_time : Continuous (time σ) := continuous_fst

theorem continuous_fiber : Continuous (fiber σ) := continuous_snd

theorem continuous_mk : Continuous (fun p : ℝ × ℝ => mk σ p.1 p.2) := continuous_id

instance : ContinuousConstSMul (Multiplicative ℤ) (NormalCover σ) where
  continuous_const_smul n :=
    (((continuous_time σ).add continuous_const).prodMk
      (continuous_const.mul (continuous_fiber σ)) : Continuous fun z : ℝ × ℝ =>
        (z.1 + ((Multiplicative.toAdd n : ℤ) : ℝ), holonomyPow σ (Multiplicative.toAdd n) * z.2))

instance : IsCancelSMul (Multiplicative ℤ) (NormalCover σ) where
  left_cancel' a b c hbc := by
    have h := congrArg (fun z => a⁻¹ • z) hbc
    simpa only [inv_smul_smul] using h
  right_cancel' a b c habc := by
    have h := congrArg (time σ) habc
    rw [smul_def, smul_def, time_mk, time_mk, add_right_inj] at h
    exact Multiplicative.toAdd.injective (by exact_mod_cast h)

instance : ProperlyDiscontinuousSMul (Multiplicative ℤ) (NormalCover σ) where
  finite_disjoint_inter_image {K L} hK hL := by
    obtain ⟨R, hR⟩ := ((hK.union hL).image (continuous_time σ)).isBounded.subset_closedBall 0
    have hRb : ∀ z ∈ K ∪ L, |time σ z| ≤ R := fun z hz => by
      have := hR (mem_image_of_mem _ hz)
      rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    set N : ℤ := ⌈2 * R⌉ with hN
    refine ((Set.finite_Icc (-N) N).image Multiplicative.ofAdd).subset ?_
    rintro n ⟨_, ⟨k, hk, rfl⟩, hkL⟩
    refine ⟨Multiplicative.toAdd n, ?_, rfl⟩
    have h1 := hRb k (Or.inl hk)
    have h2 := hRb _ (Or.inr hkL)
    change |time σ (n • k)| ≤ R at h2
    rw [smul_def, time_mk] at h2
    have h3 : |((Multiplicative.toAdd n : ℤ) : ℝ)| ≤ 2 * R := by
      have := abs_sub (time σ k + ((Multiplicative.toAdd n : ℤ) : ℝ)) (time σ k)
      rw [add_sub_cancel_left] at this
      linarith
    have h4 : |((Multiplicative.toAdd n : ℤ) : ℝ)| ≤ (N : ℝ) := h3.trans (Int.le_ceil _)
    rw [abs_le] at h4
    exact ⟨by exact_mod_cast h4.1, by exact_mod_cast h4.2⟩

instance (n : WithTop ℕ∞) : ContMDiffConstSMul 𝓘(ℝ, ℝ × ℝ) n (Multiplicative ℤ) (NormalCover σ) where
  contMDiff_const_smul k := by
    have h : ContDiff ℝ n (fun z : ℝ × ℝ =>
        (z.1 + ((Multiplicative.toAdd k : ℤ) : ℝ), holonomyPow σ (Multiplicative.toAdd k) * z.2)) :=
      (contDiff_fst.add contDiff_const).prodMk (contDiff_const.mul contDiff_snd)
    exact h.contMDiff

end NormalCover

/-- **The normal line bundle** `(ℝ × ℝ) / ((t + 1, h) ∼ (t, σ h))` of a closed curve with holonomy
`σ ∈ ℤˣ`, as the orbit space of the deck action on `NormalCover σ`. -/
abbrev NormalLineBundle (σ : ℤˣ) : Type :=
  MulAction.orbitRel.Quotient (Multiplicative ℤ) (NormalCover σ)

namespace NormalLineBundle

variable (σ : ℤˣ)

/-- The projection of the cover. -/
def proj : NormalCover σ → NormalLineBundle σ := Quotient.mk _

/-- The class of `(t, h)`. -/
def mk (t h : ℝ) : NormalLineBundle σ := proj σ (NormalCover.mk σ t h)

theorem proj_smul (n : Multiplicative ℤ) (z : NormalCover σ) : proj σ (n • z) = proj σ z :=
  MulAction.orbitRel.Quotient.quotient_smul_eq

variable {σ} in
theorem proj_eq_proj_iff {z w : NormalCover σ} :
    proj σ z = proj σ w ↔ ∃ n : Multiplicative ℤ, n • w = z := by
  unfold proj
  rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]

variable {σ} in
theorem mk_eq_mk_iff {t h t' h' : ℝ} :
    mk σ t h = mk σ t' h' ↔ ∃ n : ℤ, t' = t + n ∧ h' = holonomyPow σ n * h := by
  unfold mk
  rw [eq_comm, proj_eq_proj_iff]
  constructor
  · rintro ⟨n, hn⟩
    rw [NormalCover.smul_def, NormalCover.ext_iff'] at hn
    simp only [NormalCover.time_mk, NormalCover.fiber_mk] at hn
    exact ⟨Multiplicative.toAdd n, hn.1.symm, hn.2.symm⟩
  · rintro ⟨n, h1, h2⟩
    refine ⟨Multiplicative.ofAdd n, ?_⟩
    rw [NormalCover.smul_def, NormalCover.ext_iff']
    simp only [NormalCover.time_mk, NormalCover.fiber_mk, toAdd_ofAdd]
    exact ⟨h1.symm, h2.symm⟩

theorem mk_add_int (t h : ℝ) (n : ℤ) : mk σ (t + n) (holonomyPow σ n * h) = mk σ t h :=
  (mk_eq_mk_iff.mpr ⟨n, rfl, rfl⟩).symm

theorem proj_surjective : Function.Surjective (proj σ) := Quotient.mk_surjective

theorem continuous_proj : Continuous (proj σ) := continuous_quotient_mk'

theorem continuous_mk : Continuous (fun p : ℝ × ℝ => mk σ p.1 p.2) :=
  (continuous_proj σ).comp (NormalCover.continuous_mk σ)

/-- The projection is a local diffeomorphism of every order. -/
theorem isLocalDiffeomorph_proj (n : WithTop ℕ∞) :
    IsLocalDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) n (proj σ) :=
  MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul (n := n) 𝓘(ℝ, ℝ × ℝ)

theorem isOpenMap_proj : IsOpenMap (proj σ) :=
  (isLocalDiffeomorph_proj σ 1).isOpenMap

/-- Every class has a representative with time in `[0, 1)`. -/
theorem exists_mk_eq (q : NormalLineBundle σ) : ∃ t ∈ Ico (0 : ℝ) 1, ∃ h : ℝ, mk σ t h = q := by
  obtain ⟨z, rfl⟩ := proj_surjective σ q
  refine ⟨Int.fract (NormalCover.time σ z), ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩,
    holonomyPow σ (-⌊NormalCover.time σ z⌋) * NormalCover.fiber σ z, ?_⟩
  rw [← NormalCover.mk_time_fiber σ z]
  change mk σ _ _ = mk σ _ _
  rw [mk_eq_mk_iff]
  refine ⟨⌊NormalCover.time σ z⌋, ?_, ?_⟩
  · rw [NormalCover.time_mk, Int.fract]; ring
  · rw [NormalCover.fiber_mk, NormalCover.time_mk, ← mul_assoc, ← holonomyPow_add, add_neg_cancel,
      holonomyPow_zero, one_mul]

/-- **The fibre norm** `|h|` of the class of `(t, h)`. -/
def fiberAbs : NormalLineBundle σ → ℝ :=
  Quotient.lift (fun z : NormalCover σ => |NormalCover.fiber σ z|) (by
    intro a b hab
    obtain ⟨n, rfl⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hab)
    change |NormalCover.fiber σ (n • b)| = |NormalCover.fiber σ b|
    rw [NormalCover.smul_def, NormalCover.fiber_mk, abs_mul, abs_holonomyPow, one_mul])

@[simp] theorem fiberAbs_mk (t h : ℝ) : fiberAbs σ (mk σ t h) = |h| := rfl

theorem fiberAbs_proj (z : NormalCover σ) : fiberAbs σ (proj σ z) = |NormalCover.fiber σ z| := rfl

theorem continuous_fiberAbs : Continuous (fiberAbs σ) :=
  (continuous_abs.comp (NormalCover.continuous_fiber σ)).quotient_lift _

/-- The open `ε`-tube around the zero section. -/
theorem isOpen_tube (ε : ℝ) : IsOpen {q : NormalLineBundle σ | fiberAbs σ q < ε} :=
  isOpen_lt (continuous_fiberAbs σ) continuous_const

/-- The zero section is compact. -/
theorem isCompact_zeroSection : IsCompact (range fun t : ℝ => mk σ t 0) := by
  have h : range (fun t : ℝ => mk σ t 0) = (fun t : ℝ => mk σ t 0) '' Icc 0 1 := by
    refine Subset.antisymm ?_ (image_subset_range _ _)
    rintro _ ⟨t, rfl⟩
    refine ⟨Int.fract t, ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, ?_⟩
    rw [mk_eq_mk_iff]
    refine ⟨⌊t⌋, by rw [Int.fract]; ring, by rw [mul_zero]⟩
  rw [h]
  exact isCompact_Icc.image ((continuous_mk σ).comp (continuous_id.prodMk continuous_const))

/-- The tube is the image of the strip. -/
theorem tube_eq_image (ε : ℝ) : {q : NormalLineBundle σ | fiberAbs σ q < ε} =
    (fun p : ℝ × ℝ => mk σ p.1 p.2) '' (Ico 0 1 ×ˢ Ioo (-ε) ε) := by
  ext q
  constructor
  · intro hq
    obtain ⟨t, ht, h, rfl⟩ := exists_mk_eq σ q
    change fiberAbs σ (mk σ t h) < ε at hq
    rw [fiberAbs_mk] at hq
    exact ⟨(t, h), ⟨ht, abs_lt.mp hq⟩, rfl⟩
  · rintro ⟨⟨t, h⟩, ⟨-, hh⟩, rfl⟩
    change fiberAbs σ (mk σ t h) < ε
    rw [fiberAbs_mk]
    exact abs_lt.mpr hh

/-- Every neighbourhood of the zero section contains an open tube. -/
theorem exists_tube_subset {N : Set (NormalLineBundle σ)}
    (hN : N ∈ 𝓝ˢ (range fun t : ℝ => mk σ t 0)) :
    ∃ ε > 0, {q : NormalLineBundle σ | fiberAbs σ q < ε} ⊆ N := by
  obtain ⟨U, hUo, hZU, hUN⟩ := mem_nhdsSet_iff_exists.mp hN
  have hpre : IsOpen ((fun p : ℝ × ℝ => mk σ p.1 p.2) ⁻¹' U) := hUo.preimage (continuous_mk σ)
  have hsub : Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ) ⊆ (fun p : ℝ × ℝ => mk σ p.1 p.2) ⁻¹' U := by
    rintro ⟨t, h⟩ ⟨-, hh⟩
    rw [mem_singleton_iff] at hh
    subst hh
    exact hZU ⟨t, rfl⟩
  obtain ⟨u, v, -, hv, hu, h0v, huv⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton hpre hsub
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hv 0 (h0v rfl)
  refine ⟨ε, hε, fun q hq => ?_⟩
  obtain ⟨t, ht, h, rfl⟩ := exists_mk_eq σ q
  change fiberAbs σ (mk σ t h) < ε at hq
  rw [fiberAbs_mk] at hq
  have hhv : h ∈ v := hball (by rwa [Metric.mem_ball, Real.dist_eq, sub_zero])
  exact hUN (huv (show (t, h) ∈ u ×ˢ v from ⟨hu ⟨ht.1, ht.2.le⟩, hhv⟩))

/-- Two points of the strip `[0, 1) × ℝ` with the same class are equal. -/
theorem eq_of_mk_eq_of_mem_Ico {t h t' h' : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (ht' : t' ∈ Ico (0 : ℝ) 1)
    (heq : mk σ t h = mk σ t' h') : t = t' ∧ h = h' := by
  obtain ⟨n, h1, h2⟩ := mk_eq_mk_iff.mp heq
  have hn : (n : ℝ) = 0 := by
    have hlt : |(n : ℝ)| < 1 := by
      rw [abs_lt]; constructor <;> linarith [ht.1, ht.2, ht'.1, ht'.2]
    have hn' : n = 0 := by
      have : |n| < 1 := by exact_mod_cast hlt
      exact Int.abs_lt_one_iff.mp this
    rw [hn', Int.cast_zero]
  have hn0 : n = 0 := by exact_mod_cast hn
  subst hn0
  rw [holonomyPow_zero, one_mul] at h2
  exact ⟨by rw [h1, Int.cast_zero, add_zero], h2.symm⟩

end NormalLineBundle

end DifferentialGeometry.Geometry.FiniteSoul
