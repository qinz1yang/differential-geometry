import DifferentialGeometry.Topology.Manifold.Quotient
import DifferentialGeometry.Geometry.Metric.Quotient
import DifferentialGeometry.Geometry.Metric.Distance.InducedMetricSpace

/-!
# The anisotropic flat three-torus as an orbit quotient (lane S-FIXTURE-C1, K1, file 1)

External review 75 (D75-9, question 9): a rectangular lattice quotient `ℝ³ / (L₀ℤ ⊕ L₁ℤ ⊕ L₂ℤ)`
with independent periods, so that the circle fixture C1 (`L = (L, L, ε)`) and a torus-slim
fixture share one carrier. The carrier is the orbit quotient of `ℝ³` by the lattice translation
group, so the tree's orbit-quotient manifold machinery (`Topology/Manifold/Quotient.lean`) gives
the `ℝ³` charts (model `𝓘(ℝ, ℝ³)`, the model of every chapter-14 packet) and the smooth structure.

* `TorusPeriods_FXC1`, `TorusGroup_FXC1`, `latticeVec_FXC1`: the data and the translation action;
* `TorusGroup_FXC1.norm_latticeVec_ge`: a lattice vector is at least `|n_i| L_i` long;
* instances: continuous, properly discontinuous, free, smooth action;
* `Tor_FXC1 Λ`: the quotient (compact, connected, `T₂`), `torPi_FXC1 : ℝ³ → Tor Λ` the covering map
  (a local diffeomorphism and a covering) and `torPi_eq_iff_FXC1` (fibres are lattice orbits).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The three positive periods of a rectangular lattice. -/
structure TorusPeriods_FXC1 where
  L : Fin 3 → ℝ
  pos : ∀ i, 0 < L i

/-- The group of lattice translations (a type synonym of `ℤ³`, indexed by the periods so that the
action can be an instance). -/
def TorusGroup_FXC1 (_Λ : TorusPeriods_FXC1) : Type := Multiplicative (Fin 3 → ℤ)

instance (Λ : TorusPeriods_FXC1) : Group (TorusGroup_FXC1 Λ) :=
  inferInstanceAs (Group (Multiplicative (Fin 3 → ℤ)))

/-- The integer coordinates of a lattice element. -/
def TorusGroup_FXC1.toInts {Λ : TorusPeriods_FXC1} (n : TorusGroup_FXC1 Λ) : Fin 3 → ℤ :=
  Multiplicative.toAdd (α := Fin 3 → ℤ) n

/-- The lattice element with the given integer coordinates. -/
def TorusGroup_FXC1.ofInts (Λ : TorusPeriods_FXC1) (m : Fin 3 → ℤ) : TorusGroup_FXC1 Λ :=
  Multiplicative.ofAdd (α := Fin 3 → ℤ) m

theorem toInts_one_FXC1 (Λ : TorusPeriods_FXC1) : (1 : TorusGroup_FXC1 Λ).toInts = 0 := rfl

theorem toInts_mul_FXC1 {Λ : TorusPeriods_FXC1} (a b : TorusGroup_FXC1 Λ) :
    (a * b).toInts = a.toInts + b.toInts := rfl

theorem toInts_ofInts_FXC1 (Λ : TorusPeriods_FXC1) (m : Fin 3 → ℤ) :
    (TorusGroup_FXC1.ofInts Λ m).toInts = m := rfl

/-- The translation vector `(n₀ L₀, n₁ L₁, n₂ L₂)` of a lattice element. -/
def latticeVec_FXC1 (Λ : TorusPeriods_FXC1) (n : TorusGroup_FXC1 Λ) : E3 :=
  WithLp.toLp 2 fun i => ((n.toInts i : ℤ) : ℝ) * Λ.L i

theorem latticeVec_apply_FXC1 (Λ : TorusPeriods_FXC1) (n : TorusGroup_FXC1 Λ) (i : Fin 3) :
    latticeVec_FXC1 Λ n i = ((n.toInts i : ℤ) : ℝ) * Λ.L i := rfl

theorem latticeVec_one_FXC1 (Λ : TorusPeriods_FXC1) : latticeVec_FXC1 Λ 1 = 0 := by
  ext i
  simp [latticeVec_apply_FXC1, toInts_one_FXC1]

theorem latticeVec_mul_FXC1 (Λ : TorusPeriods_FXC1) (a b : TorusGroup_FXC1 Λ) :
    latticeVec_FXC1 Λ (a * b) = latticeVec_FXC1 Λ a + latticeVec_FXC1 Λ b := by
  ext i
  simp [latticeVec_apply_FXC1, toInts_mul_FXC1, add_mul]

instance (Λ : TorusPeriods_FXC1) : MulAction (TorusGroup_FXC1 Λ) E3 where
  smul n x := x + latticeVec_FXC1 Λ n
  one_smul x := by
    change x + latticeVec_FXC1 Λ 1 = x
    rw [latticeVec_one_FXC1, add_zero]
  mul_smul a b x := by
    change x + latticeVec_FXC1 Λ (a * b) = (x + latticeVec_FXC1 Λ b) + latticeVec_FXC1 Λ a
    rw [latticeVec_mul_FXC1]
    abel

theorem smul_def_FXC1 (Λ : TorusPeriods_FXC1) (n : TorusGroup_FXC1 Λ) (x : E3) :
    n • x = x + latticeVec_FXC1 Λ n := rfl


/-- A lattice vector is at least `|n_i| L_i` long. -/
theorem abs_toInts_mul_le_norm_FXC1 (Λ : TorusPeriods_FXC1) (n : TorusGroup_FXC1 Λ) (i : Fin 3) :
    |((n.toInts i : ℤ) : ℝ)| * Λ.L i ≤ ‖latticeVec_FXC1 Λ n‖ := by
  have h := PiLp.norm_apply_le (latticeVec_FXC1 Λ n) i
  rw [latticeVec_apply_FXC1, Real.norm_eq_abs, abs_mul, abs_of_pos (Λ.pos i)] at h
  exact h

theorem latticeVec_injective_FXC1 (Λ : TorusPeriods_FXC1) :
    Injective (latticeVec_FXC1 Λ) := by
  intro a b h
  have h' : a.toInts = b.toInts := by
    funext i
    have hi := congrArg (fun v : E3 => v i) h
    simp only [latticeVec_apply_FXC1] at hi
    exact_mod_cast mul_right_cancel₀ (Λ.pos i).ne' hi
  exact h'

instance (Λ : TorusPeriods_FXC1) : ContinuousConstSMul (TorusGroup_FXC1 Λ) E3 :=
  ⟨fun _ => continuous_id.add continuous_const⟩

instance (Λ : TorusPeriods_FXC1) : IsCancelSMul (TorusGroup_FXC1 Λ) E3 where
  left_cancel' a x y h := by
    rw [smul_def_FXC1, smul_def_FXC1] at h
    exact add_right_cancel h
  right_cancel' a b x h := by
    rw [smul_def_FXC1, smul_def_FXC1] at h
    exact latticeVec_injective_FXC1 Λ (add_left_cancel h)

instance (Λ : TorusPeriods_FXC1) : ContMDiffConstSMul 𝓘(ℝ, E3) ∞ (TorusGroup_FXC1 Λ) E3 :=
  ⟨fun _ => (contDiff_id.add contDiff_const).contMDiff⟩

/-- The lattice vectors of norm at most `B` form a finite set of elements. -/
theorem finite_norm_latticeVec_le_FXC1 (Λ : TorusPeriods_FXC1) (B : ℝ) :
    {n : TorusGroup_FXC1 Λ | ‖latticeVec_FXC1 Λ n‖ ≤ B}.Finite := by
  have hfin : (Set.pi (Set.univ : Set (Fin 3)) fun i =>
      Set.Icc (-⌈B / Λ.L i⌉) ⌈B / Λ.L i⌉).Finite :=
    Set.Finite.pi fun i => Set.finite_Icc _ _
  refine (hfin.image (TorusGroup_FXC1.ofInts Λ)).subset fun n hn => ?_
  refine ⟨n.toInts, fun i _ => ?_, rfl⟩
  have h1 := abs_toInts_mul_le_norm_FXC1 Λ n i
  have h2 : |((n.toInts i : ℤ) : ℝ)| ≤ B / Λ.L i := by
    rw [le_div_iff₀ (Λ.pos i)]
    exact h1.trans hn
  have h3 : ((n.toInts i : ℤ) : ℝ) ≤ ((⌈B / Λ.L i⌉ : ℤ) : ℝ) :=
    (le_abs_self _).trans (h2.trans (Int.le_ceil _))
  have h4 : -((n.toInts i : ℤ) : ℝ) ≤ ((⌈B / Λ.L i⌉ : ℤ) : ℝ) :=
    (neg_le_abs _).trans (h2.trans (Int.le_ceil _))
  exact ⟨by exact_mod_cast (by linarith : -((⌈B / Λ.L i⌉ : ℤ) : ℝ) ≤ ((n.toInts i : ℤ) : ℝ)),
    by exact_mod_cast h3⟩

/-- Compact sets meet only finitely many lattice translates of each other. -/
instance (Λ : TorusPeriods_FXC1) : ProperlyDiscontinuousSMul (TorusGroup_FXC1 Λ) E3 where
  finite_disjoint_inter_image {K L} hK hL := by
    obtain ⟨r, hr⟩ := (hK.isBounded.union hL.isBounded).subset_closedBall (0 : E3)
    refine (finite_norm_latticeVec_le_FXC1 Λ (2 * r)).subset fun n hn => ?_
    obtain ⟨y, ⟨x, hx, rfl⟩, hyL⟩ := hn
    have hx' := hr (Or.inl hx)
    have hy' := hr (Or.inr hyL)
    rw [mem_closedBall, dist_zero_right] at hx' hy'
    change ‖latticeVec_FXC1 Λ n‖ ≤ 2 * r
    have : latticeVec_FXC1 Λ n = (n • x) - x := by rw [smul_def_FXC1]; abel
    rw [this]
    calc ‖n • x - x‖ ≤ ‖n • x‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ 2 * r := by linarith


/-! ### The quotient -/

/-- The flat three-torus `ℝ³ / (L₀ℤ ⊕ L₁ℤ ⊕ L₂ℤ)` as the orbit space. -/
abbrev Tor_FXC1 (Λ : TorusPeriods_FXC1) : Type :=
  MulAction.orbitRel.Quotient (TorusGroup_FXC1 Λ) E3

/-- The covering map `ℝ³ → T³`. -/
def torPi_FXC1 (Λ : TorusPeriods_FXC1) : E3 → Tor_FXC1 Λ := Quotient.mk''

theorem torPi_surjective_FXC1 (Λ : TorusPeriods_FXC1) : Surjective (torPi_FXC1 Λ) :=
  Quotient.mk''_surjective

theorem torPi_eq_iff_FXC1 {Λ : TorusPeriods_FXC1} {x y : E3} :
    torPi_FXC1 Λ x = torPi_FXC1 Λ y ↔ ∃ n : TorusGroup_FXC1 Λ, y = x + latticeVec_FXC1 Λ n := by
  change (Quotient.mk'' x : Tor_FXC1 Λ) = Quotient.mk'' y ↔ _
  rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_symm,
    MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [← hn, smul_def_FXC1]⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [smul_def_FXC1, hn]⟩

example (Λ : TorusPeriods_FXC1) : ChartedSpace E3 (Tor_FXC1 Λ) := inferInstance
example (Λ : TorusPeriods_FXC1) : IsManifold 𝓘(ℝ, E3) ∞ (Tor_FXC1 Λ) := inferInstance
example (Λ : TorusPeriods_FXC1) : T2Space (Tor_FXC1 Λ) := inferInstance
example (Λ : TorusPeriods_FXC1) : ConnectedSpace (Tor_FXC1 Λ) := inferInstance


theorem torPi_isLocalDiffeomorph_FXC1 (Λ : TorusPeriods_FXC1) :
    IsLocalDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) ∞ (torPi_FXC1 Λ) :=
  MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul 𝓘(ℝ, E3)

theorem torPi_isCoveringMap_FXC1 (Λ : TorusPeriods_FXC1) : IsCoveringMap (torPi_FXC1 Λ) :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap

theorem contMDiff_torPi_FXC1 (Λ : TorusPeriods_FXC1) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, E3) ∞ (torPi_FXC1 Λ) :=
  (torPi_isLocalDiffeomorph_FXC1 Λ).contMDiff

/-- Every point of `ℝ³` is a lattice translate of a point of a fixed closed ball. -/
theorem exists_mem_closedBall_torPi_eq_FXC1 (Λ : TorusPeriods_FXC1) (x : E3) :
    ∃ y ∈ closedBall (0 : E3) (Λ.L 0 + Λ.L 1 + Λ.L 2), torPi_FXC1 Λ y = torPi_FXC1 Λ x := by
  let m : Fin 3 → ℤ := fun i => -⌊x i / Λ.L i⌋
  let n : TorusGroup_FXC1 Λ := TorusGroup_FXC1.ofInts Λ m
  refine ⟨x + latticeVec_FXC1 Λ n, ?_, ?_⟩
  · have hcoord : ∀ i, |(x + latticeVec_FXC1 Λ n) i| ≤ Λ.L i := fun i => by
      have hL := Λ.pos i
      have h1 := Int.floor_le (x i / Λ.L i)
      have h2 := Int.lt_floor_add_one (x i / Λ.L i)
      rw [le_div_iff₀ hL] at h1
      rw [div_lt_iff₀ hL] at h2
      have hv : (x + latticeVec_FXC1 Λ n) i = x i - (⌊x i / Λ.L i⌋ : ℤ) * Λ.L i := by
        simp [latticeVec_apply_FXC1, n, m, toInts_ofInts_FXC1]
        ring
      rw [hv, abs_le]
      constructor <;> nlinarith
    rw [mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
    have l0 := Λ.pos 0
    have l1 := Λ.pos 1
    have l2 := Λ.pos 2
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    rw [Fin.sum_univ_three]
    simp only [Real.norm_eq_abs, sq_abs]
    have h0 := hcoord 0
    have h1 := hcoord 1
    have h2 := hcoord 2
    have l0 := Λ.pos 0
    have l1 := Λ.pos 1
    have l2 := Λ.pos 2
    have a0 := sq_le_sq' (abs_le.mp h0).1 (abs_le.mp h0).2
    have a1 := sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
    have a2 := sq_le_sq' (abs_le.mp h2).1 (abs_le.mp h2).2
    nlinarith [mul_pos l0 l1, mul_pos l0 l2, mul_pos l1 l2]
  · exact (torPi_eq_iff_FXC1.mpr ⟨n, rfl⟩).symm


instance (Λ : TorusPeriods_FXC1) : CompactSpace (Tor_FXC1 Λ) := by
  refine ⟨?_⟩
  have h : (univ : Set (Tor_FXC1 Λ)) =
      torPi_FXC1 Λ '' closedBall (0 : E3) (Λ.L 0 + Λ.L 1 + Λ.L 2) := by
    ext z
    obtain ⟨x, rfl⟩ := torPi_surjective_FXC1 Λ z
    obtain ⟨y, hy, hyx⟩ := exists_mem_closedBall_torPi_eq_FXC1 Λ x
    exact ⟨fun _ => ⟨y, hy, hyx⟩, fun _ => mem_univ _⟩
  rw [h]
  exact (isCompact_closedBall _ _).image (contMDiff_torPi_FXC1 Λ).continuous

example (Λ : TorusPeriods_FXC1) : T3Space (Tor_FXC1 Λ) := inferInstance

end DifferentialGeometry.Geometry.Collapse
