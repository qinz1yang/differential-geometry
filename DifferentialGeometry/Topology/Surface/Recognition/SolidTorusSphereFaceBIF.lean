import DifferentialGeometry.Topology.Surface.Recognition.EmbeddedFacePartitionBCFApplications

/-!
# The sphere face of the solid-torus acceptance configuration B-L (lane BIFACEd; D69-11, D75-4/5)

Review 69 D69-11 / draft 75 D75-4 configuration B-L (solid torus `D² × S¹`): a ball zero core `B`, ONE
interval edge handle whose two end disks lie on the SAME sphere face `∂B` (the loop incidence counted
twice), the circle remainder and one cusp collar. This file is the MODEL-LEVEL (D75-1 layer (i)) check
of the face output of BCF03 / G7 (`EmbeddedFacePartition_BCF`, lane B-BCF134) on that configuration;
layers (ii)–(iii) (an actual non-empty boundary chain and FAMZ's returned packet) are D75-12's
mixed-regression fixtures and wait for the boundary chain producer (A2-mk, lane BAUG-Dc).

* `solidTorusSphereFace_BIF : EmbeddedFacePartition_BCF SphereTwo`: the face `∂B = S²` with the two
  closed polar caps `{∓z ≥ 1/2}` as the two end disks of the one handle and the closed equatorial band
  `{|z| ≤ 1/2}` as the ONE circle-bundle piece (the arc annulus), with explicit parametrizations
  `capParam_BIF` (`D² → cap`, boundary circle onto `cap ∩ band`) and `bandParam_BIF`
  (`S¹ × [0, 1] → band`, the end circles `t = 0, 1` onto the two cap circles). It is the first
  NON-VACUOUS inhabitant of the sphere branch of FC40 (`torusFacePartition_BCF` covers the torus
  branch; `no_diskFree_sphere_partition_BCF` only excludes disk-free partitions).
* Consumers: `solidTorusSphereFace_diskCount_BIF` (FC40's general sphere count applies and agrees),
  `solidTorusHandleEnd_BIF` (the two ends of the one handle ↔ the two disks) and `solidTorusFaces_BIF`
  (the B-L face catalogue: sphere face with two disks, both ends of ONE handle on the same side piece,
  one piece; cusp-front torus face with no disk and one whole piece).
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology Metric

namespace DifferentialGeometry.Topology.Surface

open DifferentialGeometry.Topology

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

theorem norm_sq_three_BIF (v : E3) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
  simp [Real.norm_eq_abs, sq_abs]

theorem norm_sq_two_BIF (v : E2) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs]

theorem mem_sphere_three_iff_BIF {v : E3} :
    v ∈ sphere (0 : E3) 1 ↔ v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by
  rw [mem_sphere_zero_iff_norm, ← norm_sq_three_BIF]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg v) two_ne_zero).symm

theorem mem_sphere_two_iff_BIF {v : E2} :
    v ∈ sphere (0 : E2) 1 ↔ v 0 ^ 2 + v 1 ^ 2 = 1 := by
  rw [mem_sphere_zero_iff_norm, ← norm_sq_two_BIF]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg v) two_ne_zero).symm

theorem ext_three_BIF {v w : E3} (h0 : v 0 = w 0) (h1 : v 1 = w 1) (h2 : v 2 = w 2) : v = w := by
  ext i
  fin_cases i <;> assumption

theorem ext_two_BIF {v w : E2} (h0 : v 0 = w 0) (h1 : v 1 = w 1) : v = w := by
  ext i
  fin_cases i <;> assumption

/-- The height `z = x₂` of a point of `S²`. -/
def sphereHeight_BIF (p : SphereTwo) : ℝ :=
  (p : E3) 2

theorem continuous_sphereHeight_BIF : Continuous sphereHeight_BIF :=
  (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.comp continuous_subtype_val

/-- The side of a polar cap: `-1` (south, index `0`) or `1` (north, index `1`). -/
def capSign_BIF (i : Fin 2) : ℝ :=
  if i = 0 then -1 else 1

theorem capSign_sq_BIF (i : Fin 2) : capSign_BIF i ^ 2 = 1 := by
  unfold capSign_BIF
  split_ifs <;> norm_num

theorem capSign_mul_self_BIF (i : Fin 2) : capSign_BIF i * capSign_BIF i = 1 := by
  rw [← sq, capSign_sq_BIF]

/-- The polar cap `{s_i z ≥ 1/2}` of `S²`. -/
def sphereCap_BIF (i : Fin 2) : Set SphereTwo :=
  {p | 1 / 2 ≤ capSign_BIF i * sphereHeight_BIF p}

/-- The equatorial band `{|z| ≤ 1/2}` of `S²`. -/
def sphereBand_BIF : Set SphereTwo :=
  {p | |sphereHeight_BIF p| ≤ 1 / 2}

/-- The cap parametrization `v ↦ (r v, s_i √(1 − r²|v|²))`, `r = √3/2`. -/
def capVec_BIF (i : Fin 2) (v : E2) : E3 :=
  !₂[Real.sqrt 3 / 2 * v 0, Real.sqrt 3 / 2 * v 1,
    capSign_BIF i * Real.sqrt (1 - 3 / 4 * (v 0 ^ 2 + v 1 ^ 2))]

theorem sqrt_three_half_sq_BIF : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

theorem capVec_apply_BIF (i : Fin 2) (v : E2) :
    capVec_BIF i v 0 = Real.sqrt 3 / 2 * v 0 ∧ capVec_BIF i v 1 = Real.sqrt 3 / 2 * v 1 ∧
      capVec_BIF i v 2 = capSign_BIF i * Real.sqrt (1 - 3 / 4 * (v 0 ^ 2 + v 1 ^ 2)) := by
  simp [capVec_BIF]

theorem capVec_mem_BIF (i : Fin 2) (v : Disk 2) :
    capVec_BIF i (v : E2) ∈ sphere (0 : E3) 1 := by
  have hv : (v : E2) 0 ^ 2 + (v : E2) 1 ^ 2 ≤ 1 := by
    rw [← norm_sq_two_BIF]
    have := mem_closedBall_zero_iff.mp v.2
    nlinarith [norm_nonneg (v : E2)]
  rw [mem_sphere_three_iff_BIF]
  obtain ⟨a0, a1, a2⟩ := capVec_apply_BIF i (v : E2)
  rw [a0, a1, a2, mul_pow, mul_pow, mul_pow, sqrt_three_half_sq_BIF, capSign_sq_BIF,
    Real.sq_sqrt (by nlinarith)]
  ring

/-- The cap parametrization as a map `D² → S²`. -/
def capParam_BIF (i : Fin 2) (v : Disk 2) : SphereTwo :=
  ⟨capVec_BIF i v, capVec_mem_BIF i v⟩

theorem continuous_capParam_BIF (i : Fin 2) : Continuous (capParam_BIF i) := by
  refine Continuous.subtype_mk ?_ _
  have h0 : Continuous fun v : Disk 2 => (v : E2) 0 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous.comp continuous_subtype_val
  have h1 : Continuous fun v : Disk 2 => (v : E2) 1 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous.comp continuous_subtype_val
  simp only [capVec_BIF]
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp
    (continuous_pi fun k => by
      fin_cases k
      · exact continuous_const.mul h0
      · exact continuous_const.mul h1
      · exact continuous_const.mul
          ((continuous_const.sub (continuous_const.mul ((h0.pow 2).add (h1.pow 2)))).sqrt))

theorem sqrt_three_half_ne_zero_BIF : Real.sqrt 3 / 2 ≠ 0 := by
  positivity

theorem injective_capParam_BIF (i : Fin 2) : Injective (capParam_BIF i) := by
  intro v w h
  have h' : capVec_BIF i v = capVec_BIF i w := congrArg Subtype.val h
  obtain ⟨a0, a1, -⟩ := capVec_apply_BIF i v
  obtain ⟨b0, b1, -⟩ := capVec_apply_BIF i w
  apply Subtype.ext
  apply ext_two_BIF
  · have := congrFun (congrArg (fun x : E3 => (x : Fin 3 → ℝ)) h') 0
    simp only at this
    rw [a0, b0] at this
    exact mul_left_cancel₀ sqrt_three_half_ne_zero_BIF this
  · have := congrFun (congrArg (fun x : E3 => (x : Fin 3 → ℝ)) h') 1
    simp only at this
    rw [a1, b1] at this
    exact mul_left_cancel₀ sqrt_three_half_ne_zero_BIF this

theorem half_eq_sqrt_quarter_BIF : (1 / 2 : ℝ) = Real.sqrt (1 / 4) := by
  rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem sphere_coords_BIF (p : SphereTwo) :
    (p : E3) 0 ^ 2 + (p : E3) 1 ^ 2 + (p : E3) 2 ^ 2 = 1 :=
  mem_sphere_three_iff_BIF.mp p.2

theorem disk_sq_le_BIF (v : Disk 2) : (v : E2) 0 ^ 2 + (v : E2) 1 ^ 2 ≤ 1 := by
  rw [← norm_sq_two_BIF]
  have := mem_closedBall_zero_iff.mp v.2
  nlinarith [norm_nonneg (v : E2)]

/-- `s_i · z ∘ capParam = √(1 − 3|v|²/4)`. -/
theorem capSign_mul_height_capParam_BIF (i : Fin 2) (v : Disk 2) :
    capSign_BIF i * sphereHeight_BIF (capParam_BIF i v) =
      Real.sqrt (1 - 3 / 4 * ((v : E2) 0 ^ 2 + (v : E2) 1 ^ 2)) := by
  change capSign_BIF i * capVec_BIF i v 2 = _
  rw [(capVec_apply_BIF i v).2.2, ← mul_assoc, capSign_mul_self_BIF, one_mul]

/-- The preimage candidate `(x₀/r, x₁/r)` of a point of a cap. -/
def capPre_BIF (p : SphereTwo) : E2 :=
  !₂[(p : E3) 0 / (Real.sqrt 3 / 2), (p : E3) 1 / (Real.sqrt 3 / 2)]

theorem capPre_sq_BIF (p : SphereTwo) :
    capPre_BIF p 0 ^ 2 + capPre_BIF p 1 ^ 2 = 4 / 3 * (1 - sphereHeight_BIF p ^ 2) := by
  have h := sphere_coords_BIF p
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [capPre_BIF, sphereHeight_BIF]
  simp [div_pow, hs]
  field_simp
  linarith [h]

theorem capPre_mem_BIF (p : SphereTwo) (hz : 1 / 4 ≤ sphereHeight_BIF p ^ 2) :
    capPre_BIF p ∈ closedBall (0 : E2) 1 := by
  rw [mem_closedBall_zero_iff]
  have h2 : ‖capPre_BIF p‖ ^ 2 ≤ 1 := by
    rw [norm_sq_two_BIF, capPre_sq_BIF]
    linarith
  nlinarith [norm_nonneg (capPre_BIF p)]

theorem capSign_abs_BIF (i : Fin 2) : |capSign_BIF i| = 1 := by
  unfold capSign_BIF
  split_ifs <;> norm_num

theorem capParam_capPre_BIF (i : Fin 2) (p : SphereTwo)
    (hp : 1 / 2 ≤ capSign_BIF i * sphereHeight_BIF p) :
    capParam_BIF i ⟨capPre_BIF p, capPre_mem_BIF p (by
      have := capSign_sq_BIF i
      nlinarith [sq_nonneg (capSign_BIF i * sphereHeight_BIF p)])⟩ = p := by
  apply Subtype.ext
  change capVec_BIF i (capPre_BIF p) = (p : E3)
  obtain ⟨a0, a1, a2⟩ := capVec_apply_BIF i (capPre_BIF p)
  have hr := sqrt_three_half_ne_zero_BIF
  apply ext_three_BIF
  · rw [a0]
    simp only [capPre_BIF]
    simp
    field_simp
  · rw [a1]
    simp only [capPre_BIF]
    simp
    field_simp
  · rw [a2, capPre_sq_BIF]
    have hz : 1 - 3 / 4 * (4 / 3 * (1 - sphereHeight_BIF p ^ 2)) = sphereHeight_BIF p ^ 2 := by
      ring
    rw [hz, Real.sqrt_sq_eq_abs]
    have habs : |sphereHeight_BIF p| = capSign_BIF i * sphereHeight_BIF p := by
      rw [← abs_of_pos (by linarith : (0 : ℝ) < capSign_BIF i * sphereHeight_BIF p), abs_mul,
        capSign_abs_BIF, one_mul]
    rw [habs, ← mul_assoc, capSign_mul_self_BIF, one_mul]
    rfl

theorem range_capParam_BIF (i : Fin 2) : range (capParam_BIF i) = sphereCap_BIF i := by
  ext p
  constructor
  · rintro ⟨v, rfl⟩
    change 1 / 2 ≤ capSign_BIF i * sphereHeight_BIF (capParam_BIF i v)
    rw [capSign_mul_height_capParam_BIF, half_eq_sqrt_quarter_BIF]
    exact Real.sqrt_le_sqrt (by linarith [disk_sq_le_BIF v])
  · intro hp
    exact ⟨_, capParam_capPre_BIF i p hp⟩

theorem capParam_diskSphere_BIF (i : Fin 2) :
    capParam_BIF i '' diskSphere 2 = sphereCap_BIF i ∩ sphereBand_BIF := by
  ext p
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hq : (v : E2) 0 ^ 2 + (v : E2) 1 ^ 2 = 1 := by
      rw [← norm_sq_two_BIF, mem_diskSphere.mp hv]
      norm_num
    have hsz : capSign_BIF i * sphereHeight_BIF (capParam_BIF i v) = 1 / 2 := by
      rw [capSign_mul_height_capParam_BIF, hq, half_eq_sqrt_quarter_BIF]
      norm_num
    refine ⟨hsz.ge, ?_⟩
    change |sphereHeight_BIF (capParam_BIF i v)| ≤ 1 / 2
    have : |capSign_BIF i * sphereHeight_BIF (capParam_BIF i v)| = 1 / 2 := by
      rw [hsz]
      norm_num
    rw [abs_mul, capSign_abs_BIF, one_mul] at this
    exact this.le
  · rintro ⟨hc, hb⟩
    change 1 / 2 ≤ capSign_BIF i * sphereHeight_BIF p at hc
    change |sphereHeight_BIF p| ≤ 1 / 2 at hb
    have habs : |capSign_BIF i * sphereHeight_BIF p| = |sphereHeight_BIF p| := by
      rw [abs_mul, capSign_abs_BIF, one_mul]
    have hsz : capSign_BIF i * sphereHeight_BIF p = 1 / 2 :=
      le_antisymm ((le_abs_self _).trans (habs ▸ hb)) hc
    refine ⟨_, ?_, capParam_capPre_BIF i p hc⟩
    rw [mem_diskSphere]
    change ‖capPre_BIF p‖ = 1
    have hz2 : sphereHeight_BIF p ^ 2 = 1 / 4 := by
      have := capSign_sq_BIF i
      have h2 : (capSign_BIF i * sphereHeight_BIF p) ^ 2 = 1 / 4 := by
        rw [hsz]
        norm_num
      rw [mul_pow, this, one_mul] at h2
      exact h2
    have h2 : ‖capPre_BIF p‖ ^ 2 = 1 := by
      rw [norm_sq_two_BIF, capPre_sq_BIF, hz2]
      norm_num
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2

/-! ## The band parametrization `S¹ × [0, 1] → {|z| ≤ 1/2}` -/

/-- `(θ, t) ↦ (√(1 − z²) θ, z)`, `z = t − 1/2`. -/
def bandVec_BIF (θ : E2) (t : ℝ) : E3 :=
  !₂[Real.sqrt (1 - (t - 1 / 2) ^ 2) * θ 0, Real.sqrt (1 - (t - 1 / 2) ^ 2) * θ 1, t - 1 / 2]

theorem bandVec_apply_BIF (θ : E2) (t : ℝ) :
    bandVec_BIF θ t 0 = Real.sqrt (1 - (t - 1 / 2) ^ 2) * θ 0 ∧
      bandVec_BIF θ t 1 = Real.sqrt (1 - (t - 1 / 2) ^ 2) * θ 1 ∧ bandVec_BIF θ t 2 = t - 1 / 2 := by
  simp [bandVec_BIF]

theorem bandVec_mem_BIF (q : sphere (0 : E2) 1 × Icc (0 : ℝ) 1) :
    bandVec_BIF q.1 q.2 ∈ sphere (0 : E3) 1 := by
  have hθ := mem_sphere_two_iff_BIF.mp q.1.2
  have ht0 := q.2.2.1
  have ht1 := q.2.2.2
  rw [mem_sphere_three_iff_BIF]
  obtain ⟨a0, a1, a2⟩ := bandVec_apply_BIF (q.1 : E2) q.2
  rw [a0, a1, a2, mul_pow, mul_pow, Real.sq_sqrt (by nlinarith)]
  linear_combination (1 - ((q.2 : ℝ) - 1 / 2) ^ 2) * hθ

/-- The band parametrization. -/
def bandParam_BIF (q : sphere (0 : E2) 1 × Icc (0 : ℝ) 1) : SphereTwo :=
  ⟨bandVec_BIF q.1 q.2, bandVec_mem_BIF q⟩

theorem sphereHeight_bandParam_BIF (q : sphere (0 : E2) 1 × Icc (0 : ℝ) 1) :
    sphereHeight_BIF (bandParam_BIF q) = (q.2 : ℝ) - 1 / 2 :=
  (bandVec_apply_BIF (q.1 : E2) q.2).2.2

theorem continuous_bandParam_BIF : Continuous bandParam_BIF := by
  refine Continuous.subtype_mk ?_ _
  have hθ0 : Continuous fun q : sphere (0 : E2) 1 × Icc (0 : ℝ) 1 => (q.1 : E2) 0 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous.comp
      (continuous_subtype_val.comp continuous_fst)
  have hθ1 : Continuous fun q : sphere (0 : E2) 1 × Icc (0 : ℝ) 1 => (q.1 : E2) 1 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous.comp
      (continuous_subtype_val.comp continuous_fst)
  have ht : Continuous fun q : sphere (0 : E2) 1 × Icc (0 : ℝ) 1 => (q.2 : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  have hr : Continuous fun q : sphere (0 : E2) 1 × Icc (0 : ℝ) 1 =>
      Real.sqrt (1 - ((q.2 : ℝ) - 1 / 2) ^ 2) :=
    (continuous_const.sub ((ht.sub continuous_const).pow 2)).sqrt
  simp only [bandVec_BIF]
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp
    (continuous_pi fun k => by
      fin_cases k
      · exact hr.mul hθ0
      · exact hr.mul hθ1
      · exact ht.sub continuous_const)

theorem band_radius_pos_BIF (t : Icc (0 : ℝ) 1) : 0 < Real.sqrt (1 - ((t : ℝ) - 1 / 2) ^ 2) := by
  have := t.2.1
  have := t.2.2
  exact Real.sqrt_pos.mpr (by nlinarith)

theorem injective_bandParam_BIF : Injective bandParam_BIF := by
  rintro ⟨θ, t⟩ ⟨θ', t'⟩ h
  have h' : bandVec_BIF θ t = bandVec_BIF θ' t' := congrArg Subtype.val h
  have hc : ∀ k, bandVec_BIF θ t k = bandVec_BIF θ' t' k := fun k => by rw [h']
  obtain ⟨a0, a1, a2⟩ := bandVec_apply_BIF (θ : E2) t
  obtain ⟨b0, b1, b2⟩ := bandVec_apply_BIF (θ' : E2) t'
  have htt : (t : ℝ) = t' := by
    have := hc 2
    rw [a2, b2] at this
    linarith
  have htt' : t = t' := Subtype.ext htt
  subst htt'
  have hr := (band_radius_pos_BIF t).ne'
  have h0 := hc 0
  have h1 := hc 1
  rw [a0, b0] at h0
  rw [a1, b1] at h1
  refine Prod.ext (Subtype.ext (ext_two_BIF ?_ ?_)) rfl
  · exact mul_left_cancel₀ hr h0
  · exact mul_left_cancel₀ hr h1

/-- The preimage candidate of a band point: `θ = (x₀, x₁)/√(1 − z²)`. -/
def bandPreθ_BIF (p : SphereTwo) : E2 :=
  !₂[(p : E3) 0 / Real.sqrt (1 - sphereHeight_BIF p ^ 2),
    (p : E3) 1 / Real.sqrt (1 - sphereHeight_BIF p ^ 2)]

theorem bandParam_surj_BIF (p : SphereTwo) (hp : |sphereHeight_BIF p| ≤ 1 / 2) :
    ∃ q, bandParam_BIF q = p := by
  have hz2 : sphereHeight_BIF p ^ 2 ≤ 1 / 4 := by
    have := abs_le.mp hp
    nlinarith
  have hpos : 0 < 1 - sphereHeight_BIF p ^ 2 := by linarith
  have hsq : Real.sqrt (1 - sphereHeight_BIF p ^ 2) ^ 2 = 1 - sphereHeight_BIF p ^ 2 :=
    Real.sq_sqrt hpos.le
  have hne : Real.sqrt (1 - sphereHeight_BIF p ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hc := sphere_coords_BIF p
  have hθ : bandPreθ_BIF p ∈ sphere (0 : E2) 1 := by
    rw [mem_sphere_two_iff_BIF]
    simp only [bandPreθ_BIF]
    simp [div_pow, hsq]
    field_simp
    simp only [sphereHeight_BIF] at hsq hpos ⊢
    linarith
  have ht : sphereHeight_BIF p + 1 / 2 ∈ Icc (0 : ℝ) 1 := by
    have := abs_le.mp hp
    constructor <;> linarith
  refine ⟨(⟨bandPreθ_BIF p, hθ⟩, ⟨_, ht⟩), Subtype.ext ?_⟩
  change bandVec_BIF (bandPreθ_BIF p) (sphereHeight_BIF p + 1 / 2) = (p : E3)
  obtain ⟨a0, a1, a2⟩ := bandVec_apply_BIF (bandPreθ_BIF p) (sphereHeight_BIF p + 1 / 2)
  have hzz : sphereHeight_BIF p + 1 / 2 - 1 / 2 = sphereHeight_BIF p := by ring
  rw [hzz] at a0 a1 a2
  apply ext_three_BIF
  · rw [a0]
    simp only [bandPreθ_BIF]
    simp
    field_simp
  · rw [a1]
    simp only [bandPreθ_BIF]
    simp
    field_simp
  · rw [a2]
    rfl

theorem range_bandParam_BIF : range bandParam_BIF = sphereBand_BIF := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    change |sphereHeight_BIF (bandParam_BIF q)| ≤ 1 / 2
    rw [sphereHeight_bandParam_BIF]
    have := q.2.2.1
    have := q.2.2.2
    rw [abs_le]
    constructor <;> linarith
  · intro hp
    exact bandParam_surj_BIF p hp

theorem mem_cap_inter_band_iff_BIF {i : Fin 2} {p : SphereTwo} :
    p ∈ sphereCap_BIF i ∩ sphereBand_BIF ↔ sphereHeight_BIF p = capSign_BIF i / 2 := by
  constructor
  · rintro ⟨hc, hb⟩
    change 1 / 2 ≤ capSign_BIF i * sphereHeight_BIF p at hc
    change |sphereHeight_BIF p| ≤ 1 / 2 at hb
    have habs : |capSign_BIF i * sphereHeight_BIF p| = |sphereHeight_BIF p| := by
      rw [abs_mul, capSign_abs_BIF, one_mul]
    have hsz : capSign_BIF i * sphereHeight_BIF p = 1 / 2 :=
      le_antisymm ((le_abs_self _).trans (habs ▸ hb)) hc
    have := capSign_mul_self_BIF i
    calc sphereHeight_BIF p = capSign_BIF i * (capSign_BIF i * sphereHeight_BIF p) := by
          rw [← mul_assoc, this, one_mul]
      _ = capSign_BIF i / 2 := by rw [hsz]; ring
  · intro h
    refine ⟨?_, ?_⟩
    · change 1 / 2 ≤ capSign_BIF i * sphereHeight_BIF p
      rw [h, mul_div_assoc', capSign_mul_self_BIF]
    · change |sphereHeight_BIF p| ≤ 1 / 2
      rw [h, abs_div, capSign_abs_BIF]
      norm_num

/-- The end parameter of the cap `i` on the band: `t = 0` (south) or `t = 1` (north). -/
def capEndT_BIF (i : Fin 2) : ℝ :=
  capSign_BIF i / 2 + 1 / 2

theorem cap_inter_band_eq_BIF (i : Fin 2) :
    sphereCap_BIF i ∩ sphereBand_BIF = bandParam_BIF '' {q | (q.2 : ℝ) = capEndT_BIF i} := by
  ext p
  rw [mem_cap_inter_band_iff_BIF]
  constructor
  · intro h
    have hb : |sphereHeight_BIF p| ≤ 1 / 2 := by
      rw [h, abs_div, capSign_abs_BIF]
      norm_num
    obtain ⟨q, hq⟩ := bandParam_surj_BIF p hb
    refine ⟨q, ?_, hq⟩
    have h2 := sphereHeight_bandParam_BIF q
    rw [hq, h] at h2
    change (q.2 : ℝ) = capSign_BIF i / 2 + 1 / 2
    linarith
  · rintro ⟨q, hq, rfl⟩
    rw [sphereHeight_bandParam_BIF]
    change (q.2 : ℝ) = capSign_BIF i / 2 + 1 / 2 at hq
    linarith

theorem capEndT_cases_BIF (i : Fin 2) : capEndT_BIF i = 0 ∨ capEndT_BIF i = 1 := by
  unfold capEndT_BIF capSign_BIF
  split_ifs
  · left
    norm_num
  · right
    norm_num

/-- The equator point `(1, 0, 0)`. -/
def equatorPoint_BIF : SphereTwo :=
  ⟨!₂[1, 0, 0], by rw [mem_sphere_three_iff_BIF]; simp⟩

/-- **Inhabitant (the sphere face of the solid torus B-L, D69-11 / D75-4)**: the sphere `S²` as the
boundary `∂B` of the ball zero core of B-L — two closed polar caps `{∓z ≥ 1/2}` (the two END DISKS of
the ONE interval edge handle, both on this face: the loop incidence counted twice) and ONE closed
equatorial band `{|z| ≤ 1/2}` (the arc annulus of the circle remainder), with the cap
parametrizations `v ↦ (√3/2 · v, ±√(1 − 3|v|²/4))` and the band parametrization
`(θ, t) ↦ (√(1 − (t − 1/2)²) θ, t − 1/2)`. -/
def solidTorusSphereFace_BIF : EmbeddedFacePartition_BCF SphereTwo where
  diskCount := 2
  pieceCount := 1
  disk := sphereCap_BIF
  piece := fun _ => sphereBand_BIF
  side := fun _ => 0
  isClosed_disk := fun _ => isClosed_le continuous_const
    (continuous_const.mul continuous_sphereHeight_BIF)
  isClosed_piece := fun _ => isClosed_le (continuous_abs.comp continuous_sphereHeight_BIF)
    continuous_const
  piece_nonempty := fun _ => ⟨equatorPoint_BIF, by
    change |(!₂[(1 : ℝ), 0, 0] : E3) 2| ≤ 1 / 2
    simp⟩
  cover := by
    refine eq_univ_of_forall fun p => ?_
    by_cases h1 : 1 / 2 ≤ sphereHeight_BIF p
    · refine Or.inl (mem_iUnion.mpr ⟨1, ?_⟩)
      change 1 / 2 ≤ capSign_BIF 1 * sphereHeight_BIF p
      simpa [capSign_BIF] using h1
    by_cases h0 : sphereHeight_BIF p ≤ -(1 / 2)
    · refine Or.inl (mem_iUnion.mpr ⟨0, ?_⟩)
      change 1 / 2 ≤ capSign_BIF 0 * sphereHeight_BIF p
      have hs : capSign_BIF 0 = -1 := by simp [capSign_BIF]
      rw [hs]
      linarith
    · refine Or.inr (mem_iUnion.mpr ⟨0, ?_⟩)
      change |sphereHeight_BIF p| ≤ 1 / 2
      rw [abs_le]
      constructor <;> linarith
  disk_disjoint := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro p hi hj
    change 1 / 2 ≤ capSign_BIF i * sphereHeight_BIF p at hi
    change 1 / 2 ≤ capSign_BIF j * sphereHeight_BIF p at hj
    fin_cases i <;> fin_cases j
    · exact hij rfl
    · simp [capSign_BIF] at hi hj
      linarith
    · simp [capSign_BIF] at hi hj
      linarith
    · exact hij rfl
  piece_disjoint := fun i j hij => (hij (Subsingleton.elim i j)).elim
  side_spec := fun _ _ _ => Subsingleton.elim _ _
  degree := fun j => Or.inr (by rw [show j = 0 from Subsingleton.elim _ _]; simp)
  disk_param := fun i => ⟨capParam_BIF i, continuous_capParam_BIF i, injective_capParam_BIF i,
    range_capParam_BIF i, capParam_diskSphere_BIF i⟩
  annulus_param := fun _ _ => ⟨bandParam_BIF, continuous_bandParam_BIF, injective_bandParam_BIF,
    range_bandParam_BIF, fun i _ => by
      rw [cap_inter_band_eq_BIF]
      rcases capEndT_cases_BIF i with h | h
      · left
        rw [h]
      · right
        rw [h]⟩
  circle_base := fun j h => absurd h (by rw [show j = 0 from Subsingleton.elim _ _]; simp)

/-- **Consumer (FC40 on the B-L sphere face, non-vacuously)**: the general sphere count
`diskCount_eq_two_of_sphere` applies to the B-L sphere face and agrees with its two end disks. -/
theorem solidTorusSphereFace_diskCount_BIF : solidTorusSphereFace_BIF.diskCount = 2 :=
  solidTorusSphereFace_BIF.diskCount_eq_two_of_sphere (Homeomorph.refl _)

/-- The two ends of the ONE interval edge handle of B-L, as the two disks of its sphere face (end
`false` ↦ the south cap, end `true` ↦ the north cap). -/
def solidTorusHandleEnd_BIF : Bool ≃ Fin solidTorusSphereFace_BIF.diskCount :=
  finTwoEquiv.symm

/-- **Consumer (the face catalogue of B-L, model level)**: the sphere face `∂B` carries exactly two
disks, which are the two ends of the one handle (the loop incidence counted twice), both with the
same side piece (the arc annulus); the cusp-front torus face (`torusFacePartition_BCF`) carries none
and is one whole circle-bundle piece (FC40, BCF03's cusp branch). -/
theorem solidTorusFaces_BIF :
    solidTorusSphereFace_BIF.diskCount = 2 ∧
      solidTorusSphereFace_BIF.side (solidTorusHandleEnd_BIF false) =
        solidTorusSphereFace_BIF.side (solidTorusHandleEnd_BIF true) ∧
      solidTorusSphereFace_BIF.pieceCount = 1 ∧
      torusFacePartition_BCF.diskCount = 0 ∧ ∃ j, torusFacePartition_BCF.piece j = univ :=
  ⟨solidTorusSphereFace_diskCount_BIF, rfl,
    solidTorusSphereFace_BIF.pieceCount_eq_one (Y := SphereTwo),
    torusFacePartition_diskCount_BCF,
    torusFacePartition_BCF.exists_piece_eq_univ_of_torus (Homeomorph.refl _)⟩

end DifferentialGeometry.Topology.Surface
