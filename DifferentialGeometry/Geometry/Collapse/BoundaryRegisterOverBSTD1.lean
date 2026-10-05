import DifferentialGeometry.Geometry.Collapse.BoundaryEarlyThresholdsBSTD1

/-!
# The boundary register over an early choice and the zero scale `V` (lane BSTG-D1, D61-11 D2)

Dispositions of task 61, D61-11 (draft §7.2–7.3): after the early choice `E` (fixed before the
standing sequence) and the producer's finite zero scale `V` (an OUTPUT of the joint producer on
the sequence, never a free interval), the boundary register fixes, in this order,
`δ_local ≺ L_max ≺ β_∂, ε_N ≺ H_∂, r_∂`:

* `BoundaryRegisterOver_BSTD1 E V`: `δ_local < δ'(E)` (the producer's cone error), `L_max > 400V`
  (the fixed interior buffers only; longer cusp tests go to `H_∂`), `0 < β_∂ < β₁`, `ε_N > 0`,
  `H_∂ ≥ 1`, and `r_∂` with (BRegPhysical) `r_∂ < boundaryPhysicalBound (10⁶Δ) c₃ H_∂ ϑ`
  (`= min{1/(1000L), 10⁻⁴, 1/(100H_∂), ϑ²/(4·10⁸(12L+1000)), 10⁻⁶/(20(c₃+1))}`, `L = 10⁶Δ`,
  `ϑ = min_j ϑ_j`, `c₃` from `E`'s early layer), BCP02's product bound `r_∂ < β_∂³/(2000(1+H_∂))`,
  and `r_∂ ≤ cuspPhysicalScale_BCUSP1 β_∂ (10⁶Δ) H_∂ ϑ c₃` (BCUSP-1's form of both, with the
  first-exit buffer: the premise at `r_∂` gives B5's premise by monotonicity).
  `R.early = E` is fixed by the type index.
* `BoundaryLateRequests_BSTD1`: late requests, each reading only what precedes it (`L_max` reads
  `V, δ`; `β_∂, ε_N` read `V, δ, L_max`; `H_∂` reads also `β_∂, ε_N`; `r_∂` reads also `H_∂`).
* The values of lane BSTG G1/G3 (`bdryLmax_BSTD1 … bdryRd_BSTD1`: `L_max = max(1, 400V+1, Rq.L)`,
  `β_∂ = min(Rq.β, β₁/2)`, `ε_N = Rq.ε`, `H_∂ = max(1, Rq.H)`,
  `r_∂ = min(Rq.r, cuspPhysicalScale_BCUSP1 β_∂ (10⁶Δ) H_∂ ϑ c₃)`) and
  `BoundaryRegisterOver_BSTD1.ofRequests_BSTD1`, their register.
* consumer `exists_boundaryRegisterOver_BSTD1`: every early choice, every `V` and every admissible
  `δ_local` carry a register meeting any late request record.

No `1/r_∂` enters an early constant (`r_∂` is read last), and no `Δ > 100/β₂` together with
`β₂⁻¹ > 10⁶Δ` is added.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter

namespace DifferentialGeometry.Geometry.Collapse

/-- **The boundary register over the early choice `E` and the zero scale `V`** (D61-11 D2): the
cone error `δ_local < δ'(E)`, the interior buffer `L_max > 400V`, the cusp quality `β_∂ < β₁` and
norm error `ε_N`, the cusp test length `H_∂ ≥ 1` and the physical scale `r_∂` with (BRegPhysical)
at `L = 10⁶Δ`, BCP02's product bound, and below lane BCUSP-1's physical cusp scale at the register's
`β_∂, H_∂` (so the premise at `r_∂` gives B5's premise, first-exit included). -/
structure BoundaryRegisterOver_BSTD1 {Θ : BoundaryProducerThresholds_BSTD1}
    (E : BoundaryEarlyOver_BSTD1 Θ) (V : ℝ) where
  δlocal : ℝ
  δlocal_pos : 0 < δlocal
  δlocal_lt : δlocal < E.δ'
  Lmax : ℝ
  Lmax_pos : 0 < Lmax
  Lmax_gt : 400 * V < Lmax
  βd : ℝ
  βd_pos : 0 < βd
  βd_lt : βd < E.β 1
  εN : ℝ
  εN_pos : 0 < εN
  Hd : ℝ
  one_le_Hd : 1 ≤ Hd
  rd : ℝ
  rd_pos : 0 < rd
  rd_phys : rd < boundaryPhysicalBound (10 ^ 6 * E.Δ) E.c₃ Hd E.ϑ
  rd_prod : rd < βd ^ 3 / (2000 * (1 + Hd))
  rd_le_cusp : rd ≤ cuspPhysicalScale_BCUSP1 βd (10 ^ 6 * E.Δ) Hd E.ϑmin E.c₃

/-- **Late boundary requests** (D61-11 order): `Lmax` (lower) reads `V, δ_local`; `βd, εN`
(upper) read `V, δ_local, L_max`; `H` (lower) reads also `β_∂, ε_N`; `rd` (upper) reads also
`H_∂`. -/
structure BoundaryLateRequests_BSTD1 where
  Lmax : ℝ → ℝ → ℝ
  βd : ℝ → ℝ → ℝ → ℝ
  εN : ℝ → ℝ → ℝ → ℝ
  H : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
  rd : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
  βd_pos : ∀ V δ L, 0 < βd V δ L
  εN_pos : ∀ V δ L, 0 < εN V δ L
  rd_pos : ∀ V δ L b e H, 0 < rd V δ L b e H

/-- The trivial late requests. -/
def BoundaryLateRequests_BSTD1.trivial : BoundaryLateRequests_BSTD1 where
  Lmax _ _ := 0
  βd _ _ _ := 1
  εN _ _ _ := 1
  H _ _ _ _ _ := 0
  rd _ _ _ _ _ _ := 1
  βd_pos _ _ _ := one_pos
  εN_pos _ _ _ := one_pos
  rd_pos _ _ _ _ _ _ := one_pos

/-! ### The values of lane BSTG G1/G3 -/

section Values

variable (Rq : BoundaryLateRequests_BSTD1) {Θ : BoundaryProducerThresholds_BSTD1}
  (E : BoundaryEarlyOver_BSTD1 Θ) (V δ : ℝ)

/-- `L_max = max(1, 400V + 1, Rq.L)`. -/
def bdryLmax_BSTD1 : ℝ := max (max 1 (400 * V + 1)) (Rq.Lmax V δ)

/-- `β_∂ = min(Rq.β, β₁/2)` (BR24: below `β₁`). -/
def bdryβd_BSTD1 : ℝ := min (Rq.βd V δ (bdryLmax_BSTD1 Rq V δ)) (E.β 1 / 2)

/-- `ε_N = Rq.ε`. -/
def bdryεN_BSTD1 : ℝ := Rq.εN V δ (bdryLmax_BSTD1 Rq V δ)

/-- `H_∂ = max(1, Rq.H)`. -/
def bdryHd_BSTD1 : ℝ :=
  max 1 (Rq.H V δ (bdryLmax_BSTD1 Rq V δ) (bdryβd_BSTD1 Rq E V δ) (bdryεN_BSTD1 Rq V δ))

/-- `r_∂ = min(Rq.r, cuspPhysicalScale_BCUSP1 β_∂ (10⁶Δ) H_∂ ϑ c₃)` (lane BSTG G3's instance). -/
def bdryRd_BSTD1 : ℝ :=
  min (Rq.rd V δ (bdryLmax_BSTD1 Rq V δ) (bdryβd_BSTD1 Rq E V δ) (bdryεN_BSTD1 Rq V δ)
      (bdryHd_BSTD1 Rq E V δ))
    (cuspPhysicalScale_BCUSP1 (bdryβd_BSTD1 Rq E V δ) (10 ^ 6 * E.Δ) (bdryHd_BSTD1 Rq E V δ)
      E.ϑmin E.c₃)

theorem one_le_bdryLmax_BSTD1 : 1 ≤ bdryLmax_BSTD1 Rq V δ :=
  (le_max_left _ _).trans (le_max_left _ _)

theorem bdryLmax_gt_BSTD1 : 400 * V < bdryLmax_BSTD1 Rq V δ :=
  (lt_add_one _).trans_le ((le_max_right _ _).trans (le_max_left _ _))

theorem bdryLmax_ge_BSTD1 : Rq.Lmax V δ ≤ bdryLmax_BSTD1 Rq V δ :=
  le_max_right _ _

theorem bdryβd_pos_BSTD1 : 0 < bdryβd_BSTD1 Rq E V δ :=
  lt_min (Rq.βd_pos _ _ _) (half_pos E.β₁_pos)

theorem bdryβd_lt_BSTD1 : bdryβd_BSTD1 Rq E V δ < E.β 1 :=
  (min_le_right _ _).trans_lt (half_lt_self E.β₁_pos)

theorem one_le_bdryHd_BSTD1 : 1 ≤ bdryHd_BSTD1 Rq E V δ :=
  le_max_left _ _

theorem bdryRd_pos_BSTD1 : 0 < bdryRd_BSTD1 Rq E V δ := by
  have hL : 0 < 10 ^ 6 * E.Δ := by
    have := E.Δ_pos
    positivity
  exact lt_min (Rq.rd_pos _ _ _ _ _ _) (cuspPhysicalScale_pos_BCUSP1 (bdryβd_pos_BSTD1 Rq E V δ) hL
    (one_pos.trans_le (one_le_bdryHd_BSTD1 Rq E V δ)) E.ϑmin_pos E.c₃_nonneg)

/-- **(BRegPhysical) and BCP02's product bound for the value `r_∂`.** -/
theorem bdryRd_bounds_BSTD1 :
    bdryRd_BSTD1 Rq E V δ < boundaryPhysicalBound (10 ^ 6 * E.Δ) E.c₃ (bdryHd_BSTD1 Rq E V δ) E.ϑ ∧
      bdryRd_BSTD1 Rq E V δ <
        bdryβd_BSTD1 Rq E V δ ^ 3 / (2000 * (1 + bdryHd_BSTD1 Rq E V δ)) := by
  have hL : 0 < 10 ^ 6 * E.Δ := by
    have := E.Δ_pos
    positivity
  have hs := cuspPhysicalScale_pos_BCUSP1 (bdryβd_pos_BSTD1 Rq E V δ) hL
    (one_pos.trans_le (one_le_bdryHd_BSTD1 Rq E V δ)) E.ϑmin_pos E.c₃_nonneg
  have hle : bdryRd_BSTD1 Rq E V δ ≤ cuspPhysicalScale_BCUSP1 (bdryβd_BSTD1 Rq E V δ)
      (10 ^ 6 * E.Δ) (bdryHd_BSTD1 Rq E V δ) E.ϑmin E.c₃ := min_le_right _ _
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := two_mul_cuspPhysicalScale_le_BCUSP1 (bdryβd_BSTD1 Rq E V δ)
    (10 ^ 6 * E.Δ) (bdryHd_BSTD1 Rq E V δ) E.ϑmin E.c₃
  set c := cuspPhysicalScale_BCUSP1 (bdryβd_BSTD1 Rq E V δ) (10 ^ 6 * E.Δ)
    (bdryHd_BSTD1 Rq E V δ) E.ϑmin E.c₃
  have e4 : (1 : ℝ) / 10 ^ 4 = 1 / 10000 := by norm_num
  have e6 : (1 : ℝ) / 10 ^ 6 = 1 / 1000000 := by norm_num
  refine ⟨?_, by linarith⟩
  unfold boundaryPhysicalBound
  rw [e4, e6]
  exact lt_min (by linarith) (lt_min (by linarith) (lt_min (by linarith)
    (lt_min (by unfold BoundaryEarlyOver_BSTD1.ϑmin at h4; linarith) (by linarith))))

end Values

/-- **The register of the values of lane BSTG G1/G3** at the early choice `E`, the zero scale `V`,
the producer's cone error `δ < δ'(E)` and the late requests `Rq`. -/
def BoundaryRegisterOver_BSTD1.ofRequests_BSTD1 {Θ : BoundaryProducerThresholds_BSTD1}
    (E : BoundaryEarlyOver_BSTD1 Θ) (V δ : ℝ) (hδ : 0 < δ) (hδ' : δ < E.δ')
    (Rq : BoundaryLateRequests_BSTD1) : BoundaryRegisterOver_BSTD1 E V where
  δlocal := δ
  δlocal_pos := hδ
  δlocal_lt := hδ'
  Lmax := bdryLmax_BSTD1 Rq V δ
  Lmax_pos := one_pos.trans_le (one_le_bdryLmax_BSTD1 Rq V δ)
  Lmax_gt := bdryLmax_gt_BSTD1 Rq V δ
  βd := bdryβd_BSTD1 Rq E V δ
  βd_pos := bdryβd_pos_BSTD1 Rq E V δ
  βd_lt := bdryβd_lt_BSTD1 Rq E V δ
  εN := bdryεN_BSTD1 Rq V δ
  εN_pos := Rq.εN_pos _ _ _
  Hd := bdryHd_BSTD1 Rq E V δ
  one_le_Hd := one_le_bdryHd_BSTD1 Rq E V δ
  rd := bdryRd_BSTD1 Rq E V δ
  rd_pos := bdryRd_pos_BSTD1 Rq E V δ
  rd_phys := (bdryRd_bounds_BSTD1 Rq E V δ).1
  rd_prod := (bdryRd_bounds_BSTD1 Rq E V δ).2
  rd_le_cusp := min_le_right _ _

/-- **Consumer: the boundary register is inhabited and meets every late request** (D61-11 D2):
for every early choice `E`, every zero scale `V` and every cone error `0 < δ < δ'(E)`, there is a
register over `E` and `V` with `δ_local = δ` meeting the late requests `Rq` in the D61-11 order. -/
theorem exists_boundaryRegisterOver_BSTD1 {Θ : BoundaryProducerThresholds_BSTD1}
    (E : BoundaryEarlyOver_BSTD1 Θ) (V δ : ℝ) (hδ : 0 < δ) (hδ' : δ < E.δ')
    (Rq : BoundaryLateRequests_BSTD1) :
    ∃ R : BoundaryRegisterOver_BSTD1 E V, R.δlocal = δ ∧ Rq.Lmax V δ ≤ R.Lmax ∧
      R.βd ≤ Rq.βd V δ R.Lmax ∧ R.εN = Rq.εN V δ R.Lmax ∧
      Rq.H V δ R.Lmax R.βd R.εN ≤ R.Hd ∧ R.rd ≤ Rq.rd V δ R.Lmax R.βd R.εN R.Hd :=
  ⟨BoundaryRegisterOver_BSTD1.ofRequests_BSTD1 E V δ hδ hδ' Rq, rfl, bdryLmax_ge_BSTD1 Rq V δ,
    min_le_left _ _, rfl, le_max_right _ _, min_le_left _ _⟩

end DifferentialGeometry.Geometry.Collapse
