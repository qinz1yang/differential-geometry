import DifferentialGeometry.Geometry.Fibration.GraphModelBlocks
import DifferentialGeometry.Geometry.Fibration.ActualCloudPackets
import DifferentialGeometry.Geometry.Fibration.ActualGlobalDerivative
import DifferentialGeometry.Analysis.InnerProductSpace.BlockNormBounds
import DifferentialGeometry.Geometry.Fibration.ActualZeroMeetingClauses

/-!
# EGP06: the model graph `Φ_i : ℝ → Q₂` of an actual edge reference and its early bounds

Blueprint `master207B.tex`, EGP06 (`thm:fibration-actual-edge-graph`, B:5088–5139): "Use the own
block `(a, 1)`. For `j ≠ i` in the actual lists use `(λ_j(a) f(λ_j(a)/(s_jℓ_j)), s_j f(…))`,
`ℓ_j = Δ` (`J_e`), `10⁵Δ` (`J_s`). For the possible zero block use FC05's `F_{s₀}(λ₀(a))`. All
other blocks are zero; `Q₂` contains neither the weak-edge height block nor the scale or
two-stratum blocks." "Each model block has its first two derivatives bounded by `50(P_* + 1)`; the
zero radius satisfies `s₀ ≥ T₀/20 > 1`. Orthogonal square summation over at most `N† + 1` blocks
plus the identity gives `C†`."

* `blockGraph_bounds_KC3` (generic): a block graph `a ↦ (φ_t(a))_t` whose blocks vanish off a finite
  active set `s` and have `C²` bounds `B` on `s` has `‖D‖, ‖D²‖ ≤ √#s · B`.
* `blockLift_KC3`: the norm-preserving lift `(u, r) ↦ (planeAxis u, r)` of scalar blocks to the
  blocks `ℝ² × ℝ` of `𝓔⁰`.
* `egpModelComponent`, `egpModelGraph L Z i sgn c` (signs `sgn` and translations `c` per tag):
  own edge tag `i` ↦ `(a, 1)`; listed edge `j` (`egpEdgeList`) ↦ `graphPacketModelBlock Δ s_j`;
  listed slim `j` (`egpSlimList`) ↦ `sgpModelBlock (10⁵Δ) s_j`; zero `k` meeting `D_i` ↦
  `zeroModelBlock (R₀/ρ(i))`, all at `sgn_t a + c_t`; all other tags `0`.
* `egpGraphConst` (`C† = 1000(N† + 2)(P† + 1)`, `N† = egp02ListBound`, `P†` the maximum of the three
  profile constants) and `egp06_model`: smoothness, own block, values in `Q₂`,
  `‖DΦ_i‖, ‖D²Φ_i‖ ≤ C†` (kernel form `egp06_model_kernel`, count `egpModelListed_card_le`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis DifferentialGeometry.Analysis.Calculus GC.MetricGeometry

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Generic

variable {κ : Type*} [Fintype κ] {V : κ → Type*} [∀ t, NormedAddCommGroup (V t)]
  [∀ t, InnerProductSpace ℝ (V t)]

/-- The block graph `a ↦ (φ_t(a))_t`. -/
def blockGraph_KC3 (φ : ∀ t, ℝ → V t) (a : ℝ) : PiLp 2 V :=
  WithLp.toLp 2 fun t => φ t a

omit [Fintype κ] [∀ t, NormedAddCommGroup (V t)] [∀ t, InnerProductSpace ℝ (V t)] in
theorem blockGraph_apply_KC3 (φ : ∀ t, ℝ → V t) (a : ℝ) (t : κ) :
    blockGraph_KC3 φ a t = φ t a :=
  rfl

theorem contDiff_blockGraph_KC3 {φ : ∀ t, ℝ → V t} {n : WithTop ℕ∞}
    (hφ : ∀ t, ContDiff ℝ n (φ t)) : ContDiff ℝ n (blockGraph_KC3 φ) := by
  have h : ContDiff ℝ n (fun a => fun t => φ t a) := contDiff_pi.2 hφ
  exact (PiLp.continuousLinearEquiv 2 ℝ V).symm.contDiff.comp h

omit [Fintype κ] in
/-- The components of the derivative of a block graph are the derivatives of its blocks. -/
theorem fderiv_blockGraph_apply_KC3 [Finite κ] {φ : ∀ t, ℝ → V t} (hφ : ∀ t, Differentiable ℝ (φ t))
    (a x : ℝ) (t : κ) :
    fderiv ℝ (blockGraph_KC3 φ) a x t = fderiv ℝ (φ t) a x := by
  have := Fintype.ofFinite κ
  have hΦ : Differentiable ℝ (blockGraph_KC3 φ) := by
    have h : Differentiable ℝ (fun a => fun t => φ t a) := differentiable_pi.2 hφ
    exact (PiLp.continuousLinearEquiv 2 ℝ V).symm.differentiable.comp h
  let π : PiLp 2 V →L[ℝ] V t := PiLp.proj 2 V t
  have h := π.hasFDerivAt.comp a (hΦ a).hasFDerivAt
  have hfun : (π ∘ blockGraph_KC3 φ) = φ t := rfl
  rw [hfun] at h
  rw [h.fderiv]
  rfl

/-- **Orthogonal square summation over the active blocks.** If every block of `a ↦ (φ_t(a))_t`
outside a finite set `s` is the zero function and every block in `s` has first and second
derivatives at most `B`, the graph has first and second derivatives at most `√#s · B`. -/
theorem blockGraph_bounds_KC3 {φ : ∀ t, ℝ → V t} (hφ : ∀ t, ContDiff ℝ 2 (φ t)) (s : Finset κ)
    {B : ℝ} (hB : 0 ≤ B) (hz : ∀ t, t ∉ s → φ t = 0)
    (h1 : ∀ t, t ∈ s → ∀ a, ‖fderiv ℝ (φ t) a‖ ≤ B)
    (h2 : ∀ t, t ∈ s → ∀ a, ‖fderiv ℝ (fderiv ℝ (φ t)) a‖ ≤ B) (a : ℝ) :
    ‖fderiv ℝ (blockGraph_KC3 φ) a‖ ≤ Real.sqrt (s.card : ℝ) * B ∧
      ‖fderiv ℝ (fderiv ℝ (blockGraph_KC3 φ)) a‖ ≤ Real.sqrt (s.card : ℝ) * B := by
  have hφd : ∀ t, Differentiable ℝ (φ t) := fun t => (hφ t).differentiable (by norm_num)
  -- the components of the second derivative are those of the blocks
  have hcomp2 : ∀ (x y : ℝ) (t : κ),
      fderiv ℝ (fderiv ℝ (blockGraph_KC3 φ)) a x y t = fderiv ℝ (fderiv ℝ (φ t)) a x y := by
    intro x y t
    have hΦ : ContDiff ℝ 2 (blockGraph_KC3 φ) := contDiff_blockGraph_KC3 hφ
    have hDΦ : Differentiable ℝ (fderiv ℝ (blockGraph_KC3 φ)) :=
      ((contDiff_succ_iff_fderiv (n := 1)).mp hΦ).2.2.differentiable (by norm_num)
    let π : PiLp 2 V →L[ℝ] V t := PiLp.proj 2 V t
    let Cπ : (ℝ →L[ℝ] PiLp 2 V) →L[ℝ] (ℝ →L[ℝ] V t) :=
      ContinuousLinearMap.compL ℝ ℝ (PiLp 2 V) (V t) π
    have hfun : (Cπ ∘ fderiv ℝ (blockGraph_KC3 φ)) = fderiv ℝ (φ t) := by
      funext b
      refine ContinuousLinearMap.ext fun z => ?_
      exact fderiv_blockGraph_apply_KC3 hφd b z t
    have h := Cπ.hasFDerivAt.comp a (hDΦ a).hasFDerivAt
    rw [hfun] at h
    rw [h.fderiv]
    rfl
  have hzero1 : ∀ t, t ∉ s → ∀ b, fderiv ℝ (φ t) b = 0 := by
    intro t ht b
    rw [hz t ht]
    exact fderiv_const_apply 0
  have hzero2 : ∀ t, t ∉ s → ∀ b, fderiv ℝ (fderiv ℝ (φ t)) b = 0 := by
    intro t ht b
    have : fderiv ℝ (φ t) = fun _ => 0 := funext (hzero1 t ht)
    rw [this]
    exact fderiv_const_apply 0
  constructor
  · refine ContinuousLinearMap.norm_le_sqrt_active_blocks _ s hB (fun x t ht => ?_)
      (fun x t ht => ?_)
    · rw [fderiv_blockGraph_apply_KC3 hφd]
      exact ((fderiv ℝ (φ t) a).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (h1 t ht a) (norm_nonneg x))
    · rw [fderiv_blockGraph_apply_KC3 hφd, hzero1 t ht a]
      rfl
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
    have hBx : 0 ≤ B * ‖x‖ := mul_nonneg hB (norm_nonneg x)
    have h := ContinuousLinearMap.norm_le_sqrt_active_blocks
      (fderiv ℝ (fderiv ℝ (blockGraph_KC3 φ)) a x) s hBx (fun y t ht => ?_) (fun y t ht => ?_)
    · calc _ ≤ Real.sqrt (s.card : ℝ) * (B * ‖x‖) := h
        _ = Real.sqrt (s.card : ℝ) * B * ‖x‖ := by ring
    · rw [hcomp2]
      refine ((fderiv ℝ (fderiv ℝ (φ t)) a x).le_opNorm y).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg y)
      exact ((fderiv ℝ (fderiv ℝ (φ t)) a).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (h2 t ht a) (norm_nonneg x))
    · rw [hcomp2, hzero2 t ht a]
      rfl

end Generic

section Lift

/-- The lift `(u, r) ↦ (planeAxis u, r)` of a scalar block to a block `ℝ² × ℝ` of `𝓔⁰`. -/
def blockLift_KC3 : WithLp 2 (ℝ × ℝ) →L[ℝ] WithLp 2 (ℝ² × ℝ) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ² ℝ).symm : (ℝ² × ℝ) →L[ℝ] WithLp 2 (ℝ² × ℝ)).comp
    ((planeAxis.prodMap (ContinuousLinearMap.id ℝ ℝ)).comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ : WithLp 2 (ℝ × ℝ) →L[ℝ] ℝ × ℝ))

theorem blockLift_apply_KC3 (m : WithLp 2 (ℝ × ℝ)) :
    blockLift_KC3 m = WithLp.toLp 2 (planeAxis m.fst, m.snd) :=
  rfl

theorem norm_blockLift_apply_KC3 (m : WithLp 2 (ℝ × ℝ)) : ‖blockLift_KC3 m‖ = ‖m‖ := by
  rw [blockLift_apply_KC3, WithLp.prod_norm_eq_of_L2, WithLp.prod_norm_eq_of_L2]
  change Real.sqrt (‖planeAxis m.fst‖ ^ 2 + ‖m.snd‖ ^ 2) = _
  rw [norm_planeAxis]
  simp only [Real.norm_eq_abs]

theorem norm_blockLift_le_KC3 : ‖blockLift_KC3‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun m => by
    rw [norm_blockLift_apply_KC3, one_mul]

/-- Precomposition with an affine map `a ↦ σa + c`, `|σ| ≤ 1`, keeps `C²` bounds. -/
theorem affine_comp_bounds_KC3 {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {W : ℝ → G} (hW : ContDiff ℝ 2 W) {B σ c : ℝ} (hσ : |σ| ≤ 1) (hB : 0 ≤ B)
    (h1 : ∀ y, ‖fderiv ℝ W y‖ ≤ B) (h2 : ∀ y, ‖fderiv ℝ (fderiv ℝ W) y‖ ≤ B) (a : ℝ) :
    ‖fderiv ℝ (fun a => W (σ * a + c)) a‖ ≤ B ∧
      ‖fderiv ℝ (fderiv ℝ (fun a => W (σ * a + c))) a‖ ≤ B := by
  let A : ℝ →L[ℝ] ℝ := σ • ContinuousLinearMap.id ℝ ℝ
  have hA : ‖A‖ ≤ 1 := by
    change ‖σ • ContinuousLinearMap.id ℝ ℝ‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul hσ ContinuousLinearMap.norm_id_le (norm_nonneg _) zero_le_one).trans
      (by norm_num)
  let g : ℝ → ℝ := fun a => A a + c
  have hfun : (fun a => W (σ * a + c)) = W ∘ g := by
    funext a
    simp [g, A, smul_eq_mul]
  have hg : ∀ b, HasFDerivAt g A b := fun b => A.hasFDerivAt.add_const c
  have hDg : fderiv ℝ g = fun _ => A := funext fun b => (hg b).fderiv
  have hgd : Differentiable ℝ g := fun b => (hg b).differentiableAt
  have hWd : Differentiable ℝ W := hW.differentiable (by norm_num)
  have hDW : Differentiable ℝ (fderiv ℝ W) :=
    ((contDiff_succ_iff_fderiv (n := 1)).mp hW).2.2.differentiable (by norm_num)
  have hDDg : fderiv ℝ (fderiv ℝ g) a = 0 := by
    rw [hDg]
    exact fderiv_const_apply A
  rw [hfun]
  constructor
  · rw [fderiv_comp a (hWd (g a)) (hgd a), (hg a).fderiv]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (h1 _) hA (norm_nonneg _) hB).trans (by linarith))
  · have hDgd : DifferentiableAt ℝ (fderiv ℝ g) a := by
      rw [hDg]
      exact differentiableAt_const A
    refine (norm_second_fderiv_comp_le hWd hgd (hDW (g a)) hDgd).trans ?_
    rw [hDDg, norm_zero, mul_zero, add_zero, (hg a).fderiv]
    have hA2 : ‖A‖ ^ 2 ≤ 1 := by
      have := norm_nonneg A
      nlinarith
    exact (mul_le_mul (h2 _) hA2 (sq_nonneg _) hB).trans (by linarith)

/-- Postcomposition with a continuous linear map of norm at most one keeps `C²` bounds. -/
theorem clm_comp_bounds_KC3 {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] (L : G →L[ℝ] H) (hL : ‖L‖ ≤ 1) {h : ℝ → G}
    (hh : ContDiff ℝ 2 h) {B : ℝ} (h1 : ∀ y, ‖fderiv ℝ h y‖ ≤ B)
    (h2 : ∀ y, ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ B) (a : ℝ) :
    ‖fderiv ℝ (L ∘ h) a‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ (L ∘ h)) a‖ ≤ B := by
  have hhd : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hDh : Differentiable ℝ (fderiv ℝ h) :=
    ((contDiff_succ_iff_fderiv (n := 1)).mp hh).2.2.differentiable (by norm_num)
  have hDL : fderiv ℝ L = fun _ => L := funext fun y => L.fderiv
  have hDDL : fderiv ℝ (fderiv ℝ L) (h a) = 0 := by
    rw [hDL]
    exact fderiv_const_apply L
  constructor
  · rw [fderiv_comp a L.differentiableAt (hhd a), L.fderiv]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hL (h1 a) (norm_nonneg _) zero_le_one).trans (by linarith))
  · have hDLd : DifferentiableAt ℝ (fderiv ℝ L) (h a) := by
      rw [hDL]
      exact differentiableAt_const L
    refine (norm_second_fderiv_comp_le L.differentiable hhd hDLd (hDh a)).trans ?_
    rw [hDDL, norm_zero, zero_mul, zero_add, L.fderiv]
    exact (mul_le_mul hL (h2 a) (norm_nonneg _) zero_le_one).trans (by linarith)

/-- A lifted model block along an affine input keeps the `C²` bounds of the scalar block. -/
theorem lifted_affine_bounds_KC3 {W : ℝ → WithLp 2 (ℝ × ℝ)} (hW : ContDiff ℝ 2 W) {B σ c : ℝ}
    (hσ : |σ| ≤ 1) (hB : 0 ≤ B) (h1 : ∀ y, ‖fderiv ℝ W y‖ ≤ B)
    (h2 : ∀ y, ‖fderiv ℝ (fderiv ℝ W) y‖ ≤ B) (a : ℝ) :
    ‖fderiv ℝ (fun a => blockLift_KC3 (W (σ * a + c))) a‖ ≤ B ∧
      ‖fderiv ℝ (fderiv ℝ (fun a => blockLift_KC3 (W (σ * a + c)))) a‖ ≤ B := by
  have haff := affine_comp_bounds_KC3 hW (c := c) hσ hB h1 h2
  have hWc : ContDiff ℝ 2 (fun a => W (σ * a + c)) :=
    hW.comp ((contDiff_const.mul contDiff_id).add contDiff_const)
  exact clm_comp_bounds_KC3 blockLift_KC3 norm_blockLift_le_KC3 hWc (fun y => (haff y).1)
    (fun y => (haff y).2) a

end Lift

section Model

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

open Classical in
/-- **The blocks of EGP06's model graph** at the edge reference `i`, with signs `sgn` and
translations `c` per tag (`λ_t(a) = sgn_t a + c_t`): own edge tag `i` ↦ `(a, 1)`; listed edge
`j ≠ i` ↦ `graphPacketModelBlock Δ s_j (λ_t(a))`; listed slim `j` ↦ `sgpModelBlock (10⁵Δ) s_j
(λ_t(a))`; zero `k` meeting `D_i` ↦ `zeroModelBlock (R₀/ρ(i)) (λ_t(a))` (`s_j = ρ(j)/ρ(i)`, scalar
blocks on `planeAxis`); every other tag (circle, unlisted, scale, `E'`) ↦ `0`. -/
def egpModelComponent (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (i : X)
    (sgn c : CGPTag L Z → ℝ) : (t : CGPTag L Z) → ℝ → WithLp 2 (ℝ² × ℝ)
  | .inl _ => 0
  | .inr (.inl j) =>
      if j.1 ∈ egpSlimList L i then
        fun a => blockLift_KC3 (sgpModelBlock (10 ^ 5 * Δ) (ρ j.1 / ρ i)
          (sgn (.inr (.inl j)) * a + c (.inr (.inl j))))
      else 0
  | .inr (.inr (.inl j)) =>
      if j.1 = i then fun a => blockLift_KC3 (WithLp.toLp 2 (a, 1))
      else if j.1 ∈ egpEdgeList L i then
        fun a => blockLift_KC3 (graphPacketModelBlock Δ (ρ j.1 / ρ i)
          (sgn (.inr (.inr (.inl j))) * a + c (.inr (.inr (.inl j)))))
      else 0
  | .inr (.inr (.inr (.inl k))) =>
      if k.1 ∈ zeroMeetingList Z i (20 * Δ) then
        fun a => blockLift_KC3 (zeroModelBlock
          ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i)
          (sgn (.inr (.inr (.inr (.inl k)))) * a + c (.inr (.inr (.inr (.inl k))))))
      else 0
  | .inr (.inr (.inr (.inr _))) => 0

/-- **EGP06's model graph** `Φ_i : ℝ → 𝓔⁰`'s block space (values in `Q₂`). -/
def egpModelGraph (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (i : X)
    (sgn c : CGPTag L Z → ℝ) : ℝ → BlockSpace (fun _ : CGPTag L Z => ℝ²) :=
  blockGraph_KC3 (egpModelComponent L Z i sgn c)

/-- The listed tags of EGP06's model at `i` (where its block may be nonzero). -/
def egpModelListed (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (i : X) : CGPTag L Z → Prop
  | .inl _ => False
  | .inr (.inl j) => j.1 ∈ egpSlimList L i
  | .inr (.inr (.inl j)) => j.1 = i ∨ j.1 ∈ egpEdgeList L i
  | .inr (.inr (.inr (.inl k))) => k.1 ∈ zeroMeetingList Z i (20 * Δ)
  | .inr (.inr (.inr (.inr _))) => False

/-- EGP06's early profile constant `P†` (edge, slim and zero profiles). -/
def egpProfileConst : ℝ := max edgeProfileDerivativeBound (max sgpProfileBound zeroProfileBound)

/-- EGP06's early constant `C† = 1000(N† + 2)(P† + 1)`. -/
def egpGraphConst : ℝ := 1000 * (egp02ListBound + 2) * (egpProfileConst + 1)

theorem one_le_egpProfileConst : 1 ≤ egpProfileConst :=
  edgeProfileDerivativeBound_ge_one.trans (le_max_left _ _)

/-- The scalar own block `a ↦ (a, 1)` has derivative norm one and second derivative zero. -/
theorem own_block_bounds_KC3 :
    ContDiff ℝ ∞ (fun a : ℝ => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ × ℝ))) ∧
      ∀ a : ℝ, ‖fderiv ℝ (fun a : ℝ => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ × ℝ))) a‖ ≤ 1 ∧
        ‖fderiv ℝ (fderiv ℝ (fun a : ℝ => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ × ℝ)))) a‖ ≤
          1 := by
  obtain ⟨v₁, hv₁def⟩ : ∃ v : WithLp 2 (ℝ × ℝ), v = WithLp.toLp 2 ((1 : ℝ), (0 : ℝ)) := ⟨_, rfl⟩
  obtain ⟨v₀, hv₀def⟩ : ∃ v : WithLp 2 (ℝ × ℝ), v = WithLp.toLp 2 ((0 : ℝ), (1 : ℝ)) := ⟨_, rfl⟩
  have hfun : (fun a : ℝ => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ × ℝ))) =
      fun a => ContinuousLinearMap.toSpanSingleton ℝ v₁ a + v₀ := by
    funext a
    rw [ContinuousLinearMap.toSpanSingleton_apply, hv₁def, hv₀def, ← WithLp.toLp_smul,
      ← WithLp.toLp_add]
    congr 1
    simp
  have hv₁ : ‖v₁‖ = 1 := by
    rw [hv₁def, WithLp.prod_norm_eq_of_L2]
    simp
  have hd : ∀ a : ℝ, HasFDerivAt (fun a : ℝ => ContinuousLinearMap.toSpanSingleton ℝ v₁ a + v₀)
      (ContinuousLinearMap.toSpanSingleton ℝ v₁) a :=
    fun a => (ContinuousLinearMap.toSpanSingleton ℝ v₁).hasFDerivAt.add_const v₀
  have hD : fderiv ℝ (fun a : ℝ => ContinuousLinearMap.toSpanSingleton ℝ v₁ a + v₀) =
      fun _ => ContinuousLinearMap.toSpanSingleton ℝ v₁ :=
    funext fun a => (hd a).fderiv
  rw [hfun]
  refine ⟨(ContinuousLinearMap.toSpanSingleton ℝ v₁).contDiff.add contDiff_const,
    fun a => ⟨?_, ?_⟩⟩
  · rw [hD, ContinuousLinearMap.norm_toSpanSingleton, hv₁]
  · rw [hD, fderiv_const_apply, norm_zero]
    exact zero_le_one

open Classical in
/-- Every unlisted block of the model is the zero function. -/
theorem egpModelComponent_eq_zero
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (i : X)
    (sgn c : CGPTag L Z → ℝ) (t : CGPTag L Z) (ht : ¬ egpModelListed L Z i t) :
    egpModelComponent L Z i sgn c t = 0 := by
  rcases t with j | j | j | k | q
  · rfl
  · simp only [egpModelListed] at ht
    simp only [egpModelComponent, ht, ite_false]
  · simp only [egpModelListed, not_or] at ht
    simp only [egpModelComponent, ht.1, ht.2, ite_false]
  · simp only [egpModelListed] at ht
    simp only [egpModelComponent, ht, ite_false]
  · rfl

open Classical in
/-- Every block of the model is smooth. -/
theorem contDiff_egpModelComponent
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (i : X)
    (sgn c : CGPTag L Z → ℝ) (t : CGPTag L Z) :
    ContDiff ℝ ∞ (egpModelComponent L Z i sgn c t) := by
  have haff : ∀ (σ c' : ℝ), ContDiff ℝ ∞ (fun a : ℝ => σ * a + c') :=
    fun σ c' => (contDiff_const.mul contDiff_id).add contDiff_const
  rcases t with j | j | j | k | q
  · exact contDiff_const
  · simp only [egpModelComponent]
    split_ifs
    · exact blockLift_KC3.contDiff.comp ((contDiff_sgpModelBlock _ _).comp (haff _ _))
    · exact contDiff_const
  · simp only [egpModelComponent]
    split_ifs
    · exact blockLift_KC3.contDiff.comp own_block_bounds_KC3.1
    · exact blockLift_KC3.contDiff.comp ((contDiff_graphPacketModelBlock _ _).comp (haff _ _))
    · exact contDiff_const
  · simp only [egpModelComponent]
    split_ifs
    · exact blockLift_KC3.contDiff.comp ((contDiff_zeroModelBlock _).comp (haff _ _))
    · exact contDiff_const
  · exact contDiff_const

theorem contDiff_egpModelGraph
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (i : X)
    (sgn c : CGPTag L Z → ℝ) : ContDiff ℝ ∞ (egpModelGraph L Z i sgn c) :=
  contDiff_blockGraph_KC3 (contDiff_egpModelComponent L Z i sgn c)

/-- The own block of the model is `(a, 1)`. -/
theorem egpModelGraph_own
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (i : X)
    (sgn c : CGPTag L Z → ℝ) (j : L.edge.finite_centres.toFinset) (hj : j.1 = i) (a : ℝ) :
    egpModelGraph L Z i sgn c a (.inr (.inr (.inl j))) = WithLp.toLp 2 (planeAxis a, 1) := by
  change egpModelComponent L Z i sgn c (.inr (.inr (.inl j))) a = _
  simp only [egpModelComponent, hj, ite_true]
  rfl

open Classical in
/-- The model takes values in `Q₂` (no circle, scale or `E'` block). -/
theorem blockRestrict_egpModelGraph
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (i : X)
    (sgn c : CGPTag L Z → ℝ) (a : ℝ) :
    blockRestrict (cgpQ2Tags L Z) (egpModelGraph L Z i sgn c a) = egpModelGraph L Z i sgn c a := by
  refine PiLp.ext fun t => ?_
  rw [blockRestrict_apply]
  split_ifs with ht
  · rfl
  · have h0 : egpModelComponent L Z i sgn c t = 0 := by
      apply egpModelComponent_eq_zero
      rcases t with j | j | j | k | q
      · exact fun h => h
      · exact (ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)).elim
      · exact (ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)).elim
      · exact (ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)).elim
      · exact fun h => h
    change 0 = egpModelComponent L Z i sgn c t a
    rw [h0]
    rfl

open Classical in
/-- **EGP06's model bounds (kernel form).** With `Δ ≥ 1`, signs `|sgn_t| ≤ 1`, ratios
`s_j ≥ 99/100` for the listed edge and slim charts, zero ratios `R₀/ρ(i) ≥ 1` for the zero
supports meeting `D_i`, and at most `N† + 2` listed tags, the model graph has first and second
derivatives at most `C† = 1000(N† + 2)(P† + 1)`. -/
theorem egp06_model_kernel
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) {i : X} (hi : i ∈ L.edge.centres)
    (sgn c : CGPTag L Z → ℝ) (hΔ : 1 ≤ Δ) (hsgn : ∀ t, |sgn t| ≤ 1)
    (hS : ∀ j ∈ egpSlimList L i, 99 / 100 ≤ ρ j / ρ i)
    (hE : ∀ j ∈ egpEdgeList L i, 99 / 100 ≤ ρ j / ρ i)
    (hZ : ∀ k (hk : k ∈ Z.centres), k ∈ zeroMeetingList Z i (20 * Δ) →
      1 ≤ (Z.zero k hk).radius / ρ i)
    (hcount : ((Finset.univ.filter (egpModelListed L Z i)).card : ℝ) ≤ egp02ListBound + 2)
    (a : ℝ) :
    ‖fderiv ℝ (egpModelGraph L Z i sgn c) a‖ ≤ egpGraphConst ∧
      ‖fderiv ℝ (fderiv ℝ (egpModelGraph L Z i sgn c)) a‖ ≤ egpGraphConst := by
  have hP := one_le_egpProfileConst
  have hPe : edgeProfileDerivativeBound ≤ egpProfileConst := le_max_left _ _
  have hPs : sgpProfileBound ≤ egpProfileConst := (le_max_left _ _).trans (le_max_right _ _)
  have hPz : zeroProfileBound ≤ egpProfileConst := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = 50 * (egpProfileConst + 1) := ⟨_, rfl⟩
  have hB : 0 ≤ B := by rw [hBdef]; linarith
  have hB1 : 1 ≤ B := by rw [hBdef]; linarith
  set S := Finset.univ.filter (egpModelListed L Z i) with hSdef
  have hblock : ∀ t, t ∈ S → ∀ a, ‖fderiv ℝ (egpModelComponent L Z i sgn c t) a‖ ≤ B ∧
      ‖fderiv ℝ (fderiv ℝ (egpModelComponent L Z i sgn c t)) a‖ ≤ B := by
    intro t ht a
    have hl := (Finset.mem_filter.mp ht).2
    rcases t with j | j | j | k | q
    · exact hl.elim
    · have hl' : j.1 ∈ egpSlimList L i := hl
      have hℓ : 1 ≤ 10 ^ 5 * Δ := by nlinarith
      have hW (y : ℝ) := sgpModelBlock_derivative_bounds hℓ (hS j.1 hl') y
      simp only [egpModelComponent, hl', ite_true]
      exact lifted_affine_bounds_KC3 ((contDiff_sgpModelBlock _ _).of_le (by simp)) (hsgn _) hB
        (fun y => (hW y).1.trans (by rw [hBdef]; linarith))
        (fun y => (hW y).2.trans (by rw [hBdef]; linarith)) a
    · by_cases hji : j.1 = i
      · simp only [egpModelComponent, hji, ite_true]
        have h := clm_comp_bounds_KC3 blockLift_KC3 norm_blockLift_le_KC3
          (own_block_bounds_KC3.1.of_le (by simp)) (fun y => (own_block_bounds_KC3.2 y).1)
          (fun y => (own_block_bounds_KC3.2 y).2) a
        exact ⟨h.1.trans hB1, h.2.trans hB1⟩
      · have hl' : j.1 ∈ egpEdgeList L i := hl.resolve_left hji
        have hW (y : ℝ) := graphPacketModelBlock_derivative_bounds hΔ (hE j.1 hl') y
        simp only [egpModelComponent, hji, hl', ite_true, ite_false]
        exact lifted_affine_bounds_KC3 ((contDiff_graphPacketModelBlock _ _).of_le (by simp))
          (hsgn _) hB (fun y => (hW y).1.trans (by rw [hBdef]; linarith))
          (fun y => (hW y).2.trans (by rw [hBdef]; linarith)) a
    · have hl' : k.1 ∈ zeroMeetingList Z i (20 * Δ) := hl
      have hW (y : ℝ) := zeroModelBlock_derivative_bounds
        (hZ k.1 ((Set.Finite.mem_toFinset _).mp k.2) hl') y
      simp only [egpModelComponent, hl', ite_true]
      exact lifted_affine_bounds_KC3 ((contDiff_zeroModelBlock _).of_le (by simp)) (hsgn _) hB
        (fun y => (hW y).1.trans (by rw [hBdef]; linarith))
        (fun y => (hW y).2.trans (by rw [hBdef]; linarith)) a
    · exact hl.elim
  have hz : ∀ t, t ∉ S → egpModelComponent L Z i sgn c t = 0 := fun t ht =>
    egpModelComponent_eq_zero L Z i sgn c t fun hl =>
      ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩)
  have hmain := blockGraph_bounds_KC3
    (fun t => (contDiff_egpModelComponent L Z i sgn c t).of_le (by simp)) S hB hz
    (fun t ht a => (hblock t ht a).1) (fun t ht a => (hblock t ht a).2) a
  -- the count
  have hown : (.inr (.inr (.inl ⟨i, (Set.Finite.mem_toFinset _).mpr hi⟩)) : CGPTag L Z) ∈ S :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩
  have hS1 : (1 : ℝ) ≤ S.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨_, hown⟩
  have hsqrt : Real.sqrt (S.card : ℝ) ≤ S.card := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hfin : Real.sqrt (S.card : ℝ) * B ≤ egpGraphConst := by
    have h1 : Real.sqrt (S.card : ℝ) * B ≤ (egp02ListBound + 2) * B :=
      mul_le_mul_of_nonneg_right (hsqrt.trans hcount) hB
    have h2 : (egp02ListBound + 2) * B ≤ egpGraphConst := by
      rw [hBdef, egpGraphConst]
      have hN : 0 ≤ egp02ListBound + 2 := by linarith
      nlinarith
    linarith
  exact ⟨hmain.1.trans hfin, hmain.2.trans hfin⟩

end Model

section Family

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricN_KC3
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsR`, as a named local instance. -/
local instance instChartedN_KC3
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricC_KC3
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

open Classical in
/-- EGP06's listed tags at an edge reference: at most `N† + 2` (EGP02's count, the own tag, and at
most one zero support meeting `D_i`). -/
theorem egpModelListed_card_le
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (he : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) (i : X) :
    ((Finset.univ.filter (egpModelListed P.toLocalChartFamily P.zero i)).card : ℝ) ≤
      egp02ListBound + 2 := by
  have hΔ0 : 0 < Δ := by linarith
  let L := P.toLocalChartFamily
  -- the three kinds of listed tags
  let SS := Finset.univ.filter fun j : L.slim.finite_centres.toFinset => j.1 ∈ egpSlimList L i
  let SE := Finset.univ.filter fun j : L.edge.finite_centres.toFinset =>
    j.1 = i ∨ j.1 ∈ egpEdgeList L i
  let SZ := Finset.univ.filter fun k : P.zero.finite_centres.toFinset =>
    k.1 ∈ zeroMeetingList P.zero i (20 * Δ)
  let eS : L.slim.finite_centres.toFinset ↪ CGPTag L P.zero :=
    ⟨fun j => .inr (.inl j), fun _ _ h => by simpa using h⟩
  let eE : L.edge.finite_centres.toFinset ↪ CGPTag L P.zero :=
    ⟨fun j => .inr (.inr (.inl j)), fun _ _ h => by simpa using h⟩
  let eZ : P.zero.finite_centres.toFinset ↪ CGPTag L P.zero :=
    ⟨fun k => .inr (.inr (.inr (.inl k))), fun _ _ h => by simpa using h⟩
  have hsub : Finset.univ.filter (egpModelListed L P.zero i) ⊆
      (SS.map eS ∪ SE.map eE) ∪ SZ.map eZ := by
    intro t ht
    have hl := (Finset.mem_filter.mp ht).2
    rcases t with j | j | j | k | q
    · exact hl.elim
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_map_of_mem eS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩)))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_map_of_mem eE (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩)))
    · exact Finset.mem_union_right _
        (Finset.mem_map_of_mem eZ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩))
    · exact hl.elim
  have hcard := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  rw [Finset.card_map, Finset.card_map, Finset.card_map] at hcard
  -- slim
  have hSS : SS.card ≤ (egpSlimList L i).ncard := by
    have h : SS.card ≤ {y | y ∈ L.slim.centres ∧ y ∈ egpSlimList L i}.ncard := by
      rw [← Set.ncard_coe_finset, Finset.coe_filter]
      simp only [Finset.mem_univ, true_and]
      exact ncard_subtype_le_KA2 L.slim.finite_centres
        (p := fun y => y ∈ egpSlimList L i) (q := fun y => y ∈ egpSlimList L i) fun _ _ hy => hy
    refine h.trans (Set.ncard_le_ncard (fun y hy => hy.2) ?_)
    exact L.slim.finite_centres.subset fun y hy => hy.1
  -- edge
  have hfinE : (egpEdgeList L i).Finite := L.edge.finite_centres.subset fun y hy => hy.1
  have hSE : SE.card ≤ (egpEdgeList L i).ncard + 1 := by
    have h : SE.card ≤ {y | y ∈ L.edge.centres ∧ (y = i ∨ y ∈ egpEdgeList L i)}.ncard := by
      rw [← Set.ncard_coe_finset, Finset.coe_filter]
      simp only [Finset.mem_univ, true_and]
      exact ncard_subtype_le_KA2 L.edge.finite_centres
        (p := fun y => y = i ∨ y ∈ egpEdgeList L i) (q := fun y => y = i ∨ y ∈ egpEdgeList L i)
        fun _ _ hy => hy
    refine h.trans ((Set.ncard_le_ncard (t := insert i (egpEdgeList L i))
      (fun y hy => ?_) (hfinE.insert i)).trans (Set.ncard_insert_le _ _))
    rcases hy.2 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  -- zero
  have hT0 : 0 < T := by have : (0 : ℝ) < 1600 * (1000000 * Δ) := by positivity
                         linarith
  have hc : ((Real.toNNReal Λ : NNReal) : ℝ) = Λ := Real.coe_toNNReal _ hΛ
  have hsmall : 2 * (20 * Δ / T) + 2 * (20 * Δ * ((Real.toNNReal Λ : NNReal) : ℝ)) ≤ 1 / 40 := by
    rw [hc]
    have h1 : 20 * Δ / T ≤ 1 / 80000 := by
      rw [div_le_iff₀ hT0]
      linarith
    have h2 : 20 * Δ * Λ ≤ 1 / 5000000 := by nlinarith
    linarith
  have hZ1 := ncard_zeroMeetingList_le_one P.zero P.lipschitz_scale he hT0 i
    (by positivity : (0 : ℝ) < 20 * Δ) hsmall
  have hSZ : SZ.card ≤ (zeroMeetingList P.zero i (20 * Δ)).ncard := by
    have h : SZ.card ≤ {y | y ∈ P.zero.centres ∧ y ∈ zeroMeetingList P.zero i (20 * Δ)}.ncard := by
      rw [← Set.ncard_coe_finset, Finset.coe_filter]
      simp only [Finset.mem_univ, true_and]
      exact ncard_subtype_le_KA2 P.zero.finite_centres
        (p := fun y => y ∈ zeroMeetingList P.zero i (20 * Δ))
        (q := fun y => y ∈ zeroMeetingList P.zero i (20 * Δ)) fun _ _ hy => hy
    refine h.trans (Set.ncard_le_ncard (fun y hy => hy.2) ?_)
    exact P.zero.finite_centres.subset fun y hy => hy.1
  have hlist := egp02_list_count L hΛ hΔ0 hLΛ i
  have hcardR : ((Finset.univ.filter (egpModelListed L P.zero i)).card : ℝ) ≤
      SS.card + SE.card + SZ.card := by exact_mod_cast hcard
  have hSSR : (SS.card : ℝ) ≤ (egpSlimList L i).ncard := by exact_mod_cast hSS
  have hSER : (SE.card : ℝ) ≤ (egpEdgeList L i).ncard + 1 := by exact_mod_cast hSE
  have hSZR : (SZ.card : ℝ) ≤ 1 := by exact_mod_cast hSZ.trans hZ1
  linarith

open Classical in
/-- **EGP06's model on the actual family.** At an edge centre `i`, for signs `|sgn_t| ≤ 1` and any
translations, the model graph `Φ_i` is smooth, has own block `(a, 1)`, takes values in `Q₂`, and has
`‖DΦ_i‖, ‖D²Φ_i‖ ≤ C†` (early: `C†` depends on no parameter). -/
theorem egp06_model
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hμ : μ ≤ 1 / 100)
    (hτ : τ ≤ 1 / 100) (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) {i : X}
    (hi : i ∈ P.edge.centres) (sgn c : CGPTag P.toLocalChartFamily P.zero → ℝ)
    (hsgn : ∀ t, |sgn t| ≤ 1) :
    ContDiff ℝ ∞ (egpModelGraph P.toLocalChartFamily P.zero i sgn c) ∧
      (∀ (j : P.edge.finite_centres.toFinset), j.1 = i → ∀ a,
        egpModelGraph P.toLocalChartFamily P.zero i sgn c a (.inr (.inr (.inl j))) =
          WithLp.toLp 2 (planeAxis a, 1)) ∧
      (∀ a, blockRestrict (cgpQ2Tags P.toLocalChartFamily P.zero)
        (egpModelGraph P.toLocalChartFamily P.zero i sgn c a) =
          egpModelGraph P.toLocalChartFamily P.zero i sgn c a) ∧
      ∀ a, ‖fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero i sgn c) a‖ ≤ egpGraphConst ∧
        ‖fderiv ℝ (fderiv ℝ (egpModelGraph P.toLocalChartFamily P.zero i sgn c)) a‖ ≤
          egpGraphConst := by
  have hΔ0 : 0 < Δ := by linarith
  have hri := hρ i
  have hρL : LipschitzWith (Real.toNNReal Λ) ρ := P.lipschitz_scale
  have hc : ((Real.toNNReal Λ : NNReal) : ℝ) = Λ := Real.coe_toNNReal _ hΛ
  have hΔΛ0 : 0 ≤ Δ * Λ := mul_nonneg hΔ0.le hΛ
  have hΔΛ : 100 * Δ * Λ ≤ 1 / 100 := by nlinarith
  have hLΛ' : 1000000 * Δ * ((Real.toNNReal Λ : NNReal) : ℝ) < 1 / 100000 := by rwa [hc]
  -- slim ratios
  have hS : ∀ j ∈ egpSlimList P.toLocalChartFamily i, 99 / 100 ≤ ρ j / ρ i := by
    intro j hj
    obtain ⟨hjc, y₀, hy1, hy2⟩ := hj
    have hsl := fc18_slim_row P.toLocalChartFamily hΔ0 hjc
    have hm : (closedBall j ((910000 * Δ) * ρ j) ∩ ball i ((20 * Δ) * ρ i)).Nonempty :=
      ⟨y₀, hsl.1 hy1, hy2⟩
    have hΛ1 : 250 * (Λ * (20 * Δ)) ≤ 1 := by
      have e : Λ * (20 * Δ) = 1 / 50000 * (1000000 * Δ * Λ) := by ring
      linarith
    have hΛ2 : 250 * (Λ * (910000 * Δ)) ≤ 1 := by
      have e : Λ * (910000 * Δ) = 91 / 100 * (1000000 * Δ * Λ) := by ring
      linarith
    exact (support_meeting_sharp_bounds hρL hri (hρ j) (a := 20 * Δ) (c := 910000 * Δ)
      (by positivity) (by positivity) (by rw [hc]; exact hΛ1) (by rw [hc]; exact hΛ2) hm).1.le
  -- edge ratios
  have hE : ∀ j ∈ egpEdgeList P.toLocalChartFamily i, 99 / 100 ≤ ρ j / ρ i := by
    intro j hj
    obtain ⟨hjc, y₀, hy1, hy2⟩ := hj
    have h14 := (fc18_edge_rowE P.toLocalChartFamilyE hΛ hΔ0 hμ hτ hΔΛ hjc).1 hy1
    have hm : (closedBall j (15 * Δ * ρ j) ∩ ball i (20 * Δ * ρ i)).Nonempty := by
      refine ⟨y₀, closedBall_subset_closedBall ?_ h14, hy2⟩
      nlinarith [hρ j]
    exact (edge_comparison_list_edge_bounds hρL hri (hρ j) hΔ hLΛ' hm).1.le
  -- zero ratios
  have hZ : ∀ k (hk : k ∈ P.zero.centres), k ∈ zeroMeetingList P.zero i (20 * Δ) →
      1 ≤ (P.zero.zero k hk).radius / ρ i := by
    intro k hk hmeet
    obtain ⟨hk', hm⟩ := hmeet
    have hT0 : 0 < T := by have : (0 : ℝ) < 1600 * (1000000 * Δ) := by positivity
                           linarith
    have hsmall : 2 * (20 * Δ / T) + 2 * (20 * Δ * Λ) ≤ 1 / 40 := by
      have h1 : 20 * Δ / T ≤ 1 / 80000 := by
        rw [div_le_iff₀ hT0]
        linarith
      have h2 : 20 * Δ * Λ ≤ 1 / 5000000 := by nlinarith
      linarith
    obtain ⟨-, hcl⟩ := zero_meeting_clauses_ZERO P hΛ he hT0 i (by positivity) hsmall
    have h := ((hcl k hk' hm).1 i (mem_ball_self (by positivity))).2.2.2.2
    have hT20 : 1 ≤ T / 20 := by
      rw [le_div_iff₀ (by norm_num)]
      have : (20 : ℝ) ≤ 1600 * (1000000 * Δ) := by nlinarith
      linarith
    exact hT20.trans h
  refine ⟨contDiff_egpModelGraph _ _ i sgn c, fun j hj a => egpModelGraph_own _ _ i sgn c j hj a,
    fun a => blockRestrict_egpModelGraph _ _ i sgn c a, fun a => ?_⟩
  exact egp06_model_kernel P.toLocalChartFamily P.zero hi sgn c hΔ hsgn hS hE hZ
    (egpModelListed_card_le P hΛ hΔ hLΛ he hT i) a

end Family

end DifferentialGeometry.Geometry.Collapse
