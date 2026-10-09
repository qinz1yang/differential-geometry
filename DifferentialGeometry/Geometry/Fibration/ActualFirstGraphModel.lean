import DifferentialGeometry.Geometry.Fibration.FirstGraphKernel
import DifferentialGeometry.Geometry.Fibration.ActualEdgeGraphModel
import DifferentialGeometry.Geometry.Fibration.ActualAdjustmentChoice
import DifferentialGeometry.Analysis.Calculus.JointCutoffNetwork

/-!
# TCP05: the model first graph `Φ_i : ℝ² → H` of a circle reference and its early bounds

Blueprint `master207B.tex`, TCP05 (`thm:fibration-actual-first-graph`, B:5518–5598): "Use the own
block `(a, 1)`, the constant scale coordinate `1`, and for the other circle and slim blocks
substitute `λ_j(a)` into their original scaled cutoff formulas. Use `F_{s₀}(λ₀(a))` for the
possible zero block. Unlisted model blocks are zero." For the edge blocks "use the WHOLE joint
network of FC10 with affine inputs `u_j(a) = λ_j(a)/s_j`, `v(a) = λ_t(a)`".

* `tcpEdgeRows`, `norm_tcpEdgeRows_le`: the linear part of the affine network input
  (`‖M‖ ≤ √#(Option ι) · r` for rows of norm `≤ r`).
* `tcpNetwork Δ s`: FC10's joint network with the actual profiles of `𝓔⁰`
  (`f = edgeCoordinateProfile`, `g = edgeHeightProfile`, `h = cgpEdgeH`, `χ = edgeSumProfile`),
  `tcpNetwork_bounds`.
* `tcpModelComponent L Z i S Se Ac cc A1 c1 Bτ cτ`, `tcpModelGraph` (= `Φ_i`): own circle tag
  `↦ (a, 1)`; listed circle `j ≠ i` (`∈ S`) `↦ scaledCutoffBlock s_j ψ (Ac_j a + cc_j)` (`ψ` the
  circle bump); listed slim `↦ sgpModelBlock (10⁵Δ) s_j (A1_j a + c1_j)`; listed zero
  `↦ zeroModelBlock (R₀/ρ(i)) (A1_k a + c1_k)` (scalar blocks lifted by `blockLift_KC3`); edge
  `j ∈ Se` and `E'` `↦` the corresponding block of `tcpNetwork Δ s (U a)` with
  `U(a)_j = A1_j a + c1_j`, `U(a)_none = Bτ a + cτ`; scale `↦ (0, 1)`; every other tag `↦ 0`.
* `contDiff_tcpModelGraph`, `tcpModelGraph_own`, and `tcp05_model_bounds`:
  `‖DΦ_i‖, ‖D²Φ_i‖ ≤ tcpGraphConst = (N + 3) · tcpBlockBound` with `N = fc07ActiveBound`, an
  early constant (profiles and FC07's count only).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis DifferentialGeometry.Analysis.Calculus GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- The scalar action on a block `ℓ²(ℝ² × ℝ)` is continuous (given directly: the instance search
for it times out). -/
local instance instContinuousSMulPlaneBlock_KA6 : ContinuousSMul ℝ (WithLp 2 (ℝ² × ℝ)) :=
  IsBoundedSMul.continuousSMul

section Network

variable {ι : Type*} [Fintype ι]

/-- The linear part `a ↦ (A_o a)_o` of the affine network input. -/
def tcpEdgeRows (A : Option ι → ℝ² →L[ℝ] ℝ) : ℝ² →L[ℝ] EuclideanSpace ℝ (Option ι) :=
  (EuclideanSpace.equiv (Option ι) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi A)

omit [Fintype ι] in
theorem tcpEdgeRows_apply (A : Option ι → ℝ² →L[ℝ] ℝ) (a : ℝ²) (o : Option ι) :
    tcpEdgeRows A a o = A o a :=
  rfl

/-- Rows of norm at most `r` give `‖M‖ ≤ √#(Option ι) · r`. -/
theorem norm_tcpEdgeRows_le (A : Option ι → ℝ² →L[ℝ] ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hA : ∀ o, ‖A o‖ ≤ r) :
    ‖tcpEdgeRows A‖ ≤ Real.sqrt (Fintype.card (Option ι) : ℝ) * r := by
  have h := ContinuousLinearMap.norm_le_sqrt_sum_block_bounds (tcpEdgeRows A) (fun _ => r)
    (fun x o => by
      rw [tcpEdgeRows_apply]
      exact (A o).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hA o) (norm_nonneg x)))
  refine h.trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.sqrt_mul (by positivity),
    Real.sqrt_sq hr]

/-- **FC10's joint network of the first graph**, with the actual profiles of `𝓔⁰`. -/
def tcpNetwork (Δ : ℝ) (s : ι → ℝ) :
    EuclideanSpace ℝ (Option ι) → PiLp 2 (fun _ : Option ι => WithLp 2 (ℝ × ℝ)) :=
  jointCutoffNetwork Δ s edgeCoordinateProfile edgeHeightProfile cgpEdgeH edgeSumProfile
    (fun j => EuclideanSpace.proj (some j)) (EuclideanSpace.proj none)

theorem contDiff_tcpNetwork (Δ : ℝ) (s : ι → ℝ) : ContDiff ℝ ∞ (tcpNetwork Δ s) :=
  contDiff_jointCutoffNetwork edgeProfiles_contDiff.1 edgeProfiles_contDiff.2.1 cgpEdgeH_contDiff
    edgeProfiles_contDiff.2.2.2 Δ s _ _

/-- The closed support of `cgpEdgeH` lies in `[1/5, 9]`. -/
theorem tsupport_cgpEdgeH_subset_KA6 : tsupport cgpEdgeH ⊆ Icc (1 / 5) 9 := by
  refine closure_minimal (fun x hx => ?_) isClosed_Icc
  by_contra hout
  rcases not_and_or.mp hout with h | h
  · exact hx (cgpEdgeH_eq_zero_of_le (le_of_lt (lt_of_not_ge h)))
  · exact hx (cgpEdgeH_eq_zero_of_ge (le_of_lt (lt_of_not_ge h)))

theorem norm_euclideanProj_le_KA6 {κ : Type*} [Fintype κ] (o : κ) :
    ‖(EuclideanSpace.proj o : EuclideanSpace ℝ κ →L[ℝ] ℝ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]
    exact PiLp.norm_apply_le x o

/-- FC10's bounds for `tcpNetwork` (`N = #ι + 1`, `K = 10N²P³`, `P = tcpProfileBound`). -/
theorem tcpNetwork_bounds {Δ : ℝ} (hΔ : 1 ≤ Δ) (s : ι → ℝ) (hs : ∀ j, s j ∈ Icc (1 / 2) 2)
    (y : EuclideanSpace ℝ (Option ι)) :
    ‖fderiv ℝ (tcpNetwork Δ s) y‖ ≤ Real.sqrt ((Fintype.card ι : ℝ) + 1) *
        (2 + 20 * (10 * ((Fintype.card ι : ℝ) + 1) ^ 2 * tcpProfileBound ^ 3)) ∧
      ‖fderiv ℝ (fderiv ℝ (tcpNetwork Δ s)) y‖ ≤ 24 * Real.sqrt ((Fintype.card ι : ℝ) + 1) *
        (10 * ((Fintype.card ι : ℝ) + 1) ^ 2 * tcpProfileBound ^ 3) / Δ := by
  obtain ⟨hP, -, -, -, hprof⟩ := tcpProfileBound_spec
  have hf := hprof edgeCoordinateProfile (by simp)
  have hg := hprof edgeHeightProfile (by simp)
  have hh := hprof cgpEdgeH (by simp)
  have hc := hprof edgeSumProfile (by simp)
  have hb := jointCutoffNetwork_bounds (edgeProfiles_contDiff.1.of_le (by simp))
    (edgeProfiles_contDiff.2.1.of_le (by simp)) (cgpEdgeH_contDiff.of_le (by simp))
    (edgeProfiles_contDiff.2.2.2.of_le (by simp)) hΔ hP
    (fun y => (edgeProfiles_mem_Icc y).1) (fun y => (edgeProfiles_mem_Icc y).2.1)
    cgpEdgeH_mem_Icc (fun y => (edgeProfiles_mem_Icc y).2.2.2)
    hf.1 hg.1 hh.1 hc.1 hf.2 hg.2 hh.2 hc.2 edgeProfiles_support.1 tsupport_cgpEdgeH_subset_KA6
    s hs (fun j => EuclideanSpace.proj (some j)) (EuclideanSpace.proj none)
    (fun j => norm_euclideanProj_le_KA6 _) (norm_euclideanProj_le_KA6 _) y
  exact ⟨hb.2.1, hb.2.2⟩

end Network

/-- `FC10`'s constant `K* = 10(N + 1)²P³` at the count bound `N = fc07ActiveBound`. -/
def tcpNetworkK : ℝ := 10 * (fc07ActiveBound + 1) ^ 2 * tcpProfileBound ^ 3

/-- The common `C²` bound of every block of the first model graph. -/
def tcpBlockBound : ℝ :=
  50 * (tcpProfileBound + 1) + 4 * (fc07ActiveBound + 1) *
    (Real.sqrt (fc07ActiveBound + 1) * (2 + 20 * tcpNetworkK) +
      24 * Real.sqrt (fc07ActiveBound + 1) * tcpNetworkK)

/-- **TCP05's early graph constant** `C = (N + 3) · tcpBlockBound` (profiles and FC07's count
only; fixed before `Δ` and noncollapse). -/
def tcpGraphConst : ℝ := (fc07ActiveBound + 3) * tcpBlockBound

theorem one_le_tcpBlockBound : 1 ≤ tcpBlockBound := by
  have hP := tcpProfileBound_spec.1
  have hN := one_le_fc07ActiveBound
  have hK : 0 ≤ tcpNetworkK := by rw [tcpNetworkK]; positivity
  rw [tcpBlockBound]
  have : 0 ≤ 4 * (fc07ActiveBound + 1) *
      (Real.sqrt (fc07ActiveBound + 1) * (2 + 20 * tcpNetworkK) +
        24 * Real.sqrt (fc07ActiveBound + 1) * tcpNetworkK) := by positivity
  linarith

theorem one_le_tcpGraphConst : 1 ≤ tcpGraphConst := by
  have h1 := one_le_tcpBlockBound
  have hN := one_le_fc07ActiveBound
  rw [tcpGraphConst]
  nlinarith

section Model

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

/-- The affine network input `U(a)`: `u_j`-coordinate `A1_j a + c1_j` (edge tag `j ∈ Se`) and
`v`-coordinate `Bτ a + cτ`. -/
def tcpEdgeInput (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)
    (Se : Finset L.edge.finite_centres.toFinset) (A1 : CGPTag L Z → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) (a : ℝ²) : EuclideanSpace ℝ (Option Se) :=
  tcpEdgeRows (fun o => Option.elim o Bτ fun j => A1 (.inr (.inr (.inl j.1)))) a +
    WithLp.toLp 2 (fun o => Option.elim o cτ fun j => c1 (.inr (.inr (.inl j.1))))

open Classical in
/-- **The blocks of TCP05's model graph** at the circle reference `i` (see the module
docstring). -/
def tcpModelComponent (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (i : X)
    (S : Finset (CGPTag L Z)) (Se : Finset L.edge.finite_centres.toFinset)
    (Ac : CGPTag L Z → ℝ² →L[ℝ] ℝ²) (cc : CGPTag L Z → ℝ²) (A1 : CGPTag L Z → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) :
    (t : CGPTag L Z) → ℝ² → WithLp 2 (ℝ² × ℝ)
  | .inl j =>
      if j.1 = i then fun a => WithLp.toLp 2 (a, 1)
      else if (.inl j : CGPTag L Z) ∈ S then
        fun a => scaledCutoffBlock (ρ j.1 / ρ i) (circleCutoffBump_LC87 : ℝ² → ℝ)
          (Ac (.inl j) a + cc (.inl j))
      else 0
  | .inr (.inl j) =>
      if (.inr (.inl j) : CGPTag L Z) ∈ S then
        fun a => blockLift_KC3 (sgpModelBlock (10 ^ 5 * Δ) (ρ j.1 / ρ i)
          (A1 (.inr (.inl j)) a + c1 (.inr (.inl j))))
      else 0
  | .inr (.inr (.inl j)) =>
      if hj : j ∈ Se then
        fun a => blockLift_KC3 (tcpNetwork Δ (fun k : Se => ρ k.1.1 / ρ i)
          (tcpEdgeInput L Z Se A1 c1 Bτ cτ a) (some ⟨j, hj⟩))
      else 0
  | .inr (.inr (.inr (.inl k))) =>
      if (.inr (.inr (.inr (.inl k))) : CGPTag L Z) ∈ S then
        fun a => blockLift_KC3 (zeroModelBlock
          ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i)
          (A1 (.inr (.inr (.inr (.inl k)))) a + c1 (.inr (.inr (.inr (.inl k))))))
      else 0
  | .inr (.inr (.inr (.inr false))) => fun _ => WithLp.toLp 2 (0, 1)
  | .inr (.inr (.inr (.inr true))) =>
      fun a => blockLift_KC3 (tcpNetwork Δ (fun k : Se => ρ k.1.1 / ρ i)
        (tcpEdgeInput L Z Se A1 c1 Bτ cτ a) none)

/-- **TCP05's model graph** `Φ_i : ℝ² → H`. -/
def tcpModelGraph (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (i : X)
    (S : Finset (CGPTag L Z)) (Se : Finset L.edge.finite_centres.toFinset)
    (Ac : CGPTag L Z → ℝ² →L[ℝ] ℝ²) (cc : CGPTag L Z → ℝ²) (A1 : CGPTag L Z → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) : ℝ² → BlockSpace (fun _ : CGPTag L Z => ℝ²) :=
  orthogonalBlocks (tcpModelComponent L Z i S Se Ac cc A1 c1 Bτ cτ)

end Model

section BlockBounds

/-- The planar own block `a ↦ (a, 1)`: smooth, derivative norm at most one, second derivative
zero. -/
theorem tcp_own_bounds_KA6 :
    ContDiff ℝ ∞ (fun a : ℝ² => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ² × ℝ))) ∧
      ∀ a : ℝ², ‖fderiv ℝ (fun a : ℝ² => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ² × ℝ))) a‖ ≤
          1 ∧
        ‖fderiv ℝ (fderiv ℝ
          (fun a : ℝ² => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ² × ℝ)))) a‖ ≤ 1 := by
  obtain ⟨J, hJ⟩ : ∃ J : ℝ² →L[ℝ] WithLp 2 (ℝ² × ℝ), ∀ a, J a = WithLp.toLp 2 (a, 0) :=
    ⟨(WithLp.prodContinuousLinearEquiv 2 ℝ ℝ² ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℝ ℝ² ℝ), fun a => rfl⟩
  obtain ⟨v₀, hv₀⟩ : ∃ v : WithLp 2 (ℝ² × ℝ), v = WithLp.toLp 2 (0, (1 : ℝ)) := ⟨_, rfl⟩
  have hfun : (fun a : ℝ² => (WithLp.toLp 2 (a, (1 : ℝ)) : WithLp 2 (ℝ² × ℝ))) =
      fun a => J a + v₀ := by
    funext a
    rw [hJ, hv₀, ← WithLp.toLp_add]
    simp
  have hJn : ‖J‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => by
    rw [hJ, WithLp.prod_norm_eq_of_L2, one_mul]
    simp
  have hd : ∀ a : ℝ², HasFDerivAt (fun a : ℝ² => J a + v₀) J a :=
    fun a => J.hasFDerivAt.add_const v₀
  have hD : fderiv ℝ (fun a : ℝ² => J a + v₀) = fun _ => J := funext fun a => (hd a).fderiv
  rw [hfun]
  refine ⟨J.contDiff.add contDiff_const, fun a => ⟨?_, ?_⟩⟩
  · rw [hD]
    exact hJn
  · rw [hD, fderiv_const_apply, norm_zero]
    exact zero_le_one

theorem tcpBlockBound_ge_KA6 :
    50 * (tcpProfileBound + 1) ≤ tcpBlockBound ∧
      4 * (fc07ActiveBound + 1) *
        (Real.sqrt (fc07ActiveBound + 1) * (2 + 20 * tcpNetworkK) +
          24 * Real.sqrt (fc07ActiveBound + 1) * tcpNetworkK) ≤ tcpBlockBound := by
  have hP := tcpProfileBound_spec.1
  have hN := one_le_fc07ActiveBound
  have hK : 0 ≤ tcpNetworkK := by rw [tcpNetworkK]; positivity
  have h1 : 0 ≤ 4 * (fc07ActiveBound + 1) *
      (Real.sqrt (fc07ActiveBound + 1) * (2 + 20 * tcpNetworkK) +
        24 * Real.sqrt (fc07ActiveBound + 1) * tcpNetworkK) := by positivity
  rw [tcpBlockBound]
  constructor <;> linarith

/-- A listed circle block `a ↦ scaledCutoffBlock s ψ (A a + c)` (`s ∈ [1/2, 2]`, `‖A‖ ≤ 1`) has
first and second derivatives at most `tcpBlockBound`. -/
theorem tcp_circle_block_bounds_KA6 {s : ℝ} (hs : s ∈ Icc (1 / 2 : ℝ) 2) (A : ℝ² →L[ℝ] ℝ²)
    (hA : ‖A‖ ≤ 1) (c : ℝ²) (a : ℝ²) :
    ‖fderiv ℝ (fun a => scaledCutoffBlock s (circleCutoffBump_LC87 : ℝ² → ℝ) (A a + c)) a‖ ≤
        tcpBlockBound ∧
      ‖fderiv ℝ (fderiv ℝ
        (fun a => scaledCutoffBlock s (circleCutoffBump_LC87 : ℝ² → ℝ) (A a + c))) a‖ ≤
        tcpBlockBound := by
  obtain ⟨hP, -, -, hbump, -⟩ := tcpProfileBound_spec
  have hs0 : 0 < s := by linarith [hs.1]
  have hsupp : tsupport (circleCutoffBump_LC87 : ℝ² → ℝ) ⊆ closedBall 0 9 := by
    rw [circleCutoffBump_LC87.tsupport_eq]
    exact le_rfl
  have hW := scaledCutoffBlock_derivative_bounds circleCutoffBump_LC87.contDiff
    hs0 (by norm_num : (0 : ℝ) ≤ 9) (by linarith : (0 : ℝ) ≤ tcpProfileBound)
    (by linarith : (0 : ℝ) ≤ tcpProfileBound)
    (fun y => ⟨circleCutoffBump_LC87.nonneg, circleCutoffBump_LC87.le_one⟩) hsupp
    (fun y => (hbump y).1) (fun y => (hbump y).2)
  have hB : 0 ≤ 50 * (tcpProfileBound + 1) := by linarith
  have h1 : ∀ y, ‖fderiv ℝ (scaledCutoffBlock s (circleCutoffBump_LC87 : ℝ² → ℝ)) y‖ ≤
      50 * (tcpProfileBound + 1) := fun y => (hW y).1.trans (by linarith)
  have h2 : ∀ y, ‖fderiv ℝ (fderiv ℝ (scaledCutoffBlock s (circleCutoffBump_LC87 : ℝ² → ℝ))) y‖ ≤
      50 * (tcpProfileBound + 1) := by
    intro y
    refine (hW y).2.trans ?_
    rw [div_le_iff₀ hs0]
    nlinarith [hs.1]
  have h := affine_comp_bounds_KA6
    (contDiff_scaledCutoffBlock circleCutoffBump_LC87.contDiff s) hB h1 h2 A hA c a
  have hge := tcpBlockBound_ge_KA6.1
  constructor
  · exact h.1.trans (by linarith)
  · exact h.2.trans (by nlinarith)

/-- A lifted scalar block `a ↦ blockLift (W (A a + c))` (`‖A‖ ≤ 1`) keeps the `C²` bounds of `W`. -/
theorem tcp_lifted_block_bounds_KA6 {W : ℝ → WithLp 2 (ℝ × ℝ)} (hW : ContDiff ℝ 2 W) {B : ℝ}
    (hB : 0 ≤ B) (h1 : ∀ y, ‖fderiv ℝ W y‖ ≤ B) (h2 : ∀ y, ‖fderiv ℝ (fderiv ℝ W) y‖ ≤ B)
    (A : ℝ² →L[ℝ] ℝ) (hA : ‖A‖ ≤ 1) (c : ℝ) (a : ℝ²) :
    ‖fderiv ℝ (fun a => blockLift_KC3 (W (A a + c))) a‖ ≤ B ∧
      ‖fderiv ℝ (fderiv ℝ (fun a => blockLift_KC3 (W (A a + c)))) a‖ ≤ B := by
  have haff := affine_comp_bounds_KA6 hW hB h1 h2 A hA c
  have hWc : ContDiff ℝ 2 (fun a => W (A a + c)) := hW.comp (A.contDiff.add contDiff_const)
  have h := clm_comp_bounds_KA6 blockLift_KC3 norm_blockLift_le_KC3 hWc
    (fun y => (haff y).1.trans (by rw [one_mul])) (fun y => (haff y).2.trans (by norm_num)) a
  exact h

/-- A block of the network along the affine input `a ↦ M a + u₀` (`#ι ≤ N`, rows of norm `≤ 2`,
`s ∈ [1/2, 2]`, `Δ ≥ 1`) has first and second derivatives at most `tcpBlockBound`. -/
theorem tcp_network_block_bounds_KA6 {ι : Type*} [Fintype ι] {Δ : ℝ} (hΔ : 1 ≤ Δ)
    (s : ι → ℝ) (hs : ∀ j, s j ∈ Icc (1 / 2) 2) (hcard : (Fintype.card ι : ℝ) ≤ fc07ActiveBound)
    (A : Option ι → ℝ² →L[ℝ] ℝ) (hA : ∀ o, ‖A o‖ ≤ 2) (u₀ : EuclideanSpace ℝ (Option ι))
    (o : Option ι) (a : ℝ²) :
    ‖fderiv ℝ (fun a => blockLift_KC3 (tcpNetwork Δ s (tcpEdgeRows A a + u₀) o)) a‖ ≤
        tcpBlockBound ∧
      ‖fderiv ℝ (fderiv ℝ (fun a => blockLift_KC3 (tcpNetwork Δ s (tcpEdgeRows A a + u₀) o)))
        a‖ ≤ tcpBlockBound := by
  have hP := tcpProfileBound_spec.1
  have hN1 := one_le_fc07ActiveBound
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  set NB : ℝ := fc07ActiveBound with hNB
  have hK : 10 * (n + 1) ^ 2 * tcpProfileBound ^ 3 ≤ tcpNetworkK := by
    rw [tcpNetworkK]
    have h3 : 0 ≤ tcpProfileBound ^ 3 := by positivity
    have h2 : (n + 1) ^ 2 ≤ (NB + 1) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    nlinarith
  have hK0 : 0 ≤ 10 * (n + 1) ^ 2 * tcpProfileBound ^ 3 := by positivity
  have hsq : Real.sqrt (n + 1) ≤ Real.sqrt (NB + 1) := Real.sqrt_le_sqrt (by linarith)
  have hsq0 : 0 ≤ Real.sqrt (n + 1) := Real.sqrt_nonneg _
  set BW : ℝ := Real.sqrt (NB + 1) * (2 + 20 * tcpNetworkK) +
    24 * Real.sqrt (NB + 1) * tcpNetworkK with hBW
  have hKs : 0 ≤ tcpNetworkK := hK0.trans hK
  have hBW0 : 0 ≤ BW := by positivity
  have hW1 : ∀ y, ‖fderiv ℝ (tcpNetwork Δ s) y‖ ≤ BW := by
    intro y
    refine (tcpNetwork_bounds hΔ s hs y).1.trans ?_
    have : Real.sqrt (n + 1) * (2 + 20 * (10 * (n + 1) ^ 2 * tcpProfileBound ^ 3)) ≤
        Real.sqrt (NB + 1) * (2 + 20 * tcpNetworkK) :=
      mul_le_mul hsq (by linarith) (by positivity) (Real.sqrt_nonneg _)
    have h0 : 0 ≤ 24 * Real.sqrt (NB + 1) * tcpNetworkK := by positivity
    linarith
  have hW2 : ∀ y, ‖fderiv ℝ (fderiv ℝ (tcpNetwork Δ s)) y‖ ≤ BW := by
    intro y
    refine (tcpNetwork_bounds hΔ s hs y).2.trans ?_
    have hΔ0 : 0 < Δ := by linarith
    have h1 : 24 * Real.sqrt (n + 1) * (10 * (n + 1) ^ 2 * tcpProfileBound ^ 3) / Δ ≤
        24 * Real.sqrt (n + 1) * (10 * (n + 1) ^ 2 * tcpProfileBound ^ 3) := by
      rw [div_le_iff₀ hΔ0]
      have : 0 ≤ 24 * Real.sqrt (n + 1) * (10 * (n + 1) ^ 2 * tcpProfileBound ^ 3) := by
        positivity
      nlinarith
    have h2 : 24 * Real.sqrt (n + 1) * (10 * (n + 1) ^ 2 * tcpProfileBound ^ 3) ≤
        24 * Real.sqrt (NB + 1) * tcpNetworkK :=
      mul_le_mul (by linarith) hK hK0 (by positivity)
    have h0 : 0 ≤ Real.sqrt (NB + 1) * (2 + 20 * tcpNetworkK) := by positivity
    linarith
  have hcardO : (Fintype.card (Option ι) : ℝ) = n + 1 := by
    rw [Fintype.card_option]
    push_cast
    rfl
  have hM : ‖tcpEdgeRows A‖ ≤ 2 * Real.sqrt (NB + 1) := by
    refine (norm_tcpEdgeRows_le A (by norm_num) hA).trans ?_
    rw [hcardO]
    nlinarith
  have hc0 : 0 ≤ 2 * Real.sqrt (NB + 1) := by positivity
  have haff := affine_comp_bounds_KA6 ((contDiff_tcpNetwork Δ s).of_le (by simp)) hBW0 hW1 hW2
    (tcpEdgeRows A) hM u₀
  set c : ℝ := 2 * Real.sqrt (NB + 1) with hc
  have hsqN : Real.sqrt (NB + 1) ^ 2 = NB + 1 := Real.sq_sqrt (by linarith)
  have hsqle : Real.sqrt (NB + 1) ≤ NB + 1 := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hcB : c * BW ≤ 4 * (NB + 1) * BW :=
    mul_le_mul_of_nonneg_right (by rw [hc]; linarith) hBW0
  have hc2B : c ^ 2 * BW = 4 * (NB + 1) * BW := by
    rw [hc, mul_pow, hsqN]
    ring
  have hge := tcpBlockBound_ge_KA6.2
  have hcomp : (fun a => blockLift_KC3 (tcpNetwork Δ s (tcpEdgeRows A a + u₀) o)) =
      (blockLift_KC3.comp (PiLp.proj 2 (fun _ : Option ι => WithLp 2 (ℝ × ℝ)) o)) ∘
        (fun a => tcpNetwork Δ s (tcpEdgeRows A a + u₀)) := rfl
  have hLn : ‖blockLift_KC3.comp (PiLp.proj 2 (fun _ : Option ι => WithLp 2 (ℝ × ℝ)) o)‖ ≤ 1 := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have hp : ‖(PiLp.proj 2 (fun _ : Option ι => WithLp 2 (ℝ × ℝ)) o :
        PiLp 2 (fun _ : Option ι => WithLp 2 (ℝ × ℝ)) →L[ℝ] WithLp 2 (ℝ × ℝ))‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
        rw [one_mul]
        exact PiLp.norm_apply_le x o
    nlinarith [norm_blockLift_le_KC3, norm_nonneg blockLift_KC3,
      norm_nonneg (PiLp.proj 2 (fun _ : Option ι => WithLp 2 (ℝ × ℝ)) o :
        PiLp 2 (fun _ : Option ι => WithLp 2 (ℝ × ℝ)) →L[ℝ] WithLp 2 (ℝ × ℝ))]
  have hWc : ContDiff ℝ 2 (fun a => tcpNetwork Δ s (tcpEdgeRows A a + u₀)) :=
    ((contDiff_tcpNetwork Δ s).of_le (by simp)).comp ((tcpEdgeRows A).contDiff.add contDiff_const)
  rw [hcomp]
  have h := clm_comp_bounds_KA6 _ hLn hWc (B := tcpBlockBound)
    (fun y => (haff y).1.trans (hcB.trans hge))
    (fun y => (haff y).2.trans (by rw [hc2B]; exact hge)) a
  exact h

end BlockBounds

section ModelFacts

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

theorem tcpEdgeInput_eq (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)
    (Se : Finset L.edge.finite_centres.toFinset) (A1 : CGPTag L Z → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) :
    tcpEdgeInput L Z Se A1 c1 Bτ cτ = fun a =>
      tcpEdgeRows (fun o => Option.elim o Bτ fun j => A1 (.inr (.inr (.inl j.1)))) a +
        WithLp.toLp 2 (fun o => Option.elim o cτ fun j => c1 (.inr (.inr (.inl j.1)))) :=
  rfl

open Classical in
/-- Every block of the model is smooth. -/
theorem contDiff_tcpModelComponent
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (i : X)
    (S : Finset (CGPTag L Z)) (Se : Finset L.edge.finite_centres.toFinset)
    (Ac : CGPTag L Z → ℝ² →L[ℝ] ℝ²) (cc : CGPTag L Z → ℝ²) (A1 : CGPTag L Z → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) (t : CGPTag L Z) :
    ContDiff ℝ ∞ (tcpModelComponent L Z i S Se Ac cc A1 c1 Bτ cτ t) := by
  have hU : ContDiff ℝ ∞ (tcpEdgeInput L Z Se A1 c1 Bτ cτ) := by
    rw [tcpEdgeInput_eq]
    exact (tcpEdgeRows (fun o : Option Se => Option.elim o Bτ
      fun j => A1 (.inr (.inr (.inl j.1))))).contDiff.add contDiff_const
  have hnet : ∀ o : Option Se, ContDiff ℝ ∞ (fun a => blockLift_KC3
      (tcpNetwork Δ (fun k : Se => ρ k.1.1 / ρ i) (tcpEdgeInput L Z Se A1 c1 Bτ cτ a) o)) := by
    intro o
    have hfun : (fun a => blockLift_KC3
        (tcpNetwork Δ (fun k : Se => ρ k.1.1 / ρ i) (tcpEdgeInput L Z Se A1 c1 Bτ cτ a) o)) =
        blockLift_KC3 ∘ ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Option Se => WithLp 2 (ℝ × ℝ)) o) ∘
          (tcpNetwork Δ (fun k : Se => ρ k.1.1 / ρ i) ∘ tcpEdgeInput L Z Se A1 c1 Bτ cτ)) := rfl
    rw [hfun]
    exact blockLift_KC3.contDiff.comp
      ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Option Se => WithLp 2 (ℝ × ℝ)) o).contDiff.comp
        ((contDiff_tcpNetwork _ _).comp hU))
  rcases t with j | j | j | k | q
  · simp only [tcpModelComponent]
    split_ifs
    · exact tcp_own_bounds_KA6.1
    · exact (contDiff_scaledCutoffBlock circleCutoffBump_LC87.contDiff _).comp
        ((Ac _).contDiff.add contDiff_const)
    · exact contDiff_const
  · simp only [tcpModelComponent]
    split_ifs
    · exact blockLift_KC3.contDiff.comp ((contDiff_sgpModelBlock _ _).comp
        ((A1 _).contDiff.add contDiff_const))
    · exact contDiff_const
  · simp only [tcpModelComponent]
    split_ifs with hj
    · exact hnet _
    · exact contDiff_const
  · simp only [tcpModelComponent]
    split_ifs
    · exact blockLift_KC3.contDiff.comp ((contDiff_zeroModelBlock _).comp
        ((A1 _).contDiff.add contDiff_const))
    · exact contDiff_const
  · cases q
    · exact contDiff_const
    · exact hnet none

theorem contDiff_tcpModelGraph
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (i : X)
    (S : Finset (CGPTag L Z)) (Se : Finset L.edge.finite_centres.toFinset)
    (Ac : CGPTag L Z → ℝ² →L[ℝ] ℝ²) (cc : CGPTag L Z → ℝ²) (A1 : CGPTag L Z → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) :
    ContDiff ℝ ∞ (tcpModelGraph L Z i S Se Ac cc A1 c1 Bτ cτ) :=
  contDiff_orthogonalBlocks (contDiff_tcpModelComponent L Z i S Se Ac cc A1 c1 Bτ cτ)

/-- The own block of the model is `(a, 1)`. -/
theorem tcpModelGraph_own
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (i : X)
    (S : Finset (CGPTag L Z)) (Se : Finset L.edge.finite_centres.toFinset)
    (Ac : CGPTag L Z → ℝ² →L[ℝ] ℝ²) (cc : CGPTag L Z → ℝ²) (A1 : CGPTag L Z → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) (j : L.circle.finite_centres.toFinset)
    (hj : j.1 = i) (a : ℝ²) :
    tcpModelGraph L Z i S Se Ac cc A1 c1 Bτ cτ a (.inl j) = WithLp.toLp 2 (a, 1) := by
  change tcpModelComponent L Z i S Se Ac cc A1 c1 Bτ cτ (.inl j) a = _
  simp only [tcpModelComponent, hj, ite_true]

/-- The scale block of the model is the constant `(0, 1)`. -/
theorem tcpModelGraph_scale
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (i : X)
    (S : Finset (CGPTag L Z)) (Se : Finset L.edge.finite_centres.toFinset)
    (Ac : CGPTag L Z → ℝ² →L[ℝ] ℝ²) (cc : CGPTag L Z → ℝ²) (A1 : CGPTag L Z → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) (a : ℝ²) :
    tcpModelGraph L Z i S Se Ac cc A1 c1 Bτ cτ a (cgpScaleTag L Z) = WithLp.toLp 2 (0, 1) :=
  rfl

open Classical in
/-- The active tags of the model: the listed set `S`, the network edges `Se`, the scale and
`E'` tags. -/
def tcpModelActive (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)
    (S : Finset (CGPTag L Z)) (Se : Finset L.edge.finite_centres.toFinset) :
    Finset (CGPTag L Z) :=
  S ∪ Se.image (fun j => (.inr (.inr (.inl j)) : CGPTag L Z)) ∪ {cgpScaleTag L Z, cgpEdgeTag L Z}

open Classical in
/-- Off the active tags every block of the model is the zero function (the own tag is in `S`). -/
theorem tcpModelComponent_eq_zero
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (i : X)
    (S : Finset (CGPTag L Z)) (Se : Finset L.edge.finite_centres.toFinset)
    (Ac : CGPTag L Z → ℝ² →L[ℝ] ℝ²) (cc : CGPTag L Z → ℝ²) (A1 : CGPTag L Z → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ)
    (hown : ∀ j : L.circle.finite_centres.toFinset, j.1 = i → (.inl j : CGPTag L Z) ∈ S)
    (t : CGPTag L Z) (ht : t ∉ tcpModelActive L Z S Se) :
    tcpModelComponent L Z i S Se Ac cc A1 c1 Bτ cτ t = 0 := by
  have hS : t ∉ S := fun h => ht (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  rcases t with j | j | j | k | q
  · have hji : j.1 ≠ i := fun h => hS (hown j h)
    simp only [tcpModelComponent, hji, hS, ite_false]
  · simp only [tcpModelComponent, hS, ite_false]
  · have hj : j ∉ Se := fun h => ht (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ h)))
    simp only [tcpModelComponent, hj, dite_false]
  · simp only [tcpModelComponent, hS, ite_false]
  · exact (ht (Finset.mem_union_right _ (by cases q <;> simp [cgpScaleTag, cgpEdgeTag]))).elim

/-- The zero block has `C²` bounds `tcpBlockBound`. -/
theorem zero_block_bounds_KA6 (b : ℝ²) :
    ‖fderiv ℝ (0 : ℝ² → WithLp 2 (ℝ² × ℝ)) b‖ ≤ tcpBlockBound ∧
      ‖fderiv ℝ (fderiv ℝ (0 : ℝ² → WithLp 2 (ℝ² × ℝ))) b‖ ≤ tcpBlockBound := by
  have hB0 : 0 ≤ tcpBlockBound := le_trans zero_le_one one_le_tcpBlockBound
  have h0 : (0 : ℝ² → WithLp 2 (ℝ² × ℝ)) = fun _ => 0 := rfl
  have h1 : fderiv ℝ (0 : ℝ² → WithLp 2 (ℝ² × ℝ)) = fun _ => 0 := by
    rw [h0]
    exact funext fun y => fderiv_const_apply 0
  rw [h1, fderiv_const_apply, norm_zero]
  exact ⟨hB0, by rw [norm_zero]; exact hB0⟩

/-- The constant scale block has `C²` bounds `tcpBlockBound`. -/
theorem scale_block_bounds_KA6 (b : ℝ²) :
    ‖fderiv ℝ (fun _ : ℝ² => (WithLp.toLp 2 (0, 1) : WithLp 2 (ℝ² × ℝ))) b‖ ≤ tcpBlockBound ∧
      ‖fderiv ℝ (fderiv ℝ (fun _ : ℝ² => (WithLp.toLp 2 (0, 1) : WithLp 2 (ℝ² × ℝ)))) b‖ ≤
        tcpBlockBound := by
  have hB0 : 0 ≤ tcpBlockBound := le_trans zero_le_one one_le_tcpBlockBound
  have h1 : fderiv ℝ (fun _ : ℝ² => (WithLp.toLp 2 (0, 1) : WithLp 2 (ℝ² × ℝ))) = fun _ => 0 :=
    funext fun y => fderiv_const_apply _
  rw [h1, fderiv_const_apply, norm_zero]
  exact ⟨hB0, by rw [norm_zero]; exact hB0⟩

/-- Every network block of the model (edge `j ∈ Se` or `E'`) has `C²` bounds `tcpBlockBound`. -/
theorem tcp_network_component_bounds_KA6
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (i : X)
    (Se : Finset L.edge.finite_centres.toFinset) (A1 : CGPTag L Z → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) (hΔ : 1 ≤ Δ)
    (hE : ∀ j ∈ Se, ‖A1 (.inr (.inr (.inl j)))‖ ≤ 2 ∧ ρ j.1 / ρ i ∈ Icc (1 / 2 : ℝ) 2)
    (hB : ‖Bτ‖ ≤ 2) (hcountE : (Se.card : ℝ) ≤ fc07ActiveBound) (o : Option Se) (b : ℝ²) :
    ‖fderiv ℝ (fun a => blockLift_KC3 (tcpNetwork Δ (fun k : Se => ρ k.1.1 / ρ i)
        (tcpEdgeInput L Z Se A1 c1 Bτ cτ a) o)) b‖ ≤ tcpBlockBound ∧
      ‖fderiv ℝ (fderiv ℝ (fun a => blockLift_KC3 (tcpNetwork Δ (fun k : Se => ρ k.1.1 / ρ i)
        (tcpEdgeInput L Z Se A1 c1 Bτ cτ a) o))) b‖ ≤ tcpBlockBound := by
  have hs : ∀ k : Se, ρ k.1.1 / ρ i ∈ Icc (1 / 2 : ℝ) 2 := fun k => (hE k.1 k.2).2
  have hcard : (Fintype.card Se : ℝ) ≤ fc07ActiveBound := by
    rw [Fintype.card_coe]
    exact hcountE
  have hA : ∀ o' : Option Se,
      ‖(Option.elim o' Bτ fun j => A1 (.inr (.inr (.inl j.1))) : ℝ² →L[ℝ] ℝ)‖ ≤ 2 := by
    intro o'
    cases o' with
    | none => exact hB
    | some k => exact (hE k.1 k.2).1
  exact tcp_network_block_bounds_KA6 hΔ (fun k : Se => ρ k.1.1 / ρ i) hs hcard
    (fun o' => Option.elim o' Bτ fun j => A1 (.inr (.inr (.inl j.1)))) hA
    (WithLp.toLp 2 (fun o' => Option.elim o' cτ fun j => c1 (.inr (.inr (.inl j.1))))) o b

open Classical in
/-- Every active block of the model has `C²` bounds `tcpBlockBound`. -/
theorem tcpModelComponent_bounds_KA6
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (i : X)
    (S : Finset (CGPTag L Z)) (Se : Finset L.edge.finite_centres.toFinset)
    (Ac : CGPTag L Z → ℝ² →L[ℝ] ℝ²) (cc : CGPTag L Z → ℝ²) (A1 : CGPTag L Z → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) (hΔ : 1 ≤ Δ)
    (hC : ∀ j : L.circle.finite_centres.toFinset, j.1 ≠ i → (.inl j : CGPTag L Z) ∈ S →
      ‖Ac (.inl j)‖ ≤ 1 ∧ ρ j.1 / ρ i ∈ Icc (1 / 2 : ℝ) 2)
    (hS : ∀ j : L.slim.finite_centres.toFinset, (.inr (.inl j) : CGPTag L Z) ∈ S →
      ‖A1 (.inr (.inl j))‖ ≤ 1 ∧ 99 / 100 ≤ ρ j.1 / ρ i)
    (hZ : ∀ k : Z.finite_centres.toFinset, (.inr (.inr (.inr (.inl k))) : CGPTag L Z) ∈ S →
      ‖A1 (.inr (.inr (.inr (.inl k))))‖ ≤ 1 ∧
        1 ≤ (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i)
    (hE : ∀ j ∈ Se, ‖A1 (.inr (.inr (.inl j)))‖ ≤ 2 ∧ ρ j.1 / ρ i ∈ Icc (1 / 2 : ℝ) 2)
    (hB : ‖Bτ‖ ≤ 2) (hcountE : (Se.card : ℝ) ≤ fc07ActiveBound) (t : CGPTag L Z) (b : ℝ²) :
    ‖fderiv ℝ (tcpModelComponent L Z i S Se Ac cc A1 c1 Bτ cτ t) b‖ ≤ tcpBlockBound ∧
      ‖fderiv ℝ (fderiv ℝ (tcpModelComponent L Z i S Se Ac cc A1 c1 Bτ cτ t)) b‖ ≤
        tcpBlockBound := by
  have hB1 := one_le_tcpBlockBound
  have hB0 : 0 ≤ tcpBlockBound := by linarith
  have hge := tcpBlockBound_ge_KA6.1
  have hP := tcpProfileBound_spec
  have hnet := tcp_network_component_bounds_KA6 L Z i Se A1 c1 Bτ cτ hΔ hE hB hcountE
  rcases t with j | j | j | k | q
  · simp only [tcpModelComponent]
    split_ifs with hji hjS
    · exact ⟨(tcp_own_bounds_KA6.2 b).1.trans hB1, (tcp_own_bounds_KA6.2 b).2.trans hB1⟩
    · exact tcp_circle_block_bounds_KA6 (hC j hji hjS).2 _ (hC j hji hjS).1 _ b
    · exact zero_block_bounds_KA6 b
  · simp only [tcpModelComponent]
    split_ifs with hjS
    · have hℓ : 1 ≤ 10 ^ 5 * Δ := by nlinarith
      have hW (y : ℝ) := sgpModelBlock_derivative_bounds hℓ (hS j hjS).2 y
      have hsP : 50 * (sgpProfileBound + 1) ≤ tcpBlockBound := by linarith [hP.2.1]
      exact tcp_lifted_block_bounds_KA6 ((contDiff_sgpModelBlock _ _).of_le (by simp)) hB0
        (fun y => (hW y).1.trans hsP) (fun y => (hW y).2.trans hsP) _ (hS j hjS).1 _ b
    · exact zero_block_bounds_KA6 b
  · simp only [tcpModelComponent]
    split_ifs with hj
    · exact hnet _ b
    · exact zero_block_bounds_KA6 b
  · simp only [tcpModelComponent]
    split_ifs with hkS
    · have hW (y : ℝ) := zeroModelBlock_derivative_bounds (hZ k hkS).2 y
      have hzP : 50 * (zeroProfileBound + 1) ≤ tcpBlockBound := by linarith [hP.2.2.1]
      exact tcp_lifted_block_bounds_KA6 ((contDiff_zeroModelBlock _).of_le (by simp)) hB0
        (fun y => (hW y).1.trans hzP) (fun y => (hW y).2.trans hzP) _ (hZ k hkS).1 _ b
    · exact zero_block_bounds_KA6 b
  · cases q
    · exact scale_block_bounds_KA6 b
    · exact hnet none b

open Classical in
/-- The active set of the model has at most `N + 3` tags. -/
theorem tcpModelActive_card_le_KA6
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)
    (S : Finset (CGPTag L Z)) (Se : Finset L.edge.finite_centres.toFinset)
    (hcount : (S.card : ℝ) + Se.card ≤ fc07ActiveBound + 1) :
    ((tcpModelActive L Z S Se).card : ℝ) ≤ fc07ActiveBound + 3 := by
  have h1 : (tcpModelActive L Z S Se).card ≤
      (S ∪ Se.image (fun j => (.inr (.inr (.inl j)) : CGPTag L Z))).card +
        ({cgpScaleTag L Z, cgpEdgeTag L Z} : Finset (CGPTag L Z)).card := Finset.card_union_le _ _
  have h2 : (S ∪ Se.image (fun j => (.inr (.inr (.inl j)) : CGPTag L Z))).card ≤
      S.card + Se.card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _)
  have h3 : ({cgpScaleTag L Z, cgpEdgeTag L Z} : Finset (CGPTag L Z)).card ≤ 2 :=
    Finset.card_le_two
  have h4 : (tcpModelActive L Z S Se).card ≤ S.card + Se.card + 2 := by omega
  have h5 : ((tcpModelActive L Z S Se).card : ℝ) ≤ (S.card : ℝ) + Se.card + 2 := by
    exact_mod_cast h4
  linarith

open Classical in
/-- **TCP05's model bounds (kernel form).** With `Δ ≥ 1`, the own tag in `S`, coisometric circle
rows (`‖Ac‖ ≤ 1`, `s_j ∈ [1/2, 2]`), slim rows `‖A1‖ ≤ 1` with `s_j ≥ 99/100`, zero rows
`‖A1‖ ≤ 1` with `R₀/ρ(i) ≥ 1`, edge input rows `‖A1‖ ≤ 2` with `s_j ∈ [1/2, 2]`, `‖Bτ‖ ≤ 2`, and
`#S + #Se ≤ N + 1`, `#Se ≤ N` (`N = fc07ActiveBound`): `‖DΦ_i‖, ‖D²Φ_i‖ ≤ tcpGraphConst`. -/
theorem tcp05_model_bounds
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (i : X)
    (S : Finset (CGPTag L Z)) (Se : Finset L.edge.finite_centres.toFinset)
    (Ac : CGPTag L Z → ℝ² →L[ℝ] ℝ²) (cc : CGPTag L Z → ℝ²) (A1 : CGPTag L Z → ℝ² →L[ℝ] ℝ)
    (c1 : CGPTag L Z → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) (hΔ : 1 ≤ Δ)
    (hown : ∀ j : L.circle.finite_centres.toFinset, j.1 = i → (.inl j : CGPTag L Z) ∈ S)
    (hC : ∀ j : L.circle.finite_centres.toFinset, j.1 ≠ i → (.inl j : CGPTag L Z) ∈ S →
      ‖Ac (.inl j)‖ ≤ 1 ∧ ρ j.1 / ρ i ∈ Icc (1 / 2 : ℝ) 2)
    (hS : ∀ j : L.slim.finite_centres.toFinset, (.inr (.inl j) : CGPTag L Z) ∈ S →
      ‖A1 (.inr (.inl j))‖ ≤ 1 ∧ 99 / 100 ≤ ρ j.1 / ρ i)
    (hZ : ∀ k : Z.finite_centres.toFinset, (.inr (.inr (.inr (.inl k))) : CGPTag L Z) ∈ S →
      ‖A1 (.inr (.inr (.inr (.inl k))))‖ ≤ 1 ∧
        1 ≤ (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i)
    (hE : ∀ j ∈ Se, ‖A1 (.inr (.inr (.inl j)))‖ ≤ 2 ∧ ρ j.1 / ρ i ∈ Icc (1 / 2 : ℝ) 2)
    (hB : ‖Bτ‖ ≤ 2) (hcount : (S.card : ℝ) + Se.card ≤ fc07ActiveBound + 1)
    (hcountE : (Se.card : ℝ) ≤ fc07ActiveBound) (a : ℝ²) :
    ‖fderiv ℝ (tcpModelGraph L Z i S Se Ac cc A1 c1 Bτ cτ) a‖ ≤ tcpGraphConst ∧
      ‖fderiv ℝ (fderiv ℝ (tcpModelGraph L Z i S Se Ac cc A1 c1 Bτ cτ)) a‖ ≤ tcpGraphConst := by
  have hB0 : 0 ≤ tcpBlockBound := le_trans zero_le_one one_le_tcpBlockBound
  have hN := one_le_fc07ActiveBound
  have hblock := tcpModelComponent_bounds_KA6 L Z i S Se Ac cc A1 c1 Bτ cτ hΔ hC hS hZ hE hB
    hcountE
  have hmain := orthogonalBlocks_support_bounds_KA6
    (fun t => (contDiff_tcpModelComponent L Z i S Se Ac cc A1 c1 Bτ cτ t).of_le (by simp))
    (tcpModelActive L Z S Se) hB0 (tcpModelComponent_eq_zero L Z i S Se Ac cc A1 c1 Bτ cτ hown)
    (fun t _ b => (hblock t b).1) (fun t _ b => (hblock t b).2) a
  have hcard := tcpModelActive_card_le_KA6 L Z S Se hcount
  have hsq : Real.sqrt ((tcpModelActive L Z S Se).card : ℝ) ≤ fc07ActiveBound + 3 := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith [Nat.cast_nonneg (α := ℝ) (tcpModelActive L Z S Se).card]
  have hfin : Real.sqrt ((tcpModelActive L Z S Se).card : ℝ) * tcpBlockBound ≤
      tcpGraphConst := by
    rw [tcpGraphConst]
    exact mul_le_mul_of_nonneg_right hsq hB0
  exact ⟨hmain.1.trans hfin, hmain.2.trans hfin⟩

end ModelFacts

end DifferentialGeometry.Geometry.Collapse
