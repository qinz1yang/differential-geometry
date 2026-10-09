import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5CommutatorEvolution
import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5CommutatorRegularity
import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5EvolutionNorm
import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5Background

/-!
# Decay of all derivatives of the traceless Hessian along the surface flow

Chapter 7, surface lemma U1, route (a), step a5.2 (iii) (lane U1C2; design D18,
`docs/geometrization/handoffs/20261004-design-u1-a5-potential-gauge.md`, review 18 §2).

* `ricciTimeCorrection_eq_smul_of_finrank_two`: in dimension two `Ric♯ = (R / 2) id`, so the
  Ricci correction of a covariant `k`-tensor is `(k R / 2) A`; hence
  `surfaceFlow_normSq0S_hasDerivAt`: `∂ₜ |A|² = 2 ⟨∂ₜ A, A⟩ + k R |A|²`.
* `surfaceFlow_tracelessHess_derivative_decay` (D18 (iii), frozen statement): with
  `u_q = (2 (T* - t))^(2 + q) |∇^q M|²`, the heat-defect calculus of
  `EquivariantRoundMetricA5CommutatorEvolution` (`∂ₜ ∇^q M = Δ ∇^q M + errField q`,
  `errField q ∈ IterCovCtl (q + 4) q`) and the bound `2 (T* - t) R ≤ C` give the linear tower
  `∂ₜ u_q ≤ Δ u_q + (-2 u_{q+1} + C_q Σ_{j ≤ q} u_j) / (2 (T* - t))`; the joint smoothness of
  `u_q` is `tracelessHess_iterCov_normSq_contMDiffOn`. `flow_linear_tower_decay` then propagates
  the decay `u_0 ≤ 4 C₀ (T* - t)^c` of (ii′) to every order with the same exponent `γ = c`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Tensor.RSTensor
open Bundle Set Filter Topology
open scoped Manifold ContDiff

namespace GC.Geometry

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {T : ℝ} {hT : 0 < T}

local notation "TF " k => Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
  (n := (∞ : WithTop ℕ∞)) k

theorem ricciTimeCorrection_eq_smul_of_finrank_two (hdim : Module.finrank ℝ E = 2)
    (g : SmoothRiemannianMetric I M) {k : ℕ} {x : M}
    (A : Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) k x) :
    ricciTimeCorrection g A = ((k : ℝ) * (metricScalarAt g x / 2)) • A := by
  have hsharp : ∀ w : TangentSpace I x, ricciSharp g x w = (metricScalarAt g x / 2) • w := by
    intro w
    apply SmoothRiemannianMetric.eq_of_inner_eq g
    intro u
    rw [inner_ricciSharp, ricciTensor_eq_half_metricScalarAt_mul_inner_of_finrank_eq_two g hdim,
      map_smul, smul_apply, smul_eq_mul]
  refine tensor0SSpace_ext k x fun v => ?_
  rw [ricciTimeCorrection_apply, Tensor0SSpace.smul_apply, smul_eq_mul]
  have hterm : ∀ q : Fin k, A (Function.update v q (ricciSharp g x (v q))) =
      metricScalarAt g x / 2 * A v := by
    intro q
    rw [hsharp, A.map_update_smul, Function.update_eq_self, smul_eq_mul]
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem surfaceFlow_normSq0S_hasDerivAt (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    {k : ℕ} (B : ℝ → TF k) {t : ℝ} (ht : t ∈ Ioo 0 T) (x : M)
    (Bd : Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) k x)
    (hB : ∀ v : Fin k → TangentSpace I x, HasDerivAt (fun s => B s x v) (Bd v) t) :
    HasDerivAt (fun s => normSq0S (S.family.metric s) x k (B s x))
      (2 * inner0S (S.family.metric t) x k Bd (B t x) +
        k * S.scalar t x * normSq0S (S.family.metric t) x k (B t x)) t := by
  have hreg : t ∈ (RealTimeInterval.closedOpen 0 T hT).regular := ht
  have hflow : ∀ v w : TangentSpace I x, HasDerivWithinAt
      (fun r => (S.family.metric r).inner x v w)
      (-2 * ricciTensor (S.family.metric t) x v w) univ t := by
    intro v w
    have h := metricDerivAt S hS ⟨t, hreg⟩ x v w
    simp only [SolutionOn.ricciAt, SolutionFamily.ricciAt, metricRicciAt_apply_eq_ricciTensor,
      SolutionOn.family_metric] at h
    exact h.hasDerivWithinAt
  obtain ⟨b, hb⟩ := exists_orthonormal_basis (S.family.metric t) x
  have hB' : ∀ v : Fin k → TangentSpace I x,
      HasDerivWithinAt (fun r => B r x v) (Bd v) univ t := fun v => (hB v).hasDerivWithinAt
  have hd := hasDerivWithinAt_normSq0S_covariantTime S.family.metric (fun r => B r x) Bd univ
    t uniqueDiffWithinAt_univ b hb hflow hB'
  have he : covariantTimeDerivWithin S.family.metric (fun r => B r x) univ t =
      Bd + ((k : ℝ) * (S.scalar t x / 2)) • B t x := by
    have hh : derivWithin (fun r => B r x) univ t = Bd :=
      (hasDerivWithinAt_tensor0S_of_eval (fun r => B r x) Bd univ t hB').derivWithin
        uniqueDiffWithinAt_univ
    rw [covariantTimeDerivWithin, hh, ricciTimeCorrection_eq_smul_of_finrank_two hdim]
    rfl
  rw [he, hasDerivWithinAt_univ] at hd
  refine hd.congr_deriv ?_
  rw [inner0S_add_left, inner0S_smul_left]
  unfold normSq0S
  ring

omit [I.Boundaryless] [T2Space M] in
theorem normSq0S_fromScalarField (g : SmoothRiemannianMetric I M) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    normSq0S g x 0 (Tensor0SField.fromScalarField (∞ : WithTop ℕ∞) f hf x) = f x ^ 2 := by
  classical
  obtain ⟨b, hb⟩ := exists_orthonormal_basis g x
  rw [normSq0S_identity_eq_sum_sq g x 0 b (metricInverseInBasis_of_orthonormal g b hb),
    Fintype.sum_unique, component0S_apply, Tensor0SField.fromScalarField_apply]

def towerU (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (Tst : ℝ)
    (Mf : ℝ → TF 2) (q : ℕ) (t : ℝ) (x : M) : ℝ :=
  (2 * (Tst - t)) ^ (2 + q) *
    normSq0S (S.family.metric t) x (2 + q) (iterCov (S.family.metric t) 2 (Mf t) q x)

def towerCtl (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (Tst : ℝ)
    (Mf : ℝ → TF 2) (n : ℕ) (t : ℝ) (x : M) : ℝ :=
  ∑ b ∈ Finset.range (n + 1), max (towerU S Tst Mf b t x) 0

omit [I.Boundaryless] in
theorem towerCtl_nonneg (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (Tst : ℝ) (Mf : ℝ → TF 2) (n : ℕ) (t : ℝ) (x : M) : 0 ≤ towerCtl S Tst Mf n t x :=
  Finset.sum_nonneg fun _ _ => le_max_right _ _

omit [I.Boundaryless] in
theorem towerCtl_mono (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (Tst : ℝ) (Mf : ℝ → TF 2) (n : ℕ) (t : ℝ) (x : M) :
    towerCtl S Tst Mf n t x ≤ towerCtl S Tst Mf (n + 1) t x := by
  unfold towerCtl
  rw [Finset.sum_range_succ _ (n + 1)]
  exact le_add_of_nonneg_right (le_max_right _ _)

omit [I.Boundaryless] in
theorem towerU_nonneg (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    {Tst : ℝ} (Mf : ℝ → TF 2) (q : ℕ) {t : ℝ} (ht : t < Tst) (x : M) :
    0 ≤ towerU S Tst Mf q t x :=
  mul_nonneg (pow_nonneg (by linarith) _) (normSq0S_nonneg _ _ _ _)

omit [I.Boundaryless] in
theorem towerCtl_eq_sum (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    {Tst : ℝ} (Mf : ℝ → TF 2) (n : ℕ) {t : ℝ} (ht : t < Tst) (x : M) :
    towerCtl S Tst Mf n t x = ∑ j ∈ Finset.range (n + 1), towerU S Tst Mf j t x :=
  Finset.sum_congr rfl fun j _ => max_eq_left (towerU_nonneg S Mf j ht x)

omit [I.Boundaryless] in
theorem towerU_le_towerCtl (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    {Tst : ℝ} (Mf : ℝ → TF 2) (q : ℕ) {t : ℝ} (ht : t < Tst) (x : M) :
    towerU S Tst Mf q t x ≤ towerCtl S Tst Mf q t x := by
  rw [towerCtl_eq_sum S Mf q ht x, Finset.sum_range_succ]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun j _ => towerU_nonneg S Mf j ht x)

theorem surfaceFlow_towerU_step (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    {Tst : ℝ} (hTT : T ≤ Tst) (Mf : ℝ → TF 2) (Err : (q : ℕ) → ℝ → TF (2 + q)) {t₀ : ℝ}
    (hD : ∀ q : ℕ, ∀ t ∈ Ioo 0 T, ∀ x (v : Fin (2 + q) → TangentSpace I x),
      HasDerivAt (fun s => iterCov (S.family.metric s) 2 (Mf s) q x v)
        ((lapField (S.family.metric t) (2 + q) (iterCov (S.family.metric t) 2 (Mf t) q) +
          Err q t) x v) t)
    (q : ℕ) {KE KR : ℝ}
    (hKE : ∀ t ∈ Ico t₀ T, ∀ x, (2 * (Tst - t)) ^ (q + 4) *
        normSq0S (S.family.metric t) x (2 + q) (Err q t x) ≤ KE * towerCtl S Tst Mf q t x)
    (hKR : ∀ t ∈ Ico t₀ T, ∀ x, (2 * (Tst - t)) ^ 2 * S.scalar t x ^ 2 ≤ KR)
    {t : ℝ} (ht : t ∈ Ioo t₀ T) (ht₀ : 0 < t₀) (x : M) :
    ∃ d : ℝ, HasDerivAt (fun s => towerU S Tst Mf q s x) d t ∧
      d ≤ laplacianAt (flowG S) t (towerU S Tst Mf q t) x +
        (-2 * towerU S Tst Mf (q + 1) t x + ((2 + q) * (1 + |KR|) + 1 + |KE|) *
          ∑ j ∈ Finset.range (q + 1), towerU S Tst Mf j t x) / (2 * (Tst - t)) := by
  have ht' : t ∈ Ioo 0 T := ⟨ht₀.trans ht.1, ht.2⟩
  have htJ : t ∈ Ico t₀ T := ⟨ht.1.le, ht.2⟩
  have hτ : 0 < Tst - t := by linarith [ht.2]
  set g := S.family.metric t with hg
  set ρ := 2 * (Tst - t) with hρdef
  have hρ : 0 < ρ := by positivity
  set Aq := iterCov g 2 (Mf t) q with hAq
  set N := normSq0S g x (2 + q) (Aq x) with hN
  set N1 := normSq0S g x (2 + (q + 1)) (iterCov g 2 (Mf t) (q + 1) x) with hN1
  set iE := inner0S g x (2 + q) (Err q t x) (Aq x) with hiE
  set iL := inner0S g x (2 + q) (lapField g (2 + q) Aq x) (Aq x) with hiL
  set NE := normSq0S g x (2 + q) (Err q t x) with hNE
  set R := S.scalar t x with hR
  set U := towerCtl S Tst Mf q t x with hU
  have hdN := surfaceFlow_normSq0S_hasDerivAt hdim S hS
    (fun s => iterCov (S.family.metric s) 2 (Mf s) q) ht' x _ (hD q t ht' x)
  have h1 : HasDerivAt (fun s => 2 * (Tst - s)) (-2) t := by
    simpa using ((hasDerivAt_id t).const_sub Tst).const_mul 2
  have hdu := (h1.pow (2 + q)).mul hdN
  refine ⟨_, hdu, ?_⟩
  have hlap : laplacianAt (flowG S) t (towerU S Tst Mf q t) x =
      ρ ^ (2 + q) * (2 * iL + 2 * N1) := by
    have hfun : towerU S Tst Mf q t = ρ ^ (2 + q) • fun y => normSq0S g y (2 + q) (Aq y) := by
      funext y; rfl
    have hsm := normSq0S_smooth g Aq
    rw [hfun, laplacianAt_smul (flowG S) t _ (fun y => (hsm y).mdifferentiableAt (by simp))
      (gradientFun_mdiffAt _ hsm x)]
    have hl : laplacianAt (flowG S) t (fun y => normSq0S g y (2 + q) (Aq y)) x =
        ΔG g (⟨fun y => normSq0S g y (2 + q) (Aq y), hsm⟩ : C^∞⟮I, M; ℝ⟯) x :=
      laplacian_levi_eq g hsm x
    rw [hl, laplacian_normSq0S_eq]
    have hle : lapField g (2 + q) Aq x = roughLap0STensor g (iterCov g (2 + q) Aq 2 x) := by
      rw [lapField, metricTraceFirstTwoField_apply]; rfl
    rw [← hle]
    rfl
  rw [hlap]
  have hder : (↑(2 + q) * ρ ^ (2 + q - 1) * -2) * N +
      ρ ^ (2 + q) * (2 * inner0S g x (2 + q)
        ((lapField g (2 + q) Aq + Err q t) x) (Aq x) + ↑(2 + q) * R * N) =
      -2 * (2 + q) * ρ ^ (1 + q) * N + ρ ^ (2 + q) * (2 * iL + 2 * iE + (2 + q) * R * N) := by
    rw [ContMDiffSection.coe_add, Pi.add_apply, inner0S_add_left,
      show 2 + q - 1 = 1 + q by omega]
    push_cast
    ring
  change (↑(2 + q) * ρ ^ (2 + q - 1) * -2) * N +
      ρ ^ (2 + q) * (2 * inner0S g x (2 + q)
        ((lapField g (2 + q) Aq + Err q t) x) (Aq x) + ↑(2 + q) * R * N) ≤ _
  rw [hder]
  have hP : ρ ^ (2 + q) = ρ ^ (1 + q) * ρ := by rw [← pow_succ]; ring_nf
  have hP1 : ρ ^ (2 + (q + 1)) = ρ ^ (2 + q) * ρ := pow_succ ρ (2 + q)
  have hP4 : ρ ^ (q + 4) = ρ ^ (2 + q) * ρ ^ 2 := by rw [← pow_add]; ring_nf
  have huq : towerU S Tst Mf q t x = ρ ^ (2 + q) * N := rfl
  have huq1 : towerU S Tst Mf (q + 1) t x = ρ ^ (2 + q) * ρ * N1 := by
    rw [← hP1]; rfl
  have hsum : ∑ j ∈ Finset.range (q + 1), towerU S Tst Mf j t x = U := by
    rw [hU, towerCtl_eq_sum S Mf q (by linarith [ht.2]) x]
  rw [hsum, huq1]
  have hNn : 0 ≤ N := normSq0S_nonneg _ _ _ _
  have hN1n : 0 ≤ N1 := normSq0S_nonneg _ _ _ _
  have hPn : 0 ≤ ρ ^ (2 + q) := pow_nonneg hρ.le _
  have hUq : ρ ^ (2 + q) * N ≤ U := by
    rw [← huq, hU]; exact towerU_le_towerCtl S Mf q (by linarith [ht.2]) x
  have hU0 : 0 ≤ U := towerCtl_nonneg S Tst Mf q t x
  have hCS : 2 * ρ * iE ≤ ρ ^ 2 * NE + N := by
    have h := two_inner0S_le g x (2 + q) (ρ • Err q t x) (Aq x)
    rw [inner0S_smul_left, normSq0S_smul'] at h
    linarith
  have hEb : ρ ^ (2 + q) * ρ ^ 2 * NE ≤ KE * U := by rw [← hP4]; exact hKE t htJ x
  have hRb : ρ * R ≤ (1 + |KR|) / 2 := by
    have h := hKR t htJ x
    have hsq : 0 ≤ (ρ * R - 1) ^ 2 := sq_nonneg _
    have e1 : (ρ * R - 1) ^ 2 = (ρ * R) ^ 2 - 2 * (ρ * R) + 1 := by ring
    have e2 : ρ ^ 2 * R ^ 2 = (ρ * R) ^ 2 := by ring
    linarith [le_abs_self KR]
  have hT1 : ρ ^ (2 + q) * (2 * ρ * iE) ≤ KE * U + ρ ^ (2 + q) * N := by
    calc ρ ^ (2 + q) * (2 * ρ * iE) ≤ ρ ^ (2 + q) * (ρ ^ 2 * NE + N) :=
          mul_le_mul_of_nonneg_left hCS hPn
      _ = ρ ^ (2 + q) * ρ ^ 2 * NE + ρ ^ (2 + q) * N := by ring
      _ ≤ KE * U + ρ ^ (2 + q) * N := by linarith
  have hT2 : (2 + q) * (ρ * R) * (ρ ^ (2 + q) * N) ≤
      (2 + q) * ((1 + |KR|) / 2) * (ρ ^ (2 + q) * N) := by
    have hq : (0 : ℝ) ≤ 2 + q := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRb hq) (mul_nonneg hPn hNn)
  have hKEU : KE * U ≤ |KE| * U := mul_le_mul_of_nonneg_right (le_abs_self _) hU0
  have key : (-2 * (2 + q) * ρ ^ (1 + q) * N +
      ρ ^ (2 + q) * (2 * iL + 2 * iE + (2 + q) * R * N) -
      ρ ^ (2 + q) * (2 * iL + 2 * N1)) * ρ ≤
      -2 * (ρ ^ (2 + q) * ρ * N1) + ((2 + q) * (1 + |KR|) + 1 + |KE|) * U := by
    have e : (-2 * (2 + q) * ρ ^ (1 + q) * N +
        ρ ^ (2 + q) * (2 * iL + 2 * iE + (2 + q) * R * N) -
        ρ ^ (2 + q) * (2 * iL + 2 * N1)) * ρ =
        -2 * (2 + q) * (ρ ^ (2 + q) * N) + ρ ^ (2 + q) * (2 * ρ * iE) +
          (2 + q) * (ρ * R) * (ρ ^ (2 + q) * N) - 2 * (ρ ^ (2 + q) * ρ * N1) := by
      rw [hP]; ring
    rw [e]
    have hq0 : (0 : ℝ) ≤ 2 + q := by positivity
    set u := ρ ^ (2 + q) * N with hu
    have hu0 : 0 ≤ u := mul_nonneg hPn hNn
    have ha : 0 ≤ (2 + q) * ((1 + |KR|) / 2) + 1 := by positivity
    have hA1 : ((2 + q) * ((1 + |KR|) / 2) + 1) * u ≤ ((2 + q) * ((1 + |KR|) / 2) + 1) * U :=
      mul_le_mul_of_nonneg_left hUq ha
    have hA2 : ((2 + q) * ((1 + |KR|) / 2) + 1) * U ≤ ((2 + q) * (1 + |KR|) + 1) * U := by
      refine mul_le_mul_of_nonneg_right ?_ hU0
      have : 0 ≤ (2 + q) * (1 + |KR|) := mul_nonneg hq0 (by positivity)
      linarith
    have hB : 0 ≤ 2 * (2 + q) * u := by positivity
    have e3 : ((2 + q) * (1 + |KR|) + 1 + |KE|) * U =
        ((2 + q) * (1 + |KR|) + 1) * U + |KE| * U := by ring
    rw [e3]
    have e4 : (2 + q) * ((1 + |KR|) / 2) * u + u =
        ((2 + q) * ((1 + |KR|) / 2) + 1) * u := by ring
    linarith
  have := (le_div_iff₀ hρ).mpr key
  linarith

end Helpers

section Frozen

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M]
  {T : ℝ} {hT : 0 < T}

theorem surfaceFlow_tracelessHess_derivative_decay (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (hscal : ∀ x, 0 < S.scalar 0 x) (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => f q.1 q.2) (Ioo 0 T ×ˢ univ))
    (hfeq : ∀ t ∈ Ioo 0 T, ∀ x,
      ΔG (S.family.metric t) (f t) x = S.scalar t x - 1 / (flowExtinctionTime S - t))
    {a : ℝ → ℝ} (hft : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun s => f s x)
      (S.scalar t x + f t x / (flowExtinctionTime S - t) + a t) t)
    (Mf : ℝ → Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (hM : ∀ t ∈ Ioo 0 T, ∀ x, Mf t x = tracelessHessAt (S.family.metric t) (f t) x)
    {t₀ C₀ c : ℝ} (ht₀ : t₀ ∈ Ioo 0 T) (hc : 0 < c)
    (hdecay : ∀ t ∈ Ico t₀ T, ∀ x,
      (flowExtinctionTime S - t) ^ 2 * normSq0S (S.family.metric t) x 2 (Mf t x) ≤
        C₀ * (flowExtinctionTime S - t) ^ c)
    (hshi : ∀ q : ℕ, ∃ B : ℝ, ∀ t ∈ Ico t₀ T, ∀ x,
      normSq0S (S.family.metric t) x (4 + q)
          (iterCov (S.family.metric t) 4 (metricRm04 (S.family.metric t)) q x) ≤
        B * (flowExtinctionTime S - t) ^ (-(2 + q : ℝ))) :
    ∀ q : ℕ, ∃ C γ : ℝ, 0 < γ ∧ ∀ t ∈ Ico t₀ T, ∀ x,
      (flowExtinctionTime S - t) ^ (2 + q) *
          normSq0S (S.family.metric t) x (2 + q) (iterCov (S.family.metric t) 2 (Mf t) q x) ≤
        C * (flowExtinctionTime S - t) ^ γ := by
  classical
  rcases isEmpty_or_nonempty M with hM0 | hM0
  · intro q
    exact ⟨0, c, hc, fun _ _ x => (IsEmpty.false x).elim⟩
  set Tst := flowExtinctionTime S with hTst
  have hTT : T ≤ Tst := surfaceFlow_le_extinctionTime hT S hS hdim hscal
  have hJ : ∀ t ∈ Ico t₀ T, 0 < Tst - t := fun t ht => by linarith [ht.2]
  have hρJ : ∀ t ∈ Ico t₀ T, 0 ≤ 2 * (Tst - t) := fun t ht => by linarith [hJ t ht]
  have hU0 := towerCtl_nonneg S Tst Mf
  have hUm := towerCtl_mono S Tst Mf
  have hM2 : IterCovCtl (fun t => S.family.metric t) (fun t => 2 * (Tst - t)) (Ico t₀ T)
      (towerCtl S Tst Mf) 2 0 Mf := by
    intro p
    refine ⟨1, fun t ht x => ?_⟩
    rw [one_mul, Nat.zero_add]
    exact towerU_le_towerCtl S Mf p (by linarith [hJ t ht]) x
  set e₀ : ℝ → Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 := fun t => (1 / (Tst - t)) • Mf t -
    (2 : ℝ) • tensor0SFieldSmulByFun (∞ : WithTop ℕ∞) (S.scalar t) (scalarSmoothOfSolution S t)
      (Mf t) with he₀
  have hR := IterCovCtl.scalarField_ctl hdim S hJ hshi
  have he0 : IterCovCtl (fun t => S.family.metric t) (fun t => 2 * (Tst - t)) (Ico t₀ T)
      (towerCtl S Tst Mf) 4 0 e₀ := by
    have h1 := hM2.timeSmul hρJ hU0 (fun t => 1 / (Tst - t)) (L := 2) (fun t ht => by
      have hτ := hJ t ht
      rw [abs_of_pos (one_div_pos.mpr hτ)]
      field_simp
      rfl)
    have h2 := (hR.smulByFun hρJ hU0 hUm (fun t => S.scalar t)
      (fun t => scalarSmoothOfSolution S t) hM2).smul 2
    exact h1.sub hρJ h2
  have h0 : ∀ t ∈ Ioo 0 T, ∀ x (v : Fin 2 → TangentSpace I x),
      HasDerivAt (fun s => Mf s x v) ((lapField (S.family.metric t) 2 (Mf t) + e₀ t) x v) t := by
    intro t ht x v
    refine (surfaceFlow_tracelessHess_tensor_evolution hdim S hS hscal f hf hfeq hft Mf hM t ht
      x v).congr_deriv ?_
    have hl : lapField (S.family.metric t) 2 (Mf t) x =
        roughLap0STensor (S.family.metric t) (iterCov (S.family.metric t) 2 (Mf t) 2 x) := by
      rw [lapField, metricTraceFirstTwoField_apply]; rfl
    rw [ContMDiffSection.coe_add, Pi.add_apply, Tensor0SSpace.add_apply, hl, he₀]
    simp only [ContMDiffSection.coe_sub, ContMDiffSection.coe_smul, Pi.sub_apply, Pi.smul_apply,
      Tensor0SSpace.sub_apply, Tensor0SSpace.smul_apply, tensor0SField_smulByFun_apply,
      smul_eq_mul]
    ring
  have hreg := tracelessHess_iterCov_apply_contMDiffOn S hS f hf Mf hM
  have hD := flow_iterCov_hasDerivAt hdim S hS Mf e₀ hreg h0
  have hE := IterCovCtl.errField_ctl hdim hJ hshi hU0 hUm hM2 he0
  choose KE hKE using fun q => hE q 0
  obtain ⟨KR, hKR⟩ := hR 0
  have hKR' : ∀ t ∈ Ico t₀ T, ∀ x, (2 * (Tst - t)) ^ 2 * S.scalar t x ^ 2 ≤ KR := by
    intro t ht x
    have h := hKR t ht x
    change (2 * (Tst - t)) ^ (2 + 0) * normSq0S (S.family.metric t) x 0
      (Tensor0SField.fromScalarField (∞ : WithTop ℕ∞) (S.scalar t) (scalarSmoothOfSolution S t)
        x) ≤ KR * 1 at h
    rw [normSq0S_fromScalarField, mul_one] at h
    exact h
  have htower : ∀ q, ∀ t ∈ Ioo t₀ T, ∀ x, ∃ d : ℝ,
      HasDerivAt (fun s => towerU S Tst Mf q s x) d t ∧
        d ≤ laplacianAt (flowG S) t (towerU S Tst Mf q t) x +
          (-2 * towerU S Tst Mf (q + 1) t x +
            (fun q : ℕ => (2 + (q : ℝ)) * (1 + |KR|) + 1 + |KE q|) q *
              ∑ j ∈ Finset.range (q + 1), towerU S Tst Mf j t x) / (2 * (Tst - t)) :=
    fun q t ht x => surfaceFlow_towerU_step hdim S hS hTT Mf (errField S Mf e₀) hD q
      (fun t ht x => hKE q t ht x) hKR' ht ht₀.1 x
  have hu : ∀ q, ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => towerU S Tst Mf q p.1 p.2) (Ioo 0 T ×ˢ univ) := fun q =>
    ((contMDiffOn_const.mul (contMDiffOn_const.sub contMDiffOn_fst)).pow (2 + q)).mul
      (tracelessHess_iterCov_normSq_contMDiffOn S hS f hf Mf hM q)
  have hnonneg : ∀ q, ∀ t ∈ Ioo 0 T, ∀ x, 0 ≤ towerU S Tst Mf q t x := fun q t ht x =>
    towerU_nonneg S Mf q (by linarith [ht.2]) x
  have hinit : ∃ K : ℝ, ∀ t ∈ Ico t₀ T, ∀ x, towerU S Tst Mf 0 t x ≤ K * (Tst - t) ^ c := by
    refine ⟨4 * C₀, fun t ht x => ?_⟩
    have h := hdecay t ht x
    change (2 * (Tst - t)) ^ 2 * normSq0S (S.family.metric t) x 2 (Mf t x) ≤ _
    calc (2 * (Tst - t)) ^ 2 * normSq0S (S.family.metric t) x 2 (Mf t x)
        = 4 * ((Tst - t) ^ 2 * normSq0S (S.family.metric t) x 2 (Mf t x)) := by ring
      _ ≤ 4 * (C₀ * (Tst - t) ^ c) := by linarith
      _ = 4 * C₀ * (Tst - t) ^ c := by ring
  have hdec := flow_linear_tower_decay S hTT hc.le ht₀ (towerU S Tst Mf) hu hnonneg _ htower hinit
  intro q
  obtain ⟨K, hK⟩ := hdec q
  refine ⟨K / 2 ^ (2 + q), c, hc, fun t ht x => ?_⟩
  have h := hK t ht x
  have h2 : (0 : ℝ) < 2 ^ (2 + q) := by positivity
  have e : towerU S Tst Mf q t x = 2 ^ (2 + q) * ((Tst - t) ^ (2 + q) *
      normSq0S (S.family.metric t) x (2 + q) (iterCov (S.family.metric t) 2 (Mf t) q x)) := by
    rw [towerU, mul_pow]; ring
  rw [e] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ h2]
  linarith

end Frozen

end GC.Geometry
