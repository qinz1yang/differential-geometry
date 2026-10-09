import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5CommutatorIdentity
import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5CommutatorTime

/-!
# The heat defect of the iterated covariant derivatives of a tensor along a surface flow

Chapter 7, surface lemma U1, route (a), step a5.2 (iii) (lane U1C2; design D18,
`docs/geometrization/handoffs/20261004-design-u1-a5-potential-gauge.md`, review 18 §2).

Along a two-dimensional Ricci flow `g(t)` let `A(t)` be a family of covariant 2-tensor fields
whose components evolve by `∂ₜ A = Δ A + e₀(t)`. Then `∂ₜ ∇^q A = Δ ∇^q A + errField q` with
* `errField 0 = e₀`,
* `errField (q + 1) = ∇ (errField q) - gammaField (∇^q A) - lapCommField (∇^q A)`,

where `gammaField` is the action of the variation `Γ̇ = -½ (dR ⊗ id + id ⊗ dR - g ⊗ ∇R)` of
the Levi-Civita connection (U1C's `flow_covStep_hasDerivAt` and P8b's
`surfaceFlow_leviCivitaVariation_pair`) and `lapCommField` is the spatial commutator
(`lapField_covStep`). This is `flow_iterCov_hasDerivAt`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Tensor.RSTensor
open Set
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {T : ℝ} {hT : 0 < T}

local notation "TF " k => Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
  (n := (∞ : WithTop ℕ∞)) k

def errField (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (A e₀ : ℝ → TF 2) : (q : ℕ) → ℝ → TF (2 + q)
  | 0 => e₀
  | q + 1 => fun t =>
    covStep (S.family.metric t) (2 + q) (errField S A e₀ q t) -
      gammaField (S.family.metric t) (scalarSmoothOfSolution S t) (2 + q)
        (iterCov (S.family.metric t) 2 (A t) q) -
      lapCommField (S.family.metric t) (2 + q) (iterCov (S.family.metric t) 2 (A t) q)

theorem surfaceFlow_slotVariation_eq_gammaField (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    {t : ℝ} (ht : t ∈ Ioo 0 T) {k : ℕ} (B : TF k) (x : M) (w : TangentSpace I x)
    (v : Fin k → TangentSpace I x) :
    ∑ i, B x (Function.update v i (leviCivitaVariation S.family.metric t x (v i) w)) =
      gammaField (S.family.metric t) (scalarSmoothOfSolution S t) k B x (Fin.cons w v) :=
  slotVariation_eq_gammaField (S.family.metric t) (scalarSmoothOfSolution S t) B x
    (fun a b => leviCivitaVariation S.family.metric t x a b) (fun a b z =>
      surfaceFlow_leviCivitaVariation_pair hdim S hS ht x b a z) w v

theorem flow_iterCov_hasDerivAt (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (A e₀ : ℝ → TF 2)
    (hreg : ∀ (q : ℕ) (V : Fin (2 + q) →
        ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => iterCov (S.family.metric p.1) 2 (A p.1) q p.2 (fun i => V i p.2))
        (Ioo 0 T ×ˢ univ))
    (h0 : ∀ t ∈ Ioo 0 T, ∀ x (v : Fin 2 → TangentSpace I x),
      HasDerivAt (fun s => A s x v) ((lapField (S.family.metric t) 2 (A t) + e₀ t) x v) t) :
    ∀ (q : ℕ), ∀ t ∈ Ioo 0 T, ∀ x (v : Fin (2 + q) → TangentSpace I x),
      HasDerivAt (fun s => iterCov (S.family.metric s) 2 (A s) q x v)
        ((lapField (S.family.metric t) (2 + q) (iterCov (S.family.metric t) 2 (A t) q) +
          errField S A e₀ q t) x v) t := by
  intro q
  induction q with
  | zero => exact h0
  | succ q ih =>
    intro t ht x v
    have h := flow_covStep_hasDerivAt S hS (fun s => iterCov (S.family.metric s) 2 (A s) q)
      (fun s => lapField (S.family.metric s) (2 + q) (iterCov (S.family.metric s) 2 (A s) q) +
        errField S A e₀ q s) (hreg q) ih ht x (v 0) (Fin.tail v)
    rw [Fin.cons_self_tail] at h
    refine h.congr_deriv ?_
    rw [covStep_add, ContMDiffSection.coe_add, Pi.add_apply, Tensor0SSpace.add_apply,
      surfaceFlow_slotVariation_eq_gammaField hdim S hS ht, Fin.cons_self_tail]
    have hlap := lapField_covStep (S.family.metric t) (iterCov (S.family.metric t) 2 (A t) q)
    have e1 : lapField (S.family.metric t) (2 + (q + 1)) (iterCov (S.family.metric t) 2 (A t)
        (q + 1)) = lapField (S.family.metric t) (2 + q + 1)
          (covStep (S.family.metric t) (2 + q) (iterCov (S.family.metric t) 2 (A t) q)) := rfl
    rw [e1, hlap]
    change _ = (covStep (S.family.metric t) (2 + q) (lapField (S.family.metric t) (2 + q)
        (iterCov (S.family.metric t) 2 (A t) q)) +
      lapCommField (S.family.metric t) (2 + q) (iterCov (S.family.metric t) 2 (A t) q) +
      (covStep (S.family.metric t) (2 + q) (errField S A e₀ q t) -
        gammaField (S.family.metric t) (scalarSmoothOfSolution S t) (2 + q)
          (iterCov (S.family.metric t) 2 (A t) q) -
        lapCommField (S.family.metric t) (2 + q) (iterCov (S.family.metric t) 2 (A t) q))) x v
    simp only [ContMDiffSection.coe_add, ContMDiffSection.coe_sub, Pi.add_apply, Pi.sub_apply,
      Tensor0SSpace.add_apply, Tensor0SSpace.sub_apply]
    ring

namespace IterCovCtl

variable {g : ℝ → SmoothRiemannianMetric I M} {ρ : ℝ → ℝ} {J : Set ℝ} {U : ℕ → ℝ → M → ℝ}

omit [I.Boundaryless] in
theorem congr_w {w w' m k : ℕ} {A : ℝ → TF k} (h : w = w') (hA : IterCovCtl g ρ J U w m A) :
    IterCovCtl g ρ J U w' m A := h ▸ hA

omit [I.Boundaryless] in
theorem iter {w m k : ℕ} {A : ℝ → TF k} (hA : IterCovCtl g ρ J U w m A) :
    ∀ q : ℕ, IterCovCtl g ρ J U (w + q) (m + q)
      (fun t => CheegerGromovCompactness.iterCov (g t) k (A t) q)
  | 0 => hA
  | q + 1 => (iter hA q).cov

omit [I.Boundaryless] [T2Space M] in
theorem normSq0S_metricTensorField_le (g : SmoothRiemannianMetric I M) (x : M) :
    normSq0S g x 2 (metricTensorField g x) ≤ (Module.finrank ℝ E : ℝ) ^ 2 := by
  classical
  obtain ⟨b, hb⟩ := exists_orthonormal_basis g x
  rw [normSq0S_identity_eq_sum_sq g x 2 b (metricInverseInBasis_of_orthonormal g b hb)]
  calc ∑ w : Fin 2 → Fin (Module.finrank ℝ (TangentSpace I x)), component0S b
        (metricTensorField g x) w ^ 2
      ≤ ∑ _w : Fin 2 → Fin (Module.finrank ℝ (TangentSpace I x)), (1 : ℝ) := by
        refine Finset.sum_le_sum fun w _ => ?_
        rw [component0S_apply, metricTensorField_apply, hb]
        split_ifs <;> norm_num
    _ = (Module.finrank ℝ E : ℝ) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin]
        simp only [nsmul_eq_mul, mul_one, Nat.cast_pow]
        rfl

omit [I.Boundaryless] in
theorem metricTensorField_ctl :
    IterCovCtl g ρ J (fun _ _ _ => (1 : ℝ)) 0 0 (fun t => metricTensorField (g t)) := by
  intro p
  refine ⟨(Module.finrank ℝ E : ℝ) ^ 2, fun t _ x => ?_⟩
  rcases p with _ | p
  · change ρ t ^ (0 + 0) * normSq0S (g t) x (2 + 0) (metricTensorField (g t) x) ≤ _ * 1
    simpa using normSq0S_metricTensorField_le (g t) x
  · rw [CheegerGromovCompactness.iterCov_metric_zero]
    have h0 : normSq0S (g t) x (2 + (p + 1)) ((0 : TF (2 + (p + 1))) x) = 0 := by
      rw [normSq0S_eq_zero_iff]; rfl
    rw [h0]
    simp only [mul_zero, mul_one]
    positivity

omit [I.Boundaryless] in
theorem rm04_ctl {Tst : ℝ} (hJ : ∀ t ∈ J, 0 < Tst - t)
    (hshi : ∀ p : ℕ, ∃ B : ℝ, ∀ t ∈ J, ∀ x,
      normSq0S (g t) x (4 + p)
          (CheegerGromovCompactness.iterCov (g t) 4 (metricRm04 (g t)) p x) ≤
        B * (Tst - t) ^ (-(2 + p : ℝ))) :
    IterCovCtl g (fun t => 2 * (Tst - t)) J (fun _ _ _ => (1 : ℝ)) 2 0
      (fun t => metricRm04 (g t)) := by
  intro p
  obtain ⟨B, hB⟩ := hshi p
  refine ⟨2 ^ (2 + p) * B, fun t ht x => ?_⟩
  have hτ := hJ t ht
  have hpow : (Tst - t) ^ (2 + p) * (Tst - t) ^ (-(2 + p : ℝ)) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hτ]
    push_cast
    simp
  have hb := hB t ht x
  calc (2 * (Tst - t)) ^ (2 + p) * normSq0S (g t) x (4 + p)
        (CheegerGromovCompactness.iterCov (g t) 4 (metricRm04 (g t)) p x)
      = 2 ^ (2 + p) * ((Tst - t) ^ (2 + p) * normSq0S (g t) x (4 + p)
          (CheegerGromovCompactness.iterCov (g t) 4 (metricRm04 (g t)) p x)) := by
        rw [mul_pow]; ring
    _ ≤ 2 ^ (2 + p) * ((Tst - t) ^ (2 + p) * (B * (Tst - t) ^ (-(2 + p : ℝ)))) := by
        gcongr
    _ = 2 ^ (2 + p) * B * 1 := by rw [← hpow]; ring

theorem scalarField_ctl (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) {J : Set ℝ}
    {Tst : ℝ} (hJ : ∀ t ∈ J, 0 < Tst - t)
    (hshi : ∀ p : ℕ, ∃ B : ℝ, ∀ t ∈ J, ∀ x,
      normSq0S (S.family.metric t) x (4 + p)
          (CheegerGromovCompactness.iterCov (S.family.metric t) 4
            (metricRm04 (S.family.metric t)) p x) ≤
        B * (Tst - t) ^ (-(2 + p : ℝ))) :
    IterCovCtl (fun t => S.family.metric t) (fun t => 2 * (Tst - t)) J (fun _ _ _ => (1 : ℝ)) 2 0
      (fun t => Tensor0SField.fromScalarField (∞ : WithTop ℕ∞) (S.scalar t)
        (scalarSmoothOfSolution S t)) := by
  have hρ : ∀ t ∈ J, 0 ≤ 2 * (Tst - t) := fun t ht => by linarith [hJ t ht]
  have h := ((((rm04_ctl hJ hshi).domDomCongr
    (frontExtendEquiv (swap01 1) : Fin 4 ≃ Fin 4)).trace hρ (s := 2)).trace hρ (s := 0)).smul (-1)
  refine h.congr fun t _ => ?_
  exact (fromScalarField_eq_neg_trace_rm04 hdim (S.family.metric t)
    (scalarSmoothOfSolution S t)).symm

theorem gradField_ctl (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) {J : Set ℝ}
    {Tst : ℝ} (hJ : ∀ t ∈ J, 0 < Tst - t)
    (hshi : ∀ p : ℕ, ∃ B : ℝ, ∀ t ∈ J, ∀ x,
      normSq0S (S.family.metric t) x (4 + p)
          (CheegerGromovCompactness.iterCov (S.family.metric t) 4
            (metricRm04 (S.family.metric t)) p x) ≤
        B * (Tst - t) ^ (-(2 + p : ℝ))) :
    IterCovCtl (fun t => S.family.metric t) (fun t => 2 * (Tst - t)) J (fun _ _ _ => (1 : ℝ)) 3 0
      (fun t => gradField (S.family.metric t) (scalarSmoothOfSolution S t)) :=
  (scalarField_ctl hdim S hJ hshi).cov.one_m.congr fun _ _ => rfl

section Flow

variable {S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)} {J : Set ℝ}
  {Tst : ℝ} {U : ℕ → ℝ → M → ℝ}

theorem gammaField_ctl (hdim : Module.finrank ℝ E = 2) (hJ : ∀ t ∈ J, 0 < Tst - t)
    (hshi : ∀ p : ℕ, ∃ B : ℝ, ∀ t ∈ J, ∀ x,
      normSq0S (S.family.metric t) x (4 + p)
          (CheegerGromovCompactness.iterCov (S.family.metric t) 4
            (metricRm04 (S.family.metric t)) p x) ≤
        B * (Tst - t) ^ (-(2 + p : ℝ)))
    (hU0 : ∀ n t x, 0 ≤ U n t x) (hUm : ∀ n t x, U n t x ≤ U (n + 1) t x)
    {w m k : ℕ} {B : ℝ → TF k}
    (hB : IterCovCtl (fun t => S.family.metric t) (fun t => 2 * (Tst - t)) J U w m B) :
    IterCovCtl (fun t => S.family.metric t) (fun t => 2 * (Tst - t)) J U (3 + w) m
      (fun t => gammaField (S.family.metric t) (scalarSmoothOfSolution S t) k (B t)) := by
  have hρ : ∀ t ∈ J, 0 ≤ 2 * (Tst - t) := fun t ht => by linarith [hJ t ht]
  have hd := gradField_ctl hdim S hJ hshi
  have hP := hd.product hρ hU0 hUm hB
  have hgd := (metricTensorField_ctl (g := fun t => S.family.metric t)
    (ρ := fun t => 2 * (Tst - t)) (J := J)).product hρ (fun _ _ _ => zero_le_one)
      (fun _ _ _ => le_rfl) hd
  have hQ := (hgd.product hρ hU0 hUm hB).congr_w (show 0 + 3 + w = 3 + w by omega)
  have hsum := IterCovCtl.sum hρ (Finset.univ : Finset (Fin k)) (A := fun i t =>
      Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (finCongr (Nat.add_comm 1 k))
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            (gradField (S.family.metric t) (scalarSmoothOfSolution S t)) (B t)) +
        Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (gammaPermB i)
          (tensor0SFieldProduct (∞ : WithTop ℕ∞)
            (gradField (S.family.metric t) (scalarSmoothOfSolution S t)) (B t)) -
        metricTraceFirstTwoField (S.family.metric t)
          (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (gammaPermC i)
            (tensor0SFieldProduct (∞ : WithTop ℕ∞)
              (tensor0SFieldProduct (∞ : WithTop ℕ∞) (metricTensorField (S.family.metric t))
                (gradField (S.family.metric t) (scalarSmoothOfSolution S t))) (B t))))
    (fun i _ => ((hP.domDomCongr _).add hρ (hP.domDomCongr _)).sub hρ
      ((hQ.domDomCongr (gammaPermC i)).trace hρ (s := k + 1)))
  exact (hsum.smul (-(1 / 2 : ℝ))).congr fun _ _ => rfl

theorem ricciSwap_ctl (hdim : Module.finrank ℝ E = 2) (hJ : ∀ t ∈ J, 0 < Tst - t)
    (hshi : ∀ p : ℕ, ∃ B : ℝ, ∀ t ∈ J, ∀ x,
      normSq0S (S.family.metric t) x (4 + p)
          (CheegerGromovCompactness.iterCov (S.family.metric t) 4
            (metricRm04 (S.family.metric t)) p x) ≤
        B * (Tst - t) ^ (-(2 + p : ℝ)))
    (hU0 : ∀ n t x, 0 ≤ U n t x) (hUm : ∀ n t x, U n t x ≤ U (n + 1) t x)
    {w m k : ℕ} {B : ℝ → TF k}
    (hB : IterCovCtl (fun t => S.family.metric t) (fun t => 2 * (Tst - t)) J U w m B) :
    IterCovCtl (fun t => S.family.metric t) (fun t => 2 * (Tst - t)) J U (2 + w) m
      (fun t => ricciSwapField (S.family.metric t) k (B t)) := by
  have hρ : ∀ t ∈ J, 0 ≤ 2 * (Tst - t) := fun t ht => by linarith [hJ t ht]
  have hP := ((metricTensorField_ctl (g := fun t => S.family.metric t)
    (ρ := fun t => 2 * (Tst - t)) (J := J)).product hρ hU0 hUm hB).congr_w
      (show 0 + w = w by omega)
  have hsum := IterCovCtl.sum hρ (Finset.univ : Finset (Fin k)) (A := fun q t =>
      Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (curvSwapPermX q)
          (tensor0SFieldProduct (∞ : WithTop ℕ∞) (metricTensorField (S.family.metric t)) (B t)) -
        Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (curvSwapPermY q)
          (tensor0SFieldProduct (∞ : WithTop ℕ∞) (metricTensorField (S.family.metric t)) (B t)))
    (fun q _ => (hP.domDomCongr _).sub hρ (hP.domDomCongr _))
  have hc := (scalarField_ctl hdim S hJ hshi).smulByFun hρ hU0 hUm
    (fun t => S.scalar t) (fun t => scalarSmoothOfSolution S t) (hsum.smul (-(1 / 2 : ℝ)))
  refine hc.congr fun t _ => ?_
  exact (ricciSwapField_eq_of_finrank_two hdim (S.family.metric t)
    (scalarSmoothOfSolution S t) (B t)).symm

theorem lapComm_ctl (hdim : Module.finrank ℝ E = 2) (hJ : ∀ t ∈ J, 0 < Tst - t)
    (hshi : ∀ p : ℕ, ∃ B : ℝ, ∀ t ∈ J, ∀ x,
      normSq0S (S.family.metric t) x (4 + p)
          (CheegerGromovCompactness.iterCov (S.family.metric t) 4
            (metricRm04 (S.family.metric t)) p x) ≤
        B * (Tst - t) ^ (-(2 + p : ℝ)))
    (hU0 : ∀ n t x, 0 ≤ U n t x) (hUm : ∀ n t x, U n t x ≤ U (n + 1) t x)
    {w m k : ℕ} {B : ℝ → TF k}
    (hB : IterCovCtl (fun t => S.family.metric t) (fun t => 2 * (Tst - t)) J U w m B) :
    IterCovCtl (fun t => S.family.metric t) (fun t => 2 * (Tst - t)) J U (w + 3) (m + 1)
      (fun t => lapCommField (S.family.metric t) k (B t)) := by
  have hρ : ∀ t ∈ J, 0 ≤ 2 * (Tst - t) := fun t ht => by linarith [hJ t ht]
  have h1 := ((ricciSwap_ctl hdim hJ hshi hU0 hUm hB).cov.trace hρ (s := k + 1)).congr_w
    (show 2 + w + 1 = w + 3 by omega)
  have h2 := (((ricciSwap_ctl hdim hJ hshi hU0 hUm hB.cov).domDomCongr
    (frontExtendEquiv (swap01 k))).trace hρ (s := k + 1)).congr_w
      (show 2 + (w + 1) = w + 3 by omega)
  exact (h1.add hρ h2).congr fun _ _ => rfl

theorem errField_ctl (hdim : Module.finrank ℝ E = 2) (hJ : ∀ t ∈ J, 0 < Tst - t)
    (hshi : ∀ p : ℕ, ∃ B : ℝ, ∀ t ∈ J, ∀ x,
      normSq0S (S.family.metric t) x (4 + p)
          (CheegerGromovCompactness.iterCov (S.family.metric t) 4
            (metricRm04 (S.family.metric t)) p x) ≤
        B * (Tst - t) ^ (-(2 + p : ℝ)))
    (hU0 : ∀ n t x, 0 ≤ U n t x) (hUm : ∀ n t x, U n t x ≤ U (n + 1) t x)
    {A e₀ : ℝ → TF 2}
    (hA : IterCovCtl (fun t => S.family.metric t) (fun t => 2 * (Tst - t)) J U 2 0 A)
    (he : IterCovCtl (fun t => S.family.metric t) (fun t => 2 * (Tst - t)) J U 4 0 e₀) :
    ∀ q : ℕ, IterCovCtl (fun t => S.family.metric t) (fun t => 2 * (Tst - t)) J U (q + 4) q
      (errField S A e₀ q)
  | 0 => he
  | q + 1 => by
    have hρ : ∀ t ∈ J, 0 ≤ 2 * (Tst - t) := fun t ht => by linarith [hJ t ht]
    have hq := errField_ctl hdim hJ hshi hU0 hUm hA he q
    have hAq := hA.iter q
    have h1 := hq.cov.congr_w (show q + 4 + 1 = q + 1 + 4 by omega)
    have h2 := ((gammaField_ctl hdim hJ hshi hU0 hUm hAq).mono_m hU0 hUm
      (show 0 + q ≤ q + 1 by omega)).congr_w (show 3 + (2 + q) = q + 1 + 4 by omega)
    have h3 := ((lapComm_ctl hdim hJ hshi hU0 hUm hAq).mono_m hU0 hUm
      (show 0 + q + 1 ≤ q + 1 by omega)).congr_w (show 2 + q + 3 = q + 1 + 4 by omega)
    exact ((h1.sub hρ h2).sub hρ h3).congr fun _ _ => rfl

end Flow

end IterCovCtl

end GC.Geometry
