import DifferentialGeometry.Analysis.Elliptic.Euclidean.RayleighMinimizer_EG
import DifferentialGeometry.Analysis.Elliptic.Euclidean.LaplaceCoefficient
import DifferentialGeometry.Analysis.Elliptic.Euclidean.Regularity.HigherOrder
import DifferentialGeometry.Analysis.Elliptic.Euclidean.Restriction
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.Local
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Iterated
import DifferentialGeometry.Analysis.Integration.Measure.ContinuousRepresentative
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Laplacian
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Integrability
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.ClassicalDivergence
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WitnessCongruence
import DifferentialGeometry.Analysis.Elliptic.Euclidean.WeakFormulation

/-!
# Interior regularity of weak solutions of `-Δu = ψ u` (S-W-EIG, G2)

`H¹` weak solutions of `∫⟨∇u,∇v⟩ = ∫ ψ u v` with `ψ` smooth near `closure Ω` lie in `Hᵏ_loc`
for all `k` (iterating `memWkp_add_two_of_bilinFormOfCoeff_eq_integral` and
`MemWkp.mul_contDiffOn`), hence have a `C^∞` representative, which solves `Δũ = -ψ ũ` pointwise.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology RealInnerProductSpace InnerProductSpace ContDiff

namespace DeGiorgi
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.EuclideanIteratedEmbedding

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The Laplacian form `⟨∇u, ∇v⟩` as a smooth elliptic bilinear form on the whole space. -/
def identityForm_EG : SmoothEllipticBilinearForm d (Set.univ : Set E) where
  a := fun _ => 1
  c := fun _ => 0
  symm := fun _ i j => by simp [Matrix.one_apply, eq_comm]
  smooth_a := fun i j => contDiff_const
  smooth_c := contDiff_const
  lam := 1
  capLam := 1
  ellipticity_pos := one_pos
  ellipticity_le_upper := le_rfl
  coercive := fun x _ ξ => by
    rw [matMulE_one, real_inner_self_eq_norm_sq, one_mul]

/-- Restriction of the weak Euler–Lagrange equation to a smaller open set. -/
theorem weak_restrict_EG {Ω W : Set E} (hΩ : IsOpen Ω) (hW : IsOpen W) (hsub : W ⊆ Ω)
    {f u : E → ℝ} (hu : MemW1pWitness 2 u Ω)
    (hweak : ∀ v, MemH01 v Ω → ∀ hv : MemW1pWitness 2 v Ω,
      (∫ x in Ω, ⟪hu.weakGrad x, hv.weakGrad x⟫_ℝ) = ∫ x in Ω, f x * v x) :
    ∀ v, MemH01 v W → ∀ hv : MemW1pWitness 2 v W,
      bilinFormOfCoeff (EllipticCoeff.identity d W) (hu.restrict hW hsub) hv =
        ∫ x in W, f x * v x := by
  intro v hv0 hv
  have h := bilinFormOfCoeff_restrict_eq_integral (A := EllipticCoeff.identity d Ω) hΩ hW hsub hu
    (fun z hz0 hz => by rw [bilinFormOfCoeff_identity]; exact hweak z hz0 hz) hv0 hv
  exact h

theorem memWkp_step_EG {Ω U : Set E} (hΩ : IsOpen Ω) (hU : IsOpen U) (hΩc : IsCompact (closure Ω))
    (hΩU : closure Ω ⊆ U) {ψ : E → ℝ} (hψ : ContDiffOn ℝ (⊤ : ℕ∞) ψ U) {u : E → ℝ}
    (hu : MemW1pWitness 2 u Ω) (k : ℕ) (hk : MemWkp k 2 u Ω)
    (hweak : ∀ v, MemH01 v Ω → ∀ hv : MemW1pWitness 2 v Ω,
      bilinFormOfCoeff (EllipticCoeff.identity d Ω) hu hv = ∫ x in Ω, (ψ x * u x) * v x)
    {V : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω) :
    MemWkp (k + 2) 2 u V := by
  have hf : MemWkp k 2 (fun x => ψ x * u x) Ω :=
    MemWkp.mul_contDiffOn (by norm_num) hΩ hU hΩc hΩU hψ hk
  exact memWkp_add_two_of_bilinFormOfCoeff_eq_integral k hΩ hV hVc hVΩ
    (A := EllipticCoeff.identity d Ω) hu hf hweak identityForm_EG (rho := 1) one_ne_zero
    (fun x _ i j => by simp only [identityForm_EG, one_mul]; rfl)

theorem memWkp_all_EG {Ω U : Set E} (hΩ : IsOpen Ω) (hU : IsOpen U) (hΩU : closure Ω ⊆ U)
    {ψ : E → ℝ} (hψ : ContDiffOn ℝ (⊤ : ℕ∞) ψ U) {u : E → ℝ} (hu : MemW1pWitness 2 u Ω)
    (hweak : ∀ v, MemH01 v Ω → ∀ hv : MemW1pWitness 2 v Ω,
      (∫ x in Ω, ⟪hu.weakGrad x, hv.weakGrad x⟫_ℝ) = ∫ x in Ω, (ψ x * u x) * v x) :
    ∀ k : ℕ, ∀ V : Set E, IsOpen V → IsCompact (closure V) → closure V ⊆ Ω →
      MemWkp k 2 u V := by
  have hP : ∀ k : ℕ,
      (∀ V : Set E, IsOpen V → IsCompact (closure V) → closure V ⊆ Ω → MemWkp k 2 u V) ∧
      (∀ V : Set E, IsOpen V → IsCompact (closure V) → closure V ⊆ Ω →
        MemWkp (k + 1) 2 u V) := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun V hV hVc hVΩ => ?_, fun V hV hVc hVΩ => ?_⟩
      · exact hu.memLp.mono_measure (Measure.restrict_mono (subset_closure.trans hVΩ) le_rfl)
      · exact MemWkp.mono_set (by norm_num) hV (subset_closure.trans hVΩ)
          (MemWkp.one_iff_memW1p.mpr hu.memW1p)
    | succ k ih =>
      refine ⟨ih.2, fun V hV hVc hVΩ => ?_⟩
      obtain ⟨V', hV'o, hVV', hV'Ω, hV'c⟩ := exists_open_between_and_isCompact_closure hVc hΩ hVΩ
      have hsub : V' ⊆ Ω := subset_closure.trans hV'Ω
      exact memWkp_step_EG hV'o hU hV'c (hV'Ω.trans (subset_closure.trans hΩU)) hψ
        (hu.restrict hV'o hsub) k
        (ih.1 V' hV'o hV'c hV'Ω) (weak_restrict_EG hΩ hV'o hsub hu hweak) hV hVc hVV'
  exact fun k => (hP k).1

omit [NeZero d] in
theorem exists_contDiffOn_rep_EG {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hall : ∀ k : ℕ, ∀ V : Set E, IsOpen V → IsCompact (closure V) → closure V ⊆ Ω →
      MemWkp k 2 u V) :
    ∃ v : E → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) v Ω ∧ u =ᵐ[volume.restrict Ω] v := by
  have hlocal : ∀ x ∈ Ω, ∃ (U : Set E) (f : E → ℝ), IsOpen U ∧ x ∈ U ∧ U ⊆ Ω ∧
      ContDiffOn ℝ (⊤ : ℕ∞) f U ∧ f =ᵐ[volume.restrict U] u := by
    intro x hx
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hΩ x hx
    have hcl : closure (Metric.ball x (r / 2)) ⊆ Ω :=
      (Metric.closure_ball_subset_closedBall.trans
        (Metric.closedBall_subset_ball (by linarith))).trans hsub
    have hcpt : IsCompact (closure (Metric.ball x (r / 2))) :=
      (isCompact_closedBall x (r / 2)).of_isClosed_subset isClosed_closure
        Metric.closure_ball_subset_closedBall
    obtain ⟨f, hf, huf⟩ :=
      exists_contDiffOn_ae_eq_of_forall_memWkp_two
        Metric.isOpen_ball (fun k => hall k _ Metric.isOpen_ball hcpt hcl)
    exact ⟨Metric.ball x (r / 2), f, Metric.isOpen_ball, Metric.mem_ball_self (half_pos hr),
      (Metric.ball_subset_ball (by linarith)).trans hsub, hf, huf.symm⟩
  obtain ⟨v, hvc, hvu⟩ :=
    MeasureTheory.exists_continuousOn_ae_eq_of_locally_continuousOn_ae_eq volume
      (fun x hx => by
        obtain ⟨U, f, hU, hxU, hUΩ, hf, hfu⟩ := hlocal x hx
        exact ⟨U, f, hU, hxU, hUΩ, hf.continuousOn, hfu⟩)
  refine ⟨v, ?_, hvu.symm⟩
  apply contDiffOn_of_locally_contDiffOn
  intro x hx
  obtain ⟨U, f, hU, hxU, hUΩ, hf, hfu⟩ := hlocal x hx
  have hvuU : v =ᵐ[volume.restrict U] u :=
    hvu.filter_mono (MeasureTheory.ae_mono (Measure.restrict_mono hUΩ le_rfl))
  have heq : EqOn v f U := Measure.eqOn_open_of_ae_eq
    (hvuU.trans hfu.symm) hU
    (hvc.mono hUΩ) hf.continuousOn
  exact ⟨U, hU, hxU, (hf.mono inter_subset_right).congr (fun y hy => heq hy.2)⟩

theorem classical_equation_EG {Ω : Set E} (hΩ : IsOpen Ω) {ψ : E → ℝ} (hψm : Measurable ψ)
    (hψc : ContinuousOn ψ Ω) {B : ℝ} (hψB : ∀ x ∈ Ω, |ψ x| ≤ B) {u ũ : E → ℝ}
    (hu : MemW1pWitness 2 u Ω) (hũ : ContDiffOn ℝ (⊤ : ℕ∞) ũ Ω)
    (huũ : ũ =ᵐ[volume.restrict Ω] u)
    (hweak : ∀ v, MemH01 v Ω → ∀ hv : MemW1pWitness 2 v Ω,
      (∫ x in Ω, ⟪hu.weakGrad x, hv.weakGrad x⟫_ℝ) = ∫ x in Ω, (ψ x * u x) * v x) :
    ∀ x ∈ Ω, Laplacian.laplacian ũ x = -(ψ x * ũ x) := by
  have hψae : ∀ᵐ x ∂(volume.restrict Ω), |ψ x| ≤ B :=
    ae_restrict_of_forall_mem hΩ.measurableSet hψB
  have hf : MemLp (fun x => ψ x * u x) 2 (volume.restrict Ω) :=
    memLp_weight_mul_EG hψm hψae hu.memLp
  have hweak' : ∀ v, MemH01 v Ω → ∀ hv : MemW1pWitness 2 v Ω,
      bilinFormOfCoeff (EllipticCoeff.identity d Ω) hu hv = ∫ x in Ω, (ψ x * u x) * v x := by
    intro v hv0 hv
    rw [bilinFormOfCoeff_identity]
    exact hweak v hv0 hv
  have hdiv := (bilinFormOfCoeff_eq_integral_iff_hasWeakDiv hΩ hu hf).mp hweak'
  let hũw : MemW1pWitness 2 ũ Ω := hu.congr huũ.symm
  have hgrad := hũw.weakGrad_ae_eq_smoothGradField (by norm_num) hΩ (hũ.of_le (by norm_cast))
  have hdiv' : HasWeakDiv (fun x => -(ψ x * ũ x)) (smoothGradField ũ) Ω := by
    refine hdiv.congr_ae ?_ ?_
    · filter_upwards [huũ] with x hx
      rw [hx]
    · filter_upwards [hgrad] with x hx
      change matMulE (1 : Matrix (Fin d) (Fin d) ℝ) (hu.weakGrad x) = _
      rw [matMulE_one]
      exact hx
  have hF : ∀ i : Fin d, ContDiffOn ℝ 1 (fun x => smoothGradField ũ x i) Ω := by
    intro i
    change ContDiffOn ℝ 1 (fun x => fderiv ℝ ũ x (EuclideanSpace.single i 1)) Ω
    have hũ2 : ContDiffOn ℝ 2 ũ Ω := hũ.of_le (by norm_cast)
    exact (hũ2.fderiv_of_isOpen (m := 1) hΩ (by norm_num)).clm_apply contDiffOn_const
  have hcont : ContinuousOn (fun x => -(ψ x * ũ x)) Ω :=
    (hψc.mul hũ.continuousOn).neg
  have heq := hdiv'.eqOn_sum_fderiv hΩ hcont hF
  intro x hx
  rw [laplacian_eq_sum_euclidean_fderiv ((hũ.contDiffAt (hΩ.mem_nhds hx)).of_le (by norm_cast))]
  exact (heq hx).symm

end DeGiorgi
