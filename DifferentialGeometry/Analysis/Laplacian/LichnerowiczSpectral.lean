import DifferentialGeometry.Analysis.Laplacian.Lichnerowicz
import DifferentialGeometry.Analysis.Laplacian.Spectral.EigenBasis
import DifferentialGeometry.Analysis.HeatEquation.Semigroup
import DifferentialGeometry.Analysis.HeatEquation.SmoothingUnconditional

/-!
# Lichnerowicz inequality at the spectral level

For a closed Riemannian manifold `(M, g)` of dimension `n ≥ 2` satisfying
`Ric ≥ (n - 1) K g` with `K > 0`, every strictly positive eigenvalue of the
variational Laplacian satisfies `λ ≥ n K`. The user-facing theorem accepts a
generic basis index `i = ⟨μ, k⟩` for the spectral eigenbasis assembled in
`Analysis/Laplacian/Spectral/EigenBasis.lean`, with no smoothness hypothesis
on the eigenfunctions.

The proof composes two ingredients:

1. **Smooth representative.** For each spectral basis vector
   `b_i := resolventEigenbasisSigma g i`, the unconditional smoothing endpoint
   of the heat semigroup (`heatSemigroup_smooth_representative_of_closed`)
   furnishes a smooth function on `M` whose `Lp` class equals `b_i`. The
   heat-semigroup action on basis vectors is multiplication by a nonzero
   exponential factor, so rescaling produces a smooth representative `f` with
   `(b_i : M → ℝ) =ᵐ f` and `Δ_g f = -lam * f` pointwise (where
   `lam = (1 - μ) / μ` is the Laplacian eigenvalue associated with
   `μ = i.1.val`).
2. **The classical Lichnerowicz inequality.** Applied to `f`, the smooth
   theorem `lichnerowicz_eigenvalue_ge_dim_mul_curvature_of_closed` yields `n K ≤ lam`.

## Main results

* `laplacianEigenfunction_smooth_representative`: a smooth `f : M → ℝ` with
  `(b_i : M → ℝ) =ᵐ f` and `Δ_g f = -lam * f` pointwise.
* `lichnerowicz_spectral_eigenvalue_ge_dim_mul_curvature_of_closed`: the spectral form
  `n K ≤ laplacianEigenvalueOf i.1.val` for every basis index whose
  Laplacian eigenvalue is strictly positive.

## Sign convention

Geometer convention `Δ_g = div_g ∘ grad_g`. The variational operator on
`laplacianDomain g` is `laplacianOp g`, acting as
`laplacianOp b_i_lift = -lam • b_i` (negative spectrum on a closed manifold).
The resolvent `(1 - Δ_g)⁻¹` has spectrum in `(0, 1]`; the corresponding
Laplacian eigenvalue `lam = (1 - μ) / μ` is non-negative.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.HeatEquation

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

set_option maxHeartbeats 6400000 in
/-- `H1ComplToLp` is injective on the variational-Laplacian domain. -/
theorem H1ComplToLp_inj_on_laplacianDomain
    (g : SmoothRiemannianMetric I M)
    {u v : laplacianDomain (I := I) (M := M) g}
    (h_eq : H1ComplToLp (I := I) (M := M) g (u : H1Compl g) =
            H1ComplToLp (I := I) (M := M) g (v : H1Compl g)) :
    (u : H1Compl g) = (v : H1Compl g) := by
  set wu : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    laplacianDomain.preimage (I := I) (M := M) g u with hwu_def
  set wv : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    laplacianDomain.preimage (I := I) (M := M) g v with hwv_def
  have h_u_res : (u : H1Compl g) =
      resolvent (I := I) (M := M) g wu :=
    (resolvent_laplacianDomain_preimage_eq (I := I) (M := M) g u).symm
  have h_v_res : (v : H1Compl g) =
      resolvent (I := I) (M := M) g wv :=
    (resolvent_laplacianDomain_preimage_eq (I := I) (M := M) g v).symm
  have hLHS : resolventL2 (I := I) (M := M) g wu =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g wu) :=
    resolventL2_apply (I := I) (M := M) g _
  have hRHS : resolventL2 (I := I) (M := M) g wv =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g wv) :=
    resolventL2_apply (I := I) (M := M) g _
  have h_eq_L2 :
      resolventL2 (I := I) (M := M) g wu =
      resolventL2 (I := I) (M := M) g wv := by
    rw [hLHS, hRHS, ← h_u_res, ← h_v_res]
    exact h_eq
  have h_pre_eq : wu = wv := by
    have h_inj := resolventL2_injective (I := I) (M := M) g
    exact h_inj h_eq_L2
  rw [h_u_res, h_v_res, h_pre_eq]

/-- The Lp coercion of the spectral basis vector at index `i`, named for
elaboration efficiency in downstream statements. -/
private def spectralBasisFun
    (g : SmoothRiemannianMetric I M)
    (i : Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
        Fin (Module.finrank ℝ (resolventEigenspace (I := I) (M := M) g μ.val))) :
    M → ℝ :=
  fun x => (resolventEigenbasisSigma (I := I) (M := M) g i) x

set_option maxHeartbeats 6400000 in
/-- **Smooth pointwise eigenfunction at every nonzero spectral eigenvalue.**

For a closed Riemannian manifold `(M, g)` and an index `i = ⟨μ, k⟩` of the
spectral eigenbasis, there exists a smooth `s : SmoothScalar g` whose `Lp`
class equals `b_i := resolventEigenbasisSigma g i` and which satisfies the
eigenfunction equation `Δ_g s = -lam * s` pointwise on `M`, where
`lam := laplacianEigenvalueOf μ`.

The proof:

* Apply the unconditional spatial smoothing of the heat semigroup at `t = 1`
  to obtain a smooth `u_smooth` with `heatSemigroup g 1 b_i =ᵐ u_smooth`.
* Use `heatSemigroup_apply_basis` to identify
  `heatSemigroup g 1 b_i = Real.exp (-lam) • b_i` as `Lp` classes, hence
  `Real.exp (-lam) • b_i =ᵐ u_smooth`.
* Set `f := Real.exp lam • u_smooth`; then `f` is smooth and
  `(b_i : M → ℝ) =ᵐ f`.
* Wrap `f` as a `SmoothScalar g` and identify its H¹ lift with the
  spectral eigenfunction lift `laplacianEigenfunction g i` via the injectivity
  of `H1ComplToLp` on `laplacianDomain g`.
* Apply `laplacianOp_smoothToH1Compl` and `laplacianOp_laplacianEigenfunction`
  to conclude `Δ_g f =ᵐ -lam * f`, then upgrade the a.e. equality to the
  pointwise equation using `Continuous.ae_eq_iff_eq` on the positive-on-opens
  Riemannian volume measure. -/
theorem laplacianEigenfunction_smooth_representative
    (g : SmoothRiemannianMetric I M)
    (i : Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
        Fin (Module.finrank ℝ (resolventEigenspace (I := I) (M := M) g μ.val))) :
    ∃ s : SmoothScalar g,
      spectralBasisFun (I := I) (M := M) g i =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g] s.toFun ∧
      (∀ x : M, Δ_g (I := I) g s.smooth x =
        -(laplacianEigenvalueOf i.1.val) * s.toFun x) := by
  classical
  set μ_g : Measure M := riemannianVolumeMeasure (I := I) (M := M) g with hμ_g_def
  set b_i : Lp ℝ 2 μ_g := resolventEigenbasisSigma (I := I) (M := M) g i with hb_i_def
  set lam : ℝ := laplacianEigenvalueOf i.1.val with hlam_def
  obtain ⟨u_smooth, hu_smooth_smooth, hu_smooth_ae⟩ :=
    heatSemigroup_smooth_representative_of_closed
      (I := I) (M := M) g (t := (1 : ℝ)) (by norm_num : (0 : ℝ) < 1) b_i
  have h_heat_basis : heatSemigroup (I := I) (M := M) g 1 b_i =
      Real.exp (-lam * 1) • b_i := by
    have h := heatSemigroup_apply_basis (I := I) (M := M) g (t := (1 : ℝ))
      (by norm_num : (0 : ℝ) ≤ 1) i
    have hlam_eq : EigenIdx.lambda (I := I) (M := M) i = lam := rfl
    rw [hlam_eq] at h
    exact h
  have h_exp_smul_ae :
      ((Real.exp (-lam * 1) • b_i :
        Lp ℝ 2 μ_g) : M → ℝ) =ᵐ[μ_g] u_smooth := by
    have h_replace : ((heatSemigroup (I := I) (M := M) g 1 b_i :
          Lp ℝ 2 μ_g) : M → ℝ) =
        ((Real.exp (-lam * 1) • b_i : Lp ℝ 2 μ_g) : M → ℝ) := by
      rw [h_heat_basis]
    rw [← h_replace]; exact hu_smooth_ae
  have h_exp_simp : Real.exp (-lam * 1) = Real.exp (-lam) := by
    rw [mul_one]
  rw [h_exp_simp] at h_exp_smul_ae
  set f : M → ℝ := Real.exp lam • u_smooth with hf_def
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := by
    have h_eq : f = (fun x : M => Real.exp lam * u_smooth x) := by
      funext x; rfl
    rw [h_eq]
    exact contMDiff_const.mul hu_smooth_smooth
  have h_bi_ae_f : ((b_i : Lp ℝ 2 μ_g) : M → ℝ) =ᵐ[μ_g] f := by
    have h_smul_coe : ((Real.exp (-lam) • b_i :
        Lp ℝ 2 μ_g) : M → ℝ) =ᵐ[μ_g]
        Real.exp (-lam) • ((b_i : Lp ℝ 2 μ_g) : M → ℝ) :=
      Lp.coeFn_smul _ _
    have h_pointwise_ae :
        Real.exp (-lam) • ((b_i : Lp ℝ 2 μ_g) : M → ℝ) =ᵐ[μ_g] u_smooth :=
      h_smul_coe.symm.trans h_exp_smul_ae
    have h_exp_inv : Real.exp lam * Real.exp (-lam) = 1 := by
      rw [← Real.exp_add, add_neg_cancel]
      exact Real.exp_zero
    filter_upwards [h_pointwise_ae] with x hx
    have hx' : Real.exp (-lam) * ((b_i : Lp ℝ 2 μ_g) : M → ℝ) x = u_smooth x := by
      simpa [Pi.smul_apply, smul_eq_mul] using hx
    have h_f_apply : f x = Real.exp lam * u_smooth x := rfl
    rw [h_f_apply, ← hx']
    rw [show Real.exp lam * (Real.exp (-lam) * ((b_i : Lp ℝ 2 μ_g) : M → ℝ) x) =
        (Real.exp lam * Real.exp (-lam)) * ((b_i : Lp ℝ 2 μ_g) : M → ℝ) x from by ring]
    rw [h_exp_inv, one_mul]
  set f_smooth : SmoothScalar g := ⟨f, hf_smooth⟩ with hf_smooth_def
  have h_smoothToLp_eq_b_i :
      (smoothToLp (I := I) (M := M) g f_smooth :
        Lp ℝ 2 μ_g) = b_i := by
    apply Lp.ext
    have h_smoothToLp_ae :
        (smoothToLp (I := I) (M := M) g f_smooth :
          Lp ℝ 2 μ_g) =ᵐ[μ_g] f :=
      MemLp.coeFn_toLp f_smooth.memLp_two
    exact h_smoothToLp_ae.trans h_bi_ae_f.symm
  have h_smoothToH1Compl_mem :
      smoothToH1Compl (I := I) (M := M) g f_smooth ∈
        laplacianDomain (I := I) (M := M) g :=
    smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) f_smooth
  set f_lap : laplacianDomain (I := I) (M := M) g :=
      ⟨smoothToH1Compl (I := I) (M := M) g f_smooth, h_smoothToH1Compl_mem⟩
    with hf_lap_def
  set ef_lap : laplacianDomain (I := I) (M := M) g :=
      laplacianEigenfunction (I := I) (M := M) g i with hef_lap_def
  have h_H1ComplToLp_f_lap :
      H1ComplToLp (I := I) (M := M) g (f_lap : H1Compl g) = b_i := by
    change H1ComplToLp (I := I) (M := M) g
        (smoothToH1Compl (I := I) (M := M) g f_smooth) = b_i
    rw [H1ComplToLp_smoothToH1Compl]
    exact h_smoothToLp_eq_b_i
  have h_H1ComplToLp_ef_lap :
      H1ComplToLp (I := I) (M := M) g (ef_lap : H1Compl g) = b_i := by
    change H1ComplToLp (I := I) (M := M) g
        (laplacianEigenfunction (I := I) (M := M) g i :
          H1Compl (I := I) (M := M) g) = b_i
    rw [H1ComplToLp_laplacianEigenfunction]
  have h_subtype_eq : (f_lap : H1Compl g) = (ef_lap : H1Compl g) :=
    H1ComplToLp_inj_on_laplacianDomain (I := I) (M := M) g
      (h_H1ComplToLp_f_lap.trans h_H1ComplToLp_ef_lap.symm)
  have h_lap_eq : f_lap = ef_lap := Subtype.ext h_subtype_eq
  have h_op_smooth :
      laplacianOp (I := I) (M := M) g f_lap =
        smoothToLp (I := I) (M := M) g f_smooth -
          smoothToLp (I := I) (M := M) g f_smooth.oneSubLapClassical :=
    laplacianOp_smoothToH1Compl (I := I) (M := M) f_smooth
  have h_op_eigen :
      laplacianOp (I := I) (M := M) g ef_lap =
        -(laplacianEigenvalueOf i.1.val) •
          resolventEigenbasisSigma (I := I) (M := M) g i :=
    laplacianOp_laplacianEigenfunction (I := I) (M := M) g i
  have h_op_eq :
      smoothToLp (I := I) (M := M) g f_smooth -
        smoothToLp (I := I) (M := M) g f_smooth.oneSubLapClassical =
      -(laplacianEigenvalueOf i.1.val) • b_i := by
    rw [← h_op_smooth, ← h_op_eigen]
    rw [h_lap_eq]
  set Δf_smooth : SmoothScalar g :=
    ⟨Δ_g (I := I) g hf_smooth, Δ_g_contMDiff (I := I) g hf_smooth⟩
    with hΔf_smooth_def
  have h_diff_eq : f_smooth - f_smooth.oneSubLapClassical = Δf_smooth := by
    apply SmoothScalar.ext
    funext x
    change (f_smooth.toFun - f_smooth.oneSubLapClassical.toFun) x =
      Δ_g (I := I) g hf_smooth x
    rw [Pi.sub_apply, SmoothScalar.oneSubLapClassical_toFun, Pi.sub_apply]
    ring
  have h_smoothToLp_diff :
      smoothToLp (I := I) (M := M) g f_smooth -
        smoothToLp (I := I) (M := M) g f_smooth.oneSubLapClassical =
      smoothToLp (I := I) (M := M) g Δf_smooth := by
    rw [show smoothToLp (I := I) (M := M) g f_smooth -
        smoothToLp (I := I) (M := M) g f_smooth.oneSubLapClassical =
        smoothToLp (I := I) (M := M) g (f_smooth - f_smooth.oneSubLapClassical) from
      (map_sub (smoothToLp (I := I) (M := M) g) _ _).symm]
    rw [h_diff_eq]
  have h_Δlp_eq :
      smoothToLp (I := I) (M := M) g Δf_smooth =
        -(laplacianEigenvalueOf i.1.val) • b_i := by
    rw [← h_smoothToLp_diff]
    exact h_op_eq
  set neg_lam_f_smooth : SmoothScalar g :=
      (-(laplacianEigenvalueOf i.1.val)) • f_smooth with hneg_lam_f_def
  have h_smoothToLp_neg_lam_f :
      smoothToLp (I := I) (M := M) g neg_lam_f_smooth =
        -(laplacianEigenvalueOf i.1.val) • b_i := by
    rw [hneg_lam_f_def]
    rw [(smoothToLp (I := I) (M := M) g).map_smul]
    rw [h_smoothToLp_eq_b_i]
  have h_Lp_eq :
      smoothToLp (I := I) (M := M) g Δf_smooth =
        smoothToLp (I := I) (M := M) g neg_lam_f_smooth :=
    h_Δlp_eq.trans h_smoothToLp_neg_lam_f.symm
  have h_Δf_ae_neg_lam_f :
      (fun x : M => Δ_g (I := I) g hf_smooth x) =ᵐ[μ_g]
      (fun x : M => -(laplacianEigenvalueOf i.1.val) * f x) := by
    have h_lhs_ae : (smoothToLp (I := I) (M := M) g Δf_smooth :
        Lp ℝ 2 μ_g) =ᵐ[μ_g] Δf_smooth.toFun :=
      MemLp.coeFn_toLp Δf_smooth.memLp_two
    have h_rhs_ae : (smoothToLp (I := I) (M := M) g neg_lam_f_smooth :
        Lp ℝ 2 μ_g) =ᵐ[μ_g] neg_lam_f_smooth.toFun :=
      MemLp.coeFn_toLp neg_lam_f_smooth.memLp_two
    have h_lhs_explicit : Δf_smooth.toFun = (fun x : M => Δ_g (I := I) g hf_smooth x) := rfl
    have h_rhs_explicit : neg_lam_f_smooth.toFun =
        (fun x : M => -(laplacianEigenvalueOf i.1.val) * f x) := by
      funext x
      change ((-(laplacianEigenvalueOf i.1.val)) • f_smooth).toFun x =
        -(laplacianEigenvalueOf i.1.val) * f x
      rw [SmoothScalar.toFun_smul_apply]
    rw [h_lhs_explicit] at h_lhs_ae
    rw [h_rhs_explicit] at h_rhs_ae
    have h_lp_ae : (smoothToLp (I := I) (M := M) g Δf_smooth :
        Lp ℝ 2 μ_g) =ᵐ[μ_g]
        (smoothToLp (I := I) (M := M) g neg_lam_f_smooth :
        Lp ℝ 2 μ_g) := by
      rw [h_Lp_eq]
    exact h_lhs_ae.symm.trans (h_lp_ae.trans h_rhs_ae)
  have h_pos : (riemannianVolumeMeasure (I := I) (M := M) g).IsOpenPosMeasure :=
    riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
  have h_Δf_cont : Continuous (fun x : M => Δ_g (I := I) g hf_smooth x) :=
    (Δ_g_contMDiff (I := I) g hf_smooth).continuous
  have h_neg_lam_f_cont :
      Continuous (fun x : M => -(laplacianEigenvalueOf i.1.val) * f x) :=
    continuous_const.mul hf_smooth.continuous
  have h_Δf_eq_neg_lam_f :
      (fun x : M => Δ_g (I := I) g hf_smooth x) =
      (fun x : M => -(laplacianEigenvalueOf i.1.val) * f x) :=
    (Continuous.ae_eq_iff_eq _ h_Δf_cont h_neg_lam_f_cont).mp h_Δf_ae_neg_lam_f
  refine ⟨f_smooth, ?_, ?_⟩
  · exact h_bi_ae_f
  · intro x
    exact congrFun h_Δf_eq_neg_lam_f x

/-- For a nonzero resolvent eigenvalue with `μ < 1`, the Laplacian eigenvalue
`lam = (1 - μ) / μ` is strictly positive. -/
private lemma laplacianEigenvalueOf_pos_of_lt_one
    (g : SmoothRiemannianMetric I M)
    (μ : NonzeroResolventEigenvalue (I := I) (M := M) g)
    (hμ_lt_one : μ.val < 1) :
    0 < laplacianEigenvalueOf μ.val := by
  unfold laplacianEigenvalueOf
  have h_pos : 0 < μ.val := nonzeroResolventEigenvalue_pos μ
  have h_num_pos : 0 < 1 - μ.val := by linarith
  exact div_pos h_num_pos h_pos

set_option maxHeartbeats 800000 in
/-- **Lichnerowicz's eigenvalue inequality at the spectral level.**

On a closed Riemannian manifold `(M, g)` of dimension `n := finrank ℝ E ≥ 2`
satisfying the Ricci lower bound `Ric ≥ (n - 1) K g` with `K > 0`, every
spectral eigenbasis index `i` whose associated Laplacian eigenvalue
`lam = laplacianEigenvalueOf i.1.val` is strictly positive satisfies the
lower bound `n K ≤ lam`.

Here `i = ⟨μ, k⟩` ranges over the spectral basis of the variational Laplacian
(`resolventEigenbasisSigma`), `μ` being a nonzero resolvent eigenvalue and
`lam = (1 - μ) / μ` the corresponding Laplacian eigenvalue. The
strict-positivity hypothesis `0 < lam` excludes the trivial eigenspace at
`μ = 1` (`lam = 0`); since `n K > 0`, it is a necessary condition for the
inequality, equivalently `μ < 1`. No smoothness hypothesis is placed on the
basis vectors.

The proof composes `laplacianEigenfunction_smooth_representative`, which
produces a smooth representative `f` of the basis vector with
`Δ_g f = -lam * f` pointwise and L²-norm one, with the smooth Lichnerowicz
inequality `lichnerowicz_eigenvalue_ge_dim_mul_curvature_of_closed` applied to `f`. -/
theorem lichnerowicz_spectral_eigenvalue_ge_dim_mul_curvature_of_closed
    (g : SmoothRiemannianMetric I M)
    (hn_ge_two : 2 ≤ Module.finrank ℝ E)
    {K : ℝ} (hK : 0 < K)
    (h_ricci : ∀ x : M, ∀ X : TangentSpace I x,
      ((Module.finrank ℝ E : ℝ) - 1) * K * g.inner x X X ≤
        ricciTensor (I := I) g x X X)
    (i : Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
        Fin (Module.finrank ℝ (resolventEigenspace (I := I) (M := M) g μ.val)))
    (hlam_pos : 0 < laplacianEigenvalueOf i.1.val) :
    (Module.finrank ℝ E : ℝ) * K ≤ laplacianEigenvalueOf i.1.val := by
  classical
  set μ_g : Measure M := riemannianVolumeMeasure (I := I) (M := M) g with hμ_g_def
  set b_i : Lp ℝ 2 μ_g := resolventEigenbasisSigma (I := I) (M := M) g i with hb_i_def
  obtain ⟨s, h_bi_ae_f, h_eigen⟩ :=
    laplacianEigenfunction_smooth_representative
      (I := I) (M := M) g i
  set f : M → ℝ := s.toFun with hf_def
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := s.smooth
  have h_f_sq_pos : 0 < ∫ x, f x * f x ∂μ_g := by
    have h_norm_sq_eq :
        ‖smoothToLp (I := I) (M := M) g s‖ ^ 2 =
          ∫ x, f x * f x ∂μ_g :=
      s.norm_smoothToLp_sq
    have h_smoothToLp_eq : (smoothToLp (I := I) (M := M) g s :
        Lp ℝ 2 μ_g) = b_i := by
      apply Lp.ext
      have h_lhs_ae : (smoothToLp (I := I) (M := M) g s :
          Lp ℝ 2 μ_g) =ᵐ[μ_g] s.toFun :=
        MemLp.coeFn_toLp s.memLp_two
      exact h_lhs_ae.trans h_bi_ae_f.symm
    have h_norm_sq_b_i : ‖smoothToLp (I := I) (M := M) g s‖ ^ 2 =
        ‖b_i‖ ^ 2 := by
      rw [h_smoothToLp_eq]
    rw [h_norm_sq_eq] at h_norm_sq_b_i
    have h_b_i_norm : ‖b_i‖ = 1 := by
      have h_onorm := resolventEigenbasisVec_orthonormal
        (I := I) (M := M) g
      have h_vec_eq : b_i = resolventEigenbasisVec (I := I) (M := M) g i :=
        resolventEigenbasisSigma_eq_resolventEigenbasisVec
          (I := I) (M := M) g i
      rw [h_vec_eq]
      exact h_onorm.1 i
    have h_b_i_norm_sq_pos : 0 < ‖b_i‖ ^ 2 := by
      rw [h_b_i_norm]; norm_num
    linarith
  exact lichnerowicz_eigenvalue_ge_dim_mul_curvature_of_closed (I := I) (M := M) g hn_ge_two hK
    hf hlam_pos h_eigen h_ricci h_f_sq_pos

end Laplacian
end Analysis
end DifferentialGeometry

end
