import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5CommutatorScalar
import DifferentialGeometry.Geometry.Metric.Convergence.IntegrableVelocity
import DifferentialGeometry.Geometry.Metric.Tensor.Scaling
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.CovariantTwoTensor

/-!
# The fixed-background hypothesis of the surface lemma from the scalar curvature rate

Chapter 7, surface lemma U1, route (a), step a5.3 L (lane U1C; design D18,
`docs/geometrization/handoffs/20261004-design-u1-a5-potential-gauge.md`).

For a Ricci flow `g(t)` on `[0, Tm)` put `ĝ(t) = g(t) / (2 (Tm - t))` and
`s = -½ log ((Tm - t) / Tm)`, so `t = Tm - Tm e^{-2 s}`. In two dimensions
`∂ₛ ĝ = V := 2 ĝ - 2 Ric(g(t))`, and `|∇^q_ĝ V|_ĝ` is `√2 |R̂ - 2|` for `q = 0` and at most
`2^{(q + 6) / 2} ((2 (Tm - t))^{q + 2} |∇^q Rm|²)^{1/2}` for `q ≥ 1` (`∇ĝ = 0`, the
Levi-Civita connection is scale invariant, `ricTower_normSq_le`).

* `surfaceFlow_ha5_of_scalar_derivative_decay`: a rate `|R̂ - 2| ≤ C (Tm - t)^δ` and the derivative
  decay D give exponential decay of every `|∇^q V|`, so `exists_metric_limit_of_exp_decay_velocity`
  (lane U1V's L1, background `g(0)`) yields the uniform lower bound and the all-order bounds of
  `ĝ(t)` against `g(0)` on a terminal interval: the hypothesis `ha5` of
  `exists_isometryInvariant_roundMetric_of_a5`, for a general surface model.
* `surfaceFlow_ha5_of_scalar_rate`: the same from the rate alone, through
  `surfaceFlow_scalar_derivative_decay`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Tensor
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Set
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M]

private def tOf (Tm s : ℝ) : ℝ := Tm - Tm * Real.exp (-2 * s)

private def sOf (Tm t : ℝ) : ℝ := -(1 / 2) * Real.log ((Tm - t) / Tm)

private theorem tOf_lt {Tm : ℝ} (hTm : 0 < Tm) (s : ℝ) : tOf Tm s < Tm := by
  unfold tOf
  have := Real.exp_pos (-2 * s)
  nlinarith

private theorem sub_tOf (Tm s : ℝ) : Tm - tOf Tm s = Tm * Real.exp (-2 * s) := by
  unfold tOf; ring

private theorem tOf_sOf {Tm t : ℝ} (hTm : 0 < Tm) (ht : t < Tm) : tOf Tm (sOf Tm t) = t := by
  unfold tOf sOf
  have hpos : 0 < (Tm - t) / Tm := div_pos (by linarith) hTm
  rw [show -2 * (-(1 / 2) * Real.log ((Tm - t) / Tm)) = Real.log ((Tm - t) / Tm) by ring,
    Real.exp_log hpos]
  field_simp
  ring

private theorem sOf_le_sOf {Tm t₀ t : ℝ} (hTm : 0 < Tm) (h0 : t₀ ≤ t) (ht : t < Tm) :
    sOf Tm t₀ ≤ sOf Tm t := by
  unfold sOf
  have h1 : 0 < (Tm - t) / Tm := div_pos (by linarith) hTm
  have h2 : (Tm - t) / Tm ≤ (Tm - t₀) / Tm := div_le_div_of_nonneg_right (by linarith) hTm.le
  have := Real.log_le_log h1 h2
  linarith

private theorem le_tOf {Tm t₀ s : ℝ} (hTm : 0 < Tm) (ht₀ : t₀ < Tm) (hs : sOf Tm t₀ ≤ s) :
    t₀ ≤ tOf Tm s := by
  have h := tOf_sOf hTm ht₀
  have hmono : Real.exp (-2 * s) ≤ Real.exp (-2 * sOf Tm t₀) :=
    Real.exp_le_exp.mpr (by linarith)
  unfold tOf at h ⊢
  nlinarith

local instance instU1CManifoldOne : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)

local instance instU1CManifoldTop : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
  change IsManifold I ∞ M
  infer_instance

private def nMetric {Tm : ℝ} {hTm : 0 < Tm}
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 Tm hTm)) (t : ℝ) :
    SmoothRiemannianMetric I M :=
  if h : t < Tm then
    scaleMetric (1 / (2 * (Tm - t))) (normalizedSurfaceMetric_pos h) (S.family.metric t)
  else S.family.metric t

omit [I.Boundaryless] [T2Space M] [CompactSpace M] in
private theorem nMetric_eq {Tm : ℝ} {hTm : 0 < Tm}
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 Tm hTm)) {t : ℝ}
    (ht : t < Tm) :
    nMetric S t =
      scaleMetric (1 / (2 * (Tm - t))) (normalizedSurfaceMetric_pos ht) (S.family.metric t) := by
  simp [nMetric, ht]

omit [I.Boundaryless] [T2Space M] [CompactSpace M] in
private theorem nMetric_tOf_inner {Tm : ℝ} {hTm : 0 < Tm}
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 Tm hTm)) (r : ℝ) (x : M)
    (a b : TangentSpace I x) :
    (nMetric S (tOf Tm r)).inner x a b =
      Real.exp (2 * r) / (2 * Tm) * (S.family.metric (tOf Tm r)).inner x a b := by
  rw [nMetric_eq S (tOf_lt hTm r)]
  change (1 / (2 * (Tm - tOf Tm r))) * (S.family.metric (tOf Tm r)).inner x a b = _
  rw [sub_tOf]
  congr 1
  rw [show (-2 : ℝ) * r = -(2 * r) by ring, Real.exp_neg]
  field_simp

private def velField {Tm : ℝ} {hTm : 0 < Tm}
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 Tm hTm)) (s : ℝ) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2 :=
  (2 : ℝ) • metricTensorField (nMetric S (tOf Tm s)) -
    (2 : ℝ) • metricRicci (S.family.metric (tOf Tm s))

omit [CompactSpace M] [I.Boundaryless] in
private theorem velField_hasDerivAt {Tm : ℝ} {hTm : 0 < Tm}
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 Tm hTm))
    (hS : IsSolutionOn S) {s : ℝ} (hs : 0 < tOf Tm s) (x : M) (v : Fin 2 → TangentSpace I x) :
    HasDerivAt (fun r => (nMetric S (tOf Tm r)).inner x (v 0) (v 1)) (velField S s x v) s := by
  have hfun : (fun r => (nMetric S (tOf Tm r)).inner x (v 0) (v 1)) =
      fun r => Real.exp (2 * r) / (2 * Tm) * (S.family.metric (tOf Tm r)).inner x (v 0) (v 1) :=
    funext fun r => nMetric_tOf_inner S r x _ _
  rw [hfun]
  have hreg : tOf Tm s ∈ (RealTimeInterval.closedOpen 0 Tm hTm).regular := ⟨hs, tOf_lt hTm s⟩
  have hg := metricDerivAt S hS ⟨tOf Tm s, hreg⟩ x (v 0) (v 1)
  have ht : HasDerivAt (tOf Tm) (Tm * (2 * Real.exp (-2 * s))) s := by
    have h1 : HasDerivAt (fun r : ℝ => -2 * r) (-2) s := by
      simpa using (hasDerivAt_id s).const_mul (-2 : ℝ)
    have h2 := ((h1.exp).const_mul Tm).const_sub Tm
    change HasDerivAt (fun r => Tm - Tm * Real.exp (-2 * r)) _ s
    exact h2.congr_deriv (by ring)
  have hgc := hg.comp s ht
  have hl : HasDerivAt (fun r => Real.exp (2 * r) / (2 * Tm))
      (Real.exp (2 * s) * 2 / (2 * Tm)) s := by
    have := (((hasDerivAt_id s).const_mul (2 : ℝ)).exp).div_const (2 * Tm)
    simpa using this
  have hprod := hl.mul hgc
  convert hprod using 1
  · funext r; rfl
  have hv : v = vec2 (v 0) (v 1) := by funext i; fin_cases i <;> rfl
  have hric : S.ricciAt (tOf Tm s) x (vec2 (v 0) (v 1)) =
      metricRicci (S.family.metric (tOf Tm s)) x v := by
    rw [metricRicci_apply, ← hv]
    rfl
  have hexp : Real.exp (2 * s) * Real.exp (-2 * s) = 1 := by
    rw [← Real.exp_add]; simp
  unfold velField
  simp only [ContMDiffSection.coe_sub, ContMDiffSection.coe_smul, Pi.sub_apply,
    Pi.smul_apply, sub_apply, smul_apply, smul_eq_mul, metricTensorField_apply,
    nMetric_tOf_inner, hric, Function.comp_def]
  have hT : Tm * Tm⁻¹ = 1 := mul_inv_cancel₀ hTm.ne'
  linear_combination (2 * metricRicci (S.family.metric (tOf Tm s)) x v * Tm * Tm⁻¹) * hexp +
    (2 * metricRicci (S.family.metric (tOf Tm s)) x v) * hT

omit [CompactSpace M] [I.Boundaryless] in
private theorem nMetric_joint {Tm : ℝ} {hTm : 0 < Tm}
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 Tm hTm))
    (hS : IsSolutionOn S) {s : ℝ} (hs : 0 < tOf Tm s) (x : M)
    (W : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
      (fun q : ℝ × M => (nMetric S (tOf Tm q.1)).inner q.2 (W 0 q.2) (W 1 q.2)) (s, x) := by
  have hfun : (fun q : ℝ × M => (nMetric S (tOf Tm q.1)).inner q.2 (W 0 q.2) (W 1 q.2)) =
      fun q : ℝ × M => Real.exp (2 * q.1) / (2 * Tm) *
        (S.family.metric (tOf Tm q.1)).inner q.2 (W 0 q.2) (W 1 q.2) :=
    funext fun q => nMetric_tOf_inner S q.1 q.2 _ _
  rw [hfun]
  have hreg : (RealTimeInterval.closedOpen 0 Tm hTm).regular ∈ nhds (tOf Tm s) :=
    isOpen_Ioo.mem_nhds ⟨hs, tOf_lt hTm s⟩
  have hpair := hS.smoothMetric.pairSmoothAt (x := x) hreg W
  have htOf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (tOf Tm) := by
    have : ContDiff ℝ ∞ (tOf Tm) := by
      unfold tOf
      fun_prop
    exact this.contMDiff
  have hφ : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun q : ℝ × M => (tOf Tm q.1, q.2)) (s, x) :=
    ((htOf.comp contMDiff_fst).prodMk contMDiff_snd).contMDiffAt
  have h2 := hpair.comp (s, x) hφ
  have hexp : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => Real.exp (2 * q.1) / (2 * Tm)) := by
    have : ContDiff ℝ ∞ (fun r : ℝ => Real.exp (2 * r) / (2 * Tm)) := by fun_prop
    exact this.contMDiff.comp contMDiff_fst
  exact hexp.contMDiffAt.mul h2

private theorem sqrt_rate {Tm s A β : ℝ} (hTm : 0 < Tm) (hA : 0 ≤ A) :
    Real.sqrt (A * (Tm * Real.exp (-2 * s)) ^ β) =
      Real.sqrt A * Tm ^ (β / 2) * Real.exp (-(β * s)) := by
  have he : 0 < Real.exp (-2 * s) := Real.exp_pos _
  have h1 : Real.sqrt (Tm ^ β) = Tm ^ (β / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hTm.le]
    ring_nf
  have h2 : Real.sqrt (Real.exp (-2 * s) ^ β) = Real.exp (-(β * s)) := by
    rw [← Real.exp_mul, Real.sqrt_eq_rpow, ← Real.exp_mul]
    ring_nf
  rw [Real.sqrt_mul hA, Real.mul_rpow hTm.le he.le,
    Real.sqrt_mul (Real.rpow_nonneg hTm.le β), h1, h2]
  ring

private theorem sqrt_le_exp_rate {N A β Tm s : ℝ} (hTm : 0 < Tm) (hA : 0 ≤ A)
    (h : N ≤ A * (Tm - tOf Tm s) ^ β) :
    Real.sqrt N ≤ Real.sqrt A * Tm ^ (β / 2) * Real.exp (-(β * s)) :=
  (Real.sqrt_le_sqrt h).trans_eq (by rw [sub_tOf, sqrt_rate hTm hA])

omit [CompactSpace M] [I.Boundaryless] in
private theorem tensor02CovDerivNormWith_eq_sqrt (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
    (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2) (g : SmoothRiemannianMetric I M) (q : ℕ)
    (x : M) :
    tensor02CovDerivNormWith q A g g x =
      Real.sqrt (normSq0S g x (2 + q) (iterCov g 2 A q x)) := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  classical
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis g x
  exact tensor02CovDerivNormWith_eq_iterCov A g q basis
    (metricInverseInBasis_of_orthonormal g basis hON)

omit [CompactSpace M] in
private theorem velField_norm_zero (hdim : Module.finrank ℝ E = 2) {Tm : ℝ} {hTm : 0 < Tm}
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 Tm hTm)) (s : ℝ) (x : M) :
    normSq0S (nMetric S (tOf Tm s)) x (2 + 0)
        (iterCov (nMetric S (tOf Tm s)) 2 (velField S s) 0 x) =
      2 * (S.scalar (tOf Tm s) x * (2 * (Tm - tOf Tm s)) - 2) ^ 2 := by
  set t := tOf Tm s with htdef
  have ht : t < Tm := tOf_lt hTm s
  have hτ : 0 < Tm - t := by linarith
  set g := S.family.metric t with hg
  set R := S.scalar t x with hR
  have hV : iterCov (nMetric S t) 2 (velField S s) 0 x =
      (2 * (1 / (2 * (Tm - t))) - R) • metricTensor0S g x := by
    apply tensor0SSpace_ext
    intro v
    change velField S s x v = _
    rw [smul_apply, metricTensor0S_apply]
    simp only [velField, ContMDiffSection.coe_sub, ContMDiffSection.coe_smul, Pi.sub_apply,
      Pi.smul_apply, sub_apply, smul_apply, smul_eq_mul, metricTensorField_apply,
      metricRicci_apply]
    rw [metricRicciAt_eq_half_metricScalarAt_smul_metric_of_finrank_eq_two g hdim x,
      nMetric_eq S ht]
    simp only [smul_apply, metricTensor0S_apply, smul_eq_mul]
    change 2 * (1 / (2 * (Tm - t)) * g.inner x (v 0) (v 1)) - 2 * (R / 2 * g.inner x (v 0) (v 1))
      = _
    ring
  rw [hV, nMetric_eq S ht, normSq0S_scale, Tensor0SBundle.normSq0S_smul]
  obtain ⟨e, horth⟩ := exists_orthonormalBasis_of_finrank_two g x hdim
  rw [normSq0S_metricTensor0S_eq_card g e _ (metricInverseInBasis_of_orthonormal g e horth)]
  simp only [Fintype.card_fin, Nat.cast_ofNat, one_div, inv_inv]
  field_simp
  ring

omit [CompactSpace M] [I.Boundaryless] in
private theorem velField_norm_succ (hdim : Module.finrank ℝ E = 2) {Tm : ℝ} {hTm : 0 < Tm}
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 Tm hTm)) (s : ℝ) (q : ℕ)
    (x : M) :
    normSq0S (nMetric S (tOf Tm s)) x (2 + (q + 1))
        (iterCov (nMetric S (tOf Tm s)) 2 (velField S s) (q + 1) x) ≤
      4 * 2 ^ (q + 1 + 4) * ((2 * (Tm - tOf Tm s)) ^ (q + 3) *
        nablaKRm04NormSqIntrinsic S (q + 1) (tOf Tm s) x) := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by decide)
  set t := tOf Tm s with htdef
  have ht : t < Tm := tOf_lt hTm s
  have hτ : 0 < Tm - t := by linarith
  set g := S.family.metric t with hg
  have hit : iterCov (nMetric S t) 2 (velField S s) (q + 1) =
      (-2 : ℝ) • iterCov g 2 (metricRicci g) (q + 1) := by
    rw [velField, iterCov_sub, iterCov_smul, iterCov_smul, iterCov_metric_zero, nMetric_eq S ht,
      iterCov_scaleMetric]
    simp only [smul_zero, zero_sub, neg_smul]
    rfl
  rw [hit, nMetric_eq S ht, ContMDiffSection.coe_smul, Pi.smul_apply, normSq0S_scale,
    Tensor0SBundle.normSq0S_smul]
  have hric := ricTower_normSq_le S t (q + 1) x
  rw [hdim] at hric
  have hric' : normSq0S g x (2 + (q + 1)) (iterCov g 2 (metricRicci g) (q + 1) x) ≤
      2 ^ (2 + (q + 1) + 2) * nablaKRm04NormSqIntrinsic S (q + 1) t x := by
    convert hric using 2 <;> rfl
  have hinv : (1 / (2 * (Tm - t)))⁻¹ = 2 * (Tm - t) := by rw [one_div, inv_inv]
  rw [hinv]
  have hpow : (2 * (Tm - t)) ^ (2 + (q + 1)) = (2 * (Tm - t)) ^ (q + 3) := by ring_nf
  rw [hpow]
  have h0 : 0 ≤ (2 * (Tm - t)) ^ (q + 3) := by positivity
  calc (2 * (Tm - t)) ^ (q + 3) * ((-2) ^ 2 * normSq0S g x (2 + (q + 1))
        (iterCov g 2 (metricRicci g) (q + 1) x))
      ≤ (2 * (Tm - t)) ^ (q + 3) * ((-2) ^ 2 * (2 ^ (2 + (q + 1) + 2) *
        nablaKRm04NormSqIntrinsic S (q + 1) t x)) := by gcongr
    _ = 4 * 2 ^ (q + 1 + 4) * ((2 * (Tm - t)) ^ (q + 3) *
        nablaKRm04NormSqIntrinsic S (q + 1) t x) := by ring

theorem surfaceFlow_ha5_of_scalar_derivative_decay (hdim : Module.finrank ℝ E = 2) {Tm : ℝ}
    (hTm : 0 < Tm)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 Tm hTm)) (hS : IsSolutionOn S)
    (hrate : ∃ C δ : ℝ, 0 < δ ∧ ∀ t ∈ Ico 0 Tm, ∀ x,
      |S.scalar t x * (2 * (Tm - t)) - 2| ≤ C * (Tm - t) ^ δ)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 Tm)
    (hD : ∀ q : ℕ, ∃ C β : ℝ, 0 < β ∧ ∀ t ∈ Ico t₀ Tm, ∀ x,
      (2 * (Tm - t)) ^ (q + 3) * nablaKRm04NormSqIntrinsic S (q + 1) t x ≤ C * (Tm - t) ^ β) :
    (∃ t₀ < Tm, (∀ q : ℕ, ∃ C : ℝ, ∀ t (ht : t ∈ Ico t₀ Tm), ∀ z,
        metricCovDerivNorm q
          (scaleMetric (1 / (2 * (Tm - t))) (normalizedSurfaceMetric_pos ht.2)
            (S.family.metric t)) (S.family.metric 0) z ≤ C) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ t (ht : t ∈ Ico t₀ Tm), ∀ x (v : TangentSpace I x),
        c * (S.family.metric 0).inner x v v ≤
          (scaleMetric (1 / (2 * (Tm - t))) (normalizedSurfaceMetric_pos ht.2)
            (S.family.metric t)).inner x v v) ∧
    ∃ t₀ < Tm, ∃ C δ : ℝ, 0 < δ ∧ ∀ t ∈ Ico t₀ Tm, ∀ x,
      |S.scalar t x * (2 * (Tm - t)) - 2| ≤ C * (Tm - t) ^ δ := by
  obtain ⟨Cr, δ, hδ, hr⟩ := hrate
  choose CD β hβ hCD using hD
  set s₀ := sOf Tm t₀ with hs₀
  have hts : ∀ s, s₀ ≤ s → t₀ ≤ tOf Tm s := fun s hs => le_tOf hTm ht₀.2 hs
  have htpos : ∀ s, s₀ ≤ s → 0 < tOf Tm s := fun s hs => ht₀.1.trans_le (hts s hs)
  let C : ℕ → ℝ := fun q => Nat.casesOn q
    (Real.sqrt (2 * Cr ^ 2) * Tm ^ (2 * δ / 2))
    (fun q => Real.sqrt (4 * 2 ^ (q + 1 + 4) * max (CD q) 0) * Tm ^ (β q / 2))
  let γ : ℕ → ℝ := fun q => Nat.casesOn q (2 * δ) (fun q => β q)
  have hγ : ∀ q, 0 < γ q := by
    intro q
    cases q with
    | zero => exact mul_pos two_pos hδ
    | succ q => exact hβ q
  have hV : ∀ q : ℕ, ∀ s, s₀ ≤ s → ∀ x : M,
      tensor02CovDerivNormWith q (velField S s) (nMetric S (tOf Tm s)) (nMetric S (tOf Tm s)) x ≤
        C q * Real.exp (-(γ q * s)) := by
    intro q s hs x
    rw [tensor02CovDerivNormWith_eq_sqrt]
    have hts' := hts s hs
    have hlt := tOf_lt hTm s
    have hτ : 0 ≤ Tm - tOf Tm s := by linarith
    cases q with
    | zero =>
      rw [velField_norm_zero hdim S s x]
      apply sqrt_le_exp_rate hTm (by positivity)
      have h := hr (tOf Tm s) ⟨(htpos s hs).le, hlt⟩ x
      have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      rw [sq_abs] at h2
      calc 2 * (S.scalar (tOf Tm s) x * (2 * (Tm - tOf Tm s)) - 2) ^ 2
          ≤ 2 * (Cr * (Tm - tOf Tm s) ^ δ) ^ 2 := by linarith
        _ = 2 * Cr ^ 2 * (Tm - tOf Tm s) ^ (2 * δ) := by
          rw [mul_pow, ← Real.rpow_natCast ((Tm - tOf Tm s) ^ δ) 2, ← Real.rpow_mul hτ,
            Nat.cast_ofNat, mul_comm δ 2]
          ring
    | succ q =>
      apply sqrt_le_exp_rate hTm (by positivity)
      refine (velField_norm_succ hdim S s q x).trans ?_
      have h := hCD q (tOf Tm s) ⟨hts', hlt⟩ x
      have hX : 0 ≤ (Tm - tOf Tm s) ^ β q := Real.rpow_nonneg hτ _
      have h' : (2 * (Tm - tOf Tm s)) ^ (q + 3) * nablaKRm04NormSqIntrinsic S (q + 1) (tOf Tm s) x
          ≤ max (CD q) 0 * (Tm - tOf Tm s) ^ β q :=
        h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hX)
      calc 4 * 2 ^ (q + 1 + 4) * ((2 * (Tm - tOf Tm s)) ^ (q + 3) *
            nablaKRm04NormSqIntrinsic S (q + 1) (tOf Tm s) x)
          ≤ 4 * 2 ^ (q + 1 + 4) * (max (CD q) 0 * (Tm - tOf Tm s) ^ β q) := by gcongr
        _ = 4 * 2 ^ (q + 1 + 4) * max (CD q) 0 * (Tm - tOf Tm s) ^ β q := by ring
  obtain ⟨lam, hlam, kInf, hlow, -, hbd, -⟩ := exists_metric_limit_of_exp_decay_velocity
    (S.family.metric 0) (fun s => nMetric S (tOf Tm s)) (velField S) s₀ C γ hγ
    (fun s hs x W => nMetric_joint S hS (htpos s hs) x W)
    (fun s hs x v => velField_hasDerivAt S hS (htpos s hs) x v) hV
  refine ⟨⟨t₀, ht₀.2, fun q => ?_, lam, hlam, fun t ht x v => ?_⟩, ⟨0, hTm, Cr, δ, hδ, hr⟩⟩
  · obtain ⟨B, hB⟩ := hbd q
    refine ⟨B, fun t ht z => ?_⟩
    have h := (hB z).2 (sOf Tm t) (sOf_le_sOf hTm ht.1 ht.2)
    rw [tOf_sOf hTm ht.2, nMetric_eq S ht.2] at h
    exact h
  · have h := hlow (sOf Tm t) (sOf_le_sOf hTm ht.1 ht.2) x v
    rw [tOf_sOf hTm ht.2, nMetric_eq S ht.2] at h
    exact h

theorem surfaceFlow_ha5_of_scalar_rate [ConnectedSpace M] (hdim : Module.finrank ℝ E = 2)
    {Tm : ℝ} (hTm : 0 < Tm)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 Tm hTm)) (hS : IsSolutionOn S)
    (hscal : ∀ x, 0 < S.scalar 0 x)
    (hrate : ∃ C δ : ℝ, 0 < δ ∧ ∀ t ∈ Ico 0 Tm, ∀ x,
      |S.scalar t x * (2 * (Tm - t)) - 2| ≤ C * (Tm - t) ^ δ) :
    (∃ t₀ < Tm, (∀ q : ℕ, ∃ C : ℝ, ∀ t (ht : t ∈ Ico t₀ Tm), ∀ z,
        metricCovDerivNorm q
          (scaleMetric (1 / (2 * (Tm - t))) (normalizedSurfaceMetric_pos ht.2)
            (S.family.metric t)) (S.family.metric 0) z ≤ C) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ t (ht : t ∈ Ico t₀ Tm), ∀ x (v : TangentSpace I x),
        c * (S.family.metric 0).inner x v v ≤
          (scaleMetric (1 / (2 * (Tm - t))) (normalizedSurfaceMetric_pos ht.2)
            (S.family.metric t)).inner x v v) ∧
    ∃ t₀ < Tm, ∃ C δ : ℝ, 0 < δ ∧ ∀ t ∈ Ico t₀ Tm, ∀ x,
      |S.scalar t x * (2 * (Tm - t)) - 2| ≤ C * (Tm - t) ^ δ := by
  have ht₀ : Tm / 2 ∈ Ioo 0 Tm := ⟨by linarith, by linarith⟩
  exact surfaceFlow_ha5_of_scalar_derivative_decay hdim hTm S hS hrate ht₀
    (surfaceFlow_scalar_derivative_decay hdim hTm S hS hscal hrate ht₀)

end GC.Geometry
