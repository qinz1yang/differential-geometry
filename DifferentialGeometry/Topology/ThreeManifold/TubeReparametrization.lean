import DifferentialGeometry.Topology.ThreeManifold.CutCap
import Mathlib.Geometry.Manifold.Instances.Icc
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Topology.Manifold.InverseFunction.ContDiffOn

set_option autoImplicit false
noncomputable section

open Set Manifold Filter Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SphericalTubeSystem

universe u
local notation "E1" => EuclideanSpace ℝ (Fin 1)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1
local notation "Unit" => Icc (0 : ℝ) 1
local notation "Interval" => Icc (-2 : ℝ) 2
local notation "CI" => ModelWithCorners.prod (𝓡 2) (𝓡∂ 1)
local notation "PI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
private local instance unitBounds : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
private local instance tubeBounds : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

private def parameterAffine : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ where
  toFun t := (t + 1) / 2
  invFun t := 2 * t - 1
  left_inv t := by dsimp; ring
  right_inv t := by dsimp; ring
  contMDiff_toFun := (by fun_prop : ContDiff ℝ ∞ (fun t : ℝ => (t + 1) / 2)).contMDiff
  contMDiff_invFun := (by fun_prop : ContDiff ℝ ∞ (fun t : ℝ => 2 * t - 1)).contMDiff

private def unitTubeParameter (t : ℝ) : Unit := projIcc 0 1 zero_le_one (parameterAffine t)

private theorem unitTubeParameter_eq {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    unitTubeParameter t = (⟨(t + 1) / 2, by constructor <;> linarith [ht.1, ht.2]⟩ : Unit) := by
  apply projIcc_of_mem

private theorem unitTubeParameter_val_eventually {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    (Subtype.val : Unit → ℝ) ∘ unitTubeParameter =ᶠ[𝓝 t] parameterAffine := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  rw [Function.comp_apply, unitTubeParameter_eq hs]
  rfl

private theorem unitTubeParameter_contMDiffAt {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    ContMDiffAt 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ unitTubeParameter t := by
  apply (ContMDiffAt.iff_comp_isImmersionAt
    ((isSmoothEmbedding_subtypeVal_Icc (x := (0 : ℝ)) (y := 1) (n := ∞)).isImmersion.isImmersionAt
      (unitTubeParameter t))).mpr
  refine ⟨continuous_projIcc.continuousAt.comp parameterAffine.continuous.continuousAt, ?_⟩
  exact (unitTubeParameter_val_eventually ht).contMDiffAt_iff.mpr parameterAffine.contMDiff.contMDiffAt

private theorem unitTubeParameter_injective_mfderiv {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 1) unitTubeParameter t) := by
  have hchain := mfderiv_comp t
    ((contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := 1) (n := ∞)).mdifferentiableAt (by simp))
    ((unitTubeParameter_contMDiffAt ht).mdifferentiableAt (by simp))
  rw [(unitTubeParameter_val_eventually ht).mfderiv_eq] at hchain
  replace hchain : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) parameterAffine t =
      (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : Unit → ℝ) (unitTubeParameter t)).comp
        (mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 1) unitTubeParameter t) :=
    (ContinuousLinearMap.ext fun _ => rfl).trans hchain
  have hinj : Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) parameterAffine t) :=
    (parameterAffine.mfderivToContinuousLinearEquiv (by simp) t).injective
  rw [hchain] at hinj
  change Injective ((mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : Unit → ℝ) (unitTubeParameter t)) ∘
    mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 1) unitTubeParameter t) at hinj
  exact hinj.of_comp

private def expandedTubeParameter (t : Unit) : Interval :=
  ⟨2 * t.val - 1, by constructor <;> linarith [t.property.1, t.property.2]⟩

private theorem expandedTubeParameter_contMDiff :
    ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ expandedTubeParameter := by
  apply (contMDiff_iff_comp_subtypeVal_Icc (n := ∞)).mpr
  have h : ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞
      (fun t : Unit => parameterAffine.symm t.val) :=
    parameterAffine.symm.contMDiff.comp contMDiff_subtypeVal_Icc
  exact ⟨h.continuous.subtype_mk _, h⟩

private theorem expandedTubeParameter_injective_mfderiv (t : Unit) :
    Injective (mfderiv (𝓡∂ 1) (𝓡∂ 1) expandedTubeParameter t) := by
  have hval := (contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := 1) (n := ∞)).mdifferentiableAt (by simp) (x := t)
  have hf := parameterAffine.symm.contMDiff.mdifferentiableAt (by simp) (x := t.val)
  have hchain := mfderiv_comp t hf hval
  have hi : Injective (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ)
      ((Subtype.val : Interval → ℝ) ∘ expandedTubeParameter) t) := by
    rw [show (Subtype.val : Interval → ℝ) ∘ expandedTubeParameter =
      parameterAffine.symm ∘ (Subtype.val : Unit → ℝ) from rfl, hchain]
    exact (parameterAffine.symm.mfderivToContinuousLinearEquiv (by simp) t.val).injective.comp
      ((isSmoothEmbedding_subtypeVal_Icc (x := (0 : ℝ)) (y := 1) (n := ∞)).isImmersion.isImmersionAt t
        |>.mfderiv_injective (by simp))
  rw [mfderiv_comp t
    ((contMDiff_subtypeVal_Icc (x := (-2 : ℝ)) (y := 2) (n := ∞)).mdifferentiableAt (by simp))
    (expandedTubeParameter_contMDiff.mdifferentiableAt (by simp))] at hi
  change Injective ((mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : Interval → ℝ) (expandedTubeParameter t)) ∘
    (mfderiv (𝓡∂ 1) (𝓡∂ 1) expandedTubeParameter t)) at hi
  exact hi.of_comp

private theorem expandedTubeParameter_injective : Injective expandedTubeParameter := by
  intro s t h
  apply Subtype.ext
  have h' := congrArg Subtype.val h
  change 2 * s.val - 1 = 2 * t.val - 1 at h'
  linarith

variable {M : ClosedOrientedManifold.{u} 3} (T : SphericalTubeSystem M)

def reparametrizedTube (a : T.Index) (Ψ : Diffeomorph CI CI (S2 × Unit) (S2 × Unit) ∞)
    (p : S2 × ℝ) : M.Carrier :=
  T.tube a ((Ψ (p.1, unitTubeParameter p.2)).1,
    expandedTubeParameter (Ψ (p.1, unitTubeParameter p.2)).2)

private theorem reparametrizedTube_contMDiffAt (a : T.Index)
    (Ψ : Diffeomorph CI CI (S2 × Unit) (S2 × Unit) ∞)
    {p : S2 × ℝ} (hp : p.2 ∈ Ioo (-1 : ℝ) 1) :
    ContMDiffAt PI (𝓡 3) ∞ (T.reparametrizedTube a Ψ) p := by
  have h1 : ContMDiffAt PI CI ∞ (Prod.map id unitTubeParameter) p :=
    contMDiffAt_id.prodMap (unitTubeParameter_contMDiffAt hp)
  have h2 : ContMDiff CI CI ∞ (Prod.map (id : S2 → S2) expandedTubeParameter) :=
    contMDiff_id.prodMap expandedTubeParameter_contMDiff
  exact (T.smooth a).contMDiff.contMDiffAt.comp p
    (h2.contMDiffAt.comp p (Ψ.contMDiff.contMDiffAt.comp p h1))

private theorem reparametrizedTube_injective_mfderiv (a : T.Index)
    (Ψ : Diffeomorph CI CI (S2 × Unit) (S2 × Unit) ∞)
    {p : S2 × ℝ} (hp : p.2 ∈ Ioo (-1 : ℝ) 1) :
    Injective (mfderiv PI (𝓡 3) (T.reparametrizedTube a Ψ) p) := by
  let j : S2 × ℝ → S2 × Unit := Prod.map id unitTubeParameter
  let k : S2 × Unit → S2 × Interval := Prod.map id expandedTubeParameter
  have hj : ContMDiffAt PI CI ∞ j p := contMDiffAt_id.prodMap (unitTubeParameter_contMDiffAt hp)
  have hk : ContMDiff CI CI ∞ k := contMDiff_id.prodMap expandedTubeParameter_contMDiff
  have hDj : Injective (mfderiv PI CI j p) := by
    rw [mfderiv_prodMap mdifferentiableAt_id
      ((unitTubeParameter_contMDiffAt hp).mdifferentiableAt (by simp)), mfderiv_id]
    exact Function.injective_id.prodMap (unitTubeParameter_injective_mfderiv hp)
  have hDk : Injective (mfderiv CI CI k (Ψ (j p))) := by
    rw [mfderiv_prodMap mdifferentiableAt_id
      (expandedTubeParameter_contMDiff.mdifferentiableAt (by simp)), mfderiv_id]
    exact Function.injective_id.prodMap (expandedTubeParameter_injective_mfderiv _)
  change Injective (mfderiv PI (𝓡 3) ((T.tube a) ∘ k ∘ Ψ ∘ j) p)
  rw [mfderiv_comp p ((T.smooth a).contMDiff.mdifferentiableAt (by simp))
    ((hk.contMDiffAt.comp p (Ψ.contMDiff.contMDiffAt.comp p hj)).mdifferentiableAt (by simp))]
  rw [mfderiv_comp p (hk.mdifferentiableAt (by simp))
    ((Ψ.contMDiff.contMDiffAt.comp p hj).mdifferentiableAt (by simp))]
  rw [mfderiv_comp p (Ψ.contMDiff.mdifferentiableAt (by simp)) (hj.mdifferentiableAt (by simp))]
  exact ((T.smooth a).isImmersion.isImmersionAt _ |>.mfderiv_injective (by simp)).comp
    (hDk.comp ((Ψ.mfderivToContinuousLinearEquiv (by simp) (j p)).injective.comp hDj))

theorem isLocalDiffeomorphAt_reparametrizedTube (a : T.Index)
    (Ψ : Diffeomorph CI CI (S2 × Unit) (S2 × Unit) ∞)
    {p : S2 × ℝ} (hp : p.2 ∈ Ioo (-1 : ℝ) 1) :
    IsLocalDiffeomorphAt PI (𝓡 3) ∞ (T.reparametrizedTube a Ψ) p := by
  let U : Set (S2 × ℝ) := {q | q.2 ∈ Ioo (-1 : ℝ) 1}
  have hU : IsOpen U := isOpen_Ioo.preimage continuous_snd
  have hs : ContMDiffOn PI (𝓡 3) ∞ (T.reparametrizedTube a Ψ) U :=
    fun q hq => (reparametrizedTube_contMDiffAt T a Ψ hq).contMDiffWithinAt
  let D : (E2 × ℝ) →L[ℝ] E3 := mfderiv PI (𝓡 3) (T.reparametrizedTube a Ψ) p
  have hD : Injective D := reparametrizedTube_injective_mfderiv T a Ψ hp
  let A : (E2 × ℝ) ≃L[ℝ] E3 :=
    (D.toLinearMap.linearEquivOfInjective hD (by simp)).toContinuousLinearEquiv
  exact Manifold.isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv
    (T.reparametrizedTube a Ψ) hs hU p hp A
    ((reparametrizedTube_contMDiffAt T a Ψ hp).mdifferentiableAt (by simp)).hasMFDerivAt

theorem reparametrizedTube_injOn (a : T.Index)
    (Ψ : Diffeomorph CI CI (S2 × Unit) (S2 × Unit) ∞) :
    InjOn (T.reparametrizedTube a Ψ) {p : S2 × ℝ | p.2 ∈ Ioo (-1 : ℝ) 1} := by
  intro p hp q hq heq
  have ht := (T.smooth a).isEmbedding.injective heq
  have hΨ : Ψ (p.1, unitTubeParameter p.2) = Ψ (q.1, unitTubeParameter q.2) :=
    Prod.ext (congrArg (fun z : S2 × Interval => z.1) ht)
      (expandedTubeParameter_injective (congrArg (fun z : S2 × Interval => z.2) ht))
  have hpq := Ψ.injective hΨ
  refine Prod.ext (congrArg (fun z : S2 × Unit => z.1) hpq) ?_
  have htime := congrArg (fun z : S2 × Unit => z.2.val) hpq
  rw [unitTubeParameter_eq hp, unitTubeParameter_eq hq] at htime
  dsimp at htime
  linarith

theorem reparametrizedTube_apply_of_preserves_time (a : T.Index)
    (Ψ : Diffeomorph CI CI (S2 × Unit) (S2 × Unit) ∞)
    (hΨ : ∀ p, (Ψ p).2 = p.2) (p : S2 × ℝ) (hp : p.2 ∈ Ioo (-1 : ℝ) 1) :
    T.reparametrizedTube a Ψ p = T.tube a
      ((Ψ (p.1, ⟨(p.2 + 1) / 2, by constructor <;> linarith [hp.1, hp.2]⟩)).1,
        ⟨p.2, by constructor <;> linarith [hp.1, hp.2]⟩) := by
  unfold reparametrizedTube
  rw [unitTubeParameter_eq hp, hΨ]
  congr 1
  refine Prod.ext rfl ?_
  exact Subtype.ext (by dsimp [expandedTubeParameter]; ring)

private def negateRadius : ℝ ≃ₘ[ℝ] ℝ where
  toFun t := -t
  invFun t := -t
  left_inv t := neg_neg t
  right_inv t := neg_neg t
  contMDiff_toFun := contMDiff_id.neg
  contMDiff_invFun := contMDiff_id.neg

theorem isLocalDiffeomorphAt_reparametrizedTube_comp_radius (a : T.Index)
    (Ψ : Diffeomorph CI CI (S2 × Unit) (S2 × Unit) ∞)
    (ρ : ℝ ≃ₘ[ℝ] ℝ) (side : Bool) {q : S2 × ℝ}
    (hq : ρ q.2 ∈ Ioo (-1 : ℝ) 1) :
    IsLocalDiffeomorphAt PI (𝓡 3) ∞
      (fun p : S2 × ℝ => T.reparametrizedTube a Ψ
        (p.1, if side then ρ p.2 else -ρ p.2)) q := by
  let D : ℝ ≃ₘ[ℝ] ℝ := if side then ρ else ρ.trans negateRadius
  let R : Diffeomorph PI PI (S2 × ℝ) (S2 × ℝ) ∞ :=
    (Diffeomorph.refl (𝓡 2) S2 ∞).prodCongr D
  have hr : (R q).2 ∈ Ioo (-1 : ℝ) 1 := by
    change (if side then ρ else ρ.trans negateRadius) q.2 ∈ Ioo (-1 : ℝ) 1
    cases side with
    | true => exact hq
    | false =>
      change -ρ q.2 ∈ Ioo (-1 : ℝ) 1
      constructor <;> linarith [hq.1,hq.2]
  have h := (R.isLocalDiffeomorph q).comp (𝓡 3) M.Carrier
    (T.isLocalDiffeomorphAt_reparametrizedTube a Ψ hr)
  cases side <;> exact h

theorem isLocalDiffeomorphAt_reparametrizedTube_comp_radius_of_strictMono (a : T.Index)
    (Ψ : Diffeomorph CI CI (S2 × Unit) (S2 × Unit) ∞)
    (ρ : ℝ ≃ₘ[ℝ] ℝ) (hρ : StrictMono (ρ : ℝ → ℝ))
    (hzero : ρ (1 / 4) = 0) (hone : ρ 1 = 1) (side : Bool)
    {q : S2 × ℝ} (hq : q.2 ∈ Ioo (1 / 4 : ℝ) 1) :
    IsLocalDiffeomorphAt PI (𝓡 3) ∞
      (fun p : S2 × ℝ => T.reparametrizedTube a Ψ
        (p.1, if side then ρ p.2 else -ρ p.2)) q := by
  apply T.isLocalDiffeomorphAt_reparametrizedTube_comp_radius a Ψ ρ side
  have hlo := hρ hq.1
  have hhi := hρ hq.2
  rw [hzero] at hlo
  rw [hone] at hhi
  exact ⟨lt_trans (by norm_num) hlo, hhi⟩

theorem reparametrizedTube_apply (a : T.Index)
    (Ψ : Diffeomorph CI CI (S2 × Unit) (S2 × Unit) ∞)
    (p : S2 × ℝ) (hp : p.2 ∈ Ioo (-1 : ℝ) 1) :
    T.reparametrizedTube a Ψ p =
      let q := Ψ (p.1, ⟨(p.2 + 1) / 2, by constructor <;> linarith [hp.1,hp.2]⟩)
      T.tube a (q.1, ⟨2 * q.2.val - 1, by constructor <;> linarith [q.2.property.1,q.2.property.2]⟩) := by
  unfold reparametrizedTube
  rw [unitTubeParameter_eq hp]
  rfl

end DifferentialGeometry.Topology.SphericalTubeSystem
