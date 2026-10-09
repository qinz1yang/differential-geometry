/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Geodesic.Existence
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.FixedLocus
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.StratumRadius

noncomputable section

open Set Filter Matrix
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.LorentzExtremal

open Hyperbolic HyperbolicAction HyperbolicFaithful HyperbolicConvexity
open HyperbolicGeometry HyperbolicGeodesic FixedLocusGeometry OrbifoldStrata

variable {n : ℕ}

def futureCone : Set (LorVec n) :=
  {v | 0 ≤ tc v ∧ lorB v v ≤ 0}

theorem zero_mem_futureCone : (0 : LorVec n) ∈ futureCone := by
  simp [futureCone, tc, lorB, sdot]

theorem val_mem_futureCone (x : HUpper n) : x.val ∈ futureCone :=
  ⟨x.future.le, by rw [x.is_unit]; norm_num⟩

theorem isClosed_futureCone : IsClosed (futureCone (n := n)) :=
  (isClosed_le continuous_const (continuous_apply (Sum.inr 0))).inter
    (isClosed_le continuous_lorB_self continuous_const)

theorem smul_mem_futureCone {v : LorVec n} (hv : v ∈ futureCone)
    {c : ℝ} (hc : 0 ≤ c) : c • v ∈ futureCone := by
  refine ⟨by rw [tc_smul]; exact mul_nonneg hc hv.1, ?_⟩
  rw [lorB_smul_left, lorB_smul_right]
  exact mul_nonpos_of_nonneg_of_nonpos hc
    (mul_nonpos_of_nonneg_of_nonpos hc hv.2)

theorem add_mem_futureCone {u v : LorVec n}
    (hu : u ∈ futureCone) (hv : v ∈ futureCone) : u + v ∈ futureCone := by
  have huu : sdot u u ≤ tc u ^ 2 := by
    have h := hu.2
    dsimp [lorB] at h
    nlinarith
  have hvv : sdot v v ≤ tc v ^ 2 := by
    have h := hv.2
    dsimp [lorB] at h
    nlinarith
  have hsq : sdot u v ^ 2 ≤ (tc u * tc v) ^ 2 := by
    calc
      sdot u v ^ 2 ≤ sdot u u * sdot v v := sdot_sq_le u v
      _ ≤ tc u ^ 2 * tc v ^ 2 :=
        mul_le_mul huu hvv (sdot_self_nonneg v) (sq_nonneg _)
      _ = (tc u * tc v) ^ 2 := (mul_pow _ _ _).symm
  have huv : sdot u v ≤ tc u * tc v := by
    nlinarith [mul_nonneg hu.1 hv.1]
  refine ⟨by rw [tc_add]; exact add_nonneg hu.1 hv.1, ?_⟩
  dsimp [lorB]
  rw [sdot_add_left, sdot_add_right, sdot_add_right, sdot_comm v u, tc_add]
  nlinarith

theorem continuous_time : Continuous (fun x : HUpper n => tc x.val) := by
  have hc : Continuous (fun x : HUpper n => Real.cosh (dist basepointH x)) :=
    Real.continuous_cosh.comp (continuous_const.dist continuous_id)
  exact hc.congr GromovBoundary.cosh_dist_basepoint

theorem spatial_eq_cosh_dist (x : HUpper n) (i : Fin n) :
    x.val (Sum.inl i) =
      Real.sqrt 2 * tc x.val - Real.cosh (dist (boostH i) x) := by
  rw [cosh_dist]
  have hs : sdot (eBoost i) x.val = x.val (Sum.inl i) := by
    simp [sdot, eBoost_apply_inl]
  change x.val (Sum.inl i) =
    Real.sqrt 2 * tc x.val - -(sdot (eBoost i) x.val - tc (eBoost i) * tc x.val)
  rw [hs, show tc (eBoost i) = Real.sqrt 2 from eBoost_apply_inr i]
  ring

theorem continuous_val : Continuous (HUpper.val : HUpper n → LorVec n) := by
  apply continuous_pi
  intro a
  rcases a with i | j
  · exact ((continuous_const.mul continuous_time).sub
      (Real.continuous_cosh.comp (continuous_const.dist continuous_id))).congr
      (fun x => (spatial_eq_cosh_dist x i).symm)
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact continuous_time

theorem isCompact_timeSublevel (T : ℝ) :
    IsCompact {x : HUpper n | tc x.val ≤ T} := by
  apply (isCompact_closedBall (basepointH : HUpper n) (Real.arcosh (max 1 T))).of_isClosed_subset
    (isClosed_le continuous_time continuous_const)
  intro x hx
  rw [Metric.mem_closedBall, dist_comm, dist_basepoint]
  exact (Real.arcosh_le_arcosh x.future (lt_of_lt_of_le zero_lt_one (le_max_left _ _))).mpr
    (hx.trans (le_max_right _ _))

theorem exists_extremal_of_linear_bound (l : LorVec n →ₗ[ℝ] ℝ)
    {Z : Set (HUpper n)} (hZ : IsClosed Z)
    {M : ℝ} (hM : ∀ y ∈ Z, l y.val ≤ M)
    {z : HUpper n} (hz : z ∈ Z) (hlz : 0 < l z.val) :
    ∃ x ∈ Z, 0 < l x.val ∧ ∀ y ∈ Z, ∀ c : ℝ, 1 < c →
      ∀ w : LorVec n, w ∈ futureCone → l w = 0 →
        y.val ≠ c • x.val - w := by
  let S : Set (HUpper n) := {y | y ∈ Z ∧ l z.val ≤ l y.val ∧
    (l y.val / l z.val) • z.val - y.val ∈ futureCone}
  have hl : Continuous (fun y : HUpper n => l y.val) :=
    l.continuous_of_finiteDimensional.comp continuous_val
  have hSclosed : IsClosed S := by
    exact hZ.inter ((isClosed_le continuous_const hl).inter
      (isClosed_futureCone.preimage
        (((hl.div_const _).smul continuous_const).sub continuous_val)))
  have hzS : z ∈ S := by
    refine ⟨hz, le_rfl, ?_⟩
    rw [div_self hlz.ne', one_smul, sub_self]
    exact zero_mem_futureCone
  have hScompact : IsCompact S := by
    apply (isCompact_timeSublevel (M / l z.val * tc z.val)).of_isClosed_subset hSclosed
    intro y hy
    have htime := hy.2.2.1
    change 0 ≤ tc ((l y.val / l z.val) • z.val - y.val) at htime
    have he : tc ((l y.val / l z.val) • z.val - y.val) =
        (l y.val / l z.val) * tc z.val - tc y.val := rfl
    rw [he] at htime
    have hle : l y.val / l z.val * tc z.val ≤ M / l z.val * tc z.val :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hM y hy.1) hlz.le) z.future.le
    exact le_trans (by linarith) hle
  obtain ⟨x, hx, hmax⟩ := hScompact.exists_isMaxOn ⟨z, hzS⟩ hl.continuousOn
  have hlx : 0 < l x.val := hlz.trans_le hx.2.1
  refine ⟨x, hx.1, hlx, fun y hy c hc w hw hlw he => ?_⟩
  have hly : l y.val = c * l x.val := by
    rw [he, map_sub, map_smul, hlw, sub_zero, smul_eq_mul]
  have hgt : l x.val < l y.val := by
    rw [hly]
    nlinarith
  have hyS : y ∈ S := by
    refine ⟨hy, hx.2.1.trans hgt.le, ?_⟩
    have hcone := add_mem_futureCone
      (smul_mem_futureCone hx.2.2 (show 0 ≤ c by linarith)) hw
    have heq : (l y.val / l z.val) • z.val - y.val =
        c • ((l x.val / l z.val) • z.val - x.val) + w := by
      rw [hly, he]
      simp only [smul_sub, smul_smul]
      have hscalar : c * l x.val / l z.val = c * (l x.val / l z.val) := by ring
      rw [hscalar]
      abel
    rw [heq]
    exact hcone
  exact (not_lt_of_ge (hmax hyS)) hgt

theorem exists_lorB_representation (l : LorVec n →ₗ[ℝ] ℝ) :
    ∃ u : LorVec n, ∀ v : LorVec n, l v = lorB u v := by
  classical
  let u : LorVec n := Sum.elim
    (fun i => l (Pi.single (Sum.inl i) 1))
    (fun _ => -l (Pi.single (Sum.inr 0) 1))
  have hexpand (v : LorVec n) : l v =
      ∑ a : Fin n ⊕ Fin 1, v a * l (Pi.single a 1) := by
    have heq : (∑ a : Fin n ⊕ Fin 1, v a • Pi.single a (1 : ℝ)) = v := by
      ext a
      simp [Pi.single_apply]
    calc
      l v = l (∑ a : Fin n ⊕ Fin 1, v a • Pi.single a 1) := by rw [heq]
      _ = ∑ a : Fin n ⊕ Fin 1, v a * l (Pi.single a 1) := by
        simp only [map_sum, map_smul, smul_eq_mul]
  refine ⟨u, fun v => ?_⟩
  rw [hexpand]
  simp [lorB, sdot, tc, u, Fintype.sum_sum_type, mul_comm]

theorem linear_bounded_on_tube (l : LorVec n →ₗ[ℝ] ℝ)
    (V : Submodule ℝ (LorVec n)) (hker : V ≤ l.ker)
    {Z : Set (HUpper n)} {R : ℝ} (hR : 0 ≤ R)
    (hnear : ∀ x ∈ Z, ∃ p : HUpper n, p.val ∈ V ∧ dist x p ≤ R) :
    ∃ M : ℝ, ∀ x ∈ Z, |l x.val| ≤ M := by
  obtain ⟨u, hu⟩ := exists_lorB_representation l
  refine ⟨Real.sqrt (lorB u u * (Real.cosh R ^ 2 - 1)), fun x hx => ?_⟩
  obtain ⟨p, hp, hdist⟩ := hnear x hx
  have hup : lorB u p.val = 0 := (hu p.val).symm.trans (hker hp)
  have hupos : 0 ≤ lorB u u := lorB_self_nonneg_of_orth p.is_unit hup
  let a := Real.cosh (dist x p)
  let v := x.val - a • p.val
  have hxp : lorB x.val p.val = -a := by dsimp [a]; rw [cosh_dist]; ring
  have hvp : lorB v p.val = 0 := by
    dsimp [v]
    rw [lorB_sub_left, lorB_smul_left, p.is_unit, hxp]
    ring
  have hvv : lorB v v = a ^ 2 - 1 := by
    rw [show v = x.val - a • p.val from rfl, lorB_sub_smul_self,
      x.is_unit, p.is_unit, hxp]
    ring
  have huv : lorB u v = l x.val := by
    dsimp [v]
    rw [lorB_sub_right, lorB_smul_right, hup, mul_zero, sub_zero, ← hu]
  have hcs := lorB_sq_le_of_orth p.is_unit hup hvp
  rw [hvv, huv] at hcs
  have ha : a ≤ Real.cosh R :=
    Real.cosh_strictMonoOn.monotoneOn dist_nonneg hR hdist
  have ha0 : 0 ≤ a := (Real.cosh_pos _).le
  have hsq : a ^ 2 - 1 ≤ Real.cosh R ^ 2 - 1 := by
    nlinarith [Real.cosh_pos R]
  have hb : (l x.val) ^ 2 ≤ lorB u u * (Real.cosh R ^ 2 - 1) :=
    hcs.trans (mul_le_mul_of_nonneg_left hsq hupos)
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hb

theorem exists_extremal_near_subspace (V : Submodule ℝ (LorVec n))
    {Z : Set (HUpper n)} (hZ : IsClosed Z)
    {R : ℝ} (hR : 0 ≤ R)
    (hnear : ∀ x ∈ Z, ∃ p : HUpper n, p.val ∈ V ∧ dist x p ≤ R)
    {z : HUpper n} (hz : z ∈ Z) (hzV : z.val ∉ V) :
    ∃ x ∈ Z, x.val ∉ V ∧ ∀ y ∈ Z, ∀ c : ℝ, 1 < c →
      ∀ w ∈ V, w ∈ futureCone → y.val ≠ c • x.val - w := by
  obtain ⟨f, hfz, hfV⟩ := V.exists_le_ker_of_notMem hzV
  let l : LorVec n →ₗ[ℝ] ℝ := (f z.val)⁻¹ • f
  have hlz : l z.val = 1 := by
    change (f z.val)⁻¹ * f z.val = 1
    exact inv_mul_cancel₀ hfz
  have hlV : V ≤ l.ker := by
    intro w hw
    change (f z.val)⁻¹ * f w = 0
    rw [show f w = 0 from hfV hw, mul_zero]
  obtain ⟨M, hM⟩ := linear_bounded_on_tube l V hlV hR hnear
  obtain ⟨x, hx, hlx, hext⟩ := exists_extremal_of_linear_bound l hZ
    (fun y hy => (le_abs_self _).trans (hM y hy)) hz (by rw [hlz]; norm_num)
  refine ⟨x, hx, ?_, fun y hy c hc w hw hcone => hext y hy c hc w hcone (hlV hw)⟩
  intro hxV
  exact hlx.ne' (hlV hxV)

theorem exists_extremal_closure_fixedStratum (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    {ε : ℝ} (hε : 0 ≤ ε) {σ : Set (HUpper n)} (hσ : σ.Nonempty)
    {z : HUpper n} (hz : z ∈ fixedStratum hn Γ ε σ) (hzσ : z ∉ σ) :
    ∃ x ∈ closure (fixedStratum hn Γ ε σ), x ∉ σ ∧
      ∀ y ∈ closure (fixedStratum hn Γ ε σ), ∀ c : ℝ, 1 < c →
        ∀ w ∈ locusSpan σ, w ∈ futureCone → y.val ≠ c • x.val - w := by
  have he : fixedLocus hn (closedSmallSubgroup hn Γ ε z) = σ := hz
  have hspan : σ = {x : HUpper n | x.val ∈ locusSpan σ} := by
    simpa only [he] using fixedLocus_eq_preimage_span hn
      (closedSmallSubgroup hn Γ ε z) (he.symm ▸ hσ)
  obtain ⟨R, hR, hnear⟩ :=
    FiniteStratumRadius.exists_radius_closure_fixedStratum hn Γ hΓ hε hσ ⟨z, hz⟩
  have hnear' : ∀ x ∈ closure (fixedStratum hn Γ ε σ),
      ∃ p : HUpper n, p.val ∈ locusSpan σ ∧ dist x p ≤ R := by
    intro x hx
    obtain ⟨p, hp, hd⟩ := hnear x hx
    exact ⟨p, val_mem_locusSpan hp, hd⟩
  obtain ⟨x, hx, hxV, hext⟩ := exists_extremal_near_subspace (locusSpan σ)
    isClosed_closure hR hnear' (subset_closure hz) (by
      intro h
      apply hzσ
      rw [hspan]
      exact h)
  exact ⟨x, hx, fun h => hxV (val_mem_locusSpan h), hext⟩

theorem geodFromTo_val_outward {p x : HUpper n} (hpx : p ≠ x) (t : ℝ) :
    (geodFromTo p x hpx t).val =
      (Real.sinh t / Real.sinh (dist p x)) • x.val -
        (Real.sinh (t - dist p x) / Real.sinh (dist p x)) • p.val := by
  have hs : Real.sinh (dist p x) ≠ 0 := (Real.sinh_pos_iff.mpr (dist_pos.mpr hpx)).ne'
  ext a
  simp only [geodFromTo, dirVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [Real.sinh_sub]
  field_simp
  ring

theorem rayTo_neg_val (x : HUpper n) (ξ : HyperbolicBoundary.BoundaryH n) (s : ℝ) :
    (AsymptoticRays.rayTo x ξ (-s)).val =
      Real.exp s • x.val - (Real.sinh s / (-lorB x.val ξ.val)) • ξ.val := by
  have hdir : AsymptoticRays.dirTo x ξ = (-lorB x.val ξ.val)⁻¹ • ξ.val - x.val :=
    eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using Busemann.add_dirTo_eq x ξ)
  have he : Real.exp s = Real.cosh s + Real.sinh s := by
    rw [Real.cosh_eq, Real.sinh_eq]
    ring
  change Real.cosh (-s) • x.val + Real.sinh (-s) • AsymptoticRays.dirTo x ξ = _
  rw [Real.cosh_neg, Real.sinh_neg, hdir, he, div_eq_mul_inv]
  module

theorem geodFromTo_notMem_of_extremal (V : Submodule ℝ (LorVec n))
    {Z : Set (HUpper n)} {x : HUpper n}
    (hext : ∀ y ∈ Z, ∀ c : ℝ, 1 < c →
      ∀ w ∈ V, w ∈ futureCone → y.val ≠ c • x.val - w)
    {p : HUpper n} (hp : p.val ∈ V) (hpx : p ≠ x)
    {t : ℝ} (ht : dist p x < t) :
    geodFromTo p x hpx t ∉ Z := by
  intro hy
  have hs : 0 < Real.sinh (dist p x) := Real.sinh_pos_iff.mpr (dist_pos.mpr hpx)
  have hc : 1 < Real.sinh t / Real.sinh (dist p x) :=
    (one_lt_div hs).mpr (Real.sinh_lt_sinh.mpr ht)
  have ha : 0 ≤ Real.sinh (t - dist p x) / Real.sinh (dist p x) :=
    div_nonneg (Real.sinh_pos_iff.mpr (sub_pos.mpr ht)).le hs.le
  exact hext _ hy _ hc _ (V.smul_mem _ hp)
    (smul_mem_futureCone (val_mem_futureCone p) ha) (geodFromTo_val_outward hpx t)

theorem rayTo_neg_notMem_of_extremal (V : Submodule ℝ (LorVec n))
    {Z : Set (HUpper n)} {x : HUpper n}
    (hext : ∀ y ∈ Z, ∀ c : ℝ, 1 < c →
      ∀ w ∈ V, w ∈ futureCone → y.val ≠ c • x.val - w)
    {ξ : HyperbolicBoundary.BoundaryH n} (hξ : ξ.val ∈ V)
    {s : ℝ} (hs : 0 < s) :
    AsymptoticRays.rayTo x ξ (-s) ∉ Z := by
  intro hy
  have hc : 1 < Real.exp s := Real.one_lt_exp_iff.mpr hs
  have hcone : ξ.val ∈ futureCone :=
    ⟨by rw [ξ.tc_eq]; norm_num, by rw [ξ.is_null]⟩
  have ha : 0 ≤ Real.sinh s / (-lorB x.val ξ.val) :=
    div_nonneg (Real.sinh_pos_iff.mpr hs).le (Busemann.neg_lorB_upper_boundary_pos x ξ).le
  exact hext _ hy _ hc _ (V.smul_mem _ hξ) (smul_mem_futureCone hcone ha)
    (rayTo_neg_val x ξ s)

theorem exists_extremal_rays_closure_fixedStratum (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    {ε : ℝ} (hε : 0 ≤ ε) {σ : Set (HUpper n)} (hσ : σ.Nonempty)
    {z : HUpper n} (hz : z ∈ fixedStratum hn Γ ε σ) (hzσ : z ∉ σ) :
    ∃ x ∈ closure (fixedStratum hn Γ ε σ), x ∉ σ ∧
      (∀ p ∈ σ, ∀ hpx : p ≠ x, ∀ t : ℝ, dist p x < t →
        geodFromTo p x hpx t ∉ closure (fixedStratum hn Γ ε σ)) ∧
      (∀ ξ : HyperbolicBoundary.BoundaryH n, ξ.val ∈ locusSpan σ →
        ∀ s : ℝ, 0 < s →
          AsymptoticRays.rayTo x ξ (-s) ∉ closure (fixedStratum hn Γ ε σ)) := by
  obtain ⟨x, hx, hxσ, hext⟩ := exists_extremal_closure_fixedStratum hn Γ hΓ hε hσ hz hzσ
  refine ⟨x, hx, hxσ, ?_, ?_⟩
  · intro p hp hpx t ht
    exact geodFromTo_notMem_of_extremal (locusSpan σ) hext (val_mem_locusSpan hp) hpx ht
  · intro ξ hξ s hs
    exact rayTo_neg_notMem_of_extremal (locusSpan σ) hext hξ hs

end DifferentialGeometry.LorentzExtremal
