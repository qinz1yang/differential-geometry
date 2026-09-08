import DifferentialGeometry.Analysis.InnerProductSpace.SpectralBounds
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.Positive

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace
open Finset

private def finTailEmbedding {r k : ℕ} (hk : k ≤ r) : Fin k ↪ Fin r :=
  ⟨fun i => ⟨r - k + i.1, by omega⟩, fun i j hij => by
    apply Fin.ext
    simpa using congr_arg Fin.val hij⟩

private theorem card_fin_tail {r k : ℕ} (hk : k ≤ r) :
    ((Finset.univ : Finset (Fin r)).filter fun i => r - k ≤ i.1).card = k := by
  let f := finTailEmbedding hk
  have htail : ((Finset.univ : Finset (Fin r)).filter fun i => r - k ≤ i.1) =
      (Finset.univ : Finset (Fin k)).map f := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro hi
      refine ⟨⟨i.1 - (r - k), by omega⟩, ?_⟩
      apply Fin.ext
      change r - k + (i.1 - (r - k)) = i.1
      omega
    · rintro ⟨j, rfl⟩
      change r - k ≤ r - k + j.1
      omega
  rw [htail, Finset.card_map, Finset.card_univ, Fintype.card_fin]

private theorem sum_fin_tail {r k : ℕ} (hk : k ≤ r) {M : Type*}
    [AddCommMonoid M] (f : Fin r → M) :
    ∑ i : Fin k, f (finTailEmbedding hk i) =
      ∑ i ∈ (Finset.univ.filter fun i : Fin r => r - k ≤ i.1), f i := by
  apply Finset.sum_bij (fun i _ => finTailEmbedding hk i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change r - k ≤ r - k + i.1
    omega
  · intro i hi j hj hij
    exact (finTailEmbedding hk).injective hij
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨⟨j.1 - (r - k), by omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    change r - k + (j.1 - (r - k)) = j.1
    omega
  · intro i hi
    rfl

private theorem sum_tail_le_weighted_sum {r k : ℕ} (hk : k ≤ r)
    {lam a : Fin r → ℝ} (hlam : Antitone lam)
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    (hasum : ∑ i, a i = k) :
    ∑ i ∈ (Finset.univ.filter fun i : Fin r => r - k ≤ i.1), lam i ≤
      ∑ i, lam i * a i := by
  by_cases hk0 : k = 0
  · subst k
    have hazero : ∀ i, a i = 0 := by
      intro i
      have hi : a i ≤ ∑ j, a j :=
        Finset.single_le_sum (fun j _ => ha0 j) (Finset.mem_univ i)
      rw [hasum] at hi
      exact le_antisymm (by simpa using hi) (ha0 i)
    have hempty : ((Finset.univ : Finset (Fin r)).filter fun i => r ≤ i.1) = ∅ := by
      ext i
      simp
    simp only [Nat.sub_zero]
    rw [hempty]
    simp [hazero]
  let tail := (Finset.univ : Finset (Fin r)).filter fun i => r - k ≤ i.1
  let head := (Finset.univ : Finset (Fin r)).filter fun i => ¬r - k ≤ i.1
  let m : Fin r := ⟨r - k, by omega⟩
  have hcard : tail.card = k := card_fin_tail hk
  have hpart (f : Fin r → ℝ) : ∑ i ∈ tail, f i + ∑ i ∈ head, f i = ∑ i, f i := by
    exact Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin r => r - k ≤ i.1) f
  have hbalance : ∑ i ∈ head, a i = ∑ i ∈ tail, (1 - a i) := by
    have hparta := hpart a
    have hdeficit : ∑ i ∈ tail, (1 - a i) = k - ∑ i ∈ tail, a i := by
      rw [Finset.sum_sub_distrib]
      simp [hcard]
    rw [hdeficit]
    linarith
  have hhead : lam m * (∑ i ∈ head, a i) ≤ ∑ i ∈ head, lam i * a i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have him : i ≤ m := by
      simp only [head, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      apply Fin.le_iff_val_le_val.mpr
      change i.1 ≤ r - k
      omega
    have hli : lam m ≤ lam i := hlam him
    nlinarith [ha0 i]
  have htail : ∑ i ∈ tail, lam i * (1 - a i) ≤
      lam m * (∑ i ∈ tail, (1 - a i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hmi : m ≤ i := by
      simp only [tail, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact Fin.le_iff_val_le_val.mpr hi
    have hli : lam i ≤ lam m := hlam hmi
    nlinarith [ha1 i]
  change ∑ i ∈ tail, lam i ≤ _
  calc
    ∑ i ∈ tail, lam i =
        ∑ i ∈ tail, lam i * a i + ∑ i ∈ tail, lam i * (1 - a i) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i ∈ tail, lam i * a i + lam m * (∑ i ∈ tail, (1 - a i)) :=
      by simpa [add_comm] using add_le_add_right htail (∑ i ∈ tail, lam i * a i)
    _ = ∑ i ∈ tail, lam i * a i + lam m * (∑ i ∈ head, a i) := by
      rw [hbalance]
    _ ≤ ∑ i ∈ tail, lam i * a i + ∑ i ∈ head, lam i * a i := by
      simpa [add_comm] using add_le_add_right hhead (∑ i ∈ tail, lam i * a i)
    _ = ∑ i, lam i * a i := hpart (fun i => lam i * a i)

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem LinearMap.IsPositive.inner_apply_self_eq_zero_iff
    {T : E →ₗ[ℝ] E} (hT : T.IsPositive) (x : E) :
    ⟪T x, x⟫_ℝ = 0 ↔ T x = 0 := by
  constructor
  · intro hx
    let p : ℝ := ⟪T x, T x⟫_ℝ
    let q : ℝ := ⟪T (T x), T x⟫_ℝ
    have hp : 0 ≤ p := by
      dsimp [p]
      exact real_inner_self_nonneg
    have hq : 0 ≤ q := hT.inner_nonneg_left (T x)
    have hqone : 0 < q + 1 := by linarith
    have hpoly (t : ℝ) : 0 ≤ 2 * t * p + t ^ 2 * q := by
      have h := hT.inner_nonneg_left (x + t • T x)
      dsimp [p, q]
      simp only [map_add, map_smul, inner_add_left, inner_add_right,
        inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial] at h
      rw [hT.isSymmetric (T x) x, hx] at h
      nlinarith
    have hspecial := hpoly (-p / (q + 1))
    have hpzero : p = 0 := by
      field_simp at hspecial
      nlinarith
    have hnorm : ‖T x‖ = 0 := by
      have hsq : ‖T x‖ ^ 2 = 0 := by
        simpa [p, real_inner_self_eq_norm_sq] using hpzero
      nlinarith [norm_nonneg (T x)]
    exact norm_eq_zero.mp hnorm
  · intro hx
    rw [hx, inner_zero_left]

omit [FiniteDimensional ℝ E] in
theorem LinearMap.IsPositive.ker_le_ker_of_inner_apply_self_eq_zero
    {S T : E →ₗ[ℝ] E} (hT : T.IsPositive)
    (hzero : ∀ x ∈ S.ker, ⟪T x, x⟫_ℝ = 0) : S.ker ≤ T.ker := by
  intro x hx
  exact LinearMap.mem_ker.mpr
    ((hT.inner_apply_self_eq_zero_iff x).mp (hzero x hx))

omit [FiniteDimensional ℝ E] in
theorem LinearMap.IsSymmetric.ker_le_ker_of_commute_of_inner_apply_self_eq_zero
    {S T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (hcomm : Commute S T)
    (hzero : ∀ x ∈ S.ker, ⟪T x, x⟫_ℝ = 0) : S.ker ≤ T.ker := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  have hTx : S (T x) = 0 := by
    have h := LinearMap.congr_fun hcomm.eq x
    simpa [Module.End.mul_apply, hx] using h
  have hsum : S (x + T x) = 0 := by simp [hx, hTx]
  have h := hzero (x + T x) (LinearMap.mem_ker.mpr hsum)
  simp only [map_add, inner_add_left, inner_add_right] at h
  rw [hzero x (LinearMap.mem_ker.mpr hx),
    hzero (T x) (LinearMap.mem_ker.mpr hTx), hT (T x) x] at h
  exact inner_self_eq_zero.mp (by nlinarith : ⟪T x, T x⟫_ℝ = 0)

omit [FiniteDimensional ℝ E] in
theorem LinearMap.IsPositive.sub_smul_rankOne_of_eigenvector
    {T : E →ₗ[ℝ] E} (hT : T.IsPositive)
    {e : E} (he : ‖e‖ = 1) {eigenvalue : ℝ}
    (hTe : T e = eigenvalue • e) :
    (T - eigenvalue • (InnerProductSpace.rankOne ℝ e e).toLinearMap).IsPositive := by
  rw [LinearMap.isPositive_iff]
  constructor
  · have hrank :
        (InnerProductSpace.rankOne ℝ e e).toLinearMap.IsSymmetric :=
      InnerProductSpace.isSymmetric_rankOne_self e
    exact hT.isSymmetric.sub (hrank.smul (by simp))
  · intro x
    let c : ℝ := ⟪e, x⟫_ℝ
    let y : E := x - c • e
    have hxy : x = y + c • e := by simp [y]
    have hey : ⟪e, y⟫_ℝ = 0 := by
      simp [y, c, inner_sub_right, inner_smul_right, he]
    have hye : ⟪y, e⟫_ℝ = 0 := by simpa [real_inner_comm] using hey
    have hTye : ⟪T y, e⟫_ℝ = 0 := by
      rw [hT.isSymmetric y e, hTe, inner_smul_right, hye, mul_zero]
    have hquad : ⟪T x, x⟫_ℝ = ⟪T y, y⟫_ℝ + eigenvalue * c ^ 2 := by
      rw [hxy, map_add, map_smul, hTe]
      simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
      simp [hTye, hey, he]
      ring
    change 0 ≤
      ⟪T x - eigenvalue • (InnerProductSpace.rankOne ℝ e e) x, x⟫_ℝ
    simp only [InnerProductSpace.rankOne_apply, inner_sub_left, inner_smul_left]
    simp only [starRingEnd_apply, star_trivial]
    dsimp only [c] at hquad ⊢
    rw [hquad]
    nlinarith [hT.inner_nonneg_left y]

namespace LinearMap.IsSymmetric

noncomputable def lowerKyFanSum {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (k : ℕ) : ℝ :=
  ∑ i ∈ (Finset.univ.filter fun i : Fin (Module.finrank ℝ E) =>
    Module.finrank ℝ E - k ≤ i.1), hT.eigenvalues rfl i

theorem lowerKyFanSum_finrank {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric) :
    hA.lowerKyFanSum (Module.finrank ℝ E) = LinearMap.trace ℝ E A := by
  rw [lowerKyFanSum]
  simp only [Nat.sub_self, Nat.zero_le, Finset.filter_true]
  have h := hA.trace_eq_sum_eigenvalues rfl
  simpa only [RCLike.ofReal_real_eq_id, id_eq] using h.symm

theorem lowerKyFanSum_one_eq_iInf_rayleighQuotient
    {A : E →L[ℝ] E} (hA : A.toLinearMap.IsSymmetric) :
    hA.lowerKyFanSum 1 = ⨅ v : {v : E // v ≠ 0}, A.rayleighQuotient v := by
  by_cases hn : Module.finrank ℝ E = 0
  · let : Subsingleton E := Module.finrank_zero_iff.mp hn
    let : IsEmpty {v : E // v ≠ 0} := ⟨fun v => v.2 (Subsingleton.elim _ _)⟩
    rw [lowerKyFanSum]
    have hi : IsEmpty (Fin (Module.finrank ℝ E)) := by rw [hn]; infer_instance
    simp only [Finset.univ_eq_empty, Finset.filter_empty, Finset.sum_empty]
    rw [iInf, Set.range_eq_empty, Real.sInf_empty]
  · obtain ⟨n, hn'⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hlast : (Finset.univ.filter fun i : Fin (Module.finrank ℝ E) =>
        Module.finrank ℝ E - 1 ≤ i.1) = {⟨n, by omega⟩} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hi; apply Fin.ext; dsimp; omega
      · rintro rfl; dsimp; omega
    rw [lowerKyFanSum, hlast, Finset.sum_singleton]
    have hm := hA.iInf_rayleighQuotient_eq_eigenvalues_last hn'
    rw [hm]
    have htransport (m : ℕ) (hm : Module.finrank ℝ E = m)
        (i : Fin (Module.finrank ℝ E)) :
        hA.eigenvalues rfl i = hA.eigenvalues hm (Fin.cast hm i) := by
      subst m; rfl
    rw [htransport (n + 1) hn']
    congr 1

theorem lowerKyFanSum_le_frame {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    {k : ℕ} (hk : k ≤ Module.finrank ℝ E) {e : Fin k → E} (he : Orthonormal ℝ e) :
    hT.lowerKyFanSum k ≤ ∑ i, ⟪T (e i), e i⟫_ℝ := by
  let b := hT.eigenvectorBasis (n := Module.finrank ℝ E) rfl
  let a : Fin (Module.finrank ℝ E) → ℝ := fun j => ∑ i, ⟪e i, b j⟫_ℝ ^ 2
  have ha0 (j) : 0 ≤ a j := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have ha1 (j) : a j ≤ 1 := by
    have h := he.sum_inner_products_le (b j) (s := Finset.univ)
    simpa [a, OrthonormalBasis.norm_eq_one, real_inner_comm, Real.norm_eq_abs,
      sq_abs] using h
  have hasum : ∑ j, a j = k := by
    simp only [a]
    rw [Finset.sum_comm]
    calc
      ∑ i : Fin k, ∑ j, ⟪e i, b j⟫_ℝ ^ 2 = ∑ i : Fin k, ‖e i‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        exact b.sum_sq_inner_left (e i)
      _ = k := by simp [he.norm_eq_one]
  have hmass := sum_tail_le_weighted_sum hk (hT.eigenvalues_antitone rfl)
    ha0 ha1 hasum
  rw [lowerKyFanSum]
  refine hmass.trans_eq ?_
  simp only [a, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hTe : T (e i) = ∑ j, (hT.eigenvalues rfl j * ⟪b j, e i⟫_ℝ) • b j := by
    conv_lhs => rw [← b.sum_repr' (e i)]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [map_smul, hT.apply_eigenvectorBasis rfl]
    simp only [smul_smul]
    change (⟪b j, e i⟫_ℝ * hT.eigenvalues rfl j) • b j =
      (hT.eigenvalues rfl j * ⟪b j, e i⟫_ℝ) • b j
    rw [mul_comm]
  rw [hTe, sum_inner]
  apply Finset.sum_congr rfl
  intro j hj
  rw [inner_smul_left, real_inner_comm]
  simp [pow_two, mul_comm, mul_left_comm]

theorem exists_eigenframe_lowerKyFanSum_eq {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    {k : ℕ} (hk : k ≤ Module.finrank ℝ E) :
    ∃ e : Fin k → E, ∃ eigenvalue : Fin k → ℝ,
      Orthonormal ℝ e ∧
      (∀ i, T (e i) = eigenvalue i • e i) ∧
      ∑ i, eigenvalue i = hT.lowerKyFanSum k := by
  let b := hT.eigenvectorBasis (n := Module.finrank ℝ E) rfl
  let e : Fin k → E := fun i => b (finTailEmbedding hk i)
  let eigenvalue : Fin k → ℝ :=
    fun i => hT.eigenvalues rfl (finTailEmbedding hk i)
  refine ⟨e, eigenvalue, b.orthonormal.comp (finTailEmbedding hk)
    (finTailEmbedding hk).injective, ?_, ?_⟩
  · intro i
    exact hT.apply_eigenvectorBasis rfl (finTailEmbedding hk i)
  exact (sum_fin_tail hk (hT.eigenvalues rfl)).trans (by rfl)

theorem exists_frame_lowerKyFanSum_eq {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    {k : ℕ} (hk : k ≤ Module.finrank ℝ E) :
    ∃ e : Fin k → E, Orthonormal ℝ e ∧
      ∑ i, ⟪T (e i), e i⟫_ℝ = hT.lowerKyFanSum k := by
  obtain ⟨e, eigenvalue, he, heigen, hsum⟩ :=
    hT.exists_eigenframe_lowerKyFanSum_eq hk
  refine ⟨e, he, ?_⟩
  calc
    ∑ i, ⟪T (e i), e i⟫_ℝ = ∑ i, eigenvalue i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [heigen i, inner_smul_left]
      simp [he.norm_eq_one]
    _ = hT.lowerKyFanSum k := hsum

theorem lowerKyFanSum_eq_of_intertwining
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    {T : E →ₗ[ℝ] E} {S : F →ₗ[ℝ] F}
    (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (e : E ≃ₗᵢ[ℝ] F) (hcomm : ∀ x, S (e x) = e (T x))
    {k : ℕ} (hk : k ≤ Module.finrank ℝ E) :
    hT.lowerKyFanSum k = hS.lowerKyFanSum k := by
  have hkF : k ≤ Module.finrank ℝ F := hk.trans_eq e.toLinearEquiv.finrank_eq
  obtain ⟨v, hv, hvsum⟩ := hT.exists_frame_lowerKyFanSum_eq hk
  obtain ⟨w, hw, hwsum⟩ := hS.exists_frame_lowerKyFanSum_eq hkF
  apply le_antisymm
  · calc
      hT.lowerKyFanSum k ≤ ∑ i, ⟪T (e.symm (w i)), e.symm (w i)⟫_ℝ :=
        hT.lowerKyFanSum_le_frame hk (hw.comp_linearIsometryEquiv e.symm)
      _ = ∑ i, ⟪S (w i), w i⟫_ℝ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← e.inner_map_map]
        simp only [LinearIsometryEquiv.apply_symm_apply]
        rw [← hcomm, LinearIsometryEquiv.apply_symm_apply]
      _ = hS.lowerKyFanSum k := hwsum
  · calc
      hS.lowerKyFanSum k ≤ ∑ i, ⟪S (e (v i)), e (v i)⟫_ℝ :=
        hS.lowerKyFanSum_le_frame hkF (hv.comp_linearIsometryEquiv e)
      _ = ∑ i, ⟪T (v i), v i⟫_ℝ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hcomm, e.inner_map_map]
      _ = hT.lowerKyFanSum k := hvsum


private theorem trace_starProjection_comp_eq_sum {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    {U : Submodule ℝ E} [U.HasOrthogonalProjection] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ U) :
    LinearMap.trace ℝ E ((U.starProjection : E →ₗ[ℝ] E) ∘ₗ T) =
      ∑ i, ⟪T (b i), b i⟫_ℝ := by
  have hproj := congr_arg ContinuousLinearMap.toLinearMap b.starProjection_eq_sum_rankOne
  have hcompSum :
      T ∘ₗ (∑ i, InnerProductSpace.rankOne ℝ (b i : E) (b i : E)).toLinearMap =
        ∑ i, T ∘ₗ (InnerProductSpace.rankOne ℝ (b i : E) (b i : E)).toLinearMap := by
    ext x
    simp
  change LinearMap.trace ℝ E ((U.starProjection : E →ₗ[ℝ] E) ∘ₗ T) = _
  rw [LinearMap.trace_comp_comm']
  rw [hproj, hcompSum, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hcomp : T ∘ₗ (InnerProductSpace.rankOne ℝ (b i : E) (b i : E)).toLinearMap =
      (InnerProductSpace.rankOne ℝ (T (b i : E)) (b i : E)).toLinearMap := by
    exact congr_arg ContinuousLinearMap.toLinearMap
      (InnerProductSpace.comp_rankOne (b i : E) (b i : E) T.toContinuousLinearMap)
  rw [hcomp, InnerProductSpace.trace_rankOne]
  exact (hT (b i) (b i)).symm

theorem lowerKyFanSum_le_trace_projection_comp {T P : E →ₗ[ℝ] E}
    (hT : T.IsSymmetric) (hP : P.IsSymmetricProjection) {k : ℕ}
    (hPrank : Module.finrank ℝ P.range = k) :
    hT.lowerKyFanSum k ≤ LinearMap.trace ℝ E (P ∘ₗ T) := by
  have hk : k ≤ Module.finrank ℝ E := hPrank ▸ P.range.finrank_le
  obtain ⟨hU, hPU⟩ := LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp hP
  let _ : P.range.HasOrthogonalProjection := hU
  let b : OrthonormalBasis (Fin k) ℝ P.range := hPrank ▸ stdOrthonormalBasis ℝ P.range
  let e : Fin k → E := fun i => b i
  have he : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro i j
    exact b.inner_eq_ite i j
  have hframe := hT.lowerKyFanSum_le_frame hk he
  rw [hPU, trace_starProjection_comp_eq_sum hT b]
  exact hframe

theorem exists_projection_lowerKyFanSum_eq {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    {k : ℕ} (hk : k ≤ Module.finrank ℝ E) :
    ∃ P : E →ₗ[ℝ] E, P.IsSymmetricProjection ∧ Module.finrank ℝ P.range = k ∧
      LinearMap.trace ℝ E (P ∘ₗ T) = hT.lowerKyFanSum k := by
  classical
  obtain ⟨e, he, henergy⟩ := hT.exists_frame_lowerKyFanSum_eq hk
  let U : Submodule ℝ E := Submodule.span ℝ ((Finset.univ.image e : Finset E) : Set E)
  let _ : U.HasOrthogonalProjection := inferInstance
  let b : OrthonormalBasis (Finset.univ : Finset (Fin k)) ℝ U :=
    OrthonormalBasis.span he Finset.univ
  let P : E →ₗ[ℝ] E := U.starProjection
  refine ⟨P, Submodule.isSymmetricProjection_starProjection U, ?_, ?_⟩
  · have hrange : P.range = U := by
      exact Submodule.range_starProjection U
    rw [hrange]
    simpa [U] using Module.finrank_eq_card_basis b.toBasis
  · rw [show P = (U.starProjection : E →ₗ[ℝ] E) by rfl,
      trace_starProjection_comp_eq_sum hT b]
    have hb (i : (Finset.univ : Finset (Fin k))) : (b i : E) = e i.1 := by
      simpa only [b] using OrthonormalBasis.span_apply he Finset.univ i
    simp_rw [hb]
    rw [← Finset.sum_subtype Finset.univ (by simp) (fun i => ⟪T (e i), e i⟫_ℝ)]
    simpa using henergy

omit [FiniteDimensional ℝ E] in
private theorem frame_energy_add_smul_id {T : E →ₗ[ℝ] E} {k : ℕ}
    {e : Fin k → E} (he : Orthonormal ℝ e) (c : ℝ) :
    ∑ i, ⟪(T + c • (LinearMap.id : E →ₗ[ℝ] E)) (e i), e i⟫_ℝ =
      ∑ i, ⟪T (e i), e i⟫_ℝ + k * c := by
  simp_rw [add_apply, smul_apply, LinearMap.id_apply, inner_add_left, inner_smul_left]
  rw [Finset.sum_add_distrib]
  simp [he.norm_eq_one, mul_comm]

theorem lowerKyFanSum_add_smul_id {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    {k : ℕ} (hk : k ≤ Module.finrank ℝ E) (c : ℝ) :
    (hT.add (LinearMap.IsSymmetric.id.smul (by simp : starRingEnd ℝ c = c))).lowerKyFanSum k =
      hT.lowerKyFanSum k + k * c := by
  let hS : (T + c • (LinearMap.id : E →ₗ[ℝ] E)).IsSymmetric :=
    hT.add (LinearMap.IsSymmetric.id.smul (by simp))
  obtain ⟨eT, heT, hminT⟩ := hT.exists_frame_lowerKyFanSum_eq hk
  obtain ⟨eS, heS, hminS⟩ := hS.exists_frame_lowerKyFanSum_eq hk
  have hupper := hS.lowerKyFanSum_le_frame hk heT
  have hlower := hT.lowerKyFanSum_le_frame hk heS
  rw [frame_energy_add_smul_id heT c, hminT] at hupper
  have hrelS := frame_energy_add_smul_id (T := T) heS c
  rw [hminS] at hrelS
  change hS.lowerKyFanSum k = _
  linarith

private theorem lowerKyFanSum_sub_le {T S : E →L[ℝ] E}
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) {k : ℕ}
    (hk : k ≤ Module.finrank ℝ E) :
    hT.lowerKyFanSum k - hS.lowerKyFanSum k ≤ k * ‖T - S‖ := by
  obtain ⟨e, he, hminS⟩ := hS.exists_frame_lowerKyFanSum_eq hk
  change (∑ i, ⟪S (e i), e i⟫_ℝ) = hS.lowerKyFanSum k at hminS
  have hframe := hT.lowerKyFanSum_le_frame hk he
  have hdiff :
      (∑ i, ⟪T (e i), e i⟫_ℝ) - (∑ i, ⟪S (e i), e i⟫_ℝ) =
        ∑ i, ⟪(T - S) (e i), e i⟫_ℝ := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp [inner_sub_left]
  have hsumabs : |∑ i, ⟪(T - S) (e i), e i⟫_ℝ| ≤ k * ‖T - S‖ := by
    calc
      |∑ i, ⟪(T - S) (e i), e i⟫_ℝ| ≤
          ∑ i, |⟪(T - S) (e i), e i⟫_ℝ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin k, ‖T - S‖ := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          |⟪(T - S) (e i), e i⟫_ℝ| = ‖⟪(T - S) (e i), e i⟫_ℝ‖ := by
            simp only [Real.norm_eq_abs]
          _ ≤ ‖(T - S) (e i)‖ * ‖e i‖ := norm_inner_le_norm _ _
          _ ≤ (‖T - S‖ * ‖e i‖) * ‖e i‖ :=
            mul_le_mul_of_nonneg_right ((T - S).le_opNorm (e i)) (norm_nonneg _)
          _ = ‖T - S‖ := by rw [he.norm_eq_one, mul_one, mul_one]
      _ = k * ‖T - S‖ := by simp
  calc
    hT.lowerKyFanSum k - hS.lowerKyFanSum k ≤
        (∑ i, ⟪T (e i), e i⟫_ℝ) - (∑ i, ⟪S (e i), e i⟫_ℝ) := by
      rw [hminS]
      exact sub_le_sub_right hframe _
    _ = ∑ i, ⟪(T - S) (e i), e i⟫_ℝ := hdiff
    _ ≤ |∑ i, ⟪(T - S) (e i), e i⟫_ℝ| := le_abs_self _
    _ ≤ k * ‖T - S‖ := hsumabs

theorem abs_lowerKyFanSum_sub_le {T S : E →L[ℝ] E}
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) {k : ℕ}
    (hk : k ≤ Module.finrank ℝ E) :
    |hT.lowerKyFanSum k - hS.lowerKyFanSum k| ≤ k * ‖T - S‖ := by
  rw [abs_le]
  constructor
  · have h := lowerKyFanSum_sub_le hS hT hk
    rw [norm_sub_rev] at h
    linarith
  · exact lowerKyFanSum_sub_le hT hS hk

theorem lipschitzWith_lowerKyFanSum (k : ℕ) (hk : k ≤ Module.finrank ℝ E) :
    LipschitzWith (k : NNReal) (fun T : {T : E →L[ℝ] E // T.IsSymmetric} =>
      T.2.lowerKyFanSum k) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro T S
  simpa [Real.dist_eq, Subtype.dist_eq, dist_eq_norm] using
    abs_lowerKyFanSum_sub_le T.2 S.2 hk

theorem continuous_lowerKyFanSum (k : ℕ) (hk : k ≤ Module.finrank ℝ E) :
    Continuous (fun T : {T : E →L[ℝ] E // T.IsSymmetric} => T.2.lowerKyFanSum k) :=
  (lipschitzWith_lowerKyFanSum k hk).continuous

theorem lowerKyFanSum_nonneg {T : E →ₗ[ℝ] E} (hT : T.IsPositive) (k : ℕ) :
    0 ≤ hT.isSymmetric.lowerKyFanSum k := by
  rw [lowerKyFanSum]
  exact Finset.sum_nonneg fun i _ => hT.nonneg_eigenvalues rfl i

theorem lowerKyFanSum_pos_iff_finrank_ker_lt {T : E →ₗ[ℝ] E} (hT : T.IsPositive)
    {k : ℕ} (hk : k ≤ Module.finrank ℝ E) :
    0 < hT.isSymmetric.lowerKyFanSum k ↔ Module.finrank ℝ T.ker < k := by
  let tail := (Finset.univ : Finset (Fin (Module.finrank ℝ E))).filter fun i =>
    Module.finrank ℝ E - k ≤ i.1
  let zeroIndices := (Finset.univ : Finset (Fin (Module.finrank ℝ E))).filter fun i =>
    hT.isSymmetric.eigenvalues rfl i = 0
  have hzeroCard : zeroIndices.card = Module.finrank ℝ T.ker := by
    have hcard := hT.isSymmetric.card_filter_eigenvalues_eq rfl 0
    rw [Module.End.eigenspace_zero] at hcard
    simpa only [zeroIndices, RCLike.ofReal_eq_zero] using hcard
  have hnonneg (i : Fin (Module.finrank ℝ E)) :
      0 ≤ hT.isSymmetric.eigenvalues rfl i := hT.nonneg_eigenvalues rfl i
  rw [lowerKyFanSum]
  change 0 < ∑ i ∈ tail, hT.isSymmetric.eigenvalues rfl i ↔ _
  rw [Finset.sum_pos_iff_of_nonneg fun i _ => hnonneg i]
  constructor
  · rintro ⟨i, hiTail, hiPos⟩
    have hzeroSubset : zeroIndices ⊆ Finset.Ioi i := by
      intro j hj
      have hjZero : hT.isSymmetric.eigenvalues rfl j = 0 := by
        simpa only [zeroIndices, Finset.mem_filter, Finset.mem_univ, true_and] using hj
      have hij : i < j := by
        by_contra hnot
        have hji : j ≤ i := le_of_not_gt hnot
        have horder := hT.isSymmetric.eigenvalues_antitone rfl hji
        rw [hjZero] at horder
        exact (not_le_of_gt hiPos) horder
      exact Finset.mem_Ioi.mpr hij
    have hcard := Finset.card_le_card hzeroSubset
    have hiVal : Module.finrank ℝ E - k ≤ i.1 := by
      simpa only [tail, Finset.mem_filter, Finset.mem_univ, true_and] using hiTail
    rw [hzeroCard, Fin.card_Ioi] at hcard
    omega
  · intro hker
    by_contra hnot
    have htailSubset : tail ⊆ zeroIndices := by
      intro i hiTail
      have hiNotPos : ¬0 < hT.isSymmetric.eigenvalues rfl i := by
        intro hiPos
        exact hnot ⟨i, hiTail, hiPos⟩
      have hiZero : hT.isSymmetric.eigenvalues rfl i = 0 :=
        le_antisymm (le_of_not_gt hiNotPos) (hnonneg i)
      simpa only [zeroIndices, Finset.mem_filter, Finset.mem_univ, true_and] using hiZero
    have hcard := Finset.card_le_card htailSubset
    rw [show tail.card = k by exact card_fin_tail hk, hzeroCard] at hcard
    omega

theorem lowerKyFanSum_pos_iff_rank_ge {T : E →ₗ[ℝ] E} (hT : T.IsPositive)
    {k : ℕ} (hk : k ≤ Module.finrank ℝ E) :
    0 < hT.isSymmetric.lowerKyFanSum k ↔
      Module.finrank ℝ E - k + 1 ≤ Module.finrank ℝ T.range := by
  rw [lowerKyFanSum_pos_iff_finrank_ker_lt hT hk]
  have hrank := T.finrank_range_add_finrank_ker
  omega

end LinearMap.IsSymmetric

namespace LinearMap.IsPositive

theorem finrank_range_le_of_lowerKyFanSum_pos
    {A B : E →ₗ[ℝ] E} (hA : A.IsPositive) (hB : B.IsPositive)
    (hpos : ∀ k, 1 ≤ k → k ≤ Module.finrank ℝ E →
      0 < hA.isSymmetric.lowerKyFanSum k →
      0 < hB.isSymmetric.lowerKyFanSum k) :
    Module.finrank ℝ A.range ≤ Module.finrank ℝ B.range := by
  let r := Module.finrank ℝ E
  let rankA := Module.finrank ℝ A.range
  by_cases hzero : rankA = 0
  · omega
  · let k := r - rankA + 1
    have hrankA : rankA ≤ r := A.range.finrank_le
    have hkpos : 1 ≤ k := by omega
    have hkle : k ≤ r := by omega
    have hsource : 0 < hA.isSymmetric.lowerKyFanSum k :=
      (LinearMap.IsSymmetric.lowerKyFanSum_pos_iff_rank_ge hA hkle).2 (by omega)
    have htarget :=
      (LinearMap.IsSymmetric.lowerKyFanSum_pos_iff_rank_ge hB hkle).1
        (hpos k hkpos hkle hsource)
    omega

theorem finrank_range_le_of_lowerKyFanSum_pos_of_finrank_eq
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    {A : E →ₗ[ℝ] E} {B : F →ₗ[ℝ] F}
    (hA : A.IsPositive) (hB : B.IsPositive)
    (hfinrank : Module.finrank ℝ E = Module.finrank ℝ F)
    (hpos : ∀ k, 1 ≤ k → k ≤ Module.finrank ℝ E →
      0 < hA.isSymmetric.lowerKyFanSum k →
      0 < hB.isSymmetric.lowerKyFanSum k) :
    Module.finrank ℝ A.range ≤ Module.finrank ℝ B.range := by
  let r := Module.finrank ℝ E
  let rankA := Module.finrank ℝ A.range
  by_cases hzero : rankA = 0
  · omega
  · let k := r - rankA + 1
    have hrankA : rankA ≤ r := A.range.finrank_le
    have hkpos : 1 ≤ k := by omega
    have hkle : k ≤ r := by omega
    have hsource : 0 < hA.isSymmetric.lowerKyFanSum k :=
      (LinearMap.IsSymmetric.lowerKyFanSum_pos_iff_rank_ge hA hkle).2 (by omega)
    have htarget := hpos k hkpos hkle hsource
    have hkleF : k ≤ Module.finrank ℝ F := by omega
    have hrankB :=
      (LinearMap.IsSymmetric.lowerKyFanSum_pos_iff_rank_ge hB hkleF).1 htarget
    omega

end LinearMap.IsPositive

namespace ContinuousLinearMap.IsPositive

open Filter Set in
theorem eventually_finrank_range_ge_of_tendsto
    {X : Type*} {l : Filter X}
    {A : X → {T : E →L[ℝ] E // T.IsPositive}}
    {A₀ : {T : E →L[ℝ] E // T.IsPositive}}
    (hA : Tendsto A l (nhds A₀)) :
    ∀ᶠ x in l,
      Module.finrank ℝ A₀.1.range ≤ Module.finrank ℝ (A x).1.range := by
  let rank₀ := Module.finrank ℝ A₀.1.range
  by_cases hzero : rank₀ = 0
  · filter_upwards with x
    omega
  · let r := Module.finrank ℝ E
    let k := r - rank₀ + 1
    have hrank₀ : rank₀ ≤ r := A₀.1.range.finrank_le
    have hkle : k ≤ r := by omega
    have hsource : 0 < A₀.2.toLinearMap.isSymmetric.lowerKyFanSum k :=
      (LinearMap.IsSymmetric.lowerKyFanSum_pos_iff_rank_ge
        A₀.2.toLinearMap hkle).2 (by omega)
    let toSymmetric : {T : E →L[ℝ] E // T.IsPositive} →
        {T : E →L[ℝ] E // T.IsSymmetric} :=
      fun T => ⟨T.1, T.2.isSymmetric⟩
    have htoSymmetric : Continuous toSymmetric := by
      exact continuous_subtype_val.subtype_mk _
    have hphi : Tendsto
        (fun x => (toSymmetric (A x)).2.lowerKyFanSum k) l
        (nhds ((toSymmetric A₀).2.lowerKyFanSum k)) := by
      exact ((LinearMap.IsSymmetric.continuous_lowerKyFanSum k hkle).comp
        htoSymmetric).continuousAt.tendsto.comp hA
    have heventually : ∀ᶠ x in l,
        0 < (toSymmetric (A x)).2.lowerKyFanSum k :=
      hphi.eventually (Ioi_mem_nhds hsource)
    filter_upwards [heventually] with x hx
    have htarget :=
      (LinearMap.IsSymmetric.lowerKyFanSum_pos_iff_rank_ge
        (A x).2.toLinearMap hkle).1 hx
    omega

end ContinuousLinearMap.IsPositive
