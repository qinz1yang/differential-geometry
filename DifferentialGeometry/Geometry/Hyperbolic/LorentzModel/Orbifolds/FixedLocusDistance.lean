/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.AxialDeformation

noncomputable section

open Set Filter Matrix
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.FixedLocusDistance

open Hyperbolic HyperbolicAction HyperbolicFaithful HyperbolicBoundary
open HyperbolicConvexity OrbifoldStrata FixedLocusGeometry LorentzExtremal
open AxisGeometry AxialStratumDeformation

variable {n : ℕ}

def normalEnergy (σ : Set (HUpper n)) (x : HUpper n) : ℝ :=
  Real.cosh (Metric.infDist x σ) ^ 2 - 1

theorem continuous_normalEnergy (σ : Set (HUpper n)) : Continuous (normalEnergy σ) :=
  ((Real.continuous_cosh.comp (Metric.continuous_infDist_pt σ)).pow 2).sub continuous_const

theorem normalEnergy_nonneg (σ : Set (HUpper n)) (x : HUpper n) :
    0 ≤ normalEnergy σ x := by
  have h := Real.one_le_cosh (Metric.infDist x σ)
  dsimp [normalEnergy]
  nlinarith

theorem eq_zero_of_null_orth (p : HUpper n) {v : LorVec n}
    (hv : lorB v v = 0) (hp : lorB v p.val = 0) : v = 0 := by
  have hcs := sdot_sq_le v p.val
  have hvv : sdot v v = tc v ^ 2 := by dsimp [lorB] at hv; nlinarith
  have hvp : sdot v p.val = tc v * tc p.val := sub_eq_zero.mp hp
  have hpp := HUpper.tc_sq p
  rw [hvv, hvp, mul_pow] at hcs
  have ht : tc v = 0 := by nlinarith
  exact eq_zero_of_lorB_self_eq_zero hv ht

theorem exists_normal_decomposition {σ : Set (HUpper n)}
    (hσ : σ.Nonempty) (hclosed : IsClosed σ)
    (hsection : σ = {z : HUpper n | z.val ∈ locusSpan σ}) (x : HUpper n) :
    ∃ p ∈ σ, dist x p = Metric.infDist x σ ∧
      ∀ v ∈ locusSpan σ,
        lorB (x.val - Real.cosh (Metric.infDist x σ) • p.val) v = 0 := by
  obtain ⟨p, hp, he⟩ := hclosed.exists_infDist_eq_dist hσ x
  let R := Real.cosh (Metric.infDist x σ)
  have hxp : lorB x.val p.val = -R := by
    dsimp [R]
    rw [he, cosh_dist]
    ring
  have hpperp : lorB (x.val - R • p.val) p.val = 0 := by
    rw [lorB_sub_left, lorB_smul_left, hxp, p.is_unit]
    ring
  have horth (a : HUpper n) (ha : a ∈ σ) : lorB (x.val - R • p.val) a.val = 0 := by
    by_cases hpa : p = a
    · simpa only [← hpa] using hpperp
    let K : ℝ := (Real.cosh (dist x a) - Real.cosh (dist p a) * R) /
      Real.sinh (dist p a)
    let F : ℝ → ℝ := fun t => Real.cosh t * R + Real.sinh t * K
    have hgeo (t : ℝ) : F t = Real.cosh (dist x (geodFromTo p a hpa t)) := by
      rw [cosh_dist_geodFromTo hpa]
      dsimp [F, K, R]
      rw [he]
    have hmem (t : ℝ) : geodFromTo p a hpa t ∈ σ := by
      rw [hsection]
      change Real.cosh t • p.val + Real.sinh t • dirVec p a ∈ locusSpan σ
      apply (locusSpan σ).add_mem ((locusSpan σ).smul_mem _ (val_mem_locusSpan hp))
      apply (locusSpan σ).smul_mem
      exact (locusSpan σ).smul_mem _
        ((locusSpan σ).sub_mem (val_mem_locusSpan ha)
          ((locusSpan σ).smul_mem _ (val_mem_locusSpan hp)))
    have hmin : IsLocalMin F 0 := by
      apply Filter.Eventually.of_forall
      intro t
      have hdist := Metric.infDist_le_dist_of_mem (x := x) (hmem t)
      have hcosh := Real.cosh_strictMonoOn.monotoneOn
        (Metric.infDist_nonneg) dist_nonneg hdist
      simpa only [hgeo, geodFromTo_zero, he] using hcosh
    have hderiv : HasDerivAt F K 0 := by
      convert ((Real.hasDerivAt_cosh 0).mul_const R).add
        ((Real.hasDerivAt_sinh 0).mul_const K) using 1;
        first | rfl | simp
    have hK : K = 0 := hmin.hasDerivAt_eq_zero hderiv
    have hnum : Real.cosh (dist x a) - Real.cosh (dist p a) * R = 0 :=
      (div_eq_zero_iff.mp hK).resolve_right
        (Real.sinh_pos_iff.mpr (dist_pos.mpr hpa)).ne'
    rw [cosh_dist, cosh_dist] at hnum
    rw [lorB_sub_left, lorB_smul_left]
    nlinarith
  refine ⟨p, hp, he.symm, ?_⟩
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨a, ha, rfl⟩ := hv
    exact horth a ha
  | zero => simp only [lorB, sdot, tc, Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero]
  | add a b _ _ ha hb => rw [lorB_add_right, ha, hb, add_zero]
  | smul c a _ ha => rw [lorB_smul_right, ha, mul_zero]

theorem normal_component_unique {σ : Set (HUpper n)} (hσ : σ.Nonempty)
    (x : LorVec n) {v w : LorVec n}
    (hvV : x - v ∈ locusSpan σ) (hwV : x - w ∈ locusSpan σ)
    (hv : ∀ z ∈ locusSpan σ, lorB v z = 0)
    (hw : ∀ z ∈ locusSpan σ, lorB w z = 0) : v = w := by
  obtain ⟨p, hp⟩ := hσ
  have hdiff : v - w ∈ locusSpan σ := by
    have h := (locusSpan σ).sub_mem hwV hvV
    convert h using 1
    abel
  have hnorm : lorB (v - w) (v - w) = 0 := by
    rw [lorB_sub_left, hv _ hdiff, hw _ hdiff, sub_self]
  have hperp : lorB (v - w) p.val = 0 := by
    rw [lorB_sub_left, hv _ (val_mem_locusSpan hp), hw _ (val_mem_locusSpan hp), sub_self]
  exact sub_eq_zero.mp (eq_zero_of_null_orth p hnorm hperp)

theorem normalEnergy_eq_norm {σ : Set (HUpper n)}
    (hσ : σ.Nonempty) (hclosed : IsClosed σ)
    (hsection : σ = {z : HUpper n | z.val ∈ locusSpan σ})
    (x : HUpper n) (w : LorVec n) (hwV : x.val - w ∈ locusSpan σ)
    (hw : ∀ z ∈ locusSpan σ, lorB w z = 0) :
    normalEnergy σ x = lorB w w := by
  obtain ⟨p, hp, he, horth⟩ := exists_normal_decomposition hσ hclosed hsection x
  let R := Real.cosh (Metric.infDist x σ)
  let v := x.val - R • p.val
  have hvV : x.val - v ∈ locusSpan σ := by
    dsimp [v]
    rw [sub_sub_cancel]
    exact (locusSpan σ).smul_mem _ (val_mem_locusSpan hp)
  have hvw : v = w := normal_component_unique hσ x.val hvV hwV horth hw
  rw [← hvw]
  have hxp : lorB x.val p.val = -R := by
    dsimp [R]
    rw [← he, cosh_dist]
    ring
  change R ^ 2 - 1 = lorB (x.val - R • p.val) (x.val - R • p.val)
  rw [lorB_sub_smul_self, x.is_unit, p.is_unit, hxp]
  ring

theorem normalEnergy_pos {σ : Set (HUpper n)} (hσ : σ.Nonempty)
    (hclosed : IsClosed σ) {x : HUpper n} (hx : x ∉ σ) : 0 < normalEnergy σ x := by
  obtain ⟨p, hp, he⟩ := hclosed.exists_infDist_eq_dist hσ x
  have hxp : x ≠ p := fun h => hx (h.symm ▸ hp)
  have hcosh : 1 < Real.cosh (Metric.infDist x σ) := by
    rw [he]
    exact Real.one_lt_cosh.mpr (dist_ne_zero.mpr hxp)
  dsimp [normalEnergy]
  nlinarith

theorem normalEnergy_eq_zero_of_mem {σ : Set (HUpper n)} {x : HUpper n} (hx : x ∈ σ) :
    normalEnergy σ x = 0 := by
  simp only [normalEnergy, Metric.infDist_zero_of_mem hx, Real.cosh_zero, one_pow, sub_self]

theorem normalEnergy_eq_of_val_eq {σ : Set (HUpper n)}
    (hσ : σ.Nonempty) (hclosed : IsClosed σ)
    (hsection : σ = {z : HUpper n | z.val ∈ locusSpan σ})
    (x y : HUpper n) (c : ℝ) (w : LorVec n) (hw : w ∈ locusSpan σ)
    (heq : y.val = c • x.val - w) :
    normalEnergy σ y = c ^ 2 * normalEnergy σ x := by
  obtain ⟨p, hp, _, horth⟩ := exists_normal_decomposition hσ hclosed hsection x
  let v := x.val - Real.cosh (Metric.infDist x σ) • p.val
  have hvV : x.val - v ∈ locusSpan σ := by
    dsimp [v]
    rw [sub_sub_cancel]
    exact (locusSpan σ).smul_mem _ (val_mem_locusSpan hp)
  have hyV : y.val - c • v ∈ locusSpan σ := by
    have h := (locusSpan σ).sub_mem ((locusSpan σ).smul_mem c hvV) hw
    convert h using 1
    rw [heq]
    dsimp [v]
    module
  have hyorth : ∀ z ∈ locusSpan σ, lorB (c • v) z = 0 := by
    intro z hz
    rw [lorB_smul_left, horth z hz, mul_zero]
  rw [normalEnergy_eq_norm hσ hclosed hsection y _ hyV hyorth,
    normalEnergy_eq_norm hσ hclosed hsection x v hvV horth,
    lorB_smul_left, lorB_smul_right]
  ring

theorem planeProject_add (ξ η : BoundaryH n) (v w : LorVec n) :
    planeProject ξ η (v + w) = planeProject ξ η v + planeProject ξ η w := by
  simp only [planeProject, lorB_add_left, add_div, add_smul]
  abel

theorem planeProject_smul (ξ η : BoundaryH n) (c : ℝ) (v : LorVec n) :
    planeProject ξ η (c • v) = c • planeProject ξ η v := by
  simp only [planeProject, lorB_smul_left, mul_div_assoc, mul_smul, smul_add]

theorem planeProject_zero (ξ η : BoundaryH n) : planeProject ξ η (0 : LorVec n) = 0 := by
  have h := planeProject_smul ξ η 0 (0 : LorVec n)
  simpa only [zero_smul] using h

theorem planeProject_sub (ξ η : BoundaryH n) (v w : LorVec n) :
    planeProject ξ η (v - w) = planeProject ξ η v - planeProject ξ η w := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ w, planeProject_add, planeProject_smul, neg_one_smul,
    sub_eq_add_neg]

theorem planeProject_selfadjoint (ξ η : BoundaryH n) (v w : LorVec n) :
    lorB (planeProject ξ η v) w = lorB v (planeProject ξ η w) := by
  simp only [planeProject, lorB_add_left, lorB_add_right, lorB_smul_left, lorB_smul_right,
    lorB_comm ξ.val w, lorB_comm η.val w]
  ring

theorem planeProject_mem_locusSpan {σ : Set (HUpper n)}
    (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hproj : ∀ p ∈ σ, axisFoot ξ η hne p ∈ σ) :
    ∀ v ∈ locusSpan σ, planeProject ξ η v ∈ locusSpan σ := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨p, hp, rfl⟩ := hv
    rw [planeProject_eq_radius_smul_foot ξ η hne p]
    exact (locusSpan σ).smul_mem _ (val_mem_locusSpan (hproj p hp))
  | zero => rw [planeProject_zero]; exact (locusSpan σ).zero_mem
  | add v w _ _ hv hw => rw [planeProject_add]; exact (locusSpan σ).add_mem hv hw
  | smul c v _ hv => rw [planeProject_smul]; exact (locusSpan σ).smul_mem c hv

theorem planeProject_orthogonal_locusSpan {σ : Set (HUpper n)}
    (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hproj : ∀ p ∈ σ, axisFoot ξ η hne p ∈ σ) {w : LorVec n}
    (hw : ∀ v ∈ locusSpan σ, lorB w v = 0) :
    ∀ v ∈ locusSpan σ, lorB (planeProject ξ η w) v = 0 := by
  intro v hv
  rw [planeProject_selfadjoint]
  exact hw _ (planeProject_mem_locusSpan ξ η hne hproj v hv)

theorem normalEnergy_normal_geod_ge {σ : Set (HUpper n)}
    (hσ : σ.Nonempty) (hclosed : IsClosed σ)
    (hsection : σ = {z : HUpper n | z.val ∈ locusSpan σ})
    (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hproj : ∀ p ∈ σ, axisFoot ξ η hne p ∈ σ)
    (y : HUpper n) (hy : axisFoot ξ η hne y ≠ y) {s : ℝ} (hs : 0 ≤ s) :
    Real.cosh s ^ 2 * normalEnergy σ y ≤
      normalEnergy σ (geodFromTo (axisFoot ξ η hne y) y hy
        (dist (axisFoot ξ η hne y) y + s)) := by
  let p := axisFoot ξ η hne y
  let r := dist p y
  let q := geodFromTo p y hy (r + s)
  let a := Real.cosh (r + s) / Real.cosh r
  let c := Real.sinh (r + s) / Real.sinh r
  have hr : 0 < r := dist_pos.mpr hy
  have hsin : 0 < Real.sinh r := Real.sinh_pos_iff.mpr hr
  have hcos : 0 < Real.cosh r := Real.cosh_pos r
  have hss : 0 ≤ Real.sinh s := Real.sinh_nonneg_iff.mpr hs
  have ha : Real.cosh s ≤ a := by
    apply (le_div_iff₀ hcos).mpr
    rw [Real.cosh_add]
    nlinarith [mul_nonneg hsin.le hss]
  have hc : Real.cosh s ≤ c := by
    apply (le_div_iff₀ hsin).mpr
    rw [Real.sinh_add]
    nlinarith [mul_nonneg hcos.le hss]
  have hR : axisRadius ξ η y = Real.cosh r := by
    rw [← cosh_dist_axisFoot ξ η hne y, dist_comm]
  have hPy : planeProject ξ η y.val = Real.cosh r • p.val := by
    rw [planeProject_eq_radius_smul_foot ξ η hne y, hR]
  have hqval : q.val = a • planeProject ξ η y.val + c • (y.val - planeProject ξ η y.val) := by
    rw [hPy]
    ext i
    change Real.cosh (r + s) * p.val i +
      Real.sinh (r + s) * ((Real.sinh r)⁻¹ * (y.val i - Real.cosh r * p.val i)) =
      a * (Real.cosh r * p.val i) + c * (y.val i - Real.cosh r * p.val i)
    dsimp [a, c]
    field_simp
  obtain ⟨z, hz, _, hw⟩ := exists_normal_decomposition hσ hclosed hsection y
  let w := y.val - Real.cosh (Metric.infDist y σ) • z.val
  let v := planeProject ξ η w
  let u := w - v
  let W := a • v + c • u
  have hwV : y.val - w ∈ locusSpan σ := by
    dsimp [w]
    rw [sub_sub_cancel]
    exact (locusSpan σ).smul_mem _ (val_mem_locusSpan hz)
  have hvorth : ∀ t ∈ locusSpan σ, lorB v t = 0 :=
    planeProject_orthogonal_locusSpan ξ η hne hproj hw
  have huorth : ∀ t ∈ locusSpan σ, lorB u t = 0 := by
    intro t ht
    rw [show u = w - v from rfl, lorB_sub_left, hw t ht, hvorth t ht, sub_self]
  have hWorth : ∀ t ∈ locusSpan σ, lorB W t = 0 := by
    intro t ht
    rw [show W = a • v + c • u from rfl, lorB_add_left, lorB_smul_left, lorB_smul_left,
      hvorth t ht, huorth t ht, mul_zero, mul_zero, add_zero]
  have hWV : q.val - W ∈ locusSpan σ := by
    have hP := planeProject_mem_locusSpan ξ η hne hproj _ hwV
    have hU := (locusSpan σ).sub_mem hwV hP
    have h := (locusSpan σ).add_mem ((locusSpan σ).smul_mem a hP) ((locusSpan σ).smul_mem c hU)
    convert h using 1
    rw [hqval, planeProject_sub]
    dsimp [W, u, v]
    module
  have hpσ : axisFoot ξ η hne z ∈ σ := hproj z hz
  have hvpos : 0 ≤ lorB v v :=
    lorB_self_nonneg_of_orth (axisFoot ξ η hne z).is_unit
      (hvorth _ (val_mem_locusSpan hpσ))
  have hupos : 0 ≤ lorB u u :=
    lorB_self_nonneg_of_orth (axisFoot ξ η hne z).is_unit
      (normal_orthogonal ξ η hne w _ (axisFoot_mem ξ η hne z))
  have huv : lorB u v = 0 := normal_orthogonal ξ η hne w _ (planeProject_mem ξ η w)
  have hvu : lorB v u = 0 := by rw [lorB_comm]; exact huv
  have hwdecomp : lorB w w = lorB v v + lorB u u := by
    have he : w = v + u := by dsimp [u]; abel
    conv_lhs => rw [he]
    rw [lorB_add_left, lorB_add_right, lorB_add_right, huv, hvu]
    ring
  have hWdecomp : lorB W W = a ^ 2 * lorB v v + c ^ 2 * lorB u u := by
    dsimp [W]
    simp only [lorB_add_left, lorB_add_right, lorB_smul_left, lorB_smul_right, huv, hvu]
    ring
  have ha2 : Real.cosh s ^ 2 ≤ a ^ 2 := by nlinarith [Real.cosh_pos s]
  have hc2 : Real.cosh s ^ 2 ≤ c ^ 2 := by nlinarith [Real.cosh_pos s]
  change Real.cosh s ^ 2 * normalEnergy σ y ≤ normalEnergy σ q
  rw [normalEnergy_eq_norm hσ hclosed hsection y w hwV hw,
    normalEnergy_eq_norm hσ hclosed hsection q W hWV hWorth, hWdecomp, hwdecomp, mul_add]
  exact add_le_add (mul_le_mul_of_nonneg_right ha2 hvpos) (mul_le_mul_of_nonneg_right hc2 hupos)

end DifferentialGeometry.FixedLocusDistance
