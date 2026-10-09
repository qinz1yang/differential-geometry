import DifferentialGeometry.Geometry.Thurston.SphericalProductQuotient
import DifferentialGeometry.Topology.ThreeManifold.SphereMappingTorusTrivialization
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Descent
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Product
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.SphereOrthogonalAction
import Mathlib.Topology.Homeomorph.Quotient

/-!
# The cyclic `S² × ℝ` quotient is `S² × S¹`

Chapter 7, packet P8, tier 2. Let `A` be an orthogonal map of `ℝ³` with `det A = 1` and
`c ≠ 0`. The rotation of `S²` by `A⁻¹` has degree one, hence is smoothly isotopic to the
identity through an isotopy `J` that is flat near the ends. Extending `J` periodically,
`twist t = J (t - ⌊t⌋) ∘ A ^ (-⌊t⌋)` untwists the generator `(x, s) ↦ (A x, s + c)`, and
`cylinderUntwist (x, s) = (twist (s / c) x, e (s / c))` is a surjective local diffeomorphism
`S² × ℝ → S² × S¹` whose fibres are the orbits of the cyclic group. Comparing with any
presentation of `Z` by the same group gives `Z ≃ S² × S¹`
(`cyclicCylinderQuotientIsSphereTwoTimesCircle`), discharging the named input
`CyclicCylinderQuotientIsSphereTwoTimesCircle`; the closed `S² × ℝ` case then needs only
`SphericalProductUniversalCover` and `DihedralCylinderQuotientIsProjectiveSum`
(`sphericalProductStandardConnectedSum_of_universalCover_of_dihedral`).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff

namespace GC.Geometry.SphericalProduct

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1
local notation "CM" => SpatialNeckCylinderModel

private local instance sphereTwoFinrankFact : Fact (Module.finrank ℝ E3 = 2 + 1) :=
  ⟨by simp⟩

universe u

private theorem isLocalDiffeomorphAt_congr_open
    {E F H G M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
    {f g : M → N} {x : M} (hf : IsLocalDiffeomorphAt I J ∞ f x) {U : Set M} (hU : IsOpen U)
    (hx : x ∈ U) (hfg : ∀ y ∈ U, f y = g y) : IsLocalDiffeomorphAt I J ∞ g x := by
  obtain ⟨Φ, hxΦ, hΦ⟩ := hf
  refine ⟨DifferentialGeometry.Topology.PartialDiffeomorph.restrict Φ U hU, ⟨hxΦ, hx⟩,
    fun y hy => ?_⟩
  exact (hfg y hy.2).symm.trans (hΦ hy.1)

theorem sphereDiffeomorphDegree_sphereDiffeo (B : E3 ≃ₗᵢ[ℝ] E3)
    (hB : LinearMap.det (B.toLinearEquiv : E3 →ₗ[ℝ] E3) = 1) :
    Manifold.sphereDiffeomorphDegree (Geometry.sphereDiffeo (n := 2) B) = 1 := by
  let v : S2 := ⟨EuclideanSpace.single 0 1, by simp⟩
  rw [Manifold.sphereDiffeomorphDegree_eq_one_iff _ v]
  have hext : Manifold.sphereRadialExtension (Geometry.sphereDiffeo (n := 2) B) =
      (B : E3 → E3) := by
    funext x
    by_cases hx : x = 0
    · subst hx
      simp [Manifold.sphereRadialExtension]
    · rw [Manifold.sphereRadialExtension_of_ne_zero _ hx, Geometry.sphereDiffeo_coe]
      change ‖x‖ • B (‖x‖⁻¹ • x) = B x
      rw [map_smul, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]
  rw [hext]
  have hd : fderiv ℝ (B : E3 → E3) (v : E3) =
      (B.toContinuousLinearEquiv : E3 →L[ℝ] E3) :=
    B.toContinuousLinearEquiv.toContinuousLinearMap.fderiv
  rw [hd]
  change 0 < LinearMap.det (B.toLinearEquiv : E3 →ₗ[ℝ] E3)
  rw [hB]
  exact one_pos

section Twist

variable (A : E3 ≃ₗᵢ[ℝ] E3) (D : SphereMappingTorusIsotopy)

def sphereRot (k : ℤ) : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2 := Geometry.sphereDiffeo (n := 2) (A ^ k)

theorem sphereRot_coe (k : ℤ) (x : S2) : ((sphereRot A k x : S2) : E3) = (A ^ k) (x : E3) :=
  rfl

theorem sphereRot_sphereRot (j k : ℤ) (x : S2) :
    sphereRot A j (sphereRot A k x) = sphereRot A (j + k) x := by
  apply Subtype.ext
  simp only [sphereRot_coe, zpow_add, LinearIsometryEquiv.coe_mul, Function.comp_apply]

theorem sphereRot_zero (x : S2) : sphereRot A 0 x = x := by
  apply Subtype.ext
  simp only [sphereRot_coe, zpow_zero, LinearIsometryEquiv.coe_one, id]

def twist (t : ℝ) (x : S2) : S2 := D.isotopy (t - ⌊t⌋) (sphereRot A (-⌊t⌋) x)

theorem twist_injective (t : ℝ) : Function.Injective (twist A D t) :=
  (D.isotopy _).injective.comp (sphereRot A _).injective

theorem twist_surjective (t : ℝ) : Function.Surjective (twist A D t) :=
  (D.isotopy _).surjective.comp (sphereRot A _).surjective

theorem twist_shift (k : ℤ) (t : ℝ) (x : S2) :
    twist A D (t + k) (sphereRot A k x) = twist A D t x := by
  unfold twist
  rw [Int.floor_add_intCast, sphereRot_sphereRot]
  have e1 : t + k - ((⌊t⌋ + k : ℤ) : ℝ) = t - ⌊t⌋ := by
    push_cast
    ring
  have e2 : -(⌊t⌋ + k) + k = -⌊t⌋ := by ring
  rw [e1, e2]

variable {A D}

theorem twist_local
    (hlow : ∀ t : ℝ, t ≤ 1 / 3 → D.isotopy t = Diffeomorph.refl (𝓡 2) SphereTwo ∞)
    (hup : ∀ t : ℝ, 2 / 3 ≤ t → D.isotopy t = sphereRot A (-1))
    (n : ℤ) {t : ℝ} (h1 : (n : ℝ) - 1 / 3 < t) (h2 : t < n + 4 / 3) (x : S2) :
    twist A D t x = D.isotopy (t - n) (sphereRot A (-n) x) := by
  have hf1 : (⌊t⌋ : ℝ) ≤ t := Int.floor_le t
  have hf2 : t < ⌊t⌋ + 1 := Int.lt_floor_add_one t
  have h3 : ((n - 2 : ℤ) : ℝ) < ⌊t⌋ := by
    push_cast
    linarith
  have h4 : (⌊t⌋ : ℝ) < ((n + 2 : ℤ) : ℝ) := by
    push_cast
    linarith
  have h3' : n - 2 < ⌊t⌋ := by exact_mod_cast h3
  have h4' : ⌊t⌋ < n + 2 := by exact_mod_cast h4
  unfold twist
  rcases (by omega : ⌊t⌋ = n - 1 ∨ ⌊t⌋ = n ∨ ⌊t⌋ = n + 1) with h | h | h
  · have hc : (⌊t⌋ : ℝ) = n - 1 := by rw [h]; push_cast; ring
    rw [hc, hup (t - (n - 1)) (by linarith), hlow (t - n) (by linarith), h,
      sphereRot_sphereRot]
    rw [show (-1 + -(n - 1) : ℤ) = -n by ring]
    rfl
  · rw [h]
  · have hc : (⌊t⌋ : ℝ) = n + 1 := by rw [h]; push_cast; ring
    rw [hc, hlow (t - (n + 1)) (by linarith), hup (t - n) (by linarith), h,
      sphereRot_sphereRot]
    rw [show (-1 + -n : ℤ) = -(n + 1) by ring]
    rfl

variable (A D)

def twistChart (c : ℝ) (hc : c ≠ 0) (n : ℤ)
    (hD : ContMDiff CM (𝓡 2) ∞ (fun p : SphereTwo × ℝ => D.isotopy p.2 p.1))
    (hDi : ContMDiff CM (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (D.isotopy p.2).symm p.1)) :
    (S2 × ℝ) ≃ₘ⟮CM, CM⟯ (S2 × ℝ) where
  toFun p := (D.isotopy (p.2 / c - n) (sphereRot A (-n) p.1), p.2 / c)
  invFun q := (sphereRot A n ((D.isotopy (q.2 - n)).symm q.1), c * q.2)
  left_inv p := by
    refine Prod.ext ?_ (mul_div_cancel₀ p.2 hc)
    change sphereRot A n ((D.isotopy (p.2 / c - n)).symm
      (D.isotopy (p.2 / c - n) (sphereRot A (-n) p.1))) = p.1
    rw [Diffeomorph.symm_apply_apply, sphereRot_sphereRot, add_neg_cancel, sphereRot_zero]
  right_inv q := by
    refine Prod.ext ?_ (mul_div_cancel_left₀ q.2 hc)
    change D.isotopy (c * q.2 / c - n) (sphereRot A (-n)
      (sphereRot A n ((D.isotopy (q.2 - n)).symm q.1))) = q.1
    rw [mul_div_cancel_left₀ q.2 hc, sphereRot_sphereRot, neg_add_cancel, sphereRot_zero,
      Diffeomorph.apply_symm_apply]
  contMDiff_toFun := by
    have hr : ContMDiff CM 𝓘(ℝ, ℝ) ∞ (fun p : S2 × ℝ => p.2 / c - n) :=
      ((contDiff_id.div_const c).sub contDiff_const).contMDiff.comp contMDiff_snd
    have h1 : ContMDiff CM CM ∞
        (fun p : S2 × ℝ => (sphereRot A (-n) p.1, p.2 / c - n)) :=
      ((sphereRot A (-n)).contMDiff.comp contMDiff_fst).prodMk hr
    exact (hD.comp h1).prodMk ((contDiff_id.div_const c).contMDiff.comp contMDiff_snd)
  contMDiff_invFun := by
    have hr : ContMDiff CM 𝓘(ℝ, ℝ) ∞ (fun q : S2 × ℝ => q.2 - n) :=
      (contDiff_id.sub contDiff_const).contMDiff.comp contMDiff_snd
    have h1 : ContMDiff CM CM ∞ (fun q : S2 × ℝ => (q.1, q.2 - n)) :=
      contMDiff_fst.prodMk hr
    exact ((sphereRot A n).contMDiff.comp (hDi.comp h1)).prodMk
      ((contDiff_const.mul contDiff_id).contMDiff.comp contMDiff_snd)

def circleCoord (t : ℝ) : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
  addCircleOneDiffeomorphSphereOne (t : AddCircle (1 : ℝ))

theorem circleCoord_isLocalDiffeomorph : IsLocalDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ∞ circleCoord :=
  DifferentialGeometry.isLocalDiffeomorph_comp addCircleOneDiffeomorphSphereOne.isLocalDiffeomorph
    AddCircle.isLocalDiffeomorph_coe

theorem circleCoord_add_int (t : ℝ) (k : ℤ) : circleCoord (t + k) = circleCoord t := by
  unfold circleCoord
  rw [AddCircle.coe_add, (AddCircle.coe_eq_zero_iff (1 : ℝ) (x := (k : ℝ))).mpr ⟨k, by simp⟩,
    add_zero]

def cylinderUntwist (c : ℝ) (p : S2 × ℝ) : SphereTwoTimesCircle :=
  (twist A D (p.2 / c) p.1, circleCoord (p.2 / c))

variable {A D}

theorem cylinderUntwist_isLocalDiffeomorph {c : ℝ} (hc : c ≠ 0)
    (hD : ContMDiff CM (𝓡 2) ∞ (fun p : SphereTwo × ℝ => D.isotopy p.2 p.1))
    (hDi : ContMDiff CM (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (D.isotopy p.2).symm p.1))
    (hlow : ∀ t : ℝ, t ≤ 1 / 3 → D.isotopy t = Diffeomorph.refl (𝓡 2) SphereTwo ∞)
    (hup : ∀ t : ℝ, 2 / 3 ≤ t → D.isotopy t = sphereRot A (-1)) :
    IsLocalDiffeomorph CM ((𝓡 2).prod (𝓡 1)) ∞ (cylinderUntwist A D c) := by
  have hψ : IsLocalDiffeomorph CM ((𝓡 2).prod (𝓡 1)) ∞
      (Prod.map (id : S2 → S2) circleCoord) :=
    IsLocalDiffeomorph.prodMap
      ((Diffeomorph.refl (𝓡 2) S2 ∞).isLocalDiffeomorph : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ id)
      circleCoord_isLocalDiffeomorph
  intro p
  let n : ℤ := ⌊p.2 / c⌋
  let U : Set (S2 × ℝ) := {q | (n : ℝ) - 1 / 3 < q.2 / c ∧ q.2 / c < n + 4 / 3}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const ((continuous_snd.div_const c))).inter
      (isOpen_lt (continuous_snd.div_const c) continuous_const)
  have hpU : p ∈ U := by
    refine ⟨?_, ?_⟩
    · linarith [Int.floor_le (p.2 / c)]
    · linarith [Int.lt_floor_add_one (p.2 / c)]
  let Θ := twistChart A D c hc n hD hDi
  have hcomp : IsLocalDiffeomorphAt CM ((𝓡 2).prod (𝓡 1)) ∞
      (Prod.map (id : S2 → S2) circleCoord ∘ Θ) p :=
    DifferentialGeometry.isLocalDiffeomorph_comp hψ Θ.isLocalDiffeomorph p
  refine isLocalDiffeomorphAt_congr_open hcomp hU hpU fun q hq => ?_
  change (D.isotopy (q.2 / c - n) (sphereRot A (-n) q.1), circleCoord (q.2 / c)) =
    (twist A D (q.2 / c) q.1, circleCoord (q.2 / c))
  rw [twist_local hlow hup n hq.1 hq.2]

theorem cylinderUntwist_surjective {c : ℝ} (hc : c ≠ 0) :
    Function.Surjective (cylinderUntwist A D c) := by
  rintro ⟨y, z⟩
  obtain ⟨w, rfl⟩ := addCircleOneDiffeomorphSphereOne.surjective z
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective w
  obtain ⟨x, hx⟩ := twist_surjective A D t y
  refine ⟨(x, c * t), ?_⟩
  change (twist A D (c * t / c) x, circleCoord (c * t / c)) = _
  rw [mul_div_cancel_left₀ t hc, hx]
  rfl

theorem cylinderAct_zpow_vaddConst (c : ℝ) (k : ℤ) (p : SpatialNeckCylinder) :
    cylinderAct ((A, AffineIsometryEquiv.vaddConst ℝ c) ^ k) p =
      (sphereRot A k p.1, p.2 + k * c) := by
  refine Prod.ext (Subtype.ext ?_) ?_
  · change ((A, AffineIsometryEquiv.vaddConst ℝ c) ^ k).1 (p.1 : E3) = (A ^ k) (p.1 : E3)
    rw [Prod.pow_fst]
  · change ((A, AffineIsometryEquiv.vaddConst ℝ c) ^ k).2 p.2 = p.2 + k * c
    rw [Prod.pow_snd]
    exact line_zpow_apply (fun s => by simp) k p.2

theorem cylinderUntwist_eq_iff {c : ℝ} (hc : c ≠ 0) (a b : SpatialNeckCylinder) :
    cylinderUntwist A D c a = cylinderUntwist A D c b ↔
      ∃ k : ℤ, cylinderAct ((A, AffineIsometryEquiv.vaddConst ℝ c) ^ k) a = b := by
  constructor
  · intro h
    have h1 : twist A D (a.2 / c) a.1 = twist A D (b.2 / c) b.1 := congrArg Prod.fst h
    have h2 : circleCoord (a.2 / c) = circleCoord (b.2 / c) := congrArg Prod.snd h
    have h3 : ((a.2 / c : ℝ) : AddCircle (1 : ℝ)) = ((b.2 / c : ℝ) : AddCircle (1 : ℝ)) :=
      addCircleOneDiffeomorphSphereOne.injective h2
    have h4 : ((b.2 / c - a.2 / c : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      rw [AddCircle.coe_sub, h3, sub_self]
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff 1).mp h4
    rw [zsmul_eq_mul, mul_one] at hk
    have ht : b.2 / c = a.2 / c + k := by linarith
    have hb2 : b.2 = a.2 + k * c := by
      have e1 : b.2 = c * (b.2 / c) := (mul_div_cancel₀ b.2 hc).symm
      have e2 : a.2 = c * (a.2 / c) := (mul_div_cancel₀ a.2 hc).symm
      rw [e1, ht, mul_add, ← e2]
      ring
    have h5 : twist A D (a.2 / c) (sphereRot A (-k) b.1) = twist A D (a.2 / c) a.1 := by
      have hs := twist_shift A D k (a.2 / c) (sphereRot A (-k) b.1)
      rw [sphereRot_sphereRot, add_neg_cancel, sphereRot_zero, ← ht] at hs
      rw [← hs]
      exact h1.symm
    have h6 := twist_injective A D _ h5
    refine ⟨k, ?_⟩
    rw [cylinderAct_zpow_vaddConst]
    refine Prod.ext ?_ hb2.symm
    change sphereRot A k a.1 = b.1
    rw [← h6, sphereRot_sphereRot, add_neg_cancel, sphereRot_zero]
  · rintro ⟨k, rfl⟩
    rw [cylinderAct_zpow_vaddConst]
    change (twist A D (a.2 / c) a.1, circleCoord (a.2 / c)) =
      (twist A D ((a.2 + k * c) / c) (sphereRot A k a.1), circleCoord ((a.2 + k * c) / c))
    have ht : (a.2 + k * c) / c = a.2 / c + k := by field_simp
    rw [ht, twist_shift, circleCoord_add_int]

end Twist

theorem nonempty_diffeomorph_of_same_fibres
    {F₂ F₃ H₂ H₃ Y W : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    [NormedAddCommGroup F₃] [NormedSpace ℝ F₃] [TopologicalSpace H₂] [TopologicalSpace H₃]
    {I₂ : ModelWithCorners ℝ F₂ H₂} {I₃ : ModelWithCorners ℝ F₃ H₃}
    [TopologicalSpace Y] [ChartedSpace H₂ Y] [TopologicalSpace W] [ChartedSpace H₃ W]
    (p : SpatialNeckCylinder → Y) (hp : IsLocalDiffeomorph CM I₂ ∞ p)
    (hps : Function.Surjective p) (q : SpatialNeckCylinder → W)
    (hq : IsLocalDiffeomorph CM I₃ ∞ q) (hqs : Function.Surjective q)
    (hfib : ∀ a b, p a = p b ↔ q a = q b) : Nonempty (Y ≃ₘ⟮I₂, I₃⟯ W) := by
  have hpq : Topology.IsQuotientMap p :=
    hp.isOpenMap.isQuotientMap hp.contMDiff.continuous hps
  have hqq : Topology.IsQuotientMap q :=
    hq.isOpenMap.isQuotientMap hq.contMDiff.continuous hqs
  let pc : C(SpatialNeckCylinder, Y) := ⟨p, hpq.continuous⟩
  let qc : C(SpatialNeckCylinder, W) := ⟨q, hqq.continuous⟩
  let hY := Topology.IsQuotientMap.homeomorph (f := pc) hpq
  let hW := Topology.IsQuotientMap.homeomorph (f := qc) hqq
  let d : Y ≃ₜ W :=
    hY.symm.trans ((Homeomorph.Quotient.congrRight (fun a b => hfib a b)).trans hW)
  have hd : ∀ x, d (p x) = q x := by
    intro x
    have h1 : hY.symm (p x) = Quotient.mk _ x := hY.symm_apply_eq.mpr rfl
    simp only [d, Homeomorph.trans_apply, h1]
    rfl
  obtain ⟨F, -⟩ := exists_diffeomorph_of_homeomorph_comp_localDiffeomorph p hp hps q hq d hd
  exact ⟨F⟩

theorem nonempty_diffeomorph_of_cyclic_presentation
    {Z : Type u} [TopologicalSpace Z] [ChartedSpace E3 Z]
    (A : E3 ≃ₗᵢ[ℝ] E3) (c : ℝ) (hA : LinearMap.det (A.toLinearEquiv : E3 →ₗ[ℝ] E3) = 1)
    (hc : c ≠ 0)
    (pr : CylinderQuotientPresentation (Subgroup.zpowers (A, AffineIsometryEquiv.vaddConst ℝ c))
      Z) :
    Nonempty (Z ≃ₘ⟮𝓡 3, (𝓡 2).prod (𝓡 1)⟯ SphereTwoTimesCircle) := by
  have hdet : LinearMap.det ((A ^ (-1 : ℤ)).toLinearEquiv : E3 →ₗ[ℝ] E3) = 1 := by
    have hcomp : ((A ^ (-1 : ℤ)).toLinearEquiv : E3 →ₗ[ℝ] E3) ∘ₗ
        (A.toLinearEquiv : E3 →ₗ[ℝ] E3) = LinearMap.id := by
      ext v
      simp
    have h := congrArg LinearMap.det hcomp
    rw [LinearMap.det_comp, hA, mul_one, LinearMap.det_id] at h
    exact h
  have hdeg : Manifold.sphereDiffeomorphDegree (sphereRot A (-1)) = 1 :=
    sphereDiffeomorphDegree_sphereDiffeo _ hdet
  obtain ⟨D, -, hD, hDi, hlow, hup⟩ := exists_sphereMappingTorusIsotopy_of_degree_one _ hdeg
  let v := cylinderUntwist A D c
  have hv : IsLocalDiffeomorph CM ((𝓡 2).prod (𝓡 1)) ∞ v :=
    cylinderUntwist_isLocalDiffeomorph hc hD hDi hlow hup
  have hfib : ∀ a b, pr.proj a = pr.proj b ↔ v a = v b := by
    intro a b
    rw [pr.fibres, cylinderUntwist_eq_iff hc]
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hγ
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨_, Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩, rfl⟩
  exact nonempty_diffeomorph_of_same_fibres pr.proj pr.isLocalDiffeomorph pr.surjective v hv
    (cylinderUntwist_surjective hc) hfib

theorem cyclicCylinderQuotientIsSphereTwoTimesCircle :
    CyclicCylinderQuotientIsSphereTwoTimesCircle.{u} := by
  intro Z _ _ _ A c hA hc pr
  exact nonempty_diffeomorph_of_cyclic_presentation A c hA hc pr

theorem sphericalProductStandardConnectedSum_of_universalCover_of_dihedral
    (hU : SphericalProductUniversalCover.{u})
    (hD : DihedralCylinderQuotientIsProjectiveSum.{u}) :
    GC.Endpoint.SphericalProductStandardConnectedSum.{u} :=
  sphericalProductStandardConnectedSum_of_universalCover hU
    cyclicCylinderQuotientIsSphereTwoTimesCircle hD

theorem geometrizes_of_sphericalProductStructure_of_universalCover_of_dihedral
    (hU : SphericalProductUniversalCover.{u})
    (hD : DihedralCylinderQuotientIsProjectiveSum.{u})
    (P : ConnectedClosedOrientedManifold.{u} 3)
    (g : GeometricStructure (𝓡 3) P.Carrier) (hg : g.model = .sphericalProduct) :
    GC.Endpoint.Geometrizes P :=
  GC.Endpoint.geometrizes_of_sphericalProductStructure
    (sphericalProductStandardConnectedSum_of_universalCover_of_dihedral hU hD) P g hg

end GC.Geometry.SphericalProduct
