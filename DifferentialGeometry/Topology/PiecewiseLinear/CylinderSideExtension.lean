/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homeomorph.SphereExtension
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.DiscreteSubset

open Set Metric Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

def cylinderSide : Set (EuclideanSpace ℝ (Fin 2) × ℝ) := {q | ‖q.1‖ = 1 ∧ |q.2| ≤ 1}

noncomputable def cylinderSidePlane (q : EuclideanSpace ℝ (Fin 2) × ℝ) :
    EuclideanSpace ℝ (Fin 2) :=
  (2 + q.2) • q.1

noncomputable def cylinderSideOfPlane (x : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) × ℝ :=
  (‖x‖⁻¹ • x, ‖x‖ - 2)

theorem norm_cylinderSidePlane {q : EuclideanSpace ℝ (Fin 2) × ℝ} (hq : q ∈ cylinderSide) :
    ‖cylinderSidePlane q‖ = 2 + q.2 := by
  have h2 := (abs_le.mp hq.2).1
  rw [cylinderSidePlane, norm_smul, hq.1, mul_one, Real.norm_of_nonneg (by linarith)]

theorem cylinderSideOfPlane_plane {q : EuclideanSpace ℝ (Fin 2) × ℝ} (hq : q ∈ cylinderSide) :
    cylinderSideOfPlane (cylinderSidePlane q) = q := by
  have hn := norm_cylinderSidePlane hq
  have h2 := (abs_le.mp hq.2).1
  have hpos : (0 : ℝ) < 2 + q.2 := by linarith
  refine Prod.ext ?_ ?_
  · change ‖cylinderSidePlane q‖⁻¹ • cylinderSidePlane q = q.1
    rw [hn, cylinderSidePlane, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
  · change ‖cylinderSidePlane q‖ - 2 = q.2
    rw [hn]
    ring

theorem cylinderSideOfPlane_mem {x : EuclideanSpace ℝ (Fin 2)} (h1 : 1 ≤ ‖x‖) (h3 : ‖x‖ ≤ 3) :
    cylinderSideOfPlane x ∈ cylinderSide := by
  have hx : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at h1
    linarith
  exact ⟨norm_smul_inv_norm hx, abs_le.mpr ⟨by change -1 ≤ ‖x‖ - 2; linarith,
    by change ‖x‖ - 2 ≤ 1; linarith⟩⟩

theorem cylinderSidePlane_ofPlane {x : EuclideanSpace ℝ (Fin 2)} (h1 : 1 ≤ ‖x‖) :
    cylinderSidePlane (cylinderSideOfPlane x) = x := by
  have hx : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at h1
    linarith
  change (2 + (‖x‖ - 2)) • (‖x‖⁻¹ • x) = x
  rw [show 2 + (‖x‖ - 2) = ‖x‖ by ring, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx),
    one_smul]

theorem norm_mem_Ioo_of_isOpen_subset_annulus {O : Set (EuclideanSpace ℝ (Fin 2))}
    (hO : IsOpen O) (hsub : ∀ y ∈ O, 1 ≤ ‖y‖ ∧ ‖y‖ ≤ 3) {y : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∈ O) : 1 < ‖y‖ ∧ ‖y‖ < 3 := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO y hy
  obtain ⟨h1, h3⟩ := hsub y hy
  constructor
  · by_contra hn
    have hy1 : ‖y‖ = 1 := le_antisymm (not_lt.mp hn) h1
    set δ := min (ε / 2) (1 / 2) with hδ
    have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
    have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
    have hz : (1 - δ) • y ∈ O := by
      apply hball
      rw [mem_ball, dist_eq_norm, show (1 - δ) • y - y = -(δ • y) by rw [sub_smul, one_smul]; abel,
        norm_neg, norm_smul, Real.norm_of_nonneg hδpos.le, hy1, mul_one]
      exact hδε
    have hn' := (hsub _ hz).1
    rw [norm_smul, Real.norm_of_nonneg (by linarith), hy1, mul_one] at hn'
    linarith
  · by_contra hn
    have hy3 : ‖y‖ = 3 := le_antisymm h3 (not_lt.mp hn)
    set δ := ε / 6 with hδ
    have hδpos : 0 < δ := by positivity
    have hz : (1 + δ) • y ∈ O := by
      apply hball
      rw [mem_ball, dist_eq_norm, show (1 + δ) • y - y = δ • y by rw [add_smul, one_smul]; abel,
        norm_smul, Real.norm_of_nonneg hδpos.le, hy3]
      linarith
    have hn' := (hsub _ hz).2
    rw [norm_smul, Real.norm_of_nonneg (by linarith), hy3] at hn'
    linarith

theorem abs_snd_lt_one_of_cylinderSide (σ : cylinderSide ≃ₜ cylinderSide) (q : cylinderSide)
    (hq : |q.val.2| < 1) : |(σ q).val.2| < 1 := by
  classical
  let G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := fun x =>
    if h : cylinderSideOfPlane x ∈ cylinderSide then cylinderSidePlane (σ ⟨_, h⟩).val else x
  let U : Set (EuclideanSpace ℝ (Fin 2)) := {x | 1 < ‖x‖ ∧ ‖x‖ < 3}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hmem : ∀ x ∈ U, cylinderSideOfPlane x ∈ cylinderSide :=
    fun x hx => cylinderSideOfPlane_mem hx.1.le hx.2.le
  have hGU : ∀ x (hx : x ∈ U), G x = cylinderSidePlane (σ ⟨_, hmem x hx⟩).val :=
    fun x hx => dite_eq_left (hmem x hx)
  have hP : Continuous cylinderSidePlane :=
    (continuous_const.add continuous_snd).smul continuous_fst
  have hcont : ContinuousOn G U := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hne : ∀ x : U, ‖x.val‖ ≠ 0 := fun x => by
      have := x.2.1
      positivity
    have hc1 : Continuous (fun x : U =>
        (⟨cylinderSideOfPlane x.val, hmem x.val x.2⟩ : cylinderSide)) := by
      apply Continuous.subtype_mk
      exact (((continuous_norm.comp continuous_subtype_val).inv₀ hne).smul
        continuous_subtype_val).prodMk
        ((continuous_norm.comp continuous_subtype_val).sub continuous_const)
    have hc2 : Continuous (fun x : U =>
        cylinderSidePlane (σ ⟨cylinderSideOfPlane x.val, hmem x.val x.2⟩).val) :=
      hP.comp (continuous_subtype_val.comp (σ.continuous.comp hc1))
    refine hc2.congr fun x => ?_
    exact (hGU x.val x.2).symm
  have hinj : InjOn G U := by
    intro x hx y hy hxy
    rw [hGU x hx, hGU y hy] at hxy
    have h1 := congrArg cylinderSideOfPlane hxy
    rw [cylinderSideOfPlane_plane (σ _).2, cylinderSideOfPlane_plane (σ _).2] at h1
    have h2 := σ.injective (Subtype.ext h1)
    have h3 := congrArg (fun q : cylinderSide => cylinderSidePlane q.val) h2
    simp only at h3
    rwa [cylinderSidePlane_ofPlane hx.1.le, cylinderSidePlane_ofPlane hy.1.le] at h3
  have hopen : IsOpen (G '' U) :=
    isOpen_image_of_continuousOn_injOn (E := EuclideanSpace ℝ (Fin 2)) hU hcont hinj
  have hann : ∀ y ∈ G '' U, 1 ≤ ‖y‖ ∧ ‖y‖ ≤ 3 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hGU x hx, norm_cylinderSidePlane (σ _).2]
    obtain ⟨h1, h2⟩ := abs_le.mp (σ ⟨_, hmem x hx⟩).2.2
    exact ⟨by linarith, by linarith⟩
  obtain ⟨hq1, hq2⟩ := abs_lt.mp hq
  have hqU : cylinderSidePlane q.val ∈ U := by
    change 1 < ‖cylinderSidePlane q.val‖ ∧ ‖cylinderSidePlane q.val‖ < 3
    rw [norm_cylinderSidePlane q.2]
    exact ⟨by linarith, by linarith⟩
  have hGq : G (cylinderSidePlane q.val) = cylinderSidePlane (σ q).val := by
    rw [hGU _ hqU]
    have he : (⟨cylinderSideOfPlane (cylinderSidePlane q.val), hmem _ hqU⟩ : cylinderSide) = q :=
      Subtype.ext (cylinderSideOfPlane_plane q.2)
    rw [he]
  have hy := norm_mem_Ioo_of_isOpen_subset_annulus hopen hann ⟨_, hqU, hGq⟩
  rw [norm_cylinderSidePlane (σ q).2] at hy
  rw [abs_lt]
  exact ⟨by linarith [hy.1], by linarith [hy.2]⟩

theorem abs_snd_eq_one_iff_of_cylinderSide (σ : cylinderSide ≃ₜ cylinderSide)
    (q : cylinderSide) : |(σ q).val.2| = 1 ↔ |q.val.2| = 1 := by
  have hle : ∀ p : cylinderSide, |p.val.2| ≤ 1 := fun p => p.2.2
  constructor
  · intro h
    by_contra hne
    have h1 := abs_snd_lt_one_of_cylinderSide σ q (lt_of_le_of_ne (hle q) hne)
    rw [h] at h1
    exact lt_irrefl _ h1
  · intro h
    by_contra hne
    have h1 := abs_snd_lt_one_of_cylinderSide σ.symm (σ q) (lt_of_le_of_ne (hle _) hne)
    rw [Homeomorph.symm_apply_apply, h] at h1
    exact lt_irrefl _ h1

theorem mem_cylinderSide_of_mem_sphere {u : EuclideanSpace ℝ (Fin 2)}
    (hu : u ∈ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) {e : ℝ} (he : |e| ≤ 1) :
    (u, e) ∈ cylinderSide :=
  ⟨mem_sphere_zero_iff_norm.mp hu, he⟩

theorem exists_rimSign (σ : cylinderSide ≃ₜ cylinderSide) {e : ℝ} (he : |e| = 1) :
    ∃ e', |e'| = 1 ∧ ∀ q : cylinderSide, q.val.2 = e → (σ q).val.2 = e' := by
  classical
  let S := sphere (0 : EuclideanSpace ℝ (Fin 2)) 1
  have hS : IsPreconnected S := by
    apply isPreconnected_sphere _ _ 1
    rw [← Module.finrank_eq_rank]
    norm_num
  let h : EuclideanSpace ℝ (Fin 2) → ℝ := fun u =>
    if hu : (u, e) ∈ cylinderSide then (σ ⟨(u, e), hu⟩).val.2 else 1
  have hmemS : ∀ u ∈ S, (u, e) ∈ cylinderSide :=
    fun u hu => mem_cylinderSide_of_mem_sphere hu he.le
  have hhS : ∀ u (hu : u ∈ S), h u = (σ ⟨(u, e), hmemS u hu⟩).val.2 :=
    fun u hu => dite_eq_left (hmemS u hu)
  have hc : ContinuousOn h S := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hc1 : Continuous (fun u : S => (⟨(u.val, e), hmemS u.val u.2⟩ : cylinderSide)) :=
      (continuous_subtype_val.prodMk continuous_const).subtype_mk _
    refine (continuous_snd.comp (continuous_subtype_val.comp (σ.continuous.comp hc1))).congr
      fun u => ?_
    exact (hhS u.val u.2).symm
  have hT : ({x : ℝ | |x| = 1}).Finite := by
    apply (Set.toFinite ({1, -1} : Set ℝ)).subset
    intro x hx
    rcases (abs_eq zero_le_one).mp hx with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  have hmaps : MapsTo h S {x : ℝ | |x| = 1} := by
    intro u hu
    change |h u| = 1
    rw [hhS u hu, abs_snd_eq_one_iff_of_cylinderSide]
    exact he
  obtain ⟨u₀, hu₀⟩ : S.Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  refine ⟨h u₀, hmaps hu₀, fun q hq => ?_⟩
  have hq1 : q.val.1 ∈ S := mem_sphere_zero_iff_norm.mpr q.2.1
  have hconst := hS.constant_of_mapsTo hT.isDiscrete hc hmaps hq1 hu₀
  rw [← hconst, hhS _ hq1]
  have he' : (⟨(q.val.1, e), hmemS _ hq1⟩ : cylinderSide) = q :=
    Subtype.ext (Prod.ext rfl hq.symm)
  rw [he']

theorem exists_rimSigns (σ : cylinderSide ≃ₜ cylinderSide) :
    ∃ ε₁ ε₂ : ℝ, |ε₁| = 1 ∧ |ε₂| = 1 ∧ ε₁ ≠ ε₂ ∧
      (∀ q : cylinderSide, q.val.2 = 1 → (σ q).val.2 = ε₁) ∧
      ∀ q : cylinderSide, q.val.2 = -1 → (σ q).val.2 = ε₂ := by
  obtain ⟨ε₁, h1, h1'⟩ := exists_rimSign σ (e := 1) (by norm_num)
  obtain ⟨ε₂, h2, h2'⟩ := exists_rimSign σ (e := -1) (by norm_num)
  refine ⟨ε₁, ε₂, h1, h2, ?_, h1', h2'⟩
  intro heq
  obtain ⟨u₀, hu₀⟩ : (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  have hm : (u₀, -ε₁) ∈ cylinderSide :=
    mem_cylinderSide_of_mem_sphere hu₀ (by rw [abs_neg, h1])
  obtain ⟨q, hq⟩ := σ.surjective ⟨_, hm⟩
  have hq2 : (σ q).val.2 = -ε₁ := by rw [hq]
  have habs : |q.val.2| = 1 := by
    rw [← abs_snd_eq_one_iff_of_cylinderSide σ, hq2, abs_neg, h1]
  have hne : ε₁ ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at h1
    norm_num at h1
  rcases (abs_eq zero_le_one).mp habs with hs | hs
  · rw [h1' q hs] at hq2
    exact hne (by linarith)
  · rw [h2' q hs, ← heq] at hq2
    exact hne (by linarith)

theorem eq_or_eq_of_rimSigns {ε₁ ε₂ t : ℝ} (h1 : |ε₁| = 1) (h2 : |ε₂| = 1) (hne : ε₁ ≠ ε₂)
    (ht : |t| = 1) : t = ε₁ ∨ t = ε₂ := by
  rcases (abs_eq zero_le_one).mp h1 with a | a <;> rcases (abs_eq zero_le_one).mp h2 with b | b <;>
    rcases (abs_eq zero_le_one).mp ht with c | c <;> subst a b c <;> simp_all

theorem exists_rimCircleHomeomorph (σ : cylinderSide ≃ₜ cylinderSide) {e ε e' ε' : ℝ}
    (he : |e| = 1) (hε : |ε| = 1) (he' : |e'| = 1) (hee : e ≠ e') (hεε : ε ≠ ε')
    (hσe : ∀ q : cylinderSide, q.val.2 = e → (σ q).val.2 = ε)
    (hσe' : ∀ q : cylinderSide, q.val.2 = e' → (σ q).val.2 = ε') :
    ∃ τ : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
      ∀ (u : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (hu : ((u : EuclideanSpace ℝ (Fin 2)), e) ∈
        cylinderSide), (σ ⟨_, hu⟩).val = (((τ u) : EuclideanSpace ℝ (Fin 2)), ε) := by
  let S := sphere (0 : EuclideanSpace ℝ (Fin 2)) 1
  have hmem : ∀ u : S, ((u : EuclideanSpace ℝ (Fin 2)), e) ∈ cylinderSide :=
    fun u => mem_cylinderSide_of_mem_sphere u.2 he.le
  let τf : S → S := fun u =>
    ⟨(σ ⟨_, hmem u⟩).val.1, mem_sphere_zero_iff_norm.mpr (σ ⟨_, hmem u⟩).2.1⟩
  have hτc : Continuous τf :=
    ((continuous_fst.comp (continuous_subtype_val.comp (σ.continuous.comp
      ((continuous_subtype_val.prodMk continuous_const).subtype_mk _))))).subtype_mk _
  have hval : ∀ u : S, (σ ⟨_, hmem u⟩).val = (((τf u) : EuclideanSpace ℝ (Fin 2)), ε) :=
    fun u => Prod.ext rfl (hσe _ rfl)
  have hinj : Function.Injective τf := by
    intro u v huv
    have h1 : (σ ⟨_, hmem u⟩).val = (σ ⟨_, hmem v⟩).val := by
      rw [hval, hval, huv]
    have h2 := congrArg (fun q : cylinderSide => q.val.1) (σ.injective (Subtype.ext h1))
    exact Subtype.ext h2
  have hsurj : Function.Surjective τf := by
    intro v
    have hm : ((v : EuclideanSpace ℝ (Fin 2)), ε) ∈ cylinderSide :=
      mem_cylinderSide_of_mem_sphere v.2 hε.le
    obtain ⟨q, hq⟩ := σ.surjective ⟨_, hm⟩
    have hq2 : (σ q).val.2 = ε := by rw [hq]
    have habs : |q.val.2| = 1 := by rw [← abs_snd_eq_one_iff_of_cylinderSide σ, hq2, hε]
    have hqe : q.val.2 = e := by
      rcases eq_or_eq_of_rimSigns he he' hee habs with h | h
      · exact h
      · rw [hσe' q h] at hq2
        exact absurd hq2.symm hεε
    have hu : q.val.1 ∈ S := mem_sphere_zero_iff_norm.mpr q.2.1
    refine ⟨⟨_, hu⟩, Subtype.ext ?_⟩
    have he2 : (⟨(q.val.1, e), hmem ⟨_, hu⟩⟩ : cylinderSide) = q :=
      Subtype.ext (Prod.ext rfl hqe.symm)
    have h3 : (σ ⟨(q.val.1, e), hmem ⟨_, hu⟩⟩).val.1 = (v : EuclideanSpace ℝ (Fin 2)) := by
      rw [he2, hq]
    exact h3
  refine ⟨hτc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective τf ⟨hinj, hsurj⟩),
    fun u hu => ?_⟩
  exact hval u

theorem norm_eq_one_of_mem_cylinderSide {q : EuclideanSpace ℝ (Fin 2) × ℝ}
    (hq : q ∈ cylinderSide) : ‖q‖ = 1 := by
  rw [Prod.norm_def, hq.1, Real.norm_eq_abs]
  exact max_eq_left hq.2

theorem norm_fst_lt_one_of_notMem_cylinderSide {q : EuclideanSpace ℝ (Fin 2) × ℝ}
    (hq : ‖q‖ = 1) (hs : q ∉ cylinderSide) : ‖q.1‖ < 1 ∧ |q.2| = 1 := by
  rw [Prod.norm_def, Real.norm_eq_abs] at hq
  have h1 : ‖q.1‖ ≤ 1 := hq ▸ le_max_left _ _
  have h2 : |q.2| ≤ 1 := hq ▸ le_max_right _ _
  have h3 : ‖q.1‖ ≠ 1 := fun h => hs ⟨h, h2⟩
  refine ⟨lt_of_le_of_ne h1 h3, ?_⟩
  rcases max_choice ‖q.1‖ |q.2| with h | h
  · rw [h] at hq
    exact absurd hq h3
  · rw [h] at hq
    exact hq

theorem exists_homeomorph_extension_of_cylinderSide (σ : cylinderSide ≃ₜ cylinderSide) :
    ∃ Φ : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₜ (EuclideanSpace ℝ (Fin 2) × ℝ),
      (∀ q, ‖Φ q‖ = ‖q‖) ∧ ∀ q : cylinderSide, Φ q.val = (σ q).val := by
  classical
  obtain ⟨ε₁, ε₂, h1, h2, hne, hσ1, hσ2⟩ := exists_rimSigns σ
  obtain ⟨τ₁, hτ₁⟩ := exists_rimCircleHomeomorph σ (e := 1) (e' := -1) (by norm_num) h1
    (by norm_num) (by norm_num) hne hσ1 hσ2
  obtain ⟨τ₂, hτ₂⟩ := exists_rimCircleHomeomorph σ (e := -1) (e' := 1) (by norm_num) h2
    (by norm_num) (by norm_num) hne.symm hσ2 hσ1
  let R₁ := sphereRadialHomeomorph τ₁
  let R₂ := sphereRadialHomeomorph τ₂
  have hR₁n : ∀ x, ‖R₁ x‖ = ‖x‖ := norm_sphereRadialHomeomorph τ₁
  have hR₂n : ∀ x, ‖R₂ x‖ = ‖x‖ := norm_sphereRadialHomeomorph τ₂
  have hR₁s : ∀ x, ‖R₁.symm x‖ = ‖x‖ := norm_sphereRadialHomeomorph τ₁.symm
  have hR₂s : ∀ x, ‖R₂.symm x‖ = ‖x‖ := norm_sphereRadialHomeomorph τ₂.symm
  let B0 : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2) × ℝ := fun q =>
    if h : q ∈ cylinderSide then (σ ⟨q, h⟩).val
    else if 0 < q.2 then (R₁ q.1, ε₁) else (R₂ q.1, ε₂)
  let Sph := sphere (0 : EuclideanSpace ℝ (Fin 2) × ℝ) 1
  have hside : ∀ q (h : q ∈ cylinderSide), B0 q = (σ ⟨q, h⟩).val := fun q h => dite_eq_left h
  have hcapP : ∀ q, q ∉ cylinderSide → 0 < q.2 → B0 q = (R₁ q.1, ε₁) := by
    intro q h hp
    simp only [B0, dite_eq_right h, ite_eq_left hp]
  have hcapN : ∀ q, q ∉ cylinderSide → ¬ 0 < q.2 → B0 q = (R₂ q.1, ε₂) := by
    intro q h hp
    simp only [B0, dite_eq_right h, ite_eq_right hp]
  have hB0n : ∀ q ∈ Sph, B0 q ∈ Sph := by
    intro q hq
    rw [mem_sphere_zero_iff_norm] at hq ⊢
    by_cases hs : q ∈ cylinderSide
    · rw [hside q hs]
      exact norm_eq_one_of_mem_cylinderSide (σ _).2
    · obtain ⟨hq1, -⟩ := norm_fst_lt_one_of_notMem_cylinderSide hq hs
      by_cases hp : 0 < q.2
      · rw [hcapP q hs hp, Prod.norm_def, hR₁n, Real.norm_eq_abs, h1]
        exact max_eq_right hq1.le
      · rw [hcapN q hs hp, Prod.norm_def, hR₂n, Real.norm_eq_abs, h2]
        exact max_eq_right hq1.le
  have hsideC : IsClosed cylinderSide :=
    (isClosed_eq (continuous_norm.comp continuous_fst) continuous_const).inter
      (isClosed_le (continuous_abs.comp continuous_snd) continuous_const)
  let CP : Set (EuclideanSpace ℝ (Fin 2) × ℝ) := {q | ‖q.1‖ ≤ 1 ∧ q.2 = 1}
  let CN : Set (EuclideanSpace ℝ (Fin 2) × ℝ) := {q | ‖q.1‖ ≤ 1 ∧ q.2 = -1}
  have hCPC : IsClosed CP :=
    (isClosed_le (continuous_norm.comp continuous_fst) continuous_const).inter
      (isClosed_eq continuous_snd continuous_const)
  have hCNC : IsClosed CN :=
    (isClosed_le (continuous_norm.comp continuous_fst) continuous_const).inter
      (isClosed_eq continuous_snd continuous_const)
  have h1c : ContinuousOn B0 cylinderSide := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine (continuous_subtype_val.comp σ.continuous).congr fun q => ?_
    exact (hside q.val q.2).symm
  have h2c : ContinuousOn B0 CP := by
    have hc : Continuous (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => (R₁ q.1, ε₁)) :=
      (R₁.continuous.comp continuous_fst).prodMk continuous_const
    refine hc.continuousOn.congr fun q hq => ?_
    by_cases hs : q ∈ cylinderSide
    · rw [hside q hs]
      have hu : q.1 ∈ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := mem_sphere_zero_iff_norm.mpr hs.1
      have hmem1 : (((⟨q.1, hu⟩ : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
          EuclideanSpace ℝ (Fin 2)), (1 : ℝ)) ∈ cylinderSide := ⟨hs.1, by norm_num⟩
      have hR : R₁ q.1 = ((τ₁ ⟨q.1, hu⟩ : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
          EuclideanSpace ℝ (Fin 2)) := sphereRadialHomeomorph_apply_sphere τ₁ ⟨q.1, hu⟩
      change (σ ⟨q, hs⟩).val = (R₁ q.1, ε₁)
      rw [hR, ← hτ₁ ⟨q.1, hu⟩ hmem1]
      exact congrArg (fun p => (σ p).val) (Subtype.ext (Prod.ext rfl hq.2))
    · rw [hcapP q hs (by rw [hq.2]; norm_num)]
  have h3c : ContinuousOn B0 CN := by
    have hc : Continuous (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => (R₂ q.1, ε₂)) :=
      (R₂.continuous.comp continuous_fst).prodMk continuous_const
    refine hc.continuousOn.congr fun q hq => ?_
    by_cases hs : q ∈ cylinderSide
    · rw [hside q hs]
      have hu : q.1 ∈ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := mem_sphere_zero_iff_norm.mpr hs.1
      have hmem1 : (((⟨q.1, hu⟩ : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
          EuclideanSpace ℝ (Fin 2)), (-1 : ℝ)) ∈ cylinderSide := ⟨hs.1, by norm_num⟩
      have hR : R₂ q.1 = ((τ₂ ⟨q.1, hu⟩ : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
          EuclideanSpace ℝ (Fin 2)) := sphereRadialHomeomorph_apply_sphere τ₂ ⟨q.1, hu⟩
      change (σ ⟨q, hs⟩).val = (R₂ q.1, ε₂)
      rw [hR, ← hτ₂ ⟨q.1, hu⟩ hmem1]
      exact congrArg (fun p => (σ p).val) (Subtype.ext (Prod.ext rfl hq.2))
    · rw [hcapN q hs (by rw [hq.2]; norm_num)]
  have hcov : Sph ⊆ cylinderSide ∪ CP ∪ CN := by
    intro q hq
    by_cases hs : q ∈ cylinderSide
    · exact Or.inl (Or.inl hs)
    · obtain ⟨hq1, hq2⟩ :=
        norm_fst_lt_one_of_notMem_cylinderSide (mem_sphere_zero_iff_norm.mp hq) hs
      rcases (abs_eq zero_le_one).mp hq2 with h | h
      · exact Or.inl (Or.inr ⟨hq1.le, h⟩)
      · exact Or.inr ⟨hq1.le, h⟩
  have hcont : ContinuousOn B0 Sph :=
    ((h1c.union_of_isClosed h2c hsideC hCPC).union_of_isClosed h3c (hsideC.union hCPC)
      hCNC).mono hcov
  let βf : Sph → Sph := fun q => ⟨B0 q.val, hB0n q.val q.2⟩
  have hβc : Continuous βf :=
    (hcont.comp_continuous continuous_subtype_val fun q => q.2).subtype_mk _
  have hcapfst : ∀ q, q ∈ Sph → q ∉ cylinderSide → ‖(B0 q).1‖ < 1 := by
    intro q hq hs
    obtain ⟨hq1, -⟩ := norm_fst_lt_one_of_notMem_cylinderSide (mem_sphere_zero_iff_norm.mp hq) hs
    by_cases hp : 0 < q.2
    · rw [hcapP q hs hp, hR₁n]
      exact hq1
    · rw [hcapN q hs hp, hR₂n]
      exact hq1
  have hsidefst : ∀ q (hs : q ∈ cylinderSide), ‖(B0 q).1‖ = 1 := by
    intro q hs
    rw [hside q hs]
    exact (σ _).2.1
  have hsnd : ∀ q, q ∈ Sph → q ∉ cylinderSide → (0 < q.2 → q.2 = 1) ∧ (¬ 0 < q.2 → q.2 = -1) := by
    intro q hq hs
    obtain ⟨-, hq2⟩ := norm_fst_lt_one_of_notMem_cylinderSide (mem_sphere_zero_iff_norm.mp hq) hs
    constructor
    · intro hp
      rcases (abs_eq zero_le_one).mp hq2 with h | h
      · exact h
      · linarith
    · intro hp
      rcases (abs_eq zero_le_one).mp hq2 with h | h
      · rw [h] at hp
        norm_num at hp
      · exact h
  have hβinj : Function.Injective βf := by
    intro q1 q2 h
    have h' : B0 q1.val = B0 q2.val := congrArg Subtype.val h
    apply Subtype.ext
    by_cases hs1 : q1.val ∈ cylinderSide <;> by_cases hs2 : q2.val ∈ cylinderSide
    · rw [hside _ hs1, hside _ hs2] at h'
      exact congrArg (fun p : cylinderSide => p.val) (σ.injective (Subtype.ext h'))
    · exfalso
      have ha := hsidefst _ hs1
      rw [h'] at ha
      linarith [hcapfst _ q2.2 hs2]
    · exfalso
      have ha := hsidefst _ hs2
      rw [← h'] at ha
      linarith [hcapfst _ q1.2 hs1]
    · obtain ⟨hP1, hN1⟩ := hsnd _ q1.2 hs1
      obtain ⟨hP2, hN2⟩ := hsnd _ q2.2 hs2
      by_cases hp1 : 0 < q1.val.2 <;> by_cases hp2 : 0 < q2.val.2
      · rw [hcapP _ hs1 hp1, hcapP _ hs2 hp2] at h'
        exact Prod.ext (R₁.injective (congrArg Prod.fst h')) ((hP1 hp1).trans (hP2 hp2).symm)
      · rw [hcapP _ hs1 hp1, hcapN _ hs2 hp2] at h'
        exact absurd (congrArg Prod.snd h') hne
      · rw [hcapN _ hs1 hp1, hcapP _ hs2 hp2] at h'
        exact absurd (congrArg Prod.snd h').symm hne
      · rw [hcapN _ hs1 hp1, hcapN _ hs2 hp2] at h'
        exact Prod.ext (R₂.injective (congrArg Prod.fst h')) ((hN1 hp1).trans (hN2 hp2).symm)
  have hβsurj : Function.Surjective βf := by
    intro y
    by_cases hs : y.val ∈ cylinderSide
    · obtain ⟨q, hq⟩ := σ.surjective ⟨y.val, hs⟩
      refine ⟨⟨q.val, mem_sphere_zero_iff_norm.mpr (norm_eq_one_of_mem_cylinderSide q.2)⟩,
        Subtype.ext ?_⟩
      change B0 q.val = y.val
      rw [hside _ q.2, hq]
    · obtain ⟨hy1, hy2⟩ :=
        norm_fst_lt_one_of_notMem_cylinderSide (mem_sphere_zero_iff_norm.mp y.2) hs
      rcases eq_or_eq_of_rimSigns h1 h2 hne hy2 with ht | ht
      · let q : EuclideanSpace ℝ (Fin 2) × ℝ := (R₁.symm y.val.1, 1)
        have hqn : ‖q.1‖ = ‖y.val.1‖ := hR₁s _
        have hqs : q ∉ cylinderSide := fun h => by
          have := h.1
          rw [hqn] at this
          linarith
        have hqS : q ∈ Sph := by
          rw [mem_sphere_zero_iff_norm, Prod.norm_def, hqn, Real.norm_eq_abs, abs_one]
          exact max_eq_right hy1.le
        refine ⟨⟨q, hqS⟩, Subtype.ext ?_⟩
        change B0 q = y.val
        rw [hcapP q hqs (by norm_num)]
        exact Prod.ext (R₁.apply_symm_apply _) ht.symm
      · let q : EuclideanSpace ℝ (Fin 2) × ℝ := (R₂.symm y.val.1, -1)
        have hqn : ‖q.1‖ = ‖y.val.1‖ := hR₂s _
        have hqs : q ∉ cylinderSide := fun h => by
          have := h.1
          rw [hqn] at this
          linarith
        have hqS : q ∈ Sph := by
          rw [mem_sphere_zero_iff_norm, Prod.norm_def, hqn, Real.norm_eq_abs, abs_neg, abs_one]
          exact max_eq_right hy1.le
        refine ⟨⟨q, hqS⟩, Subtype.ext ?_⟩
        change B0 q = y.val
        rw [hcapN q hqs (by norm_num)]
        exact Prod.ext (R₂.apply_symm_apply _) ht.symm
  have hSc : CompactSpace Sph := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  let β : Sph ≃ₜ Sph := hβc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective βf ⟨hβinj, hβsurj⟩)
  refine ⟨sphereRadialHomeomorph β, fun q => norm_sphereRadialHomeomorph β q, fun q => ?_⟩
  have hqS : q.val ∈ Sph := mem_sphere_zero_iff_norm.mpr (norm_eq_one_of_mem_cylinderSide q.2)
  have h := sphereRadialHomeomorph_apply_sphere β ⟨q.val, hqS⟩
  change sphereRadialHomeomorph β ((⟨q.val, hqS⟩ : Sph) : EuclideanSpace ℝ (Fin 2) × ℝ) = _
  rw [h]
  exact hside q.val q.2

end DifferentialGeometry.Topology.PiecewiseLinear
