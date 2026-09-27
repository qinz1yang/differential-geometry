/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BigonBoundaryCrossing
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Order.LocalExtr

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem HasPLCurveCrossingOnAt.isLocalMaxOn_surface_of_level
    {S A B U : Set E} {x : E} (hc : HasPLCurveCrossingOnAt S A B x)
    {f : E → ℝ} (hU : IsOpen U) (hxU : x ∈ U) (hf : ContinuousOn f (S ∩ U))
    (hlevel : ∀ y ∈ S ∩ U, f y = f x ↔ y ∈ B) (hmax : IsLocalMaxOn f A x) :
    IsLocalMaxOn f S x := by
  obtain ⟨W, V, φ, T, P, Q, hW, hV, hxW, hφ, hφx, hT, hP, hQ, hPT, hQT, hPQ,
    hlocal⟩ := hc
  have hsmall : ∀ᶠ y in 𝓝 x, y ∈ W ∧ y ∈ U ∧
      (y ∈ S ↔ φ y ∈ T) ∧ (y ∈ A ↔ φ y ∈ P) ∧ (y ∈ B ↔ φ y ∈ Q) ∧
      (y ∈ A → f y ≤ f x) := by
    filter_upwards [hW.mem_nhds hxW, hU.mem_nhds hxU, hlocal,
      eventually_nhdsWithin_iff.mp hmax] with y hyW hyU hy hle
    exact ⟨hyW, hyU, hy.1, hy.2.1, hy.2.2, hle⟩
  obtain ⟨O, hOO, hO, hxO⟩ := _root_.mem_nhds_iff.mp hsmall
  let ψ := Function.invFunOn φ W
  have h0V : (0 : E) ∈ V := hφx ▸ hφ.bijOn.mapsTo hxW
  have hψ0 : ψ 0 = x := by
    rw [← hφx]
    exact hφ.bijOn.invOn_invFunOn.1 hxW
  have hψc : ContinuousAt ψ 0 := hφ.isPiecewiseAffineOn_invFunOn.continuousOn.continuousAt
    (hV.mem_nhds h0V)
  have htarget : V ∩ ψ ⁻¹' O ∈ 𝓝 (0 : E) :=
    Filter.inter_mem (hV.mem_nhds h0V)
      (hψc.preimage_mem_nhds (hψ0.symm ▸ hO.mem_nhds hxO))
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp htarget
  have hcoords : ∀ z ∈ ball (0 : E) r, φ (ψ z) = z :=
    fun z hz => hφ.bijOn.invOn_invFunOn.2 (hrsub hz).1
  have hmaps : MapsTo ψ (ball (0 : E) r ∩ (T : Set E)) (S ∩ U) := by
    intro z hz
    have ho := hOO (hrsub hz.1).2
    refine ⟨ho.2.2.1.mpr ?_, ho.2.1⟩
    rw [hcoords z hz.1]
    exact hz.2
  let g : E → ℝ := fun z => f (ψ z)
  have hg : ContinuousOn g (ball (0 : E) r ∩ (T : Set E)) :=
    hf.comp (hφ.isPiecewiseAffineOn_invFunOn.continuousOn.mono
      (fun z hz => (hrsub hz.1).1)) hmaps
  have hzero : ∀ z ∈ ball (0 : E) r ∩ (T : Set E), g z = f x ↔ z ∈ Q := by
    intro z hz
    rw [show g z = f (ψ z) from rfl, hlevel _ (hmaps hz)]
    exact (hOO (hrsub hz.1).2).2.2.2.2.1.trans (by rw [hcoords z hz.1])
  have hPne : P ≠ ⊥ := by
    intro heq
    rw [heq, finrank_bot] at hP
    omega
  obtain ⟨v, hvP, hv0⟩ := P.ne_bot_iff.mp hPne
  have hvQ : v ∉ Q := by
    intro hvQ
    have hv : v ∈ (P ⊓ Q : Submodule ℝ E) := ⟨hvP, hvQ⟩
    rw [hPQ] at hv
    exact hv0 hv
  obtain ⟨ℓ, hℓv, hQℓ⟩ := Q.exists_le_ker_of_notMem hvQ
  have hQK : Q ≤ T ⊓ LinearMap.ker ℓ := le_inf hQT hQℓ
  have hKT : T ⊓ LinearMap.ker ℓ < T := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro heq
    have hv : v ∈ T ⊓ LinearMap.ker ℓ := heq.symm ▸ hPT hvP
    exact hℓv hv.2
  have hker : Q = T ⊓ LinearMap.ker ℓ := by
    apply Submodule.eq_of_le_of_finrank_eq hQK
    have hlo := Submodule.finrank_mono hQK
    have hhi := Submodule.finrank_lt_finrank_of_lt hKT
    omega
  let w := (ℓ v)⁻¹ • v
  have hwP : w ∈ P := P.smul_mem _ hvP
  have hℓw : ℓ w = 1 := by simp [w, hℓv]
  have hsc : Continuous (fun t : ℝ => t • w) := continuous_id.smul continuous_const
  have hn : ∀ᶠ t in 𝓝 (0 : ℝ), t • w ∈ ball (0 : E) r :=
    hsc.continuousAt.preimage_mem_nhds (by simpa using ball_mem_nhds (0 : E) hr)
  obtain ⟨a, ha, haB⟩ := Metric.mem_nhds_iff.mp hn
  have hapos : a / 2 ∈ ball (0 : ℝ) a := by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos ha)]
    linarith
  have haneg : -(a / 2) ∈ ball (0 : ℝ) a := by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_neg, abs_of_pos (half_pos ha)]
    linarith
  have hside : ∀ R : Set E, Convex ℝ R → R ⊆ ball (0 : E) r ∩ (T : Set E) →
      (∀ z ∈ R, ℓ z ≠ 0) → (∃ z ∈ R, z ∈ P) → ∀ z ∈ R, g z < f x := by
    intro R hR hRsub hRne hRP
    have hconn := hR.isPreconnected.image g (hg.mono hRsub)
    have hcover : g '' R ⊆ Iio (f x) ∪ Ioi (f x) := by
      rintro _ ⟨z, hz, rfl⟩
      have hne : g z ≠ f x := by
        intro hgz
        have hzQ := (hzero z (hRsub hz)).mp hgz
        exact hRne z hz (hQℓ hzQ)
      exact hne.lt_or_gt
    have hdis : Disjoint (Iio (f x)) (Ioi (f x)) :=
      Set.disjoint_left.mpr fun z hz hz' => lt_asymm (show z < f x from hz) hz'
    rcases hconn.subset_or_subset isOpen_Iio isOpen_Ioi hdis hcover with hlt | hgt
    · exact fun z hz => hlt ⟨z, hz, rfl⟩
    · obtain ⟨z, hzR, hzP⟩ := hRP
      have hzball := (hRsub hzR).1
      have ho := hOO (hrsub hzball).2
      have hzA : ψ z ∈ A := ho.2.2.2.1.mpr (by rw [hcoords z hzball]; exact hzP)
      exact ((ho.2.2.2.2.2 hzA).not_gt (hgt ⟨z, hzR, rfl⟩)).elim
  have hle : ∀ z ∈ ball (0 : E) r ∩ (T : Set E), g z ≤ f x := by
    intro z hz
    by_cases hzQ : z ∈ Q
    · exact ((hzero z hz).mpr hzQ).le
    have hℓz : ℓ z ≠ 0 := fun heq => hzQ (hker.symm ▸ ⟨hz.2, heq⟩)
    rcases hℓz.lt_or_gt with hneg | hpos
    · apply le_of_lt (hside (ball (0 : E) r ∩ (T : Set E) ∩ {y | ℓ y < 0})
        (((convex_ball (0 : E) r).inter T.convex).inter
          (convex_halfSpace_lt ℓ.isLinear 0)) inter_subset_left
        (fun y hy => hy.2.ne) ?_ z ⟨hz, hneg⟩)
      refine ⟨-(a / 2) • w, ⟨⟨haB haneg, hPT (P.smul_mem _ hwP)⟩, ?_⟩,
        P.smul_mem _ hwP⟩
      change ℓ (-(a / 2) • w) < 0
      simpa only [map_smul, smul_eq_mul, hℓw, mul_one] using neg_lt_zero.mpr (half_pos ha)
    · apply le_of_lt (hside (ball (0 : E) r ∩ (T : Set E) ∩ {y | 0 < ℓ y})
        (((convex_ball (0 : E) r).inter T.convex).inter
          (convex_halfSpace_gt ℓ.isLinear 0)) inter_subset_left
        (fun y hy => hy.2.ne') ?_ z ⟨hz, hpos⟩)
      refine ⟨(a / 2) • w, ⟨⟨haB hapos, hPT (P.smul_mem _ hwP)⟩, ?_⟩,
        P.smul_mem _ hwP⟩
      change 0 < ℓ ((a / 2) • w)
      simpa only [map_smul, smul_eq_mul, hℓw, mul_one] using half_pos ha
  apply eventually_nhdsWithin_iff.mpr
  have hφc : ContinuousAt φ x := hφ.isPiecewiseAffineOn.continuousOn.continuousAt
    (hW.mem_nhds hxW)
  have hnb : φ ⁻¹' ball (0 : E) r ∈ 𝓝 x :=
    hφc.preimage_mem_nhds (hφx.symm ▸ ball_mem_nhds (0 : E) hr)
  filter_upwards [hO.mem_nhds hxO, hnb] with y hyO hyball hyS
  have ho := hOO hyO
  have heq : ψ (φ y) = y := hφ.bijOn.invOn_invFunOn.1 ho.1
  simpa only [g, heq] using hle (φ y) ⟨hyball, ho.2.2.1.mp hyS⟩

theorem HasPLCurveCrossingOnAt.not_isLocalExtrOn_of_level
    {S A B U : Set E} {x : E} (hc : HasPLCurveCrossingOnAt S A B x)
    {f : E → ℝ} (hU : IsOpen U) (hxU : x ∈ U) (hf : ContinuousOn f (S ∩ U))
    (hlevel : ∀ y ∈ S ∩ U, f y = f x ↔ y ∈ B)
    (hopen : 𝓝 (f x) ≤ Filter.map f (𝓝[S] x)) : ¬ IsLocalExtrOn f A x := by
  rintro (hmin | hmax)
  · have hneg := hc.isLocalMaxOn_surface_of_level hU hxU hf.neg
      (fun y hy => by simpa only [Pi.neg_apply, neg_inj] using hlevel y hy) hmin.neg
    have hminS : IsLocalMinOn f S x := by
      simpa only [Pi.neg_apply, neg_neg] using hneg.neg
    exact hminS.not_nhds_le_map hopen
  · exact (hc.isLocalMaxOn_surface_of_level hU hxU hf hlevel hmax).not_nhds_le_map hopen

end DifferentialGeometry.Topology.PiecewiseLinear
