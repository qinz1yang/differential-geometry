/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BigonBoundaryCrossing
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnLocalInterior

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M]

theorem HasPLCurveCrossingOnAt.mem_closure_inter_cellInterior_in_chart
    {S A B D Db : Set M} {x : M} (c : OpenPartialHomeomorph M E3)
    (hxc : x ∈ c.source)
    (hc : HasPLCurveCrossingOnAt (c '' (S ∩ c.source))
      (c '' (A ∩ c.source)) (c '' (B ∩ c.source)) (c x))
    (hD : IsPLCellOn 2 D Db) (hDS : D ⊆ S)
    (hboundary : ∀ᶠ y in 𝓝 x, y ∈ Db ↔ y ∈ B) :
    x ∈ closure (A ∩ (D \ Db)) := by
  classical
  by_contra hxcl
  obtain ⟨U, V, φ, T, P, Q, hU, hV, hxU, hφ, hφx, hT, hP, hQ, hPT, hQT, hPQ,
    hlocal⟩ := hc
  let e := c.trans (hφ.toOpenPartialHomeomorph hU hV)
  have hxe : x ∈ e.source := ⟨hxc, hxU⟩
  have he0 : e x = 0 := hφx
  have hmem (Z : Set M) {y : M} (hy : y ∈ c.source) :
      y ∈ Z ↔ c y ∈ c '' (Z ∩ c.source) := by
    refine ⟨fun hyZ => ⟨y, ⟨hyZ, hy⟩, rfl⟩, ?_⟩
    rintro ⟨z, hz, hzy⟩
    exact c.injOn hz.2 hy hzy ▸ hz.1
  have hlocal : ∀ᶠ y in 𝓝 x,
      (y ∈ S ↔ e y ∈ T) ∧ (y ∈ A ↔ e y ∈ P) ∧ (y ∈ B ↔ e y ∈ Q) := by
    filter_upwards [(c.continuousAt hxc).tendsto.eventually hlocal,
      c.open_source.mem_nhds hxc] with y hy hyc
    exact ⟨(hmem S hyc).trans hy.1, (hmem A hyc).trans hy.2.1,
      (hmem B hyc).trans hy.2.2⟩
  have hxB : x ∈ B := (hlocal.self_of_nhds).2.2.mpr (he0 ▸ Q.zero_mem)
  have hxJ : x ∈ Db := hboundary.self_of_nhds.mpr hxB
  have hJD : Db ⊆ D := hD.boundary_subset
  have hsmall : ∀ᶠ y in 𝓝 x, y ∈ e.source ∧
      (y ∈ S ↔ e y ∈ T) ∧ (y ∈ A ↔ e y ∈ P) ∧ (y ∈ B ↔ e y ∈ Q) ∧
      (y ∈ Db ↔ y ∈ B) ∧
      y ∉ A ∩ (D \ Db) := by
    filter_upwards [e.open_source.mem_nhds hxe, hlocal, hboundary,
      isClosed_closure.isOpen_compl.mem_nhds hxcl] with y hyU hy hyJ hycl
    exact ⟨hyU, hy.1, hy.2.1, hy.2.2, hyJ, fun hyA => hycl (subset_closure hyA)⟩
  obtain ⟨O, hOO, hO, hxO⟩ := _root_.mem_nhds_iff.mp hsmall
  have hQne : Q ≠ ⊥ := by
    intro heq
    rw [heq, finrank_bot] at hQ
    omega
  obtain ⟨v, hvQ, hv0⟩ := Q.ne_bot_iff.mp hQne
  have hvP : v ∉ P := by
    intro hvP
    have hv : v ∈ (P ⊓ Q : Submodule ℝ E3) := ⟨hvP, hvQ⟩
    rw [hPQ] at hv
    exact hv0 hv
  obtain ⟨ℓ, hℓv, hPℓ⟩ := P.exists_le_ker_of_notMem hvP
  have hPK : P ≤ T ⊓ LinearMap.ker ℓ := le_inf hPT hPℓ
  have hKT : T ⊓ LinearMap.ker ℓ < T := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro heq
    have hv : v ∈ T ⊓ LinearMap.ker ℓ := heq.symm ▸ hQT hvQ
    exact hℓv hv.2
  have hker : P = T ⊓ LinearMap.ker ℓ := by
    apply Submodule.eq_of_le_of_finrank_eq hPK
    have hlo := Submodule.finrank_mono hPK
    have hhi := Submodule.finrank_lt_finrank_of_lt hKT
    omega
  let w := (ℓ v)⁻¹ • v
  have hwQ : w ∈ Q := Q.smul_mem _ hvQ
  have hℓw : ℓ w = 1 := by simp [w, hℓv]
  let f : M → ℝ := fun y => ℓ (e y)
  have hfc : ContinuousOn f e.source := ℓ.continuous_of_finiteDimensional.comp_continuousOn
    e.continuousOn
  obtain ⟨L, hLO, hLD, hLconn, O', hO', hxO', hO'L⟩ :=
    hD.exists_preconnected_sdiff_boundary (hJD hxJ) (hO.mem_nhds hxO)
  have hLU : L ⊆ e.source := fun y hy => (hOO (hLO hy)).1
  have hfne : ∀ y ∈ L, f y ≠ 0 := by
    intro y hy hfy
    have hyO := hOO (hLO hy)
    have hyT : e y ∈ T := hyO.2.1.mp (hDS (hLD hy).1)
    have hyP : e y ∈ P := hker.symm ▸ ⟨hyT, hfy⟩
    exact hyO.2.2.2.2.2 ⟨hyO.2.2.1.mpr hyP, hLD hy⟩
  have hside : (∀ y ∈ L, f y < 0) ∨ (∀ y ∈ L, 0 < f y) := by
    have hconn := hLconn.image f (hfc.mono hLU)
    have hcover : f '' L ⊆ Iio 0 ∪ Ioi 0 := by
      rintro _ ⟨y, hy, rfl⟩
      exact (lt_or_gt_of_ne (hfne y hy)).elim Or.inl Or.inr
    have hdisj : Disjoint (Iio (0 : ℝ)) (Ioi 0) := disjoint_left.mpr fun z hz hz' =>
      (not_lt_of_ge (show 0 ≤ z from le_of_lt hz')) hz
    exact (hconn.subset_or_subset isOpen_Iio isOpen_Ioi hdisj hcover).imp
      (fun h y hy => h ⟨y, hy, rfl⟩) (fun h y hy => h ⟨y, hy, rfl⟩)
  have hDcl : O' ∩ D ⊆ closure L := by
    intro y hy
    have hycl : y ∈ closure (O' ∩ (D \ Db)) :=
      hO'.inter_closure ⟨hy.1, hD.closure_sdiff_boundary.symm ▸ hy.2⟩
    exact closure_mono hO'L hycl
  let ψ := e.symm
  have h0V : (0 : E3) ∈ e.target := he0 ▸ e.map_source hxe
  have hψ0 : ψ 0 = x := by
    rw [← he0]
    exact e.left_inv hxe
  have hψc : ContinuousAt ψ 0 := e.symm.continuousAt h0V
  let g : ℝ → M := fun t => ψ (t • w)
  have hg0 : g 0 = x := by simp [g, hψ0]
  have hgc : ContinuousAt g 0 := by
    have hψc' : ContinuousAt ψ ((0 : ℝ) • w) := by simpa using hψc
    exact ContinuousAt.comp (f := fun t : ℝ => t • w) (g := ψ) hψc'
      (show ContinuousAt (fun t : ℝ => t • w) 0 by fun_prop)
  have hgn : ∀ᶠ t in 𝓝 (0 : ℝ), t • w ∈ e.target ∧ g t ∈ O ∩ O' := by
    have h1 : ∀ᶠ t in 𝓝 (0 : ℝ), t • w ∈ e.target :=
      (by fun_prop : Continuous (fun t : ℝ => t • w)).continuousAt.preimage_mem_nhds
        (by simpa using e.open_target.mem_nhds h0V)
    exact h1.and (hgc.preimage_mem_nhds (hg0.symm ▸ (hO.inter hO').mem_nhds ⟨hxO, hxO'⟩))
  obtain ⟨δ, hδ, hδg⟩ := Metric.mem_nhds_iff.mp hgn
  have hgt : ∀ t ∈ ball (0 : ℝ) δ, g t ∈ e.source ∩ closure L ∧ f (g t) = t := by
    intro t ht
    obtain ⟨htV, htO, htO'⟩ := hδg ht
    have hφg : e (g t) = t • w := e.right_inv htV
    have hdata := hOO htO
    have htB : g t ∈ B := hdata.2.2.2.1.mpr (hφg ▸ Q.smul_mem t hwQ)
    have htD : g t ∈ D := hJD (hdata.2.2.2.2.1.mpr htB)
    refine ⟨⟨hdata.1, hDcl ⟨htO', htD⟩⟩, ?_⟩
    change ℓ (e (g t)) = t
    rw [hφg, map_smul, smul_eq_mul, hℓw, mul_one]
  have hpos : δ / 2 ∈ ball (0 : ℝ) δ := by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
    linarith
  have hneg : -(δ / 2) ∈ ball (0 : ℝ) δ := by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_neg, abs_of_pos (half_pos hδ)]
    linarith
  have hclosure : ∀ y ∈ e.source ∩ closure L, f y ∈ closure (f '' L) := by
    intro y hy
    exact (hfc.continuousAt (e.open_source.mem_nhds hy.1)).continuousWithinAt.mem_closure_image hy.2
  rcases hside with hside | hside
  · have hle : f (g (δ / 2)) ≤ 0 := closure_minimal
      (by rintro z ⟨y, hy, rfl⟩; exact (hside y hy).le) isClosed_Iic
      (hclosure _ (hgt _ hpos).1)
    rw [(hgt _ hpos).2] at hle
    linarith
  · have hle : 0 ≤ f (g (-(δ / 2))) := closure_minimal
      (by rintro z ⟨y, hy, rfl⟩; exact (hside y hy).le) isClosed_Ici
      (hclosure _ (hgt _ hneg).1)
    rw [(hgt _ hneg).2] at hle
    linarith

end DifferentialGeometry.Topology.PiecewiseLinear
