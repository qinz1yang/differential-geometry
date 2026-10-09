/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.FundamentalGroup.Circle
import DifferentialGeometry.Topology.FundamentalGroup.Retraction
import DifferentialGeometry.Topology.FundamentalGroup.SimplyConnected
import DifferentialGeometry.Topology.Homotopy.ConvexProduct
import DifferentialGeometry.Topology.PiecewiseLinear.CoveringLift
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsAnnularSplitBall
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsGeneralPositionSolidTorusRelative
import DifferentialGeometry.Topology.PiecewiseLinear.OrientableSurfaceEulerParity
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame
import DifferentialGeometry.Topology.PiecewiseLinear.SeparatingPolygonDisk
import DifferentialGeometry.Topology.PiecewiseLinear.SphereDisk
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskPair

open Set Topology
open scoped ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Transfer

theorem surjective_fundamentalGroup_map_of_homotopy {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {F₀ F₁ : C(X, Y)} (H : F₀.Homotopy F₁) (x : X)
    (h : Function.Surjective (FundamentalGroup.map F₁ x)) :
    Function.Surjective (FundamentalGroup.map F₀ x) := by
  intro γ
  obtain ⟨ℓ, hℓ⟩ := h (FundamentalGroup.fromPath
    (((Path.Homotopic.Quotient.mk (H.evalAt x)).symm.trans (FundamentalGroup.toPath γ)).trans
      (Path.Homotopic.Quotient.mk (H.evalAt x))))
  refine ⟨ℓ, ?_⟩
  induction ℓ using Path.Homotopic.Quotient.ind with
  | mk ℓ =>
  have hsq : Path.Homotopic.Quotient.mk ((ℓ.map F₀.continuous).trans (H.evalAt x)) =
      Path.Homotopic.Quotient.mk ((H.evalAt x).trans (ℓ.map F₁.continuous)) :=
    Path.Homotopic.Quotient.eq.mpr (Path.Homotopic.map_trans_evalAt H ℓ)
  rw [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_trans] at hsq
  change Path.Homotopic.Quotient.mk (ℓ.map F₁.continuous) = _ at hℓ
  change Path.Homotopic.Quotient.mk (ℓ.map F₀.continuous) = γ
  rw [hℓ, ← Path.Homotopic.Quotient.trans_assoc, ← Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.refl_trans] at hsq
  calc Path.Homotopic.Quotient.mk (ℓ.map F₀.continuous)
      = ((Path.Homotopic.Quotient.mk (ℓ.map F₀.continuous)).trans
          (Path.Homotopic.Quotient.mk (H.evalAt x))).trans
          (Path.Homotopic.Quotient.mk (H.evalAt x)).symm := by
        rw [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
          Path.Homotopic.Quotient.trans_refl]
    _ = γ := by
        rw [hsq, Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
          Path.Homotopic.Quotient.trans_refl]

theorem carriesFundamentalGroupOnto_image_zero_of_image_one {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] {C : Set X} (hC : IsCompact C) {T : Set Y}
    {f : X × ℝ → Y} (hf : ContinuousOn f (C ×ˢ Icc 0 1)) (hfT : MapsTo f (C ×ˢ Icc 0 1) T)
    (hinj : InjOn (fun x => f (x, 1)) C)
    (hcarry : CarriesFundamentalGroupOnto ((fun x => f (x, 1)) '' C) T) :
    CarriesFundamentalGroupOnto ((fun x => f (x, 0)) '' C) T := by
  have hmem : ∀ c ∈ C, ∀ t ∈ Icc (0 : ℝ) 1, f (c, t) ∈ T := fun c hc t ht => hfT ⟨hc, ht⟩
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.mpr zero_le_one
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.mpr zero_le_one
  have hE₀T : (fun x => f (x, 0)) '' C ⊆ T := by
    rintro _ ⟨c, hc, rfl⟩
    exact hmem c hc 0 h0
  have hE₁T : (fun x => f (x, 1)) '' C ⊆ T := hcarry.1
  refine ⟨hE₀T, fun hsub b => ?_⟩
  obtain ⟨_, c₀, hc₀, rfl⟩ := b
  have hcontT : ∀ t ∈ Icc (0 : ℝ) 1, Continuous fun c : C => f ((c : X), t) := fun t ht =>
    hf.comp_continuous (continuous_subtype_val.prodMk continuous_const) fun c => ⟨c.2, ht⟩
  have hcontH : Continuous fun p : unitInterval × C =>
      (⟨f ((p.2 : X), (p.1 : ℝ)), hmem p.2 p.2.2 p.1 p.1.2⟩ : T) :=
    (hf.comp_continuous ((continuous_subtype_val.comp continuous_snd).prodMk
      (continuous_subtype_val.comp continuous_fst)) fun p => ⟨p.2.2, p.1.2⟩).subtype_mk _
  let F₀ : C(C, T) := ⟨fun c => ⟨f ((c : X), 0), hmem c c.2 0 h0⟩, (hcontT 0 h0).subtype_mk _⟩
  let F₁ : C(C, T) := ⟨fun c => ⟨f ((c : X), 1), hmem c c.2 1 h1⟩, (hcontT 1 h1).subtype_mk _⟩
  let H : F₀.Homotopy F₁ :=
    { toFun := fun p => ⟨f ((p.2 : X), (p.1 : ℝ)), hmem p.2 p.2.2 p.1 p.1.2⟩
      continuous_toFun := hcontH
      map_zero_left := fun _ => rfl
      map_one_left := fun _ => rfl }
  let c₀' : C := ⟨c₀, hc₀⟩
  let _ : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let k₁ : C → (fun x => f (x, 1)) '' C := fun c => ⟨f ((c : X), 1), c, c.2, rfl⟩
  have hk₁ : Continuous k₁ := (hcontT 1 h1).subtype_mk _
  have hk₁bij : Function.Bijective k₁ := by
    refine ⟨fun a b hab => Subtype.ext (hinj a.2 b.2 (congrArg Subtype.val hab)), ?_⟩
    rintro ⟨_, c, hc, rfl⟩
    exact ⟨⟨c, hc⟩, rfl⟩
  let e : C ≃ₜ (fun x => f (x, 1)) '' C :=
    hk₁.homeoOfEquivCompactToT2 (f := Equiv.ofBijective k₁ hk₁bij)
  let ec : C(C, (fun x => f (x, 1)) '' C) := ⟨e, e.continuous⟩
  let i₁ : C((fun x => f (x, 1)) '' C, T) := ⟨inclusion hE₁T, continuous_inclusion hE₁T⟩
  have hF₁ : F₁ = i₁.comp ec := ContinuousMap.ext fun _ => rfl
  have hsurj₁ : Function.Surjective (FundamentalGroup.map F₁ c₀') := by
    rw [hF₁, fundamentalGroup_map_continuousMap_comp, MonoidHom.coe_comp]
    exact (hcarry.2 hE₁T (ec c₀')).comp
      (bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse e.symm.toHomotopyEquiv ec
        (fun c => e.symm_apply_apply c) c₀').2
  have hsurj₀ := surjective_fundamentalGroup_map_of_homotopy H c₀' hsurj₁
  let g₀ : C(C, (fun x => f (x, 0)) '' C) :=
    ⟨fun c => ⟨f ((c : X), 0), c, c.2, rfl⟩, (hcontT 0 h0).subtype_mk _⟩
  intro γ
  obtain ⟨ℓ, hℓ⟩ := hsurj₀ γ
  refine ⟨FundamentalGroup.map g₀ c₀' ℓ, ?_⟩
  rw [← hℓ]
  exact (DFunLike.congr_fun (fundamentalGroup_map_continuousMap_comp g₀
    (⟨inclusion hsub, continuous_inclusion hsub⟩ : C((fun x => f (x, 0)) '' C, T)) c₀') ℓ).symm

end Transfer

section SolidTorus

theorem IsTopologicalSolidTorus.isPathConnected {E : Type*} [TopologicalSpace E] {S : Set E}
    (hS : IsTopologicalSolidTorus S) : IsPathConnected S := by
  obtain ⟨φ⟩ := hS
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    rw [← Module.finrank_eq_rank', finrank_euclideanSpace_fin]
    norm_num
  have hD : PathConnectedSpace (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).isPathConnected
        ⟨0, Metric.mem_closedBall_self zero_le_one⟩)
  have hC : PathConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere hrank 0 zero_le_one)
  let _ : PathConnectedSpace S := φ.symm.surjective.pathConnectedSpace φ.symm.continuous
  exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance

theorem IsTopologicalSolidTorus.not_simplyConnectedSpace {E : Type*} [TopologicalSpace E]
    {S : Set E} (hS : IsTopologicalSolidTorus S) : ¬ SimplyConnectedSpace S := by
  intro hsc
  obtain ⟨φ⟩ := hS
  let p : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    ⟨0, Metric.mem_closedBall_self zero_le_one⟩
  let e : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₕ S :=
    ((DifferentialGeometry.HomotopyEquiv.productConvex
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
      (convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) p).symm.trans
      (Homeomorph.prodComm _ _).toHomotopyEquiv).trans φ.symm.toHomotopyEquiv
  have hC : SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    e.simplyConnectedSpace
  let c : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ Circle :=
    (Complex.orthonormalBasisOneI.repr.toHomeomorph.subtype fun z => by
      change z ∈ Metric.sphere (0 : ℂ) 1 ↔
        Complex.orthonormalBasisOneI.repr z ∈ Metric.sphere 0 1
      rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm,
        Complex.orthonormalBasisOneI.repr.norm_map]).symm
  have hcirc : SimplyConnectedSpace Circle := c.symm.toHomotopyEquiv.simplyConnectedSpace
  let g := fundamentalGroupCircleEquivInt
  have hg := (simplyConnectedSpace_iff_fundamentalGroup_eq_one (1 : Circle)).mp hcirc
    (g.symm (Multiplicative.ofAdd (1 : ℤ)))
  have he := congrArg (fun x => Multiplicative.toAdd (g x)) hg
  simp only [MulEquiv.apply_symm_apply, map_one, toAdd_ofAdd, toAdd_one] at he
  exact one_ne_zero he

theorem IsTopologicalSolidTorus.not_carriesFundamentalGroupOnto_of_subset_isPLBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S D K : Set E} {n : ℕ} (hS : IsTopologicalSolidTorus S) (hD : IsPLBall n D)
    (hDS : D ⊆ S) (hK : K.Nonempty) (hKD : K ⊆ D) : ¬ CarriesFundamentalGroupOnto K S := by
  rintro ⟨hKS, hcarry⟩
  obtain ⟨b, hb⟩ := hK
  have hsurj := hcarry hKS ⟨b, hb⟩
  have hDsc : SimplyConnectedSpace D := hD.simplyConnectedSpace
  let _ : PathConnectedSpace S := isPathConnected_iff_pathConnectedSpace.mp hS.isPathConnected
  apply hS.not_simplyConnectedSpace
  refine (simplyConnectedSpace_iff_fundamentalGroup_eq_one (⟨b, hKS hb⟩ : S)).mpr fun g => ?_
  obtain ⟨a, rfl⟩ := hsurj g
  let iKD : C(K, D) := ⟨inclusion hKD, continuous_inclusion hKD⟩
  let iDS : C(D, S) := ⟨inclusion hDS, continuous_inclusion hDS⟩
  have hcomp := DFunLike.congr_fun (fundamentalGroup_map_continuousMap_comp iKD iDS ⟨b, hb⟩) a
  rw [MonoidHom.comp_apply, Subsingleton.elim (FundamentalGroup.map iKD _ a) 1, map_one] at hcomp
  exact hcomp

end SolidTorus

section Prism

open Classical in
private theorem isPLSphere_prism_frontier :
    IsPLSphere 2 (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ) ∪
      stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
  have hΔ : IsPLBall 2 (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) := isPLBall_stdSimplex 2
  have hΔpoly : IsPolyhedron (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) := hΔ.isPolyhedron
  obtain ⟨Kd, hKdfin, hKdspace⟩ := hΔpoly.exists_simplicialComplex
  let _ : Finite Kd.faces := hKdfin.to_subtype
  have hKd : IsPLBall 2 Kd.space := hKdspace ▸ hΔ
  have hid : IsPLHomeomorphOn id (Convexity.StdSimplex.coordinateSet ℝ (Fin (1 + 2))) Kd.space := by
    rw [hKdspace]
    exact isPLHomeomorphOn_id_of_isHPolytope (isHPolytope_stdSimplex _)
  have hprism := isPLBall_three_prod hΔ (isPLBall_Icc (zero_lt_one' ℝ))
  obtain ⟨A, hAfin, hAspace⟩ := hprism.isPolyhedron.exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  have hA : IsPLBall 3 A.space := hAspace ▸ hprism
  have hAbd : (boundaryComplex 3 A).space = Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ {0, 1} ∪
      stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 := by
    have h := boundaryComplex_space_prism Kd hKd (zero_lt_one' ℝ) A (by rw [hAspace, hKdspace])
    have h2 := boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex (n := 1) Kd hid
    rw [image_id, simplexBoundary_stdVertices_space] at h2
    rw [← hKdspace, ← h2]
    convert h using 5
  have hS : IsPLSphere 2 (boundaryComplex 3 A).space := by
    convert isPLSphere_boundaryComplex_space_of_isPLBall A hA
  rwa [hAbd] at hS

theorem IsPLSphere.exists_disk_or_annulus_of_subset_prism_lateral
    {K : Set ((Fin 3 → ℝ) × ℝ)} (hK : IsPLSphere 1 K)
    (hKA : K ⊆ stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) :
    (∃ (D : Set ((Fin 3 → ℝ) × ℝ)) (r : (Fin 3 → ℝ) → (Fin 3 → ℝ) × ℝ),
        IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧
        D ⊆ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 ∧ r '' stdSimplexBoundary 2 = K) ∨
      ∃ ψ : (Fin 3 → ℝ) × ℝ → (Fin 3 → ℝ) × ℝ,
        IsPLHomeomorphOn ψ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
          (ψ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
        ψ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 ∧
        (∀ x ∈ stdSimplexBoundary 2, ψ (x, 0) = (x, 0)) ∧
        ψ '' (stdSimplexBoundary 2 ×ˢ {1}) = K := by
  have hSig := isPLSphere_prism_frontier
  have hΔ : IsPLBall 2 (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) := isPLBall_stdSimplex 2
  have hΔpoly : IsPolyhedron (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) := hΔ.isPolyhedron
  let _ : Finite (simplexBoundary (stdVertices 1) (stdVertices_affineIndependent 1)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  have hBpoly : IsPolyhedron (stdSimplexBoundary 2) := by
    rw [← simplexBoundary_stdVertices_space 1]
    exact isPolyhedron_space _
  have hA₀poly : IsPolyhedron (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) :=
    hBpoly.prod isHPolytope_Icc.isPolyhedron
  have hA₀Sph : stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 ⊆
      Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ) ∪ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 :=
    subset_union_right
  have hKA₀ : K ⊆ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 :=
    fun y hy => ⟨(hKA hy).1, Ioo_subset_Icc_self (hKA hy).2⟩
  have hKSph := hKA₀.trans hA₀Sph
  have hι₀ := hΔpoly.isPLHomeomorphOn_prod_const (0 : ℝ)
  have hι₁ := hΔpoly.isPLHomeomorphOn_prod_const (1 : ℝ)
  have hE₀ : IsPLBall 2 (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0} : Set ℝ)) := hΔ.of_isPLHomeomorphOn hι₀
  have hE₁ : IsPLBall 2 (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({1} : Set ℝ)) := hΔ.of_isPLHomeomorphOn hι₁
  have hE₀Sph : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0} : Set ℝ) ⊆
      Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ) ∪ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 :=
    fun y hy => Or.inl ⟨hy.1, Or.inl hy.2⟩
  have hE₁Sph : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({1} : Set ℝ) ⊆
      Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ) ∪ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 :=
    fun y hy => Or.inl ⟨hy.1, Or.inr hy.2⟩
  have hE₀K : Disjoint (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0} : Set ℝ)) K := by
    rw [disjoint_left]
    intro y hy hyK
    have h := (hKA hyK).2.1
    rw [mem_singleton_iff.mp hy.2] at h
    exact lt_irrefl _ h
  have hE₁K : Disjoint (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({1} : Set ℝ)) K := by
    rw [disjoint_left]
    intro y hy hyK
    have h := (hKA hyK).2.2
    rw [mem_singleton_iff.mp hy.2] at h
    exact lt_irrefl _ h
  have hE₀E₁ : Disjoint (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0} : Set ℝ))
      (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({1} : Set ℝ)) := by
    rw [disjoint_left]
    intro y hy0 hy1
    have h := (mem_singleton_iff.mp hy0.2).symm.trans (mem_singleton_iff.mp hy1.2)
    exact zero_ne_one h
  obtain ⟨D₁, D₂, hU, hI, f₁, f₂, hf₁, hf₂, hf₁b, hf₂b⟩ :=
    exists_disk_decomposition_of_isPLSphere_one_subset_two hSig hK hKSph
  have hside : ∀ C, C ⊆ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ) ∪
      stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 → IsPreconnected C → Disjoint C K →
        C ⊆ D₁ ∨ C ⊆ D₂ := by
    intro C hCSph hC hCK
    refine isPreconnected_iff_subset_of_disjoint_closed.mp hC D₁ D₂
      (IsPLBall.isPolyhedron ⟨f₁, hf₁⟩).isClosed (IsPLBall.isPolyhedron ⟨f₂, hf₂⟩).isClosed
      (by rw [hU]; exact hCSph) ?_
    rw [hI]
    exact hCK.inter_eq
  have hdisk : ∀ D D' : Set ((Fin 3 → ℝ) × ℝ), D ∪ D' = Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ) ∪
      stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 → D ∩ D' = K →
      Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0} : Set ℝ) ⊆ D' → Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({1} : Set ℝ) ⊆ D' →
        D ⊆ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 := by
    intro D D' hDD' hDI h0 h1 y hy
    have hySph : y ∈ D ∪ D' := Or.inl hy
    rw [hDD'] at hySph
    rcases hySph with ⟨hyΔ, hy01⟩ | hyA
    · have hyD' : y ∈ D' := by
        rcases hy01 with hy0 | hy1
        · exact h0 ⟨hyΔ, hy0⟩
        · exact h1 ⟨hyΔ, hy1⟩
      have hyK : y ∈ D ∩ D' := ⟨hy, hyD'⟩
      rw [hDI] at hyK
      exact hKA₀ hyK
    · exact hyA
  have hann : ∀ (D D' : Set ((Fin 3 → ℝ) × ℝ)) (f' : (Fin 3 → ℝ) → (Fin 3 → ℝ) × ℝ),
      IsPLHomeomorphOn f' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D' → f' '' stdSimplexBoundary 2 = K →
      D ∪ D' = Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ) ∪
        stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 → D ∩ D' = K →
      Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0} : Set ℝ) ⊆ D → Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({1} : Set ℝ) ⊆ D' →
      ∃ ψ : (Fin 3 → ℝ) × ℝ → (Fin 3 → ℝ) × ℝ,
        IsPLHomeomorphOn ψ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
          (ψ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
        ψ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 ∧
        (∀ x ∈ stdSimplexBoundary 2, ψ (x, 0) = (x, 0)) ∧
        ψ '' (stdSimplexBoundary 2 ×ˢ {1}) = K := by
    intro D D' f' hf' hf'b hDD' hDI h0 h1
    have hD'Sph : D' ⊆ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ) ∪
        stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 := by
      rw [← hDD']
      exact subset_union_right
    have hdis0 : Disjoint (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0} : Set ℝ)) D' := by
      rw [disjoint_left]
      intro y hy0 hyD'
      have hyK : y ∈ D ∩ D' := ⟨h0 hy0, hyD'⟩
      rw [hDI] at hyK
      exact disjoint_left.mp hE₀K hy0 hyK
    obtain ⟨Φ, hΦ, hΦid, hΦD'⟩ := exists_isPLHomeomorphOn_map_disk_pair_eqOn_disk hSig hSig hE₀
      hE₀Sph ⟨f', hf'⟩ hD'Sph hdis0 hE₁ hE₁Sph hE₀E₁ hE₀.isPolyhedron.isPLHomeomorphOn_id hE₀Sph
    have hΦD'pl : IsPLHomeomorphOn Φ D' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({1} : Set ℝ)) := by
      have h := hΦ.restrict (IsPLBall.isPolyhedron ⟨f', hf'⟩) hD'Sph
      rwa [hΦD'] at h
    have hrim : Φ '' K = stdSimplexBoundary 2 ×ˢ ({1} : Set ℝ) := by
      have h := IsPLHomeomorphOn.image_image_stdSimplexBoundary hf' hι₁ hΦD'pl
      rw [hf'b] at h
      rw [h, prod_singleton]
    have hψ : IsPLHomeomorphOn (Function.invFunOn Φ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ) ∪
        stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ) ∪
        stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ) ∪
        stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := hΦ.symm
    refine ⟨_, hψ.restrict hA₀poly hA₀Sph, ?_, fun x hx => ?_, ?_⟩
    · rintro _ ⟨y, hyA, rfl⟩
      have hySph := hA₀Sph hyA
      have hxSph := hψ.bijOn.mapsTo hySph
      have hΦx := hΦ.bijOn.invOn_invFunOn.2 hySph
      by_cases hxD' : Function.invFunOn Φ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ) ∪
          stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) y ∈ D'
      · have hyE₁ : y ∈ Φ '' D' := ⟨_, hxD', hΦx⟩
        rw [hΦD'] at hyE₁
        have hyB : y ∈ stdSimplexBoundary 2 ×ˢ ({1} : Set ℝ) := ⟨hyA.1, hyE₁.2⟩
        rw [← hrim] at hyB
        obtain ⟨x', hx'K, hx'y⟩ := hyB
        have hx' := hΦ.bijOn.injOn (hKSph hx'K) hxSph (hx'y.trans hΦx.symm)
        rw [← hx']
        exact hKA₀ hx'K
      · rcases hxSph with ⟨hxΔ, hx01⟩ | hxA
        · rcases hx01 with hx0 | hx1
          · have hfix := hΦid (show _ ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0} : Set ℝ) from ⟨hxΔ, hx0⟩)
            rw [id_eq, hΦx] at hfix
            rw [← hfix]
            exact hyA
          · exact (hxD' (h1 ⟨hxΔ, hx1⟩)).elim
        · exact hxA
    · have hxE₀ : (x, (0 : ℝ)) ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0} : Set ℝ) := ⟨hx.1, rfl⟩
      have hfix := hΦid hxE₀
      calc Function.invFunOn Φ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ) ∪
            stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) (x, 0)
          = Function.invFunOn Φ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ) ∪
            stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) (Φ (x, 0)) := by rw [hfix, id_eq]
        _ = (x, 0) := hΦ.bijOn.invOn_invFunOn.1 (hE₀Sph hxE₀)
    · rw [← hrim]
      exact hΦ.bijOn.injOn.invFunOn_image hKSph
  rcases hside _ hE₀Sph hE₀.isConnected.isPreconnected hE₀K with h0 | h0 <;>
    rcases hside _ hE₁Sph hE₁.isConnected.isPreconnected hE₁K with h1 | h1
  · exact Or.inl ⟨D₂, f₂, hf₂, hdisk D₂ D₁ (by rw [union_comm]; exact hU)
      (by rw [inter_comm]; exact hI) h0 h1, hf₂b⟩
  · exact Or.inr (hann D₁ D₂ f₂ hf₂ hf₂b hU hI h0 h1)
  · exact Or.inr (hann D₂ D₁ f₁ hf₁ hf₁b (by rw [union_comm]; exact hU)
      (by rw [inter_comm]; exact hI) h0 h1)
  · exact Or.inl ⟨D₁, f₁, hf₁, hdisk D₁ D₂ hU hI h0 h1, hf₁b⟩

end Prism

section BoundaryTorus

open Classical in
theorem IsCombinatorialSolidTorus.carriesFundamentalGroupOnto_of_isPreconnected_sdiff
    {S K G : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsCombinatorialSolidTorus S)
    (hK : IsPLSphere 1 K) (hKS : K ⊆ frontier S) (hKgen : CarriesFundamentalGroupOnto K S)
    (hG : IsPLSphere 1 G) (hGS : G ⊆ frontier S) (hGK : Disjoint G K)
    (hnonsep : IsPreconnected (frontier S \ G)) : CarriesFundamentalGroupOnto G S := by
  have hT : IsPLTorus (frontier S) := hS.isPLTorus_frontier
  have hTS : frontier S ⊆ S := hS.isPolyhedron.isClosed.frontier_subset
  obtain ⟨L, hLfin, hL, hLc, hLT⟩ := hT.exists_combinatorial_triangulation
  let _ : Finite L.faces := hLfin.to_subtype
  have hLo := hL.isOrientable_euclidean_three L hLc
  have hβ := hT.bettiOne_le_two
  rw [← hLT] at hβ
  have hχ := hL.eulerChar_eq_two_sub_bettiOne_of_isOrientable L hLc hLo
  have hGL : G ⊆ L.space := by
    rw [hLT]
    exact hGS
  have hnonsep' : IsPreconnected (L.space \ G) := by
    rw [hLT]
    exact hnonsep
  have hU : L.space \ K ∈ 𝓝ˢ[L.space] G :=
    mem_nhdsSetWithin.mpr ⟨Kᶜ, hK.isPolyhedron.isClosed.isOpen_compl,
      fun x hx => disjoint_left.mp hGK hx, fun x hx => ⟨hx.2, hx.1⟩⟩
  obtain ⟨R, hRfin, hR, -, hRc, hRχ, W, ρ, -, hWL, hWU, -, hρ, hzero, -, -, hRbd, -, hcover,
      hGm, hGp, hdis⟩ := hL.exists_connected_annulus_complement L hLo hG hGL hnonsep' hU
  let _ : Finite R.faces := hRfin.to_subtype
  have hRbd' := hRbd.trans (show ρ '' (G ×ˢ {(-1 : ℝ), 1}) =
      ρ '' (G ×ˢ {(-1 : ℝ)}) ∪ ρ '' (G ×ˢ {(1 : ℝ)}) by
    rw [← singleton_union, prod_union, image_union])
  have hRχ0 : eulerChar R = 0 := by
    have hle := hR.eulerChar_nonpos_of_boundary_eq_union R hRc hGm hGp hdis hRbd'
    omega
  obtain ⟨h, hh, hh0, hh1⟩ :=
    hR.exists_isPLHomeomorphOn_annulus_of_eulerChar_eq_zero R hRc hRχ0 hGm hGp hdis hRbd'
  have hρW : ρ '' (G ×ˢ Icc (-1 : ℝ) 1) = W := hρ.image_eq
  have hGIcc : ∀ t ∈ ({(-1 : ℝ), 1} : Set ℝ), t ∈ Icc (-1 : ℝ) 1 := by
    rintro t (rfl | rfl)
    · exact ⟨le_rfl, by norm_num⟩
    · exact ⟨by norm_num, le_rfl⟩
  have hbdW : ρ '' (G ×ˢ {(-1 : ℝ)}) ∪ ρ '' (G ×ˢ {(1 : ℝ)}) ⊆ W := by
    rw [← hρW]
    rintro _ (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact ⟨y, ⟨hy.1, hGIcc _ (Or.inl hy.2)⟩, rfl⟩
    · exact ⟨y, ⟨hy.1, hGIcc _ (Or.inr hy.2)⟩, rfl⟩
  have hKW : Disjoint K W := by
    rw [disjoint_left]
    intro x hxK hxW
    exact (hWU hxW).2 hxK
  have hKL : K ⊆ L.space := by
    rw [hLT]
    exact hKS
  have hKR : K ⊆ R.space := by
    intro x hx
    have hxL := hKL hx
    rw [← hcover] at hxL
    exact hxL.resolve_left (disjoint_left.mp hKW hx)
  have hRS : R.space ⊆ S := by
    intro x hx
    have hxL : x ∈ L.space := by
      rw [← hcover]
      exact Or.inr hx
    rw [hLT] at hxL
    exact hTS hxL
  have hhs : IsPLHomeomorphOn (Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
      R.space (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := hh.symm
  have hK' : IsPLSphere 1 (Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' K) :=
    hK.of_isPLHomeomorphOn (hhs.restrict hK.isPolyhedron hKR)
  have hhK' : h '' (Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' K) = K :=
    LeftInvOn.image_image (hh.bijOn.invOn_invFunOn.2.mono hKR)
  have hK'A : Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' K ⊆
      stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have hyA := hhs.bijOn.mapsTo (hKR hx)
    have hhy := hh.bijOn.invOn_invFunOn.2 (hKR hx)
    refine ⟨hyA.1, lt_of_le_of_ne hyA.2.1 fun h0 => ?_, lt_of_le_of_ne hyA.2.2 fun h1 => ?_⟩
    · have hx0 : x ∈ h '' (stdSimplexBoundary 2 ×ˢ ({0} : Set ℝ)) := ⟨_, ⟨hyA.1, h0.symm⟩, hhy⟩
      rw [hh0] at hx0
      exact disjoint_left.mp hKW hx (hbdW (Or.inl hx0))
    · have hx1 : x ∈ h '' (stdSimplexBoundary 2 ×ˢ ({1} : Set ℝ)) := ⟨_, ⟨hyA.1, h1⟩, hhy⟩
      rw [hh1] at hx1
      exact disjoint_left.mp hKW hx (hbdW (Or.inr hx1))
  let _ : Finite (simplexBoundary (stdVertices 1) (stdVertices_affineIndependent 1)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  have hBcpt : IsCompact (stdSimplexBoundary 2) := by
    rw [← simplexBoundary_stdVertices_space 1]
    exact (isPolyhedron_space _).isCompact
  have hGmcarry : CarriesFundamentalGroupOnto (ρ '' (G ×ˢ {(-1 : ℝ)})) S := by
    rcases hK'.exists_disk_or_annulus_of_subset_prism_lateral hK'A with
      ⟨D, r, hr, hDA, hrb⟩ | ⟨ψ, hψ, hψA, hψ0, hψ1⟩
    · exfalso
      have hhD : IsPLHomeomorphOn h D (h '' D) :=
        hh.restrict (IsPLBall.isPolyhedron ⟨r, hr⟩) hDA
      refine hS.1.not_carriesFundamentalGroupOnto_of_subset_isPLBall
        (IsPLBall.of_isPLHomeomorphOn ⟨r, hr⟩ hhD) ?_ hK.nonempty ?_ hKgen
      · rintro _ ⟨y, hy, rfl⟩
        exact hRS (hh.bijOn.mapsTo (hDA hy))
      · rw [← hhK', ← hrb]
        exact image_mono (image_subset_iff.mpr fun x hx => hr.bijOn.mapsTo hx.1)
    · have hcont : ContinuousOn (fun p => h (ψ p)) (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) :=
        hh.isPiecewiseAffineOn.continuousOn.comp hψ.isPiecewiseAffineOn.continuousOn
          fun p hp => hψA ⟨p, hp, rfl⟩
      have hmaps : MapsTo (fun p => h (ψ p)) (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) S :=
        fun p hp => hRS (hh.bijOn.mapsTo (hψA ⟨p, hp, rfl⟩))
      have h1mem : ∀ x ∈ stdSimplexBoundary 2,
          (x, (1 : ℝ)) ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 :=
        fun x hx => ⟨hx, right_mem_Icc.mpr zero_le_one⟩
      have hinj : InjOn (fun x => h (ψ (x, 1))) (stdSimplexBoundary 2) := by
        intro a ha b hb hab
        have h1 := hh.bijOn.injOn (hψA ⟨_, h1mem a ha, rfl⟩) (hψA ⟨_, h1mem b hb, rfl⟩) hab
        have h2 := hψ.bijOn.injOn (h1mem a ha) (h1mem b hb) h1
        exact congrArg Prod.fst h2
      have himg1 : (fun x => h (ψ (x, 1))) '' stdSimplexBoundary 2 = K := by
        rw [← hhK', ← hψ1, prod_singleton, image_image, image_image]
      have himg0 : (fun x => h (ψ (x, 0))) '' stdSimplexBoundary 2 =
          ρ '' (G ×ˢ {(-1 : ℝ)}) := by
        rw [← hh0, prod_singleton, image_image]
        exact image_congr fun x hx => by rw [hψ0 x hx]
      have h := carriesFundamentalGroupOnto_image_zero_of_image_one hBcpt hcont hmaps hinj
        (Eq.subst (motive := fun X => CarriesFundamentalGroupOnto X S) himg1.symm hKgen)
      exact Eq.subst (motive := fun X => CarriesFundamentalGroupOnto X S) himg0 h
  have hGcpt : IsCompact G := hG.isPolyhedron.isCompact
  have hmemρ : ∀ p ∈ G ×ˢ Icc (0 : ℝ) 1, (p.1, -p.2) ∈ G ×ˢ Icc (-1 : ℝ) 1 := by
    rintro p ⟨hp1, hp2, hp3⟩
    exact ⟨hp1, by linarith, by linarith⟩
  have hcontρ : ContinuousOn (fun p : EuclideanSpace ℝ (Fin 3) × ℝ => ρ (p.1, -p.2))
      (G ×ˢ Icc (0 : ℝ) 1) :=
    hρ.isPiecewiseAffineOn.continuousOn.comp (continuous_fst.prodMk continuous_snd.neg).continuousOn
      hmemρ
  have hmapsρ : MapsTo (fun p : EuclideanSpace ℝ (Fin 3) × ℝ => ρ (p.1, -p.2))
      (G ×ˢ Icc (0 : ℝ) 1) S := by
    intro p hp
    have hpW := hρ.bijOn.mapsTo (hmemρ p hp)
    have hpL := hWL hpW
    rw [hLT] at hpL
    exact hTS hpL
  have hm1 : ∀ x ∈ G, (x, -(1 : ℝ)) ∈ G ×ˢ Icc (-1 : ℝ) 1 :=
    fun x hx => ⟨hx, le_rfl, by norm_num⟩
  have hinjρ : InjOn (fun x => ρ (x, -(1 : ℝ))) G := fun a ha b hb hab =>
    congrArg Prod.fst (hρ.bijOn.injOn (hm1 a ha) (hm1 b hb) hab)
  have himgρ1 : (fun x => ρ (x, -(1 : ℝ))) '' G = ρ '' (G ×ˢ {(-1 : ℝ)}) := by
    rw [prod_singleton, image_image]
  have himgρ0 : (fun x => ρ (x, -(0 : ℝ))) '' G = G := by
    rw [neg_zero]
    exact (image_congr fun x hx => hzero x hx).trans (image_id' G)
  have hfinal := carriesFundamentalGroupOnto_image_zero_of_image_one hGcpt hcontρ hmapsρ hinjρ
    (Eq.subst (motive := fun X => CarriesFundamentalGroupOnto X S) himgρ1.symm hGmcarry)
  exact Eq.subst (motive := fun X => CarriesFundamentalGroupOnto X S) himgρ0 hfinal

end BoundaryTorus

end DifferentialGeometry.Topology.PiecewiseLinear
