/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homology.FieldHurewiczOne
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRayEmbedding
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.EulerUnion
import DifferentialGeometry.Topology.PiecewiseLinear.HandleCount
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldCapping
import DifferentialGeometry.Topology.PiecewiseLinear.TorusOfOrientableEulerCharZero
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Hurewicz

variable {k X V : Type} [Field k] [TopologicalSpace X] [AddCommGroup V] [Module k V]

noncomputable def fundamentalGroupoidLoopValue {x : X}
    (φ : FundamentalGroup X x →* Multiplicative V) (r : ∀ z : X, Path x z) {a b : X}
    (γ : Path.Homotopic.Quotient a b) : V :=
  Multiplicative.toAdd (φ (FundamentalGroup.fromPath
    ((Path.Homotopic.Quotient.mk (r a)).trans
      (γ.trans (Path.Homotopic.Quotient.mk (r b)).symm))))

theorem fundamentalGroupoidLoopValue_trans {x : X}
    (φ : FundamentalGroup X x →* Multiplicative V) (r : ∀ z : X, Path x z) {a b c : X}
    (γ : Path.Homotopic.Quotient a b) (δ : Path.Homotopic.Quotient b c) :
    fundamentalGroupoidLoopValue φ r (γ.trans δ) =
      fundamentalGroupoidLoopValue φ r γ + fundamentalGroupoidLoopValue φ r δ := by
  have key : (Path.Homotopic.Quotient.mk (r a)).trans
      ((γ.trans δ).trans (Path.Homotopic.Quotient.mk (r c)).symm) =
      ((Path.Homotopic.Quotient.mk (r a)).trans
        (γ.trans (Path.Homotopic.Quotient.mk (r b)).symm)).trans
        ((Path.Homotopic.Quotient.mk (r b)).trans
          (δ.trans (Path.Homotopic.Quotient.mk (r c)).symm)) := by
    simp only [Path.Homotopic.Quotient.trans_assoc]
    rw [← Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.mk (r b)).symm,
      Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]
  unfold fundamentalGroupoidLoopValue
  rw [key, add_comm, ← toAdd_mul, ← map_mul]
  rfl

theorem fundamentalGroupoidLoopValue_cast {x : X}
    (φ : FundamentalGroup X x →* Multiplicative V) (r : ∀ z : X, Path x z) {a b a' b' : X}
    (γ : Path.Homotopic.Quotient a b) (ha : a' = a) (hb : b' = b) :
    fundamentalGroupoidLoopValue φ r (γ.cast ha hb) = fundamentalGroupoidLoopValue φ r γ := by
  subst ha hb
  rw [Path.Homotopic.Quotient.cast_rfl_rfl]

theorem fundamentalGroupoidLoopValue_mk_eq_of_forall_apply_eq {x : X}
    (φ : FundamentalGroup X x →* Multiplicative V) (r : ∀ z : X, Path x z) {a b a' b' : X}
    (p : Path a b) (q : Path a' b') (h : ∀ t, p t = q t) :
    fundamentalGroupoidLoopValue φ r (Path.Homotopic.Quotient.mk p) =
      fundamentalGroupoidLoopValue φ r (Path.Homotopic.Quotient.mk q) := by
  have ha : a = a' := by simpa using h 0
  have hb : b = b' := by simpa using h 1
  subst ha hb
  have hpq : p = q := Path.ext (funext h)
  rw [hpq]

theorem fundamentalGroupoidLoopValue_loop {x : X}
    (φ : FundamentalGroup X x →* Multiplicative V) (r : ∀ z : X, Path x z)
    (γ : Path.Homotopic.Quotient x x) :
    fundamentalGroupoidLoopValue φ r γ =
      Multiplicative.toAdd (φ (FundamentalGroup.fromPath γ)) := by
  have key : (FundamentalGroup.fromPath ((Path.Homotopic.Quotient.mk (r x)).trans
      (γ.trans (Path.Homotopic.Quotient.mk (r x)).symm)) : FundamentalGroup X x) =
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (r x)))⁻¹ *
        FundamentalGroup.fromPath γ *
          FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (r x)) := rfl
  unfold fundamentalGroupoidLoopValue
  rw [key]
  simp only [map_mul, map_inv, toAdd_mul, toAdd_inv]
  abel

theorem exists_linearMap_fieldHurewiczOne [PathConnectedSpace X] (x : X)
    (φ : FundamentalGroup X x →* Multiplicative V) :
    ∃ Φ : (fieldSingularChains (k := k) (X := X)).homology 1 →ₗ[k] V,
      ∀ a, Φ (Multiplicative.toAdd (fieldHurewiczOne (k := k) x a)) =
        Multiplicative.toAdd (φ a) := by
  let r : ∀ z : X, Path x z := fun z => PathConnectedSpace.somePath x z
  let f : integralSingularSimplex 1 X → V := fun σ =>
    fundamentalGroupoidLoopValue φ r (Path.Homotopic.Quotient.mk (integralSimplexPath σ))
  let Φ₀ : (fieldSingularChains (k := k) (X := X)).X 1 →ₗ[k] V :=
    (fieldSingularChainBasis (k := k) (X := X) 1).constr ℕ f
  have hΦ₀ : ∀ σ, Φ₀ (fieldSimplexChain (k := k) 1 σ) = f σ := fun σ => by
    rw [← fieldSingularChainBasis_apply]
    exact (fieldSingularChainBasis (k := k) (X := X) 1).constr_basis ℕ f σ
  have hface : ∀ τ : integralSingularSimplex 2 X,
      f ((TopCat.toSSet.obj (TopCat.of X)).δ 2 τ) + f ((TopCat.toSSet.obj (TopCat.of X)).δ 0 τ) =
        f ((TopCat.toSSet.obj (TopCat.of X)).δ 1 τ) := by
    intro τ
    let T : C(Convexity.StdSimplex ℝ (Fin 3), X) := integralSingularSimplexEquiv 2 X τ
    let g : Fin 3 → unitInterval → Convexity.StdSimplex ℝ (Fin 3) := fun i t =>
      Convexity.StdSimplex.map (Fin.succAbove i)
        (TopCat.stdSimplexHomeomorphI.{0}.symm (TopCat.I.homeomorph.{0}.symm t))
    have hg : ∀ i, Continuous (g i) := fun i => (Convexity.StdSimplex.continuous_map ℝ _).comp
      (TopCat.stdSimplexHomeomorphI.{0}.symm.continuous.comp
        TopCat.I.homeomorph.{0}.symm.continuous)
    let e : ∀ i, Path (g i 0) (g i 1) := fun i => ⟨⟨g i, hg i⟩, rfl, rfl⟩
    have hf : ∀ i, f ((TopCat.toSSet.obj (TopCat.of X)).δ i τ) =
        fundamentalGroupoidLoopValue φ r (Path.Homotopic.Quotient.mk ((e i).map T.continuous)) :=
      fun i => fundamentalGroupoidLoopValue_mk_eq_of_forall_apply_eq φ r _ _ fun _ => rfl
    have hg0 : ∀ i, g i 0 = Convexity.StdSimplex.single (Fin.succAbove i 0) := fun i => by
      change Convexity.StdSimplex.map _ (TopCat.stdSimplexHomeomorphI.{0}.symm 0) = _
      rw [TopCat.stdSimplexHomeomorphI_symm_zero.{0}, Convexity.StdSimplex.map_single]
    have hg1 : ∀ i, g i 1 = Convexity.StdSimplex.single (Fin.succAbove i 1) := fun i => by
      change Convexity.StdSimplex.map _ (TopCat.stdSimplexHomeomorphI.{0}.symm 1) = _
      rw [TopCat.stdSimplexHomeomorphI_symm_one.{0}, Convexity.StdSimplex.map_single]
    have h1 : g 2 1 = g 0 0 := by
      rw [hg1, hg0]
      rfl
    have h0 : g 2 0 = g 1 0 := by
      rw [hg0, hg0]
      rfl
    have h2 : g 0 1 = g 1 1 := by
      rw [hg1, hg1]
      rfl
    let _ : ContractibleSpace (Convexity.StdSimplex ℝ (Fin 3)) := inferInstance
    have hPQ := SimplyConnectedSpace.paths_homotopic ((e 2).trans ((e 0).cast h1 rfl))
      ((e 1).cast h0 h2)
    have hmap := Path.Homotopic.Quotient.eq.mpr (hPQ.map T)
    rw [hf 2, hf 0, hf 1,
      fundamentalGroupoidLoopValue_mk_eq_of_forall_apply_eq φ r ((e 0).map T.continuous)
        (((e 0).cast h1 rfl).map T.continuous) fun _ => rfl,
      ← fundamentalGroupoidLoopValue_trans, ← Path.Homotopic.Quotient.mk_trans,
      ← Path.map_trans, hmap]
    exact fundamentalGroupoidLoopValue_mk_eq_of_forall_apply_eq φ r _ _ fun _ => rfl
  have hbd : ∀ c, Φ₀ ((fieldSingularChains (k := k) (X := X)).d 2 1 c) = 0 := by
    have hzero : Φ₀.comp ((fieldSingularChains (k := k) (X := X)).d 2 1).hom = 0 := by
      apply (fieldSingularChainBasis (k := k) (X := X) 2).ext
      intro τ
      rw [fieldSingularChainBasis_apply, LinearMap.comp_apply, LinearMap.zero_apply]
      change Φ₀ ((fieldSingularChains (k := k) (X := X)).d 2 1
        (fieldSimplexChain (k := k) 2 τ)) = 0
      rw [fieldSimplexChain_boundary_two, map_add, map_sub, hΦ₀, hΦ₀, hΦ₀, ← hface τ]
      abel
    exact fun c => LinearMap.congr_fun hzero c
  let Φ₁ : fieldSingularCycles (k := k) (X := X) 0 →ₗ[k] V :=
    Φ₀.comp (fieldSingularCycles (k := k) (X := X) 0).subtype
  have hle : LinearMap.range (fieldSingularBoundaryToCycles (k := k) (X := X) 0) ≤
      LinearMap.ker Φ₁ := by
    rintro _ ⟨c, rfl⟩
    exact hbd c
  refine ⟨((LinearMap.range (fieldSingularBoundaryToCycles (k := k) (X := X) 0)).liftQ Φ₁
    hle).comp (fieldSingularHomologyCycleEquiv (k := k) (X := X) 0).toLinearMap, fun a => ?_⟩
  induction a using Path.Homotopic.Quotient.ind with
  | mk γ =>
    rw [LinearMap.comp_apply, fieldHurewiczOne_apply]
    change (LinearMap.range (fieldSingularBoundaryToCycles (k := k) (X := X) 0)).liftQ Φ₁ hle
      ((fieldSingularHomologyCycleEquiv (k := k) (X := X) 0)
        ((fieldSingularHomologyCycleEquiv (k := k) (X := X) 0).symm
          (Submodule.Quotient.mk (fieldLoopCycle (k := k) γ)))) = _
    rw [LinearEquiv.apply_symm_apply, Submodule.liftQ_apply]
    change Φ₀ (fieldSimplexChain (k := k) 1 (integralPathSimplex γ)) = _
    rw [hΦ₀]
    have hpt : ∀ t, integralSimplexPath (integralPathSimplex γ) t = γ t := by
      intro t
      have h := integralPathSimplex_apply γ (TopCat.stdSimplexHomeomorphI.{0}.symm
        (TopCat.I.homeomorph.{0}.symm t))
      refine h.trans (congrArg γ ?_)
      change Convexity.StdSimplex.homeomorphI (Convexity.StdSimplex.homeomorphI.symm
        (Homeomorph.ulift.{0, 0}.symm.symm (Homeomorph.ulift.{0, 0}.symm t))) = t
      rw [Homeomorph.symm_symm, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
    rw [show f (integralPathSimplex γ) = fundamentalGroupoidLoopValue φ r
      (Path.Homotopic.Quotient.mk γ) from
      fundamentalGroupoidLoopValue_mk_eq_of_forall_apply_eq φ r _ _ hpt,
      fundamentalGroupoidLoopValue_loop]

theorem finrank_fieldHomology_one_le_of_fundamentalGroup_map_bijective
    {S Y : Type} [TopologicalSpace S] [TopologicalSpace Y] [PathConnectedSpace S]
    [PathConnectedSpace Y] (f : C(S, Y)) (x : S)
    (hf : Function.Bijective (FundamentalGroup.map f x))
    [FiniteDimensional k ((fieldSingularChains (k := k) (X := Y)).homology 1)] :
    Module.finrank k ((fieldSingularChains (k := k) (X := S)).homology 1) ≤
      Module.finrank k ((fieldSingularChains (k := k) (X := Y)).homology 1) := by
  let e := MulEquiv.ofBijective (FundamentalGroup.map f x) hf
  obtain ⟨Φ, hΦ⟩ := exists_linearMap_fieldHurewiczOne (k := k) (f x)
    ((fieldHurewiczOne (k := k) x).comp e.symm.toMonoidHom)
  have hrange : LinearMap.range Φ = ⊤ := by
    apply top_unique
    rw [← fieldHurewiczOne_span_range (k := k) x, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    refine ⟨Multiplicative.toAdd (fieldHurewiczOne (k := k) (f x) (e a)), ?_⟩
    rw [hΦ]
    simp
  have h := LinearMap.finrank_range_le Φ
  rwa [hrange, finrank_top] at h

end Hurewicz

section Capping

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem IsPolyhedron.isPLHomeomorphOn_linearMap_image {P : Set E} (hP : IsPolyhedron P)
    (Λ : E →ₗ[ℝ] F) (hΛ : Function.Injective Λ) : IsPLHomeomorphOn Λ P (Λ '' P) :=
  isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hP
    ((isPiecewiseAffineOn_of_affine Λ.toAffineMap isOpen_univ).mono_of_isPolyhedron hP
      (subset_univ _)) hΛ.injOn.bijOn_image

theorem IsConnected.union_biUnion {X α : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsConnected s) (W : Finset α) {t : α → Set X} (ht : ∀ i ∈ W, IsConnected (t i))
    (hst : ∀ i ∈ W, (s ∩ t i).Nonempty) :
    IsConnected (s ∪ ⋃ i ∈ W, t i) := by
  classical
  induction W using Finset.induction_on with
  | empty =>
    have h : (⋃ i ∈ (∅ : Finset α), t i) = ∅ := by
      ext x
      simp
    rw [h, union_empty]
    exact hs
  | insert i W hi ih =>
    rw [Finset.set_biUnion_insert, ← union_assoc, union_comm s (t i), union_assoc,
      union_comm (t i)]
    have hW := ih (fun j hj => ht j (Finset.mem_insert_of_mem hj))
      (fun j hj => hst j (Finset.mem_insert_of_mem hj))
    obtain ⟨x, hx⟩ := hst i (Finset.mem_insert_self i W)
    exact IsConnected.union ⟨x, Or.inl hx.1, hx.2⟩ hW (ht i (Finset.mem_insert_self i W))

theorem IsPolyhedron.eulerChar_biUnion {α : Type*} (W : Finset α) {P : α → Set E}
    (hP : ∀ i ∈ W, IsPolyhedron (P i))
    (hdisj : ∀ i ∈ W, ∀ j ∈ W, i ≠ j → Disjoint (P i) (P j)) :
    IsPolyhedron (⋃ i ∈ W, P i) ∧ Homology.eulerChar ℚ (TopCat.of ↥(⋃ i ∈ W, P i)) =
      ∑ i ∈ W, Homology.eulerChar ℚ (TopCat.of ↥(P i)) := by
  classical
  induction W using Finset.induction_on with
  | empty =>
    have h : (⋃ i ∈ (∅ : Finset α), P i) = ∅ := by
      ext x
      simp
    rw [h, Finset.sum_empty]
    let _ : IsEmpty ↥(∅ : Set E) := ⟨fun x => Set.notMem_empty _ x.2⟩
    exact ⟨IsPolyhedron.empty, Homology.eulerChar_of_isEmpty ℚ⟩
  | insert i W hi ih =>
    obtain ⟨hW, hWχ⟩ := ih (fun j hj => hP j (Finset.mem_insert_of_mem hj))
      (fun j hj l hl hjl =>
        hdisj j (Finset.mem_insert_of_mem hj) l (Finset.mem_insert_of_mem hl) hjl)
    have hi' := hP i (Finset.mem_insert_self i W)
    have hd : Disjoint (P i) (⋃ j ∈ W, P j) := by
      rw [Set.disjoint_iUnion₂_right]
      intro j hj
      exact hdisj i (Finset.mem_insert_self i W) j (Finset.mem_insert_of_mem hj)
        fun h => hi (h ▸ hj)
    rw [Finset.set_biUnion_insert, Finset.sum_insert hi]
    refine ⟨hi'.union hW, ?_⟩
    rw [hi'.eulerChar_union_of_disjoint hW hd ℚ, hWχ]

theorem IsPLSphere.homologyEulerChar_eq_zero {C : Set E} (hC : IsPLSphere 1 C) :
    Homology.eulerChar ℚ (TopCat.of ↥C) = 0 := by
  obtain ⟨L, hLfin, hLspace⟩ := hC.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  rw [← hLspace, ← eulerChar_eq_singular L ℚ]
  exact eulerChar_of_isPLSphere_one L (hLspace.symm ▸ hC)

theorem IsPLBall.homologyEulerChar_eq_one {n : ℕ} {C : Set E} (hC : IsPLBall n C) :
    Homology.eulerChar ℚ (TopCat.of ↥C) = 1 := by
  obtain ⟨L, hLfin, hLspace⟩ := hC.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  rw [← hLspace, ← eulerChar_eq_singular L ℚ]
  exact eulerChar_of_isPLBall L (hLspace.symm ▸ hC)

open Classical in
theorem IsCombinatorialManifoldWithBoundary.eulerChar_add_card_le_two
    (M : Geometry.SimplicialComplex ℝ E) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 2 M) (hconn : IsConnected M.space)
    {ι : Type} (I : Finset ι) (J : ι → Set E) (hJ : ∀ i ∈ I, IsPLSphere 1 (J i))
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (J i) (J j))
    (hbd : (boundaryComplex 2 M).space = ⋃ i ∈ I, J i) :
    eulerChar M + I.card ≤ 2 := by
  classical
  let _ : DecidableEq (E × (I → ℝ)) := fun a b => Classical.propDecidable (a = b)
  let ι₀ : E →ₗ[ℝ] E × (I → ℝ) := LinearMap.inl ℝ E (I → ℝ)
  have hι₀ : Function.Injective ι₀ := LinearMap.inl_injective
  have hMpoly := isPolyhedron_space M
  have hι₀M := hMpoly.isPLHomeomorphOn_linearMap_image ι₀ hι₀
  obtain ⟨M', hM'fin, hM'space⟩ := (hMpoly.image_of_isPiecewiseAffineOn
    hι₀M.isPiecewiseAffineOn hι₀.injOn).exists_simplicialComplex
  let _ : Finite M'.faces := hM'fin.to_subtype
  have hι : IsPLHomeomorphOn ι₀ M.space M'.space := by
    rw [hM'space]
    exact hι₀M
  have hM' : IsCombinatorialManifoldWithBoundary 2 M' := hM.of_isPLHomeomorphOn hι
  have hJM : ∀ i ∈ I, J i ⊆ M.space := fun i hi =>
    (subset_iUnion₂ (s := fun j (_ : j ∈ I) => J j) i hi).trans
      (hbd.symm.subset.trans (boundaryComplex_space_subset 2 M))
  have hM'bd : (boundaryComplex 2 M').space = ⋃ i : I, ι₀ '' J i := by
    change (boundaryComplex (1 + 1) M').space = _
    rw [boundaryComplex_space_of_isPLHomeomorphOn M M' hM hι, hbd, image_iUnion₂]
    ext y
    simp only [mem_iUnion, exists_prop, Subtype.exists]
  have hdisk : ∀ i : I, ∃ (D : Set (E × (I → ℝ))) (r : (Fin 3 → ℝ) → E × (I → ℝ)),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ r '' stdSimplexBoundary 2 = ι₀ '' J i ∧
      D ∩ M'.space = ι₀ '' J i ∧
      ∀ y ∈ D, ∃ s : ℝ, y.2 = s • Pi.single i (1 : ℝ) ∧ (s = 0 → y ∈ ι₀ '' J i) := by
    intro i
    obtain ⟨D, r, hr, hrbd, hD⟩ := exists_cone_disk_of_isPLSphere_one (hJ i.1 i.2)
    let Λ : E × ℝ →ₗ[ℝ] E × (I → ℝ) := LinearMap.prodMap LinearMap.id
      ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (Pi.single i (1 : ℝ)))
    have hΛapply : ∀ z : E × ℝ, Λ z = (z.1, z.2 • Pi.single i (1 : ℝ)) := fun z => rfl
    have hΛ : Function.Injective Λ := by
      intro z z' hzz
      rw [hΛapply, hΛapply, Prod.mk.injEq] at hzz
      have h2 := congrFun hzz.2 i
      simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h2
      exact Prod.ext hzz.1 h2
    have hball : IsPLBall 2 D := ⟨r, hr⟩
    have hr' := hr.trans (hball.isPolyhedron.isPLHomeomorphOn_linearMap_image Λ hΛ)
    have hΛJ : Λ '' (J i ×ˢ {0}) = ι₀ '' J i := by
      ext y
      simp only [mem_image, mem_prod, mem_singleton_iff, Prod.exists]
      constructor
      · rintro ⟨x, s, ⟨hx, rfl⟩, rfl⟩
        exact ⟨x, hx, by rw [hΛapply]; simp [ι₀]⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, 0, ⟨hx, rfl⟩, by rw [hΛapply]; simp [ι₀]⟩
    have hpt : ∀ y ∈ Λ '' D, ∃ s : ℝ, y.2 = s • Pi.single i (1 : ℝ) ∧
        (s = 0 → y ∈ ι₀ '' J i) := by
      rintro _ ⟨z, hz, rfl⟩
      refine ⟨z.2, by rw [hΛapply], fun hs => ?_⟩
      have hzJ := (hD z hz).2 hs
      rw [← hΛJ]
      exact mem_image_of_mem Λ hzJ
    refine ⟨Λ '' D, Λ ∘ r, hr', by rw [image_comp, hrbd, hΛJ], ?_, hpt⟩
    apply Subset.antisymm
    · rintro y ⟨hyD, hyM⟩
      obtain ⟨s, hs, hsJ⟩ := hpt y hyD
      refine hsJ ?_
      rw [hM'space] at hyM
      obtain ⟨x, -, rfl⟩ := hyM
      have h0 := congrFun hs i
      simpa [ι₀] using h0.symm
    · intro y hy
      refine ⟨?_, ?_⟩
      · rw [← hΛJ, ← hrbd] at hy
        exact image_mono ((image_mono fun x hx => hx.1).trans hr.image_eq.subset) hy
      · rw [hM'space]
        exact image_mono (hJM i.1 i.2) hy
  choose D r hr hrbd hDM hDpt using hdisk
  have hDdisj : ∀ i j : I, i ≠ j → Disjoint (D i) (D j) := by
    intro i j hij
    rw [disjoint_left]
    intro y hyi hyj
    obtain ⟨s, hs, hsJ⟩ := hDpt i y hyi
    obtain ⟨s', hs', hs'J⟩ := hDpt j y hyj
    have hsi : s = 0 := by
      have h := congrFun (hs.symm.trans hs') i
      simpa [Pi.single_apply, hij] using h
    have hs'j : s' = 0 := by
      have h := congrFun (hs.symm.trans hs') j
      simpa [Pi.single_apply, Ne.symm hij] using h.symm
    obtain ⟨x, hx, rfl⟩ := hsJ hsi
    obtain ⟨x', hx', hxx'⟩ := hs'J hs'j
    have hxeq : x' = x := hι₀ hxx'
    rw [hxeq] at hx'
    exact disjoint_left.mp (hdisj i.1 i.2 j.1 j.2 fun h => hij (Subtype.ext h)) hx hx'
  have hunion : ∀ W : Finset I, ∃ L : Geometry.SimplicialComplex ℝ (E × (I → ℝ)),
      L.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 2 L ∧ L.space = ⋃ i ∈ W, D i ∧
      (boundaryComplex 2 L).space = ⋃ i ∈ W, ι₀ '' J i := by
    intro W
    induction W using Finset.induction_on with
    | empty =>
      refine ⟨⊥, by simp [Geometry.SimplicialComplex.faces_bot], fun v hv => ?_, ?_, ?_⟩
      · simp [Geometry.SimplicialComplex.faces_bot] at hv
      · rw [Geometry.SimplicialComplex.space_bot]
        ext y
        simp
      · have h : (boundaryComplex 2 (⊥ : Geometry.SimplicialComplex ℝ (E × (I → ℝ)))).space =
            ∅ := by
          ext y
          simp only [mem_empty_iff_false, iff_false]
          intro hy
          obtain ⟨t, ht, -⟩ := (boundaryComplex 2 _).mem_space_iff.mp hy
          simpa [Geometry.SimplicialComplex.faces_bot] using
            boundaryComplex_faces_subset 2 _ ht
        rw [h]
        ext y
        simp
    | insert i W hi ih =>
      obtain ⟨LW, hLWfin, hLW, hLWspace, hLWbd⟩ := ih
      let _ : Finite LW.faces := hLWfin.to_subtype
      have hball : IsPLBall 2 (D i) := ⟨r i, hr i⟩
      obtain ⟨Li, hLifin, hLispace⟩ := hball.isPolyhedron.exists_simplicialComplex
      let _ : Finite Li.faces := hLifin.to_subtype
      have hLi : IsCombinatorialManifoldWithBoundary 2 Li :=
        (hLispace.symm ▸ hball).isCombinatorialManifoldWithBoundary
      have hLibd : (boundaryComplex 2 Li).space = ι₀ '' J i := by
        change (boundaryComplex (1 + 1) Li).space = _
        rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex Li (hLispace.symm ▸ hr i),
          simplexBoundary_stdVertices_space, hrbd i]
      have hdis : Disjoint LW.space Li.space := by
        rw [hLWspace, hLispace, Set.disjoint_iUnion₂_left]
        intro j hj
        exact hDdisj j i fun h => hi (h ▸ hj)
      obtain ⟨R, hRfin, hR, hRspace, hRbd⟩ := hLW.exists_space_disjoint_union LW Li hLi hdis
      refine ⟨R, hRfin, hR, ?_, ?_⟩
      · rw [hRspace, hLWspace, hLispace, Finset.set_biUnion_insert, union_comm]
      · rw [hRbd, hLWbd, hLibd, Finset.set_biUnion_insert, union_comm]
  obtain ⟨L, hLfin, hL, hLspace, hLbd⟩ := hunion Finset.univ
  let _ : Finite L.faces := hLfin.to_subtype
  have hinter : M'.space ∩ L.space = ⋃ i : I, ι₀ '' J i := by
    rw [hLspace, inter_iUnion₂]
    ext y
    simp only [mem_iUnion, Finset.mem_univ, exists_prop, true_and]
    constructor
    · rintro ⟨i, hy⟩
      rw [inter_comm, hDM i] at hy
      exact ⟨i, hy⟩
    · rintro ⟨i, hy⟩
      refine ⟨i, ?_⟩
      rw [inter_comm, hDM i]
      exact hy
  have hLbd' : (boundaryComplex 2 L).space = ⋃ i : I, ι₀ '' J i := by
    rw [hLbd]
    ext y
    simp
  obtain ⟨R, hRfin, hR, hRspace⟩ := exists_isCombinatorialManifold_space_union M' L hM' hL
    (hinter.trans hM'bd.symm) (hinter.trans hLbd'.symm)
  let _ : Finite R.faces := hRfin.to_subtype
  have hM'c : IsConnected M'.space := by
    rw [hM'space]
    exact hconn.image ι₀ ι₀.continuous_of_finiteDimensional.continuousOn
  have hRc : IsConnected R.space := by
    rw [hRspace, hLspace]
    refine IsConnected.union_biUnion hM'c Finset.univ
      (fun i _ => IsPLBall.isConnected ⟨r i, hr i⟩) fun i _ => ?_
    rw [inter_comm, hDM i]
    exact (hJ i.1 i.2).nonempty.image ι₀
  have hle : eulerChar R ≤ 2 := IsCombinatorialManifold.faceEulerChar_le_two R hR hRc
  let Bd := boundaryComplex 2 M'
  let _ : Finite Bd.faces := (boundaryComplex_faces_finite 2 M').to_subtype
  have hsplit := eulerChar_eq_add_sub_of_space_union R M' L Bd hRspace
    (by rw [hinter]; exact hM'bd)
  have hχM := eulerChar_eq_of_isPLHomeomorphOn M M' hι
  have hχL : eulerChar L = I.card := by
    rw [eulerChar_eq_singular L ℚ, hLspace]
    have h := IsPolyhedron.eulerChar_biUnion (Finset.univ : Finset I)
      (fun i _ => IsPLBall.isPolyhedron ⟨r i, hr i⟩) (fun i _ j _ hij => hDdisj i j hij)
    rw [h.2, Finset.sum_congr rfl fun i _ => IsPLBall.homologyEulerChar_eq_one ⟨r i, hr i⟩]
    simp
  have hχBd : eulerChar Bd = 0 := by
    rw [eulerChar_eq_singular Bd ℚ, hM'bd]
    have hsph : ∀ i : I, IsPLSphere 1 (ι₀ '' J i) := fun i =>
      (hJ i.1 i.2).of_isPLHomeomorphOn
        ((hJ i.1 i.2).isPolyhedron.isPLHomeomorphOn_linearMap_image ι₀ hι₀)
    have hU : (⋃ i : I, ι₀ '' J i) = ⋃ i ∈ (Finset.univ : Finset I), ι₀ '' J i := by
      ext y
      simp
    rw [hU]
    have h := IsPolyhedron.eulerChar_biUnion (Finset.univ : Finset I)
      (fun i _ => (hsph i).isPolyhedron) fun i _ j _ hij =>
        (hdisj i.1 i.2 j.1 j.2 fun h => hij (Subtype.ext h)).image hι₀.injOn
          (subset_univ _) (subset_univ _)
    rw [h.2]
    exact Finset.sum_eq_zero fun i _ => (hsph i).homologyEulerChar_eq_zero
  have hsum : eulerChar R = eulerChar M + I.card := by
    rw [hsplit, hχBd, hχL, ← hχM, sub_zero]
  omega

end Capping

section Additivity

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPolyhedron.eulerChar_biUnion_of_inter {α : Type*} (W : Finset α) {P : α → Set E}
    (hP : ∀ i ∈ W, IsPolyhedron (P i))
    (hinter : ∀ i ∈ W, ∀ j ∈ W, i ≠ j → P i ∩ P j = ∅ ∨ IsPLSphere 1 (P i ∩ P j))
    (htriple : ∀ i ∈ W, ∀ j ∈ W, ∀ l ∈ W, i ≠ j → i ≠ l → j ≠ l → P i ∩ P j ∩ P l = ∅) :
    IsPolyhedron (⋃ i ∈ W, P i) ∧ Homology.eulerChar ℚ (TopCat.of ↥(⋃ i ∈ W, P i)) =
      ∑ i ∈ W, Homology.eulerChar ℚ (TopCat.of ↥(P i)) := by
  classical
  induction W using Finset.induction_on with
  | empty =>
    have h : (⋃ i ∈ (∅ : Finset α), P i) = ∅ := by
      ext x
      simp
    rw [h, Finset.sum_empty]
    let _ : IsEmpty ↥(∅ : Set E) := ⟨fun x => Set.notMem_empty _ x.2⟩
    exact ⟨IsPolyhedron.empty, Homology.eulerChar_of_isEmpty ℚ⟩
  | insert w W hw ih =>
    obtain ⟨hU, hUχ⟩ := ih (fun j hj => hP j (Finset.mem_insert_of_mem hj))
      (fun j hj l hl hjl =>
        hinter j (Finset.mem_insert_of_mem hj) l (Finset.mem_insert_of_mem hl) hjl)
      (fun a ha b hb c hc hab hac hbc => htriple a (Finset.mem_insert_of_mem ha) b
        (Finset.mem_insert_of_mem hb) c (Finset.mem_insert_of_mem hc) hab hac hbc)
    have hPw := hP w (Finset.mem_insert_self w W)
    have hpieces : ∀ u ∈ W, IsPolyhedron (P w ∩ P u) ∧
        Homology.eulerChar ℚ (TopCat.of ↥(P w ∩ P u)) = 0 := by
      intro u hu
      have hwu : w ≠ u := fun h => hw (h ▸ hu)
      rcases hinter w (Finset.mem_insert_self w W) u (Finset.mem_insert_of_mem hu) hwu with
        h0 | hs
      · rw [h0]
        let _ : IsEmpty ↥(∅ : Set E) := ⟨fun x => Set.notMem_empty _ x.2⟩
        exact ⟨IsPolyhedron.empty, Homology.eulerChar_of_isEmpty ℚ⟩
      · exact ⟨hs.isPolyhedron, hs.homologyEulerChar_eq_zero⟩
    have hdisj : ∀ u ∈ W, ∀ u' ∈ W, u ≠ u' → Disjoint (P w ∩ P u) (P w ∩ P u') := by
      intro u hu u' hu' huu'
      rw [disjoint_iff_inter_eq_empty]
      have h := htriple w (Finset.mem_insert_self w W) u (Finset.mem_insert_of_mem hu) u'
        (Finset.mem_insert_of_mem hu') (fun h => hw (h ▸ hu)) (fun h => hw (h ▸ hu')) huu'
      rw [← h]
      ext x
      simp only [mem_inter_iff]
      tauto
    obtain ⟨-, hIχ⟩ := IsPolyhedron.eulerChar_biUnion W (fun u hu => (hpieces u hu).1) hdisj
    have hadd := hPw.eulerChar_union_add_inter hU ℚ
    rw [inter_iUnion₂, hIχ, Finset.sum_eq_zero fun u hu => (hpieces u hu).2, add_zero] at hadd
    rw [Finset.set_biUnion_insert, Finset.sum_insert hw]
    exact ⟨hPw.union hU, by rw [hadd, hUχ]⟩

end Additivity

section Ray

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem isEmbedding_derivedNeighborhoodRay_Ico_and_range (A K : Geometry.SimplicialComplex ℝ E)
    [Finite A.faces] (hKA : K.faces ⊆ A.faces)
    (hN : (derivedNeighborhood A K).space ⊆ interior A.space) :
    _root_.Topology.IsEmbedding (fun q : frontier (derivedNeighborhood A K).space ×
        Set.Ico (0 : ℝ) 1 => (1 - (q.2 : ℝ)) • (q.1 : E) + (q.2 : ℝ) •
          subcomplexBarycentricProjection (barycentricSubdivision A) (barycentricSubdivision K)
            q.1) ∧
      Set.range (fun q : frontier (derivedNeighborhood A K).space × Set.Ico (0 : ℝ) 1 =>
        (1 - (q.2 : ℝ)) • (q.1 : E) + (q.2 : ℝ) •
          subcomplexBarycentricProjection (barycentricSubdivision A) (barycentricSubdivision K)
            q.1) = (derivedNeighborhood A K).space \ K.space := by
  have hfront := frontier_derivedNeighborhood_space_subset A K
  let _ : Finite (derivedNeighborhood A K).faces :=
    (derivedNeighborhood_faces_finite A K).to_subtype
  have hclosed : IsClosed (derivedNeighborhood A K).space :=
    (SimplicialComplex.isCompact_geometricSpace _).isClosed
  have _ : CompactSpace (frontier (derivedNeighborhood A K).space) :=
    isCompact_iff_compactSpace.mp
      ((SimplicialComplex.isCompact_geometricSpace _).of_isClosed_subset isClosed_frontier hfront)
  let R : frontier (derivedNeighborhood A K).space × Set.Icc (0 : ℝ) 1 → E := fun q =>
    (1 - (q.2 : ℝ)) • (q.1 : E) + (q.2 : ℝ) •
      subcomplexBarycentricProjection (barycentricSubdivision A) (barycentricSubdivision K) q.1
  have hp : Continuous (fun x : frontier (derivedNeighborhood A K).space =>
      subcomplexBarycentricProjection (barycentricSubdivision A) (barycentricSubdivision K) x) :=
    (continuousOn_subcomplexBarycentricProjection_derivedNeighborhood.mono hfront).domRestrict
  have hR : Continuous R :=
    ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
      (continuous_subtype_val.comp continuous_fst)).add
      ((continuous_subtype_val.comp continuous_snd).smul (hp.comp continuous_fst))
  have hlt : ∀ q : frontier (derivedNeighborhood A K).space × Set.Icc (0 : ℝ) 1,
      R q ∉ K.space → (q.2 : ℝ) < 1 := by
    intro q hq
    refine lt_of_le_of_ne q.2.2.2 fun h1 => hq ?_
    change (1 - (q.2 : ℝ)) • (q.1 : E) + (q.2 : ℝ) •
      subcomplexBarycentricProjection (barycentricSubdivision A) (barycentricSubdivision K) q.1
        ∈ K.space
    rw [h1, sub_self, zero_smul, one_smul, zero_add]
    exact subcomplexBarycentricProjection_mem_subcomplex hKA (hfront q.1.2)
  have hinj : Function.Injective ((K.space)ᶜ.restrictPreimage R) := by
    rintro ⟨q, hq⟩ ⟨q', hq'⟩ heq
    obtain ⟨hbb, htt⟩ := eq_of_smul_add_smul_subcomplexBarycentricProjection_eq hN q.1.2 q'.1.2
      q.2.2.1 (hlt q hq) q'.2.2.1 (hlt q' hq') (congrArg Subtype.val heq)
    exact Subtype.ext (Prod.ext (Subtype.ext hbb) (Subtype.ext htt))
  have hemb : _root_.Topology.IsEmbedding ((K.space)ᶜ.restrictPreimage R) :=
    (_root_.Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap hR.restrictPreimage
      hinj (IsClosedMap.restrictPreimage hR.isClosedMap _)).isEmbedding
  have hmem : ∀ q : frontier (derivedNeighborhood A K).space × Set.Ico (0 : ℝ) 1,
      Prod.map id (Set.inclusion Set.Ico_subset_Icc_self) q ∈ R ⁻¹' (K.space)ᶜ := fun q =>
    smul_add_smul_subcomplexBarycentricProjection_notMem hKA hN q.1.2 q.2.2.1 q.2.2.2
  refine ⟨(_root_.Topology.IsEmbedding.subtypeVal.comp hemb).comp
    ((_root_.Topology.IsEmbedding.id.prodMap
      (_root_.Topology.IsEmbedding.inclusion Set.Ico_subset_Icc_self)).codRestrict _ hmem), ?_⟩
  apply Subset.antisymm
  · rintro _ ⟨⟨⟨b, hb⟩, ⟨t, ht0, ht1⟩⟩, rfl⟩
    refine ⟨?_, smul_add_smul_subcomplexBarycentricProjection_notMem hKA hN hb ht0 ht1⟩
    rcases ht0.eq_or_lt with h0 | h0
    · subst h0
      simp only [sub_zero, one_smul, zero_smul, add_zero]
      exact hfront hb
    · exact interior_subset
        (smul_add_smul_subcomplexBarycentricProjection_mem_interior hN hb h0 ht1)
  · rintro x ⟨hx, hxK⟩
    by_cases hxint : x ∈ interior (derivedNeighborhood A K).space
    · obtain ⟨b, hb, t, ht, hbt⟩ :=
        exists_mem_frontier_derivedNeighborhood_of_mem_interior hKA hxint hxK
      exact ⟨(⟨b, hb⟩, ⟨t, ht.1.le, ht.2⟩), hbt⟩
    · have hxfr : x ∈ frontier (derivedNeighborhood A K).space := by
        rw [hclosed.frontier_eq]
        exact ⟨hx, hxint⟩
      refine ⟨(⟨x, hxfr⟩, ⟨0, le_rfl, zero_lt_one⟩), ?_⟩
      simp

theorem nonempty_homotopyEquiv_prod_Ico (X : Type) [TopologicalSpace X] :
    Nonempty (ContinuousMap.HomotopyEquiv (X × Set.Ico (0 : ℝ) 1) X) := by
  let z : Set.Ico (0 : ℝ) 1 := ⟨0, le_rfl, zero_lt_one⟩
  let f : C(X × Set.Ico (0 : ℝ) 1, X) := ⟨Prod.fst, continuous_fst⟩
  let g : C(X, X × Set.Ico (0 : ℝ) 1) := ⟨fun x => (x, z), by fun_prop⟩
  have hmem : ∀ (s : unitInterval) (t : Set.Ico (0 : ℝ) 1), (s : ℝ) * t ∈ Set.Ico (0 : ℝ) 1 :=
    fun s t => ⟨mul_nonneg s.2.1 t.2.1, lt_of_le_of_lt
      (mul_le_of_le_one_left t.2.1 s.2.2) t.2.2⟩
  let H : ContinuousMap.Homotopy (g.comp f) (ContinuousMap.id _) :=
    { toFun := fun p => (p.2.1, ⟨(p.1 : ℝ) * p.2.2, hmem p.1 p.2.2⟩)
      continuous_toFun := by fun_prop
      map_zero_left := fun p => by
        change (p.1, _) = (p.1, z)
        congr 1
        exact Subtype.ext (zero_mul _)
      map_one_left := fun p => by
        change (p.1, _) = p
        exact Prod.ext rfl (Subtype.ext (one_mul _)) }
  exact ⟨{ toFun := f, invFun := g, left_inv := ⟨H⟩, right_inv := ContinuousMap.Homotopic.refl _ }⟩

end Ray

section Sdiff

theorem nonempty_homeomorph_sdiff_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {A B : Set X} (hf : _root_.Topology.IsEmbedding (A.domRestrict f))
    (hBA : B ⊆ A) : Nonempty (↥(A \ B) ≃ₜ ↥(f '' A \ f '' B)) := by
  have hinj : InjOn f A := injOn_iff_injective.mpr hf.injective
  have hg : _root_.Topology.IsEmbedding ((A \ B).domRestrict f) :=
    hf.comp (_root_.Topology.IsEmbedding.inclusion sdiff_subset)
  have hrange : Set.range ((A \ B).domRestrict f) = f '' A \ f '' B := by
    ext y
    constructor
    · rintro ⟨⟨x, hxA, hxB⟩, rfl⟩
      refine ⟨⟨x, hxA, rfl⟩, ?_⟩
      rintro ⟨z, hzB, hzx⟩
      exact hxB ((hinj (hBA hzB) hxA hzx) ▸ hzB)
    · rintro ⟨⟨x, hxA, rfl⟩, hy⟩
      exact ⟨⟨x, hxA, fun hxB => hy ⟨x, hxB, rfl⟩⟩, rfl⟩
  exact ⟨hg.toHomeomorph.trans (Homeomorph.setCongr hrange)⟩

end Sdiff

section Tube

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {N N' : Set (EuclideanSpace ℝ (Fin 3))}
  {C Cpp : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3))}
  {D Dbd Ec Eint Ebd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
  {XK : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {AK : EuclideanSpace ℝ (Fin 3) → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}

theorem IsHandleDecompositionOfTube.inter_inter_eq_empty
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    {u w z : E3} (hu : u ∈ K.vertices) (hw : w ∈ K.vertices) (hz : z ∈ K.vertices)
    (huw : u ≠ w) (huz : u ≠ z) (hwz : w ≠ z) : Cpp u ∩ Cpp w ∩ Cpp z = ∅ := by
  by_cases h1 : ({u, w} : Finset E3) ∈ K.faces
  · by_cases h2 : ({w, z} : Finset E3) ∈ K.faces
    · have hsub : Cpp u ∩ Cpp w ∩ Cpp z ⊆ Ec {u, w} ∩ Ec {w, z} := by
        rw [← hd.handleEdge u hu w hw huw h1, ← hd.handleEdge w hw z hz hwz h2]
        exact fun x hx => ⟨⟨hx.1.1, hx.1.2⟩, ⟨hx.1.2, hx.2⟩⟩
      have hne : ({u, w} : Finset E3) ≠ {w, z} := by
        intro heq
        have hmem : u ∈ ({w, z} : Finset E3) := heq ▸ Finset.mem_insert_self u {w}
        rcases Finset.mem_insert.mp hmem with h | h
        · exact huw h
        · exact huz (Finset.mem_singleton.mp h)
      exact subset_eq_empty (hsub.trans (hd.pseudoCellDisjoint _ h1 (Finset.card_pair huw) _ h2
        (Finset.card_pair hwz) hne).inter_eq.subset) rfl
    · rw [inter_assoc, hd.handleNonEdge w hw z hz hwz h2, inter_empty]
  · rw [hd.handleNonEdge u hu w hw huw h1, empty_inter]

theorem IsTube.isConnected_space_of_isConnected (ht : IsTube K N C D Dbd h N') {X : Set E3}
    (hX : IsConnected X) (hXN : X ⊆ N') (hKX : h '' K.space ⊆ X) : IsConnected K.space := by
  classical
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  obtain ⟨A, hAfin, -, hKA, hC, -⟩ := ht.derivedModel
  let _ : Finite A.faces := hAfin.to_subtype
  have hN : N = (derivedNeighborhood A K).space := by
    rw [ht.unionEq, ← iUnion_graphDualCell_space A K hKA]
    exact iUnion₂_congr hC
  have hKN : K.space ⊆ N := by
    rw [hN]
    exact subcomplex_space_subset_derivedNeighborhood hKA
  let eN : ↥N ≃ₜ ↥(h '' N) := ht.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (by rw [range_domRestrict]))
  have heN : ∀ x : ↥N, ((eN x : ↥(h '' N)) : E3) = h x := fun _ => rfl
  have hXN' : X ⊆ h '' N := ht.imageEq ▸ hXN
  have hXs : IsConnected (Subtype.val ⁻¹' X : Set ↥(h '' N)) := by
    refine ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := hX.nonempty
      exact ⟨⟨x, hXN' hx⟩, hx⟩
    · apply _root_.Topology.IsInducing.subtypeVal.isPreconnected_image.mp
      rw [Subtype.image_preimage_coe, inter_eq_right.mpr hXN']
      exact hX.isPreconnected
  let p := subcomplexBarycentricProjection (barycentricSubdivision A) (barycentricSubdivision K)
  have hp : ContinuousOn p N := by
    rw [hN]
    exact continuousOn_subcomplexBarycentricProjection_derivedNeighborhood
  have hpc : Continuous (fun x : ↥N => p x) := hp.domRestrict
  have hcon := (hXs.image _ eN.symm.continuous.continuousOn).image _ hpc.continuousOn
  convert hcon using 1
  ext y
  constructor
  · intro hy
    refine ⟨⟨y, hKN hy⟩, ⟨⟨h y, mem_image_of_mem h (hKN hy)⟩, hKX (mem_image_of_mem h hy), ?_⟩, ?_⟩
    · apply eN.injective
      rw [Homeomorph.apply_symm_apply]
      exact Subtype.ext (heN ⟨y, hKN hy⟩).symm
    · change p y = y
      exact subcomplexBarycentricProjection_eq_self_on_subcomplex hKA hy
  · rintro ⟨x, -, rfl⟩
    have hxN : (x : E3) ∈ (derivedNeighborhood A K).space := hN ▸ x.2
    exact subcomplexBarycentricProjection_mem_subcomplex hKA hxN

open Classical in
theorem IsTube.bettiOne_sdiff_image_eq (ht : IsTube K N C D Dbd h N') [Finite K.faces]
    (hconn : IsConnected K.space) :
    PathConnectedSpace ↥(N' \ h '' K.space) ∧
      FiniteDimensional ℚ
        ((fieldSingularChains (k := ℚ) (X := ↥(N' \ h '' K.space))).homology 1) ∧
      (Homology.bettiOne ↥(N' \ h '' K.space) : ℤ) = 2 - 2 * eulerChar K := by
  classical
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  obtain ⟨A, hAfin, hA, hKA, hC, -⟩ := ht.derivedModel
  let _ : Finite A.faces := hAfin.to_subtype
  have hN : N = (derivedNeighborhood A K).space := by
    rw [ht.unionEq, ← iUnion_graphDualCell_space A K hKA]
    exact iUnion₂_congr hC
  have hKN : K.space ⊆ interior N := subset_interior_iff_mem_nhdsSet.mpr ht.isNeighborhood
  have hNA : N ⊆ A.space := by
    rw [hN]
    exact derivedNeighborhood_space_subset A K
  have hKint : K.space ⊆ interior A.space := hKN.trans (interior_mono hNA)
  have hNint := derivedNeighborhood_space_subset_interior (n := 2) finrank_euclideanSpace_fin hA
    hKA hKint
  obtain ⟨hemb, hrange⟩ := isEmbedding_derivedNeighborhoodRay_Ico_and_range A K hKA hNint
  let e₁ := hemb.toHomeomorph.trans (Homeomorph.setCongr hrange)
  have hemb' : _root_.Topology.IsEmbedding ((derivedNeighborhood A K).space.domRestrict h) :=
    hN ▸ ht.isEmbedding
  obtain ⟨e₂⟩ := nonempty_homeomorph_sdiff_image hemb'
    (subcomplex_space_subset_derivedNeighborhood hKA)
  have hN' : N' = h '' (derivedNeighborhood A K).space := by
    rw [ht.imageEq, hN]
  obtain ⟨HP⟩ := nonempty_homotopyEquiv_prod_Ico (frontier (derivedNeighborhood A K).space)
  let e₃ : ↥(N' \ h '' K.space) ≃ₜ
      (frontier (derivedNeighborhood A K).space × Set.Ico (0 : ℝ) 1) :=
    (Homeomorph.setCongr (by rw [hN'])).trans (e₂.symm.trans e₁.symm)
  let HE : ContinuousMap.HomotopyEquiv ↥(N' \ h '' K.space)
      ↥(frontier (derivedNeighborhood A K).space) := e₃.toHomotopyEquiv.trans HP
  let Nc := derivedNeighborhood A K
  have hNc : IsCombinatorialManifoldWithBoundary 3 Nc := hA.derivedNeighborhood K
  let BN := @boundaryComplex _ _ _ (Classical.decEq _) (2 + 1) Nc
  have hFr : frontier (derivedNeighborhood A K).space = BN.space :=
    frontier_space_eq_boundaryComplex_space hNc
  let _ : Finite BN.faces := ((Set.toFinite Nc.faces).subset fun _ hs => hs.1).to_subtype
  have hBman : IsCombinatorialManifold 2 BN := isCombinatorialManifold_boundaryComplex Nc hNc
  have hNcconn : IsConnected Nc.space := by
    obtain ⟨x₀, hx₀⟩ := hconn.nonempty
    refine ⟨⟨x₀, subcomplex_space_subset_derivedNeighborhood hKA hx₀⟩, ?_⟩
    refine isPreconnected_of_forall x₀ fun y hy => ?_
    let py := subcomplexBarycentricProjection (barycentricSubdivision A)
      (barycentricSubdivision K) y
    have hpy : py ∈ K.space := subcomplexBarycentricProjection_mem_subcomplex hKA hy
    refine ⟨K.space ∪ segment ℝ y py, union_subset
      (subcomplex_space_subset_derivedNeighborhood hKA) ?_, Or.inl hx₀,
      Or.inr (left_mem_segment ℝ y py), ?_⟩
    · rintro z ⟨a, b, ha, hb, hab, rfl⟩
      have hmem := subcomplexBarycentricHomotopy_mem_derivedNeighborhood hy
        ⟨b, hb, by linarith⟩
      have ha' : a = 1 - b := by linarith
      rw [ha']
      exact hmem
    · exact IsPreconnected.union py hpy (right_mem_segment ℝ y py) hconn.isPreconnected
        (convex_segment y py).isPreconnected
  have hb2 : Homology.bettiNumber ℚ (TopCat.of Nc.space) 2 = 0 := by
    rw [bettiNumber_derivedNeighborhood_eq ℚ hKA 2]
    exact bettiNumber_eq_zero_of_card_le K ℚ 2 ht.oneDimensional 2 le_rfl
  obtain ⟨T, -, hTcard, hAT⟩ := exists_affineIndependent_openSimplex_superset 3
    finrank_euclideanSpace_fin (isPolyhedron_space A).isCompact.isBounded
  have hAo : IsOrientable 3 A := isOrientable_of_space_subset_convexHull A hA T hTcard
    (hAT.trans (openSimplex_subset_convexHull T))
  obtain ⟨o⟩ : IsOrientable 3 Nc := IsOrientable.derivedNeighborhood hA hAo
  have hBne : BN.space.Nonempty := by
    rw [← hFr]
    by_contra hempty
    rw [not_nonempty_iff_eq_empty] at hempty
    have hclopen : IsClopen Nc.space := isClopen_iff_frontier_eq_empty.mpr hempty
    rcases isClopen_iff.mp hclopen with h0 | huniv
    · exact hNcconn.nonempty.ne_empty h0
    · exact noncompact_univ E3 (huniv ▸ SimplicialComplex.isCompact_geometricSpace Nc)
  have hBconn : IsConnected BN.space := by
    obtain ⟨y₀, hy₀⟩ := hBne
    let c₀ : ConnectedComponents BN.space := ConnectedComponents.mk ⟨y₀, hy₀⟩
    have hcard := card_otherBoundaryComponent_le_bettiNumber_two (k := ℚ) Nc hNc hNcconn o c₀
    rw [hb2, Nat.le_zero] at hcard
    let _ : Finite (ConnectedComponents BN.space) := finite_connectedComponents_space BN
    have hempty : IsEmpty (OtherBoundaryComponent BN c₀) :=
      (Nat.card_eq_zero.mp hcard).resolve_right (not_infinite_iff_finite.mpr inferInstance)
    rw [isConnected_iff_connectedSpace, connectedSpace_iff_connectedComponent]
    refine ⟨⟨y₀, hy₀⟩, eq_univ_of_forall fun z => ?_⟩
    by_contra hz
    exact hempty.false ⟨ConnectedComponents.mk z, fun hzc =>
      hz (ConnectedComponents.coe_eq_coe'.mp hzc)⟩
  have hBo := hBman.isOrientable_of_finrank_eq_three BN finrank_euclideanSpace_fin hBconn
  have hχ := hBman.eulerChar_eq_two_sub_bettiOne_of_isOrientable BN hBconn hBo
  have hχK : eulerChar BN = 2 * eulerChar K :=
    eulerChar_boundary_derivedNeighborhood_eq_two_mul hA hKA
  have hbetti : Homology.bettiOne ↥(N' \ h '' K.space) =
      Homology.bettiOne ↥(frontier (derivedNeighborhood A K).space) :=
    Homology.bettiNumber_eq_of_homotopyEquiv ℚ (X := TopCat.of ↥(N' \ h '' K.space))
      (Y := TopCat.of ↥(frontier (derivedNeighborhood A K).space)) HE 1
  have hFrpc : PathConnectedSpace ↥(frontier (derivedNeighborhood A K).space) := by
    rw [hFr]
    exact isPathConnected_iff_pathConnectedSpace.mp
      (SimplicialComplex.isPathConnected_geometricSpace BN hBconn)
  have hIcopc : PathConnectedSpace (Set.Ico (0 : ℝ) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Ico (0 : ℝ) 1).isPathConnected ⟨0, le_rfl, zero_lt_one⟩)
  refine ⟨e₃.symm.surjective.pathConnectedSpace e₃.symm.continuous, ?_, ?_⟩
  · have hfin : Homology.finiteHomologyType ℚ
        (TopCat.of ↥(frontier (derivedNeighborhood A K).space)) := by
      rw [hFr]
      exact SimplicialComplex.finiteHomologyType_geometricSpace BN ℚ
    exact ((Homology.finiteHomologyType_iff_of_homotopyEquiv ℚ HE).mpr hfin).1 1
  · rw [hbetti, hFr]
    omega

theorem pathConnectedSpace_frontier_and_homologyEulerChar [Finite XK.faces]
    (hX : IsCombinatorialManifoldWithBoundary 3 XK) (hS : IsConnected (frontier XK.space)) :
    PathConnectedSpace ↥(frontier XK.space) ∧
      Homology.eulerChar ℚ (TopCat.of ↥(frontier XK.space)) =
        2 - (Homology.bettiOne ↥(frontier XK.space) : ℤ) := by
  classical
  let B := @boundaryComplex _ _ _ (Classical.decEq _) (2 + 1) XK
  have hFr : frontier XK.space = B.space := frontier_space_eq_boundaryComplex_space hX
  let _ : Finite B.faces := ((Set.toFinite XK.faces).subset fun _ hs => hs.1).to_subtype
  have hBman : IsCombinatorialManifold 2 B := isCombinatorialManifold_boundaryComplex XK hX
  rw [hFr] at hS ⊢
  have hBo := hBman.isOrientable_of_finrank_eq_three B finrank_euclideanSpace_fin hS
  refine ⟨isPathConnected_iff_pathConnectedSpace.mp
    (SimplicialComplex.isPathConnected_geometricSpace B hS), ?_⟩
  rw [← eulerChar_eq_singular B ℚ]
  exact hBman.eulerChar_eq_two_sub_bettiOne_of_isOrientable B hS hBo

theorem two_mul_eulerChar_eq_sum_edgesAt [Finite K.faces] (hdim : ∀ s ∈ K.faces, s.card ≤ 2) :
    2 * eulerChar K =
      ∑ v ∈ simplicialComplexVertices K, (2 - ((edgesAt K v).ncard : ℤ)) := by
  classical
  let F := (Set.toFinite K.faces).toFinset
  have hF : ∀ s, s ∈ F ↔ s ∈ K.faces := fun s => Set.Finite.mem_toFinset _
  let F2 := F.filter (fun s => s.card = 2)
  let VK := simplicialComplexVertices K
  have hF1 : F.filter (fun s => s.card = 1) = VK.image (fun v => ({v} : Finset E3)) := by
    ext s
    simp only [Finset.mem_filter, hF, Finset.mem_image, VK, mem_simplicialComplexVertices]
    constructor
    · rintro ⟨hs, hcard⟩
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard
      exact ⟨v, hs, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨hv, Finset.card_singleton v⟩
  have hFnot : F.filter (fun s => ¬ s.card = 1) = F2 := by
    ext s
    simp only [Finset.mem_filter, F2]
    constructor
    · rintro ⟨hs, hne⟩
      refine ⟨hs, le_antisymm (hdim s ((hF s).mp hs)) ?_⟩
      have hpos := Finset.card_pos.mpr (K.nonempty_of_mem_faces ((hF s).mp hs))
      omega
    · rintro ⟨hs, hcard⟩
      exact ⟨hs, by omega⟩
  have hχ : eulerChar K = (VK.card : ℤ) - F2.card := by
    change (∑ s ∈ F, -(-1 : ℤ) ^ s.card) = _
    rw [← Finset.sum_filter_add_sum_filter_not F (fun s => s.card = 1), hFnot]
    have h1 : ∑ s ∈ F.filter (fun s => s.card = 1), -(-1 : ℤ) ^ s.card = VK.card := by
      rw [Finset.sum_congr rfl (f := fun s : Finset E3 => -(-1 : ℤ) ^ s.card)
        (g := fun _ => (1 : ℤ))
        fun s hs => by simp only [(Finset.mem_filter.mp hs).2]; norm_num]
      rw [Finset.sum_const, hF1, Finset.card_image_of_injective _ Finset.singleton_injective]
      simp
    have h2 : ∑ s ∈ F2, -(-1 : ℤ) ^ s.card = -(F2.card : ℤ) := by
      rw [Finset.sum_congr rfl (f := fun s : Finset E3 => -(-1 : ℤ) ^ s.card)
        (g := fun _ => (-1 : ℤ))
        fun s hs => by simp only [(Finset.mem_filter.mp hs).2]; norm_num]
      simp
    rw [h1, h2]
    ring
  have hdeg : ∀ v, ((edgesAt K v).ncard : ℤ) = ((F2.filter (fun e => v ∈ e)).card : ℤ) := by
    intro v
    have hset : edgesAt K v = ↑(F2.filter (fun e => v ∈ e)) := by
      ext e
      change (e ∈ K.faces ∧ e.card = 2 ∧ v ∈ e) ↔ e ∈ F2.filter (fun e => v ∈ e)
      rw [Finset.mem_filter, Finset.mem_filter, hF]
      tauto
    rw [hset, Set.ncard_coe_finset]
  have hsumdeg : ∑ v ∈ VK, ((F2.filter (fun e => v ∈ e)).card : ℤ) = 2 * F2.card := by
    have h1 : ∀ v ∈ VK, ((F2.filter (fun e => v ∈ e)).card : ℤ) =
        ∑ e ∈ F2, if v ∈ e then (1 : ℤ) else 0 := fun v _ => by
      rw [Finset.card_filter, Nat.cast_sum]
      exact Finset.sum_congr rfl fun e _ => by split_ifs <;> simp
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    have h2 : ∀ e ∈ F2, (∑ v ∈ VK, if v ∈ e then (1 : ℤ) else 0) = 2 := by
      intro e he
      obtain ⟨heF, hcard⟩ := Finset.mem_filter.mp he
      have hsub : VK.filter (fun v => v ∈ e) = e := by
        ext v
        simp only [Finset.mem_filter, VK, mem_simplicialComplexVertices]
        constructor
        · exact fun hv => hv.2
        · intro hv
          exact ⟨K.down_closed ((hF e).mp heF) (Finset.singleton_subset_iff.mpr hv)
            (Finset.singleton_nonempty v), hv⟩
      rw [← Finset.sum_filter, Finset.sum_const, hsub, hcard]
      simp
    rw [Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [Finset.sum_sub_distrib, Finset.sum_congr rfl fun v _ => hdeg v, hsumdeg, hχ,
    Finset.sum_const, nsmul_eq_mul]
  ring

theorem section33_faceEulerChar_handlePiece
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
    (h34 : HasSinglePolygonTraces K h Ec XK.space)
    (h56 : HasConnectedHandlePieces K Ec Cpp XK.space AK)
    (hiso : ∀ hsub : frontier XK.space ⊆ N' \ h '' K.space, ∀ x : frontier XK.space,
      Function.Bijective (FundamentalGroup.map
        (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ :
          C(frontier XK.space, ↥(N' \ h '' K.space))) x)) :
    ∀ v ∈ K.vertices, ∀ [Finite (AK v).faces],
      SimplicialComplex.faceEulerChar (AK v).toPreAbstractSimplicialComplex =
        2 - ((edgesAt K v).ncard : ℤ) := by
  classical
  have ht := hd.tube
  let _ : Finite K.faces := ht.facesFinite.to_subtype
  obtain ⟨hXconn, hSconn, hpiece⟩ := h56
  let _ : Finite XK.faces := h2.facesFinite.to_subtype
  have hXclosed : IsClosed XK.space := (isPolyhedron_space XK).isClosed
  have hKX : h '' K.space ⊆ interior XK.space :=
    subset_interior_iff_mem_nhdsSet.mpr h2.isNeighborhood
  have hXN : XK.space ⊆ N' := h2.subsetInterior.trans interior_subset
  have hsub : frontier XK.space ⊆ N' \ h '' K.space := fun x hx =>
    ⟨hXN (hXclosed.frontier_subset hx), fun hxK => hx.2 (hKX hxK)⟩
  have hKconn : IsConnected K.space :=
    ht.isConnected_space_of_isConnected hXconn hXN (hKX.trans interior_subset)
  obtain ⟨hYpc, hYfin, hbY⟩ := ht.bettiOne_sdiff_image_eq hKconn
  obtain ⟨hSpc, hχS⟩ := pathConnectedSpace_frontier_and_homologyEulerChar h2.isManifold hSconn
  obtain ⟨x₀⟩ : Nonempty ↥(frontier XK.space) := hSconn.nonempty.to_subtype
  have hb1 : Homology.bettiOne ↥(frontier XK.space) ≤ Homology.bettiOne ↥(N' \ h '' K.space) :=
    finrank_fieldHomology_one_le_of_fundamentalGroup_map_bijective (k := ℚ)
      ⟨Set.inclusion hsub, continuous_inclusion hsub⟩ x₀ (hiso hsub x₀)
  have hglobal : 2 * eulerChar K ≤ Homology.eulerChar ℚ (TopCat.of ↥(frontier XK.space)) := by
    rw [hχS]
    have hb1' : (Homology.bettiOne ↥(frontier XK.space) : ℤ) ≤
        Homology.bettiOne ↥(N' \ h '' K.space) := by exact_mod_cast hb1
    omega
  let VK := simplicialComplexVertices K
  have hVK : ∀ u, u ∈ VK ↔ u ∈ K.vertices := fun u => mem_simplicialComplexVertices K
  have hspace : ∀ u ∈ K.vertices, (AK u).space = Cpp u ∩ frontier XK.space :=
    fun u hu => (hpiece u hu).2.1
  have hU : (⋃ u ∈ VK, (AK u).space) = frontier XK.space := by
    apply Subset.antisymm
    · refine iUnion₂_subset fun u hu => ?_
      rw [hspace u ((hVK u).mp hu)]
      exact inter_subset_right
    · intro x hx
      have hxN : x ∈ N' := (hsub hx).1
      rw [hd.coversTube] at hxN
      obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hxN
      exact mem_iUnion₂.mpr ⟨u, (hVK u).mpr hu, by rw [hspace u hu]; exact ⟨hxu, hx⟩⟩
  have hadd := IsPolyhedron.eulerChar_biUnion_of_inter VK (P := fun u => (AK u).space)
    (fun u hu => by
      let _ : Finite (AK u).faces := (hpiece u ((hVK u).mp hu)).1.to_subtype
      exact isPolyhedron_space _)
    (fun u hu w hw huw => by
      have hu' := (hVK u).mp hu
      have hw' := (hVK w).mp hw
      rw [hspace u hu', hspace w hw']
      by_cases hedge : ({u, w} : Finset E3) ∈ K.faces
      · right
        have heq : Cpp u ∩ frontier XK.space ∩ (Cpp w ∩ frontier XK.space) =
            Ec {u, w} ∩ frontier XK.space := by
          rw [← hd.handleEdge u hu' w hw' huw hedge]
          ext x
          simp only [mem_inter_iff]
          tauto
        rw [heq]
        exact (h34 _ hedge (Finset.card_pair huw)).1
      · left
        have hempty := hd.handleNonEdge u hu' w hw' huw hedge
        ext x
        simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
        intro hx
        have : x ∈ Cpp u ∩ Cpp w := ⟨hx.1.1, hx.2.1⟩
        rw [hempty] at this
        exact this)
    (fun u hu w hw z hz huw huz hwz => by
      have hu' := (hVK u).mp hu
      have hw' := (hVK w).mp hw
      have hz' := (hVK z).mp hz
      rw [hspace u hu', hspace w hw', hspace z hz']
      have htr := hd.inter_inter_eq_empty hu' hw' hz' huw huz hwz
      ext x
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
      intro hx
      have : x ∈ Cpp u ∩ Cpp w ∩ Cpp z := ⟨⟨hx.1.1.1, hx.1.2.1⟩, hx.2.1⟩
      rw [htr] at this
      exact this)
  rw [hU] at hadd
  have hcap : ∀ u ∈ VK, Homology.eulerChar ℚ (TopCat.of (AK u).space) ≤
      2 - ((edgesAt K u).ncard : ℤ) := by
    intro u hu
    have hu' := (hVK u).mp hu
    obtain ⟨hfin, -, hman, hconnu, hbd⟩ := hpiece u hu'
    let _ : Finite (AK u).faces := hfin.to_subtype
    have hEfin : (edgesAt K u).Finite := ht.facesFinite.subset fun e he => he.1
    let I := hEfin.toFinset
    have hI : (edgesAt K u).ncard = I.card := Set.ncard_eq_toFinset_card _ hEfin
    have hbd' : (@boundaryComplex _ _ _ (fun a b => Classical.propDecidable (a = b)) 2
        (AK u)).space = ⋃ e ∈ I, Ec e ∩ frontier XK.space := by
      have hIU : (⋃ e ∈ I, Ec e ∩ frontier XK.space) =
          ⋃ e ∈ edgesAt K u, Ec e ∩ frontier XK.space := by
        ext x
        simp [I]
      rw [hIU]
      convert hbd using 3
    have hle := IsCombinatorialManifoldWithBoundary.eulerChar_add_card_le_two (AK u) hman hconnu
      I (fun e => Ec e ∩ frontier XK.space)
      (fun e he => (h34 e ((hEfin.mem_toFinset).mp he).1 ((hEfin.mem_toFinset).mp he).2.1).1)
      (fun e he f hf hef => (hd.pseudoCellDisjoint e ((hEfin.mem_toFinset).mp he).1
        ((hEfin.mem_toFinset).mp he).2.1 f ((hEfin.mem_toFinset).mp hf).1
        ((hEfin.mem_toFinset).mp hf).2.1 hef).mono inter_subset_left inter_subset_left) hbd'
    rw [← eulerChar_eq_singular (AK u) ℚ, hI]
    omega
  have hsumle := Finset.sum_le_sum hcap
  have hcomb : 2 * eulerChar K = ∑ u ∈ VK, (2 - ((edgesAt K u).ncard : ℤ)) :=
    two_mul_eulerChar_eq_sum_edgesAt ht.oneDimensional
  have heq : ∑ u ∈ VK, Homology.eulerChar ℚ (TopCat.of (AK u).space) =
      ∑ u ∈ VK, (2 - ((edgesAt K u).ncard : ℤ)) := by
    have := hadd.2
    omega
  have hall := (Finset.sum_eq_sum_iff_of_le hcap).mp heq
  intro v hv _
  have hv' := hall v ((hVK v).mpr hv)
  rw [← eulerChar_eq_singular (AK v) ℚ] at hv'
  exact hv'

end Tube

end DifferentialGeometry.Topology.PiecewiseLinear
