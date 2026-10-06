/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.ThreeManifold.TorusCut.Compression
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.Moise252Producer

set_option autoImplicit false

/-!
# LT-P4 core: the Loop Theorem for a torus that is a boundary component of a combinatorial
3-manifold with boundary

No Ricci-flow vocabulary. A triangulation `h : |K| ≃ₜ W` of `W` by an oriented combinatorial
3-manifold with boundary, in which the image of an injective torus `τ` is one connected component
of `∂K`, yields from `¬ Injective π₁(τ)` an embedded essential loop of the torus that dies in `W`.
-/

noncomputable section
open Set Topology
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.PiecewiseLinear

namespace GC.LongTime.CuspP1
open GC.Topology
universe u v

section Loops
variable {S : Type u} {Y : Type v} [TopologicalSpace S] [TopologicalSpace Y]

theorem loopDegreeClass_one_mem_ker_LTP4 (τ : C(S, Y)) (γ : freeLoop S)
    (h : (τ.comp γ).Nullhomotopic) :
    loopDegreeClass γ 1 ∈ (FundamentalGroup.map τ (γ 0)).ker := by
  rw [MonoidHom.mem_ker, loopDegreeClass, intLoop_one]
  have hp : pathToCircle (circleToPath (⟨γ, rfl⟩ : basedCircleLoop (γ 0))) = γ :=
    congrArg Subtype.val ((basedPathCircleHomeomorph (γ 0)).apply_symm_apply ⟨γ, rfl⟩)
  apply Path.Homotopic.Quotient.eq.mpr
  apply (pathToCircle_nullhomotopic_iff
    ((circleToPath (⟨γ, rfl⟩ : basedCircleLoop (γ 0))).map τ.continuous)).mp
  rw [pathToCircle_natural, hp]
  exact h

end Loops


theorem exists_essential_embedded_null_of_cut_LTP4 {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [hdec : DecidableEq E] {W : Type v} [TopologicalSpace W]
    {τ : C(Torus, W)} (hτ : Function.Injective τ)
    (K : Geometry.SimplicialComplex ℝ E) [hKfin : Finite K.faces] (h : K.space ≃ₜ W)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hKo : IsOrientable 3 K)
    (c : ConnectedComponents (boundaryComplex 3 K).space)
    (hc : ∀ k : K.space, (k : E) ∈ (connectedComponentComplex (boundaryComplex 3 K) c).space ↔
      h k ∈ range τ)
    {x : Torus} (hx : ¬ Function.Injective (FundamentalGroup.map τ x)) :
    ∃ γ : freeLoop Torus, Topology.IsEmbedding γ ∧ ¬ γ.Nullhomotopic ∧
      loopDegreeClass γ 1 ∈ (FundamentalGroup.map τ (γ 0)).ker := by
  obtain rfl : hdec = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  classical
  set B := connectedComponentComplex (boundaryComplex 3 K) c with hBdef
  have hBK : B.space ⊆ K.space := by
    rw [hBdef, connectedComponentComplex_space]
    rintro _ ⟨z, -, rfl⟩
    exact boundaryComplex_space_subset 3 K z.2
  have hmemB : ∀ k : K.space, (k : E) ∈ B.space ↔ h k ∈ range τ := hc
  have hψmem : ∀ t, ((h.symm (τ t) : K.space) : E) ∈ B.space := fun t =>
    (hmemB _).mpr (by rw [h.apply_symm_apply]; exact mem_range_self t)
  let ψ : C(Torus, B.space) := ⟨fun t => ⟨h.symm (τ t), hψmem t⟩,
    (continuous_subtype_val.comp (h.symm.continuous.comp τ.continuous)).subtype_mk _⟩
  have hψinj : Function.Injective ψ := by
    intro s t hst
    have h1 : ((ψ s : B.space) : E) = ψ t := congrArg Subtype.val hst
    exact hτ (h.symm.injective (Subtype.ext h1))
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    obtain ⟨t, ht⟩ := (hmemB ⟨y, hBK hy⟩).mp hy
    refine ⟨t, Subtype.ext ?_⟩
    change ((h.symm (τ t) : K.space) : E) = y
    rw [ht, h.symm_apply_apply]
  let Ψ : Torus ≃ₜ B.space :=
    ψ.continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective ψ ⟨hψinj, hψsurj⟩)
  have hτΨ : ∀ t, τ t = h ⟨Ψ t, hBK (Ψ t).2⟩ := by
    intro t
    have hk : (⟨Ψ t, hBK (Ψ t).2⟩ : K.space) = h.symm (τ t) := Subtype.ext rfl
    rw [hk, h.apply_symm_apply]
  let ι : C(B.space, K.space) :=
    ⟨Set.inclusion hBK, continuous_inclusion _⟩
  obtain ⟨g, hgne, hgmap⟩ := exists_ne_one_map_eq_one_of_not_injective τ Ψ ι h hτΨ hx
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective g
  have hnn : ¬ IsNullHomotopic (pathToCircle p) := fun hnull =>
    hgne (Path.Homotopic.Quotient.eq.mpr ((pathToCircle_nullhomotopic_iff p).mp hnull))
  have hnull : IsNullHomotopic (ι.comp (pathToCircle p)) := by
    rw [← pathToCircle_natural ι (Ψ x) p]
    refine (pathToCircle_nullhomotopic_iff (p.map ι.continuous)).mpr ?_
    exact Path.Homotopic.Quotient.eq.mp hgmap
  obtain ⟨Δ, r, hr, hΔ, hmeet, hb, hess⟩ :=
    moise252 K hKfin hK hKo c hBK (pathToCircle p) hnull hnn
  obtain ⟨σ, hσc, hσi, hσball, hσsphere, -⟩ :=
    exists_continuous_injective_image_closedBall_eq_stdSimplex
  let R := Complex.orthonormalBasisOneI.repr
  have hstd : ∀ z : closedDisk, σ (R z) ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) := by
    intro z
    rw [← hσball]
    refine ⟨R z, ?_, rfl⟩
    have hz := z.2
    rw [Metric.mem_closedBall, dist_zero_right] at hz ⊢
    rwa [LinearIsometryEquiv.norm_map]
  have hbs : stdSimplexBoundary 2 ⊆ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) :=
    fun y hy => hy.1
  have hrc : ContinuousOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) :=
    hr.2.1.continuousOn
  let F : closedDisk → E := fun z => r (σ (R z))
  have hFΔ : ∀ z, F z ∈ Δ := fun z => hr.1.mapsTo (hstd z)
  have hFK : ∀ z, F z ∈ K.space := fun z => hΔ (hFΔ z)
  have hFc : Continuous F :=
    hrc.comp_continuous (hσc.comp (R.continuous.comp continuous_subtype_val)) hstd
  let d : C(closedDisk, W) :=
    ⟨fun z => h ⟨F z, hFK z⟩, h.continuous.comp (hFc.subtype_mk _)⟩
  have hβmem : ∀ θ : loopCircle,
      r (σ (planarCircleParam θ)) ∈ r '' stdSimplexBoundary 2 := fun θ =>
    ⟨σ (planarCircleParam θ),
      by rw [← hσsphere]; exact ⟨_, (planarCircleParam θ).2, rfl⟩, rfl⟩
  have hs : ∀ φ : loopCircle, σ (planarCircleParam φ) ∈
      Convexity.StdSimplex.coordinateSet ℝ (Fin 3) := fun φ => by
    rw [← hσball]
    exact ⟨_, Metric.sphere_subset_closedBall (planarCircleParam φ).2, rfl⟩
  let β₀ : loopCircle → r '' stdSimplexBoundary 2 := fun θ =>
    ⟨r (σ (planarCircleParam θ)), hβmem θ⟩
  have hβc : Continuous β₀ := (hrc.comp_continuous
    (hσc.comp (continuous_subtype_val.comp planarCircleParam.continuous)) hs).subtype_mk _
  have hβinj : Function.Injective β₀ := by
    intro θ θ' hθ
    have h1 : r (σ (planarCircleParam θ)) = r (σ (planarCircleParam θ')) :=
      congrArg Subtype.val hθ
    exact planarCircleParam.injective (Subtype.ext (hσi (hr.1.injOn (hs θ) (hs θ') h1)))
  have hβsurj : Function.Surjective β₀ := by
    rintro ⟨y, w, hw, rfl⟩
    rw [← hσsphere] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    refine ⟨planarCircleParam.symm ⟨v, hv⟩, Subtype.ext ?_⟩
    change r (σ (planarCircleParam (planarCircleParam.symm ⟨v, hv⟩))) = r (σ v)
    rw [Homeomorph.apply_symm_apply]
  let β : loopCircle ≃ₜ r '' stdSimplexBoundary 2 :=
    hβc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective β₀ ⟨hβinj, hβsurj⟩)
  have hkey : ∀ θ, F (diskBoundary θ) = (β θ : E) := fun θ => by
    change r (σ (R (AddCircle.toCircle θ : ℂ))) = r (σ (planarCircleParam θ))
    rw [planarCircleParam_apply]
  let γ : freeLoop Torus := ⟨fun θ => Ψ.symm ⟨β θ, hb (β θ).2⟩,
    Ψ.symm.continuous.comp ((continuous_subtype_val.comp β.continuous).subtype_mk _)⟩
  have hγd : τ.comp γ = diskTrace d := by
    ext θ
    change τ (Ψ.symm _) = h ⟨F (diskBoundary θ), hFK _⟩
    rw [hτΨ, Homeomorph.apply_symm_apply]
    exact congrArg h (Subtype.ext (hkey θ).symm)
  have hemb : Topology.IsEmbedding γ := by
    have h1 : Topology.IsEmbedding (fun θ => (⟨β θ, hb (β θ).2⟩ : B.space)) :=
      (Topology.IsEmbedding.inclusion hb).comp β.isEmbedding
    exact Ψ.symm.isEmbedding.comp h1
  refine ⟨γ, hemb, fun hγ => hess ?_, loopDegreeClass_one_mem_ker_LTP4 τ γ ?_⟩
  · have hn := (hγ.comp_right (Ψ : C(Torus, B.space))).comp_left
      (β.symm : C(r '' stdSimplexBoundary 2, loopCircle))
    have heq : (⟨Set.inclusion hb, continuous_inclusion hb⟩ :
        C(r '' stdSimplexBoundary 2, B.space)) =
        ((Ψ : C(Torus, B.space)).comp γ).comp
          (β.symm : C(r '' stdSimplexBoundary 2, loopCircle)) := by
      refine ContinuousMap.ext fun y => Subtype.ext ?_
      change (y : E) = ((Ψ (Ψ.symm ⟨β (β.symm y), _⟩) : B.space) : E)
      rw [Homeomorph.apply_symm_apply]
      exact congrArg Subtype.val (β.apply_symm_apply y).symm
    rw [heq]
    exact hn
  · rw [hγd]
    exact diskTrace_nullhomotopic d

end GC.LongTime.CuspP1
