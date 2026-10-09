import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspFinitePatch
import DifferentialGeometry.Topology.Manifold.RegularLevel.BoundarySublevelProduct

/-!
# The closed inner collar as a torus product (F-e, E6 kernel on a cusp carrier)

Row E6 (BCP01.c, blueprint 207B:8146–8153): the closure of the inner collar of the boundary
component `X = ∂_i W` cut by a regular smooth level is smoothly diffeomorphic, as a pair, to
`(T² × [0, 1], T² × {0})`, with the label `X` kept.

`CuspEmbedding.exists_sublevel_diffeomorph_torus_Icc`: let `e : CuspEmbedding W g K δ X` and let
`F` be a smooth function on `W` with no critical point on `{F ≤ r}`, equal to `a < r` on `X`, and
such that the only boundary points of `W` in `{F ≤ r}` are those of `X`. Then `{F ≤ r}` (a
manifold with boundary `X ∪ {F = r}`, lane SUB-BDY) is diffeomorphic to `T² × [a, r]`, carrying
the second coordinate to `F` and `T² × {a}` onto `X`.

The bottom boundary `X` is parametrised by the `C^{K+1}` injective immersion `t ↦ e (t, 0)`
(`CuspEmbedding.boundary_image`, `boundary_preimage`); the torus factor is obtained from it by the
finite-order inverse function theorem and W-1's upgrade, so the cusp embedding need not be smooth.
The existence of such an `F` built from the BCP01 height `η` (smooth height up to the boundary
with exact level on `X`) is the remaining binding step E6(i).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- The boundary torus of a cusp embedding: `t ↦ e (t, 0)` is a `C^{K+1}` injective immersion
onto `X` by boundary points. -/
theorem CuspEmbedding.boundary_param {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) :
    ContMDiff torusModel W.model (K + 1) (fun t : Torus => e.toFun (t, halfZero)) ∧
      Injective (fun t : Torus => e.toFun (t, halfZero)) ∧
      (∀ t, Injective (mfderiv torusModel W.model (fun t : Torus => e.toFun (t, halfZero)) t)) ∧
      ∀ t : Torus, W.model.IsBoundaryPoint (e.toFun (t, halfZero)) := by
  have hz : ∀ t : Torus, ((t, halfZero) : CuspHalfSpace) ∈ cuspDomain := fun t => by
    change (0 : ℝ) < 100
    norm_num
  have hι : ∀ t : Torus, HasMFDerivAt torusModel halfCollarModel
      (fun t : Torus => ((t, halfZero) : CuspHalfSpace)) t
      ((ContinuousLinearMap.id ℝ (TangentSpace torusModel t)).prod
        (0 : TangentSpace torusModel t →L[ℝ] TangentSpace (𝓡∂ 1) halfZero)) :=
    fun t => (hasMFDerivAt_id t).prodMk (hasMFDerivAt_const halfZero t)
  have he : ∀ t : Torus, ContMDiffAt halfCollarModel W.model (K + 1) e.toFun (t, halfZero) :=
    fun t => e.contMDiffOn.contMDiffAt (isOpen_cuspDomain.mem_nhds (hz t))
  refine ⟨fun t => (he t).comp t (contMDiff_id.prodMk contMDiff_const).contMDiffAt,
    fun t₁ t₂ h => ?_, fun t => ?_, fun t => (e.boundary_preimage (hz t)).mpr rfl⟩
  · have h' : (⟨(t₁, halfZero), hz t₁⟩ : cuspDomain) = ⟨(t₂, halfZero), hz t₂⟩ :=
      e.isEmbedding.injective h
    exact congrArg (fun p : cuspDomain => p.1.1) h'
  · have hed : MDifferentiableAt halfCollarModel W.model e.toFun (t, halfZero) :=
      (he t).mdifferentiableAt (by simp)
    have hcomp := (hed.hasMFDerivAt.comp t (hι t)).mfderiv
    change mfderiv torusModel W.model (e.toFun ∘ fun t : Torus => ((t, halfZero) : CuspHalfSpace))
      t = _ at hcomp
    change Injective (mfderiv torusModel W.model
      (e.toFun ∘ fun t : Torus => ((t, halfZero) : CuspHalfSpace)) t)
    rw [hcomp]
    intro v w hvw
    have h := e.immersion _ (hz t) hvw
    exact congrArg Prod.fst h

/-- **E6 kernel on a cusp carrier.** A smooth `F` on `W` without critical points on `{F ≤ r}`,
equal to `a < r` on the boundary component `X` of a cusp embedding, and whose sublevel meets `∂W`
only in `X`, has a sublevel `{F ≤ r}` that is a compact manifold with boundary `X ∪ {F = r}`,
diffeomorphic to `T² × [a, r]` carrying the second coordinate to `F` and `T² × {a}` onto `X`. -/
theorem CuspEmbedding.exists_sublevel_diffeomorph_torus_Icc {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {F : W.Carrier → ℝ} {a r : ℝ} (har : a < r)
    (hF : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ F)
    (hreg : ∀ x, F x ≤ r → mfderiv W.model 𝓘(ℝ, ℝ) F x ≠ 0) (hr : ∃ x, F x = r)
    (hXa : ∀ x ∈ X, F x = a) (hbd : ∀ x, W.model.IsBoundaryPoint x → F x ≤ r → x ∈ X) :
    ∃ cs : ChartedSpace (EuclideanHalfSpace 3) {x : W.Carrier // F x ≤ r},
      letI := cs
      IsManifold (𝓡∂ 3) ∞ {x : W.Carrier // F x ≤ r} ∧
      ContMDiff (𝓡∂ 3) W.model ∞ (fun x : {x : W.Carrier // F x ≤ r} => x.1) ∧
      (∀ y : {x : W.Carrier // F x ≤ r}, (𝓡∂ 3).IsBoundaryPoint y ↔ (y.1 ∈ X ∨ F y.1 = r)) ∧
      haveI : Fact (a < r) := ⟨har⟩
      ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) (𝓡∂ 3) (Torus × Icc a r)
          {x : W.Carrier // F x ≤ r} ∞,
        (∀ p, F (D p).1 = p.2.1) ∧ ∀ p, (D p).1 ∈ X ↔ p.2.1 = a := by
  obtain ⟨hj, hjinj, hjd, hjbd⟩ := e.boundary_param
  have hmem : ∀ x, x ∈ range (fun t : Torus => e.toFun (t, halfZero)) ↔ x ∈ X :=
    fun x => Set.ext_iff.mp e.boundary_image x
  have hja : ∀ t : Torus, F (e.toFun (t, halfZero)) = a := fun t =>
    hXa _ ((hmem _).mp (mem_range_self t))
  have hjrange : ∀ x, W.model.IsBoundaryPoint x → F x ≤ r →
      x ∈ range (fun t : Torus => e.toFun (t, halfZero)) := fun x hx hxr =>
    (hmem x).mpr (hbd x hx hxr)
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) = 2 := by
    rw [Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin]
  cases W with
  | mk k M orientation =>
    cases k with
    | closed =>
      obtain ⟨t₀⟩ := (inferInstance : Nonempty Torus)
      have hh := ModelWithCorners.Boundaryless.boundary_eq_empty (I := 𝓡 3) (M := M)
      have hb : e.toFun (t₀, halfZero) ∈ (𝓡 3).boundary M := hjbd t₀
      rw [hh] at hb
      exact hb.elim
    | withBoundary =>
      obtain ⟨cs, hm, hval, hiff, D, hDF, hDX⟩ :=
        exists_boundarySublevel_diffeomorph_of_boundary_param (m := 2) (J := torusModel)
          (T := Torus) hdim har hF hreg hr (k := K + 1) (by omega) hj hjinj hjd hjbd hja
          hjrange
      exact ⟨cs, hm, hval, fun y => (hiff y).trans (or_congr_left (hmem y.1)), D, hDF,
        fun p => (hmem _).symm.trans (hDX p)⟩

end DifferentialGeometry.Geometry.Collapse
