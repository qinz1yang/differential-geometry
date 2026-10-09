import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspHeightSecondOrder
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspTaylorPatch
import DifferentialGeometry.Topology.VectorField.PullbackExtendBracket
import DifferentialGeometry.Geometry.Connection.Hessian.Scalar
import DifferentialGeometry.Geometry.Connection.Hessian.ChartEstimate
import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.FiniteJet
import DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Formula
import DifferentialGeometry.Geometry.Coordinates.Frame.TangentProduct
import DifferentialGeometry.Bundle.Frame

/-!
# The Hessian of the collar height (statement G, clause (v): the boundary is convex)

For a cusp embedding `e : CuspEmbedding W g K δ X` with `K ≥ 1` and `0 ≤ δ ≤ 1/100`, let
`ζ = z ∘ e⁻¹` be the collar height and `Hess ζ` its Hessian for the Levi-Civita connection of `g`
(the EXISTING Hessian `(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)`).

* `CuspEmbedding.three_eighths_inner_le_neg_hessian_height` (core bound): on the whole collar
  `e '' cuspDomain`, boundary included, every `v` with `dζ(v) = 0` has
  `(3/8)·g(v,v) ≤ −Hess ζ(v,v)`;
* `CuspEmbedding.inner_div_four_mul_abs_le_neg_hessian_height` (clause (v), corrected chart-free
  form, see `docs/geometrization/chapter13/errata-boundary-geometry-G-II-20261004.md`): for
  `y ∈ X`, `g(v,v)/4 · |dζ(u)| ≤ −Hess ζ(v,v) · √g(u,u)`, i.e. `II ≥ g/4` for the outward normal
  `−grad ζ / ‖dζ‖_g`.

Route (valid at boundary points): the Koszul formula of the tree's Levi-Civita connection
(`leviCivitaConnectionOfMetric_inner_eq_koszulScalar`, any point) for the pushforwards by `e` of
fields that are constant in the cusp chart at `p` (their brackets vanish), compared with the
Koszul formula of the model metric and with the Leibniz evaluation of `∇_H (e^*g − H)` (G1.a);
the model value `Hess_H z(a,a) = −½ H(a,a)` on horizontal vectors comes from the explicit metric.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Function DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.TensorLieDeriv
open GC.Endpoint
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "Ec" => (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1)
local notation "Et" => EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)

section Fields

private theorem cuspHess_t2Half : T2Space (EuclideanHalfSpace 1) := by
  unfold EuclideanHalfSpace
  infer_instance

attribute [local instance] cuspHess_t2Half

/-- A chart-constant field is the inverse trivialization applied to its value at the base point. -/
private theorem cuspHess_extend_eq_symmL {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] (x : M) (v : TangentSpace I x) {y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace I) x).baseSet) :
    FiberBundle.extend E v y = (trivializationAt E (TangentSpace I) x).symmL ℝ y v := by
  have hc : (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x v = v := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (mem_chart_source H x)]
    exact (tangentBundleCore I M).coordChange_self (achart H x) x (by simp) v
  rw [DifferentialGeometry.VectorField.fiberBundleExtend_eq_symmL x v hy, hc]

private theorem cuspHess_extend_smooth {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] (x : M) (v : TangentSpace I x) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (⟨y, FiberBundle.extend E v y⟩ : TotalSpace E (TangentSpace I)))
      (trivializationAt E (TangentSpace I) x).baseSet := by
  set t := trivializationAt E (TangentSpace I) x
  suffices ContMDiffOn I 𝓘(ℝ, E) ∞ (fun y ↦ (t ⟨y, FiberBundle.extend E v y⟩).2) t.baseSet by
    intro y hy
    rw [t.contMDiffWithinAt_section _ hy]
    exact this y hy
  let w : E := t.continuousLinearMapAt ℝ x v
  have : ContMDiffOn I 𝓘(ℝ, E) ∞ (fun (_y : M) ↦ w) t.baseSet := contMDiffOn_const
  refine this.congr (fun y hy ↦ ?_)
  rw [DifferentialGeometry.VectorField.fiberBundleExtend_eq_symmL x v hy, t.symmL_apply hy,
    t.apply_mk_symm hy]

/-- Smooth global vector fields on the cusp agreeing near `p` with all chart-constant fields. -/
theorem cusp_exists_chartConstant_sections (p : CuspHalfSpace) :
    ∃ V : Ec → ContMDiffSection halfCollarModel Ec ∞
      (TangentSpace halfCollarModel : CuspHalfSpace → Type _),
      ∀ᶠ q in 𝓝 p, ∀ c : Ec, V c q = FiberBundle.extend (E := (TangentSpace halfCollarModel : CuspHalfSpace → Type _)) Ec
        (x := p) c q := by
  obtain ⟨V, hV⟩ := exists_contMDiffSection_eqOn_nhd (I := halfCollarModel) (F := Ec)
    (V := (TangentSpace halfCollarModel : CuspHalfSpace → Type _)) (n := ⊤)
    (s := fun c : Ec => FiberBundle.extend (E := (TangentSpace halfCollarModel : CuspHalfSpace → Type _)) Ec
        (x := p) c)
    (fun c => cuspHess_extend_smooth p c)
    (trivializationAt Ec (TangentSpace halfCollarModel) p).open_baseSet
    (FiberBundle.mem_baseSet_trivializationAt' p)
  exact ⟨V, hV⟩

/-- On the cusp, near `p`, every chart-constant field at `p` is the product of the torus
chart-constant field of its torus part (the inverse torus trivialization) and its constant height
part. -/
theorem cusp_extend_eq_prod (p : CuspHalfSpace) :
    ∀ᶠ q in 𝓝 p, ∀ c : Ec, FiberBundle.extend (E := (TangentSpace halfCollarModel : CuspHalfSpace → Type _)) Ec
        (x := p) c q =
      (((trivializationAt Et (TangentSpace torusModel) p.1).symmL ℝ q.1 c.1, c.2) :
        TangentSpace halfCollarModel q) := by
  have hb : p ∈ (trivializationAt Ec (TangentSpace halfCollarModel) p).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' p
  filter_upwards [(trivializationAt Ec (TangentSpace halfCollarModel) p).open_baseSet.mem_nhds hb]
    with q hq c
  rw [cuspHess_extend_eq_symmL p c hq, trivializationAt_symmL_prod p q hq c]
  congr 1
  have hq₂ : q.2 ∈ (chartAt (EuclideanHalfSpace 1) p.2).source := by simp
  rw [TangentBundle.symmL_trivializationAt_eq_core hq₂]
  exact (tangentBundleCore (𝓡∂ 1) (EuclideanHalfSpace 1)).coordChange_self
    (achart (EuclideanHalfSpace 1) p.2) q.2 (by simp) c.2

/-- The inverse torus trivialization at the base point is the identity. -/
theorem torus_symmL_trivializationAt_self (t : Torus) (v : Et) :
    (trivializationAt Et (TangentSpace torusModel) t).symmL ℝ t v = v := by
  have h := cuspHess_extend_eq_symmL (I := torusModel) t v
    (FiberBundle.mem_baseSet_trivializationAt' t)
  exact h.symm.trans (FiberBundle.extend_apply_self (E := (TangentSpace torusModel : Torus → Type _))
    Et (x := t) v)

end Fields

section Main

attribute [local instance] cuspHess_t2Half

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
  {δ : ℝ} {X : Set W.Carrier}

/-- A smooth metric applied to two `C¹` vector fields is `C¹`. -/
private theorem cuspHess_contMDiffAt_inner {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (G : SmoothRiemannianMetric I M) {U U' : (x : M) → TangentSpace I x} {x : M}
    (hU : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun y => (⟨y, U y⟩ : TotalSpace E (TangentSpace I))) x)
    (hU' : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun y => (⟨y, U' y⟩ : TotalSpace E (TangentSpace I))) x) :
    ContMDiffAt I 𝓘(ℝ, ℝ) 1 (fun y => G.inner y (U y) (U' y)) x := by
  have hg : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
      (fun y => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) y (G.inner y)) x :=
    (G.contMDiff.of_le (by simp)).contMDiffAt
  have h := ContMDiffAt.clm_bundle_apply₂ (E₁ := fun b : M => TangentSpace I b)
    (E₂ := fun b : M => TangentSpace I b) (E₃ := fun _ : M => ℝ) (b := fun y => y)
    (ψ := fun y => G.inner y) hg hU hU'
  rw [contMDiffAt_totalSpace] at h
  exact h.2

/-- The chart representative at `p` of the metric error of a cusp embedding is differentiable
(within the model range) at the chart image of `p`, boundary points included (`K ≥ 1`). -/
theorem CuspEmbedding.differentiableWithinAt_chart_metricError (e : CuspEmbedding W g K δ X)
    (hK : 1 ≤ K) {p : CuspHalfSpace} (hp : p ∈ cuspDomain) :
    DifferentiableWithinAt ℝ
      (tensor0SModelInChart (𝕜 := ℝ) (I := halfCollarModel) 2 p
        (cuspMetricError g e.cusp e.toFun))
      (range halfCollarModel) (extChartAt halfCollarModel p p) := by
  let σ : Ec → (q : CuspHalfSpace) → TangentSpace halfCollarModel q := fun u q =>
    (trivializationAt Ec (TangentSpace halfCollarModel) p).symmL ℝ q u
  have hσ : ∀ u, ContMDiffAt halfCollarModel (halfCollarModel.prod 𝓘(ℝ, Ec)) 1
      (fun q => (⟨q, σ u q⟩ : TotalSpace Ec (TangentSpace halfCollarModel))) p :=
    fun u => DifferentialGeometry.Geometry.contMDiffAt_tangent_symmL_frame p u
  let Φ : Ec → Ec → CuspHalfSpace → ℝ := fun u w q =>
    g.inner (e.toFun q) (mfderiv halfCollarModel W.model e.toFun q (σ u q))
        (mfderiv halfCollarModel W.model e.toFun q (σ w q)) -
      e.cusp.metric.inner q (σ u q) (σ w q)
  have hΦ : ∀ u w, ContMDiffAt halfCollarModel 𝓘(ℝ, ℝ) 1 (Φ u w) p := fun u w =>
    (e.contMDiffAt_pullback_inner hK hp (hσ u) (hσ w)).sub
      (cuspHess_contMDiffAt_inner e.cusp.metric (hσ u) (hσ w))
  let B : Ec → Ec →L[ℝ] Ec →L[ℝ] ℝ := fun y =>
    (localPullInner (I := halfCollarModel) (J := W.model) g e.toFun
        ((extChartAt halfCollarModel p).symm y) -
      e.cusp.metric.inner ((extChartAt halfCollarModel p).symm y)).bilinearComp
      ((trivializationAt Ec (TangentSpace halfCollarModel) p).symmL ℝ
        ((extChartAt halfCollarModel p).symm y))
      ((trivializationAt Ec (TangentSpace halfCollarModel) p).symmL ℝ
        ((extChartAt halfCollarModel p).symm y))
  have hchart : tensor0SModelInChart (𝕜 := ℝ) (I := halfCollarModel) 2 p
      (cuspMetricError g e.cusp e.toFun) = fun y => bilinToTensor0SModel Ec (B y) := by
    funext y
    ext m
    rw [tensor0SModelInChart_apply]
    rfl
  have hB : ContDiffWithinAt ℝ 1 B (range halfCollarModel) (extChartAt halfCollarModel p p) := by
    refine contDiffWithinAt_clm_apply.mpr fun u => contDiffWithinAt_clm_apply.mpr fun w => ?_
    have hsymm : ContMDiffWithinAt 𝓘(ℝ, Ec) halfCollarModel 1 (extChartAt halfCollarModel p).symm
        (range halfCollarModel) (extChartAt halfCollarModel p p) := by
      simpa using contMDiffWithinAt_extChartAt_symm_range_self (I := halfCollarModel) (n := 1) p
    have hΦc : ContMDiffAt halfCollarModel 𝓘(ℝ, ℝ) 1 (Φ u w)
        ((extChartAt halfCollarModel p).symm (extChartAt halfCollarModel p p)) := by
      rw [extChartAt_to_inv]
      exact hΦ u w
    have hcomp := hΦc.comp_contMDiffWithinAt (x := extChartAt halfCollarModel p p) hsymm
    exact contMDiffWithinAt_iff_contDiffWithinAt.mp hcomp
  rw [hchart]
  exact ((bilinToTensor0SModel Ec).contDiff.contDiffAt.comp_contDiffWithinAt _ hB).differentiableWithinAt
    (by norm_num)

/-- **The Hessian of the collar height on a pushforward slot.** If the height component of a
smooth vector field `V` on the cusp is constant near `p`, then
`Hess ζ (v, De(V p)) = − dζ(∇_v (e_* V))`, boundary points included (`K ≥ 1`). -/
theorem CuspEmbedding.hessian_height_pushforward (e : CuspEmbedding W g K δ X) (hK : 1 ≤ K)
    {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    (V : ContMDiffSection halfCollarModel Ec ∞
      (TangentSpace halfCollarModel : CuspHalfSpace → Type _))
    (hV : ∀ᶠ q in 𝓝 p, (V q).2 0 = (V p).2 0) (v : TangentSpace W.model (e.toFun p)) :
    (CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
        (fun y => (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p) v
        (mfderiv halfCollarModel W.model e.toFun p (V p)) =
      -mvfderiv W.model (fun y => (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p)
        ((LeviCivita g) (VectorField.mpullback W.model halfCollarModel
          (invFunOn e.toFun cuspDomain) (fun q => V q)) (e.toFun p) v) := by
  set ζ : W.Carrier → ℝ := fun y => (invFunOn e.toFun cuspDomain y).2.val 0 with hζ
  set P := VectorField.mpullback W.model halfCollarModel (invFunOn e.toFun cuspDomain)
    (fun q => V q) with hPdef
  have hinvC2 := e.contMDiffAt_invFunOn_two hK hp
  have hinvp : invFunOn e.toFun cuspDomain (e.toFun p) = p :=
    e.injOn_cuspDomain.leftInvOn_invFunOn hp
  have hP : MDifferentiableAt W.model (W.model.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))
      (fun y => (⟨y, P y⟩ : TotalSpace (EuclideanSpace ℝ (Fin 3)) (TangentSpace W.model)))
      (e.toFun p) :=
    MDifferentiableAt.mpullback_vectorField ((V.contMDiff _).mdifferentiableAt (by simp)) hinvC2
      (e.isInvertible_mfderiv_invFunOn hp) le_rfl
  have hζ2 : ContMDiffAt W.model 𝓘(ℝ, ℝ) 2 ζ (e.toFun p) :=
    (e.contMDiffOn_height_invFunOn_two hK).contMDiffAt
      (e.isOpen_image_cuspDomain.mem_nhds (mem_image_of_mem _ hp))
  have hσ : ContMDiffAt W.model (W.model.prod 𝓘(ℝ, ℝ)) 2 (fun y =>
      (⟨y, ζ y⟩ : TotalSpace ℝ (Bundle.Trivial W.Carrier ℝ))) (e.toFun p) :=
    (contMDiffAt_section (F := ℝ) (E := Bundle.Trivial W.Carrier ℝ) (e.toFun p)).mpr hζ2
  have hcov : CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.trivial W.model W.Carrier ℝ) ∞ :=
    inferInstance
  have hD := (hcov.contMDiffAt (m := 1) hσ (by norm_num)).mdifferentiableAt (by simp)
  have h := (CovariantDerivative.trivial W.model W.Carrier ℝ).hessian_apply (LeviCivita g) hD hP v
  simp only [CovariantDerivative.trivial_apply] at h
  have hPp : P (e.toFun p) = mfderiv halfCollarModel W.model e.toFun p (V p) :=
    e.mpullback_invFunOn_apply hp (fun q => V q)
  rw [hPp] at h
  rw [h]
  have hconst : (fun y => mvfderiv W.model ζ y (P y)) =ᶠ[𝓝 (e.toFun p)]
      fun _ => (V p).2 0 := by
    have h1 : ∀ᶠ y in 𝓝 (e.toFun p), (V (invFunOn e.toFun cuspDomain y)).2 0 = (V p).2 0 := by
      have ht := hinvC2.continuousAt.tendsto
      rw [hinvp] at ht
      exact ht.eventually hV
    filter_upwards [e.isOpen_image_cuspDomain.mem_nhds (mem_image_of_mem _ hp), h1] with y hy hy1
    obtain ⟨q, hq, rfl⟩ := hy
    have hPq : P (e.toFun q) = mfderiv halfCollarModel W.model e.toFun q (V q) :=
      e.mpullback_invFunOn_apply hq (fun q => V q)
    rw [hPq]
    rw [e.injOn_cuspDomain.leftInvOn_invFunOn hq] at hy1
    have hd := e.mfderiv_height_invFunOn_mfderiv hq (V q)
    rw [← hy1, ← hd]
    rfl
  have h0 : mvfderiv W.model (fun y => mvfderiv W.model ζ y (P y)) (e.toFun p) v = 0 := by
    rw [mvfderiv_eq_of_eventuallyEq hconst, mvfderiv_const]
    rfl
  rw [h0, zero_sub]

/-- The Koszul formula for three differentiable vector fields whose pairwise brackets vanish at
`x` (boundary points allowed). -/
private theorem cuspHess_koszul {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (G : SmoothRiemannianMetric I M) {X Y Z : (x : M) → TangentSpace I x} {x : M}
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun y => (⟨y, X y⟩ : TotalSpace E (TangentSpace I))) x)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun y => (⟨y, Y y⟩ : TotalSpace E (TangentSpace I))) x)
    (hZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun y => (⟨y, Z y⟩ : TotalSpace E (TangentSpace I))) x)
    (hXY : VectorField.mlieBracket I X Y x = 0) (hYZ : VectorField.mlieBracket I Y Z x = 0)
    (hZX : VectorField.mlieBracket I Z X x = 0) :
    G.inner x ((leviCivitaConnectionOfMetric G Y x) (X x)) (Z x) =
      (1 / 2 : ℝ) * (mvfderiv I (fun y => G.inner y (Y y) (Z y)) x (X x) +
        mvfderiv I (fun y => G.inner y (Z y) (X y)) x (Y x) -
        mvfderiv I (fun y => G.inner y (X y) (Y y)) x (Z x)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h := leviCivitaConnectionOfMetric_inner_eq_koszulScalar G X Y Z x hX hY hZ
  rw [h]
  simp only [koszulScalar, directionalDerivAlong, hXY, hYZ, hZX, map_zero, sub_zero, add_zero]

/-- **Koszul formula for pushforwards of commuting fields.** For smooth fields `Va, Vb, Vc` on the
cusp with vanishing brackets at `p`, the Levi-Civita connection of `g` on their pushforwards by
`e` is computed by the derivatives at `p` of the pulled-back inner products (`K ≥ 1`, boundary
points included). -/
theorem CuspEmbedding.inner_leviCivita_pushforward (e : CuspEmbedding W g K δ X) (hK : 1 ≤ K)
    {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    (Va Vb Vc : ContMDiffSection halfCollarModel Ec ∞
      (TangentSpace halfCollarModel : CuspHalfSpace → Type _))
    (hab : VectorField.mlieBracket halfCollarModel (fun q => Va q) (fun q => Vb q) p = 0)
    (hbc : VectorField.mlieBracket halfCollarModel (fun q => Vb q) (fun q => Vc q) p = 0)
    (hca : VectorField.mlieBracket halfCollarModel (fun q => Vc q) (fun q => Va q) p = 0) :
    g.inner (e.toFun p)
        ((leviCivitaConnectionOfMetric g (VectorField.mpullback W.model halfCollarModel
          (invFunOn e.toFun cuspDomain) (fun q => Vb q)) (e.toFun p))
          (mfderiv halfCollarModel W.model e.toFun p (Va p)))
        (mfderiv halfCollarModel W.model e.toFun p (Vc p)) =
      (1 / 2 : ℝ) *
        (mvfderiv halfCollarModel (fun q => g.inner (e.toFun q)
            (mfderiv halfCollarModel W.model e.toFun q (Vb q))
            (mfderiv halfCollarModel W.model e.toFun q (Vc q))) p (Va p) +
          mvfderiv halfCollarModel (fun q => g.inner (e.toFun q)
            (mfderiv halfCollarModel W.model e.toFun q (Vc q))
            (mfderiv halfCollarModel W.model e.toFun q (Va q))) p (Vb p) -
          mvfderiv halfCollarModel (fun q => g.inner (e.toFun q)
            (mfderiv halfCollarModel W.model e.toFun q (Va q))
            (mfderiv halfCollarModel W.model e.toFun q (Vb q))) p (Vc p)) := by
  have hinvC2 := e.contMDiffAt_invFunOn_two hK hp
  have hinvp : invFunOn e.toFun cuspDomain (e.toFun p) = p := e.injOn_cuspDomain.leftInvOn_invFunOn hp
  let P : ContMDiffSection halfCollarModel Ec ∞
      (TangentSpace halfCollarModel : CuspHalfSpace → Type _) →
      (y : W.Carrier) → TangentSpace W.model y := fun V =>
    VectorField.mpullback W.model halfCollarModel (invFunOn e.toFun cuspDomain)
      (fun q => V q)
  have hPd : ∀ V : ContMDiffSection halfCollarModel Ec ∞
      (TangentSpace halfCollarModel : CuspHalfSpace → Type _),
      MDifferentiableAt W.model (W.model.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))
        (fun y => (⟨y, P V y⟩ : TotalSpace (EuclideanSpace ℝ (Fin 3)) (TangentSpace W.model)))
        (e.toFun p) := fun V =>
    MDifferentiableAt.mpullback_vectorField ((V.contMDiff _).mdifferentiableAt (by simp)) hinvC2
      (e.isInvertible_mfderiv_invFunOn hp) le_rfl
  have hPp : ∀ V : ContMDiffSection halfCollarModel Ec ∞
      (TangentSpace halfCollarModel : CuspHalfSpace → Type _),
      P V (e.toFun p) = mfderiv halfCollarModel W.model e.toFun p (V p) := fun V =>
    e.mpullback_invFunOn_apply hp (fun q => V q)
  have hbr : ∀ V V' : ContMDiffSection halfCollarModel Ec ∞
      (TangentSpace halfCollarModel : CuspHalfSpace → Type _),
      VectorField.mlieBracket halfCollarModel (fun q => V q) (fun q => V' q) p = 0 →
      VectorField.mlieBracket W.model (P V) (P V') (e.toFun p) = 0 := by
    intro V V' h
    refine DifferentialGeometry.VectorField.mlieBracket_mpullback_eq_zero hinvC2
      ((V.contMDiff _).mdifferentiableAt (by simp)) ((V'.contMDiff _).mdifferentiableAt (by simp)) ?_
    rw [hinvp]
    exact h
  -- the pulled-back inner products
  have hfun : ∀ V V' : ContMDiffSection halfCollarModel Ec ∞
      (TangentSpace halfCollarModel : CuspHalfSpace → Type _),
      (fun y => g.inner y (P V y) (P V' y)) =ᶠ[𝓝 (e.toFun p)]
        (fun q => g.inner (e.toFun q) (mfderiv halfCollarModel W.model e.toFun q (V q))
          (mfderiv halfCollarModel W.model e.toFun q (V' q))) ∘ invFunOn e.toFun cuspDomain := by
    intro V V'
    filter_upwards [e.isOpen_image_cuspDomain.mem_nhds (mem_image_of_mem _ hp)] with y hy
    obtain ⟨q, hq, rfl⟩ := hy
    have h1 : P V (e.toFun q) = mfderiv halfCollarModel W.model e.toFun q (V q) :=
      e.mpullback_invFunOn_apply hq (fun q => V q)
    have h2 : P V' (e.toFun q) = mfderiv halfCollarModel W.model e.toFun q (V' q) :=
      e.mpullback_invFunOn_apply hq (fun q => V' q)
    rw [comp_apply, h1, h2]
    exact (congrArg (fun r => g.inner (e.toFun r) (mfderiv halfCollarModel W.model e.toFun r (V r))
      (mfderiv halfCollarModel W.model e.toFun r (V' r)))
      (e.injOn_cuspDomain.leftInvOn_invFunOn hq)).symm
  have hdir : ∀ V V' V'' : ContMDiffSection halfCollarModel Ec ∞
      (TangentSpace halfCollarModel : CuspHalfSpace → Type _),
      mvfderiv W.model (fun y => g.inner y (P V y) (P V' y)) (e.toFun p) (P V'' (e.toFun p)) =
        mvfderiv halfCollarModel (fun q => g.inner (e.toFun q)
          (mfderiv halfCollarModel W.model e.toFun q (V q))
          (mfderiv halfCollarModel W.model e.toFun q (V' q))) p (V'' p) := by
    intro V V' V''
    rw [mvfderiv_eq_of_eventuallyEq (hfun V V'), hPp V'']
    exact e.mvfderiv_comp_invFunOn hp
      ((e.contMDiffAt_pullback_inner hK hp ((V.contMDiff p).of_le (by simp))
        ((V'.contMDiff p).of_le (by simp))).mdifferentiableAt one_ne_zero) (V'' p)
  have hk := cuspHess_koszul g (hPd Va) (hPd Vb) (hPd Vc) (hbr Va Vb hab) (hbr Vb Vc hbc)
    (hbr Vc Va hca)
  rw [hdir Vb Vc Va, hdir Vc Va Vb, hdir Va Vb Vc, hPp Va, hPp Vc] at hk
  exact hk

/-- **Leibniz evaluation of `∇_H (e^*g − H)` on smooth fields (G1.a for the cusp).** -/
theorem CuspEmbedding.metricCovariantDerivative_metricError_apply (e : CuspEmbedding W g K δ X)
    (hK : 1 ≤ K) {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    (Vx Vy Vw : ContMDiffSection halfCollarModel Ec ∞
      (TangentSpace halfCollarModel : CuspHalfSpace → Type _)) :
    metricCovariantDerivative e.cusp.metric 2 (cuspMetricError g e.cusp e.toFun) p
        (Fin.cons (Vx p) ![Vy p, Vw p]) =
      mvfderiv halfCollarModel (fun q => g.inner (e.toFun q)
          (mfderiv halfCollarModel W.model e.toFun q (Vy q))
          (mfderiv halfCollarModel W.model e.toFun q (Vw q))) p (Vx p) -
        mvfderiv halfCollarModel (fun q => e.cusp.metric.inner q (Vy q) (Vw q)) p (Vx p) -
        ((g.inner (e.toFun p)
            (mfderiv halfCollarModel W.model e.toFun p
              (leviCivitaConnectionOfMetric e.cusp.metric (fun q => Vy q) p (Vx p)))
            (mfderiv halfCollarModel W.model e.toFun p (Vw p)) -
          e.cusp.metric.inner p (leviCivitaConnectionOfMetric e.cusp.metric (fun q => Vy q) p (Vx p))
            (Vw p)) +
         (g.inner (e.toFun p) (mfderiv halfCollarModel W.model e.toFun p (Vy p))
            (mfderiv halfCollarModel W.model e.toFun p
              (leviCivitaConnectionOfMetric e.cusp.metric (fun q => Vw q) p (Vx p))) -
          e.cusp.metric.inner p (Vy p)
            (leviCivitaConnectionOfMetric e.cusp.metric (fun q => Vw q) p (Vx p)))) := by
  have hĜ : MDifferentiableAt halfCollarModel 𝓘(ℝ, ℝ) (fun q => g.inner (e.toFun q)
      (mfderiv halfCollarModel W.model e.toFun q (Vy q))
      (mfderiv halfCollarModel W.model e.toFun q (Vw q))) p :=
    (e.contMDiffAt_pullback_inner hK hp ((Vy.contMDiff p).of_le (by simp))
      ((Vw.contMDiff p).of_le (by simp))).mdifferentiableAt one_ne_zero
  have hHd : MDifferentiableAt halfCollarModel 𝓘(ℝ, ℝ)
      (fun q => e.cusp.metric.inner q (Vy q) (Vw q)) p :=
    (cuspHess_contMDiffAt_inner e.cusp.metric ((Vy.contMDiff p).of_le (by simp))
      ((Vw.contMDiff p).of_le (by simp))).mdifferentiableAt one_ne_zero
  have hpairfun : (fun q => cuspMetricError g e.cusp e.toFun q (fun a => ![Vy, Vw] a q)) =
      fun q => g.inner (e.toFun q) (mfderiv halfCollarModel W.model e.toFun q (Vy q))
          (mfderiv halfCollarModel W.model e.toFun q (Vw q)) -
        e.cusp.metric.inner q (Vy q) (Vw q) := rfl
  have hslots : (fun a : Fin 2 => ![Vy, Vw] a p) = ![Vy p, Vw p] := by
    funext a
    fin_cases a <;> rfl
  have h := metricCovariantDerivative_apply_smooth_slots e.cusp.metric
    (cuspMetricError g e.cusp e.toFun) p (e.differentiableWithinAt_chart_metricError hK hp) Vx
    ![Vy, Vw] (by rw [hpairfun]; exact hĜ.sub hHd)
  rw [hslots] at h
  rw [h, hpairfun, mvfderiv_fun_sub hĜ hHd, Fin.sum_univ_two]
  rfl

/-- First-order binding of the metric error: `|∇_H (e^*g − H)(x; y, w)| ≤ δ |x|_H |y|_H |w|_H`
on the cusp domain (`K ≥ 1`). -/
theorem CuspEmbedding.abs_metricCovariantDerivative_metricError_le (e : CuspEmbedding W g K δ X)
    (hK : 1 ≤ K) {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    (x y w : TangentSpace halfCollarModel p) :
    |metricCovariantDerivative e.cusp.metric 2 (cuspMetricError g e.cusp e.toFun) p
        (Fin.cons x ![y, w])| ≤
      δ * Real.sqrt (e.cusp.metric.inner p x x) * Real.sqrt (e.cusp.metric.inner p y y) *
        Real.sqrt (e.cusp.metric.inner p w w) := by
  have h1 := e.metric_error 1 hK p hp
  change tensor0SFiberNorm e.cusp.metric p 3
    (metricCovariantDerivative e.cusp.metric 2 (cuspMetricError g e.cusp e.toFun) p) ≤ δ at h1
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := halfCollarModel) e.cusp.metric p
  have hb := abs_apply_le_sqrt_normSq0S (I := halfCollarModel) e.cusp.metric p 3 basis hON
    (metricCovariantDerivative e.cusp.metric 2 (cuspMetricError g e.cusp e.toFun) p)
    (Fin.cons x ![y, w])
  have hp3 : (∏ a : Fin 3, Real.sqrt (e.cusp.metric.inner p ((Fin.cons x ![y, w] :
      Fin 3 → TangentSpace halfCollarModel p) a) ((Fin.cons x ![y, w] :
      Fin 3 → TangentSpace halfCollarModel p) a))) =
      Real.sqrt (e.cusp.metric.inner p x x) * Real.sqrt (e.cusp.metric.inner p y y) *
        Real.sqrt (e.cusp.metric.inner p w w) := by
    rw [Fin.prod_univ_three]
    rfl
  rw [hp3] at hb
  refine hb.trans ?_
  have hnn : 0 ≤ Real.sqrt (e.cusp.metric.inner p x x) * Real.sqrt (e.cusp.metric.inner p y y) *
      Real.sqrt (e.cusp.metric.inner p w w) := by positivity
  calc Real.sqrt (normSq0S e.cusp.metric p 3
        (metricCovariantDerivative e.cusp.metric 2 (cuspMetricError g e.cusp e.toFun) p)) *
        (Real.sqrt (e.cusp.metric.inner p x x) * Real.sqrt (e.cusp.metric.inner p y y) *
          Real.sqrt (e.cusp.metric.inner p w w))
      ≤ δ * (Real.sqrt (e.cusp.metric.inner p x x) * Real.sqrt (e.cusp.metric.inner p y y) *
          Real.sqrt (e.cusp.metric.inner p w w)) := mul_le_mul_of_nonneg_right h1 hnn
    _ = _ := by ring

private theorem cuspHess_fromTangentSpace (y w : ℝ) :
    (NormedSpace.fromTangentSpace y : TangentSpace 𝓘(ℝ, ℝ) y ≃L[ℝ] ℝ) w = w := rfl

/-- The differential of `q ↦ e^{-z(q)}` on the cusp. -/
private theorem cuspHess_hasMFDerivAt_expHeight (p : CuspHalfSpace) :
    HasMFDerivAt halfCollarModel 𝓘(ℝ, ℝ) (fun q : CuspHalfSpace => Real.exp (-(q.2.val 0))) p
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (Real.exp (-(p.2.val 0)) * -1)).comp
        ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).toContinuousLinearMap.comp
          (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
            (EuclideanSpace ℝ (Fin 1))))) := by
  have h1 := hasMFDerivAt_cusp_height p
  have h2 : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => Real.exp (-t)) (p.2.val 0)
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (Real.exp (-(p.2.val 0)) * -1)) :=
    ((Real.hasDerivAt_exp (-(p.2.val 0))).comp (p.2.val 0)
      (hasDerivAt_neg (p.2.val 0))).hasFDerivAt.hasMFDerivAt
  change HasMFDerivAt halfCollarModel 𝓘(ℝ, ℝ)
    ((fun t : ℝ => Real.exp (-t)) ∘ (fun q : CuspHalfSpace => q.2.val 0)) p _
  exact HasMFDerivAt.comp (g := fun t : ℝ => Real.exp (-t))
    (f := fun q : CuspHalfSpace => q.2.val 0) p h2 h1

private theorem cuspHess_expHeight_deriv_apply (p : CuspHalfSpace)
    (v : TangentSpace halfCollarModel p) :
    ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (Real.exp (-(p.2.val 0)) * -1)).comp
        ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).toContinuousLinearMap.comp
          (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
            (EuclideanSpace ℝ (Fin 1))))) v =
      -(Real.exp (-(p.2.val 0)) * v.2 0) := by
  change (v.2 0) * (Real.exp (-(p.2.val 0)) * -1) = _
  ring

/-- **The model Christoffel symbol in the height direction.** For chart-constant fields at `p`, the
height component of `∇^H_a V_b` is `½ e^{-z} g_T(a₁, b₁)` (boundary points included). -/
theorem cusp_leviCivita_height (Hc : HyperbolicCusp) (p : CuspHalfSpace)
    (V : Ec → ContMDiffSection halfCollarModel Ec ∞
      (TangentSpace halfCollarModel : CuspHalfSpace → Type _))
    (hV : ∀ᶠ q in 𝓝 p, ∀ c : Ec, V c q = FiberBundle.extend
      (E := (TangentSpace halfCollarModel : CuspHalfSpace → Type _)) Ec (x := p) c q)
    (a b : Ec) :
    (leviCivitaConnectionOfMetric Hc.metric (fun q => V b q) p a).2 0 =
      (1 / 2 : ℝ) * (Real.exp (-(p.2.val 0)) * Hc.torusMetric.inner p.1 a.1 b.1) := by
  let ez : TangentSpace halfCollarModel p := ((0 : Et), EuclideanSpace.single 0 1)
  have hVp : ∀ c : Ec, V c p = c := fun c => by
    rw [hV.self_of_nhds c]
    exact FiberBundle.extend_apply_self (E := (TangentSpace halfCollarModel : CuspHalfSpace → Type _))
      Ec (x := p) c
  have hV' : ∀ c : Ec, (fun q => (V c q : TangentSpace halfCollarModel q)) =ᶠ[𝓝 p]
      FiberBundle.extend (E := (TangentSpace halfCollarModel : CuspHalfSpace → Type _)) Ec
        (x := p) c := fun c => hV.mono fun q hq => hq c
  have hbr : ∀ c c' : Ec, VectorField.mlieBracket halfCollarModel (fun q => V c q)
      (fun q => V c' q) p = 0 := fun c c' => by
    rw [(hV' c).mlieBracket_vectorField_eq (hV' c')]
    exact DifferentialGeometry.VectorField.mlieBracket_fiberBundleExtend_eq_zero p c c'
  have hd : ∀ c : Ec, MDifferentiableAt halfCollarModel (halfCollarModel.prod 𝓘(ℝ, Ec))
      (fun q => (⟨q, V c q⟩ : TotalSpace Ec (TangentSpace halfCollarModel))) p := fun c =>
    (V c).contMDiff.mdifferentiableAt (by simp)
  have hk := cuspHess_koszul Hc.metric (hd a) (hd b) (hd ez) (hbr a b) (hbr b ez) (hbr ez a)
  rw [hVp a, hVp b, hVp ez] at hk
  have hprod := (cusp_extend_eq_prod p).and hV
  -- the left side is the height component
  have hL : Hc.metric.inner p (leviCivitaConnectionOfMetric Hc.metric (fun q => V b q) p a) ez =
      (leviCivitaConnectionOfMetric Hc.metric (fun q => V b q) p a).2 0 := by
    refine (Hc.metric_formula p _ _).trans ?_
    simp only [ez, PiLp.single_apply, ite_true, mul_one]
    rw [show Hc.torusMetric.inner p.1
      ((leviCivitaConnectionOfMetric Hc.metric (fun q => V b q) p) a).1 (0 : Et) = 0 from
      (Hc.torusMetric.inner p.1 _).map_zero]
    ring
  -- the two mixed terms vanish
  have hmix : ∀ c : Ec, (fun q => Hc.metric.inner q (V c q) (V ez q)) =ᶠ[𝓝 p]
      fun _ => c.2 0 := fun c => by
    filter_upwards [hprod] with q hq
    rw [hq.2 c, hq.2 ez, hq.1 c, hq.1 ez]
    refine (Hc.metric_formula q _ _).trans ?_
    simp [ez]
  have hmix' : ∀ c : Ec, (fun q => Hc.metric.inner q (V ez q) (V c q)) =ᶠ[𝓝 p]
      fun _ => c.2 0 := fun c => by
    filter_upwards [hmix c] with q hq
    rw [Hc.metric.symm]
    exact hq
  have h1 : mvfderiv halfCollarModel (fun q => Hc.metric.inner q (V b q) (V ez q)) p a = 0 := by
    rw [mvfderiv_eq_of_eventuallyEq (hmix b), mvfderiv_const]
    rfl
  have h2 : mvfderiv halfCollarModel (fun q => Hc.metric.inner q (V ez q) (V a q)) p b = 0 := by
    rw [mvfderiv_eq_of_eventuallyEq (hmix' a), mvfderiv_const]
    rfl
  -- the vertical derivative of the horizontal inner product
  let F : Torus → ℝ := fun t => Hc.torusMetric.inner t
    ((trivializationAt Et (TangentSpace torusModel) p.1).symmL ℝ t a.1)
    ((trivializationAt Et (TangentSpace torusModel) p.1).symmL ℝ t b.1)
  have hab : (fun q => Hc.metric.inner q (V a q) (V b q)) =ᶠ[𝓝 p]
      fun q => a.2 0 * b.2 0 + Real.exp (-(q.2.val 0)) * F q.1 := by
    filter_upwards [hprod] with q hq
    rw [hq.2 a, hq.2 b, hq.1 a, hq.1 b]
    exact Hc.metric_formula q _ _
  have hFd : MDifferentiableAt torusModel 𝓘(ℝ, ℝ) F p.1 :=
    (cuspHess_contMDiffAt_inner Hc.torusMetric
      (DifferentialGeometry.Geometry.contMDiffAt_tangent_symmL_frame (n := 1) p.1 a.1)
      (DifferentialGeometry.Geometry.contMDiffAt_tangent_symmL_frame (n := 1) p.1 b.1)).mdifferentiableAt
      one_ne_zero
  have hFp : F p.1 = Hc.torusMetric.inner p.1 a.1 b.1 := by
    simp only [F, torus_symmL_trivializationAt_self]
  have hE := cuspHess_hasMFDerivAt_expHeight p
  have hF : HasMFDerivAt halfCollarModel 𝓘(ℝ, ℝ) (fun q : CuspHalfSpace => F q.1) p
      ((mfderiv torusModel 𝓘(ℝ, ℝ) F p.1).comp
        (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
          (EuclideanSpace ℝ (Fin 1)))) :=
    hFd.hasMFDerivAt.comp p (hasMFDerivAt_fst p)
  have h3 : mvfderiv halfCollarModel (fun q => Hc.metric.inner q (V a q) (V b q)) p ez =
      -(Real.exp (-(p.2.val 0)) * Hc.torusMetric.inner p.1 a.1 b.1) := by
    rw [mvfderiv_eq_of_eventuallyEq hab]
    have e1 : (fun q : CuspHalfSpace => a.2 0 * b.2 0 + Real.exp (-(q.2.val 0)) * F q.1) =
        (fun _ : CuspHalfSpace => a.2 0 * b.2 0) +
          ((fun q : CuspHalfSpace => Real.exp (-(q.2.val 0))) * (fun q : CuspHalfSpace => F q.1)) :=
      rfl
    rw [e1, mvfderiv_add mdifferentiableAt_const (hE.mdifferentiableAt.mul hF.mdifferentiableAt),
      mvfderiv_const, zero_add, mvfderiv_mul hE.mdifferentiableAt hF.mdifferentiableAt]
    rw [add_apply, smul_apply, smul_apply]
    have hd1 : mvfderiv halfCollarModel (fun q : CuspHalfSpace => Real.exp (-(q.2.val 0))) p ez =
        -(Real.exp (-(p.2.val 0)) * ez.2 0) := by
      change mfderiv halfCollarModel 𝓘(ℝ, ℝ) (fun q : CuspHalfSpace => Real.exp (-(q.2.val 0))) p ez
        = _
      rw [hE.mfderiv]
      exact cuspHess_expHeight_deriv_apply p ez
    have hd2 : mvfderiv halfCollarModel (fun q : CuspHalfSpace => F q.1) p ez = 0 := by
      change mfderiv halfCollarModel 𝓘(ℝ, ℝ) (fun q : CuspHalfSpace => F q.1) p ez = 0
      rw [hF.mfderiv]
      change mfderiv torusModel 𝓘(ℝ, ℝ) F p.1 ez.1 = 0
      exact (mfderiv torusModel 𝓘(ℝ, ℝ) F p.1).map_zero
    have hz1 : ez.2 0 = 1 := by simp [ez]
    rw [hd1, hd2, hz1]
    simp only [smul_eq_mul, hFp]
    ring
  rw [hL, h1, h2, h3] at hk
  rw [hk]
  ring

private theorem cuspHess_alg {δ na nb nD : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4) (hna : 0 ≤ na)
    (hnb : 0 ≤ nb) (hnD : 0 ≤ nD)
    (hquad : (1 - δ) * nD ^ 2 ≤ (3 / 2 : ℝ) * (δ * na * nb * nD)) : nD ≤ 2 * δ * na * nb := by
  have hP : 0 ≤ δ * na * nb := by positivity
  by_contra hcon
  have hcon' : 2 * δ * na * nb < nD := lt_of_not_ge hcon
  have h1 : 2 * δ * na * nb * nD ≤ nD * nD := mul_le_mul_of_nonneg_right hcon'.le hnD
  nlinarith

/-- A vector `u` of the cusp with `H(u, w) = 0` for every `w` vanishes. -/
private theorem cuspHess_eq_zero_of_inner (Hc : HyperbolicCusp) {p : CuspHalfSpace}
    {u : TangentSpace halfCollarModel p} (h : ∀ w, Hc.metric.inner p u w = 0) : u = 0 := by
  by_contra hu
  have := Hc.metric.pos p u hu
  rw [h u] at this
  exact lt_irrefl 0 this

/-- **Symmetry of the model Christoffel symbols** on chart-constant fields at `p`. -/
theorem cusp_leviCivita_symm (Hc : HyperbolicCusp) (p : CuspHalfSpace)
    (V : Ec → ContMDiffSection halfCollarModel Ec ∞
      (TangentSpace halfCollarModel : CuspHalfSpace → Type _))
    (hV : ∀ᶠ q in 𝓝 p, ∀ c : Ec, V c q = FiberBundle.extend
      (E := (TangentSpace halfCollarModel : CuspHalfSpace → Type _)) Ec (x := p) c q)
    (x y : Ec) :
    leviCivitaConnectionOfMetric Hc.metric (fun q => V y q) p x =
      leviCivitaConnectionOfMetric Hc.metric (fun q => V x q) p y := by
  have hVp : ∀ c : Ec, V c p = c := fun c => by
    rw [hV.self_of_nhds c]
    exact FiberBundle.extend_apply_self (E := (TangentSpace halfCollarModel : CuspHalfSpace → Type _))
      Ec (x := p) c
  have hV' : ∀ c : Ec, (fun q => (V c q : TangentSpace halfCollarModel q)) =ᶠ[𝓝 p]
      FiberBundle.extend (E := (TangentSpace halfCollarModel : CuspHalfSpace → Type _)) Ec
        (x := p) c := fun c => hV.mono fun q hq => hq c
  have hbr : ∀ c c' : Ec, VectorField.mlieBracket halfCollarModel (fun q => V c q)
      (fun q => V c' q) p = 0 := fun c c' => by
    rw [(hV' c).mlieBracket_vectorField_eq (hV' c')]
    exact DifferentialGeometry.VectorField.mlieBracket_fiberBundleExtend_eq_zero p c c'
  have hd : ∀ c : Ec, MDifferentiableAt halfCollarModel (halfCollarModel.prod 𝓘(ℝ, Ec))
      (fun q => (⟨q, V c q⟩ : TotalSpace Ec (TangentSpace halfCollarModel))) p := fun c =>
    (V c).contMDiff.mdifferentiableAt (by simp)
  rw [← sub_eq_zero]
  refine cuspHess_eq_zero_of_inner Hc fun w => ?_
  have k1 := cuspHess_koszul Hc.metric (hd x) (hd y) (hd w) (hbr x y) (hbr y w) (hbr w x)
  have k2 := cuspHess_koszul Hc.metric (hd y) (hd x) (hd w) (hbr y x) (hbr x w) (hbr w y)
  rw [hVp x, hVp y, hVp w] at k1 k2
  have s1 : (fun q => Hc.metric.inner q (V x q) (V w q)) =
      fun q => Hc.metric.inner q (V w q) (V x q) := funext fun q => Hc.metric.symm q _ _
  have s2 : (fun q => Hc.metric.inner q (V w q) (V y q)) =
      fun q => Hc.metric.inner q (V y q) (V w q) := funext fun q => Hc.metric.symm q _ _
  have s3 : (fun q => Hc.metric.inner q (V y q) (V x q)) =
      fun q => Hc.metric.inner q (V x q) (V y q) := funext fun q => Hc.metric.symm q _ _
  rw [s1, s2, s3] at k2
  rw [map_sub, sub_apply, k1, k2]
  ring

/-- **The cusp-height Hessian estimate (Z-H), all pairs.** For a cusp embedding with `K ≥ 1` and
`0 ≤ δ ≤ 1/4`, at every point of the cusp domain (height zero included), for all `a, b`,
`|Hess_g ζ(De a, De b) + ½ e^{-z} g_T(a₁, b₁)| ≤ 2 δ |a|_H |b|_H`, where `ζ = z ∘ e⁻¹` and
`Hess_g` is the existing Hessian of the Levi-Civita connection of `g`. -/
theorem CuspEmbedding.abs_hessian_height_add_le (e : CuspEmbedding W g K δ X) (hK : 1 ≤ K)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4) {p : CuspHalfSpace} (hp : p ∈ cuspDomain) (a b : Ec) :
    |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
        (fun y => (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p)
        (mfderiv halfCollarModel W.model e.toFun p a)
        (mfderiv halfCollarModel W.model e.toFun p b) +
      (1 / 2 : ℝ) * (Real.exp (-(p.2.val 0)) * e.cusp.torusMetric.inner p.1 a.1 b.1)| ≤
      2 * δ * Real.sqrt (e.cusp.metric.inner p a a) * Real.sqrt (e.cusp.metric.inner p b b) := by
  obtain ⟨V, hV⟩ := cusp_exists_chartConstant_sections p
  have hVp : ∀ c : Ec, V c p = c := fun c => by
    rw [hV.self_of_nhds c]
    exact FiberBundle.extend_apply_self (E := (TangentSpace halfCollarModel : CuspHalfSpace → Type _))
      Ec (x := p) c
  have hV' : ∀ c : Ec, (fun q => (V c q : TangentSpace halfCollarModel q)) =ᶠ[𝓝 p]
      FiberBundle.extend (E := (TangentSpace halfCollarModel : CuspHalfSpace → Type _)) Ec
        (x := p) c := fun c => hV.mono fun q hq => hq c
  have hbr : ∀ c c' : Ec, VectorField.mlieBracket halfCollarModel (fun q => V c q)
      (fun q => V c' q) p = 0 := fun c c' => by
    rw [(hV' c).mlieBracket_vectorField_eq (hV' c')]
    exact DifferentialGeometry.VectorField.mlieBracket_fiberBundleExtend_eq_zero p c c'
  have hd : ∀ c : Ec, MDifferentiableAt halfCollarModel (halfCollarModel.prod 𝓘(ℝ, Ec))
      (fun q => (⟨q, V c q⟩ : TotalSpace Ec (TangentSpace halfCollarModel))) p := fun c =>
    (V c).contMDiff.mdifferentiableAt (by simp)
  have hheight : ∀ c : Ec, ∀ᶠ q in 𝓝 p, (V c q).2 0 = (V c p).2 0 := fun c => by
    filter_upwards [(cusp_extend_eq_prod p).and hV] with q hq
    rw [hq.2 c, hq.1 c, hVp c]
  -- notation
  let Gp : Ec → Ec → ℝ := fun u v => g.inner (e.toFun p)
    (mfderiv halfCollarModel W.model e.toFun p u) (mfderiv halfCollarModel W.model e.toFun p v)
  let Hp : Ec → Ec → ℝ := fun u v => e.cusp.metric.inner p u v
  let Γ : Ec → Ec → Ec := fun x y => leviCivitaConnectionOfMetric e.cusp.metric (fun q => V y q) p x
  let dG : Ec → Ec → Ec → ℝ := fun x y z => mvfderiv halfCollarModel (fun q => g.inner (e.toFun q)
    (mfderiv halfCollarModel W.model e.toFun q (V y q))
    (mfderiv halfCollarModel W.model e.toFun q (V z q))) p x
  let dH : Ec → Ec → Ec → ℝ := fun x y z => mvfderiv halfCollarModel
    (fun q => e.cusp.metric.inner q (V y q) (V z q)) p x
  let nT : Ec → Ec → Ec → ℝ := fun x y z =>
    metricCovariantDerivative e.cusp.metric 2 (cuspMetricError g e.cusp e.toFun) p
      (Fin.cons x ![y, z])
  -- the Hessian
  have hHess := e.hessian_height_pushforward (g := g) hK hp (V b) (hheight b)
    (mfderiv halfCollarModel W.model e.toFun p a)
  rw [hVp b] at hHess
  -- the vector γ
  obtain ⟨A₀, hA⟩ := e.isInvertible_mfderiv hp
  let A : Ec ≃L[ℝ] EuclideanSpace ℝ (Fin 3) := A₀
  have hAD : ∀ v : Ec, A v = mfderiv halfCollarModel W.model e.toFun p v := fun v =>
    congrArg (fun L : TangentSpace halfCollarModel p →L[ℝ] TangentSpace W.model (e.toFun p) => L v) hA
  let w : EuclideanSpace ℝ (Fin 3) := leviCivitaConnectionOfMetric g
    (VectorField.mpullback W.model halfCollarModel (invFunOn e.toFun cuspDomain) (fun q => V b q))
    (e.toFun p) (mfderiv halfCollarModel W.model e.toFun p a)
  let γ : Ec := A.symm w
  have hγ : mfderiv halfCollarModel W.model e.toFun p γ = w := by
    rw [← hAD]
    exact A.apply_symm_apply w
  have hdζ : mvfderiv W.model (fun y => (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p) w =
      γ.2 0 := by
    rw [← hγ]
    exact e.mfderiv_height_invFunOn_mfderiv hp γ
  have hHessγ : (CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
      (fun y => (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p)
      (mfderiv halfCollarModel W.model e.toFun p a) (mfderiv halfCollarModel W.model e.toFun p b) =
      -γ.2 0 := by
    rw [hHess]
    change -mvfderiv W.model (fun y => (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p) w = _
    rw [hdζ]
  -- Koszul on W
  have hKW : ∀ c : Ec, Gp γ c = (1 / 2 : ℝ) * (dG a b c + dG b c a - dG c a b) := fun c => by
    have h := e.inner_leviCivita_pushforward (g := g) hK hp (V a) (V b) (V c) (hbr a b) (hbr b c)
      (hbr c a)
    rw [hVp a, hVp b, hVp c] at h
    change g.inner (e.toFun p) (mfderiv halfCollarModel W.model e.toFun p γ)
      (mfderiv halfCollarModel W.model e.toFun p c) = _
    rw [hγ]
    exact h
  -- Koszul on the model
  have hKH : ∀ c : Ec, Hp (Γ a b) c = (1 / 2 : ℝ) * (dH a b c + dH b c a - dH c a b) :=
    fun c => by
    have h := cuspHess_koszul e.cusp.metric (hd a) (hd b) (hd c) (hbr a b) (hbr b c) (hbr c a)
    rw [hVp a, hVp b, hVp c] at h
    exact h
  -- Leibniz evaluation of `∇T`
  have hG1 : ∀ x y z : Ec, nT x y z = dG x y z - dH x y z -
      ((Gp (Γ x y) z - Hp (Γ x y) z) + (Gp y (Γ x z) - Hp y (Γ x z))) := by
    intro x y z
    have h := e.metricCovariantDerivative_metricError_apply (g := g) hK hp (V x) (V y) (V z)
    rw [hVp x, hVp y, hVp z] at h
    exact h
  -- symmetries
  have hΓs : ∀ x y : Ec, Γ x y = Γ y x := fun x y => cusp_leviCivita_symm e.cusp p V hV x y
  have hGs : ∀ u v : Ec, Gp u v = Gp v u := fun u v => g.symm _ _ _
  have hHs : ∀ u v : Ec, Hp u v = Hp v u := fun u v => e.cusp.metric.symm _ _ _
  have hdGs : ∀ x y z : Ec, dG x y z = dG x z y := fun x y z => by
    change mvfderiv halfCollarModel (fun q => g.inner (e.toFun q)
      (mfderiv halfCollarModel W.model e.toFun q (V y q))
      (mfderiv halfCollarModel W.model e.toFun q (V z q))) p x =
      mvfderiv halfCollarModel (fun q => g.inner (e.toFun q)
      (mfderiv halfCollarModel W.model e.toFun q (V z q))
      (mfderiv halfCollarModel W.model e.toFun q (V y q))) p x
    congr 2
    funext q
    exact g.symm _ _ _
  have hdHs : ∀ x y z : Ec, dH x y z = dH x z y := fun x y z => by
    change mvfderiv halfCollarModel (fun q => e.cusp.metric.inner q (V y q) (V z q)) p x =
      mvfderiv halfCollarModel (fun q => e.cusp.metric.inner q (V z q) (V y q)) p x
    congr 2
    funext q
    exact e.cusp.metric.symm _ _ _
  -- the key identity
  have hkey : ∀ c : Ec, Gp (γ - Γ a b) c =
      (1 / 2 : ℝ) * (nT a b c + nT b c a - nT c a b) := fun c => by
    have e1 : Gp (γ - Γ a b) c = Gp γ c - Gp (Γ a b) c := by
      let L : Ec →L[ℝ] EuclideanSpace ℝ (Fin 3) := mfderiv halfCollarModel W.model e.toFun p
      let Bg : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
        g.inner (e.toFun p)
      change Bg (L (γ - Γ a b)) (L c) = Bg (L γ) (L c) - Bg (L (Γ a b)) (L c)
      rw [map_sub, map_sub, sub_apply]
    have h1 := hG1 a b c
    have h2 := hG1 b c a
    have h3 := hG1 c a b
    have h4 := hKW c
    have h5 := hKH c
    rw [hΓs b a] at h2
    rw [hΓs c a, hΓs c b] at h3
    rw [hGs b (Γ a c), hHs b (Γ a c)] at h1
    rw [hGs c (Γ a b), hHs c (Γ a b)] at h2
    rw [hGs a (Γ b c), hHs a (Γ b c)] at h3
    rw [hdGs b c a, hdHs b c a] at h2
    rw [hdGs c a b, hdHs c a b] at h3
    rw [hdGs b c a, hdGs c a b] at h4
    rw [hdHs b c a, hdHs c a b] at h5
    rw [e1]
    linarith
  -- the bound on `γ - Γ a b`
  set Dv : Ec := γ - Γ a b with hDvdef
  have hnT : ∀ x y z : Ec, |nT x y z| ≤ δ * Real.sqrt (Hp x x) * Real.sqrt (Hp y y) *
      Real.sqrt (Hp z z) := fun x y z =>
    e.abs_metricCovariantDerivative_metricError_le (g := g) hK hp x y z
  have hDD := hkey Dv
  have hlow : (1 - δ) * Hp Dv Dv ≤ Gp Dv Dv := e.one_sub_mul_le_pullback_inner hp Dv
  set na := Real.sqrt (Hp a a) with hna
  set nb := Real.sqrt (Hp b b) with hnb
  set nD := Real.sqrt (Hp Dv Dv) with hnD
  have hna0 : 0 ≤ na := Real.sqrt_nonneg _
  have hnb0 : 0 ≤ nb := Real.sqrt_nonneg _
  have hnD0 : 0 ≤ nD := Real.sqrt_nonneg _
  have hDsq : Hp Dv Dv = nD ^ 2 := (Real.sq_sqrt (metric_inner_self_nonneg _ _ _)).symm
  have b1 := abs_le.mp (hnT a b Dv)
  have b2 := abs_le.mp (hnT b Dv a)
  have b3 := abs_le.mp (hnT Dv a b)
  have hup : Gp Dv Dv ≤ (3 / 2 : ℝ) * (δ * na * nb * nD) := by
    rw [hDD]
    linarith [b1.2, b2.2, b3.1]
  have hquad : (1 - δ) * nD ^ 2 ≤ (3 / 2 : ℝ) * (δ * na * nb * nD) := by
    rw [← hDsq]
    exact hlow.trans hup
  have hnDle : nD ≤ 2 * δ * na * nb := cuspHess_alg hδ0 hδ hna0 hnb0 hnD0 hquad
  -- the height component
  have hheightD : |Dv.2 0| ≤ nD := Real.abs_le_sqrt (sq_height_le_cusp_inner e.cusp p Dv)
  have hγsplit : γ.2 0 = (Γ a b).2 0 + Dv.2 0 := by
    rw [hDvdef]
    simp
  have hmodel := cusp_leviCivita_height e.cusp p V hV a b
  change (Γ a b).2 0 = _ at hmodel
  rw [hHessγ, hγsplit, hmodel]
  have : -((1 / 2 : ℝ) * (Real.exp (-(p.2.val 0)) * e.cusp.torusMetric.inner p.1 a.1 b.1) +
      Dv.2 0) + (1 / 2 : ℝ) * (Real.exp (-(p.2.val 0)) * e.cusp.torusMetric.inner p.1 a.1 b.1) =
      -Dv.2 0 := by ring
  rw [this, abs_neg]
  exact hheightD.trans hnDle

private theorem cuspHess_core_alg {δ Hv Gv Hs : ℝ} (hδ : δ ≤ 1 / 100)
    (hHv : 0 ≤ Hv) (hG : Gv ≤ (1 + δ) * Hv) (hs : |Hs + (1 / 2 : ℝ) * Hv| ≤ 2 * δ * Hv) :
    (3 / 8 : ℝ) * Gv ≤ -Hs := by
  have h1 := (abs_le.mp hs).2
  nlinarith

/-- **Core bound for the collar height Hessian.** On the whole open collar `e '' cuspDomain`
(boundary included), for `K ≥ 1` and `0 ≤ δ ≤ 1/100`, every `v` with `dζ(v) = 0` has
`(3/8)·g(v,v) ≤ −Hess_g ζ(v,v)`. -/
theorem CuspEmbedding.three_eighths_inner_le_neg_hessian_height (e : CuspEmbedding W g K δ X)
    (hK : 1 ≤ K) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 100) {y : W.Carrier}
    (hy : y ∈ e.toFun '' cuspDomain) (v : TangentSpace W.model y)
    (hv : mvfderiv W.model (fun y => (invFunOn e.toFun cuspDomain y).2.val 0) y v = 0) :
    (3 / 8 : ℝ) * g.inner y v v ≤
      -((CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
        (fun y => (invFunOn e.toFun cuspDomain y).2.val 0) y v v) := by
  obtain ⟨p, hp, rfl⟩ := hy
  obtain ⟨A₀, hA⟩ := e.isInvertible_mfderiv hp
  let A : Ec ≃L[ℝ] EuclideanSpace ℝ (Fin 3) := A₀
  have hAD : ∀ w : Ec, A w = mfderiv halfCollarModel W.model e.toFun p w := fun w =>
    congrArg (fun L : TangentSpace halfCollarModel p →L[ℝ] TangentSpace W.model (e.toFun p) => L w) hA
  let a : Ec := A.symm v
  have hva : mfderiv halfCollarModel W.model e.toFun p a = v := by
    rw [← hAD]
    exact A.apply_symm_apply v
  have ha2 : a.2 0 = 0 := by
    have h := e.mfderiv_height_invFunOn_mfderiv hp a
    rw [hva] at h
    exact h.symm.trans hv
  have hest := e.abs_hessian_height_add_le (g := g) hK hδ0 (by linarith) hp a a
  rw [hva] at hest
  have hHa : e.cusp.metric.inner p a a =
      Real.exp (-(p.2.val 0)) * e.cusp.torusMetric.inner p.1 a.1 a.1 := by
    refine (e.cusp.metric_formula p a a).trans ?_
    rw [ha2]
    ring
  have e1 : |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
        (fun y => (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p) v v +
        (1 / 2 : ℝ) * e.cusp.metric.inner p a a| =
      |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
        (fun y => (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p) v v +
        (1 / 2 : ℝ) * (Real.exp (-(p.2.val 0)) * e.cusp.torusMetric.inner p.1 a.1 a.1)| :=
    congrArg (fun t => |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
        (fun y => (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p) v v + (1 / 2 : ℝ) * t|) hHa
  have e2 : 2 * δ * Real.sqrt (e.cusp.metric.inner p a a) * Real.sqrt (e.cusp.metric.inner p a a) =
      2 * δ * e.cusp.metric.inner p a a :=
    (mul_assoc _ _ _).trans (congrArg (fun t => 2 * δ * t)
      (Real.mul_self_sqrt (metric_inner_self_nonneg e.cusp.metric p a)))
  have hest' := (e1.trans_le hest).trans_eq e2
  have hG := e.pullback_inner_le_one_add_mul hp a
  rw [hva] at hG
  exact cuspHess_core_alg hδ (metric_inner_self_nonneg _ _ _) hG hest'

/-- **Statement G, clause (v): the boundary is uniformly convex** (corrected chart-free form, see
`docs/geometrization/chapter13/errata-boundary-geometry-G-II-20261004.md`). For `K ≥ 1` and
`0 ≤ δ ≤ 1/100`, at every point `y` of the boundary component `X` and for all `v, u` with
`dζ(v) = 0`: `g(v,v)/4 · |dζ(u)| ≤ −Hess_g ζ(v,v) · √g(u,u)`, i.e. `II ≥ g/4` for the outward
normal `−grad ζ/‖dζ‖_g`. -/
theorem CuspEmbedding.inner_div_four_mul_abs_le_neg_hessian_height (e : CuspEmbedding W g K δ X)
    (hK : 1 ≤ K) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 100) :
    let Hζ := (CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
      (fun y => (invFunOn e.toFun cuspDomain y).2.val 0)
    ∀ y ∈ X, ∀ v u : TangentSpace W.model y,
      mvfderiv W.model (fun y => (invFunOn e.toFun cuspDomain y).2.val 0) y v = 0 →
      g.inner y v v / 4 * |mvfderiv W.model (fun y => (invFunOn e.toFun cuspDomain y).2.val 0) y u| ≤
        -(Hζ y v v) * Real.sqrt (g.inner y u u) := by
  intro Hζ y hyX v u hv
  rw [← e.boundary_image] at hyX
  obtain ⟨t, rfl⟩ := hyX
  have hp : ((t, halfZero) : CuspHalfSpace) ∈ cuspDomain := by
    change (halfZero : EuclideanHalfSpace 1).val 0 < cuspDepth
    change (0 : ℝ) < 100
    norm_num
  have hcore := e.three_eighths_inner_le_neg_hessian_height (g := g) hK hδ0 hδ
    (mem_image_of_mem _ hp) v hv
  have hdual := e.abs_mfderiv_height_invFunOn_le (by linarith) hp u
  have hs : (Real.sqrt (1 - δ))⁻¹ ≤ 3 / 2 := by
    have h49 : (2 / 3 : ℝ) ≤ Real.sqrt (1 - δ) := by
      rw [show (2 / 3 : ℝ) = Real.sqrt ((2 / 3) ^ 2) by
        rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hpos : (0 : ℝ) < 2 / 3 := by norm_num
    calc (Real.sqrt (1 - δ))⁻¹ ≤ (2 / 3 : ℝ)⁻¹ := inv_anti₀ hpos h49
      _ = 3 / 2 := by norm_num
  have hgv : 0 ≤ g.inner (e.toFun (t, halfZero)) v v := metric_inner_self_nonneg _ _ _
  have hgu : 0 ≤ Real.sqrt (g.inner (e.toFun (t, halfZero)) u u) := Real.sqrt_nonneg _
  have hdual' : |mvfderiv W.model (fun y => (invFunOn e.toFun cuspDomain y).2.val 0)
      (e.toFun (t, halfZero)) u| ≤ 3 / 2 * Real.sqrt (g.inner (e.toFun (t, halfZero)) u u) :=
    hdual.trans (mul_le_mul_of_nonneg_right hs hgu)
  calc g.inner (e.toFun (t, halfZero)) v v / 4 *
        |mvfderiv W.model (fun y => (invFunOn e.toFun cuspDomain y).2.val 0)
          (e.toFun (t, halfZero)) u|
      ≤ g.inner (e.toFun (t, halfZero)) v v / 4 *
          (3 / 2 * Real.sqrt (g.inner (e.toFun (t, halfZero)) u u)) :=
        mul_le_mul_of_nonneg_left hdual' (by positivity)
    _ = (3 / 8 : ℝ) * g.inner (e.toFun (t, halfZero)) v v *
          Real.sqrt (g.inner (e.toFun (t, halfZero)) u u) := by ring
    _ ≤ -(Hζ (e.toFun (t, halfZero)) v v) * Real.sqrt (g.inner (e.toFun (t, halfZero)) u u) :=
        mul_le_mul_of_nonneg_right hcore hgu

end Main

end DifferentialGeometry.Geometry.Collapse
