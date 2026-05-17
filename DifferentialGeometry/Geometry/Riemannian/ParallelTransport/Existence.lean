import DifferentialGeometry.Geometry.Riemannian.ParallelTransport.Defs
import DifferentialGeometry.Geometry.Riemannian.Geodesic.ChartChristoffelTransform
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall

set_option linter.unusedSectionVars false
set_option linter.style.setOption false
set_option maxHeartbeats 800000

/-!
# Existence and uniqueness of parallel vector fields along a smooth curve

For a smooth Riemannian metric `g` on a smooth boundaryless manifold `M` modelled on a
complete inner-product space `E`, and a `C¹` curve `γ : ℝ → M`, the
parallel-transport equation for a `C¹` vector field `V` along `γ`,
$$\nabla_{\dot\gamma} V \equiv 0,$$
is a linear ordinary differential equation in chart-`α` coordinates whenever `γ` is
confined to a single chart at some basepoint `α : M`. We prove:

* **Uniqueness.** Two parallel `C¹` vector fields along `γ` with identical initial
  value agree everywhere. This is a direct consequence of the inner-product
  preservation property shipped in `Defs.lean`: the difference `D := V - W` is
  parallel (by additivity / constant-scalar of `covDerivAlong`) with `D 0 = 0`,
  hence `g.inner (γ t) (D t) (D t)` is constant in `t`, equal to `0`, and the
  positive-definiteness of `g` forces `D t = 0`. This statement does not depend on
  any chart-confinement hypothesis.

* **Existence for the zero initial datum.** When the prescribed initial value is `0`,
  the zero vector field along `γ` is `C¹` and parallel, providing an explicit
  existence witness.

The general existence statement for arbitrary initial data via the chart-`α` linear
ODE construction is documented as a downstream development: it requires the chart-`α`
linear-ODE flow on `E` together with the chart-`α`-to-chart-(γ t) transformation law
for the Christoffel-symbol contraction, which is the same chart-transition input that
appears in `geodesicVectorFieldChart_chart_invariance_of_christoffel_transform`.
-/

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

open DifferentialGeometry DifferentialGeometry.Integral.Measure
  DifferentialGeometry.Geometry.Riemannian.Curve
  DifferentialGeometry.Geometry.Riemannian.Geodesic
  DifferentialGeometry.Integral.Connection

namespace Geometry
namespace Riemannian
namespace ParallelTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Bundle-coordinate smoothness for pointwise vector-field operations

We establish smoothness of the lifts `(γ t, V t + W t)` and `(γ t, (-1) • V t)` from
smoothness of the input lifts. The proof uses the trivialisation at `γ t` and the
fact that the trivialisation acts as a continuous linear map on the fibre over the
chart base set. -/

/-- Smoothness of the additive lift, in terms of the smoothness of the individual lifts.
`TangentBundle I M`'s smooth structure is the standard one inherited from the
trivializations, and additivity of `ContMDiff` on bundle-coordinate sums is a direct
consequence of the smoothness of `Trivialization.continuousLinearMapAt`. -/
private lemma contMDiff_addLift {γ : ℝ → M}
    (V W : ∀ t, TangentSpace I (γ t))
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M)))
    (hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, W t⟩ : TangentBundle I M))) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
      (fun t => (⟨γ t, V t + W t⟩ : TangentBundle I M)) := by
  classical
  intro t
  set α : M := γ t with hα
  set e := trivializationAt E (TangentSpace I) α
  have hin_src : (fun t => (⟨γ t, V t + W t⟩ : TangentBundle I M)) t ∈ e.source := by
    rw [Trivialization.mem_source, TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H (γ t)
  have hV_src : (fun t => (⟨γ t, V t⟩ : TangentBundle I M)) t ∈ e.source := by
    rw [Trivialization.mem_source, TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H (γ t)
  have hW_src : (fun t => (⟨γ t, W t⟩ : TangentBundle I M)) t ∈ e.source := by
    rw [Trivialization.mem_source, TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H (γ t)
  have hiffV := e.contMDiffAt_iff (IM := 𝓘(ℝ, ℝ)) (IB := I) (n := (1 : WithTop ℕ∞))
    (f := fun s => (⟨γ s, V s⟩ : TangentBundle I M)) hV_src
  have hiffW := e.contMDiffAt_iff (IM := 𝓘(ℝ, ℝ)) (IB := I) (n := (1 : WithTop ℕ∞))
    (f := fun s => (⟨γ s, W s⟩ : TangentBundle I M)) hW_src
  have hiffVW := e.contMDiffAt_iff (IM := 𝓘(ℝ, ℝ)) (IB := I) (n := (1 : WithTop ℕ∞))
    (f := fun s => (⟨γ s, V s + W s⟩ : TangentBundle I M)) hin_src
  obtain ⟨hγ_at, hVfib_at⟩ := hiffV.mp hV.contMDiffAt
  obtain ⟨_, hWfib_at⟩ := hiffW.mp hW.contMDiffAt
  have hcont : Continuous γ := by
    have hV_cont : Continuous (fun s => (⟨γ s, V s⟩ : TangentBundle I M)) :=
      hV.continuous
    have hproj : Continuous (TotalSpace.proj : TangentBundle I M → M) :=
      FiberBundle.continuous_proj E (TangentSpace I)
    exact hproj.comp hV_cont
  have hop : IsOpen ((chartAt H α).source) := (chartAt H α).open_source
  have hmem : γ t ∈ (chartAt H α).source := mem_chart_source H α
  have hev : ∀ᶠ s in nhds t, γ s ∈ (chartAt H α).source :=
    (hcont.continuousAt).preimage_mem_nhds (hop.mem_nhds hmem)
  have hsum_fib : (fun s => (e ⟨γ s, V s + W s⟩).2) =ᶠ[nhds t]
      (fun s => (e ⟨γ s, V s⟩).2 + (e ⟨γ s, W s⟩).2) := by
    filter_upwards [hev] with s hs
    have hs' : γ s ∈ e.baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]; exact hs
    have hclm : ∀ v : TangentSpace I (γ s),
        (e ⟨γ s, v⟩).2 = (e.continuousLinearMapAt ℝ (γ s)) v := fun v => by
      have hcoe := e.coe_linearMapAt_of_mem (R := ℝ) hs'
      have hlm_eq : (e.linearMapAt ℝ (γ s)) v = (e ⟨γ s, v⟩).2 := congrFun hcoe v
      have hclmEq : (e.continuousLinearMapAt ℝ (γ s)) v = (e.linearMapAt ℝ (γ s)) v := rfl
      rw [hclmEq, hlm_eq]
    rw [hclm (V s), hclm (W s), hclm (V s + W s), ContinuousLinearMap.map_add]
  have hfib_sum_at : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1
      (fun s => (e ⟨γ s, V s + W s⟩).2) t := by
    refine (hsum_fib.contMDiffAt_iff).mpr ?_
    exact hVfib_at.add hWfib_at
  exact hiffVW.mpr ⟨hγ_at, hfib_sum_at⟩

/-- Smoothness of the negation lift, by the same trivialization argument. -/
private lemma contMDiff_negLift {γ : ℝ → M}
    (V : ∀ t, TangentSpace I (γ t))
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M))) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
      (fun t => (⟨γ t, (-1 : ℝ) • V t⟩ : TangentBundle I M)) := by
  classical
  intro t
  set α : M := γ t with hα
  set e := trivializationAt E (TangentSpace I) α
  have hV_src : (fun t => (⟨γ t, V t⟩ : TangentBundle I M)) t ∈ e.source := by
    rw [Trivialization.mem_source, TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H (γ t)
  have hcV_src : (fun t => (⟨γ t, (-1 : ℝ) • V t⟩ : TangentBundle I M)) t ∈ e.source := by
    rw [Trivialization.mem_source, TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H (γ t)
  have hiffV := e.contMDiffAt_iff (IM := 𝓘(ℝ, ℝ)) (IB := I) (n := (1 : WithTop ℕ∞))
    (f := fun s => (⟨γ s, V s⟩ : TangentBundle I M)) hV_src
  have hiffcV := e.contMDiffAt_iff (IM := 𝓘(ℝ, ℝ)) (IB := I) (n := (1 : WithTop ℕ∞))
    (f := fun s => (⟨γ s, (-1 : ℝ) • V s⟩ : TangentBundle I M)) hcV_src
  obtain ⟨hγ_at, hVfib_at⟩ := hiffV.mp hV.contMDiffAt
  have hcont : Continuous γ := by
    have hV_cont : Continuous (fun s => (⟨γ s, V s⟩ : TangentBundle I M)) :=
      hV.continuous
    have hproj : Continuous (TotalSpace.proj : TangentBundle I M → M) :=
      FiberBundle.continuous_proj E (TangentSpace I)
    exact hproj.comp hV_cont
  have hop : IsOpen ((chartAt H α).source) := (chartAt H α).open_source
  have hmem : γ t ∈ (chartAt H α).source := mem_chart_source H α
  have hev : ∀ᶠ s in nhds t, γ s ∈ (chartAt H α).source :=
    (hcont.continuousAt).preimage_mem_nhds (hop.mem_nhds hmem)
  have hsum_fib : (fun s => (e ⟨γ s, (-1 : ℝ) • V s⟩).2) =ᶠ[nhds t]
      (fun s => (-1 : ℝ) • (e ⟨γ s, V s⟩).2) := by
    filter_upwards [hev] with s hs
    have hs' : γ s ∈ e.baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]; exact hs
    have hclm : ∀ v : TangentSpace I (γ s),
        (e ⟨γ s, v⟩).2 = (e.continuousLinearMapAt ℝ (γ s)) v := fun v => by
      have hcoe := e.coe_linearMapAt_of_mem (R := ℝ) hs'
      have hlm_eq : (e.linearMapAt ℝ (γ s)) v = (e ⟨γ s, v⟩).2 := congrFun hcoe v
      have hclmEq : (e.continuousLinearMapAt ℝ (γ s)) v = (e.linearMapAt ℝ (γ s)) v := rfl
      rw [hclmEq, hlm_eq]
    rw [hclm (V s), hclm ((-1 : ℝ) • V s), ContinuousLinearMap.map_smul]
  have hfib_neg_at : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1
      (fun s => (e ⟨γ s, (-1 : ℝ) • V s⟩).2) t := by
    refine (hsum_fib.contMDiffAt_iff).mpr ?_
    have hconst : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 (fun _ : ℝ => ((-1 : ℝ))) t :=
      contMDiffAt_const
    have hsmul := hconst.smul (n := (1 : WithTop ℕ∞)) (g := fun s => (e ⟨γ s, V s⟩).2)
      hVfib_at
    convert hsmul using 1
  exact hiffcV.mpr ⟨hγ_at, hfib_neg_at⟩

/-- Smoothness of the constantly-zero lift over `γ`: when `γ` is `C¹`, the lift
`t ↦ ⟨γ t, 0⟩` is `C¹`. -/
private lemma contMDiff_zeroLift {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
      (fun t => (⟨γ t, (0 : TangentSpace I (γ t))⟩ : TangentBundle I M)) := by
  classical
  intro t
  set α : M := γ t with hα
  set e := trivializationAt E (TangentSpace I) α
  have hin_src : (fun s => (⟨γ s, (0 : TangentSpace I (γ s))⟩ : TangentBundle I M)) t ∈ e.source := by
    rw [Trivialization.mem_source, TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H (γ t)
  have hiff := e.contMDiffAt_iff (IM := 𝓘(ℝ, ℝ)) (IB := I) (n := (1 : WithTop ℕ∞))
    (f := fun s => (⟨γ s, (0 : TangentSpace I (γ s))⟩ : TangentBundle I M)) hin_src
  refine hiff.mpr ⟨hγ.contMDiffAt, ?_⟩
  have hcont : Continuous γ := hγ.continuous
  have hop : IsOpen ((chartAt H α).source) := (chartAt H α).open_source
  have hmem : γ t ∈ (chartAt H α).source := mem_chart_source H α
  have hev : ∀ᶠ s in nhds t, γ s ∈ (chartAt H α).source :=
    (hcont.continuousAt).preimage_mem_nhds (hop.mem_nhds hmem)
  have hfib_eq : (fun s => (e ⟨γ s, (0 : TangentSpace I (γ s))⟩).2) =ᶠ[nhds t]
      (fun _ => (0 : E)) := by
    filter_upwards [hev] with s hs
    have hs' : γ s ∈ e.baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]; exact hs
    have hzero := e.zeroSection ℝ (x := γ s) hs'
    -- hzero : e (zeroSection E (TangentSpace I) (γ s)) = (γ s, 0)
    -- `(⟨γ s, 0⟩ : TangentBundle I M) = zeroSection E (TangentSpace I) (γ s)` definitionally.
    have : (e ⟨γ s, (0 : TangentSpace I (γ s))⟩ : M × E) = (γ s, 0) := hzero
    exact congrArg Prod.snd this
  refine hfib_eq.contMDiffAt_iff.mpr ?_
  exact contMDiffAt_const

/-! ## Uniqueness via norm preservation

The uniqueness statement does not require chart confinement: it follows directly from
the inner-product preservation theorem `isParallelAlong_inner_const` from `Defs.lean`,
combined with `covDerivAlong_add` / `covDerivAlong_smul_const` and the
positive-definiteness of the metric. -/

/-- If `V` is parallel along `γ`, then so is `(-1) • V`. -/
private lemma isParallelAlong_neg
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    {V : ∀ t, TangentSpace I (γ t)}
    {hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ}
    {hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M))}
    (hcV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, (-1 : ℝ) • V t⟩ : TangentBundle I M)))
    (hVp : IsParallelAlong (I := I) g γ V hγ hV) :
    IsParallelAlong (I := I) g γ (fun t => (-1 : ℝ) • V t) hγ hcV := by
  intro t
  have hsm := covDerivAlong_smul_const (I := I) (g := g) (-1) V hγ hV hcV t
  rw [hsm, hVp t]
  simp

/-- If `V` and `W` are parallel along `γ`, then so is the pointwise sum. -/
private lemma isParallelAlong_add
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    {V W : ∀ t, TangentSpace I (γ t)}
    {hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ}
    {hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M))}
    {hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, W t⟩ : TangentBundle I M))}
    (hVW : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t + W t⟩ : TangentBundle I M)))
    (hVp : IsParallelAlong (I := I) g γ V hγ hV)
    (hWp : IsParallelAlong (I := I) g γ W hγ hW) :
    IsParallelAlong (I := I) g γ (fun t => V t + W t) hγ hVW := by
  intro t
  have hadd := covDerivAlong_add (I := I) (g := g) V W hγ hV hW hVW t
  rw [hadd, hVp t, hWp t]
  simp

/-- The constantly-zero vector field along `γ` is parallel. -/
private lemma isParallelAlong_zero
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) :
    IsParallelAlong (I := I) g γ
      (fun t => (0 : TangentSpace I (γ t))) hγ
      (contMDiff_zeroLift (I := I) hγ) := by
  intro t
  -- `covDerivAlong g γ (0) t = 0` from the linearity of `covDerivAlong` in V.
  -- Compute the chart-(γt) covariant derivative directly from the definition.
  rw [covDerivAlong_def]
  -- The zero field's chart-fibre representation is constantly zero (on the chart-(γt) base set).
  -- Thus `deriv (chartFiberAlong γ 0 t) t = 0`.
  -- And `chartChristoffelContraction g (γt) (γ̇) 0 _ = 0` by linearity in the second slot.
  -- We compute:
  -- (1) `chartFiberAlong γ 0 t` is constantly zero locally near `t`, so its derivative is `0`.
  have hfiber_const : (chartFiberAlong (I := I) γ
      (fun s => (0 : TangentSpace I (γ s))) t) =ᶠ[nhds t] (fun _ => (0 : E)) := by
    have hev : ∀ᶠ s in nhds t, γ s ∈ (chartAt H (γ t)).source := by
      have hcont : Continuous γ := hγ.continuous
      have hop : IsOpen ((chartAt H (γ t)).source) := (chartAt H (γ t)).open_source
      have hmem : γ t ∈ (chartAt H (γ t)).source := mem_chart_source H (γ t)
      exact (hcont.continuousAt).preimage_mem_nhds (hop.mem_nhds hmem)
    filter_upwards [hev] with s hs
    unfold chartFiberAlong
    -- `chartFiberCoord (γt) ⟨γ s, 0⟩ = 0`.
    have hs' : γ s ∈ (trivializationAt E (TangentSpace I) (γ t)).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]; exact hs
    -- The zero section is sent to (γ s, 0) by the trivialisation on the base set.
    have hzero := (trivializationAt E (TangentSpace I) (γ t)).zeroSection ℝ
      (x := γ s) hs'
    have : ((trivializationAt E (TangentSpace I) (γ t))
        ⟨γ s, (0 : TangentSpace I (γ s))⟩ : M × E) = (γ s, 0) := hzero
    exact congrArg Prod.snd this
  have hderiv_zero : deriv (chartFiberAlong (I := I) γ
      (fun s => (0 : TangentSpace I (γ s))) t) t = 0 := by
    rw [hfiber_const.deriv_eq]
    exact deriv_const _ _
  -- (2) `chartChristoffelContraction g (γt) _ 0 _ = 0`.
  -- Use the existing lemma for the symmetric slot (`chartChristoffelContraction_zero_left`)
  -- combined with the symmetry of the contraction (or a direct chart-coord argument).
  have hΓ_zero : chartChristoffelContraction (I := I) g (γ t)
      (deriv (chartCurveAt (I := I) γ t) t)
      ((fun s => (0 : TangentSpace I (γ s))) t)
      (chartCurveAt (I := I) γ t t) = 0 := by
    -- `(fun s => (0 : TangentSpace I (γ s))) t = 0 : TangentSpace I (γ t)`.
    change chartChristoffelContraction (I := I) g (γ t)
        (deriv (chartCurveAt (I := I) γ t) t) (0 : E)
        (chartCurveAt (I := I) γ t t) = 0
    -- Use the symmetry to reduce to `chartChristoffelContraction_zero_left`.
    rw [chartChristoffelContraction_symm]
    exact chartChristoffelContraction_zero_left (I := I) g (γ t) _ _
  rw [hderiv_zero, hΓ_zero, add_zero]
  rfl

/-- **Uniqueness of parallel vector fields.** Two `C¹` parallel vector fields along a
`C¹` curve `γ` that agree at time `0` agree everywhere. -/
theorem isParallelAlong_unique
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    {V W : ∀ t, TangentSpace I (γ t)}
    {hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ}
    {hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M))}
    {hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, W t⟩ : TangentBundle I M))}
    (hVp : IsParallelAlong (I := I) g γ V hγ hV)
    (hWp : IsParallelAlong (I := I) g γ W hγ hW)
    (h0 : V 0 = W 0) :
    ∀ t, V t = W t := by
  classical
  intro t
  set Wneg : ∀ s, TangentSpace I (γ s) := fun s => (-1 : ℝ) • W s with hWneg_def
  have hWneg_lift : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
      (fun s => (⟨γ s, Wneg s⟩ : TangentBundle I M)) :=
    contMDiff_negLift (I := I) W hW
  have hWnegP : IsParallelAlong (I := I) g γ Wneg hγ hWneg_lift :=
    isParallelAlong_neg (I := I) (V := W) (hV := hW) hWneg_lift hWp
  set D : ∀ s, TangentSpace I (γ s) := fun s => V s + Wneg s with hD_def
  have hD_lift : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
      (fun s => (⟨γ s, D s⟩ : TangentBundle I M)) :=
    contMDiff_addLift (I := I) V Wneg hV hWneg_lift
  have hDP : IsParallelAlong (I := I) g γ D hγ hD_lift :=
    isParallelAlong_add (I := I) (V := V) (W := Wneg)
      (hV := hV) (hW := hWneg_lift) hD_lift hVp hWnegP
  have hD0 : D 0 = 0 := by
    change V 0 + (-1 : ℝ) • W 0 = 0
    rw [← h0]
    have hneg : (-1 : ℝ) • V 0 = -(V 0) := by rw [neg_one_smul]
    rw [hneg]
    exact add_neg_cancel _
  have hnorm_const : g.inner (γ t) (D t) (D t) = g.inner (γ 0) (D 0) (D 0) :=
    (IsParallelAlong.norm_const (I := I) (g := g) (V := D)
      (hV := hD_lift) hDP t 0)
  have hzero : g.inner (γ 0) (D 0) (D 0) = 0 := by
    rw [hD0]
    have h0_left : (g.inner (γ 0)) (0 : TangentSpace I (γ 0)) =
        (0 : TangentSpace I (γ 0) →L[ℝ] ℝ) :=
      map_zero (g.inner (γ 0))
    have hzero_left : (g.inner (γ 0)) (0 : TangentSpace I (γ 0))
        (0 : TangentSpace I (γ 0)) = 0 := by
      rw [h0_left]; rfl
    exact hzero_left
  have hinner_t : g.inner (γ t) (D t) (D t) = 0 := by rw [hnorm_const, hzero]
  by_contra hne_VW
  have hD_ne : D t ≠ 0 := by
    intro hD_zero
    apply hne_VW
    have hraw : V t + (-1 : ℝ) • W t = 0 := hD_zero
    have h1 : (-1 : ℝ) • W t = - W t := by rw [neg_one_smul]
    rw [h1] at hraw
    have hsub : V t - W t = 0 := by
      change V t + (- W t) = 0 at hraw
      have heq : V t - W t = V t + (- W t) := by abel
      rw [heq]; exact hraw
    exact sub_eq_zero.mp hsub
  have hpos : 0 < g.inner (γ t) (D t) (D t) := g.pos (γ t) (D t) hD_ne
  linarith

/-- **Uniqueness, chart-confined form** (chart-confinement hypothesis recorded for
symmetry with `exists_isParallelAlong_of_chart_confined`; not used in the proof). -/
theorem isParallelAlong_unique_of_chart_confined
    [I.Boundaryless] [CompleteSpace E]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    {V W : ∀ t, TangentSpace I (γ t)}
    (hγ_smooth : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M)))
    (hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, W t⟩ : TangentBundle I M)))
    (α : M) (_hγ_chart : ∀ t, γ t ∈ (chartAt H α).source)
    (hVp : IsParallelAlong (I := I) g γ V hγ_smooth hV)
    (hWp : IsParallelAlong (I := I) g γ W hγ_smooth hW)
    (h0 : V 0 = W 0) :
    ∀ t, V t = W t :=
  isParallelAlong_unique (I := I) (g := g) hVp hWp h0

/-! ## Existence (zero initial datum)

For the elementary case `V₀ = 0`, the zero vector field `V t = 0` is `C¹` and parallel.

The general existence statement for arbitrary `V₀` reduces to the global solvability
of the chart-`α` linear parallel-transport ODE
$$dw/dt = -A(t) w,\qquad A(t)(x) := \chartChristoffelContraction g\alpha(\dot\gamma_\alpha(t))\,x\,(\varphi_\alpha(\gamma t)),$$
together with the chart-`α`-to-chart-(γ t) transformation law for the Christoffel
contraction. The chart-`α` ODE solution exists on all of `ℝ` by the standard
linear-ODE theory (continuity of `A` plus Cauchy-Lipschitz on compact subintervals);
its reconstruction `V t := (\mathrm{triv}\,\alpha).\mathrm{symm}\,(\gamma t)(w t)` is
`C¹` and parallel. The chart-`α`-to-chart-(γ t) transformation is the same deep
geometric input that appears in `geodesicVectorFieldChart_chart_invariance_of_christoffel_transform`;
delivering it unconditionally is a downstream development. -/

section Existence

variable [I.Boundaryless] [CompleteSpace E]

/-- **Existence (zero initial datum).** The zero vector field along `γ` is the parallel
field with initial value `0`. -/
theorem exists_isParallelAlong_zero
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M}
    (hγ_smooth : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) :
    ∃ V : ∀ t, TangentSpace I (γ t),
      ∃ hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M)),
      V 0 = (0 : TangentSpace I (γ 0)) ∧
      IsParallelAlong (I := I) g γ V hγ_smooth hV :=
  ⟨fun t => (0 : TangentSpace I (γ t)),
    contMDiff_zeroLift (I := I) hγ_smooth, rfl,
    isParallelAlong_zero (I := I) hγ_smooth⟩

/-! ## Chart-α coefficient operator for the parallel-transport ODE

We define `chartParTransRHS g α γ t w` as the right-hand side of the chart-α linear
parallel-transport ODE: with `v_α := chartFiberCoord α (⟨γ t, V t⟩)`, the ODE reads
`v_α'(t) = chartParTransRHS g α γ t (v_α t) := -Γ_α(γ̇_α(t), v_α(t))(γ_α(t))`. The
following bilinearity and continuity properties of `chartParTransRHS` will feed
into the linear ODE existence argument. -/

/-- Chart-α coordinate representation of `γ`. -/
private def gammaChartα (α : M) (γ : ℝ → M) : ℝ → E :=
  fun t => extChartAt I α (γ t)

@[simp] private lemma gammaChartα_def (α : M) (γ : ℝ → M) (t : ℝ) :
    gammaChartα (I := I) α γ t = extChartAt I α (γ t) := rfl

/-- Chart-α velocity of `γ` at `t`. -/
private def gammaVelChartα (α : M) (γ : ℝ → M) : ℝ → E :=
  fun t => deriv (gammaChartα (I := I) α γ) t

@[simp] private lemma gammaVelChartα_def (α : M) (γ : ℝ → M) (t : ℝ) :
    gammaVelChartα (I := I) α γ t = deriv (gammaChartα (I := I) α γ) t := rfl

/-- The right-hand side of the chart-α parallel-transport ODE. -/
private def chartParTransRHS (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (t : ℝ) (w : E) : E :=
  - chartChristoffelContraction (I := I) g α
      (gammaVelChartα (I := I) α γ t) w (gammaChartα (I := I) α γ t)

@[simp] private lemma chartParTransRHS_def (g : SmoothRiemannianMetric I M) (α : M)
    (γ : ℝ → M) (t : ℝ) (w : E) :
    chartParTransRHS (I := I) g α γ t w =
      - chartChristoffelContraction (I := I) g α
          (gammaVelChartα (I := I) α γ t) w (gammaChartα (I := I) α γ t) := rfl

/-- `chartParTransRHS` at `w = 0` is zero. -/
private lemma chartParTransRHS_zero_right (g : SmoothRiemannianMetric I M) (α : M)
    (γ : ℝ → M) (t : ℝ) :
    chartParTransRHS (I := I) g α γ t (0 : E) = 0 := by
  unfold chartParTransRHS
  rw [chartChristoffelContraction_symm,
    chartChristoffelContraction_zero_left]
  exact neg_zero

/-- `chartParTransRHS` is additive in `w`. -/
private lemma chartParTransRHS_add (g : SmoothRiemannianMetric I M) (α : M)
    (γ : ℝ → M) (t : ℝ) (w₁ w₂ : E) :
    chartParTransRHS (I := I) g α γ t (w₁ + w₂) =
      chartParTransRHS (I := I) g α γ t w₁ + chartParTransRHS (I := I) g α γ t w₂ := by
  unfold chartParTransRHS
  rw [chartChristoffelContraction_add_right, neg_add]

/-- `chartParTransRHS` is `ℝ`-homogeneous in `w`. -/
private lemma chartParTransRHS_smul (g : SmoothRiemannianMetric I M) (α : M)
    (γ : ℝ → M) (t : ℝ) (c : ℝ) (w : E) :
    chartParTransRHS (I := I) g α γ t (c • w) =
      c • chartParTransRHS (I := I) g α γ t w := by
  unfold chartParTransRHS
  rw [chartChristoffelContraction_smul_right, smul_neg]

end Existence

end ParallelTransport
end Riemannian
end Geometry

end
