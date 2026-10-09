import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14

/-!
# Structural inhabitants of the final chapter-13 families over the empty manifold

Lead decision T48-4 (external review 48, item 5): the family structures do not require
`Nonempty X`, so `X := PEmpty` gives a cheap compiled fixture. It tests the field texts of the
structures (every field is satisfiable for EVERY value of the real parameters, and no field forces
a point), NOT the slim / edge / circle / zero geometry; the geometric existence evidence is the
producer (`eventually_nonempty_localChartPacketsC14`).

* `metricPEmpty_FAM`: the (vacuous) smooth Riemannian metric on the empty three-manifold
  (`ChartedSpace.empty`, `IsManifold.empty`, the metric induced from `ℝ` with the canonical
  topology of `PEmpty`).
* `nonempty_localChartPacketsC14_pempty_FAM`: an inhabitant of `LocalChartPacketsC14` for all
  parameters (empty circle / slim / edge / zero families).
* `nonempty_localChartPacketsR_pempty_FAM`, `…RV…`, `…Z…`, `…RVZ…`: the projections.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The metric on `PEmpty` (induced from `ℝ`), with the canonical topology of `PEmpty`. -/
local instance metricSpacePEmpty_FAM : MetricSpace PEmpty.{1} :=
  (MetricSpace.induced (PEmpty.elim : PEmpty.{1} → ℝ) (fun x => x.elim)
    inferInstance).replaceTopology (by ext s; simp only [Set.eq_empty_of_isEmpty s, isOpen_empty])

/-- The empty three-manifold. -/
local instance chartedSpacePEmpty_FAM : ChartedSpace E3 PEmpty.{1} :=
  ChartedSpace.empty E3 PEmpty.{1}

/-- The model metrics over the empty family (a vacuous instance). -/
local instance metricElim_FAM (a : PEmpty.{1}) : MetricSpace (a.elim : Type) := a.elim

/-- The model charts over the empty family (a vacuous instance). -/
local instance chartedElim_FAM (a : PEmpty.{1}) : ChartedSpace E3 (a.elim : Type) := a.elim

/-- The (vacuous) smooth Riemannian metric on the empty three-manifold. -/
def metricPEmpty_FAM : SmoothRiemannianMetric 𝓘(ℝ, E3) PEmpty.{1} where
  inner x := x.elim
  symm x := x.elim
  pos x := x.elim
  isVonNBounded x := x.elim
  contMDiff x := x.elim

/-- **Structural inhabitant of the final family** (T48-4): over the empty three-manifold, for all
values of the real parameters, `LocalChartPacketsC14` is inhabited (empty circle, slim, edge and
zero families; every field is vacuous). -/
theorem nonempty_localChartPacketsC14_pempty_FAM
    (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
    (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ) :
    Nonempty (LocalChartPacketsC14 PEmpty.{1} metricPEmpty_FAM (fun a => a.elim) (fun a => a.elim)
      (fun a => a.elim) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz) := by
  refine ⟨{
    toLocalChartFamilyE := ?_
    circleAdapted := ?_
    N := fun a => a.elim
    C := fun a => a.elim
    instMetricN := metricElim_FAM
    instChartedN := chartedElim_FAM
    instMetricC := metricElim_FAM
    o := fun a => a.elim
    zero :=
      { centres := ∅
        finite_centres := finite_empty
        zero := fun c => c.elim
        zero_center := fun c => c.elim
        radius_mem := fun c => c.elim
        disjoint := fun c => c.elim
        meets_stratum := fun c => c.elim
        covers_stratum := fun c => c.elim
        one_end := fun c => c.elim }
    edgeDisk := ?_
    circle_residual := ?_
    zero_local_comparison := ?_
    slim_value := ?_
    zero_shell_split := ?_
    zero_adapted := ?_
    zero_curvature := ?_
    edge_section := ?_ }⟩
  all_goals repeat' (first
    | (intros; exact (‹PEmpty.{1}›).elim)
    | exact (∅ : Set PEmpty.{1})
    | exact Set.finite_empty
    | (intro x; exact x.elim)
    | constructor)

/-- The merged family `LocalChartPacketsRVZ` over the empty manifold (projection). -/
theorem nonempty_localChartPacketsRVZ_pempty_FAM
    (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
    (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ) :
    Nonempty (LocalChartPacketsRVZ PEmpty.{1} metricPEmpty_FAM (fun a => a.elim) (fun a => a.elim)
      (fun a => a.elim) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz) :=
  (nonempty_localChartPacketsC14_pempty_FAM Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
    vs ζ Λz).map LocalChartPacketsC14.toLocalChartPacketsRVZ

/-- `LocalChartPacketsRV` over the empty manifold (projection). -/
theorem nonempty_localChartPacketsRV_pempty_FAM
    (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
    (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ) :
    Nonempty (LocalChartPacketsRV PEmpty.{1} metricPEmpty_FAM (fun a => a.elim) (fun a => a.elim)
      (fun a => a.elim) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs) :=
  (nonempty_localChartPacketsRVZ_pempty_FAM Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
    vs 0 0).map LocalChartPacketsRVZ.toLocalChartPacketsRV

/-- `LocalChartPacketsZ` over the empty manifold (projection). -/
theorem nonempty_localChartPacketsZ_pempty_FAM
    (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
    (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ) :
    Nonempty (LocalChartPacketsZ PEmpty.{1} metricPEmpty_FAM (fun a => a.elim) (fun a => a.elim)
      (fun a => a.elim) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz) :=
  (nonempty_localChartPacketsRVZ_pempty_FAM Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
    0 ζ Λz).map LocalChartPacketsRVZ.toLocalChartPacketsZ

/-- `LocalChartPacketsR` over the empty manifold (projection). -/
theorem nonempty_localChartPacketsR_pempty_FAM
    (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
    (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ) :
    Nonempty (LocalChartPacketsR PEmpty.{1} metricPEmpty_FAM (fun a => a.elim) (fun a => a.elim)
      (fun a => a.elim) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V) :=
  (nonempty_localChartPacketsRV_pempty_FAM Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
    0).map LocalChartPacketsRV.toLocalChartPacketsR

end DifferentialGeometry.Geometry.Collapse
