import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Equation.Lichnerowicz
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
noncomputable section
open Bundle Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

local instance ricciTerminalC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

theorem ricciPair_hasDerivWithinAt_terminal_of_rhsContinuous
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {a b : ℝ} (hab : a < b)
    (hslab : Set.Icc a b ⊆ D.carrier) (hreg : Set.Ioo a b ⊆ D.regular)
    (x : M) (v w : TangentSpace I x)
    (hrhs : ContinuousWithinAt (fun s => ricciPairRHS S s x v w) (Set.Iio b) b) :
    HasDerivWithinAt (fun s => S.ricci s x (vec2 v w))
      (ricciPairRHS S b x v w) (Set.Iic b) b := by
  have hint (t : ℝ) (ht : t ∈ Set.Ioo a b) :
      HasDerivAt (fun s => S.ricci s x (vec2 v w)) (ricciPairRHS S t x v w) t :=
    (ricciPairCoord S hS x ⟨t, hreg ht⟩ v w).hasDerivAt
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht)
        (Set.Ioo_subset_Icc_self.trans hslab))
  have hcont : ContinuousOn (fun s => S.ricci s x (vec2 v w)) D.carrier := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact hS.ricciCont.eval_continuous (P := {s : ℝ // s ∈ D.carrier})
      (τ := Subtype.val) (b := fun _ => x) continuous_subtype_val
      (fun s => s.2) continuous_const (v := fun i _ => vec2 v w i)
      (fun _ => continuous_const)
  refine hasDerivWithinAt_Iic_of_tendsto_deriv (s := Set.Ioo a b)
    (fun t ht => (hint t ht).differentiableAt.differentiableWithinAt)
    ((hcont b (hslab ⟨hab.le, le_rfl⟩)).mono
      (Set.Ioo_subset_Icc_self.trans hslab)) (Ioo_mem_nhdsLT hab) ?_
  exact hrhs.tendsto.congr'
    (Filter.eventuallyEq_of_mem (Ioo_mem_nhdsLT hab) fun t ht => (hint t ht).deriv).symm

theorem ricciPair_terminal_nonpos_of_nonnegative_of_rhsContinuous
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {a b : ℝ} (hab : a < b)
    (hslab : Set.Icc a b ⊆ D.carrier) (hreg : Set.Ioo a b ⊆ D.regular)
    (x : M) (v : TangentSpace I x)
    (hrhs : ContinuousWithinAt (fun s => ricciPairRHS S s x v v) (Set.Iio b) b)
    (hnonneg : ∀ s ∈ Set.Icc a b, 0 ≤ S.ricci s x (vec2 v v))
    (hzero : S.ricci b x (vec2 v v) = 0) :
    ricciPairRHS S b x v v ≤ 0 := by
  have hd := ricciPair_hasDerivWithinAt_terminal_of_rhsContinuous
    S hS hab hslab hreg x v v hrhs
  have hlim : Tendsto (slope (fun s => S.ricci s x (vec2 v v)) b)
      (𝓝[<] b) (𝓝 (ricciPairRHS S b x v v)) :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp : b ∉ Set.Iio b)).mp
      (hd.mono Set.Iio_subset_Iic_self)
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT hab] with s hs
  rw [slope_def_field, hzero, sub_zero]
  exact div_nonpos_of_nonneg_of_nonpos (hnonneg s ⟨hs.1.le, hs.2.le⟩)
    (sub_nonpos.mpr hs.2.le)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
