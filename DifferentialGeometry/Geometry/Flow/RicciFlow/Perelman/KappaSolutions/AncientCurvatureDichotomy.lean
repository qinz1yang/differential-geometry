import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Positivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance ancientPositiveTopology : TopologicalSpace F.M := F.topology
private local instance ancientPositiveCharted : ChartedSpace H F.M := F.charted
private local instance ancientPositiveSmooth : IsManifold I ∞ F.M := F.smooth
private local instance ancientPositiveT2 : T2Space F.M := F.t2

def AncientPositiveCurvatureOperator : Prop :=
  ∀ t : ℝ, t ≤ 0 → ∀ x : F.M, CurvatureOperatorPositiveAt (F.S.family.metric t) x

omit [I.Boundaryless] in
theorem ancientKappa_positive_or_null_plane {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3) :
    AncientPositiveCurvatureOperator F ∨
      ∃ t : ℝ, t ≤ 0 ∧ ∃ x : F.M, ∃ a b : TangentSpace I x,
        0 < (F.S.family.metric t).inner x a a * (F.S.family.metric t).inner x b b -
          ((F.S.family.metric t).inner x a b) ^ 2 ∧
        F.S.base.rm04 t x (vec4 (I := I) a b b a) = 0 := by
  classical
  by_cases hpositive : AncientPositiveCurvatureOperator F
  · exact Or.inl hpositive
  · right
    change ¬ ∀ t : ℝ, t ≤ 0 → ∀ x : F.M,
      CurvatureOperatorPositiveAt (F.S.family.metric t) x at hpositive
    push Not at hpositive
    obtain ⟨t, ht, x, hx⟩ := hpositive
    have hplanes := (not_congr
      (curvatureOperatorPositiveAt_iff_sectional (F.S.family.metric t) x hdim)).mp hx
    push Not at hplanes
    obtain ⟨a, b, hgram, hnonpos⟩ := hplanes
    refine ⟨t, ht, x, a, b, hgram, ?_⟩
    have hnonneg : 0 ≤ F.S.base.rm04 t x (vec4 (I := I) a b b a) := by
      have h := hF.nonnegativeCurvatureOperator t (by simpa using ht)
      simpa only [Fin.sum_univ_one, one_mul] using
        (h x 1 (fun _ => 1) (fun _ => a) (fun _ => b))
    exact le_antisymm hnonpos hnonneg

omit [I.Boundaryless] in
theorem ancientPositiveCurvatureOperator_not_null_plane
    (hF : AncientPositiveCurvatureOperator F) (hdim : Module.finrank ℝ E = 3)
    (t : ℝ) (ht : t ≤ 0) (x : F.M) (a b : TangentSpace I x)
    (hgram : 0 <
      (F.S.family.metric t).inner x a a * (F.S.family.metric t).inner x b b -
        ((F.S.family.metric t).inner x a b) ^ 2)
    (hnull : F.S.base.rm04 t x (vec4 (I := I) a b b a) = 0) : False := by
  have hpos := (curvatureOperatorPositiveAt_iff_sectional
    (F.S.family.metric t) x hdim).mp (hF t ht x) a b hgram
  exact (ne_of_gt hpos) hnull

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
