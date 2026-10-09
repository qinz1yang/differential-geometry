import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ForwardFlatness


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution

open Set
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} {F : PointedFlowData.{u, uE, uH} (I := I) D}

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : T2Space F.M := F.t2
private local instance : SigmaCompactSpace F.M := F.sigmaCompact

theorem exists_rmNormSq_ne_zero_before
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (b : ℝ) :
    ∃ t : ℝ, t < b ∧ t ∈ D.carrier ∧ ∃ x : F.M, F.rmNormSq (I := I) t x ≠ 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨tw, htw, y, hy⟩ := hF.notFlat
  have htw0 : tw ≤ 0 := by
    simpa only [hF.carrier_eq, mem_Iic] using htw
  let a : ℝ := min tw b - 1
  have hatw : a < tw := by
    dsimp only [a]
    linarith [min_le_left tw b]
  have hab : a < b := by
    dsimp only [a]
    linarith [min_le_right tw b]
  have hcarrier : Icc a tw ⊆ D.carrier := by
    intro t ht
    simpa only [hF.carrier_eq, mem_Iic] using ht.2.trans htw0
  have hregular : Ico a tw ⊆ D.regular := by
    intro t ht
    simpa only [hF.regular_eq, mem_Iio] using ht.2.trans_le htw0
  obtain ⟨K, hK⟩ := hF.exists_rmNormSq_le
  have hbound : ∃ C : ℝ, ∀ t ∈ Icc a tw, ∀ x : F.M,
      F.rmNormSq (I := I) t x ≤ C :=
    ⟨K, fun t ht x => hK t (hcarrier ht) x⟩
  have hnotflat : ¬ ∀ x : F.M, F.rmNormSq (I := I) a x = 0 := by
    intro hflat
    have hprop := complete_forward_flatness F hatw hcarrier hregular
      (fun t ht => hF.complete t (hcarrier ht)) hbound hflat
    exact hy (hprop tw ⟨hatw.le, le_rfl⟩ y)
  obtain ⟨x, hx⟩ := not_forall.mp hnotflat
  exact ⟨a, hab, hcarrier ⟨le_rfl, hatw.le⟩, x, hx⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution
