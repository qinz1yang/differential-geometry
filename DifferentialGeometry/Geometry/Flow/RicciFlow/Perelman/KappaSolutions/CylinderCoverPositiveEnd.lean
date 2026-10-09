import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCylinderBranch
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderDeckRecentering
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood (ancientTimeInterval)
open scoped _root_.Manifold ContDiff

local notation "S" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Cylinder" => S × ℝ
local notation "CI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local notation "gS" => roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)

private local instance translatedChartSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval}

private local instance translatedChartTopology : TopologicalSpace F.M := F.topology
private local instance translatedChartCharted : ChartedSpace H F.M := F.charted
private local instance translatedChartSmooth : IsManifold I ∞ F.M := F.smooth
private local instance translatedChartInhabited : Inhabited F.M := ⟨F.basepoint⟩
private local instance translatedChartT2 : T2Space F.M := F.t2
private local instance translatedChartLocallyPathConnected : LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M
private local instance translatedChartSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

namespace ShrinkingCylinderCover

variable (C : ShrinkingCylinderCover F)

theorem exists_partialDiffeomorph_projection_translate_of_diagonalModel
    (hmodel : C.DiagonalModel) (R : ℝ) :
    ∃ Phi : PartialDiffeomorph CI I Cylinder F.M ∞,
      Phi.toPartialEquiv.source = Set.univ ×ˢ Set.Ioi (-R) ∧
      Phi.toPartialEquiv.target =
        (C.projection ∘ cylinderLineTranslation R) '' (Set.univ ×ˢ Set.Ioi (-R)) ∧
      Phi.toFun = C.projection ∘ cylinderLineTranslation R := by
  obtain ⟨d, hd⟩ := hmodel.1
  have hlocal : IsLocalDiffeomorph CI I ∞
      (C.projection ∘ cylinderLineTranslation R) :=
    isLocalDiffeomorph_comp C.projection_local
      (cylinderLineTranslation R).isLocalDiffeomorph
  have hinj : Set.InjOn (C.projection ∘ cylinderLineTranslation R)
      (Set.univ ×ˢ Set.Ioi (-R)) := by
    intro p hp q hq heq
    have hquot :
        CylinderDiagonalQuotient.proj (cylinderLineTranslation R p) =
          CylinderDiagonalQuotient.proj (cylinderLineTranslation R q) := by
      apply d.injective
      exact (hd _).trans (heq.trans (hd _).symm)
    rcases (CylinderDiagonalQuotient.proj_eq_iff
      (cylinderLineTranslation R p) (cylinderLineTranslation R q)).mp hquot with h | h
    · exact (cylinderLineTranslation R).injective h.symm
    · have hps : -R < p.2 := hp.2
      have hqs : -R < q.2 := hq.2
      have hs := congrArg Prod.snd h
      change q.2 + R = -(p.2 + R) at hs
      linarith
  apply IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
    (hlocal.isLocalDiffeomorphOn _) (isOpen_univ.prod isOpen_Ioi) _ hinj
  exact ⟨(sphereEquator 0, -R + 1), Set.mem_univ _, by
    change -R < -R + 1
    linarith⟩

theorem mfderiv_projection_comp_lineTranslation
    (R : ℝ) (y : S) (s : ℝ) (v : TangentSpace (𝓡 2) y) (a : ℝ) :
    mfderiv CI I (C.projection ∘ cylinderLineTranslation R) (y, s) (v, a) =
      mfderiv CI I C.projection (y, s + R) (v, a) := by
  rw [mfderiv_comp_apply (y, s)
    (C.projection_local.contMDiff.mdifferentiable (by decide)
      (cylinderLineTranslation R (y, s)))
    ((cylinderLineTranslation R).mdifferentiable (by decide) (y, s)) (v, a),
    mfderiv_cylinderLineTranslation, cylinderLineTranslation_apply]
  rfl

theorem projection_translate_metric
    (R t : ℝ) (ht : t ≤ 0) (y : S) (s : ℝ)
    (v w : TangentSpace (𝓡 2) y) (a b : ℝ) :
    (F.S.family.metric t).inner ((C.projection ∘ cylinderLineTranslation R) (y, s))
        (mfderiv CI I (C.projection ∘ cylinderLineTranslation R) (y, s) (v, a))
        (mfderiv CI I (C.projection ∘ cylinderLineTranslation R) (y, s) (w, b)) =
      (2 * (C.extinctionTime - t)) * (gS).inner y v w + a * b := by
  rw [C.mfderiv_projection_comp_lineTranslation, C.mfderiv_projection_comp_lineTranslation]
  exact C.projection_metric t ht y (s + R) v w a b

end ShrinkingCylinderCover

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
