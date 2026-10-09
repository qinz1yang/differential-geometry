import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedExtensionTimeJets


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

private local instance errorJetFlowC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)


theorem exists_pointed_metric_error_time_jets
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi)
    {c : ℝ} (hcarrier : X.D.carrier = Iic c) (hregular : X.D.regular = Iio c) :
    ∃ G : ℕ → ℝ → SmoothRiemannianMetric I L.M,
    ∃ J : ℕ → ℕ → ℝ → Tensor0SField (I := I) (M := L.M) (n := ∞) 2,
      (∀ i t, J i 0 t = metricTensorField (G i t) - metricTensorField (L.S.base.metric t)) ∧
      (∀ i q t, t ≤ c → ∀ x : L.M,
        HasDerivWithinAt (fun s => J i q s x) (J i (q + 1) t x) (Iic c) t) ∧
      ∀ K : Set L.M, IsCompact K → ∀ᶠ i in atTop,
        ∃ U : Set L.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Phi.source i ∧
          ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
            (G i t).inner x v w =
              ((X.term (phi i)).S.base.metric t).inner (Phi.map i x)
                (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x w) := by
  obtain ⟨G, B, hBzero, hBderiv, hG⟩ := exists_pointed_extension_time_jets Phi hcarrier hregular
  obtain ⟨C, hCzero, hCderiv⟩ := exists_ancient_ordinary_metric_time_jets
    L.S L.isSolution hcarrier hregular
  let B' : ℕ → ℕ → ℝ → Tensor0SField (I := I) (M := L.M) (n := ∞) 2 := B
  let C' : ℕ → ℝ → Tensor0SField (I := I) (M := L.M) (n := ∞) 2 := C
  let J : ℕ → ℕ → ℝ → Tensor0SField (I := I) (M := L.M) (n := ∞) 2 :=
    fun i q t => B' i q t - C' q t
  refine ⟨G, J, ?_, ?_, hG⟩
  · intro i t
    change B' i 0 t - C' 0 t = _
    exact congrArg₂ (fun A C : Tensor0SField (I := I) (M := L.M) (n := ∞) 2 => A - C)
      (hBzero i t) (hCzero t)
  · intro i q t ht x
    change HasDerivWithinAt (fun s => B' i q s x - C' q s x)
      (B' i (q + 1) t x - C' (q + 1) t x) (Iic c) t
    exact (hBderiv i q t ht x).sub (hCderiv q t ht x).2

section ClosedWindow

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance errorJetC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

omit [CompleteSpace E] [I.Boundaryless] in
theorem tensor_time_tower_derivWithin_Icc {r : ℕ}
    (B : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) r)
    {c : ℝ} (hB : ∀ q t, t ≤ c → ∀ x : M,
      HasDerivWithinAt (fun s => B q s x) (B (q + 1) t x) (Iic c) t)
    {a b : ℝ} (hab : a < b) (hbc : b ≤ c)
    (q : ℕ) (t : ℝ) (ht : t ∈ Icc a b) (x : M) (v : Fin r → TangentSpace I x) :
    B (q + 1) t x v = derivWithin (fun s => B q s x v) (Icc a b) t := by
  have hd := (hB q t (ht.2.trans hbc) x).mono
    (fun s hs => hs.2.trans hbc : Icc a b ⊆ Iic c)
  have hv : HasDerivWithinAt (fun s => B q s x v) (B (q + 1) t x v) (Icc a b) t :=
    (tensor0SEvalCLM (I := I) (x := x) v).hasFDerivAt.comp_hasDerivWithinAt t hd
  exact (hv.derivWithin (uniqueDiffOn_Icc hab t ht)).symm

end ClosedWindow

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
