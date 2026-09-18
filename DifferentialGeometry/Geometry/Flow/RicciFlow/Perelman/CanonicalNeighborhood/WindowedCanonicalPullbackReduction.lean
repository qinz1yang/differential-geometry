import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientCanonicalNeighborhood
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureModelsReduction

set_option autoImplicit false

noncomputable section

open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped _root_.DifferentialGeometry.Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

def WindowedCanonicalPullbackAt (eps : ℝ) : Prop :=
  ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ ∀ kappa : ℝ, 0 < kappa →
    ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
        IsSolutionOn S → ∀ (x : M) (t : ℝ),
        Set.Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
        WindowedModelWitness delta kappa S x t → Nonempty (CanonicalWitness S eps C1 C2 x t)

def OrientedCanonicalPullbackAt (eps : ℝ) : Prop :=
  ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ ∀ kappa : ℝ, 0 < kappa →
    ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
        IsSolutionOn S → ∀ (o : TangentOrientationSection M) (x : M) (t : ℝ),
        Set.Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
        OrientedWitness S o delta kappa x t → Nonempty (CanonicalWitness S eps C1 C2 x t)

omit [T2Space M] [SigmaCompactSpace M] in
def WindowedModelWitness.mono_kappa {eps kappa kappa' : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa' S x t) (hpos : 0 < kappa) (hle : kappa ≤ kappa') :
    WindowedModelWitness eps kappa S x t :=
  { W with model_ancient := isAncientKappaSolution_of_kappa_le W.model_ancient hpos hle }

omit [T2Space M] [SigmaCompactSpace M] in
theorem OrientedWitness.mono_kappa {eps kappa kappa' : ℝ} {x : M} {t : ℝ}
    {o : TangentOrientationSection M} (W : OrientedWitness S o eps kappa' x t)
    (hpos : 0 < kappa) (hle : kappa ≤ kappa') :
    OrientedWitness S o eps kappa x t := by
  obtain ⟨W', oN, hO⟩ := W
  exact ⟨W'.mono_kappa hpos hle, oN, hO⟩

theorem windowedCanonicalPullbackAt_mono {eps eps' : ℝ}
    (h : WindowedCanonicalPullbackAt.{u} eps) (hle : eps ≤ eps') (hsmall : eps' < 1 / 11) :
    WindowedCanonicalPullbackAt.{u} eps' := by
  obtain ⟨C1, C2, hC1, hC2, hmain⟩ := h
  refine ⟨C1, C2, hC1, hC2, fun kappa hkappa => ?_⟩
  obtain ⟨delta, hd, hd1, himp⟩ := hmain kappa hkappa
  refine ⟨delta, hd, hd1, fun M _ _ _ _ _ D S hS x t hreg hw => ?_⟩
  obtain ⟨W⟩ := himp M D S hS x t hreg hw
  exact ⟨W.mono_eps hle hsmall⟩

theorem orientedCanonicalPullbackAt_mono {eps eps' : ℝ}
    (h : OrientedCanonicalPullbackAt.{u} eps) (hle : eps ≤ eps') (hsmall : eps' < 1 / 11) :
    OrientedCanonicalPullbackAt.{u} eps' := by
  obtain ⟨C1, C2, hC1, hC2, hmain⟩ := h
  refine ⟨C1, C2, hC1, hC2, fun kappa hkappa => ?_⟩
  obtain ⟨delta, hd, hd1, himp⟩ := hmain kappa hkappa
  refine ⟨delta, hd, hd1, fun M _ _ _ _ _ D S hS o x t hreg hw => ?_⟩
  obtain ⟨W⟩ := himp M D S hS o x t hreg hw
  exact ⟨W.mono_eps hle hsmall⟩

omit [T2Space M] [SigmaCompactSpace M] in
theorem orientedCanonicalPullbackAt_of_windowedCanonicalPullbackAt {eps : ℝ}
    (h : WindowedCanonicalPullbackAt.{u} eps) : OrientedCanonicalPullbackAt.{u} eps := by
  obtain ⟨C1, C2, hC1, hC2, hmain⟩ := h
  refine ⟨C1, C2, hC1, hC2, fun kappa hkappa => ?_⟩
  obtain ⟨delta, hd, hd1, himp⟩ := hmain kappa hkappa
  refine ⟨delta, hd, hd1, fun M _ _ _ _ _ D S hS o x t hreg hw => ?_⟩
  obtain ⟨W, _, _⟩ := hw
  exact himp M D S hS x t hreg W

omit [T2Space M] [SigmaCompactSpace M] in
theorem windowedCanonicalPullbackAt_iff_kappa_le_one {eps : ℝ} :
    WindowedCanonicalPullbackAt.{u} eps ↔
      ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ ∀ kappa : ℝ, 0 < kappa → kappa ≤ 1 →
        ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
          ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
            [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
            (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
            IsSolutionOn S → ∀ (x : M) (t : ℝ),
            Set.Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
            WindowedModelWitness delta kappa S x t →
              Nonempty (CanonicalWitness S eps C1 C2 x t) := by
  constructor
  · intro h
    obtain ⟨C1, C2, hC1, hC2, hmain⟩ := h
    exact ⟨C1, C2, hC1, hC2, fun kappa hkappa _ => hmain kappa hkappa⟩
  · rintro ⟨C1, C2, hC1, hC2, hmain⟩
    refine ⟨C1, C2, hC1, hC2, fun kappa hkappa => ?_⟩
    by_cases hkappa1 : kappa ≤ 1
    · exact hmain kappa hkappa hkappa1
    · obtain ⟨delta, hd, hd1, himp⟩ := hmain 1 one_pos le_rfl
      exact ⟨delta, hd, hd1, fun M _ _ _ _ _ D S hS x t hreg hw =>
        himp M D S hS x t hreg (hw.mono_kappa one_pos (not_le.mp hkappa1).le)⟩

omit [T2Space M] [SigmaCompactSpace M] in
theorem orientedCanonicalPullbackAt_iff_kappa_le_one {eps : ℝ} :
    OrientedCanonicalPullbackAt.{u} eps ↔
      ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ ∀ kappa : ℝ, 0 < kappa → kappa ≤ 1 →
        ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
          ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
            [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
            (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
            IsSolutionOn S → ∀ (o : TangentOrientationSection M) (x : M) (t : ℝ),
            Set.Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
            OrientedWitness S o delta kappa x t →
              Nonempty (CanonicalWitness S eps C1 C2 x t) := by
  constructor
  · intro h
    obtain ⟨C1, C2, hC1, hC2, hmain⟩ := h
    exact ⟨C1, C2, hC1, hC2, fun kappa hkappa _ => hmain kappa hkappa⟩
  · rintro ⟨C1, C2, hC1, hC2, hmain⟩
    refine ⟨C1, C2, hC1, hC2, fun kappa hkappa => ?_⟩
    by_cases hkappa1 : kappa ≤ 1
    · exact hmain kappa hkappa hkappa1
    · obtain ⟨delta, hd, hd1, himp⟩ := hmain 1 one_pos le_rfl
      exact ⟨delta, hd, hd1, fun M _ _ _ _ _ D S hS o x t hreg hw =>
        himp M D S hS o x t hreg (hw.mono_kappa one_pos (not_le.mp hkappa1).le)⟩

theorem windowedCanonicalPullback_iff_forall_eps_le :
    windowedCanonicalPullback.{u} ↔
      ∀ eps : ℝ, 0 < eps → eps ≤ 1 / 44 → WindowedCanonicalPullbackAt.{u} eps := by
  constructor
  · intro h eps heps heps44
    obtain ⟨epsCan, hepsCan, hmain⟩ := h
    exact windowedCanonicalPullbackAt_mono
      (hmain (min eps epsCan) (lt_min heps hepsCan) (min_le_right _ _))
      (min_le_left _ _) (by linarith)
  · intro h
    exact ⟨1 / 44, by norm_num, fun eps heps heps44 => h eps heps heps44⟩

theorem bufferedCanonicalPullbackFrontier_iff_forall_eps_le :
    BufferedCanonicalPullbackFrontier.{u} ↔
      ∀ eps : ℝ, 0 < eps → eps ≤ 1 / 44 → OrientedCanonicalPullbackAt.{u} eps := by
  constructor
  · intro h eps heps heps44
    obtain ⟨epsCan, hepsCan, hmain⟩ := h
    exact orientedCanonicalPullbackAt_mono
      (hmain (min eps epsCan) (lt_min heps hepsCan) (min_le_right _ _))
      (min_le_left _ _) (by linarith)
  · intro h
    exact ⟨1 / 44, by norm_num, fun eps heps heps44 => h eps heps heps44⟩

theorem windowedCanonicalPullback_iff_forall_nat :
    windowedCanonicalPullback.{u} ↔
      ∀ n : ℕ, WindowedCanonicalPullbackAt.{u} (1 / (44 * ((n : ℝ) + 1))) := by
  constructor
  · intro h n
    have hpos : 0 < 1 / (44 * ((n : ℝ) + 1)) := by positivity
    have hle : 1 / (44 * ((n : ℝ) + 1)) ≤ 1 / 44 := by
      refine one_div_le_one_div_of_le (by norm_num) ?_
      have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
      linarith
    exact (windowedCanonicalPullback_iff_forall_eps_le.mp h) _ hpos hle
  · intro h
    rw [windowedCanonicalPullback_iff_forall_eps_le]
    intro eps heps heps44
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / (44 * eps))
    have hpos44 : 0 < 44 * eps := by positivity
    have hN' : 1 < ((N : ℝ) + 1) * (44 * eps) := by
      have hlt : 1 < (N : ℝ) * (44 * eps) := (div_lt_iff₀ hpos44).mp hN
      nlinarith
    have hbase : 1 / (44 * ((N : ℝ) + 1)) ≤ eps := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hN']
    exact windowedCanonicalPullbackAt_mono (h N) hbase (by linarith)

theorem not_windowedCanonicalPullbackAt_of_one_le {kappa : ℝ}
    (P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    (hanc : IsAncientKappaSolution (I := I3) kappa P)
    (hbase : PointedFlowScalarAtBase (I := I3) P 1)
    (o : TangentOrientationSection P.M) {eps : ℝ} (heps : 1 ≤ eps) :
    ¬ WindowedCanonicalPullbackAt.{u} eps := by
  intro h
  obtain ⟨C1, C2, _hC1, _hC2, hmain⟩ := h
  obtain ⟨delta, hd, hd1, himp⟩ := hmain kappa hanc.kappa_pos
  obtain ⟨W, _, _⟩ := orientedWitness_self P hanc hbase o hd hd1
  obtain ⟨Wc⟩ := himp P.M ancientTimeInterval P.S P.isSolution P.basepoint 0 (fun _ hs => hs.2) W
  exact (isEmpty_canonicalWitness_of_one_le (S := P.S) (x := P.basepoint) (t := 0)
    (eps := eps) (C1 := C1) (C2 := C2) heps).false Wc

theorem not_orientedCanonicalPullbackAt_of_one_le {kappa : ℝ}
    (P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    (hanc : IsAncientKappaSolution (I := I3) kappa P)
    (hbase : PointedFlowScalarAtBase (I := I3) P 1)
    (o : TangentOrientationSection P.M) {eps : ℝ} (heps : 1 ≤ eps) :
    ¬ OrientedCanonicalPullbackAt.{u} eps := by
  intro h
  obtain ⟨C1, C2, _hC1, _hC2, hmain⟩ := h
  obtain ⟨delta, hd, hd1, himp⟩ := hmain kappa hanc.kappa_pos
  obtain ⟨Wc⟩ := himp P.M ancientTimeInterval P.S P.isSolution o P.basepoint 0 (fun _ hs => hs.2)
    (orientedWitness_self P hanc hbase o hd hd1)
  exact (isEmpty_canonicalWitness_of_one_le (S := P.S) (x := P.basepoint) (t := 0)
    (eps := eps) (C1 := C1) (C2 := C2) heps).false Wc

theorem kappa_canonical_neighborhood_of_windowedCanonicalPullback
    (h : windowedCanonicalPullback.{u}) :
    ∃ epsCan : ℝ, 0 < epsCan ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsCan →
      ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ ∀ kappa : ℝ, 0 < kappa →
        ∀ P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval,
          IsAncientKappaSolution (I := I3) kappa P → PointedFlowScalarAtBase (I := I3) P 1 →
          TangentOrientationSection P.M →
            Nonempty (CanonicalWitness P.S eps C1 C2 P.basepoint 0) := by
  obtain ⟨epsCan, hepsCan, hmain⟩ := h
  refine ⟨epsCan, hepsCan, fun eps heps hepsCan' => ?_⟩
  obtain ⟨C1, C2, hC1, hC2, hmain'⟩ := hmain eps heps hepsCan'
  refine ⟨C1, C2, hC1, hC2, fun kappa hkappa P hanc hbase o => ?_⟩
  obtain ⟨delta, hd, hd1, himp⟩ := hmain' kappa hkappa
  obtain ⟨W, _, _⟩ := orientedWitness_self P hanc hbase o hd hd1
  exact himp P.M ancientTimeInterval P.S P.isSolution P.basepoint 0 (fun _ hs => hs.2) W

theorem windowedCanonicalPullback_of_ancientModelClassification_halfWindow
    (hgap : ∀ (kappa : ℝ), 0 < kappa →
      ∀ P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval,
        IsAncientKappaSolution (I := I3) kappa P →
          IsShrinkingSphericalSpaceFormFlow (I := I3) P ∨
            IsAncientKappaSolution (I := I3) universalKappaConstant P)
    (hclass : ∀ eps : ℝ, 0 < eps → eps ≤ 1 / 44 →
      ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧
        ∀ P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval,
          (IsShrinkingSphericalSpaceFormFlow (I := I3) P ∨
            IsAncientKappaSolution (I := I3) universalKappaConstant P) →
          PointedFlowScalarAtBase (I := I3) P 1 →
            Nonempty (CanonicalWitness P.S (eps / 2) C1 C2 P.basepoint 0))
    (htransfer : ∀ (eps C1 C2 kappa : ℝ)
      (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
      (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
      IsSolutionOn S → ∀ (x : M) (t : ℝ),
      Set.Ioo (t - ((1 / 2) * S.scalar t x)⁻¹) t ⊆ D.regular → ∀ (W : WindowedModelWitness (1 / 2) kappa S x t),
      Nonempty (CanonicalWitness W.model.S (eps / 2) C1 C2 W.model.basepoint 0) →
        Nonempty (CanonicalWitness S (eps / 2) C1 C2 x t)) :
    windowedCanonicalPullback.{u} := by
  refine ⟨1 / 88, by norm_num, fun eps heps heps88 => ?_⟩
  obtain ⟨C1, C2, hC1, hC2, hmain⟩ := hclass (2 * eps) (by linarith) (by linarith)
  refine ⟨C1, C2, hC1, hC2, fun kappa hkappa => ?_⟩
  refine ⟨1 / 2, by norm_num, by norm_num, fun M _ _ _ _ _ D S hS x t hreg hw => ?_⟩
  have htransfer' := htransfer (2 * eps) C1 C2 kappa M D S hS x t hreg hw
    (hmain hw.model (hgap kappa hkappa hw.model hw.model_ancient) hw.model_scalar_base)
  have hcancel : 2 * eps / 2 = eps := by ring
  rwa [hcancel] at htransfer'

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
