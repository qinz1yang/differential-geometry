import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.BallComplementCylinder
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ProjectivePresentation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapCollarDepth

noncomputable section

open Set Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps t : ℝ} {x : M} {U : Set M}

theorem LocalCap.exists_ball_complement_chart_of_core_ball_complement_chart
    (cap : LocalCap S eps x t U)
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace ThreeSpace Z] [T2Space Z] [CompactSpace Z]
    (b : PartialDiffeomorph I3 I3 ThreeSpace Z ∞)
    (P : PartialDiffeomorph I3 I3 Z M ∞)
    (hb : closedBall (0 : ThreeSpace) 1 ⊆ b.source)
    (hP : (b '' ball (0 : ThreeSpace) 1)ᶜ ⊆ P.source)
    (hcore : P '' (b '' ball (0 : ThreeSpace) 1)ᶜ = cap.core.carrier) :
    ∃ (B : PartialDiffeomorph I3 I3 Z M ∞)
      (F : ThreeSpace ≃ₘ⟮I3, I3⟯ ThreeSpace),
      F '' closedBall (0 : ThreeSpace) 1 = closedBall (0 : ThreeSpace) 1 ∧
      ((b ∘ F) '' ball (0 : ThreeSpace) (1 / 2))ᶜ ⊆ B.source ∧
      B '' ((b ∘ F) '' ball (0 : ThreeSpace) (1 / 2))ᶜ = U ∧
      EqOn B P (b '' ball (0 : ThreeSpace) 1)ᶜ ∧
      (∀ q : Sphere 2, ∀ a ∈ Icc (0 : ℝ) 1,
        B (b (F ((1 - a / 2) • (q : ThreeSpace)))) = cap.tubeMap (q, a)) ∧
      ∃ V : Set Cylinder, IsOpen V ∧ univ ×ˢ Icc (0 : ℝ) 1 ⊆ V ∧
        EqOn (fun q => B (b (F ((1 - q.2 / 2) • (q.1 : ThreeSpace))))) cap.tubeMap V := by
  have hK : IsCompact (b '' ball (0 : ThreeSpace) 1)ᶜ :=
    (b.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_ball
      (ball_subset_closedBall.trans hb)).isClosed_compl.isCompact
  have hboundary : P '' (b '' sphere (0 : ThreeSpace) 1) =
      range (fun q : Sphere 2 => cap.tubeMap (q, 0)) := by
    rw [DifferentialGeometry.Topology.Manifold.image_sphere_eq_frontier_of_ball_complement
      b P hb hK hP, hcore, ← cap.inner_boundary]
    ext y
    constructor
    · rintro ⟨⟨q, a⟩, ha, rfl⟩
      have ha0 : a = 0 := ha.2
      exact ⟨q, by rw [ha0]⟩
    · rintro ⟨q, rfl⟩
      exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  obtain ⟨B, F, hF, hBs, hBi, hBP, hBT, V, hVo, hVs, hBV⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_ball_complement_chart_of_ball_complement_and_cylinder
      b P cap.tubeMap hb hP cap.tube_domain hboundary
      (fun q a ha hm => (cap.tube_map_mem_core_iff ha).mp (hcore ▸ hm))
  refine ⟨B, F, hF, hBs, ?_, hBP, hBT, V, hVo, hVs, hBV⟩
  rw [hBi, hcore, cap.tube_eq, ← cap.union_eq]

theorem LocalCap.exists_projective_model_of_core_projective_chart
    (cap : LocalCap S eps x t U)
    {Z : Type u} [TopologicalSpace Z] [ChartedSpace ThreeSpace Z]
    [IsManifold I3 ∞ Z] [T2Space Z] [CompactSpace Z]
    (pr : ProjectivePresentation Z)
    (b : PartialDiffeomorph I3 I3 ThreeSpace Z ∞)
    (P : PartialDiffeomorph I3 I3 Z M ∞)
    (hb : closedBall (0 : ThreeSpace) 1 ⊆ b.source)
    (hP : (b '' ball (0 : ThreeSpace) 1)ᶜ ⊆ P.source)
    (hcore : P '' (b '' ball (0 : ThreeSpace) 1)ᶜ = cap.core.carrier) :
    ∃ (e : RealProjectiveThreeSpace ≃ₘ⟮I3, I3⟯ Z),
      (∀ a : Sphere 3, e (realProjectiveSpaceQuotientMap a) = pr.quotient a) ∧
      ∃ (b' : PartialDiffeomorph I3 I3 ThreeSpace Z ∞)
      (B : PartialDiffeomorph I3 I3 Z M ∞)
      (F : ThreeSpace ≃ₘ⟮I3, I3⟯ ThreeSpace),
      (∀ z, b' z = b (F ((1 / 2 : ℝ) • z))) ∧
      F '' closedBall (0 : ThreeSpace) 1 = closedBall (0 : ThreeSpace) 1 ∧
      closedBall (0 : ThreeSpace) 2 ⊆ b'.source ∧
      (b' '' ball (0 : ThreeSpace) 1)ᶜ ⊆ B.source ∧
      B '' (b' '' ball (0 : ThreeSpace) 1)ᶜ = U ∧
      EqOn B P (b '' ball (0 : ThreeSpace) 1)ᶜ ∧
      (∀ q : Sphere 2, ∀ a ∈ Icc (0 : ℝ) 1,
        B (b' ((2 - a) • (q : ThreeSpace))) = cap.tubeMap (q, a)) ∧
      Nonempty (CapCore U) ∧
      ∃ V : Set Cylinder, IsOpen V ∧ univ ×ˢ Icc (0 : ℝ) 1 ⊆ V ∧
        EqOn (fun q => B (b' ((2 - q.2) • (q.1 : ThreeSpace)))) cap.tubeMap V := by
  obtain ⟨e, he⟩ := pr.exists_realProjectiveThree_diffeomorph
  refine ⟨e, he, ?_⟩
  obtain ⟨B, F, hF, hBs, hBi, hBP, hBT, V, hVo, hVs, hBV⟩ :=
    cap.exists_ball_complement_chart_of_core_ball_complement_chart b P hb hP hcore
  let D : ThreeSpace ≃ₘ[ℝ] ThreeSpace :=
    (LinearEquiv.smulOfNeZero ℝ ThreeSpace (1 / 2 : ℝ) (by norm_num)).toContinuousLinearEquiv.toDiffeomorph
  let b' := (D.toPartialDiffeomorph.trans F.toPartialDiffeomorph).trans b
  have hb' : closedBall (0 : ThreeSpace) 2 ⊆ b'.source := by
    intro z hz
    refine ⟨⟨mem_univ _, mem_univ _⟩, hb ?_⟩
    apply hF.subset
    refine ⟨(1 / 2 : ℝ) • z, ?_, rfl⟩
    rw [mem_closedBall_zero_iff, norm_smul]
    have hn := mem_closedBall_zero_iff.mp hz
    norm_num
    linarith
  have hball : b' '' ball (0 : ThreeSpace) 1 =
      (b ∘ F) '' ball (0 : ThreeSpace) (1 / 2) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(1 / 2 : ℝ) • z, ?_, rfl⟩
      rw [mem_ball_zero_iff, norm_smul]
      have hn := mem_ball_zero_iff.mp hz
      norm_num
      linarith
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(2 : ℝ) • z, ?_, ?_⟩
      · rw [mem_ball_zero_iff, norm_smul]
        have hn := mem_ball_zero_iff.mp hz
        norm_num
        linarith
      · change b (F ((1 / 2 : ℝ) • ((2 : ℝ) • z))) = b (F z)
        rw [smul_smul]
        norm_num
  have hb's : (b' '' ball (0 : ThreeSpace) 1)ᶜ ⊆ B.source := hball.symm ▸ hBs
  have hbi : B '' (b' '' ball (0 : ThreeSpace) 1)ᶜ = U := hball.symm ▸ hBi
  refine ⟨b', B, F, fun _ => rfl, hF, hb', hb's, hbi, hBP, ?_,
    ⟨CapCore.projective Z pr b' hb' B hb's hbi⟩, V, hVo, hVs, ?_⟩
  · intro q a ha
    change B (b (F ((1 / 2 : ℝ) • ((2 - a) • (q : ThreeSpace))))) = _
    have heq : (1 / 2 : ℝ) • ((2 - a) • (q : ThreeSpace)) =
        (1 - a / 2) • (q : ThreeSpace) := by rw [smul_smul]; congr 1; ring
    rw [heq]
    exact hBT q a ha
  · intro q hq
    change B (b (F ((1 / 2 : ℝ) • ((2 - q.2) • (q.1 : ThreeSpace))))) = _
    have heq : (1 / 2 : ℝ) • ((2 - q.2) • (q.1 : ThreeSpace)) =
        (1 - q.2 / 2) • (q.1 : ThreeSpace) := by rw [smul_smul]; congr 1; ring
    rw [heq]
    exact hBV hq

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
