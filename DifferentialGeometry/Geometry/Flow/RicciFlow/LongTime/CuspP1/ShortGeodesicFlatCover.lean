import DifferentialGeometry.Geometry.Exponential.Flat.FlatTorusSmooth
import DifferentialGeometry.Geometry.Exponential.Flat.TorusTypeApplications
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Smoothness
import DifferentialGeometry.Geometry.Curvature.DimensionTwo.SectionalScalarBound
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.TorusGluing

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.Exponential
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
namespace GC.LongTime.CuspP1

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- `exp_p` of a compact flat orientable surface is a periodic cover with an explicit lattice
(same as `exists_periodic_cover_of_flat`, but remembering that the cover is `exp_p`). -/
theorem exists_exp_lattice_of_flat_CPA2 (hdim : Module.finrank ℝ E = 2) [CompactSpace M]
    [ConnectedSpace M] (o : DifferentialGeometry.ManifoldOrientation I M 2)
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hR : ∀ x (X Y Z : TangentSpace I x), riemannOp (LeviCivita (I := I) g) x X Y Z = 0)
    (p : M) :
    ∃ v₁ v₂ : E,
      IsLocalDiffeomorph 𝓘(ℝ, E) I ∞
        (fun z : E => expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from z)) ∧
      Surjective
        (fun z : E => expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from z)) ∧
      LinearIndependent ℝ ![v₁, v₂] ∧
      ∀ y z : E,
        expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from y) =
          expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from z) ↔
        ∃ m n : ℤ, z - y = m • v₁ + n • v₂ := by
  let F : E → M := fun z => expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from z)
  obtain ⟨hloc, -, hcovF, hsurj⟩ :=
    flat_expMapIntrinsic_isLocalIsometry_isCoveringMap (I := I) g hEnorm hR p
  obtain ⟨Λ, hdisc, hfibΛ⟩ := flat_exists_translationLattice (I := I) hdim o g hEnorm hR p
  have hopen : ∀ n : ℕ, IsOpen (F '' Metric.ball (0 : E) n) := fun n =>
    hloc.isOpenMap _ Metric.isOpen_ball
  have hcover : (univ : Set M) ⊆ ⋃ n : ℕ, F '' Metric.ball (0 : E) n := by
    intro q _
    obtain ⟨y, rfl⟩ := hsurj q
    obtain ⟨n, hn⟩ := exists_nat_gt ‖y‖
    exact mem_iUnion.mpr ⟨n, y, mem_ball_zero_iff.mpr hn, rfl⟩
  have hmono : Monotone fun n : ℕ => F '' Metric.ball (0 : E) n := fun a c hac =>
    image_mono (Metric.ball_subset_ball (by exact_mod_cast hac))
  obtain ⟨n, hn⟩ := isCompact_univ.elim_directed_cover _ hopen hcover hmono.directed_le
  have hcocpt : ∀ y : E, ∃ l ∈ Λ.toIntSubmodule, ‖y - l‖ ≤ n := by
    intro y
    obtain ⟨z, hz, hFz⟩ := hn (mem_univ (F y))
    refine ⟨y - z, (hfibΛ z y).mp hFz, ?_⟩
    rw [sub_sub_cancel]
    exact (mem_ball_zero_iff.mp hz).le
  have : DiscreteTopology Λ.toIntSubmodule := hdisc
  obtain ⟨b, hb⟩ :=
    DifferentialGeometry.Geometry.FlatSurface.exists_basis_span_eq_of_discrete_of_cocompact
      Λ.toIntSubmodule hcocpt
  let b₂ := b.reindex (finCongr hdim)
  have hrange : Set.range b = {b₂ 0, b₂ 1} := by
    rw [← b.range_reindex (finCongr hdim)]
    ext x
    simp only [Set.mem_range, Fin.exists_fin_two, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | h) <;> [exact Or.inl h.symm; exact Or.inr h.symm]
    · rintro (h | h) <;> [exact Or.inl h.symm; exact Or.inr h.symm]
  refine ⟨b₂ 0, b₂ 1, hloc, hsurj, ?_, ?_⟩
  · have h := b₂.linearIndependent
    convert h using 1
    ext i
    fin_cases i <;> rfl
  · intro y z
    rw [hfibΛ y z]
    change z - y ∈ Λ.toIntSubmodule ↔ _
    rw [← hb, hrange, Submodule.mem_span_pair]
    constructor
    · rintro ⟨m, k, h⟩
      exact ⟨m, k, h.symm⟩
    · rintro ⟨m, k, h⟩
      exact ⟨m, k, h.symm⟩

end Generic

end GC.LongTime.CuspP1
