import DifferentialGeometry.Topology.ThreeManifold.CapBallChart
import DifferentialGeometry.Topology.Manifold.SpherePolarCoordinates
import DifferentialGeometry.Topology.Manifold.InjectiveLocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.CollarReparametrization

noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1
local notation "CI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

def capShellMap (b : T.Boundary) (q : S2 × ℝ) : N.Carrier :=
  (C.capBallChart b).chart (q.2 • (q.1 : E3))

private theorem norm_radial (q : S2 × ℝ) (hq : 0 < q.2) :
    ‖q.2 • (q.1 : E3)‖ = q.2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hq, norm_eq_of_mem_sphere, mul_one]

private theorem radial_mem_capBallChart_source (b : T.Boundary) (q : S2 × ℝ)
    (hq : q.2 ∈ Ioo (0 : ℝ) 4) : q.2 • (q.1 : E3) ∈ (C.capBallChart b).chart.source := by
  rw [C.capBallChart_source, mem_ball_zero_iff, norm_radial q hq.1]
  exact hq.2

theorem isLocalDiffeomorphAt_capShellMap (b : T.Boundary) (q : S2 × ℝ)
    (hq : q.2 ∈ Ioo (0 : ℝ) 4) :
    IsLocalDiffeomorphAt CI (𝓡 3) ∞ (C.capShellMap b) q :=
  Manifold.isLocalDiffeomorphAt_chart_sphere_smul (C.capBallChart b).chart q hq.1
    (C.radial_mem_capBallChart_source b q hq)

theorem capShellMap_injOn (b : T.Boundary) :
    InjOn (C.capShellMap b) (univ ×ˢ Ioo (0 : ℝ) 4) := by
  intro p hp q hq h
  have heq := (C.capBallChart b).chart.injOn
    (C.radial_mem_capBallChart_source b p hp.2) (C.radial_mem_capBallChart_source b q hq.2) h
  have hrad : p.2 = q.2 := by
    have hn := congrArg norm heq
    rwa [norm_radial p hp.2.1, norm_radial q hq.2.1] at hn
  apply Prod.ext
  · apply Subtype.ext
    apply (smul_right_injective E3 (ne_of_gt hp.2.1))
    rwa [← hrad] at heq
  · exact hrad

private theorem norm_cap_radial_lt_one (b : T.Boundary) (q : S2 × ℝ)
    (hq : q.2 ∈ Ioo (0 : ℝ) 4) :
    ‖(if b.2 then (1 / 4 : ℝ) else -(1 / 4 : ℝ)) • (q.2 • (q.1 : E3))‖ < 1 := by
  rw [norm_smul, Real.norm_eq_abs, norm_radial q hq.1]
  have h : |if b.2 then (1 / 4 : ℝ) else -(1 / 4 : ℝ)| = 1 / 4 := by cases b.2 <;> norm_num
  rw [h]
  linarith [hq.2]

theorem capShellMap_eq_cap (b : T.Boundary) (q : S2 × ℝ) (hq : q.2 ∈ Ioo (0 : ℝ) 4) :
    C.capShellMap b q = C.cap b
      ⟨(if b.2 then (1 / 4 : ℝ) else -(1 / 4 : ℝ)) • (q.2 • (q.1 : E3)),
        (norm_cap_radial_lt_one b q hq).le⟩ :=
  C.capBallChart_apply b _ (norm_cap_radial_lt_one b q hq)

@[simp] theorem capShellMap_one (b : T.Boundary) (z : S2) :
    C.capShellMap b (z, 1) = ((C.capBallChart b).toBallChart.boundaryMap z).val := by
  simp only [capShellMap, one_smul]
  rfl

theorem exists_capShell_partialDiffeomorph (b : T.Boundary) :
    ∃ e : PartialDiffeomorph CI (𝓡 3) (S2 × ℝ) N.Carrier ∞,
      e.source = univ ×ˢ Ioo (0 : ℝ) 4 ∧
      e.target = C.capShellMap b '' (univ ×ˢ Ioo (0 : ℝ) 4) ∧
      (e : S2 × ℝ → N.Carrier) = C.capShellMap b := by
  let _ : Nonempty S2 := ⟨⟨EuclideanSpace.single 0 1, by simp⟩⟩
  exact Manifold.exists_partialDiffeomorph_of_injOn (isOpen_univ.prod isOpen_Ioo)
    (fun q => C.isLocalDiffeomorphAt_capShellMap b q.val q.property.2) (C.capShellMap_injOn b)

theorem capShellMap_image_subset_cap_interior (b : T.Boundary) :
    C.capShellMap b '' (univ ×ˢ Ioo (0 : ℝ) 4) ⊆
      C.cap b '' {x : ClosedCell 3 | ‖x.val‖ < 1} := by
  rintro y ⟨q, hq, rfl⟩
  rw [← C.capBallChart_target]
  exact (C.capBallChart b).chart.map_source (C.radial_mem_capBallChart_source b q hq.2)

theorem disjoint_capShellMap_image_core (b : T.Boundary) :
    Disjoint (C.capShellMap b '' (univ ×ˢ Ioo (0 : ℝ) 4)) (range C.coreInclusion) := by
  let _ : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) := Handle.closedCellChartedSpaceSucc 2
  apply Set.disjoint_left.mpr
  intro y hy hcore
  obtain ⟨p, hp, rfl⟩ := C.capShellMap_image_subset_cap_interior b hy
  have hboth : C.cap b p ∈ range C.coreInclusion ∩ range (C.cap b) := ⟨hcore, ⟨p, rfl⟩⟩
  rw [C.core_cap_intersection b] at hboth
  obtain ⟨z, hz⟩ := hboth
  have hcap : C.cap b (sphereToClosedCell ((C.attaching b).symm z)) = C.cap b p := by
    rw [C.boundary_eq b ((C.attaching b).symm z), Diffeomorph.apply_symm_apply]
    exact hz
  have heq := congrArg (fun q : ClosedCell 3 => ‖q.val‖) ((C.cap_embedding b).isEmbedding.injective hcap)
  have hz1 : ‖(sphereToClosedCell ((C.attaching b).symm z)).val‖ = 1 :=
    mem_sphere_zero_iff_norm.mp ((C.attaching b).symm z).property
  rw [hz1] at heq
  exact (ne_of_lt hp) heq.symm

theorem exists_capShell_reparametrization (b : T.Boundary) (r₀ r₁ : ℝ)
    (hr₀ : r₀ ∈ Ioo (0 : ℝ) 4) (hr₁ : r₁ ∈ Ioo (0 : ℝ) 4) :
    ∃ (φ : ℝ ≃ₘ[ℝ] ℝ) (F : N.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ N.Carrier),
      φ r₀ = r₁ ∧ (∀ r, 0 < deriv φ r) ∧
      (∀ z r, r ∈ Ioo (0 : ℝ) 4 → F (C.capShellMap b (z, r)) = C.capShellMap b (z, φ r)) ∧
      (∀ z r, r ∈ Ioo (0 : ℝ) 4 → F.symm (C.capShellMap b (z, r)) =
        C.capShellMap b (z, φ.symm r)) ∧
      (∀ x : T.core, F (C.coreInclusion x) = C.coreInclusion x ∧
        F.symm (C.coreInclusion x) = C.coreInclusion x) ∧
      (∀ b' : T.Boundary, b' ≠ b → ∀ x : ClosedCell 3,
        F (C.cap b' x) = C.cap b' x ∧ F.symm (C.cap b' x) = C.cap b' x) ∧
      ∃ K : Set N.Carrier, IsCompact K ∧ K ⊆ C.capShellMap b '' (univ ×ˢ Ioo (0 : ℝ) 4) ∧
        ∀ x, x ∉ K → F x = x ∧ F.symm x = x := by
  obtain ⟨e, hs, ht, he⟩ := C.exists_capShell_partialDiffeomorph b
  obtain ⟨φ, _, _, _, hmove, hpos, _, F, _, _, _, hF, hFi, K, hK, hKe, hfix⟩ :=
    e.exists_collar_reparametrization_isotopy hr₀ hr₁ (by rw [hs])
  have hKsub : K ⊆ C.capShellMap b '' (univ ×ˢ Ioo (0 : ℝ) 4) := by
    simpa only [he] using hKe
  have hfix' (x : N.Carrier) (hx : x ∉ K) : F 1 x = x ∧ (F 1).symm x = x :=
    ⟨(hfix 1).1 hx, (hfix 1).2 hx⟩
  refine ⟨φ 1, F 1, ?_, hpos 1, ?_, ?_, ?_, ?_, K, hK, hKsub, hfix'⟩
  · have h := hmove 1 ⟨zero_le_one, le_rfl⟩
    simpa using h
  · intro z r hr
    have h := hF 1 (z, r) (hs ▸ ⟨mem_univ _, hr⟩)
    simpa only [he] using h
  · intro z r hr
    have h := hFi 1 (z, r) (hs ▸ ⟨mem_univ _, hr⟩)
    simpa only [he] using h
  · intro x
    apply hfix'
    intro hx
    exact Set.disjoint_left.mp (C.disjoint_capShellMap_image_core b) (hKsub hx) ⟨x, rfl⟩
  · intro b' hne x
    apply hfix'
    intro hx
    obtain ⟨y, _, hy⟩ := C.capShellMap_image_subset_cap_interior b (hKsub hx)
    exact Set.disjoint_left.mp (C.cap_disjoint hne.symm) ⟨y, hy⟩ ⟨x, rfl⟩

end DifferentialGeometry.Topology.SphericalCapping
