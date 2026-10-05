import DifferentialGeometry.Topology.Attachment.Defs
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

open scoped Manifold Topology

namespace DifferentialGeometry.Topology.Handle

noncomputable section

universe u v w

noncomputable def cellBoundarySphereHomeomorph (k : ℕ) :
    CellBoundary k ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 where
  toFun := fun x => ⟨x.1, by
    change dist (x.1 : EuclideanSpace ℝ (Fin k)) 0 = 1
    rw [dist_eq_norm, sub_zero]
    exact x.2⟩
  invFun := fun x => ⟨x.1, by
    have hx := x.2
    change dist (x.1 : EuclideanSpace ℝ (Fin k)) 0 = 1 at hx
    rw [dist_eq_norm, sub_zero] at hx
    exact hx⟩
  left_inv := by
    intro x
    apply Subtype.ext
    rfl
  right_inv := by
    intro x
    apply Subtype.ext
    rfl
  continuous_toFun := by
    exact Continuous.subtype_mk continuous_subtype_val (fun x => by
      change dist (x.1 : EuclideanSpace ℝ (Fin k)) 0 = 1
      rw [dist_eq_norm, sub_zero]
      exact x.2)
  continuous_invFun := by
    exact Continuous.subtype_mk continuous_subtype_val (fun x => by
      have hx := x.2
      change dist (x.1 : EuclideanSpace ℝ (Fin k)) 0 = 1 at hx
      rw [dist_eq_norm, sub_zero] at hx
      exact hx)

instance (k : ℕ) : Neg (CellBoundary k) :=
  ⟨fun x => ⟨-x.1, by simp [x.2]⟩⟩

instance (k : ℕ) [NeZero k] :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = (k - 1) + 1) := by
  exact ⟨by
    have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = k := by simp
    rw [hfin]
    have hk : 0 < k := NeZero.pos k
    omega⟩

instance (k : ℕ) [NeZero k] : Fact (k = (k - 1) + 1) := by
  exact ⟨by
    have hk : 0 < k := NeZero.pos k
    omega⟩

noncomputable def cellBoundaryChart (k : ℕ)
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = (k - 1) + 1)]
    (v : CellBoundary k) :
    OpenPartialHomeomorph (CellBoundary k) (EuclideanSpace ℝ (Fin (k - 1))) :=
  (cellBoundarySphereHomeomorph k).toOpenPartialHomeomorph ≫ₕ
    stereographic' (k - 1) (cellBoundarySphereHomeomorph k v)

@[reducible]
noncomputable def cellBoundaryChartedSpace (k : ℕ)
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = (k - 1) + 1)] :
    ChartedSpace (EuclideanSpace ℝ (Fin (k - 1))) (CellBoundary k) where
  atlas := Set.range (fun v : CellBoundary k => cellBoundaryChart k v)
  chartAt := fun v : CellBoundary k => cellBoundaryChart k (-v)
  mem_chart_source := by
    intro v
    have hne : v ≠ -v := by
      intro h
      have h0 : (v : EuclideanSpace ℝ (Fin k)) = 0 := by
        have h2 : (2 : ℝ) • (v : EuclideanSpace ℝ (Fin k)) = 0 := by
          have h' : (v : EuclideanSpace ℝ (Fin k)) = -(v : EuclideanSpace ℝ (Fin k)) :=
            congrArg (fun z : CellBoundary k => (z : EuclideanSpace ℝ (Fin k))) h
          have hplus : (v : EuclideanSpace ℝ (Fin k)) + (v : EuclideanSpace ℝ (Fin k)) = 0 := by
            nth_rewrite 1 [h']
            simp
          simpa [two_smul] using hplus
        exact smul_eq_zero.mp h2 |>.resolve_left (by norm_num)
      have hnorm : ‖(v : EuclideanSpace ℝ (Fin k))‖ = 1 := v.2
      rw [h0] at hnorm
      norm_num at hnorm
    change v ∈ (cellBoundaryChart k (-v)).source
    dsimp [cellBoundaryChart]
    constructor
    · trivial
    · change (cellBoundarySphereHomeomorph k v) ∈
        (stereographic' (k - 1) (cellBoundarySphereHomeomorph k (-v))).source
      rw [stereographic'_source]
      change (cellBoundarySphereHomeomorph k v) ≠ (cellBoundarySphereHomeomorph k (-v))
      exact fun hh => hne (by
        have hh' := congrArg (fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 => z.1) hh
        exact Subtype.ext hh')
  chart_mem_atlas := fun v => ⟨-v, rfl⟩

theorem cellBoundaryHasGroupoid (k : ℕ)
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = (k - 1) + 1)] :
    @HasGroupoid (EuclideanSpace ℝ (Fin (k - 1))) _ (CellBoundary k) _
      (cellBoundaryChartedSpace k)
      (contDiffGroupoid (↑(⊤ : ℕ∞) : WithTop ℕ∞) (𝓡 (k - 1))) := by
  classical
  let := cellBoundaryChartedSpace k
  refine hasGroupoid_of_pregroupoid (contDiffPregroupoid (↑(⊤ : ℕ∞) : WithTop ℕ∞) (𝓡 (k - 1))) ?_
  intro e e' he he'
  rcases he with ⟨v₁, rfl⟩
  rcases he' with ⟨v₂, rfl⟩
  let h : CellBoundary k ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 :=
    cellBoundarySphereHomeomorph k
  let s₁ : OpenPartialHomeomorph (Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1)
      (EuclideanSpace ℝ (Fin (k - 1))) := stereographic' (k - 1) (h v₁)
  let s₂ : OpenPartialHomeomorph (Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1)
      (EuclideanSpace ℝ (Fin (k - 1))) := stereographic' (k - 1) (h v₂)
  have hmid : h.toOpenPartialHomeomorph.symm ≫ₕ h.toOpenPartialHomeomorph =
      (OpenPartialHomeomorph.refl (Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1) :
        OpenPartialHomeomorph (Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1)
          (Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1)) := by
    apply OpenPartialHomeomorph.ext
    · intro x
      change h.toPartialEquiv.toFun (h.toOpenPartialHomeomorph.symm x) = x
      exact h.right_inv x
    · intro x
      change h.toPartialEquiv.toFun (h.toOpenPartialHomeomorph.symm x) = x
      exact h.right_inv x
    · ext x
      simp
  have ht : (cellBoundaryChart k v₁).symm ≫ₕ (cellBoundaryChart k v₂) = s₁.symm ≫ₕ s₂ := by
    dsimp [cellBoundaryChart]
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
    change (s₁.symm ≫ₕ h.toOpenPartialHomeomorph.symm) ≫ₕ
        (h.toOpenPartialHomeomorph ≫ₕ s₂) = s₁.symm ≫ₕ s₂
    rw [OpenPartialHomeomorph.trans_assoc]
    rw [← OpenPartialHomeomorph.trans_assoc (e'' := s₂)]
    rw [hmid]
    simp
  rw [ht]
  have hmemOmega : s₁.symm ≫ₕ s₂ ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 (k - 1)) :=
    (inferInstance : HasGroupoid (Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1)
      (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 (k - 1)))).compatible ⟨h v₁, rfl⟩ ⟨h v₂, rfl⟩
  have hmemInfty : s₁.symm ≫ₕ s₂ ∈ contDiffGroupoid (↑(⊤ : ℕ∞) : WithTop ℕ∞) (𝓡 (k - 1)) :=
    contDiffGroupoid_le (by exact le_top : (⊤ : ℕ∞) ≤ (⊤ : WithTop ℕ∞)) hmemOmega
  have hm : s₁.symm ≫ₕ s₂ ∈ Pregroupoid.groupoid
      (contDiffPregroupoid (↑(⊤ : ℕ∞) : WithTop ℕ∞) (𝓡 (k - 1))) := by
    simpa [contDiffGroupoid] using hmemInfty
  exact (mem_groupoid_of_pregroupoid.mp hm).1

theorem cellBoundaryIsManifold (k : ℕ)
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = (k - 1) + 1)] :
    @IsManifold ℝ _ (EuclideanSpace ℝ (Fin (k - 1))) _ _ (EuclideanSpace ℝ (Fin (k - 1))) _
      (𝓡 (k - 1)) (⊤ : ℕ∞) (CellBoundary k) _ (cellBoundaryChartedSpace k) := by
  let := cellBoundaryChartedSpace k
  exact { toHasGroupoid := cellBoundaryHasGroupoid k }

theorem cellBoundaryInclusion_contMDiff (k : ℕ)
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = (k - 1) + 1)] :
    @ContMDiff ℝ _ (EuclideanSpace ℝ (Fin (k - 1))) _ _ (EuclideanSpace ℝ (Fin (k - 1))) _
      (𝓡 (k - 1)) (CellBoundary k) _ (cellBoundaryChartedSpace k)
      (EuclideanSpace ℝ (Fin k)) _ _ (EuclideanSpace ℝ (Fin k)) _
      (𝓘(ℝ, EuclideanSpace ℝ (Fin k))) (EuclideanSpace ℝ (Fin k)) _ _
      (⊤ : ℕ∞)
      (fun u : CellBoundary k => (u : EuclideanSpace ℝ (Fin k))) := by
  classical
  let : ChartedSpace (EuclideanSpace ℝ (Fin (k - 1))) (CellBoundary k) :=
    cellBoundaryChartedSpace k
  let : IsManifold (𝓡 (k - 1)) (⊤ : ℕ∞) (CellBoundary k) := cellBoundaryIsManifold k
  let : ChartedSpace (EuclideanSpace ℝ (Fin (k - 1)))
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1) :=
    EuclideanSpace.instChartedSpaceSphere (n := k - 1)
  let : IsManifold (𝓡 (k - 1)) (⊤ : WithTop ℕ∞)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1) :=
    EuclideanSpace.instIsManifoldSphere (n := k - 1)
  intro u
  let h : CellBoundary k ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 :=
    cellBoundarySphereHomeomorph k
  have hchart : chartAt (H := EuclideanSpace ℝ (Fin (k - 1))) (M := CellBoundary k) u =
      cellBoundaryChart k (-u) := rfl
  have hc : ContMDiffOn (𝓡 (k - 1)) (𝓡 (k - 1)) (⊤ : ℕ∞)
      (cellBoundaryChart k (-u)) (cellBoundaryChart k (-u)).source := by
    have h := contMDiffOn_chart (I := 𝓡 (k - 1))
      (H := EuclideanSpace ℝ (Fin (k - 1))) (M := CellBoundary k) (n := (⊤ : ℕ∞)) (x := u)
    simpa [hchart] using h
  let s₀ : OpenPartialHomeomorph (Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1)
      (EuclideanSpace ℝ (Fin (k - 1))) := stereographic' (k - 1) (h (-u))
  have hs : chartAt (H := EuclideanSpace ℝ (Fin (k - 1)))
      (M := Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1) (h u) = s₀ := by
    dsimp [s₀]
    change stereographic' (k - 1) (-(h u)) = stereographic' (k - 1) (h (-u))
    congr 1
  have hchartDef : cellBoundaryChart k (-u) = h.toOpenPartialHomeomorph ≫ₕ s₀ := by
    rfl
  have hsymm0 : ContMDiffOn (𝓡 (k - 1)) (𝓡 (k - 1)) (⊤ : ℕ∞)
      s₀.symm s₀.target := by
    have hω := contMDiffOn_chart_symm (I := 𝓡 (k - 1))
      (H := EuclideanSpace ℝ (Fin (k - 1)))
      (M := Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1) (n := (⊤ : WithTop ℕ∞)) (x := h u)
    simpa [hs] using hω.of_le (by exact le_top : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞))
  have hcoe : ContMDiffOn (𝓡 (k - 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin k))) (⊤ : ℕ∞)
      ((↑) : Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 → EuclideanSpace ℝ (Fin k)) Set.univ :=
    contMDiffOn_univ.mpr (contMDiff_coe_sphere (m := (⊤ : ℕ∞)) (n := k - 1))
  have hsymm : ContMDiffOn (𝓡 (k - 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin k))) (⊤ : ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin (k - 1)) =>
        ((s₀.symm y : Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1) :
          EuclideanSpace ℝ (Fin k)))
      s₀.target := by
    refine hcoe.comp hsymm0 ?_
    intro y hy
    trivial
  have htarget : (cellBoundaryChart k (-u)).target = s₀.target := by
    rw [hchartDef]
    simp
  have hval : ∀ y ∈ s₀.target,
      ((cellBoundaryChart k (-u)).symm y : EuclideanSpace ℝ (Fin k)) =
        ((s₀.symm y : Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1) :
          EuclideanSpace ℝ (Fin k)) := by
    intro y hy
    rw [hchartDef]
    change (((s₀.symm.trans h.toOpenPartialHomeomorph.symm) y : CellBoundary k) :
        EuclideanSpace ℝ (Fin k)) =
      ((s₀.symm y : Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1) :
        EuclideanSpace ℝ (Fin k))
    rw [OpenPartialHomeomorph.coe_trans]
    rfl
  have hg : ContMDiffOn (𝓡 (k - 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin k))) (⊤ : ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin (k - 1)) =>
        ((cellBoundaryChart k (-u)).symm y : EuclideanSpace ℝ (Fin k)))
      (cellBoundaryChart k (-u)).target := by
    rw [htarget]
    exact hsymm.congr hval
  have hst : (cellBoundaryChart k (-u)).source ⊆
      (cellBoundaryChart k (-u)) ⁻¹' (cellBoundaryChart k (-u)).target := by
    intro y hy
    exact (cellBoundaryChart k (-u)).mapsTo hy
  have hcomp : ContMDiffOn (𝓡 (k - 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin k))) (⊤ : ℕ∞)
      (fun x : CellBoundary k =>
        ((cellBoundaryChart k (-u)).symm ((cellBoundaryChart k (-u)) x) :
          EuclideanSpace ℝ (Fin k)))
      (cellBoundaryChart k (-u)).source :=
    hg.comp hc hst
  have hcong : ContMDiffOn (𝓡 (k - 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin k))) (⊤ : ℕ∞)
      (fun u : CellBoundary k => (u : EuclideanSpace ℝ (Fin k)))
      (cellBoundaryChart k (-u)).source := by
    refine hcomp.congr ?_
    intro y hy
    rw [(cellBoundaryChart k (-u)).left_inv hy]
  exact hcong.contMDiffAt ((cellBoundaryChart k (-u)).open_source.mem_nhds (by
    simpa [hchart] using (mem_chart_source (H := EuclideanSpace ℝ (Fin (k - 1)))
      (M := CellBoundary k) u)))

end

end DifferentialGeometry.Topology.Handle
