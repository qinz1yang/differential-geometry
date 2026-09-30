import DifferentialGeometry.Topology.ThreeManifold.Surgery.TubeSystem.Defs

noncomputable section

open Metric Set Bundle Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

abbrev FourSpace := EuclideanSpace ℝ (Fin 4)

def snocR {n : ℕ} (f : Fin n → ℝ) (a : ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc (α := fun _ => ℝ) f a

@[simp] theorem snocR_castSucc {n : ℕ} (f : Fin n → ℝ) (a : ℝ) (i : Fin n) :
    snocR f a i.castSucc = f i := Fin.snoc_castSucc (α := fun _ => ℝ) a f i

@[simp] theorem snocR_last {n : ℕ} (f : Fin n → ℝ) (a : ℝ) :
    snocR f a (Fin.last n) = a := Fin.snoc_last (α := fun _ => ℝ) a f

def neckPoint (x : Sphere 2) (t : ℝ) : FourSpace :=
  WithLp.toLp 2 (snocR (fun i : Fin 3 => Real.sqrt (1 - (t / 4) ^ 2) * x.1 i) (t / 4))

theorem neckPoint_mem_sphere (x : Sphere 2) (t : Icc (-2 : ℝ) 2) :
    neckPoint x t.1 ∈ Sphere 3 := by
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
  have habs : |t.1| ≤ 2 := abs_le.mpr ⟨t.2.1, t.2.2⟩
  have h4 : t.1 ^ 2 ≤ 4 := by rw [← sq_abs]; nlinarith [habs, abs_nonneg t.1]
  have ht : (t.1 / 4) ^ 2 ≤ 1 := by nlinarith [h4]
  have hsqrt : Real.sqrt (1 - (t.1 / 4) ^ 2) ^ 2 = 1 - (t.1 / 4) ^ 2 :=
    Real.sq_sqrt (by linarith)
  have hx : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    have h := x.2
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
    exact h
  have h2 : ‖neckPoint x t.1‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [neckPoint, WithLp.ofLp_toLp]
    rw [Fin.sum_univ_castSucc]
    have h1 : (∑ i : Fin 3, ‖snocR (fun i : Fin 3 => Real.sqrt (1 - (t.1 / 4) ^ 2) * x.1 i)
        (t.1 / 4) i.castSucc‖ ^ 2)
        = (Real.sqrt (1 - (t.1 / 4) ^ 2)) ^ 2 * ∑ i : Fin 3, ‖x.1 i‖ ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [snocR_castSucc, norm_mul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [h1, snocR_last, Real.norm_eq_abs, sq_abs,
      ← EuclideanSpace.norm_sq_eq (x : EuclideanSpace ℝ (Fin 3)), hx, hsqrt]
    ring
  nlinarith [norm_nonneg (neckPoint x t.1), h2]

def standardNeckTubeFun (z : TubeDomain) : Sphere 3 :=
  ⟨neckPoint z.1 z.2.1, neckPoint_mem_sphere z.1 z.2⟩

theorem continuous_snocR_family :
    Continuous fun z : TubeDomain =>
      (fun i : Fin 3 => Real.sqrt (1 - (z.2.1 / 4) ^ 2) * z.1.1 i) := by
  apply continuous_pi
  intro i
  have hc : Continuous fun z : TubeDomain => Real.sqrt (1 - (z.2.1 / 4) ^ 2) := by fun_prop
  have hx : Continuous fun z : TubeDomain => ((z.1 : Sphere 2) : EuclideanSpace ℝ (Fin 3)) i := by
    fun_prop
  exact hc.mul hx

theorem continuous_standardNeckTubeFun : Continuous standardNeckTubeFun := by
  apply Continuous.subtype_mk
  have hg : Continuous fun z : TubeDomain => z.2.1 / 4 :=
    (continuous_subtype_val.comp continuous_snd).div_const 4
  have hbase : Continuous fun z : TubeDomain =>
      snocR (fun i : Fin 3 => Real.sqrt (1 - (z.2.1 / 4) ^ 2) * z.1.1 i) (z.2.1 / 4) :=
    Continuous.finSnoc continuous_snocR_family hg
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 4 => ℝ)).comp hbase

theorem standardNeckTubeFun_injective : Function.Injective standardNeckTubeFun := by
  intro z w hzw
  have hlast : z.2.1 / 4 = w.2.1 / 4 := by
    have h := congrArg (fun p : Sphere 3 => (p.1 : FourSpace).ofLp (Fin.last 3)) hzw
    simpa only [standardNeckTubeFun, neckPoint, WithLp.ofLp_toLp, snocR_last] using h
  have ht : z.2.1 = w.2.1 := by linarith
  have hpos : 0 < Real.sqrt (1 - (z.2.1 / 4) ^ 2) := by
    have habs : |z.2.1| ≤ 2 := abs_le.mpr ⟨z.2.2.1, z.2.2.2⟩
    have h4 : z.2.1 ^ 2 ≤ 4 := by rw [← sq_abs]; nlinarith [habs, abs_nonneg z.2.1]
    apply Real.sqrt_pos.mpr
    nlinarith [h4]
  have hx : z.1 = w.1 := by
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    funext i
    have h := congrArg (fun p : Sphere 3 => (p.1 : FourSpace).ofLp i.castSucc) hzw
    simp only [standardNeckTubeFun, neckPoint, WithLp.ofLp_toLp, snocR_castSucc] at h
    rw [← ht] at h
    exact mul_left_cancel₀ (ne_of_gt hpos) h
  exact Prod.ext hx (Subtype.ext ht)

theorem isEmbedding_standardNeckTubeFun : Topology.IsEmbedding standardNeckTubeFun :=
  (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap continuous_standardNeckTubeFun
    standardNeckTubeFun_injective
    fun _s hs => (hs.isCompact.image continuous_standardNeckTubeFun).isClosed).toIsEmbedding

def standardNeckTube : C(TubeDomain, Sphere 3) :=
  ⟨standardNeckTubeFun, continuous_standardNeckTubeFun⟩

def standardNeckTubeSystem : TubeSystem (Sphere 3) where
  Index := PUnit
  finiteIndex := inferInstance
  tube := fun _ => standardNeckTube
  embedding := fun _ => isEmbedding_standardNeckTubeFun
  disjoint := fun a b hab => (hab (Subsingleton.elim a b)).elim

theorem standardNeckTubeSystem_index_nonempty :
    Nonempty standardNeckTubeSystem.Index := ⟨PUnit.unit⟩

theorem standardNeckTubeSystem_boundary_nonempty :
    Nonempty standardNeckTubeSystem.Boundary := ⟨(PUnit.unit, false)⟩


theorem standardNeckTubeSystem_removedBand_nonempty :
    (standardNeckTubeSystem.removedBand PUnit.unit).Nonempty := by
  let x₀ : Sphere 2 := ⟨EuclideanSpace.single 0 1, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, PiLp.norm_single]
    norm_num⟩
  let z₀ : TubeDomain := (x₀, ⟨0, by norm_num, by norm_num⟩)
  exact ⟨standardNeckTube z₀, z₀, ⟨by norm_num, by norm_num⟩, rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private def sphereTwoPoint : Sphere 2 :=
  ⟨EuclideanSpace.single 0 1, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, PiLp.norm_single]
    norm_num⟩

theorem standardNeckTubeSystem_nontrivial :
    Nonempty standardNeckTubeSystem.Index ∨ Nonempty (Sphere 3) :=
  Or.inl standardNeckTubeSystem_index_nonempty

theorem standardNeckTubeSystem_boundarySpheres_disjoint :
    Disjoint (Set.range (standardNeckTubeSystem.boundarySphere (PUnit.unit, false)))
      (Set.range (standardNeckTubeSystem.boundarySphere (PUnit.unit, true))) := by
  rw [Set.disjoint_left]
  rintro p ⟨x, rfl⟩ ⟨y, hy⟩
  have h' : standardNeckTubeFun (x, TubeSystem.boundaryLevel false) =
      standardNeckTubeFun (y, TubeSystem.boundaryLevel true) := hy.symm
  have h2 : (TubeSystem.boundaryLevel false : ℝ) = (TubeSystem.boundaryLevel true : ℝ) :=
    congrArg (fun z : TubeDomain => (z.2 : ℝ)) (standardNeckTubeFun_injective h')
  exact absurd h2 (by norm_num [TubeSystem.boundaryLevel])

theorem standardNeckTubeSystem_boundarySphere_ne :
    standardNeckTubeSystem.boundarySphere (PUnit.unit, false) ≠
      standardNeckTubeSystem.boundarySphere (PUnit.unit, true) := by
  intro h
  have hmem : standardNeckTubeSystem.boundarySphere (PUnit.unit, false) sphereTwoPoint ∈
      Set.range (standardNeckTubeSystem.boundarySphere (PUnit.unit, true)) := by
    rw [← h]
    exact Set.mem_range_self _
  exact Set.disjoint_left.mp standardNeckTubeSystem_boundarySpheres_disjoint
    (Set.mem_range_self _) hmem

theorem standardNeckTubeSystem_core_nonempty : (standardNeckTubeSystem.core).Nonempty :=
  ⟨standardNeckTubeSystem.boundarySphere (PUnit.unit, false) sphereTwoPoint,
    TubeSystem.boundarySphere_mem_core (T := standardNeckTubeSystem) _ _⟩

theorem standardNeckTubeSystem_removedBand_ne_univ :
    standardNeckTubeSystem.removedBand PUnit.unit ≠ Set.univ := by
  intro h
  obtain ⟨x, hx⟩ := standardNeckTubeSystem_core_nonempty
  rw [TubeSystem.core, Set.mem_compl_iff] at hx
  exact hx (Set.mem_iUnion.mpr ⟨PUnit.unit, by rw [h]; exact Set.mem_univ x⟩)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
