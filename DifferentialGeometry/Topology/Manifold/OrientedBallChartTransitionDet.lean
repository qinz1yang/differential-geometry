import DifferentialGeometry.Topology.Manifold.BallChartStraightening
import DifferentialGeometry.Topology.Manifold.OrientedBallChartStraightening
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Metric Filter Topology
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology (BallChart)
open DifferentialGeometry.Topology.Manifold
  (exists_isotopy_eqOn_closedBall_of_partialDiffeomorphs_of_subset)

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private def modelBasisOrientation (x : ThreeSpace) :
    Orientation ℝ (TangentSpace ThreeModel x) (Fin 3) :=
  ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.map
    (NormedSpace.fromTangentSpace x).symm.toLinearEquiv).orientation

private theorem modelBasisOrientation_eq (x y : ThreeSpace) :
    modelBasisOrientation x = modelBasisOrientation y := by
  have hx : modelBasisOrientation x =
      ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis).orientation := by
    rw [modelBasisOrientation]
    congr 1
  have hy : modelBasisOrientation y =
      ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis).orientation := by
    rw [modelBasisOrientation]
    congr 1
  rw [hx, hy]

theorem OrientedBallEmbedding.transition_fderiv_det_pos {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    {o : ManifoldOrientation ThreeModel U 3} (b b' : OrientedBallEmbedding U o)
    (h0t : b.chart 0 ∈ b'.chart.target) :
    0 < (fderiv ℝ (fun x : ThreeSpace => b'.chart.symm (b.chart x)) 0).det := by
  classical
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ ThreeSpace := by simp
  have h0s : (0 : ThreeSpace) ∈ b.chart.source :=
    b.closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))
  have hx0s : b'.chart.symm (b.chart 0) ∈ b'.chart.source :=
    PartialEquiv.map_target b'.chart.toPartialEquiv h0t
  have hpx : b'.chart (b'.chart.symm (b.chart 0)) = b.chart 0 :=
    PartialDiffeomorph.apply_symm_apply b'.chart h0t
  have hmdd₁ := PartialDiffeomorph.mdifferentiableAt b'.chart.symm (n := ∞) (by simp) h0t
  have hmdd₁' : MDifferentiableAt ThreeModel ThreeModel (b'.chart.symm : U → ThreeSpace)
      (b'.chart (b'.chart.symm (b.chart 0))) := by
    rw [hpx]
    exact hmdd₁
  have hmdd₂ := PartialDiffeomorph.mdifferentiableAt b'.chart (n := ∞) (by simp) hx0s
  have hmdd₀ := PartialDiffeomorph.mdifferentiableAt b.chart (n := ∞) (by simp) h0s
  let Aclm : TangentSpace ThreeModel (0 : ThreeSpace) →L[ℝ]
      TangentSpace ThreeModel (b.chart 0) :=
    mfderiv ThreeModel ThreeModel (b.chart : ThreeSpace → U) (0 : ThreeSpace)
  let Bclm : TangentSpace ThreeModel (b'.chart.symm (b.chart 0)) →L[ℝ]
      TangentSpace ThreeModel (b.chart 0) :=
    mfderiv ThreeModel ThreeModel (b'.chart : ThreeSpace → U) (b'.chart.symm (b.chart 0))
  let Cclm : TangentSpace ThreeModel (b.chart 0) →L[ℝ]
      TangentSpace ThreeModel (b'.chart.symm (b.chart 0)) :=
    mfderiv ThreeModel ThreeModel (b'.chart.symm : U → ThreeSpace) (b.chart 0)
  let Aeq : TangentSpace ThreeModel (0 : ThreeSpace) ≃ₗ[ℝ]
      TangentSpace ThreeModel (b.chart 0) :=
    (IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv
      (PartialDiffeomorph.isLocalDiffeomorphAt ThreeModel ThreeModel ∞ b.chart h0s)
      (by simp)).toLinearEquiv
  let Beq : TangentSpace ThreeModel (b'.chart.symm (b.chart 0)) ≃ₗ[ℝ]
      TangentSpace ThreeModel (b.chart 0) :=
    (IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv
      (PartialDiffeomorph.isLocalDiffeomorphAt ThreeModel ThreeModel ∞ b'.chart hx0s)
      (by simp)).toLinearEquiv
  let Ceq : TangentSpace ThreeModel (b.chart 0) ≃ₗ[ℝ]
      TangentSpace ThreeModel (b'.chart.symm (b.chart 0)) :=
    (IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv
      (PartialDiffeomorph.isLocalDiffeomorphAt ThreeModel ThreeModel ∞ b'.chart.symm h0t)
      (by simp)).toLinearEquiv
  have hA : Orientation.map (Fin 3) Aeq (modelBasisOrientation 0) = o.orientation (b.chart 0) :=
    b.preserves_orientation 0 h0s
  have hB : Orientation.map (Fin 3) Beq (modelBasisOrientation (b'.chart.symm (b.chart 0)))
      = o.orientation (b.chart 0) := by
    have h := b'.preserves_orientation (b'.chart.symm (b.chart 0)) hx0s
    rwa [hpx] at h
  have hAeq_f : ∀ v : TangentSpace ThreeModel (0 : ThreeSpace), Aeq v = Aclm v := fun _ => rfl
  have hBeq_f : ∀ v : TangentSpace ThreeModel (b'.chart.symm (b.chart 0)), Beq v = Bclm v :=
    fun _ => rfl
  have hCeq_f : ∀ v : TangentSpace ThreeModel (b.chart 0), Ceq v = Cclm v := fun _ => rfl
  have hCBval : ∀ w : TangentSpace ThreeModel (b'.chart.symm (b.chart 0)), Cclm (Bclm w) = w := by
    intro w
    have hcomp := mfderiv_comp (x := b'.chart.symm (b.chart 0))
      (f := (b'.chart : ThreeSpace → U)) (g := (b'.chart.symm : U → ThreeSpace))
      hmdd₁' hmdd₂
    rw [hpx] at hcomp
    have hev : ((b'.chart.symm : U → ThreeSpace) ∘ (b'.chart : ThreeSpace → U))
        =ᶠ[𝓝 (b'.chart.symm (b.chart 0))] id := by
      filter_upwards [b'.chart.open_source.mem_nhds hx0s] with y hy
      exact PartialDiffeomorph.symm_apply_apply b'.chart hy
    rw [hev.mfderiv_eq, mfderiv_id] at hcomp
    have h2 := DFunLike.congr_fun hcomp.symm w
    simp only [Function.comp_apply] at h2
    rw [hpx] at h2
    change Cclm (Bclm w) = w at h2
    exact h2
  have hAc : Cclm.comp Aclm = mfderiv ThreeModel ThreeModel
      (fun y : ThreeSpace => b'.chart.symm (b.chart y)) (0 : ThreeSpace) := by
    have hcomp := mfderiv_comp (x := (0 : ThreeSpace)) (f := (b.chart : ThreeSpace → U))
      (g := (b'.chart.symm : U → ThreeSpace)) hmdd₁ hmdd₀
    exact hcomp.symm
  have hCB : Beq.trans Ceq = LinearEquiv.refl ℝ
      (TangentSpace ThreeModel (b'.chart.symm (b.chart 0))) := by
    ext v
    change Ceq (Beq v) = v
    rw [hCeq_f, hBeq_f]
    exact hCBval v
  have hCsymm : Ceq = Beq.symm := by
    have h1 : Beq.symm.trans (Beq.trans Ceq) = Beq.symm.trans
        (LinearEquiv.refl ℝ (TangentSpace ThreeModel (b'.chart.symm (b.chart 0)))) := by
      rw [hCB]
    rw [← LinearEquiv.trans_assoc, LinearEquiv.symm_trans_self, LinearEquiv.refl_trans,
      LinearEquiv.trans_refl] at h1
    exact h1
  have hC : Orientation.map (Fin 3) Ceq (o.orientation (b.chart 0))
      = modelBasisOrientation (b'.chart.symm (b.chart 0)) := by
    have h2 : Orientation.map (Fin 3) Beq.symm
        (Orientation.map (Fin 3) Beq (modelBasisOrientation (b'.chart.symm (b.chart 0))))
        = Orientation.map (Fin 3) Beq.symm (o.orientation (b.chart 0)) := congrArg _ hB
    rw [← Orientation.map_symm, Equiv.symm_apply_apply] at h2
    have hsymm : (Orientation.map (Fin 3) Beq).symm = Orientation.map (Fin 3) Ceq := by
      rw [Orientation.map_symm, ← hCsymm]
    rw [hsymm] at h2
    exact h2.symm
  have hmap : Orientation.map (Fin 3) (Aeq.trans Ceq) (modelBasisOrientation 0)
      = modelBasisOrientation 0 := by
    rw [← DifferentialGeometry.VectorBundle.map_orientation_trans_between Aeq Ceq
      (modelBasisOrientation 0), hA, hC, modelBasisOrientation_eq]
  have hdet : 0 < LinearMap.det ((Aeq.trans Ceq :
      TangentSpace ThreeModel (0 : ThreeSpace) →ₗ[ℝ]
        TangentSpace ThreeModel (b'.chart.symm (b.chart 0)))) :=
    (Orientation.map_eq_iff_det_pos (modelBasisOrientation 0) (Aeq.trans Ceq) hcard).mp hmap
  have htof : ((Aeq.trans Ceq : TangentSpace ThreeModel (0 : ThreeSpace) ≃ₗ[ℝ]
        TangentSpace ThreeModel (b'.chart.symm (b.chart 0))) :
        TangentSpace ThreeModel (0 : ThreeSpace) →ₗ[ℝ]
          TangentSpace ThreeModel (b'.chart.symm (b.chart 0)))
      = (fderiv ℝ (fun x : ThreeSpace => b'.chart.symm (b.chart x)) 0 :
          ThreeSpace →ₗ[ℝ] ThreeSpace) := by
    ext v
    change Ceq (Aeq v) = (fderiv ℝ (fun x : ThreeSpace => b'.chart.symm (b.chart x)) 0) v
    rw [hCeq_f, hAeq_f]
    change (Cclm.comp Aclm) v = (fderiv ℝ (fun x : ThreeSpace => b'.chart.symm (b.chart x)) 0) v
    rw [hAc, mfderiv_eq_fderiv]
    rfl
  rw [htof] at hdet
  exact hdet

theorem OrientedBallEmbedding.transition_fderiv_det_pos_self {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    {o : ManifoldOrientation ThreeModel U 3} (b : OrientedBallEmbedding U o) :
    0 < (fderiv ℝ (fun x : ThreeSpace => b.chart.symm (b.chart x)) 0).det :=
  b.transition_fderiv_det_pos b (by
    have h0 : (0 : ThreeSpace) ∈ b.chart.source :=
      b.closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))
    simpa using PartialEquiv.map_source b.chart.toPartialEquiv h0)


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
