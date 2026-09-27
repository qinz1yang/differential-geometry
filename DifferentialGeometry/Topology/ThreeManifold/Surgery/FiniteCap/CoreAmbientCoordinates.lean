import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CoreInteriorCoordinates

set_option autoImplicit false
noncomputable section
open Set Function Manifold IsManifold
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev NormalE2 := EuclideanSpace ℝ (Fin 2)
private abbrev NormalC := NormalE2 × ℝ
private abbrev NormalIC := (𝓡 2).prod 𝓘(ℝ)
private abbrev NormalH := ModelProd NormalE2 ℝ
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable (hdim : Module.finrank ℝ E = 3)

def coreAmbientLinearEquiv : E ≃L[ℝ] NormalC :=
  (LinearEquiv.ofFinrankEq (R := ℝ) E NormalC (by simpa using hdim)).toContinuousLinearEquiv

def coreBoundaryAmbientLinearEquiv : (NormalE2 × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] E :=
  ((ContinuousLinearEquiv.refl ℝ NormalE2).prodCongr
    (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ))).trans (coreAmbientLinearEquiv hdim).symm

def coreAmbientCoordinateDiffeomorph : H ≃ₘ⟮I, 𝓘(ℝ, NormalC)⟯ NormalC where
  toEquiv := (I.toHomeomorph.trans (coreAmbientLinearEquiv hdim).toHomeomorph).toEquiv
  contMDiff_toFun := (coreAmbientLinearEquiv hdim).contDiff.contMDiff.comp I.contMDiff
  contMDiff_invFun := by
    have hI : ContMDiff 𝓘(ℝ, E) I ∞ I.symm := by
      rw [← contMDiffOn_univ, ← I.range_eq_univ]
      exact I.contMDiffOn_symm
    exact hI.comp (coreAmbientLinearEquiv hdim).symm.contDiff.contMDiff

def coreAmbientNormalizingHomeomorph (a σ : ℝ) (hσ : σ ^ 2 = 1) : NormalH ≃ₜ H :=
  (NormalIC.toHomeomorph.trans
    (cylinderAxialDiffeomorph (I := 𝓡 2) (M := NormalE2) a σ hσ).toHomeomorph).trans
      (coreAmbientCoordinateDiffeomorph I hdim).symm.toHomeomorph

theorem coreAmbientNormalizingHomeomorph_contMDiff (a σ : ℝ) (hσ : σ ^ 2 = 1) :
    ContMDiff NormalIC I ∞ (coreAmbientNormalizingHomeomorph I hdim a σ hσ) := by
  have hA : ContDiff ℝ ∞ (fun z : NormalC => (z.1, a + σ * z.2)) := by fun_prop
  exact (coreAmbientCoordinateDiffeomorph I hdim).symm.contMDiff.comp
    (hA.contMDiff.comp NormalIC.contMDiff)

theorem coreAmbientNormalizingHomeomorph_symm_contMDiff (a σ : ℝ) (hσ : σ ^ 2 = 1) :
    ContMDiff I NormalIC ∞ (coreAmbientNormalizingHomeomorph I hdim a σ hσ).symm := by
  have hA : ContDiff ℝ ∞ (fun z : NormalC => (z.1, σ * (z.2 - a))) := by fun_prop
  have hIC : ContMDiff 𝓘(ℝ, NormalC) NormalIC ∞ NormalIC.symm := by
    rw [← contMDiffOn_univ, ← NormalIC.range_eq_univ]
    exact NormalIC.contMDiffOn_symm
  exact hIC.comp (hA.contMDiff.comp (coreAmbientCoordinateDiffeomorph I hdim).contMDiff)

theorem coreAmbientNormalizingHomeomorph_extend (a σ : ℝ) (hσ : σ ^ 2 = 1) (z : NormalH) :
    I (coreAmbientNormalizingHomeomorph I hdim a σ hσ z) =
      (coreAmbientLinearEquiv hdim).symm (z.1, a + σ * z.2) := by
  exact I.right_inv (by rw [I.range_eq_univ]; trivial)
end DifferentialGeometry.Topology.ThreeManifold.Surgery
