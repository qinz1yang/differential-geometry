import DifferentialGeometry.Topology.Manifold.TangentPartialDiffeomorph
import DifferentialGeometry.Geometry.Exponential.NormalBall.Chart

set_option autoImplicit false

noncomputable section

universe u uE uH

open Bundle Manifold Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace NormalCoordinates

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

namespace NormalBallChart

noncomputable def tangentHome {p : M}
    (c : NormalBallChart (I := I) p) :
    OpenPartialHomeomorph (E × E) (TangentBundle I M) :=
  (tangentBundleModelSpaceHomeomorph 𝓘(Real, E)).symm.toOpenPartialHomeomorph.trans
    (PartialDiffeomorph.tangentHome c.restrictBall (by simp))

noncomputable def pairHome {p : M}
    (c : NormalBallChart (I := I) p) :
    OpenPartialHomeomorph (E × E) (M × M) :=
  c.restrictBall.toOpenPartialHomeomorph.prod
    c.restrictBall.toOpenPartialHomeomorph

theorem tangentHome_apply {p : M}
    (c : NormalBallChart (I := I) p) (z : E × E)
    (hz : z.1 ∈ Metric.ball (0 : E) c.radius) :
    c.tangentHome z = c.tangent z := by
  change tangentMapWithin 𝓘(Real, E) I
      (c.restrictBall : E → M) c.restrictBall.source
      ((tangentBundleModelSpaceHomeomorph 𝓘(Real, E)).symm z) =
    c.tangent z
  have huniq : UniqueMDiffWithinAt 𝓘(Real, E)
      c.restrictBall.source z.1 :=
    c.restrictBall.open_source.uniqueMDiffOn z.1 (by
      simpa only [restrict_ball_source] using hz)
  have hdiff : MDifferentiableAt 𝓘(Real, E) I
      (c.restrictBall : E → M) z.1 :=
    c.restrictBall.mdifferentiableAt (by simp) (by
      simpa only [restrict_ball_source] using hz)
  rw [tangentMapWithin_eq_tangentMap huniq hdiff]
  rfl

omit [IsManifold I ∞ M] in
@[simp] theorem pairHome_apply {p : M}
    (c : NormalBallChart (I := I) p) (z : E × E) :
    c.pairHome z = c.pair z :=
  rfl

theorem tangentHome_source {p : M}
    (c : NormalBallChart (I := I) p) :
    c.tangentHome.source =
      Prod.fst ⁻¹' Metric.ball (0 : E) c.radius := by
  ext z
  simp only [tangentHome, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source,
    PartialDiffeomorph.tangentHome]
  constructor
  · rintro ⟨_, hz⟩
    exact hz
  · intro hz
    exact ⟨mem_univ z, hz⟩

theorem tangentHome_target {p : M}
    (c : NormalBallChart (I := I) p) :
    c.tangentHome.target =
      Bundle.TotalSpace.proj ⁻¹' c.restrictBall.target := by
  ext v
  simp only [tangentHome, OpenPartialHomeomorph.trans_target,
    Homeomorph.toOpenPartialHomeomorph_target,
    PartialDiffeomorph.tangentHome, Set.mem_inter_iff, Set.mem_preimage]
  simp

theorem tangentHome_symm_apply {p : M}
    (c : NormalBallChart (I := I) p) {y : M}
    (hy : y ∈ c.restrictBall.target) (v : TangentSpace I y) :
    c.tangentHome.symm
        (⟨y, v⟩ : TangentBundle I M) =
      (c.inv y,
        mfderiv I (modelWithCornersSelf Real E) c.inv y v) := by
  change
    tangentBundleModelSpaceHomeomorph (modelWithCornersSelf Real E)
        (tangentMapWithin I (modelWithCornersSelf Real E)
          (c.restrictBall.symm : M → E) c.restrictBall.target
          (⟨y, v⟩ : TangentBundle I M)) =
      (c.inv y,
        mfderiv I (modelWithCornersSelf Real E) c.inv y v)
  simp only [tangentMapWithin,
    tangentBundleModelSpaceHomeomorph_coe]
  rw [mfderivWithin_of_isOpen c.restrictBall.open_target hy]
  rfl

omit [IsManifold I ∞ M] in
@[simp] theorem pairHome_source {p : M}
    (c : NormalBallChart (I := I) p) :
    c.pairHome.source =
      Metric.ball (0 : E) c.radius ×ˢ Metric.ball (0 : E) c.radius :=
  rfl

theorem tangentHome_contMDiffOn {p : M}
    (c : NormalBallChart (I := I) p) :
    ContMDiffOn 𝓘(Real, E × E) I.tangent ∞
      c.tangentHome c.tangentHome.source := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  let Φ := c.restrictBall
  let m : OpenPartialHomeomorph (E × E) (TangentBundle 𝓘(Real, E) E) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(Real, E)).symm.toOpenPartialHomeomorph
  let t := PartialDiffeomorph.tangentHome Φ (by simp)
  have hm : ContMDiff (𝓘(Real, E).prod 𝓘(Real, E)) 𝓘(Real, E).tangent ∞
      (m : E × E → TangentBundle 𝓘(Real, E) E) := by
    have hm0 := contMDiff_tangentBundleModelSpaceHomeomorph_symm
      (I := 𝓘(Real, E)) (n := (∞ : WithTop ℕ∞))
    unfold ModelProd at hm0
    rw [← chartedSpaceSelf_prod] at hm0
    convert! hm0 using 1
  have ht : ContMDiffOn 𝓘(Real, E).tangent I.tangent ∞
      (t : TangentBundle 𝓘(Real, E) E → TangentBundle I M) t.source := by
    convert! Φ.contMDiffOn_toFun.contMDiffOn_tangentMapWithin
      (m := (∞ : WithTop ℕ∞)) (by simp) Φ.open_source.uniqueMDiffOn using 1
  have hmOn : ContMDiffOn (𝓘(Real, E).prod 𝓘(Real, E))
      𝓘(Real, E).tangent ∞
      (m : E × E → TangentBundle 𝓘(Real, E) E) m.source :=
    hm.contMDiffOn
  change ContMDiffOn (𝓘(Real, E).prod 𝓘(Real, E)) I.tangent ∞
    ((t : TangentBundle 𝓘(Real, E) E → TangentBundle I M) ∘
      (m : E × E → TangentBundle 𝓘(Real, E) E))
    (m.source ∩
      (m : E × E → TangentBundle 𝓘(Real, E) E) ⁻¹' t.source)
  exact ht.comp' hmOn

theorem tangentHome_symm_contMDiffOn {p : M}
    (c : NormalBallChart (I := I) p) :
    ContMDiffOn I.tangent 𝓘(Real, E × E) ∞
      c.tangentHome.symm c.tangentHome.target := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  let Φ := c.restrictBall
  let m : OpenPartialHomeomorph (E × E) (TangentBundle 𝓘(Real, E) E) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(Real, E)).symm.toOpenPartialHomeomorph
  let t := PartialDiffeomorph.tangentHome Φ (by simp)
  have hm : ContMDiff 𝓘(Real, E).tangent
      (𝓘(Real, E).prod 𝓘(Real, E)) ∞
      (m.symm : TangentBundle 𝓘(Real, E) E → E × E) := by
    have hm0 := contMDiff_tangentBundleModelSpaceHomeomorph
      (I := 𝓘(Real, E)) (n := (∞ : WithTop ℕ∞))
    unfold ModelProd at hm0
    rw [← chartedSpaceSelf_prod] at hm0
    convert! hm0 using 1
  have ht : ContMDiffOn I.tangent 𝓘(Real, E).tangent ∞
      (t.symm : TangentBundle I M → TangentBundle 𝓘(Real, E) E) t.target := by
    convert! Φ.contMDiffOn_invFun.contMDiffOn_tangentMapWithin
      (m := (∞ : WithTop ℕ∞)) (by simp) Φ.open_target.uniqueMDiffOn using 1
  have hmOn : ContMDiffOn 𝓘(Real, E).tangent
      (𝓘(Real, E).prod 𝓘(Real, E)) ∞
      (m.symm : TangentBundle 𝓘(Real, E) E → E × E) m.target :=
    hm.contMDiffOn
  change ContMDiffOn I.tangent (𝓘(Real, E).prod 𝓘(Real, E)) ∞
    ((m.symm : TangentBundle 𝓘(Real, E) E → E × E) ∘
      (t.symm : TangentBundle I M → TangentBundle 𝓘(Real, E) E))
    (t.target ∩
      (t.symm : TangentBundle I M → TangentBundle 𝓘(Real, E) E) ⁻¹' m.target)
  exact hmOn.comp' ht

omit [IsManifold I ∞ M] in
theorem pairHome_contMDiffOn {p : M}
    (c : NormalBallChart (I := I) p) :
    ContMDiffOn 𝓘(Real, E × E) (I.prod I) ∞
      c.pairHome c.pairHome.source := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  have h := c.restrictBall.contMDiffOn_toFun.prodMap
    c.restrictBall.contMDiffOn_toFun
  convert! h using 1

omit [IsManifold I ∞ M] in
theorem pairHome_symm_contMDiffOn {p : M}
    (c : NormalBallChart (I := I) p) :
    ContMDiffOn (I.prod I) 𝓘(Real, E × E) ∞
      c.pairHome.symm c.pairHome.target := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  have h := c.restrictBall.contMDiffOn_invFun.prodMap
    c.restrictBall.contMDiffOn_invFun
  convert! h using 1

end NormalBallChart
end NormalCoordinates
end Riemannian
end Geometry
end DifferentialGeometry
