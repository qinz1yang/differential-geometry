import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.Descent
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph

noncomputable section
set_option autoImplicit false

open Bundle Manifold Set Metric Module
open DifferentialGeometry.Manifold
open scoped Manifold Topology ContDiff RealInnerProductSpace

namespace DifferentialGeometry.Geometry

universe uE uQ

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)] [NeZero n]

private noncomputable def opensTangentEquiv
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace (EuclideanSpace ℝ (Fin n)) Q]
    (U : TopologicalSpace.Opens Q) (x : U) :
    TangentSpace (𝓡 n) (x : Q) ≃L[ℝ] TangentSpace (𝓡 n) x :=
  (tangentSpaceModelContinuousLinearEquiv (I := 𝓡 n) (x : Q)).trans
    (tangentSpaceModelContinuousLinearEquiv (I := 𝓡 n) x).symm

omit [NeZero n] in
private theorem mfderiv_subtype_val_opensTangentEquiv
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace (EuclideanSpace ℝ (Fin n)) Q]
    (U : TopologicalSpace.Opens Q) (x : U) (v : TangentSpace (𝓡 n) (x : Q)) :
    mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → Q) x (opensTangentEquiv U x v) = v := by
  rw [mfderiv_subtype_val_apply]
  apply (tangentSpaceModelContinuousLinearEquiv (I := 𝓡 n) (x : Q)).injective
  change tangentSpaceModelContinuousLinearEquiv (I := 𝓡 n) (x : Q)
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓡 n) x).symm
        (tangentSpaceModelContinuousLinearEquiv (I := 𝓡 n) (x : Q) v)) =
    tangentSpaceModelContinuousLinearEquiv (I := 𝓡 n) (x : Q) v
  rw [tangentSpaceModelContinuousLinearEquiv_symm_apply]
  exact tangentSpaceModelContinuousLinearEquiv_apply (I := 𝓡 n) (x : Q) v

omit [NeZero n] in
private theorem sphereDiffeo_symm_apply (e : E ≃ₗᵢ[ℝ] E) (x : sphere (0 : E) 1) :
    sphereDiffeo (n := n) e.symm (sphereDiffeo (n := n) e x) = x := by
  apply Subtype.ext
  rw [sphereDiffeo_coe, sphereDiffeo_coe]
  exact e.symm_apply_apply x

omit [NeZero n] in
private theorem sphereDiffeo_apply_symm (e : E ≃ₗᵢ[ℝ] E) (x : sphere (0 : E) 1) :
    sphereDiffeo (n := n) e (sphereDiffeo (n := n) e.symm x) = x := by
  apply Subtype.ext
  rw [sphereDiffeo_coe, sphereDiffeo_coe]
  exact e.apply_symm_apply x

omit [FiniteDimensional ℝ E] [NeZero n] in
private theorem roundInner_congr {p q : sphere (0 : E) 1} (h : p = q)
    (v w : TangentSpace (𝓡 n) p) :
    roundInner (n := n) q v w = roundInner (n := n) p v w := by
  cases h
  rfl

namespace RoundSphereQuotient

theorem gQuot_inner_proj (D : RoundSphereQuotient E n) (y : sphere (0 : E) 1)
    (V W : TangentSpace (𝓡 n) y) :
    D.gQuot.inner (D.proj y) (mfderiv (𝓡 n) (𝓡 n) D.proj y V)
        (mfderiv (𝓡 n) (𝓡 n) D.proj y W)
      = (roundMetric (E := E) (n := n)).inner y V W := by
  have h0 : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  let S := D.sectionAt (D.proj y)
  let xW : S.baseNeighborhood := ⟨D.proj y, S.mem_baseNeighborhood⟩
  obtain ⟨γ, hγ⟩ := D.proj_eq_imp y (S.toSphere xW) (S.toSphere_proj xW).symm
  have hmain :
      D.gQuot.inner (D.proj y) (mfderiv (𝓡 n) (𝓡 n) D.proj y V)
          (mfderiv (𝓡 n) (𝓡 n) D.proj y W) =
        roundInner (n := n) (S.toSphere xW)
          (mfderiv (𝓡 n) (𝓡 n) S.toSphere xW
            (opensTangentEquiv S.baseNeighborhood xW (mfderiv (𝓡 n) (𝓡 n) D.proj y V)))
          (mfderiv (𝓡 n) (𝓡 n) S.toSphere xW
            (opensTangentEquiv S.baseNeighborhood xW (mfderiv (𝓡 n) (𝓡 n) D.proj y W))) := by
    have hgm : D.gm (D.proj y) (mfderiv (𝓡 n) (𝓡 n) D.proj y V)
          (mfderiv (𝓡 n) (𝓡 n) D.proj y W)
        = (Diffeomorph.pullbackMetric
            ((roundMetric (E := E) (n := n)).restrictOpen S.sphereNeighborhood)
            S.localSection).inner xW
              (opensTangentEquiv S.baseNeighborhood xW (mfderiv (𝓡 n) (𝓡 n) D.proj y V))
              (opensTangentEquiv S.baseNeighborhood xW (mfderiv (𝓡 n) (𝓡 n) D.proj y W)) := by
      rw [D.gm_apply]
      rfl
    rw [D.gQuot_inner, hgm]
    exact S.pullback_inner_eval S.mem_baseNeighborhood _ _
  rw [hmain]
  have hA'inj : Function.Injective (mfderiv (𝓡 n) (𝓡 n) D.proj (S.toSphere xW)) :=
    S.dproj_inj D.proj_smooth xW
  have hproj_y' : MDifferentiableAt (𝓡 n) (𝓡 n) D.proj (S.toSphere xW) :=
    D.proj_smooth.mdifferentiableAt h0
  have htoSphere : MDifferentiableAt (𝓡 n) (𝓡 n) S.toSphere xW :=
    S.toSphere_contMDiff.mdifferentiableAt h0
  have hsec_app : ∀ u : TangentSpace (𝓡 n) xW,
      mfderiv (𝓡 n) (𝓡 n) D.proj (S.toSphere xW)
          (mfderiv (𝓡 n) (𝓡 n) S.toSphere xW u)
        = mfderiv (𝓡 n) (𝓡 n) (Subtype.val : S.baseNeighborhood → D.Q) xW u := by
    intro u
    have h := mfderiv_comp_apply xW hproj_y' htoSphere u
    have hfun : D.proj ∘ S.toSphere =
        (Subtype.val : S.baseNeighborhood → D.Q) := funext (fun r => S.toSphere_proj r)
    rw [hfun] at h
    exact h.symm
  have hA_app : ∀ w : TangentSpace (𝓡 n) y,
      mfderiv (𝓡 n) (𝓡 n) D.proj (S.toSphere xW)
          (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) (D.ρ γ)) y w)
        = mfderiv (𝓡 n) (𝓡 n) D.proj y w := by
    intro w
    have h := mfderiv_comp_apply y
      (show MDifferentiableAt (𝓡 n) (𝓡 n) D.proj
          (sphereDiffeo (n := n) (D.ρ γ) y) from by
        rw [hγ]
        exact hproj_y')
      ((sphereDiffeo (n := n) (D.ρ γ)).contMDiff.mdifferentiableAt h0) w
    have hfun : D.proj ∘ (sphereDiffeo (n := n) (D.ρ γ) : sphere (0 : E) 1 → sphere (0 : E) 1)
        = D.proj := funext (fun z => D.proj_smul γ z)
    rw [hfun, hγ] at h
    exact h.symm
  have hB : ∀ a : TangentSpace (𝓡 n) y,
      mfderiv (𝓡 n) (𝓡 n) S.toSphere xW
          (opensTangentEquiv S.baseNeighborhood xW (mfderiv (𝓡 n) (𝓡 n) D.proj y a))
        = mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) (D.ρ γ)) y a := by
    intro a
    have h1 : mfderiv (𝓡 n) (𝓡 n) D.proj (S.toSphere xW)
        (mfderiv (𝓡 n) (𝓡 n) S.toSphere xW
          (opensTangentEquiv S.baseNeighborhood xW (mfderiv (𝓡 n) (𝓡 n) D.proj y a)))
        = mfderiv (𝓡 n) (𝓡 n) D.proj y a := by
      rw [hsec_app (opensTangentEquiv S.baseNeighborhood xW (mfderiv (𝓡 n) (𝓡 n) D.proj y a)),
        mfderiv_subtype_val_opensTangentEquiv S.baseNeighborhood xW]
    exact hA'inj (h1.trans (hA_app a).symm)
  rw [hB V, hB W]
  exact (roundInner_congr hγ.symm (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) (D.ρ γ)) y V)
      (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) (D.ρ γ)) y W)).symm.trans
    (roundInner_sphereDiffeo (E := E) (n := n) (D.ρ γ) y V W)

theorem exists_partialDiffeomorph_gQuot_inner (D : RoundSphereQuotient E n) (x₀ : D.Q) :
    ∃ e : PartialDiffeomorph (𝓡 n) (𝓡 n) (sphere (0 : E) 1) D.Q ∞,
      x₀ ∈ e.target ∧ ∀ y ∈ e.source, ∀ (V W : TangentSpace (𝓡 n) y),
        D.gQuot.inner (e y) (mfderiv (𝓡 n) (𝓡 n) e y V)
            (mfderiv (𝓡 n) (𝓡 n) e y W)
          = (roundMetric (E := E) (n := n)).inner y V W := by
  let S := D.sectionAt x₀
  have hUne : Nonempty S.baseNeighborhood := ⟨⟨x₀, S.mem_baseNeighborhood⟩⟩
  let A : PartialDiffeomorph (𝓡 n) (𝓡 n) S.baseNeighborhood D.Q ∞ :=
    openSubtypePartialDiffeomorph (𝓡 n) S.baseNeighborhood hUne
  have hAinv : ∀ (x : D.Q) (hx : x ∈ (S.baseNeighborhood : Set D.Q)),
      A.invFun x = ⟨x, hx⟩ := by
    intro x hx
    have h := A.right_inv'
      (show x ∈ A.target from by
        simpa only [A, openSubtypePartialDiffeomorph_target] using hx)
    exact Subtype.ext h
  have hAcont : ContMDiffOn (𝓡 n) (𝓡 n) ∞ A.invFun (S.baseNeighborhood : Set D.Q) := by
    simpa only [A, openSubtypePartialDiffeomorph_target] using A.contMDiffOn_invFun
  have hsec : ∀ (y : sphere (0 : E) 1)
      (hy : y ∈ (S.sphereNeighborhood : Set (sphere (0 : E) 1))),
      S.toSphere (S.localSection.symm ⟨y, hy⟩) = y := by
    intro y hy
    have h1 : S.localSection (S.localSection.symm ⟨y, hy⟩) = ⟨y, hy⟩ :=
      (S.localSection).apply_symm_apply ⟨y, hy⟩
    exact congrArg (Subtype.val : S.sphereNeighborhood → sphere (0 : E) 1) h1
  have hproj : ∀ (y : sphere (0 : E) 1)
      (hy : y ∈ (S.sphereNeighborhood : Set (sphere (0 : E) 1))),
      D.proj y = (S.localSection.symm ⟨y, hy⟩ : D.Q) := by
    intro y hy
    calc D.proj y = D.proj (S.toSphere (S.localSection.symm ⟨y, hy⟩)) := by rw [hsec y hy]
      _ = (S.localSection.symm ⟨y, hy⟩ : D.Q) := S.toSphere_proj _
  refine ⟨{ toFun := D.proj
            invFun := fun x => S.toSphere (A.invFun x)
            source := (S.sphereNeighborhood : Set (sphere (0 : E) 1))
            target := (S.baseNeighborhood : Set D.Q)
            map_source' := ?_
            map_target' := ?_
            left_inv' := ?_
            right_inv' := ?_
            open_source := S.sphereNeighborhood.2
            open_target := S.baseNeighborhood.2
            contMDiffOn_toFun := D.proj_smooth.contMDiffOn
            contMDiffOn_invFun := ?_ }, ?_, ?_⟩
  · intro y hy
    rw [hproj y hy]
    exact (S.localSection.symm ⟨y, hy⟩).2
  · intro x hx
    exact (S.localSection (A.invFun x)).2
  · intro y hy
    rw [hproj y hy, hAinv _ (S.localSection.symm ⟨y, hy⟩).2]
    exact hsec y hy
  · intro x hx
    show D.proj (S.toSphere (A.invFun x)) = x
    rw [hAinv x hx]
    exact S.toSphere_proj ⟨x, hx⟩
  · have hcomp : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (S.toSphere ∘ A.invFun)
        (S.baseNeighborhood : Set D.Q) :=
      ContMDiffOn.comp (s := (S.baseNeighborhood : Set D.Q)) (t := Set.univ)
        (S.toSphere_contMDiff.contMDiffOn) hAcont (fun z _ => Set.mem_univ (A.invFun z))
    exact hcomp
  · exact S.mem_baseNeighborhood
  · intro y hy V W
    exact gQuot_inner_proj D y V W

end RoundSphereQuotient

end DifferentialGeometry.Geometry
