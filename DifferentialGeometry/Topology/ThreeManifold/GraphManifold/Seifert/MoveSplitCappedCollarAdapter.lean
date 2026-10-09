import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedCollarAdapterData
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedCollarAdapterDisc

/-!
Precomposing actual germ side maps by the radius-three disc compression restores the frozen full
collar interface. Ports and holonomy are retained, and the same image supplies all cap/core fields.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff

universe u

namespace GC.Seifert.ElementaryPresentation

private local instance : ChartedSpace (EuclideanHalfSpace 2)
    (discPlanarBase.{u} 1).surface.Carrier :=
  inferInstanceAs (ChartedSpace (EuclideanHalfSpace 2) discSet.{u})

private local instance : IsManifold (𝓡∂ 2) ∞ (discPlanarBase.{u} 1).surface.Carrier :=
  inferInstanceAs (IsManifold (𝓡∂ 2) ∞ discSet.{u})

variable {Q : ConnectedClosedOrientedManifold.{u} 3} {E : ElementaryPresentation (NoCuts.carrier Q)}
  {j : Fin E.toTorus.pairing.count} {b : Bool} {h : E.IsSplitSeam j b}
  {T : SphericalTubeSystem Q.toClosedOrientedManifold} {N : ClosedOrientedManifold.{u} 3}
  {K : SphericalCapping Q.toClosedOrientedManifold N T} {a : T.Index}

def sideData_of_collarGerm (G : E.SideDataGerm h K a) {δ₂ : ℝ}
    (hδ₂ : 0 < δ₂) (hbound : δ₂ ≤ G.bound) : E.SideData h K a δ₂ := by
  let k := δ₂ / G.δ_star
  have hk : 0 < k := G.ratio_pos hδ₂
  have hcompression := exists_discCollarCompression.{u} hk (G.ratio_le_one hbound)
  let R := Classical.choose hcompression
  have hcollar := (Classical.choose_spec hcompression).2
  let I := (𝓡∂ 2).prod (𝓡 1)
  let P : ((discPlanarBase.{u} 1).surface.Carrier × Circle) ≃ₘ⟮I, I⟯
      ((discPlanarBase.{u} 1).surface.Carrier × Circle) :=
    R.prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)
  have hzero (p : Torus) :
      P ((discPlanarBase.{u} 1).collar 0 (p.1, halfZero), p.2) =
        ((discPlanarBase.{u} 1).collar 0 (p.1, halfZero), p.2) := by
    apply Prod.ext
    · change R ((discPlanarBase.{u} 1).collar 0 (p.1, halfZero)) =
        (discPlanarBase.{u} 1).collar 0 (p.1, halfZero)
      simpa only [R, halfZero, mul_zero] using hcollar p.1 0 le_rfl one_pos
    · rfl
  have hboundary (q : (discPlanarBase.{u} 1).surface.Carrier × Circle) :
      OnSolidBoundary (P q) → OnSolidBoundary q := by
    rintro ⟨p, hp⟩
    exact ⟨p, P.injective (hp.trans (hzero p).symm)⟩
  refine
    { port := G.port
      port_ne := G.port_ne
      port_false_ne_true := G.port_false_ne_true
      holonomy := G.holonomy
      solid := fun t q => G.solid t (P q)
      smooth := fun t => (G.smooth t).comp P.contMDiff
      mfderiv_bijective := ?_
      injective := fun t => (G.injective t).comp P.injective
      collar := ?_
      cap_mem := ?_
      core_mem := ?_
      image := fun t q => G.image t (P q)
      boundary_of_eq := ?_ }
  · intro t q
    have hbP : Function.Bijective (mfderiv I I P q) :=
      (P.mfderivToContinuousLinearEquiv (by simp) q).bijective
    change Function.Bijective (mfderiv I (𝓡 3) (G.solid t ∘ P) q)
    rw [mfderiv_comp q ((G.smooth t).mdifferentiableAt (by simp))
      (P.contMDiff.mdifferentiableAt (by simp))]
    exact (G.mfderiv_bijective t (P q)).comp hbP
  · intro t p s hs hs1
    change G.solid t (R ((discPlanarBase.{u} 1).collar 0 (p.1, halfPoint s hs)), p.2) = _
    rw [hcollar p.1 s hs hs1, G.collar t p (k * s) (mul_nonneg hk.le hs)
      (G.ratio_mul_lt hδ₂ hbound hs1 t)]
    have he : G.δ_star * (k * s) = δ₂ * s := by
      dsimp [k]
      field_simp [G.δ_star_pos.ne']
    rw [he]
  · intro t w
    obtain ⟨q, hq⟩ := G.cap_mem t w
    refine ⟨P.symm q, ?_⟩
    rwa [P.apply_symm_apply]
  · intro y hy hc
    obtain ⟨t, q, hq⟩ := G.core_mem y hy hc
    refine ⟨t, P.symm q, ?_⟩
    rwa [P.apply_symm_apply]
  · intro q q' heq
    obtain ⟨hq, hq'⟩ := G.boundary_of_eq (P q) (P q') heq
    exact ⟨hboundary q hq, hboundary q' hq'⟩

theorem sideData_of_collarGerm_port (G : E.SideDataGerm h K a) {δ₂ : ℝ}
    (hδ₂ : 0 < δ₂) (hbound : δ₂ ≤ G.bound) :
    (sideData_of_collarGerm G hδ₂ hbound).port = G.port := rfl

theorem sideData_of_collarGerm_holonomy (G : E.SideDataGerm h K a) {δ₂ : ℝ}
    (hδ₂ : 0 < δ₂) (hbound : δ₂ ≤ G.bound) :
    (sideData_of_collarGerm G hδ₂ hbound).holonomy = G.holonomy := rfl

theorem exists_sideData_of_collarGerm (G : E.SideDataGerm h K a) :
    ∃ δ₀ > (0 : ℝ), ∀ δ₂, 0 < δ₂ → δ₂ ≤ δ₀ → Nonempty (E.SideData h K a δ₂) :=
  ⟨G.bound, G.bound_pos, fun δ₂ hδ₂ hbound => ⟨sideData_of_collarGerm G (δ₂ := δ₂) hδ₂ hbound⟩⟩

end GC.Seifert.ElementaryPresentation
