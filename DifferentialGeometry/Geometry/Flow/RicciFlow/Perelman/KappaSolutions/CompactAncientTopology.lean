import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SelectedCompactDiagonalProjective
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CompactAncientSphere
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.OrientedCylinderExclusion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSurfaceSmoothModels

section
set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

private theorem nonempty_antipodal_projectivePlane_diffeomorph :
    Nonempty (SphereAntipodalQuotient ≃ₘ⟮𝓡 2, 𝓡 2⟯ RealProjectivePlane) := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  obtain ⟨e, _he⟩ := exists_antipodal_quotient_diffeomorph
    realProjectivePlaneQuotientMap
    (realProjectiveSpaceQuotientMap_isLocalDiffeomorph (E := EuclideanSpace ℝ (Fin 3)) (n := 2))
    realProjectivePlaneQuotientMap_surjective (by
      intro x y
      rw [realProjectivePlaneQuotientMap_eq_iff]
      constructor
      · rintro (h | h)
        · exact Or.inl h.symm
        · right
          apply Subtype.ext
          change (y : EuclideanSpace ℝ (Fin 3)) = -(x : EuclideanSpace ℝ (Fin 3))
          simpa only [neg_neg] using (congrArg Neg.neg h).symm
      · rintro (rfl | rfl)
        · exact Or.inl rfl
        · right
          simp)
  exact ⟨e⟩

theorem nonempty_positiveComponent_of_compact_nonround_ancientKappa
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) [CompactSpace F.M]
    (hnotround : ¬ IsShrinkingSphericalSpaceFormFlow F)
    (orient : TangentOrientationSection F.M) :
    Nonempty (PositiveComponent (univ : Set F.M)) := by
  let tau : ℕ → ℝ := fun i => (i : ℝ) + 1
  have htau (i : ℕ) : 0 < tau i := by dsimp only [tau]; positivity
  have hescape : Tendsto tau atTop atTop := tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  obtain ⟨b, hb, _hbmem, q, N, _hsigma, P, phi, Phi, _R, _bf, _hsrc, _htgt, co,
      _hphi, _hRP, _hR, _hconn, _hcomplete, _hsolution, hf, _hscalar, _hancient,
      _hflow, _hcomparison, _hback, Psi, _hPsi, _C, _hC, _href⟩ :=
    exists_poleEndpoint_strongNecks_or_diagonal_canonical_with_projective_presentation_of_not_round
      F hF hnotround F.basepoint tau htau hescape
  obtain ⟨f, _hsol, _hnormal, hmass, _hmasslt, _hnoncompact, _hmodels, hcases⟩ := hf
  rcases hcases with ⟨d, hd, hpotential, _hnecks⟩ | ⟨d, _hd, _hpotential⟩ | ⟨_d, _hd, _hpotential, _htubes, hcaps⟩
  · obtain ⟨e⟩ := nonempty_diffeomorph_sphere_of_compact_ordinary_cylinder F hF b hb F.basepoint P
      (co.gInf 0) f d (hd 0 le_rfl) hpotential hmass
    exact ⟨positiveComponentOfDiffeomorphSphereThree e⟩
  · obtain ⟨e⟩ := nonempty_antipodal_projectivePlane_diffeomorph
    exact (pointedLimit_not_antipodalProduct_diffeomorph Psi (fun _ => orient)
      ⟨(e.prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)).trans d⟩).elim
  · obtain ⟨_p, _hp, _L, _r, _Cmodel, _rsource, _Csource, _hL, _hpL, _hr, _hCm,
      _hrs, _hrsC, _hCs, _cap, _hcore, _htube, _hmap, _hcount, _hchain, _hfar,
      _hK, _hlim, _B, _hBc, _hUB, hcapSource⟩ := hcaps (1 / 100 : ℝ) (by norm_num) (by norm_num)
    obtain ⟨i, hi⟩ := hcapSource.exists
    obtain ⟨_hBi, _cap', _hcore', _htube', _hmap', _hcount', _hchain', _hdepth',
      _Ks, _hKs, _hrad, _hcap, _hextconn, _hextcompact, _hsmooth, _hboundary, _hemb,
      _G, _hG, _hGo, _hGc, _hGs, e, _heSlab, _heCollar, pr, _hpr, _D, _hD, _heBall⟩ := hi
    exact ⟨positiveComponentOfDiffeomorphProjective F.M pr (Diffeomorph.refl I3 F.M ∞)⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end
