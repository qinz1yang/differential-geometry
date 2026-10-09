/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Analysis.Calculus.Quasiconformal.NullSets
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.Quasiconformal
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.CoarseMaps
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Dynamics.BoundaryPairErgodicity
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Dynamics.FrameTensorDynamics
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Dynamics.FrameTensorIsotropy
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Dynamics.GeodesicErgodicity
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Rigidity.RecurrentBoundary

open MeasureTheory DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.MostowRigidity

open DifferentialGeometry.Hyperbolic
open DifferentialGeometry.HyperbolicAction
open DifferentialGeometry.HyperbolicBoundary
open DifferentialGeometry.BoundaryTopology

variable {n : ℕ}

theorem exists_equivariant_boundary_extension_of_uniform_morse
    (hn : 3 ≤ n) (Γ Λ : Subgroup (PO n 1))
    (disc_Γ : IsDiscrete (SetLike.coe Γ)) (disc_Λ : IsDiscrete (SetLike.coe Λ))
    (hcoΓ : UniformPseudoIsometry.ActsCocompactly (by omega : 1 ≤ n) Γ)
    (hcoΛ : UniformPseudoIsometry.ActsCocompactly (by omega : 1 ≤ n) Λ)
    (f : Γ ≃* Λ)
    (hmorse : ∀ (Φ : HUpper n → HUpper n) (K C : ℝ),
      PseudoIsometry.IsPseudoIsometry K C Φ →
      PseudoIsometry.IsFEquivariant f (by omega : 1 ≤ n) Φ →
      ∀ (o : HUpper n) (ξ : BoundaryH n) (M : ℝ), ∃ N : ℕ, ∀ s ≥ N, ∀ t ≥ N,
        ∀ w : HUpper n,
        MorseStability.OnSegment (Φ (AsymptoticRays.rayTo o ξ (s : ℝ)))
          (Φ (AsymptoticRays.rayTo o ξ (t : ℝ))) w → M ≤ dist (Φ o) w) :
    ∃ (Φ : HUpper n → HUpper n) (K C : ℝ) (φ : BoundaryH n → BoundaryH n),
      PseudoIsometry.IsPseudoIsometry K C Φ
      ∧ PseudoIsometry.IsFEquivariant f (by omega : 1 ≤ n) Φ
      ∧ (∀ (γ : Γ) (ξ : BoundaryH n),
          φ ((poBoundaryMulAction (by omega : 1 ≤ n)).smul (γ : PO n 1) ξ)
            = (poBoundaryMulAction (by omega : 1 ≤ n)).smul (f γ : PO n 1) (φ ξ))
      ∧ (∀ ξ : BoundaryH n,
          BoundaryTopology.ConvergesToBoundary
            (fun m : ℕ => Φ (BoundaryTopology.geodesicRay ξ (m : ℝ))) (φ ξ)) := by
  have h1 : (1 : ℕ) ≤ n := by omega
  obtain ⟨Φ, K, C, hPI, hFE⟩ :=
    UniformPseudoIsometry.exists_isPseudoIsometry_isFEquivariant_of_actsCocompactly
      h1 Γ Λ disc_Γ disc_Λ hcoΓ hcoΛ f
  obtain ⟨φ, hφeq, hφconv⟩ :=
    MorseStability.exists_equivariant_boundary_extension_of_onSegment_tendsto hPI h1 hFE
      (hmorse Φ K C hPI hFE)
  exact ⟨Φ, K, C, φ, hPI, hFE, hφeq, hφconv⟩

theorem exists_equivariant_boundary_extension_of_uniform
    (hn : 3 ≤ n) (Γ Λ : Subgroup (PO n 1))
    (disc_Γ : IsDiscrete (SetLike.coe Γ)) (disc_Λ : IsDiscrete (SetLike.coe Λ))
    (hcoΓ : UniformPseudoIsometry.ActsCocompactly (by omega : 1 ≤ n) Γ)
    (hcoΛ : UniformPseudoIsometry.ActsCocompactly (by omega : 1 ≤ n) Λ)
    (f : Γ ≃* Λ) :
    ∃ (Φ : HUpper n → HUpper n) (K C : ℝ) (φ : BoundaryH n → BoundaryH n),
      PseudoIsometry.IsPseudoIsometry K C Φ
      ∧ PseudoIsometry.IsFEquivariant f (by omega : 1 ≤ n) Φ
      ∧ (∀ (γ : Γ) (ξ : BoundaryH n),
          φ ((poBoundaryMulAction (by omega : 1 ≤ n)).smul (γ : PO n 1) ξ)
            = (poBoundaryMulAction (by omega : 1 ≤ n)).smul (f γ : PO n 1) (φ ξ))
      ∧ (∀ ξ : BoundaryH n,
          BoundaryTopology.ConvergesToBoundary
            (fun m : ℕ => Φ (BoundaryTopology.geodesicRay ξ (m : ℝ))) (φ ξ)) := by
  have h1 : (1 : ℕ) ≤ n := by omega
  obtain ⟨Φ, K, C, hPI, hFE⟩ :=
    UniformPseudoIsometry.exists_isPseudoIsometry_isFEquivariant_of_actsCocompactly
      h1 Γ Λ disc_Γ disc_Λ hcoΓ hcoΛ f
  obtain ⟨φ, hφeq, hφconv⟩ :=
    MorseStability.exists_equivariant_boundary_extension_of_onSegment_tendsto hPI h1 hFE
      (fun o ξ M => MorseDivergence.onSegment_tendsto_of_isPseudoIsometry hPI h1 o ξ M)
  exact ⟨Φ, K, C, φ, hPI, hFE, hφeq, hφconv⟩

theorem exists_equivariant_homeomorph_boundary_extension_of_uniform
    (hn : 3 ≤ n) (Γ Λ : Subgroup (PO n 1))
    (disc_Γ : IsDiscrete (SetLike.coe Γ)) (disc_Λ : IsDiscrete (SetLike.coe Λ))
    (hcoΓ : UniformPseudoIsometry.ActsCocompactly (by omega : 1 ≤ n) Γ)
    (hcoΛ : UniformPseudoIsometry.ActsCocompactly (by omega : 1 ≤ n) Λ)
    (f : Γ ≃* Λ) :
    ∃ (Φ : HUpper n → HUpper n) (K C : ℝ) (φ : BoundaryH n ≃ₜ BoundaryH n),
      PseudoIsometry.IsPseudoIsometry K C Φ
      ∧ PseudoIsometry.IsFEquivariant f (by omega : 1 ≤ n) Φ
      ∧ (∀ (γ : Γ) (ξ : BoundaryH n),
          φ ((poBoundaryMulAction (by omega : 1 ≤ n)).smul (γ : PO n 1) ξ)
            = (poBoundaryMulAction (by omega : 1 ≤ n)).smul (f γ : PO n 1) (φ ξ))
      ∧ (∀ ξ : BoundaryH n,
          BoundaryTopology.ConvergesToBoundary
            (fun m : ℕ => Φ (BoundaryTopology.geodesicRay ξ (m : ℝ))) (φ ξ)) := by
  have h1 : (1 : ℕ) ≤ n := by omega
  obtain ⟨Φ, K, C, φ, hPI, hFE, hφeq, hφconv⟩ :=
    BoundaryHomeomorph.exists_equivariant_homeomorph_boundaryExtension h1 Γ Λ disc_Γ disc_Λ
      hcoΓ hcoΛ f
  exact ⟨Φ, K, C, φ, hPI, hFE, hφeq, hφconv⟩

theorem exists_equivariant_pseudoIsometry_mobius_boundary
    (hn : 3 ≤ n) (Γ Λ : Subgroup (PO n 1))
    (disc_Γ : IsDiscrete (SetLike.coe Γ)) (disc_Λ : IsDiscrete (SetLike.coe Λ))
    [HasFundamentalDomain Γ (PO n 1)] [HasFundamentalDomain Λ (PO n 1)]
    (hΓ : Countable ↥Γ) (hΛ : Countable ↥Λ)
    (hΓinf : Infinite ↥Γ) (hΛinf : Infinite ↥Λ)
    (covol_Γ : covolume Γ (PO n 1) ≠ ⊤) (hcovΓ : covolume Γ (PO n 1) ≠ 0)
    (covol_Λ : covolume Λ (PO n 1) ≠ ⊤) (hcovΛ : covolume Λ (PO n 1) ≠ 0)
    (f : Γ ≃* Λ) :
    ∃ (Φ : HUpper n → HUpper n) (K C : ℝ),
      PseudoIsometry.IsPseudoIsometry K C Φ
      ∧ PseudoIsometry.IsFEquivariant f (by omega : 1 ≤ n) Φ
      ∧ ∃ φ : BoundaryH n ≃ₜ BoundaryH n,
          (∀ (γ : Γ) (ξ : BoundaryH n),
            φ ((poBoundaryMulAction (by omega : 1 ≤ n)).smul (γ : PO n 1) ξ)
              = (poBoundaryMulAction (by omega : 1 ≤ n)).smul (f γ : PO n 1) (φ ξ))
          ∧ (∃ g : PO n 1, ∀ ξ : BoundaryH n,
              φ ξ = (poBoundaryMulAction (by omega : 1 ≤ n)).smul g ξ)
          ∧ (∀ ξ : BoundaryH n,
              BoundaryTopology.ConvergesToBoundary
                (fun m : ℕ => Φ (BoundaryTopology.geodesicRay ξ (m : ℝ))) (φ ξ)) := by
  have h1 : 1 ≤ n := by omega
  have hright : Measure.IsMulRightInvariant (volume : Measure (PO n 1)) :=
    LatticeMeasure.volume_isMulRightInvariant Γ disc_Γ covol_Γ
  let : Countable Γ := hΓ
  let : Countable Λ := hΛ
  let : Measure.IsMulRightInvariant (volume : Measure (PO n 1)) := hright
  let νΓ := DifferentialGeometry.HomogeneousSpaceMeasure.probabilityMeasure volume Γ
  let νΛ := DifferentialGeometry.HomogeneousSpaceMeasure.probabilityMeasure volume Λ
  have hνΓprob : IsProbabilityMeasure νΓ :=
    DifferentialGeometry.HomogeneousSpaceMeasure.isProbabilityMeasure_probabilityMeasure volume Γ covol_Γ hcovΓ
  have hνΛprob : IsProbabilityMeasure νΛ :=
    DifferentialGeometry.HomogeneousSpaceMeasure.isProbabilityMeasure_probabilityMeasure volume Λ covol_Λ hcovΛ
  have hνΓright (g : PO n 1) :
      MeasurePreserving (DifferentialGeometry.HomogeneousSpaceMeasure.right Γ g) νΓ νΓ :=
    DifferentialGeometry.HomogeneousSpaceMeasure.probabilityMeasure_right volume Γ g
  have hνΛright (g : PO n 1) :
      MeasurePreserving (DifferentialGeometry.HomogeneousSpaceMeasure.right Λ g) νΛ νΛ :=
    DifferentialGeometry.HomogeneousSpaceMeasure.probabilityMeasure_right volume Λ g
  have hνΓnull (U : Set (DifferentialGeometry.HomogeneousSpaceMeasure.FrameQuotient Γ)) (hU : MeasurableSet U) :
      νΓ U = 0 ↔ volume (DifferentialGeometry.HomogeneousSpaceMeasure.projection Γ ⁻¹' U) = 0 :=
    DifferentialGeometry.HomogeneousSpaceMeasure.probabilityMeasure_null_iff volume Γ covol_Γ hU
  have hνΛnull (U : Set (DifferentialGeometry.HomogeneousSpaceMeasure.FrameQuotient Λ)) (hU : MeasurableSet U) :
      νΛ U = 0 ↔ volume (DifferentialGeometry.HomogeneousSpaceMeasure.projection Λ ⁻¹' U) = 0 :=
    DifferentialGeometry.HomogeneousSpaceMeasure.probabilityMeasure_null_iff volume Λ covol_Λ hU
  have hthickΓ : ∀ ε : ℝ, 0 < ε →
      ∃ K : Set (HUpper n), IsCompact K ∧ K ⊆ LatticeCompactness.thickPart h1 Γ ε ∧
        ∀ x ∈ LatticeCompactness.thickPart h1 Γ ε, ∃ γ : Γ,
          (poMulAction h1).smul (γ : PO n 1) x ∈ K :=
    fun _ hε => LatticeCompactness.exists_compact_thickPart_core h1 Γ disc_Γ covol_Γ hε
  have hthickΛ : ∀ ε : ℝ, 0 < ε →
      ∃ K : Set (HUpper n), IsCompact K ∧ K ⊆ LatticeCompactness.thickPart h1 Λ ε ∧
        ∀ x ∈ LatticeCompactness.thickPart h1 Λ ε, ∃ γ : Λ,
          (poMulAction h1).smul (γ : PO n 1) x ∈ K :=
    fun _ hε => LatticeCompactness.exists_compact_thickPart_core h1 Λ disc_Λ covol_Λ hε
  obtain ⟨ε, hε, hMargulis⟩ := Margulis.exists_margulis_constant h1
  obtain ⟨KΓ, hKΓcompact, hKΓthick, hKΓcover⟩ := hthickΓ ε hε
  obtain ⟨KΛ, hKΛcompact, hKΛthick, hKΛcover⟩ := hthickΛ ε hε
  have hsmallΓ : ∀ x : HUpper n,
      Group.IsVirtuallyNilpotent (Margulis.smallSubgroup h1 Γ ε x) :=
    hMargulis Γ disc_Γ
  have hsmallΛ : ∀ x : HUpper n,
      Group.IsVirtuallyNilpotent (Margulis.smallSubgroup h1 Λ ε x) :=
    hMargulis Λ disc_Λ
  have hgeometryΓ : ∀ x : HUpper n,
      BoundaryStabilizer.ElementaryGeometry h1 (Margulis.smallSubgroup h1 Γ ε x) :=
    fun x => BoundaryStabilizer.smallSubgroup_geometry h1 Γ disc_Γ ε x (hsmallΓ x)
  have hgeometryΛ : ∀ x : HUpper n,
      BoundaryStabilizer.ElementaryGeometry h1 (Margulis.smallSubgroup h1 Λ ε x) :=
    fun x => BoundaryStabilizer.smallSubgroup_geometry h1 Λ disc_Λ ε x (hsmallΛ x)
  have hstructureΓ : ∀ x : HUpper n,
      AxialGroups.ElementaryStructure h1 (Margulis.smallSubgroup h1 Γ ε x) :=
    fun x => AxialGroups.structure_of_geometry h1 _
      (disc_Γ.mono (Margulis.smallSubgroup_le h1 Γ ε x)) (hgeometryΓ x)
  have hstructureΛ : ∀ x : HUpper n,
      AxialGroups.ElementaryStructure h1 (Margulis.smallSubgroup h1 Λ ε x) :=
    fun x => AxialGroups.structure_of_geometry h1 _
      (disc_Λ.mono (Margulis.smallSubgroup_le h1 Λ ε x)) (hgeometryΛ x)
  have hregionsΓ : Pairwise (fun ξ η : BoundaryH n =>
      Disjoint (closure (ParabolicRegions.region h1 Γ (ε / 2) ξ))
        (closure (ParabolicRegions.region h1 Γ (ε / 2) η))) :=
    fun _ _ hne => ParabolicRegions.disjoint_closure_regions h1 Γ disc_Γ
      (by linarith : ε / 2 < ε) hgeometryΓ hne
  have hregionsΛ : Pairwise (fun ξ η : BoundaryH n =>
      Disjoint (closure (ParabolicRegions.region h1 Λ (ε / 2) ξ))
        (closure (ParabolicRegions.region h1 Λ (ε / 2) η))) :=
    fun _ _ hne => ParabolicRegions.disjoint_closure_regions h1 Λ disc_Λ
      (by linarith : ε / 2 < ε) hgeometryΛ hne
  have hlocalΓ : LocallyFinite (ParabolicRegions.closedRegion h1 Γ (ε / 2)) :=
    ParabolicRegions.locallyFinite_closedRegion h1 Γ disc_Γ (ε / 2)
  have hlocalΛ : LocallyFinite (ParabolicRegions.closedRegion h1 Λ (ε / 2)) :=
    ParabolicRegions.locallyFinite_closedRegion h1 Λ disc_Λ (ε / 2)
  have hhalf : 0 < ε / 2 := by linarith
  have hclosedGeometryΓ : ∀ x : HUpper n,
      BoundaryStabilizer.ElementaryGeometry h1
        (OrbifoldStrata.closedSmallSubgroup h1 Γ (ε / 2) x) :=
    fun x => OrbifoldStrata.closedSmallSubgroup_geometry h1 Γ
      (by linarith : ε / 2 < ε) x (hgeometryΓ x)
  have hclosedGeometryΛ : ∀ x : HUpper n,
      BoundaryStabilizer.ElementaryGeometry h1
        (OrbifoldStrata.closedSmallSubgroup h1 Λ (ε / 2) x) :=
    fun x => OrbifoldStrata.closedSmallSubgroup_geometry h1 Λ
      (by linarith : ε / 2 < ε) x (hgeometryΛ x)
  have hstrataLocalΓ : LocallyFinite (OrbifoldStrata.fixedStratum h1 Γ (ε / 2)) :=
    OrbifoldStrata.locallyFinite_fixedStratum h1 Γ disc_Γ (ε / 2)
  have hstrataLocalΛ : LocallyFinite (OrbifoldStrata.fixedStratum h1 Λ (ε / 2)) :=
    OrbifoldStrata.locallyFinite_fixedStratum h1 Λ disc_Λ (ε / 2)
  have hstrataCompactΓ (σ : Set (HUpper n)) (hσ : σ.Nonempty) :=
    OrbifoldStrata.exists_compact_cover_closure_fixedStratum h1 Γ disc_Γ covol_Γ hhalf hσ
  have hstrataCompactΛ (σ : Set (HUpper n)) (hσ : σ.Nonempty) :=
    OrbifoldStrata.exists_compact_cover_closure_fixedStratum h1 Λ disc_Λ covol_Λ hhalf hσ
  have hstrataIncidenceΓ (σ : Set (HUpper n)) (hσ : σ.Nonempty) :=
    OrbifoldStrata.exists_finite_incident_representatives h1 Γ disc_Γ covol_Γ hhalf hσ
  have hstrataIncidenceΛ (σ : Set (HUpper n)) (hσ : σ.Nonempty) :=
    OrbifoldStrata.exists_finite_incident_representatives h1 Λ disc_Λ covol_Λ hhalf hσ
  have hstrataParabolicsΓ (σ : Set (HUpper n)) (hσ : σ.Nonempty) :=
    OrbifoldStrata.exists_finite_parabolic_neighbors h1 Γ disc_Γ covol_Γ hhalf hσ
  have hstrataParabolicsΛ (σ : Set (HUpper n)) (hσ : σ.Nonempty) :=
    OrbifoldStrata.exists_finite_parabolic_neighbors h1 Λ disc_Λ covol_Λ hhalf hσ
  have hincidenceLengthΓ := FixedLocusGeometry.incidence_chain_length_le h1 Γ disc_Γ (ε / 2)
  have hincidenceLengthΛ := FixedLocusGeometry.incidence_chain_length_le h1 Λ disc_Λ (ε / 2)
  have hstratumObstructionΓ (σ : Set (HUpper n)) (hσ : σ.Nonempty)
      (hF : (OrbifoldStrata.fixedStratum h1 Γ (ε / 2) σ).Nonempty)
      (hproper : σ ≠ Set.univ)
      (hopen : IsOpen (OrbifoldStrata.fixedStratum h1 Γ (ε / 2) σ)) :=
    StratumDeformation.exists_axial_extremal_of_isOpen h1 Γ disc_Γ hhalf.le
      hclosedGeometryΓ hσ hF hproper hopen
  have hstratumObstructionΛ (σ : Set (HUpper n)) (hσ : σ.Nonempty)
      (hF : (OrbifoldStrata.fixedStratum h1 Λ (ε / 2) σ).Nonempty)
      (hproper : σ ≠ Set.univ)
      (hopen : IsOpen (OrbifoldStrata.fixedStratum h1 Λ (ε / 2) σ)) :=
    StratumDeformation.exists_axial_extremal_of_isOpen h1 Λ disc_Λ hhalf.le
      hclosedGeometryΛ hσ hF hproper hopen
  have hstratumOutgoingΓ (σ : Set (HUpper n)) (hσ : σ.Nonempty)
      (hopen : ¬IsOpen (OrbifoldStrata.fixedStratum h1 Γ (ε / 2) σ)) :=
    StratumIncidence.exists_higher_rank_incident_of_not_isOpen h1 Γ disc_Γ (ε / 2) hσ hopen
  have hstratumOutgoingΛ (σ : Set (HUpper n)) (hσ : σ.Nonempty)
      (hopen : ¬IsOpen (OrbifoldStrata.fixedStratum h1 Λ (ε / 2) σ)) :=
    StratumIncidence.exists_higher_rank_incident_of_not_isOpen h1 Λ disc_Λ (ε / 2) hσ hopen
  have hstratumNotOpenΓ (σ : Set (HUpper n)) (hσ : σ.Nonempty)
      (hF : (OrbifoldStrata.fixedStratum h1 Γ (ε / 2) σ).Nonempty)
      (hproper : σ ≠ Set.univ) :=
    StratumMaximum.not_isOpen_fixedStratum h1 (by omega) Γ disc_Γ covol_Γ hhalf
      hclosedGeometryΓ hσ hF hproper
  have hstratumNotOpenΛ (σ : Set (HUpper n)) (hσ : σ.Nonempty)
      (hF : (OrbifoldStrata.fixedStratum h1 Λ (ε / 2) σ).Nonempty)
      (hproper : σ ≠ Set.univ) :=
    StratumMaximum.not_isOpen_fixedStratum h1 (by omega) Λ disc_Λ covol_Λ hhalf
      hclosedGeometryΛ hσ hF hproper
  have hfiniteStratumOrbitsΓ :=
    FiniteLocusCompactness.exists_finite_stratum_representatives h1 (by omega)
      Γ disc_Γ covol_Γ hhalf hclosedGeometryΓ
  have hfiniteStratumOrbitsΛ :=
    FiniteLocusCompactness.exists_finite_stratum_representatives h1 (by omega)
      Λ disc_Λ covol_Λ hhalf hclosedGeometryΛ
  obtain ⟨QΓ, hQΓcompact, hQΓfinite, hQΓcover⟩ :=
    FiniteLocusCompactness.exists_compact_finiteLocus_core h1 (by omega)
      Γ disc_Γ covol_Γ hhalf hclosedGeometryΓ
  obtain ⟨QΛ, hQΛcompact, hQΛfinite, hQΛcover⟩ :=
    FiniteLocusCompactness.exists_compact_finiteLocus_core h1 (by omega)
      Λ disc_Λ covol_Λ hhalf hclosedGeometryΛ
  have hfiniteParabolicNeighborsΓ :=
    FiniteLocusCompactness.exists_finite_parabolic_neighbors h1 (by omega)
      Γ disc_Γ covol_Γ hhalf hclosedGeometryΓ
  have hfiniteParabolicNeighborsΛ :=
    FiniteLocusCompactness.exists_finite_parabolic_neighbors h1 (by omega)
      Λ disc_Λ covol_Λ hhalf hclosedGeometryΛ
  have hfiniteLocusNonemptyΓ := OrbifoldThinRegions.finiteLocus_nonempty h1 (by omega)
    Γ disc_Γ hhalf.le (by linarith : ε / 2 < ε) hgeometryΓ
  have hfiniteLocusNonemptyΛ := OrbifoldThinRegions.finiteLocus_nonempty h1 (by omega)
    Λ disc_Λ hhalf.le (by linarith : ε / 2 < ε) hgeometryΛ
  have hparabolicOrbitsΓ := OrbifoldThinRegions.exists_finite_parabolic_representatives
    h1 (by omega) Γ disc_Γ covol_Γ hhalf (by linarith : ε / 2 < ε) hgeometryΓ
  have hparabolicOrbitsΛ := OrbifoldThinRegions.exists_finite_parabolic_representatives
    h1 (by omega) Λ disc_Λ covol_Λ hhalf (by linarith : ε / 2 < ε) hgeometryΛ
  obtain ⟨truncΓ⟩ := CuspTruncation.exists_finite_cusp_truncation h1 (by omega)
    Γ disc_Γ covol_Γ hhalf (by linarith : ε / 2 < ε) hgeometryΓ
  obtain ⟨truncΛ⟩ := CuspTruncation.exists_finite_cusp_truncation h1 (by omega)
    Λ disc_Λ covol_Λ hhalf (by linarith : ε / 2 < ε) hgeometryΛ
  have htruncΓnonempty := truncΓ.core_nonempty (by omega) disc_Γ hhalf.le
    (by linarith : ε / 2 < ε) hgeometryΓ
  have htruncΛnonempty := truncΛ.core_nonempty (by omega) disc_Λ hhalf.le
    (by linarith : ε / 2 < ε) hgeometryΛ
  have htruncΓcompact := truncΓ.isCompact_quotient
  have htruncΛcompact := truncΛ.isCompact_quotient
  have hhorospheresΓ (ξ : truncΓ.centers) (c : ℝ) :=
    CuspCrossSections.exists_compact_horosphere_core h1 (by omega) Γ disc_Γ covol_Γ
      hhalf (by linarith : ε / 2 < ε) hgeometryΓ (truncΓ.region_nonempty ξ) c
  have hhorospheresΛ (ξ : truncΛ.centers) (c : ℝ) :=
    CuspCrossSections.exists_compact_horosphere_core h1 (by omega) Λ disc_Λ covol_Λ
      hhalf (by linarith : ε / 2 < ε) hgeometryΛ (truncΛ.region_nonempty ξ) c
  have hhoroballsΓ (ξ : truncΓ.centers) (γ : Γ) := truncΓ.precisely_invariant disc_Γ ξ γ
  have hhoroballsΛ (ξ : truncΛ.centers) (γ : Λ) := truncΛ.precisely_invariant disc_Λ ξ γ
  obtain ⟨matched⟩ := MatchedCusps.exists_matched_truncation h1 hn Γ Λ disc_Γ disc_Λ
    covol_Γ covol_Λ hhalf (by linarith : ε / 2 < ε) hgeometryΓ hgeometryΛ truncΓ truncΛ f
  have hmatchedSourceCompact := matched.source.isCompact_quotient
  have hmatchedTargetCompact := matched.target.isCompact_quotient
  have hmatchedSourceNonempty := matched.source.core_nonempty (by omega) disc_Γ hhalf.le
    (by linarith : ε / 2 < ε) hgeometryΓ
  have hmatchedTargetNonempty := matched.target.core_nonempty (by omega) disc_Λ hhalf.le
    (by linarith : ε / 2 < ε) hgeometryΛ
  have hmatchedHoroballs (ξ : matched.source.centers) := matched.image_horoball ξ
  have hmatchedOverlap := matched.compatible_on_overlap disc_Γ
  have hlocalUniform (ξ : matched.source.centers) := (matched.cuspMap ξ).uniform_toFun
  have hlocalInverseUniform (ξ : matched.source.centers) := (matched.cuspMap ξ).uniform_invFun
  have hlocalMetric (ξ : matched.source.centers) := (matched.cuspMap ξ).forward_bound
  have hlocalInverseMetric (ξ : matched.source.centers) := (matched.cuspMap ξ).inverse_bound
  have hlocalCoarseInverse (ξ : matched.source.centers) := (matched.cuspMap ξ).coarse_inverse_bounds
  have hproperΓ : ∀ Φ : HUpper n → HUpper n, UniformContinuous Φ →
      PseudoIsometry.IsFEquivariant f h1 Φ → IsProperMap Φ :=
    fun _ hΦ heq => EquivariantProperness.isProperMap_of_uniformContinuous_equivariant
      h1 Γ Λ disc_Γ disc_Λ covol_Γ f hΦ heq
  have hproperΛ : ∀ Ψ : HUpper n → HUpper n, UniformContinuous Ψ →
      PseudoIsometry.IsFEquivariant f.symm h1 Ψ → IsProperMap Ψ :=
    fun _ hΨ heq => EquivariantProperness.isProperMap_of_uniformContinuous_equivariant
      h1 Λ Γ disc_Λ disc_Γ covol_Λ f.symm hΨ heq
  obtain ⟨Φ, K, C, φ, hΦuniform, hΦmetric, hΦequivariant,
      hφdistortion, hφinverseDistortion, hφequivariant, hφconverges⟩ :=
    CuspCoarseMaps.exists_equivariant_controlled_boundary_extension matched disc_Γ disc_Λ
      (by linarith : ε / 2 < ε) hgeometryΓ hgeometryΛ
  have hΦproper := hproperΓ Φ hΦuniform hΦequivariant
  have hφlocal := BoundaryQuasiconformal.hasLocalMetricDistortion_of_crossRatioControl
    φ hφdistortion
  have hφinverseLocal := BoundaryQuasiconformal.hasLocalMetricDistortion_of_crossRatioControl
    φ.symm hφinverseDistortion
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  let : MulAction (PO (m + 1) 1) (BoundaryH (m + 1)) := poBoundaryMulAction (by omega)
  obtain ⟨μGeoΓ, hμGeoΓprob, hμGeoΓflow, hμGeoΓergodic, hμGeoΓnull⟩ :=
    GeodesicErgodicity.exists_ergodic_probability (by omega : 1 ≤ m) Γ disc_Γ covol_Γ
  obtain ⟨μGeoΛ, hμGeoΛprob, hμGeoΛflow, hμGeoΛergodic, hμGeoΛnull⟩ :=
    GeodesicErgodicity.exists_ergodic_probability (by omega : 1 ≤ m) Λ disc_Λ covol_Λ
  let μBoundaryPair := (BoundaryMeasure.boundaryMeasure m).prod (BoundaryMeasure.boundaryMeasure m)
  have hboundaryPairΓ (U : Set (BoundaryPairErgodicity.BoundaryPair m)) (hU : MeasurableSet U)
      (hInv : ∀ γ : Γ, (fun p : BoundaryPairErgodicity.BoundaryPair m =>
        (γ : PO (m + 1) 1) • p) ⁻¹' U =ᵐ[μBoundaryPair] U) :
      μBoundaryPair U = 0 ∨ μBoundaryPair Uᶜ = 0 :=
    BoundaryPairErgodicity.null_or_conull_of_ae_invariant Γ μGeoΓ hμGeoΓnull hμGeoΓergodic hU hInv
  have hboundaryPairΛ (U : Set (BoundaryPairErgodicity.BoundaryPair m)) (hU : MeasurableSet U)
      (hInv : ∀ γ : Λ, (fun p : BoundaryPairErgodicity.BoundaryPair m =>
        (γ : PO (m + 1) 1) • p) ⁻¹' U =ᵐ[μBoundaryPair] U) :
      μBoundaryPair U = 0 ∨ μBoundaryPair Uᶜ = 0 :=
    BoundaryPairErgodicity.null_or_conull_of_ae_invariant Λ μGeoΛ hμGeoΛnull hμGeoΛergodic hU hInv
  obtain ⟨a, F, haInfinity, hFchart, hFglobal, hFinverseGlobal⟩ :=
    EuclideanBoundary.exists_normalized_chart_with_globalDistortion
      φ hφdistortion hφinverseDistortion
  have hFlocal := hFglobal.local
  have hFinverseLocal := hFinverseGlobal.local
  have hFdiff : ∀ᵐ x ∂(volume : Measure (Horospherical.Horizontal m)),
      DifferentiableAt ℝ F x :=
    MetricDifferentiability.ae_differentiableAt volume F hFlocal
  have hFinverseDiff : ∀ᵐ x ∂(volume : Measure (Horospherical.Horizontal m)),
      DifferentiableAt ℝ F.symm x :=
    MetricDifferentiability.ae_differentiableAt volume F.symm hFinverseLocal
  have hFrank : ∀ᵐ x ∂(volume : Measure (Horospherical.Horizontal m)),
      fderiv ℝ F x = 0 ∨ Function.Injective (fderiv ℝ F x) :=
    hFdiff.mono fun _ hx => MetricDifferentiability.derivative_zero_or_injective hFlocal hx.hasFDerivAt
  have hFinverseRank : ∀ᵐ x ∂(volume : Measure (Horospherical.Horizontal m)),
      fderiv ℝ F.symm x = 0 ∨ Function.Injective (fderiv ℝ F.symm x) :=
    hFinverseDiff.mono fun _ hx =>
      MetricDifferentiability.derivative_zero_or_injective hFinverseLocal hx.hasFDerivAt
  have hFzeroImage : volume (F '' {x | DifferentiableAt ℝ F x ∧ fderiv ℝ F x = 0}) = 0 :=
    MetricDifferentiability.image_zero_derivative_null volume F
  have hFinverseZeroImage :
      volume (F.symm '' {x | DifferentiableAt ℝ F.symm x ∧ fderiv ℝ F.symm x = 0}) = 0 :=
    MetricDifferentiability.image_zero_derivative_null volume F.symm
  let : Nonempty (Fin (m - 1)) := ⟨⟨0, by omega⟩⟩
  have hFACL (e : ((Fin (m - 1) → ℝ) × ℝ) ≃L[ℝ] Horospherical.Horizontal m) :
      ∀ᵐ z ∂(volume : Measure (Fin (m - 1) → ℝ)), ∀ u v : ℝ,
        AbsolutelyContinuousOnInterval (fun t => F (e (z, t))) u v :=
    QuasiconformalACL.ae_absolutelyContinuousOn_linear_coordinates
      ((volume : Measure (Fin (m - 1) → ℝ)).prod volume) volume e F hFglobal
  have hFinverseACL (e : ((Fin (m - 1) → ℝ) × ℝ) ≃L[ℝ] Horospherical.Horizontal m) :
      ∀ᵐ z ∂(volume : Measure (Fin (m - 1) → ℝ)), ∀ u v : ℝ,
        AbsolutelyContinuousOnInterval (fun t => F.symm (e (z, t))) u v :=
    QuasiconformalACL.ae_absolutelyContinuousOn_linear_coordinates
      ((volume : Measure (Fin (m - 1) → ℝ)).prod volume) volume e F.symm hFinverseGlobal
  have hboundaryDim : 2 ≤ Module.finrank ℝ (Horospherical.Horizontal m) := by
    simpa only [Horospherical.Horizontal, finrank_euclideanSpace_fin] using
      (show 2 ≤ m by omega)
  have hFN (s : Set (Horospherical.Horizontal m)) (hs : volume s = 0) :
      volume (F '' s) = 0 :=
    MetricDifferentiability.HasGlobalDistortion.image_null volume F hFglobal hboundaryDim hs
  have hFinverseN (s : Set (Horospherical.Horizontal m)) (hs : volume s = 0) :
      volume (F.symm '' s) = 0 :=
    MetricDifferentiability.HasGlobalDistortion.image_null
      volume F.symm hFinverseGlobal hboundaryDim hs
  have hFzeroNull : volume {x | DifferentiableAt ℝ F x ∧ fderiv ℝ F x = 0} = 0 := by
    have h := hFinverseN _ hFzeroImage
    simpa only [Set.image_image, Homeomorph.symm_apply_apply, Set.image_id'] using h
  have hFinverseZeroNull :
      volume {x | DifferentiableAt ℝ F.symm x ∧ fderiv ℝ F.symm x = 0} = 0 := by
    have h := hFN _ hFinverseZeroImage
    simpa only [Set.image_image, Homeomorph.apply_symm_apply, Set.image_id'] using h
  have hFinjective : ∀ᵐ x ∂(volume : Measure (Horospherical.Horizontal m)),
      Function.Injective (fderiv ℝ F x) := by
    filter_upwards [hFdiff, hFrank, measure_eq_zero_iff_ae_notMem.mp hFzeroNull]
      with x hx hrank hnonzero
    exact hrank.resolve_left (fun hzero => hnonzero ⟨hx, hzero⟩)
  have hFinverseInjective : ∀ᵐ x ∂(volume : Measure (Horospherical.Horizontal m)),
      Function.Injective (fderiv ℝ F.symm x) := by
    filter_upwards [hFinverseDiff, hFinverseRank,
      measure_eq_zero_iff_ae_notMem.mp hFinverseZeroNull] with x hx hrank hnonzero
    exact hrank.resolve_left (fun hzero => hnonzero ⟨hx, hzero⟩)
  have hFmap : Measure.QuasiMeasurePreserving F volume volume :=
    MetricDifferentiability.quasiMeasurePreserving_symm_of_image_null volume F.symm hFinverseN
  have hFinverseMap : Measure.QuasiMeasurePreserving F.symm volume volume :=
    MetricDifferentiability.quasiMeasurePreserving_symm_of_image_null volume F hFN
  have hFderivativeInverse := MetricDifferentiability.ae_inverse_fderiv_comp
    volume F hFmap hFdiff hFinverseDiff
  have hFinverseDerivativeInverse := MetricDifferentiability.ae_inverse_fderiv_comp
    volume F.symm hFinverseMap hFinverseDiff hFdiff
  have hFeccentricityMeasurable := DerivativeEccentricity.measurable_chartEccentricity F
  have hFinverseEccentricityMeasurable :=
    DerivativeEccentricity.measurable_chartEccentricity F.symm
  obtain ⟨HF, hHFpos, hFeccentricityBounds⟩ :=
    DerivativeEccentricity.ae_chartEccentricity_bounds
      volume F hFlocal hFdiff hFderivativeInverse
  obtain ⟨HFinverse, hHFinversePos, hFinverseEccentricityBounds⟩ :=
    DerivativeEccentricity.ae_chartEccentricity_bounds
      volume F.symm hFinverseLocal hFinverseDiff hFinverseDerivativeInverse
  have hFeccentricityConformal := DerivativeEccentricity.ae_chartEccentricity_eq_one_iff
    volume F hFderivativeInverse
  have hFinverseEccentricityConformal := DerivativeEccentricity.ae_chartEccentricity_eq_one_iff
    volume F.symm hFinverseDerivativeInverse
  let ψ : BoundaryH (m + 1) → BoundaryH (m + 1) := fun v => a • φ v
  have hψchart (x : Horospherical.Horizontal m) : EuclideanBoundary.embed (F x) =
      ψ (EuclideanBoundary.embed x) := hFchart x
  have hψequivariant (γ : Γ) (v : BoundaryH (m + 1)) :
      ψ ((γ : PO (m + 1) 1) • v) = (a * (f γ : PO (m + 1) 1) * a⁻¹) • ψ v := by
    have he : φ ((γ : PO (m + 1) 1) • v) = (f γ : PO (m + 1) 1) • φ v :=
      hφequivariant γ v
    change a • φ ((γ : PO (m + 1) 1) • v) =
      (a * (f γ : PO (m + 1) 1) * a⁻¹) • (a • φ v)
    rw [he]
    simp only [mul_smul, inv_smul_smul]
  have hFderivativeEquivariant (γ : Γ) :=
    BoundaryChartAction.ae_fderiv_conjugacy (γ : PO (m + 1) 1)
      (a * (f γ : PO (m + 1) 1) * a⁻¹) ψ F hψchart (hψequivariant γ) hFdiff
  have hFderivativeEquivariantAll := ae_all_iff.mpr hFderivativeEquivariant
  have hFeccentricityInvariant (γ : Γ) :=
    BoundaryChartConformal.ae_chartEccentricity_conjugacy (γ : PO (m + 1) 1)
      (a * (f γ : PO (m + 1) 1) * a⁻¹) ψ F hψchart (hψequivariant γ)
      hFdiff hFderivativeInverse
  have hFeccentricityInvariantAll := ae_all_iff.mpr hFeccentricityInvariant
  have hFtensorMeasurable := NormalizedDerivative.measurable_chartTensor (F : _ → _)
  have hFnonzero : ∀ᵐ x ∂(volume : Measure (Horospherical.Horizontal m)), fderiv ℝ F x ≠ 0 := by
    filter_upwards [hFderivativeInverse] with x hx
    intro hz
    have he := hx.1
    rw [hz, ContinuousLinearMap.comp_zero] at he
    have heNorm := congrArg norm he
    exact zero_ne_one (by simpa only [norm_zero, ContinuousLinearMap.norm_id] using heNorm)
  have hFtensorNorm := hFnonzero.mono
    (fun _ hx => NormalizedDerivative.norm_normalizedTensor _ hx)
  have hFtensorConformal := hFnonzero.mono
    (fun _ hx => NormalizedDerivative.normalizedTensor_eq_id_iff _ hx)
  have hFtensorEquivariant (γ : Γ) :=
    NormalizedDerivative.ae_normalizedTensor_conjugacy (γ : PO (m + 1) 1)
      (a * (f γ : PO (m + 1) 1) * a⁻¹) ψ F hψchart (hψequivariant γ) hFdiff
  have hFtensorEquivariantAll := ae_all_iff.mpr hFtensorEquivariant
  have hFframeMap : Measure.QuasiMeasurePreserving
      (fun g : PO (m + 1) 1 =>
        EuclideanBoundary.coords (g • EuclideanBoundary.embed (0 : Horospherical.Horizontal m)))
      volume volume :=
    BoundaryChartAction.measurePreserving_coords.quasiMeasurePreserving.comp
      (BoundaryMeasure.quasiMeasurePreserving_orbit _)
  have hFframeDiff := hFframeMap.ae hFdiff
  have hFframeInjective := hFframeMap.ae hFinjective
  have hFframeDerivativeInverse := hFframeMap.ae hFderivativeInverse
  have hFtensorHaarMeasurable := hFtensorMeasurable.comp hFframeMap.measurable
  have hFframeFinite : ∀ᵐ g ∂(volume : Measure (PO (m + 1) 1)),
      (0 : Horospherical.Horizontal m) ∈ BoundaryChartAction.chartDomain g := by
    have h := BoundaryMeasure.haar_orbit_infty_null
      (EuclideanBoundary.embed (0 : Horospherical.Horizontal m))
    simpa only [ae_iff, BoundaryChartAction.chartDomain, Set.mem_ofPred_eq, not_not] using h
  have hFmovingMeasurable := MovingFrameTensor.measurable_frameTensor (F : _ → _)
  have hFmovingNorm := MovingFrameTensor.ae_norm_frameTensor (F : _ → _) hFnonzero
  have hFmovingInvariant (γ : Γ) :=
    MovingFrameTensor.ae_frameTensor_left (γ : PO (m + 1) 1)
      (a * (f γ : PO (m + 1) 1) * a⁻¹) ψ F hψchart (hψequivariant γ) hFdiff
  obtain ⟨Tq, hTqMeasurable, hTqRepresentative⟩ :=
    MovingFrameTensor.exists_quotient_tensor Γ F hFmovingInvariant
  let : SecondCountableTopology
      (Horospherical.Horizontal m →L[ℝ] Horospherical.Horizontal m) :=
    instSecondCountableTopologyContinuousLinearMapIdOfFiniteDimensional
  let : MeasurableSpace.CountablyGenerated
      (Horospherical.Horizontal m →L[ℝ] Horospherical.Horizontal m) :=
    BorelSpace.countablyGenerated
  let : IsProbabilityMeasure νΓ := hνΓprob
  have hTqFlow (t : ℝ) :
      (fun q => Tq (DifferentialGeometry.HomogeneousSpaceMeasure.right Γ (GeodesicFlow.diagonal t) q)) =ᵐ[νΓ] Tq :=
    (FrameTensorDynamics.quotient_right_invariance_iff Γ volume νΓ hνΓnull
      Tq hTqMeasurable (MovingFrameTensor.frameTensor F) hTqRepresentative _).mpr
        (Filter.Eventually.of_forall (fun g => MovingFrameTensor.frameTensor_right_diagonal F g t))
  let H := FrameTensorDynamics.rightFieldStabilizer Γ νΓ hνΓright Tq
  have hHT (b : Fin m → ℝ) : LorentzGenerators.translation b ∈ H :=
    FrameTensorDynamics.translation_mem_rightFieldStabilizer (by omega)
      Γ disc_Γ νΓ hνΓright Tq hTqMeasurable hTqFlow b
  have hHO (b : Fin m → ℝ) : LorentzGenerators.oppositeTranslation b ∈ H :=
    FrameTensorDynamics.oppositeTranslation_mem_rightFieldStabilizer (by omega)
      Γ disc_Γ νΓ hνΓright Tq hTqMeasurable hTqFlow b
  have hHhaar (h : PO (m + 1) 1) (hh : h ∈ H) :
      (fun g => MovingFrameTensor.frameTensor F (g * h)) =ᵐ[volume]
        MovingFrameTensor.frameTensor F :=
    (FrameTensorDynamics.quotient_right_invariance_iff Γ volume νΓ hνΓnull
      Tq hTqMeasurable (MovingFrameTensor.frameTensor F) hTqRepresentative h).mp hh
  have hFmovingIdentity := FrameTensorIsotropy.ae_frameTensor_eq_id_of_horospherical
    (F : _ → _) hFnonzero H hHT hHO hHhaar
  have hFchartIdentity := FrameTensorIsotropy.ae_chartTensor_eq_id_of_frameTensor
    (F : _ → _) hFnonzero hFmovingIdentity
  have hFconformal : ∀ᵐ x ∂(volume : Measure (Horospherical.Horizontal m)),
      IsConformalMap (fderiv ℝ F x) := by
    filter_upwards [hFchartIdentity, hFtensorConformal] with x hx hc
    exact hc.mp hx
  let ψH : BoundaryH (m + 1) ≃ₜ BoundaryH (m + 1) :=
    φ.trans (EuclideanBoundary.actionHomeomorph (by omega) a)
  have hψH (v : BoundaryH (m + 1)) : ψH v = ψ v :=
    EuclideanBoundary.actionHomeomorph_apply (by omega) a (φ v)
  have hψHchart (x : Horospherical.Horizontal m) :
      EuclideanBoundary.embed (F x) = ψH (EuclideanBoundary.embed x) := by
    rw [hψH]
    exact hψchart x
  have hψHequivariant (γ : Γ) (v : BoundaryH (m + 1)) :
      ψH ((γ : PO (m + 1) 1) • v) =
        (a * (f γ : PO (m + 1) 1) * a⁻¹) • ψH v := by
    rw [hψH, hψH]
    exact hψequivariant γ v
  obtain ⟨b, hb⟩ := RecurrentBoundaryRigidity.exists_mobius_of_ae_conformal (by omega)
    Γ disc_Γ νΓ hνΓright hνΓnull ψH (fun γ => a * (f γ : PO (m + 1) 1) * a⁻¹)
      F hψHchart hψHequivariant hFdiff hFconformal
  refine ⟨Φ, K, C, hΦmetric, hΦequivariant, φ, hφequivariant,
    ⟨a⁻¹ * b, ?_⟩, hφconverges⟩
  intro ξ
  have he := congrArg (fun v : BoundaryH (m + 1) => a⁻¹ • v) (hb ξ)
  rw [hψH] at he
  change a⁻¹ • (a • φ ξ) = a⁻¹ • (b • ξ) at he
  change φ ξ = (a⁻¹ * b) • ξ
  simpa only [inv_smul_smul, mul_smul] using he

theorem exists_equivariant_mobius_boundary_homeomorph (hn : 3 ≤ n) (Γ Λ : Subgroup (PO n 1))
    (disc_Γ : IsDiscrete (SetLike.coe Γ)) (disc_Λ : IsDiscrete (SetLike.coe Λ))
    [HasFundamentalDomain Γ (PO n 1)] [HasFundamentalDomain Λ (PO n 1)]
    (hΓ : Countable ↥Γ) (hΛ : Countable ↥Λ)
    (hΓinf : Infinite ↥Γ) (hΛinf : Infinite ↥Λ)
    (covol_Γ : covolume Γ (PO n 1) ≠ ⊤) (hcovΓ : covolume Γ (PO n 1) ≠ 0)
    (covol_Λ : covolume Λ (PO n 1) ≠ ⊤) (hcovΛ : covolume Λ (PO n 1) ≠ 0)
    (f : Γ ≃* Λ) :
    ∃ φ : BoundaryH n ≃ₜ BoundaryH n,
      (∀ (γ : Γ) (ξ : BoundaryH n),
        φ ((poBoundaryMulAction (by omega : 1 ≤ n)).smul (γ : PO n 1) ξ)
          = (poBoundaryMulAction (by omega : 1 ≤ n)).smul (f γ : PO n 1) (φ ξ))
      ∧ ∃ g : PO n 1, ∀ ξ : BoundaryH n,
        φ ξ = (poBoundaryMulAction (by omega : 1 ≤ n)).smul g ξ := by
  obtain ⟨Φ, K, C, _hPI, _hFE, φ, heq, ⟨g, hg⟩, _hext⟩ :=
    exists_equivariant_pseudoIsometry_mobius_boundary hn Γ Λ disc_Γ disc_Λ hΓ hΛ
      hΓinf hΛinf covol_Γ hcovΓ covol_Λ hcovΛ f
  exact ⟨φ, heq, g, hg⟩

theorem exists_conj_of_equivariant_mobius_boundary (hn : 3 ≤ n) {Γ Λ : Subgroup (PO n 1)} (f : Γ ≃* Λ)
    (hcore : ∃ φ : BoundaryH n ≃ₜ BoundaryH n,
      (∀ (γ : Γ) (ξ : BoundaryH n),
        φ ((poBoundaryMulAction (by omega : 1 ≤ n)).smul (γ : PO n 1) ξ)
          = (poBoundaryMulAction (by omega : 1 ≤ n)).smul (f γ : PO n 1) (φ ξ))
      ∧ ∃ g : PO n 1, ∀ ξ : BoundaryH n,
        φ ξ = (poBoundaryMulAction (by omega : 1 ≤ n)).smul g ξ) :
    ∃ g : PO n 1, ∀ γ : Γ, (f γ : PO n 1) = g * γ * g⁻¹ := by
  obtain ⟨φ, heq, g, hg⟩ := hcore
  have h1 : (1 : ℕ) ≤ n := by omega
  have h2 : 2 ≤ n := by omega
  let := poBoundaryMulAction h1
  refine ⟨g, fun γ => ?_⟩
  have heq' : ∀ (γ : Γ) (ξ : BoundaryH n), φ ((γ : PO n 1) • ξ) = (f γ : PO n 1) • φ ξ :=
    fun γ ξ => heq γ ξ
  have hg' : ∀ ξ : BoundaryH n, φ ξ = g • ξ := fun ξ => hg ξ
  have key : ∀ ξ : BoundaryH n, ((f γ : PO n 1) * g) • ξ = (g * (γ : PO n 1)) • ξ := by
    intro ξ
    rw [mul_smul, mul_smul, ← hg' ξ, ← heq' γ ξ, ← hg' ((γ : PO n 1) • ξ)]
  have hab : (f γ : PO n 1) * g = g * (γ : PO n 1) :=
    eq_of_po_boundary_smul_eq h2 key
  rw [eq_mul_inv_iff_mul_eq]
  exact hab

theorem exists_equivariant_mobius_boundary_of_conj (hn : 3 ≤ n) {Γ Λ : Subgroup (PO n 1)} (f : Γ ≃* Λ)
    (h : ∃ g : PO n 1, ∀ γ : Γ, (f γ : PO n 1) = g * γ * g⁻¹) :
    ∃ φ : BoundaryH n ≃ₜ BoundaryH n,
      (∀ (γ : Γ) (ξ : BoundaryH n),
        φ ((poBoundaryMulAction (by omega : 1 ≤ n)).smul (γ : PO n 1) ξ)
          = (poBoundaryMulAction (by omega : 1 ≤ n)).smul (f γ : PO n 1) (φ ξ))
      ∧ ∃ g : PO n 1, ∀ ξ : BoundaryH n,
        φ ξ = (poBoundaryMulAction (by omega : 1 ≤ n)).smul g ξ := by
  obtain ⟨g, hg⟩ := h
  have h1 : (1 : ℕ) ≤ n := by omega
  let := poBoundaryMulAction h1
  obtain ⟨φ, hφ⟩ := po_boundary_homeomorph h1 g
  have hφ' : ∀ v : BoundaryH n, φ v = g • v := fun v => hφ v
  refine ⟨φ, ?_, g, hφ⟩
  intro γ ξ
  change φ ((γ : PO n 1) • ξ) = (f γ : PO n 1) • φ ξ
  rw [hφ', hφ', ← mul_smul, ← mul_smul, hg γ]
  have hgg : (g * (γ : PO n 1) * g⁻¹) * g = g * (γ : PO n 1) := by group
  rw [hgg]

theorem exists_equivariant_mobius_boundary_iff_exists_conj (hn : 3 ≤ n) {Γ Λ : Subgroup (PO n 1)} (f : Γ ≃* Λ) :
    (∃ φ : BoundaryH n ≃ₜ BoundaryH n,
      (∀ (γ : Γ) (ξ : BoundaryH n),
        φ ((poBoundaryMulAction (by omega : 1 ≤ n)).smul (γ : PO n 1) ξ)
          = (poBoundaryMulAction (by omega : 1 ≤ n)).smul (f γ : PO n 1) (φ ξ))
      ∧ ∃ g : PO n 1, ∀ ξ : BoundaryH n,
        φ ξ = (poBoundaryMulAction (by omega : 1 ≤ n)).smul g ξ)
    ↔ (∃ g : PO n 1, ∀ γ : Γ, (f γ : PO n 1) = g * γ * g⁻¹) :=
  ⟨exists_conj_of_equivariant_mobius_boundary hn f, exists_equivariant_mobius_boundary_of_conj hn f⟩

theorem exists_conj_of_actsCocompactly_of_boundary_rigidity
    (hn : 3 ≤ n) (Γ Λ : Subgroup (PO n 1))
    (disc_Γ : IsDiscrete (SetLike.coe Γ)) (disc_Λ : IsDiscrete (SetLike.coe Λ))
    (hcoΓ : UniformPseudoIsometry.ActsCocompactly (by omega : 1 ≤ n) Γ)
    (hcoΛ : UniformPseudoIsometry.ActsCocompactly (by omega : 1 ≤ n) Λ)
    (f : Γ ≃* Λ)
    (hmob : ∀ (φ : BoundaryH n ≃ₜ BoundaryH n),
      (∀ (γ : Γ) (ξ : BoundaryH n),
        φ ((poBoundaryMulAction (by omega : 1 ≤ n)).smul (γ : PO n 1) ξ)
          = (poBoundaryMulAction (by omega : 1 ≤ n)).smul (f γ : PO n 1) (φ ξ)) →
      ∃ g : PO n 1, ∀ ξ : BoundaryH n,
        φ ξ = (poBoundaryMulAction (by omega : 1 ≤ n)).smul g ξ) :
    ∃ g : PO n 1, ∀ γ : Γ, (f γ : PO n 1) = g * γ * g⁻¹ := by
  have h1 : (1 : ℕ) ≤ n := by omega
  obtain ⟨Φ, K, C, φ, hPI, hFE, hφeq, hφconv⟩ :=
    exists_equivariant_homeomorph_boundary_extension_of_uniform hn Γ Λ disc_Γ disc_Λ
      hcoΓ hcoΛ f
  exact exists_conj_of_equivariant_mobius_boundary hn f ⟨φ, hφeq, hmob φ hφeq⟩

theorem exists_conj_of_equivariant_smoothConformal_boundary (n : ℕ) (hn : 4 ≤ n)
    (Γ Λ : Subgroup (PO n 1)) (f : Γ ≃* Λ)
    (φ : BoundaryH n ≃ₜ BoundaryH n)
    (hequiv : ∀ (γ : Γ) (ξ : BoundaryH n),
      φ ((poBoundaryMulAction (by omega : 1 ≤ n)).smul (γ : PO n 1) ξ)
        = (poBoundaryMulAction (by omega : 1 ≤ n)).smul (f γ : PO n 1) (φ ξ))
    (F : LiouvilleRigidity.ES (n - 1) → LiouvilleRigidity.ES (n - 1)) (hF : ContDiff ℝ 3 F)
    (hconf : ∀ x, IsConformalMap (fderiv ℝ F x))
    (hφF : ∀ x : Fin (n-1) → ℝ,
      φ ((DifferentialGeometry.LiouvilleBoundary.boundaryHCongr (by omega : (n-1)+1 = n)) (MobiusBoundary.horo x))
        = (DifferentialGeometry.LiouvilleBoundary.boundaryHCongr (by omega : (n-1)+1 = n))
            (MobiusBoundary.horo
              (DifferentialGeometry.LiouvilleBoundary.eucEquiv (F (DifferentialGeometry.LiouvilleBoundary.eucEquiv.symm x))))) :
    ∃ g : PO n 1, ∀ γ : Γ, (f γ : PO n 1) = g * γ * g⁻¹ := by
  obtain ⟨g, hg⟩ :=
    DifferentialGeometry.LiouvilleBoundary.mobius_boundary_of_smoothConformal_dim hn φ F hF hconf hφF
  exact exists_conj_of_equivariant_mobius_boundary (by omega : 3 ≤ n) f ⟨φ, hequiv, g, hg⟩

end DifferentialGeometry.MostowRigidity
