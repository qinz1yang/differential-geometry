import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Correspondence
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Truncation

noncomputable section

namespace DifferentialGeometry

open ProjectiveOrthogonalGroup (PO)
open HyperbolicBoundary (BoundaryH poBoundaryMulAction)
open MeasureTheory (HasFundamentalDomain covolume)

namespace CuspCorrespondence

variable {n : ℕ}

abbrev Cusp (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) : Type :=
  letI := poBoundaryMulAction hn
  letI : MulAction Γ (BoundaryH n) := MulAction.compHom _ Γ.subtype
  Quotient ((MulAction.orbitRel Γ (BoundaryH n)).comap
    (Subtype.val : {ξ : BoundaryH n // IsCuspCenter hn Γ ξ} → BoundaryH n))

def Cusp.mk {hn : 1 ≤ n} {Γ : Subgroup (PO n 1)}
    (ξ : {ξ : BoundaryH n // IsCuspCenter hn Γ ξ}) : Cusp hn Γ :=
  Quotient.mk _ ξ

theorem Cusp.mk_eq_mk_iff {hn : 1 ≤ n} {Γ : Subgroup (PO n 1)}
    (ξ η : {ξ : BoundaryH n // IsCuspCenter hn Γ ξ}) :
    Cusp.mk ξ = Cusp.mk η ↔
      ∃ γ : Γ, (poBoundaryMulAction hn).smul (γ : PO n 1) η.val = ξ.val :=
  Quotient.eq

def cuspCount (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) : ℕ∞ :=
  ENat.card (Cusp hn Γ)

end CuspCorrespondence

namespace CuspTruncation.FiniteCuspTruncation

open CuspCorrespondence (Cusp IsCuspCenter cuspCount)

variable {n : ℕ} {hn : 1 ≤ n} {Γ : Subgroup (PO n 1)} {r ε : ℝ}

def cuspEquiv (D : FiniteCuspTruncation hn Γ r) (hdim : 3 ≤ n)
    (hΓ : IsDiscrete (SetLike.coe Γ)) [HasFundamentalDomain Γ (PO n 1)]
    (hcov : covolume Γ (PO n 1) ≠ ⊤) (hr : 0 < r) (hre : r < ε)
    (hgeom : ∀ x : Hyperbolic.HUpper n,
      BoundaryStabilizer.ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x)) :
    D.centers ≃ Cusp hn Γ := by
  let f : D.centers → Cusp hn Γ := fun ξ => Cusp.mk
    ⟨ξ.val, CuspCorrespondence.isCuspCenter_of_thinRegion hn hdim Γ hΓ hcov hr hre hgeom
      (D.region_nonempty ξ)⟩
  apply Equiv.ofBijective f
  constructor
  · intro ξ η h
    obtain ⟨γ, hγ⟩ := (Cusp.mk_eq_mk_iff _ _).mp h
    exact (D.distinct_orbits η ξ γ hγ).symm
  · intro q
    induction q using Quotient.inductionOn with
    | _ ξ =>
      have hξ := ξ.property.thinRegion_nonempty hΓ hr
        (fun x => OrbifoldStrata.closedSmallSubgroup_geometry hn Γ hre x (hgeom x))
      obtain ⟨γ, hγ⟩ := D.covers_centers ξ.val hξ
      refine ⟨⟨(poBoundaryMulAction hn).smul (γ : PO n 1) ξ.val, hγ⟩, ?_⟩
      exact (Cusp.mk_eq_mk_iff _ _).mpr ⟨γ, rfl⟩

@[simp] theorem cuspEquiv_apply (D : FiniteCuspTruncation hn Γ r) (hdim : 3 ≤ n)
    (hΓ : IsDiscrete (SetLike.coe Γ)) [HasFundamentalDomain Γ (PO n 1)]
    (hcov : covolume Γ (PO n 1) ≠ ⊤) (hr : 0 < r) (hre : r < ε)
    (hgeom : ∀ x : Hyperbolic.HUpper n,
      BoundaryStabilizer.ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x))
    (ξ : D.centers) :
    D.cuspEquiv hdim hΓ hcov hr hre hgeom ξ = Cusp.mk
      ⟨ξ.val, CuspCorrespondence.isCuspCenter_of_thinRegion hn hdim Γ hΓ hcov hr hre hgeom
        (D.region_nonempty ξ)⟩ := rfl

theorem cuspCount_eq_ncard_centers (D : FiniteCuspTruncation hn Γ r) (hdim : 3 ≤ n)
    (hΓ : IsDiscrete (SetLike.coe Γ)) [HasFundamentalDomain Γ (PO n 1)]
    (hcov : covolume Γ (PO n 1) ≠ ⊤) (hr : 0 < r) (hre : r < ε)
    (hgeom : ∀ x : Hyperbolic.HUpper n,
      BoundaryStabilizer.ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x)) :
    cuspCount hn Γ = D.centers.ncard := by
  rw [cuspCount, ← ENat.card_congr (D.cuspEquiv hdim hΓ hcov hr hre hgeom),
    ENat.card_coe_set_eq, D.finite_centers.cast_ncard_eq]

theorem ncard_centers_eq {s δ : ℝ}
    (D : FiniteCuspTruncation hn Γ r) (E : FiniteCuspTruncation hn Γ s) (hdim : 3 ≤ n)
    (hΓ : IsDiscrete (SetLike.coe Γ)) [HasFundamentalDomain Γ (PO n 1)]
    (hcov : covolume Γ (PO n 1) ≠ ⊤) (hr : 0 < r) (hs : 0 < s)
    (hre : r < ε) (hsd : s < δ)
    (hgeomε : ∀ x : Hyperbolic.HUpper n,
      BoundaryStabilizer.ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x))
    (hgeomδ : ∀ x : Hyperbolic.HUpper n,
      BoundaryStabilizer.ElementaryGeometry hn (Margulis.smallSubgroup hn Γ δ x)) :
    D.centers.ncard = E.centers.ncard := by
  exact_mod_cast (D.cuspCount_eq_ncard_centers hdim hΓ hcov hr hre hgeomε).symm.trans
    (E.cuspCount_eq_ncard_centers hdim hΓ hcov hs hsd hgeomδ)

end CuspTruncation.FiniteCuspTruncation

namespace CuspCorrespondence

variable {n : ℕ}

theorem finite_cusp (hn : 1 ≤ n) (hdim : 2 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤) :
    Finite (Cusp hn Γ) := by
  obtain ⟨ε, hε, hgeom⟩ := BoundaryStabilizer.exists_margulis_geometry_constant hn
  have hr : 0 < ε / 2 := half_pos hε
  have hre : ε / 2 < ε := half_lt_self hε
  obtain ⟨A, hA, hcover⟩ := OrbifoldThinRegions.exists_finite_parabolic_representatives
    hn hdim Γ hΓ hcov hr hre (hgeom Γ hΓ)
  let B := A ∩ {ξ : BoundaryH n | IsCuspCenter hn Γ ξ}
  let : Finite B := hA.inter_of_left _
  let f : B → Cusp hn Γ := fun ξ => Cusp.mk ⟨ξ.val, ξ.property.2⟩
  apply Finite.of_surjective f
  intro q
  induction q using Quotient.inductionOn with
  | _ ξ =>
    obtain ⟨γ, hγ⟩ := hcover ξ.val ξ.property
    refine ⟨⟨(poBoundaryMulAction hn).smul (γ : PO n 1) ξ.val,
      hγ, ξ.property.smul γ⟩, ?_⟩
    exact (Cusp.mk_eq_mk_iff _ _).mpr ⟨γ, rfl⟩

theorem cuspCount_lt_top (hn : 1 ≤ n) (hdim : 2 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤) :
    cuspCount hn Γ < ⊤ :=
  ENat.card_lt_top.mpr (finite_cusp hn hdim Γ hΓ hcov)

end CuspCorrespondence

end DifferentialGeometry
