import DifferentialGeometry.Topology.PiecewiseLinear.EulerCellOperations
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceHomology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def surfaceHandleCrosscapProfile (h m : ℕ) : OpenCellProfile where
  vertices := 1
  edges := 2 * h + m
  faces := 1

theorem surfaceHandleCrosscapProfile_eulerChar (h m : ℕ) :
    (surfaceHandleCrosscapProfile h m).eulerChar = 2 - ((2 * h + m : ℕ) : ℤ) := by
  simp [surfaceHandleCrosscapProfile, OpenCellProfile.eulerChar]
  omega

theorem eulerChar_eq_two_sub_handle_crosscap_count
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hd : ∀ s ∈ K.faces, s.card ≤ 3) (h m : ℕ)
    (hrefine : OpenCellProfile.IsRefinement
      (simplicialOpenCellProfile K) (surfaceHandleCrosscapProfile h m)) :
    eulerChar K = 2 - ((2 * h + m : ℕ) : ℤ) := by
  rw [← simplicialOpenCellProfile_eulerChar K hd]
  exact (OpenCellProfile.eulerChar_eq_of_isRefinement hrefine).trans
    (surfaceHandleCrosscapProfile_eulerChar h m)

open Classical in
theorem IsCombinatorialManifold.bettiOne_eq_two_mul_of_isOrientable_of_eulerChar_eq
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : _root_.IsConnected K.space)
    (ho : IsOrientable 2 K) (h : ℕ)
    (hEuler : eulerChar K = 2 - 2 * (h : ℤ)) :
    Homology.bettiOne K.space = 2 * h := by
  have hformula := hK.eulerChar_eq_two_sub_bettiOne_of_isOrientable K hconn ho
  have hcast : (Homology.bettiOne K.space : ℤ) = 2 * (h : ℤ) := by omega
  exact_mod_cast hcast

open Classical in
theorem IsCombinatorialManifold.bettiOne_eq_two_mul_of_one_crosscap
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : _root_.IsConnected K.space)
    (ho : ¬ IsOrientable 2 K) (h : ℕ)
    (hEuler : eulerChar K = 2 - (2 * (h : ℤ) + 1)) :
    Homology.bettiOne K.space = 2 * h := by
  have hformula := hK.eulerChar_eq_one_sub_bettiOne_of_not_isOrientable K hconn ho
  have hcast : (Homology.bettiOne K.space : ℤ) = 2 * (h : ℤ) := by omega
  exact_mod_cast hcast

open Classical in
theorem IsCombinatorialManifold.bettiOne_eq_two_mul_add_one_of_two_crosscaps
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : _root_.IsConnected K.space)
    (ho : ¬ IsOrientable 2 K) (h : ℕ)
    (hEuler : eulerChar K = 2 - (2 * (h : ℤ) + 2)) :
    Homology.bettiOne K.space = 2 * h + 1 := by
  have hformula := hK.eulerChar_eq_one_sub_bettiOne_of_not_isOrientable K hconn ho
  have hcast : (Homology.bettiOne K.space : ℤ) = 2 * (h : ℤ) + 1 := by omega
  exact_mod_cast hcast

noncomputable def surfaceHandleNumber
    (K : Geometry.SimplicialComplex ℝ E) : ℕ :=
  Homology.bettiOne K.space / 2

open Classical in
theorem IsCombinatorialManifold.surfaceHandleNumber_eq_of_isOrientable_of_eulerChar_eq
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : _root_.IsConnected K.space)
    (ho : IsOrientable 2 K) (h : ℕ)
    (hEuler : eulerChar K = 2 - 2 * (h : ℤ)) :
    surfaceHandleNumber K = h := by
  rw [surfaceHandleNumber,
    hK.bettiOne_eq_two_mul_of_isOrientable_of_eulerChar_eq K hconn ho h hEuler]
  omega

open Classical in
theorem IsCombinatorialManifold.even_bettiOne_of_isOrientable_of_eulerChar_eq
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : _root_.IsConnected K.space)
    (ho : IsOrientable 2 K) (h : ℕ)
    (hEuler : eulerChar K = 2 - 2 * (h : ℤ)) :
    Even (Homology.bettiOne K.space) := by
  rw [hK.bettiOne_eq_two_mul_of_isOrientable_of_eulerChar_eq K hconn ho h hEuler]
  exact ⟨h, by omega⟩

open Classical in
theorem IsCombinatorialManifold.bettiOne_eq_two_mul_of_isOrientable_of_handle_profile
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : _root_.IsConnected K.space)
    (ho : IsOrientable 2 K) (h : ℕ)
    (hrefine : OpenCellProfile.IsRefinement
      (simplicialOpenCellProfile K) (surfaceHandleCrosscapProfile h 0)) :
    Homology.bettiOne K.space = 2 * h := by
  apply hK.bettiOne_eq_two_mul_of_isOrientable_of_eulerChar_eq K hconn ho h
  have hEuler := eulerChar_eq_two_sub_handle_crosscap_count K
    (fun s hs => hK.card_le K hs) h 0 hrefine
  simpa using hEuler

open Classical in
theorem IsCombinatorialManifold.bettiOne_eq_two_mul_of_one_crosscap_profile
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : _root_.IsConnected K.space)
    (ho : ¬ IsOrientable 2 K) (h : ℕ)
    (hrefine : OpenCellProfile.IsRefinement
      (simplicialOpenCellProfile K) (surfaceHandleCrosscapProfile h 1)) :
    Homology.bettiOne K.space = 2 * h := by
  apply hK.bettiOne_eq_two_mul_of_one_crosscap K hconn ho h
  have hEuler := eulerChar_eq_two_sub_handle_crosscap_count K
    (fun s hs => hK.card_le K hs) h 1 hrefine
  simpa [Nat.cast_add, Nat.cast_mul] using hEuler

open Classical in
theorem IsCombinatorialManifold.bettiOne_eq_two_mul_add_one_of_two_crosscap_profile
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : _root_.IsConnected K.space)
    (ho : ¬ IsOrientable 2 K) (h : ℕ)
    (hrefine : OpenCellProfile.IsRefinement
      (simplicialOpenCellProfile K) (surfaceHandleCrosscapProfile h 2)) :
    Homology.bettiOne K.space = 2 * h + 1 := by
  apply hK.bettiOne_eq_two_mul_add_one_of_two_crosscaps K hconn ho h
  have hEuler := eulerChar_eq_two_sub_handle_crosscap_count K
    (fun s hs => hK.card_le K hs) h 2 hrefine
  simpa [Nat.cast_add, Nat.cast_mul] using hEuler

open Classical in
theorem IsCombinatorialManifold.surfaceHandleNumber_eq_of_isOrientable_of_handle_profile
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : _root_.IsConnected K.space)
    (ho : IsOrientable 2 K) (h : ℕ)
    (hrefine : OpenCellProfile.IsRefinement
      (simplicialOpenCellProfile K) (surfaceHandleCrosscapProfile h 0)) :
    surfaceHandleNumber K = h := by
  apply hK.surfaceHandleNumber_eq_of_isOrientable_of_eulerChar_eq K hconn ho h
  have hEuler := eulerChar_eq_two_sub_handle_crosscap_count K
    (fun s hs => hK.card_le K hs) h 0 hrefine
  simpa using hEuler

open Classical in
theorem IsCombinatorialManifold.even_bettiOne_of_isOrientable_of_handle_profile
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : _root_.IsConnected K.space)
    (ho : IsOrientable 2 K) (h : ℕ)
    (hrefine : OpenCellProfile.IsRefinement
      (simplicialOpenCellProfile K) (surfaceHandleCrosscapProfile h 0)) :
    Even (Homology.bettiOne K.space) := by
  apply hK.even_bettiOne_of_isOrientable_of_eulerChar_eq K hconn ho h
  have hEuler := eulerChar_eq_two_sub_handle_crosscap_count K
    (fun s hs => hK.card_le K hs) h 0 hrefine
  simpa using hEuler

end DifferentialGeometry.Topology.PiecewiseLinear
