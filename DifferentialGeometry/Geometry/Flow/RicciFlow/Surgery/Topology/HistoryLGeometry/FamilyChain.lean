import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.IndexChain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.JacobianUnconditional

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman

universe u

variable {H : ObservedHistory.{u}}

structure LFamilyChain (H : ObservedHistory.{u}) {first last fst : Fin (H.eventCount + 1)}
    (hle : first ≤ last) (hfst : first ≤ fst) (T w v : ℝ) (p : (H.stage last).Carrier)
    (Z₀ : H.historyLExpDomain hle T w p) extends
    H.LWindowChain T v (fun j : H.StageInterval fst last =>
      H.historyLCurve hle T w p Z₀ ⟨j.val, hfst.trans j.property.1, j.property.2⟩) where
  V : ℕ → Set ThreeSpace
  K : ℕ → Set ℝ
  β : (k : ℕ) → ThreeSpace × ℝ → (W k).X
  isOpen_V : ∀ k, IsOpen (V k)
  mem_V : ∀ k, Z₀.1 ∈ V k
  V_sub : ∀ k, ∀ Z ∈ V k, (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T w p
  isOpen_K : ∀ k, IsOpen (K k)
  piece_K : ∀ k < n, Icc (c k) (c (k + 1)) ⊆ K k
  K_W : ∀ k, K k ∩ Ioi 0 ⊆ Ioo (W k).a (W k).b
  smooth : ∀ k, ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ (β k) (V k ×ˢ K k)
  family : ∀ k, ∀ Z ∈ V k, IsLRegularizedGeodesicOn (W k).S T (fun r => β k (Z, r)) (K k)
  curve : ∀ k, ∀ s ∈ K k, β k (Z₀.1, s) = γ k s
  rep : ∀ k, ∀ Z (hZ : Z ∈ V k) (j : H.StageInterval (lo k) (hi k)),
    ∀ r ∈ K k ∩ Ioo (H.regularizedStageStart T (W k).a j.val)
      (H.regularizedStageEnd T (W k).b j.val),
      H.historyLCurve hle T w p ⟨Z, V_sub k Z hZ⟩
        ⟨j.val, hfst.trans ((first_le k).trans j.property.1), j.property.2.trans (le_last k)⟩ r =
        (W k).f j (β k (Z, r))
  base : ∃ (x : (W 0).X) (L : ThreeSpace →L[ℝ] ThreeSpace), Function.Injective L ∧
    ∀ Z ∈ V 0, ∀ s ∈ K 0, s ∈ lRegularizedDomain (W 0).S T x (L Z) ∧
      β 0 (Z, s) = lRegularizedCurve (W 0).S T x (L Z) s

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
