import RicciFlower.Coordinates.Normal

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# GSM245 Lecture 7.3: normal-coordinate front end

The reusable normal-coordinate API now lives in `RicciFlower.Coordinates.Normal`.
This file preserves the old lecture import path and names while the lecture notes
continue to point at the construction.
-/

noncomputable section

namespace RicciFlower
namespace GlobalGeometry
namespace Lecture07

export RicciFlower.Coordinates
  (IsCoordGeodesicOn
   IsCoordGeodesicSegment
   CoordExpRelAtTime
   CoordExpRel
   expAt
   expAt_iff
   expAt_of_segment
   expAt_mem_source
   expAt_zero
   exists_exp_one
   expAt_strict
   exists_coordGeoAt
   coordExp_zero
   exists_coordGeoOn
   exists_coordExpTime
   NormalCoordinateData
   exists_normalData)

end Lecture07
end GlobalGeometry
end RicciFlower
