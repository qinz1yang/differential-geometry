import DifferentialGeometry.Geometry.Hyperbolic.ThickPart
import DifferentialGeometry.Geometry.Hyperbolic.ApproximationThinness

/-!
# Consumer of the G9 intake (S-HG-INTAKE, suffix `_HGI`)

Thick-part compactness of the normalized universal cover deck displacement, and
small volume implies a short deck displacement.
-/

set_option autoImplicit false

open DifferentialGeometry.Geometry.Hyperbolic

example := @isCompact_image_setOf_le_normalized_deck_displacement

example := @exists_deck_displacement_lt_of_small_volume_metric_bounds

example := @exists_deck_displacement_lt_of_small_volume_metric_approximation
