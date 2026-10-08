import Homogenization.Ambient.Euclidean

/-!
# Geometry near a coordinate line

The transverse distance to the first coordinate axis is the Euclidean magnitude
of the vector obtained by setting the first coordinate to zero.
-/

namespace CoarseDeGiorgi.Sharpness

open Homogenization

/-- The transverse component of `x`, with its axial coordinate set to zero. -/
def transversePart {d : ℕ} (x : Vec d) : Vec d :=
  fun i => if i.val = 0 then 0 else x i

/-- Euclidean distance from `x` to the line in the first coordinate direction. -/
noncomputable def transverseNorm {d : ℕ} (x : Vec d) : ℝ :=
  euclideanNorm (transversePart x)

end CoarseDeGiorgi.Sharpness
