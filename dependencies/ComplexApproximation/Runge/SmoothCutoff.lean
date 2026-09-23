import FunctionTheory.Smooth.Cutoff

/-!
# Compatibility names for smooth cutoff and compact extension

The original proofs now live in FunctionTheory.Smooth.Cutoff, so they can also
be reused by smooth conformal corrections. Both original Runge declarations
remain available with exactly their previous statements.
-/

namespace Runge

export FunctionTheory (exists_smooth_cutoff exists_smooth_compact_extension)

end Runge
