-- RLGeneralization.Draft: frontier modules excluded from the trusted root.
--
-- These files compile with zero sorry, but they are not part of the
-- trusted benchmark target because their theorems are conditional,
-- wrapper, vacuous, or too thin (definitions-only with trivial corollaries).

-- Bellman rank and GOLF (has vacuous theorem)
import RLGeneralization.BilinearRank.Basic

-- Natural policy-gradient update (definitions only)
import RLGeneralization.PolicyOptimization.NPG
