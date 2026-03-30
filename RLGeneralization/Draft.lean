-- RLGeneralization.Draft: frontier modules excluded from the trusted root.
--
-- These files build, but several still contain deferred proofs (`sorry`),
-- vacuous theorems, or thin wrappers, so they are not part of the
-- trusted benchmark target.

-- Bellman rank and GOLF (has vacuous theorem)
import RLGeneralization.BilinearRank.Basic

-- Phase 9: cross-cutting modules (conditional, sorry proofs)
import RLGeneralization.OfflineRL.FunctionApprox
import RLGeneralization.MDP.AverageRewardNonasymptotic
import RLGeneralization.MDP.POmdpBeliefMDP
import RLGeneralization.BilinearRank.RepresentationBound

-- Phase 10: executable artifacts (promoted to trusted root)
